# C# IoScheduler TCP_NODELAY Fix

## Problem

C# IoScheduler server had ~131 req/s in SSL=false mode, vs ~2066 req/s in SSL=true mode.
P50 latency was exactly 40ms — matching the Linux TCP delayed ACK timer.

## Root Cause

`IoFramework.cs` never sets `TCP_NODELAY` on its `TcpClient` connections.

The `SenderThread.SendLoop` writes messages in two steps:
1. `IoEncoder.WriteUInt64(stream, messageSize)` — 8 bytes
2. `IoEncoder.WriteBytes(stream, message, 0, messageSize)` — message body

With Nagle's algorithm enabled, the 8-byte length header gets buffered when there is
unacknowledged data on the socket. The kernel waits for the receiver's delayed ACK
(40ms on Linux) before sending the buffered data. This adds 40ms to ~50% of requests.

SSL=true mode was unaffected because `SslStream` has its own internal buffer. Multiple
small writes get batched into a single TLS record, which is flushed as one TCP segment,
bypassing the Nagle + delayed ACK interaction.

`LightRSLClient` and the Lion server both already set `NoDelay = true`, which is why
they never exhibited this issue.

## Fix

Two lines in `IoFramework.cs`:

**Line 681** (ClientSenderThread.Connect — outbound connections):
```csharp
client = new TcpClient(destinationPublicIdentity.HostNameOrAddress, destinationPublicIdentity.Port);
client.NoDelay = true;  // <-- added
```

**Line 790** (ListenerThread.ListenLoop — inbound connections):
```csharp
TcpClient client = listener.AcceptTcpClient();
client.NoDelay = true;  // <-- added
```

## Results (localhost, 4 threads, 30s, SSL=false)

| Client         | Before Fix  | After Fix    | Speedup |
|----------------|-------------|--------------|---------|
| RSLClient      | 161 req/s   | 2,303 req/s  | 14.3x   |
| LightRSLClient | 131 req/s   | 3,043 req/s  | 23.2x   |

## Fair Comparison After Fix (LightRSLClient, SSL=false, localhost)

| Server IO Layer    | Throughput    | P50     | P99     |
|--------------------|---------------|---------|---------|
| C# IoScheduler     | 3,043 req/s   | 1.04 ms | 3.38 ms |
| Lion IO (Rust FFI) | 7,712 req/s   | 0.43 ms | 1.08 ms |

Lion is 2.5x faster than the fixed C# IoScheduler.
