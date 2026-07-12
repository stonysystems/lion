using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Security.Cryptography.X509Certificates;
using IronfleetIoFramework;

namespace IronfleetIoFramework
{
  [StructLayout(LayoutKind.Sequential)]
  public struct FfiIdentity
  {
    public IntPtr public_key;
    public uint public_key_len;
    public IntPtr host;
    public uint host_len;
    public ushort port;
  }

  public class LionIoScheduler
  {
    private const string LibName = "ironfleet_io_lion";

    [DllImport(LibName)] static extern IntPtr lion_io_create(
      IntPtr bind_host, uint bind_host_len, ushort bind_port,
      IntPtr my_public_key, uint my_public_key_len,
      IntPtr known, uint known_count);

    [DllImport(LibName)] static extern void lion_io_destroy(IntPtr handle);

    [DllImport(LibName)] static extern void lion_io_my_key_hash(
      IntPtr handle, out IntPtr out_hash, out uint out_hash_len);

    [DllImport(LibName)] static extern void lion_io_receive(
      IntPtr handle, int time_limit_ms,
      out byte out_ok, out byte out_timed_out,
      out IntPtr out_remote, out uint out_remote_len,
      out IntPtr out_msg, out uint out_msg_len);

    [DllImport(LibName)] static extern byte lion_io_send(
      IntPtr handle,
      IntPtr remote_key_hash, uint remote_key_hash_len,
      IntPtr message, uint message_len);

    [DllImport(LibName)] static extern void lion_io_free_buffer(IntPtr ptr, uint len);

    private IntPtr handle;
    private byte[] myPublicKeyHash;
    private SHA256 hasher;

    private LionIoScheduler(IntPtr handle, byte[] myPublicKeyHash)
    {
      this.handle = handle;
      this.myPublicKeyHash = myPublicKeyHash;
      this.hasher = SHA256.Create();
    }

    public static LionIoScheduler CreateServer(
      PrivateIdentity myIdentity,
      string localHostNameOrAddress,
      int localPort,
      List<PublicIdentity> knownIdentities,
      bool verbose,
      bool useSsl)
    {
      var cert = new X509Certificate2(myIdentity.Pkcs12, "", X509KeyStorageFlags.Exportable);
      var myPublicKey = IoScheduler.GetCertificatePublicKey(cert);

      if (string.IsNullOrEmpty(localHostNameOrAddress))
        localHostNameOrAddress = myIdentity.HostNameOrAddress;
      if (localPort == 0)
        localPort = myIdentity.Port;

      var hostBytes = System.Text.Encoding.UTF8.GetBytes(localHostNameOrAddress);
      var hostPin = GCHandle.Alloc(hostBytes, GCHandleType.Pinned);
      var pkPin = GCHandle.Alloc(myPublicKey, GCHandleType.Pinned);

      var ffiIds = new FfiIdentity[knownIdentities.Count];
      var pins = new List<GCHandle>();

      for (int i = 0; i < knownIdentities.Count; i++)
      {
        var id = knownIdentities[i];
        var pkBytes = id.PublicKey;
        var hBytes = System.Text.Encoding.UTF8.GetBytes(id.HostNameOrAddress);

        var pkGc = GCHandle.Alloc(pkBytes, GCHandleType.Pinned);
        var hGc = GCHandle.Alloc(hBytes, GCHandleType.Pinned);
        pins.Add(pkGc);
        pins.Add(hGc);

        ffiIds[i] = new FfiIdentity
        {
          public_key = pkGc.AddrOfPinnedObject(),
          public_key_len = (uint)pkBytes.Length,
          host = hGc.AddrOfPinnedObject(),
          host_len = (uint)hBytes.Length,
          port = (ushort)id.Port,
        };
      }

      var ffiPin = GCHandle.Alloc(ffiIds, GCHandleType.Pinned);

      var h = lion_io_create(
        hostPin.AddrOfPinnedObject(), (uint)hostBytes.Length, (ushort)localPort,
        pkPin.AddrOfPinnedObject(), (uint)myPublicKey.Length,
        ffiPin.AddrOfPinnedObject(), (uint)knownIdentities.Count);

      ffiPin.Free();
      foreach (var p in pins) p.Free();
      hostPin.Free();
      pkPin.Free();

      IntPtr hashPtr;
      uint hashLen;
      lion_io_my_key_hash(h, out hashPtr, out hashLen);
      var keyHash = new byte[hashLen];
      Marshal.Copy(hashPtr, keyHash, 0, (int)hashLen);

      if (verbose)
        Console.WriteLine("Lion IO scheduler started on {0}:{1}", localHostNameOrAddress, localPort);

      return new LionIoScheduler(h, keyHash);
    }

    public void ReceivePacket(int timeLimit, out bool ok, out bool timedOut,
                               out byte[] remotePublicKeyHash, out byte[] message)
    {
      byte okByte, timedOutByte;
      IntPtr remotePtr, msgPtr;
      uint remoteLen, msgLen;

      lion_io_receive(handle, timeLimit,
                      out okByte, out timedOutByte,
                      out remotePtr, out remoteLen,
                      out msgPtr, out msgLen);

      ok = okByte != 0;
      timedOut = timedOutByte != 0;

      if (ok && !timedOut && remotePtr != IntPtr.Zero)
      {
        remotePublicKeyHash = new byte[remoteLen];
        Marshal.Copy(remotePtr, remotePublicKeyHash, 0, (int)remoteLen);
        lion_io_free_buffer(remotePtr, remoteLen);

        message = new byte[msgLen];
        Marshal.Copy(msgPtr, message, 0, (int)msgLen);
        lion_io_free_buffer(msgPtr, msgLen);
      }
      else
      {
        remotePublicKeyHash = null;
        message = null;
      }
    }

    public bool SendPacket(byte[] remotePublicKeyHash, byte[] message)
    {
      var rkhPin = GCHandle.Alloc(remotePublicKeyHash, GCHandleType.Pinned);
      var msgPin = GCHandle.Alloc(message, GCHandleType.Pinned);

      var result = lion_io_send(handle,
                                rkhPin.AddrOfPinnedObject(), (uint)remotePublicKeyHash.Length,
                                msgPin.AddrOfPinnedObject(), (uint)message.Length);

      rkhPin.Free();
      msgPin.Free();
      return result != 0;
    }

    public byte[] HashPublicKey(byte[] publicKey)
    {
      return hasher.ComputeHash(publicKey);
    }

    ~LionIoScheduler()
    {
      if (handle != IntPtr.Zero)
      {
        lion_io_destroy(handle);
        handle = IntPtr.Zero;
      }
    }
  }
}
