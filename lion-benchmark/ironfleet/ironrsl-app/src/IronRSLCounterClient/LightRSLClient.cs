using System;
using System.Collections.Generic;
using System.IO;
using System.Net.Sockets;
using IronfleetIoFramework;

namespace IronRSLCounterClient
{
  public class LightRSLClient
  {
    private Socket[] sockets;
    private int serverCount;
    private ulong nextSeqNum;
    private int primaryIndex;
    private byte[] myKey;
    private ServiceIdentity serviceIdentity;
    private byte[] hdrBuf = new byte[8];

    public LightRSLClient(ServiceIdentity si, string serviceName)
    {
      serviceIdentity = si;
      serverCount = si.Servers.Count;
      sockets = new Socket[serverCount];
      nextSeqNum = 0;
      primaryIndex = 0;

      var cert = IronfleetCrypto.CreateTransientClientIdentity();
      myKey = IoScheduler.GetCertificatePublicKey(cert);

      for (int i = 0; i < serverCount; i++)
        ConnectToServer(i);
    }

    private void ConnectToServer(int idx)
    {
      var server = serviceIdentity.Servers[idx];
      var sock = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);
      sock.NoDelay = true;
      sock.Connect(server.HostNameOrAddress, server.Port);
      sockets[idx] = sock;

      SendRaw(sock, ToBE64((ulong)myKey.Length));
      SendRaw(sock, myKey);
    }

    public byte[] SubmitRequest(byte[] request, int timeoutMs = 1000)
    {
      ulong seqNum = nextSeqNum++;
      byte[] msg = EncodeRequest(seqNum, request);

      SendMessage(primaryIndex, msg);

      while (true)
      {
        byte[] reply = PollReply(timeoutMs);

        if (reply == null)
        {
          primaryIndex = (primaryIndex + 1) % serverCount;
          SendMessage(primaryIndex, msg);
          continue;
        }

        if (reply.Length < 24) continue;
        if (ReadBE64(reply, 0) != 6) continue;
        if (ReadBE64(reply, 8) != seqNum) continue;

        ulong replyLen = ReadBE64(reply, 16);
        if (replyLen + 24 != (ulong)reply.Length) continue;

        byte[] result = new byte[reply.Length - 24];
        Buffer.BlockCopy(reply, 24, result, 0, result.Length);
        return result;
      }
    }

    private byte[] EncodeRequest(ulong seqNum, byte[] payload)
    {
      byte[] msg = new byte[24 + payload.Length];
      WriteBE64(msg, 0, 0);
      WriteBE64(msg, 8, seqNum);
      WriteBE64(msg, 16, (ulong)payload.Length);
      Buffer.BlockCopy(payload, 0, msg, 24, payload.Length);
      return msg;
    }

    private void SendMessage(int idx, byte[] msg)
    {
      var sock = sockets[idx];
      SendRaw(sock, ToBE64((ulong)msg.Length));
      SendRaw(sock, msg);
    }

    private byte[] PollReply(int timeoutMs)
    {
      var checkRead = new List<Socket>();
      for (int i = 0; i < serverCount; i++)
        if (sockets[i] != null && sockets[i].Connected)
          checkRead.Add(sockets[i]);

      if (checkRead.Count == 0) return null;

      Socket.Select(checkRead, null, null, timeoutMs * 1000);

      foreach (var sock in checkRead)
      {
        if (!RecvFull(sock, hdrBuf, 0, 8)) continue;
        ulong msgLen = ReadBE64(hdrBuf, 0);
        byte[] body = new byte[msgLen];
        if (!RecvFull(sock, body, 0, (int)msgLen)) continue;
        return body;
      }

      return null;
    }

    private static void SendRaw(Socket sock, byte[] data)
    {
      int sent = 0;
      while (sent < data.Length)
        sent += sock.Send(data, sent, data.Length - sent, SocketFlags.None);
    }

    private static bool RecvFull(Socket sock, byte[] buf, int offset, int count)
    {
      int received = 0;
      while (received < count)
      {
        int n = sock.Receive(buf, offset + received, count - received, SocketFlags.None);
        if (n == 0) return false;
        received += n;
      }
      return true;
    }

    private static byte[] ToBE64(ulong val)
    {
      byte[] b = BitConverter.GetBytes(val);
      if (BitConverter.IsLittleEndian) Array.Reverse(b);
      return b;
    }

    private static void WriteBE64(byte[] buf, int offset, ulong val)
    {
      byte[] b = BitConverter.GetBytes(val);
      if (BitConverter.IsLittleEndian) Array.Reverse(b);
      Buffer.BlockCopy(b, 0, buf, offset, 8);
    }

    private static ulong ReadBE64(byte[] buf, int offset)
    {
      byte[] b = new byte[8];
      Buffer.BlockCopy(buf, offset, b, 0, 8);
      if (BitConverter.IsLittleEndian) Array.Reverse(b);
      return BitConverter.ToUInt64(b, 0);
    }
  }
}
