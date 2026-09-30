#!/usr/bin/env python3
"""Evidence glue, not a client feature: send one exact byte payload to a
running `mini serve` socket and retain the Host's complete reply.

usage: raw-host-op.py SOCKET CONFIG HOST OP INPUT REPLY [DECODED_JSON]

Frames exactly as the client's transport::invoke_pinned: tag 2, config length
(u32 LE), config bytes, SHA-256 of the Host image, operation byte, payload;
the whole request and reply are u32 LE length-prefixed. When the reply is a
refusal (byte 255) and DECODED_JSON is given, the same Host decodes its own
frame with op 8 (`inspect outcome`); this script never decodes it.
Exit: 0 when the Host answered OP, 3 when it refused (255), 1 otherwise.
"""
import hashlib, json, socket, struct, sys


def invoke(sock_path, config, host_sha, op, payload):
    frame = bytes([2]) + struct.pack("<I", len(config)) + config + host_sha + bytes([op]) + payload
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
        s.connect(sock_path)
        s.sendall(struct.pack("<I", len(frame)) + frame)
        head = b""
        while len(head) < 4:
            chunk = s.recv(4 - len(head))
            if not chunk:
                raise SystemExit("connection closed before reply")
            head += chunk
        size = struct.unpack("<I", head)[0]
        body = b""
        while len(body) < size:
            chunk = s.recv(size - len(body))
            if not chunk:
                raise SystemExit("truncated reply")
            body += chunk
    return body


def main():
    if len(sys.argv) not in (7, 8):
        print(__doc__, file=sys.stderr)
        return 64
    sock_path, config_path, host_path, op, input_path, reply_path = sys.argv[1:7]
    config = open(config_path, "rb").read()
    host_sha = hashlib.sha256(open(host_path, "rb").read()).digest()
    payload = open(input_path, "rb").read()
    reply = invoke(sock_path, config, host_sha, int(op), payload)
    open(reply_path, "wb").write(reply)
    if reply[:1] == bytes([int(op)]):
        print(f"answered op {op}, {len(reply) - 1} bytes")
        return 0
    if reply[:1] == bytes([255]) and len(sys.argv) == 8:
        kind = b"outcome"
        inspect = struct.pack("<H", len(kind)) + kind + reply[1:]
        decoded = invoke(sock_path, config, host_sha, 8, inspect)
        if decoded[:1] != bytes([8]):
            print("Host could not decode its refusal frame", file=sys.stderr)
            return 1
        value = json.loads(decoded[1:])
        open(sys.argv[7], "w").write(json.dumps(value, indent=2) + "\n")
        print(f"refused (Host decoding): reason {value.get('reason')}", file=sys.stderr)
        return 3
    return 3 if reply[:1] == bytes([255]) else 1


if __name__ == "__main__":
    sys.exit(main())
