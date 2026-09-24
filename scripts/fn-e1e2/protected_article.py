"""Read one ARTICLE through the protected B listener on the isolated hbox fixture.

The caller must independently verify the returned carrier through fn native.
This script only performs bounded transport and dot unstuffing.
"""

import json
from pathlib import Path
import socket
import ssl
import sys


def line(stream):
    value = stream.readline(4097)
    if not value or len(value) > 4096 or not value.endswith(b"\r\n"):
        raise RuntimeError("invalid or missing NNTP response line")
    return value


def article(ready, message_id):
    with socket.create_connection(("127.0.0.1", ready["b_port"]), timeout=15) as raw:
        raw.settimeout(15)
        with raw.makefile("rwb", buffering=0) as plain:
            if not line(plain).startswith((b"200 ", b"201 ")):
                raise RuntimeError("unexpected NNTP greeting")
            plain.write(b"STARTTLS\r\n")
            if not line(plain).startswith(b"382 "):
                raise RuntimeError("STARTTLS refused")
        context = ssl.create_default_context(cafile=ready["b_tls_cert"])
        with context.wrap_socket(raw, server_hostname="localhost") as tls:
            with tls.makefile("rwb", buffering=0) as stream:
                stream.write(b"AUTHINFO USER " + ready["b_login"].encode("ascii") + b"\r\n")
                if not line(stream).startswith(b"381 "):
                    raise RuntimeError("AUTHINFO USER refused")
                password = Path(ready["b_password_file"]).read_bytes().rstrip(b"\r\n")
                if not password or len(password) > 256:
                    raise RuntimeError("invalid observer password length")
                stream.write(b"AUTHINFO PASS " + password + b"\r\n")
                if not line(stream).startswith(b"281 "):
                    raise RuntimeError("AUTHINFO PASS refused")
                stream.write(b"ARTICLE " + message_id.encode("ascii") + b"\r\n")
                response = line(stream)
                if response.startswith(b"430 "):
                    raise RuntimeError("article definitively absent")
                if not response.startswith(b"220 "):
                    raise RuntimeError("ARTICLE refused: " + response.decode("ascii", "replace"))
                out = bytearray()
                while True:
                    record = line(stream)
                    if record == b".\r\n":
                        break
                    if record.startswith(b".."):
                        record = record[1:]
                    out.extend(record)
                    if len(out) > 65536:
                        raise RuntimeError("ARTICLE exceeds experiment bound")
                return bytes(out)


def main():
    if len(sys.argv) != 4:
        raise SystemExit("usage: protected_article.py READY.json MESSAGE-ID OUT.eml")
    ready = json.loads(Path(sys.argv[1]).read_text(encoding="ascii"))
    message_id = sys.argv[2]
    if not (message_id.startswith("<") and message_id.endswith(">") and
            len(message_id) <= 256 and all(33 <= ord(ch) <= 126 for ch in message_id)):
        raise RuntimeError("invalid Message-ID")
    output = Path(sys.argv[3])
    if output.exists():
        raise RuntimeError("refusing to replace existing carrier")
    output.write_bytes(article(ready, message_id))


if __name__ == "__main__":
    main()
