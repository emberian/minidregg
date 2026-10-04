#!/usr/bin/env python3
"""journey.d/lib/hostraw.py -- the Host session wire, spoken directly, for journeys
that must do what the client never does: resend one exact signed call, alter a
byte of it, or lose a reply on purpose. Not a client: it signs nothing, encodes no
Lean value and decides nothing; every verdict comes from the Host's own frame,
decoded by the Host (`HOST CONFIG inspect outcome`).

The wire (native/resource-client/src/transport.rs, invoke_inner / write_frame):
  frame   = 0x02 ++ u32le(len config) ++ config ++ sha256(host image) ++ op ++ payload
  message = u32le(len frame) ++ frame          (the reply is framed the same way)
A reply's first byte is the operation (accepted), 255 (refused, the rest is an
encoded outcome) or 254 (the socket refused to forward; the rest is text).

  hostraw.py call SOCKET CONFIG HOST OP PAYLOAD OUT
      one exchange; OUT gets the reply bytes; prints "<first byte> <ms>".
  hostraw.py repeat SOCKET CONFIG HOST OP PAYLOAD N OUTDIR [STOP_SHA]
      N serial exchanges of the same payload; OUTDIR/replies.tsv rows
      "i <first byte> <ms> <sha256 of reply>", each distinct reply kept once as
      OUTDIR/reply-<sha>.bin; stops early after the first reply whose sha is
      STOP_SHA-different-from-the-first when STOP_SHA is "change".
  hostraw.py proxy LISTEN UPSTREAM DROP_OP DROP_COUNT MODE LOG
      forward every framed exchange to UPSTREAM, logging "n op first-byte" per
      exchange to LOG and keeping each reply as LOG.<n>-op<op>.bin. For the first
      DROP_COUNT requests with operation DROP_OP: MODE lose-reply forwards the
      request, reads the Host's reply (the Host has decided) and closes the
      client's connection without it (a lost reply); MODE never-forward closes
      the client's connection without forwarding (the Host never sees it).
      Runs until killed.
  hostraw.py refusals LOG OFFSET
      the Host's operator log (a `mini serve` log): one line per
      "host: submission refused (operator log):" entry written after byte OFFSET,
      "<n>\t<lane|authsig|legsig|other>\t<the entry on one line>". The Host is serial,
      so with one serial client the n-th entry is the n-th refused request.
  hostraw.py debt SOCKET CONFIG HOST OP CHARGED VALID LOG OUTDIR MAX
      sends CHARGED (a call refused AFTER authentication, so it is charged) until a
      refusalLane entry is followed by a charged one -- the lane was closed, so that
      charge leaves it in debt -- then sends VALID at once from this process (no
      interpreter start between them). OUTDIR gets valid.bin and debt.tsv: tries,
      ms from the charge's reply to sending VALID, kinds of the entries after it.
  hostraw.py flip PAYLOAD SIGHEX WHICH OUT
      copy PAYLOAD with the last byte of the WHICH-th (first|last) occurrence of
      the 64-byte signature SIGHEX inverted; prints the occurrence count.
"""
import hashlib, os, socket, struct, sys, time


def frame(config, host, op, payload):
    sha = hashlib.sha256(open(host, "rb").read()).digest()
    body = b"\x02" + struct.pack("<I", len(config)) + config + sha + bytes([op]) + payload
    return struct.pack("<I", len(body)) + body


def read_exact(sock, n):
    out = b""
    while len(out) < n:
        chunk = sock.recv(n - len(out))
        if not chunk:
            raise EOFError("connection closed after %d of %d bytes" % (len(out), n))
        out += chunk
    return out


def read_message(sock):
    (size,) = struct.unpack("<I", read_exact(sock, 4))
    return read_exact(sock, size)


def exchange(path, message):
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    sock.settimeout(600)
    sock.connect(path)
    try:
        sock.sendall(message)
        return read_message(sock)
    finally:
        sock.close()


def cmd_call(sock_path, config, host, op, payload, out):
    message = frame(open(config, "rb").read(), host, int(op), open(payload, "rb").read())
    t0 = time.monotonic()
    reply = exchange(sock_path, message)
    ms = (time.monotonic() - t0) * 1000
    open(out, "wb").write(reply)
    print(reply[0], "%.1f" % ms)


def cmd_repeat(sock_path, config, host, op, payload, n, outdir, stop=None):
    os.makedirs(outdir, exist_ok=True)
    message = frame(open(config, "rb").read(), host, int(op), open(payload, "rb").read())
    first = None
    with open(os.path.join(outdir, "replies.tsv"), "w") as tsv:
        for i in range(1, int(n) + 1):
            t0 = time.monotonic()
            reply = exchange(sock_path, message)
            ms = (time.monotonic() - t0) * 1000
            digest = hashlib.sha256(reply).hexdigest()
            kept = os.path.join(outdir, "reply-%s.bin" % digest[:16])
            if not os.path.exists(kept):
                open(kept, "wb").write(reply)
            tsv.write("%d\t%d\t%.1f\t%s\n" % (i, reply[0], ms, digest[:16]))
            tsv.flush()
            if first is None:
                first = digest
            elif stop == "change" and digest != first:
                break


def cmd_proxy(listen, upstream, drop_op, drop_count, mode, log):
    assert mode in ("lose-reply", "never-forward"), mode
    drop_op, left, n = int(drop_op), int(drop_count), 0
    server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    if os.path.exists(listen):
        os.unlink(listen)
    server.bind(listen)
    os.chmod(listen, 0o600)
    server.listen(16)
    with open(log, "a") as record:
        while True:
            client, _ = server.accept()
            n += 1
            try:
                request = read_message(client)
                (clen,) = struct.unpack("<I", request[1:5])
                op = request[5 + clen + (32 if request[0] == 2 else 0)]
                dropping = op == drop_op and left > 0
                if dropping:
                    left -= 1
                if dropping and mode == "never-forward":
                    record.write("%d\t%d\tnot-forwarded\n" % (n, op))
                    record.flush()
                    continue
                reply = exchange(upstream, struct.pack("<I", len(request)) + request)
                open("%s.%d-op%d.bin" % (log, n, op), "wb").write(reply)
                record.write("%d\t%d\t%d\t%s\n" % (n, op, reply[0], "reply-lost" if dropping else "replied"))
                record.flush()
                if dropping:
                    continue  # the finally closes the client: the reply is lost
                client.sendall(struct.pack("<I", len(reply)) + reply)
            except Exception as error:  # a broken client never stops the proxy
                record.write("%d\terror\t%r\n" % (n, error))
                record.flush()
            finally:
                client.close()


def entries_from(log, offset):
    """(entries, end offset): the refusal entries written after byte OFFSET."""
    head = "host: submission refused (operator log):"
    entries, current = [], None
    handle = open(log, errors="replace")
    handle.seek(int(offset))
    for line in handle:
        if line.startswith(head):
            if current is not None:
                entries.append(current)
            current = line.strip()
        elif current is not None and line[:1] in (" ", "\t"):
            current += " " + line.strip()
        elif current is not None:
            entries.append(current)
            current = None
    if current is not None:
        entries.append(current)
    return [entry[len(head):].strip() for entry in entries], handle.tell()


def kind_of(entry):
    # D3: an authority-envelope failure (signature first, unauthenticated, never
    # charged) and a target-leg failure (authenticated, charged) are distinct names.
    return ("lane" if "refusalLane" in entry else
            "authsig" if "Reject.authoritySignature" in entry else
            "legsig" if "Reject.legSignature" in entry else "other")


def cmd_debt(sock_path, config, host, op, charged, valid, log, outdir, most):
    os.makedirs(outdir, exist_ok=True)
    cfg = open(config, "rb").read()
    charge_msg = frame(cfg, host, int(op), open(charged, "rb").read())
    valid_msg = frame(cfg, host, int(op), open(valid, "rb").read())
    offset, prev = os.path.getsize(log), None
    for tries in range(1, int(most) + 1):
        exchange(sock_path, charge_msg)
        replied = time.monotonic()
        new, offset = entries_from(log, offset)
        kind = kind_of(new[-1]) if new else "none"
        if prev == "lane" and kind == "legsig":
            gap = (time.monotonic() - replied) * 1000
            reply = exchange(sock_path, valid_msg)
            open(os.path.join(outdir, "valid.bin"), "wb").write(reply)
            after = ",".join(kind_of(e) for e in entries_from(log, offset)[0]) or "none"
            with open(os.path.join(outdir, "debt.tsv"), "w") as tsv:
                tsv.write("%d\t%.1f\t%s\n" % (tries, gap, after))
            print(tries, "%.1f" % gap, after)
            return
        prev = kind
    sys.exit("debt: no closed-lane charge in %s tries" % most)


def cmd_refusals(log, offset):
    """Refusal entries written after byte OFFSET of the operator log (a mark taken
    with `stat -c %s`): reading from the mark keeps a mark-call-read cycle at a few
    milliseconds however long the log has grown."""
    entries, _ = entries_from(log, offset)
    for n, entry in enumerate(entries, 1):
        print("%d\t%s\t%s" % (n, kind_of(entry), entry))


def cmd_flip(payload, sighex, which, out):
    data = bytearray(open(payload, "rb").read())
    sig = bytes.fromhex(sighex)
    assert len(sig) == 64, "a signature is 64 bytes"
    at, start = [], 0
    while True:
        i = data.find(sig, start)
        if i < 0:
            break
        at.append(i)
        start = i + 1
    if not at:
        sys.exit("signature not found in payload")
    i = at[0] if which == "first" else at[-1]
    data[i + 63] ^= 0xFF
    open(out, "wb").write(bytes(data))
    print(len(at))


if __name__ == "__main__":
    verb, args = sys.argv[1], sys.argv[2:]
    {"call": cmd_call, "repeat": cmd_repeat, "proxy": cmd_proxy, "flip": cmd_flip,
     "refusals": cmd_refusals, "debt": cmd_debt}[verb](*args)
