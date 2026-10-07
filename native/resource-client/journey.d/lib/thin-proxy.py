#!/usr/bin/env python3
"""Journey tool: a lying Host at the thin-consent boundary.

`mini` starts this file as its local consent provider (MINI_CONSENT_HOST). It
starts the real provider (THIN_PROXY_REAL, same arguments) and relays every
frame both ways. On frame 232 (thin plan consent) it rewrites what the Host
supplied, as THIN_PROXY_MODE says:

  pass                 change nothing
  view=PATH            serve the bytes of PATH as every target's view (a view of
                       another state: the Host lies about the target)
  slots-from=PATH      keep the proposed plan up to its slots, then splice in the
                       slots of the plan at PATH (headers that sign another command);
                       THIN_PROXY_OTHER_INTENT names that plan's retained intent
  capture=PATH         save the proposed plan and intent as PATH.plan and
                       PATH.intent and refuse the frame itself: nothing is signed

Each rewrite is appended to THIN_PROXY_LOG as one line, so a journey can assert
that the planted change happened before it reads the provider's verdict.
"""
import os
import struct
import subprocess
import sys


def read_exactly(stream, count):
    data = b""
    while len(data) < count:
        chunk = stream.read(count - len(data))
        if not chunk:
            return None
        data += chunk
    return data


def split_pair(payload):
    (width,) = struct.unpack("<I", payload[:4])
    return payload[4:4 + width], payload[4 + width:]


def pair(left, right):
    return struct.pack("<I", len(left)) + left + right


def stream_nat(value):
    out = bytearray()
    while value > 0:
        out.append(value % 255)
        value //= 255
    out.append(255)
    return bytes(out)


def decode_nat(data, offset):
    value, scale = 0, 1
    while data[offset] != 255:
        value += data[offset] * scale
        scale *= 255
        offset += 1
    return value, offset + 1


def decode_byte_list(data):
    count, offset = decode_nat(data, 0)
    items = []
    for _ in range(count):
        width, offset = decode_nat(data, offset)
        items.append(data[offset:offset + width])
        offset += width
    return items


def encode_byte_list(items):
    out = stream_nat(len(items))
    for item in items:
        out += stream_nat(len(item)) + item
    return out


def slots_parse(plan, offset):
    """True when the bytes from `offset` are exactly a slot list:
    count, then (role, index, header bytes) per slot, ending at the plan's end."""
    try:
        count, at = decode_nat(plan, offset)
        for _ in range(count):
            _, at = decode_nat(plan, at)
            _, at = decode_nat(plan, at)
            width, at = decode_nat(plan, at)
            at += width
        return at == len(plan) and count > 0
    except IndexError:
        return False


def slots_offset(plan, intent):
    """Where a plan's slot list starts: right after its finalized draft, whose
    command bytes the retained intent also carries. The offset must parse as the
    whole slot list, or the proxy refuses to plant anything."""
    import difflib
    match = difflib.SequenceMatcher(None, intent, plan, autojunk=False).find_longest_match(
        0, len(intent), 0, len(plan))
    end = match.b + match.size
    for offset in range(end, max(end - 8, 0), -1):
        if slots_parse(plan, offset):
            return offset
    raise SystemExit("thin-proxy: the plan's slot list was not located")


def log(line):
    path = os.environ.get("THIN_PROXY_LOG")
    if path:
        with open(path, "a") as handle:
            handle.write(line + "\n")


def rewrite(payload, mode):
    intent, rest = split_pair(payload)
    signer, rest = split_pair(rest)
    plan, views_bytes = split_pair(rest)
    views = decode_byte_list(views_bytes)
    if mode == "pass":
        return payload
    if mode.startswith("view="):
        with open(mode[5:], "rb") as handle:
            lie = handle.read()
        changed = [lie for _ in views]
        if changed == views:
            raise SystemExit("thin-proxy: the substituted view equals the served one")
        log(f"view: replaced {len(views)} served view(s) with {mode[5:]}")
        return pair(intent, pair(signer, pair(plan, encode_byte_list(changed))))
    if mode.startswith("slots-from="):
        with open(mode[11:], "rb") as handle:
            other = handle.read()
        with open(os.environ["THIN_PROXY_OTHER_INTENT"], "rb") as handle:
            other_intent = handle.read()
        forged = plan[:slots_offset(plan, intent)] + other[slots_offset(other, other_intent):]
        if forged == plan:
            raise SystemExit("thin-proxy: the spliced plan equals the proposed one")
        log(f"slots-from: spliced the slots of {mode[11:]} into the proposed plan")
        return pair(intent, pair(signer, pair(forged, views_bytes)))
    raise SystemExit(f"thin-proxy: unknown mode {mode}")


def main():
    real = os.environ["THIN_PROXY_REAL"]
    mode = os.environ.get("THIN_PROXY_MODE", "pass")
    child = subprocess.Popen([real] + sys.argv[1:], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    source = sys.stdin.buffer
    sink = sys.stdout.buffer
    while True:
        header = read_exactly(source, 4)
        if header is None:
            break
        (length,) = struct.unpack("<I", header)
        body = read_exactly(source, length)
        if body is None:
            break
        operation, payload = body[0], body[1:]
        log(f"frame {operation}")
        if operation == 232 and mode.startswith("capture="):
            intent, rest = split_pair(payload)
            _, rest = split_pair(rest)
            plan, _ = split_pair(rest)
            with open(mode[8:] + ".plan", "wb") as handle:
                handle.write(plan)
            with open(mode[8:] + ".intent", "wb") as handle:
                handle.write(intent)
            log(f"capture: saved the proposed plan as {mode[8:]}.plan and refused it")
            refusal = bytes([255]) + b"thin-proxy captured this plan; nothing signed"
            sink.write(struct.pack("<I", len(refusal)) + refusal)
            sink.flush()
            continue
        if operation == 232:
            payload = rewrite(payload, mode)
        body = bytes([operation]) + payload
        child.stdin.write(struct.pack("<I", len(body)) + body)
        child.stdin.flush()
        answer_header = read_exactly(child.stdout, 4)
        if answer_header is None:
            break
        (answer_length,) = struct.unpack("<I", answer_header)
        answer = read_exactly(child.stdout, answer_length)
        sink.write(answer_header + answer)
        sink.flush()
    child.stdin.close()
    child.wait()


if __name__ == "__main__":
    main()
