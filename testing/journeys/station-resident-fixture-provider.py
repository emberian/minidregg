#!/usr/bin/env python3
"""Bounded no-paid station narrator through the existing resident provider seam.

The tool result is the existing ACP's actual native document read. This provider
neither reads controller journals nor constructs/submits native commands. Source
citations and an authored suggested method are data; receiving must reselect the
current inputs and execute the checked source under ordinary current authority.
"""
import argparse
import hashlib
import http.server
import json
import os
import pathlib
import threading

MAX_BODY = 1048576
MAX_TEXT = 32768
MAX_REPLIES = 64
PROTOCOL = "station-resident-input-v1"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def reply_from_read(body):
    reads = [row for row in body.get("messages", [])
             if row.get("role") == "tool" and row.get("tool_call_id") == "captured-input-read"]
    if len(reads) != 1:
        raise ValueError("one actual native captured document read required")
    result = json.loads(reads[0]["content"])
    content = result.get("content", [])
    if result.get("isError") or len(content) != 1 or content[0].get("type") != "text":
        raise ValueError("native document read refused or shape differs")
    read = json.loads(content[0]["text"])
    doc, text = read["doc"], read["text"]
    if not isinstance(doc, str) or not isinstance(text, str) or len(text.encode()) > MAX_TEXT:
        raise ValueError("bounded native document required")
    station = json.loads(text)
    if station.get("type") != PROTOCOL:
        raise ValueError("explicit authored station input required")
    # A source citation is preserved verbatim. It is not a signature, grant,
    # current-root certificate or proof that the cited method was executed.
    source = station["source"]
    if not isinstance(source, dict) or set(source) != {"artifact", "definition", "revision"}:
        raise ValueError("exact source/export/revision citation required")
    if not all(isinstance(source[k], str) and source[k] for k in source):
        raise ValueError("source citation must contain exact nonempty strings")
    observations = station["observations"]
    if not isinstance(observations, list) or not 1 <= len(observations) <= 16:
        raise ValueError("bounded explicit observation citations required")
    for observed in observations:
        if not isinstance(observed, dict) or set(observed) != {"role", "target", "root"}:
            raise ValueError("observation citation shape differs")
        if not all(isinstance(observed[k], str) and observed[k] for k in observed):
            raise ValueError("observation citation absent")
    narrative = station["narrative"]
    suggestion = station["suggestion"]
    if not isinstance(narrative, str) or not 0 < len(narrative.encode()) <= 4096:
        raise ValueError("bounded authored narration required")
    if not isinstance(suggestion, dict) or set(suggestion) != {"method", "arguments"}:
        raise ValueError("separate opaque method suggestion required")
    if not isinstance(suggestion["method"], str) or not suggestion["method"] or not isinstance(suggestion["arguments"], dict):
        raise ValueError("method suggestion shape differs")
    if len(json.dumps(suggestion).encode()) > 4096:
        raise ValueError("method suggestion too large")
    text_hash = digest(text.encode())
    reply = {"type": "station-gm-output-v1", "narrative": narrative,
             "citedInput": {"document": doc, "textSha256": text_hash,
                            "source": source, "observations": observations},
             "suggestedSourceCall": suggestion}
    return json.dumps(reply, ensure_ascii=False, separators=(",", ":")), text_hash


def run(state, port):
    if not 1024 < port < 65536:
        raise ValueError("explicit unprivileged port required")
    os.umask(0o077)
    state = pathlib.Path(state)
    lock = threading.Lock()

    def publish(name, value):
        destination = state / name
        temporary = state / (name + ".tmp")
        with open(temporary, "w") as stream:
            json.dump(value, stream, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, destination)
        fd = os.open(state, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)

    class Endpoint(http.server.BaseHTTPRequestHandler):
        def do_POST(self):
            if self.path != "/v1/chat/completions":
                self.send_error(404)
                return
            try:
                length = int(self.headers.get("Content-Length", "0"))
                if not 0 < length <= MAX_BODY:
                    self.send_error(413)
                    return
                raw = self.rfile.read(length)
                reply, read_hash = reply_from_read(json.loads(raw))
            except (ValueError, KeyError, TypeError) as error:
                self.send_error(400, str(error))
                return
            with lock:
                path = state / "provider-received.json"
                received = json.loads(path.read_text()) if path.exists() else []
                if len(received) >= MAX_REPLIES:
                    self.send_error(429, "bounded fixture reply capacity reached")
                    return
                received.append({"body": json.loads(raw), "sha256": digest(raw), "reply": reply,
                                 "nativeInputTextSha256": read_hash})
                publish("provider-received.json", received)
            chunks = [{"id": "station-narration", "object": "chat.completion.chunk",
                       "created": 1, "model": "mini-hermes-completion-cut",
                       "choices": [{"index": 0, "delta": {"role": "assistant", "content": reply},
                                    "finish_reason": "stop"}]},
                      {"id": "station-narration", "object": "chat.completion.chunk",
                       "created": 1, "model": "mini-hermes-completion-cut", "choices": [],
                       "usage": {"prompt_tokens": 1, "completion_tokens": 2, "total_tokens": 3}}]
            payload = ("".join("data: " + json.dumps(c) + "\n\n" for c in chunks)
                       + "data: [DONE]\n\n").encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def log_message(self, *args):
            pass

    server = http.server.ThreadingHTTPServer(("127.0.0.1", port), Endpoint)
    publish("provider-ready.json", {"protocol": "mini-resident-fixture-provider-ready-v1",
            "pid": os.getpid(), "endpoint": f"http://127.0.0.1:{port}/v1/chat/completions",
            "sourceSha256": digest(pathlib.Path(__file__).read_bytes())})
    server.serve_forever()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--state", required=True)
    parser.add_argument("--port", type=int, required=True)
    args = parser.parse_args()
    run(args.state, args.port)
