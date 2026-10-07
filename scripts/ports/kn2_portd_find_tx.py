#!/usr/bin/env python3
"""PORT-D rewrite: `opened.durable.image.accepted.find? (fun entry => entry.transactionId.value == X)`
inside a `let some record := ... | fail` becomes the Reader's `byTx` through
`NativeHost.acceptedRecord` (a refusal is thrown with its message, never absent).
Anchored: the whole three-line binding must match; other shapes are left alone."""
import re, sys
for path in sys.argv[1:]:
    s = open(path).read()
    pat = re.compile(
        r"let some record := (opened)\.durable\.image\.accepted\.find\?\n"
        r"(\s+)\(fun entry => entry\.transactionId\.value == (\w+)\)\n")
    s2, n = pat.subn(lambda m: f"let some record ← NativeHost.acceptedRecord config {m.group(1)} ⟨{m.group(3)}⟩\n", s)
    open(path, "w").write(s2)
    print(path, n)
