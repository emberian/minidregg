import struct
from pathlib import Path

p = Path('/tank/dregg-build/bonsai2-local-20260927/model/Ternary-Bonsai-2-27B-PTQ1_0.gguf')
f = p.open('rb')
def read(fmt):
    return struct.unpack('<'+fmt, f.read(struct.calcsize('<'+fmt)))[0]
def string():
    return f.read(read('Q')).decode()
def value(t):
    fmts = {0:'B',1:'b',2:'H',3:'h',4:'I',5:'i',6:'f',7:'?',10:'Q',11:'q',12:'d'}
    if t in fmts: return read(fmts[t])
    if t == 8: return string()
    if t == 9:
        item, count = read('I'), read('Q')
        return [value(item) for _ in range(count)]
    raise ValueError(t)
print(f'magic={f.read(4).decode()} version={read("I")} tensors={read("Q")} kv={read("Q")}')
for _ in range(24):
    key=string()
    val=value(read('I'))
    if any(name in key for name in ('architecture','block_count','context_length','embedding_length','head_count','key_length','value_length')):
        print(f'{key}={val}')
