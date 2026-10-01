# room/chat: a room friends talk in

`chat new ROOM` and `chat invite ROOM SUBJECT [NAME]` (`native/resource-client/src/chat.rs`)
run exactly these client operations. `law.author.json` is the one law the template installs;
`@SUBJECT` is replaced by the subject the law protects. The client compiles this file in
(`include_str!`), so this file is the law, not a copy of it.

## The shape

- **The room** `ROOM` is a `declared` cell. Its law is `law.author.json` with the founder's
  subject: only the founder writes it (mutate 2, append 7); reads and grants pass.
- **The roster** is the room cell's fields: field 2 = the founder's subject; member `k`
  (from 1) = field `2k+1` (subject) and field `2k+2` (the member's stream cell). Field 1 is
  the field every declared cell is born with (value 0); the roster leaves it alone.
- **A stream per member**: a `stream` cell born `--in ROOM`, owned by the member, under
  `law.author.json` with the member's subject. Only its owner can append to it.
- **The room grant**: `observe` + `append` `under ROOM` (`"room": true`). It reads the
  roster and every stream, and appends to the holder's own stream; the author law refuses
  it on anyone else's.

## `chat new ROOM` (the founder)

1. `workspace --action create --name ROOM --storage declared --predicate law.author(FOUNDER)`
2. `workspace --action create --name ROOM-me --storage stream --predicate law.author(FOUNDER) --in ROOM`
3. `propose` + `submit` + `publish-delegation`: delegate ROOM to FOUNDER, verbs observe,append, `room: true`
   (the founder's own grant on ROOM names ROOM alone; reading the streams needs `under ROOM`);
   `import ROOM-room --from-ref` it.
4. `propose` + `submit` an invoke on ROOM: create fields 2 = FOUNDER, 3 = FOUNDER, 4 = ROOM-me's cell.

## `chat invite ROOM SUBJECT [NAME]` (the founder; the founder pays)

1. Read the roster; refuse unless I am field 2 and SUBJECT is not on it.
2. Delegate ROOM to SUBJECT (observe, append, `room: true`), submit, publish.
3. `workspace --action create --name ROOM-<subject> --storage stream --predicate law.author(SUBJECT) --in ROOM --owner SUBJECT`
   (K-STREAM: a workspace without a birth context cannot birth, so the founder births it;
   the owner and control grants go to SUBJECT, the founder holds nothing on it).
4. Invoke on ROOM: create fields 2k+1 = SUBJECT, 2k+2 = the stream cell.
5. Print `chat join ROOM <the recipient reference>` for the member.

## `chat join ROOM INVITATION` (the member)

`import ROOM --from-ref` the invitation; read the roster with it; `import ROOM-me` my
stream with the room grant as both observe and operation capability.

A joiner who arrives later reads the whole room: every topic, pin and reaction before it.
