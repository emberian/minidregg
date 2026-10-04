# Room templates

A room template is a file of shell lines: exactly what a friend would type,
in order (PLACE §4.9). `room new NAME --template T` binds `$ROOM` to NAME and
`$ME` to the founder's subject, plans every line first (a line that is not a
verb refuses the whole template, naming the line, before anything is born),
then runs them as the founder; the first line that does not end done stops the
rest, naming the line and the Host's refusal, and the lines before it stand.
The files are compiled into `mini` (`shell/template.rs`), so `room template
show T` prints this directory's file byte for byte; a friend's own copy runs
as `--template @FILE` from HOME/requests. A `$NAME` the template is not given
refuses it. Comments (`#`) and blank lines are skipped; line numbers are the
file's.

| template | what it births | read |
|---|---|---|
| `workroom/template.shell` | `$ROOM` (open law), `$ROOM/index` (the map: only `$ME` writes, only grows), `$ROOM/wall` (stream), `$ROOM/notes` (draft), `$ROOM/tasks` (note), the map's line and links to wall/notes/tasks, notes → index | `room template show workroom` |
| `social/template.shell` | `$ROOM`, `$ROOM/index`, `$ROOM/wall` (stream), `$ROOM/intro` (draft), the map's links | `room template show social` |
| `social/member.shell` | `room welcome $ROOM $MEMBER --template social`: the invite (observe, place, append), and `$ROOM/stream-$MEMBER`, born owned by the founder (a birth into a room is owned by its creator; its law refuses every writer but `$MEMBER`, the founder included) (PLACE §2.3 (a)) | `room template show social member` |
| `story/template.shell` | `$ROOM`, `$ROOM/index`, `$ROOM/chapters` (note), `$ROOM/scenes` (stream), `$ROOM/cast` (draft), the map's links, chapters → cast | `room template show story` |

The map's links to a stream are `external mini:object/ID` links (the
hyperdocument `LinkTarget` has no resource constructor); `doc show` renders
them by the reader's own reference name, and `doc backlinks` finds them.
