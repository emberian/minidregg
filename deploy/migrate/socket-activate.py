"""socket-activate.py PATH OWNER_UID -- CMD...: bind one Unix listener at PATH (owner OWNER_UID, 0600) and exec
CMD with it as systemd's one activated listener (fd 3, LISTEN_FDS=1, LISTEN_PID = the exec'd pid)."""
import os, socket, sys

path, owner, sep, *cmd = sys.argv[1:]
assert sep == "--" and cmd, __doc__
s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
s.bind(path)
os.chown(path, int(owner), -1)
os.chmod(path, 0o600)
s.listen(64)
if s.fileno() != 3:
    os.dup2(s.fileno(), 3)
os.set_inheritable(3, True)
os.environ.update(LISTEN_FDS="1", LISTEN_PID=str(os.getpid()))
os.execvp(cmd[0], cmd)
