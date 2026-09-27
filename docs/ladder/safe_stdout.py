"""Make a closed stdout non-fatal, so a script's SIDE EFFECTS still happen.

`tool.py | head -N` closes stdout once head has its N lines.  The next print
raises BrokenPipeError and kills the script MID-RUN -- and in these tools the
work that matters (rewriting the note's state lines, `git add`, writing
table_new.txt, appending a cpu/elapsed sample) all happens AFTER the printing.
The run then looks successful: head has already displayed the figures, and a
pipeline's exit status belongs to head, not to the script behind it.

Caught at idx 1522, where two `bank.py | head -N` runs left the note's state
lines claiming 1691 rows against a staged 1692.  Nothing had been committed
wrong -- 40 commits were re-checked, note against blob, and all agreed -- but
only because the disagreement was noticed before the commit.

This lives in ONE file on purpose.  The duplicate-sample guard was written in
cnf_mtime_check.py and never reached bank.py, and that gap put three duplicate
key rows in the sample log; copying this block into three scripts would be the
same mistake with a different body.

    import sys, os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import safe_stdout  # noqa: F401
"""
import builtins, os, sys

_ORIG_PRINT = builtins.print
_PIPE_DEAD = []


def _safe_print(*a, **k):
    if _PIPE_DEAD:
        return
    try:
        _ORIG_PRINT(*a, **k)
        sys.stdout.flush()
    except (BrokenPipeError, ValueError):
        _PIPE_DEAD.append(True)
        try:
            sys.stdout = open(os.devnull, 'w')
        except OSError:
            pass


builtins.print = _safe_print


def pipe_died():
    """True once stdout went away -- for a caller that wants to know."""
    return bool(_PIPE_DEAD)
