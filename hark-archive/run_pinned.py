#!/usr/bin/env python3
"""Run a hash-pinned checker unchanged on any machine.

usage: python3 hark-archive/run_pinned.py <pinned-script> [args...]
  e.g. python3 hark-archive/run_pinned.py hark-archive/n26/local/certB.py 100

The pinned file's bytes are hashed (and compared with the sha256 the certificates
record), then executed as __main__ with the sandbox root literal
'/workspace/work/dcp-n26' replaced in memory by $DCP_N26_ROOT (see _paths.py).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _paths

if len(sys.argv) < 2:
    sys.exit(__doc__)
path = os.path.abspath(sys.argv[1])
rel = os.path.relpath(os.path.realpath(path), os.path.realpath(_paths.HARK_ARCHIVE))
want = _paths.PINNED.get(rel)
src, got = _paths.pinned_source(path)
print(f'[run_pinned] {rel} sha256={got} ' + ('(matches certificate pin)' if got == want else
      ('(MISMATCH, pin=' + str(want) + ')')), file=sys.stderr)
sys.argv = [path] + sys.argv[2:]
sys.path[0] = os.path.dirname(path)
g = {'__name__': '__main__', '__file__': path, '__builtins__': __builtins__}
exec(compile(src, path, 'exec'), g)
