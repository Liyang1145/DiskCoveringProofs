"""Portable path roots for the hark-archive scripts.

Every script under hark-archive/ locates this file by walking up from its own
``__file__`` to the ``hark-archive`` directory, so scripts run from any cwd on any
machine.  Each root can be overridden with an environment variable:

  DCP_N26_ROOT    n=26 work tree            (default: <hark-archive>/n26)
  DCP_N11_ROOT    n=11 Lean work tree       (default: <hark-archive>/n11)
  DCP_MAIN_REPO   checkout of DiskCoveringProofs main (needed by the v3-replay
                  scripts that read cover26/proof_bundle/...)
                                            (default: $DCP_N26_ROOT/repo)
  DCP_TMP         scratch dir for build products / staging that the original
                  sandbox kept in /tmp or /var/tmp
                                            (default: tempfile.gettempdir(), i.e. $TMPDIR or /tmp)
  LEAN_TOOLCHAIN  Lean toolchain prefix (bin/lean, lib/lean)
                  (default: $ELAN_HOME/toolchains/leanprover--lean4---v4.33.1,
                   ELAN_HOME defaulting to ~/.elan; else `lean --print-prefix`)
  LEAN            lean executable           (default: $LEAN_TOOLCHAIN/bin/lean)
  LEANTAR         leantar executable        (default: leantar on PATH, else $LEAN_TOOLCHAIN/bin/leantar)

LEAN_TOOLCHAIN / LEAN / LEANTAR are resolved lazily (only when imported).
"""
import os
import shutil
import subprocess
import tempfile

HARK_ARCHIVE = os.path.dirname(os.path.abspath(__file__))
LEAN_VERSION = 'v4.33.1'


def _env(name, default):
    v = os.environ.get(name)
    return os.path.abspath(os.path.expanduser(v)) if v else default


DCP_N26 = _env('DCP_N26_ROOT', os.path.join(HARK_ARCHIVE, 'n26'))
DCP_N11 = _env('DCP_N11_ROOT', os.path.join(HARK_ARCHIVE, 'n11'))
DCP_MAIN_REPO = _env('DCP_MAIN_REPO', os.path.join(DCP_N26, 'repo'))
DCP_TMP = _env('DCP_TMP', tempfile.gettempdir())


def _toolchain():
    v = os.environ.get('LEAN_TOOLCHAIN')
    if v:
        return os.path.abspath(os.path.expanduser(v))
    elan = os.environ.get('ELAN_HOME') or os.path.expanduser('~/.elan')
    cand = os.path.join(elan, 'toolchains', 'leanprover--lean4---' + LEAN_VERSION)
    if os.path.isdir(cand):
        return cand
    lean = os.environ.get('LEAN') or shutil.which('lean')
    if lean:
        try:
            out = subprocess.run([lean, '--print-prefix'], capture_output=True,
                                 text=True, timeout=120).stdout.strip()
            if out:
                return out
        except Exception:
            pass
    return cand


def __getattr__(name):  # PEP 562: lazy toolchain lookup
    if name == 'LEAN_TOOLCHAIN':
        return _toolchain()
    if name == 'LEAN':
        return os.environ.get('LEAN') or os.path.join(_toolchain(), 'bin', 'lean')
    if name == 'LEANTAR':
        return (os.environ.get('LEANTAR') or shutil.which('leantar')
                or os.path.join(_toolchain(), 'bin', 'leantar'))
    raise AttributeError(name)


# ---------------------------------------------------------------------------
# Hash-pinned checkers.  These two files are byte-for-byte what the certificates
# record (local/FOREST-Q6.json pins certB.py, ROOT25-FOREST-INDEX.json pins
# verify_certs_v3_pre_slabforest.py), so they still contain the original sandbox
# root literal.  They are NOT edited; instead the literal is rewritten in memory
# when they are imported (finder below) or run (hark-archive/run_pinned.py).
SANDBOX_N26 = '/workspace/work/dcp-n26'
PINNED = {
    os.path.join('n26', 'local', 'certB.py'):
        'f8dc2f98f64ee2758ad5a5a2a8bd137da855bab87422d97b2ccf88d90655be18',
    os.path.join('n26', 'verify_certs_v3_pre_slabforest.py'):
        'cbb67463619328ccdbade8872398072fee84f40544e4dec8210a3c52d246ca6b',
}


def pinned_source(path):
    """(rewritten source, sha256 of the untouched file bytes) for a pinned script."""
    import hashlib
    raw = open(path, 'rb').read()
    src = raw.decode('utf-8')
    for q in ("'", '"'):
        src = src.replace(q + SANDBOX_N26 + q, repr(DCP_N26))
    return src, hashlib.sha256(raw).hexdigest()


def _is_pinned(path):
    try:
        rel = os.path.relpath(os.path.realpath(path), os.path.realpath(HARK_ARCHIVE))
    except ValueError:
        return False
    return rel in PINNED


import importlib.abc as _iabc
import importlib.machinery as _imach
import sys as _sys


class _PinnedLoader(_iabc.SourceLoader):
    def __init__(self, fullname, path):
        self.fullname, self.path = fullname, path

    def get_filename(self, fullname):
        return self.path

    def get_data(self, path):
        if path == self.path:
            return pinned_source(path)[0].encode('utf-8')
        with open(path, 'rb') as fh:
            return fh.read()

    def path_stats(self, path):  # disable bytecode cache for rewritten sources
        raise OSError


class _PinnedFinder(_iabc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if '.' in fullname:
            return None
        spec = _imach.PathFinder.find_spec(fullname, path)
        if spec is None or not spec.origin or not _is_pinned(spec.origin):
            return None
        return _imach.ModuleSpec(fullname, _PinnedLoader(fullname, spec.origin), origin=spec.origin)


if not any(isinstance(f, _PinnedFinder) for f in _sys.meta_path):
    _sys.meta_path.insert(0, _PinnedFinder())
