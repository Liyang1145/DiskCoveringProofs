"""Regenerate out/oracle_index_audit.txt from the audit module (pure import + log dump)."""
import runpy, io, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
mod = HERE / "oracle_index_audit.py"
src = mod.read_text(encoding="utf-8")
# strip the module's own (mis-pathed) final write
src = src.replace('(OUT / "oracle_index_audit.txt").write_text("\\n".join(log) + "\\n")', "pass")
src = src.replace('print("wrote", OUT / "oracle_index_audit.txt")', "pass")
g = {"__name__": "__main__", "__file__": str(mod)}
exec(compile(src, str(mod), "exec"), g)
out = HERE.parent / "out" / "oracle_index_audit.txt"
out.write_text("\n".join(g["log"]) + "\n", encoding="utf-8")
print("wrote", out, len(g["log"]), "lines")
