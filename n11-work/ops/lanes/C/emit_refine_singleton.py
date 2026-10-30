#!/usr/bin/env python3
"""Emit a singleton B13 refinement wrapper from the audited 2965 template."""
import argparse
from pathlib import Path
LEAN = Path(__file__).resolve().parents[3] / "lean" / "N11Formalization"
def emit(source: str, target: str) -> None:
    target_id = str(int(target))
    for stem in ("", "Main"):
        old = LEAN / f"EnergyTerminalBatchB13Refine{source}{stem}.lean"
        new = LEAN / f"EnergyTerminalBatchB13Refine{target}{stem}.lean"
        text = old.read_text(encoding="utf-8")
        text = text.replace(f"N{source}", f"N{target}")
        text = text.replace(f"Refine{source}", f"Refine{target}")
        text = text.replace(f"refine{source}", f"refine{target}")
        text = text.replace(f"not_paid_{source}", f"not_paid_{target}")
        text = text.replace(f"terminal {source}.", f"terminal {target_id}.")
        text = text.replace(f"\n{source}\n", f"\n{target_id}\n")
        text = text.replace(f"\n{source}.", f"\n{target_id}.")
        text = text.replace(f"({source} : Fin 5011)", f"({target_id} : Fin 5011)")
        text = text.replace(f"= {source} := by", f"= {target_id} := by")
        assert source not in text, old
        new.write_text(text, encoding="utf-8")
        print(new)
def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("target", choices=(
        "0037", "2337", "3112", "3440", "3589", "3623", "3633", "3777",
        "3792", "3853"))
    args = parser.parse_args()
    emit("2965", args.target)
if __name__ == "__main__":
    main()
