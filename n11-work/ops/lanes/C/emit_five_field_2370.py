#!/usr/bin/env python3
"""Emit the exact five-field 2370 witness by specializing the 2368 emitter."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "emit_five_field_2368.py"


def main():
    text = SOURCE.read_text(encoding="utf-8")
    text = text.replace(
        "residual-mixture-faces5-float-2360-2368-2370.json",
        "residual-mixture-faces5-float-2370.json",
    )
    assert "residual-mixture-faces5-float-2370.json" in text
    text = text.replace("2368", "2370")
    compile(text, str(SOURCE), "exec")
    exec(text, {"__name__": "__main__", "__file__": str(SOURCE)})


if __name__ == "__main__":
    main()
