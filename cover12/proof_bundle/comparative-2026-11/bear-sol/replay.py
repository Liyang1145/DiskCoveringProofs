"""Replay all checks used in proof.md, from the task directory."""

if not __debug__:
    raise SystemExit("Run without -O: the proof checks use assertions.")

from verify_arcs import checks as arcs
from verify_local import checks as local
from verify_nine_potential import proof as potential
from verify_nine_structure import tests as structure
from verify_ten import CERT, replay as ten
from verify_upper import checks as upper


def main():
    upper()
    arcs()
    local()
    structure()
    potential()
    ten(CERT)
    print("PASS: construction and both global lower-bound cases")


if __name__ == "__main__":
    main()
