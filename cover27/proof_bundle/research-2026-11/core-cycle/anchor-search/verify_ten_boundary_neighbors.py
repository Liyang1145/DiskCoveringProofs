"""Use the fifth inner norm to require ten outer-adjacent inner centers."""
from polar_tables import CORE_CAPS, R, TURN, beta, machins_formula

LOWER=901_410_000


def verify():
    machins_formula()
    s=LOWER-R
    v=CORE_CAPS[4]
    if s<=R or not s-R<v or v*v>s*s+R*R:
        raise ValueError("bad first-exit radius or fifth inner norm")
    general=beta(s,s-R,s+R)
    if 16*general>=TURN:
        raise ValueError("eight inner boundary neighbors may suffice")
    # Among any nine of the 13 inner centers, one satisfies the
    # fifth-smallest norm bound. At these norms the angular projection
    # of the disk beyond radius s is bounded by its arc on radius s.
    small=beta(s,s-R,v)
    if 2*(8*general+small)>=TURN:
        raise ValueError("nine inner boundary neighbors may suffice")
    print(f"PASS B=14: D1 >= {LOWER}/1e9 requires at least ten inner boundary neighbors.")


if __name__=="__main__":
    verify()
