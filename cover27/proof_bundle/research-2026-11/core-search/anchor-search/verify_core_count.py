"""Exclude eleven or twelve outer disks in the auxiliary thirteen-disk cover."""
from polar_tables import SCALE, TURN, beta
from weighted_rings import verify_weighted_rings

Q=342_000_000
CAP=SCALE-Q


def verify():
    if 18*beta(SCALE,CAP,SCALE,Q)>=TURN:
        raise ValueError("nine boundary disks may suffice")
    cases=(
        (
            ((328,162946),(356,146285),(420,82696),(500,74207),(1000,533866)),
            ((11,CAP,SCALE,".187"),(2,0,CAP,".514")),
        ),
        (
            ((369,42),(1000,58)),
            ((12,CAP,SCALE,".210"),(1,0,3*Q-SCALE,"0")),
        ),
    )
    for weights,classes in cases:
        rings=[(r*10**6,w) for r,w in weights]
        boxes=verify_weighted_rings(Q,rings,classes)
        print(f"PASS: the thirteen-disk cover cannot have {classes[0][0]} norms >= 1-0.342 ({boxes}).")

if __name__=="__main__":
    verify()
