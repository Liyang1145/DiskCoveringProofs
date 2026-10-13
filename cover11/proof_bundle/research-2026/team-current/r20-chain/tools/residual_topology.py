"""r20-chain: topology of the residual set  Res = D \\ (union of the 9 ring disks).

Uses a fine polar grid + exact distance tests (not a covering grid: every reported component is
confirmed by exact point tests), to answer: how many connected components does Res have, which
circle arcs bound them, and which points are the extreme vertices?
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT

LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}")
    P("ring order: " + ", ".join(map(str, ring_ids)))

    NT, NR = 4001, 601
    th = np.linspace(0, 2 * np.pi, NT, endpoint=False)
    rr = np.linspace(0, 1, NR)
    T, Rg = np.meshgrid(th, rr, indexing="ij")
    X = Rg * np.cos(T)
    Y = Rg * np.sin(T)
    rho = np.stack([X.ravel(), Y.ravel()], 1)
    d = np.linalg.norm(rho[:, None, :] - ring[None, :, :], axis=2)
    unc = np.all(d > R, axis=1).reshape(NT, NR)
    P(f"\ngrid {NT}x{NR}; uncovered fraction of D = {unc.mean():.9f}")
    area = unc.mean() * np.pi
    P(f"uncovered area ~ {area:.9f}  (pi*R^2 of one disk = {np.pi*R*R:.9f})")

    # connected components on the (theta,r) grid with wrap in theta
    lab = -np.ones_like(unc, dtype=int)
    cur = 0
    for i in range(NT):
        for j in range(NR):
            if not unc[i, j] or lab[i, j] >= 0:
                continue
            stack = [(i, j)]
            lab[i, j] = cur
            while stack:
                a, b = stack.pop()
                for da, db in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                    na, nb = (a + da) % NT, b + db
                    if 0 <= nb < NR and unc[na, nb] and lab[na, nb] < 0:
                        lab[na, nb] = cur
                        stack.append((na, nb))
            cur += 1
    P(f"number of connected components (grid resolution) = {cur}")
    for k in range(cur):
        m = lab == k
        pts = rho.reshape(NT, NR, 2)[m]
        P(f"  component {k}: {m.sum()} grid points, area ~ {m.mean()*np.pi:.6f},"
          f" |x| in [{np.linalg.norm(pts,axis=1).min():.6f},{np.linalg.norm(pts,axis=1).max():.6f}],"
          f" azimuth in [{np.degrees(np.arctan2(pts[:,1],pts[:,0])).min():.2f},"
          f"{np.degrees(np.arctan2(pts[:,1],pts[:,0])).max():.2f}] deg")
        for lab_, H in (("A", HA), ("B", HB)):
            dd = np.linalg.norm(pts - H, axis=1)
            P(f"      hub {lab_}: max |H-x| over component = {dd.max():.9f}"
              f"   R - that = {R - dd.max():+.6e}")

    (OUT / "residual_topology.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "residual_topology.txt"))


if __name__ == "__main__":
    main()
