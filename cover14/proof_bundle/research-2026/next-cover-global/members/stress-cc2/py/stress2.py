"""stress2.py -- clean-room stress kernel (mpmath) for the capped-simplex KKT network.

Method objects (all of this is conditional on the method note; nothing here is a proof):
  nodes: anchors (fixed S^1 points) + sites (free planar nodes) + witnesses (fixed points)
  edges: e=(u,v) with weight alpha_e >= 0
  equilibrium at free (site) nodes:  sum_e alpha_e * unit(z_other - z_site) = 0
  anchor torque (per unit tangential displacement of anchor i, theta = polar angle):
      tau_i = 2 * sum_{e at i} alpha_e * cross(d_e, t_i),  d_e = unit(z_other - a_i),
      t_i = (-sin th_i, cos th_i)
      [d|b-a(th)|/dth = cross(d,t), and edge energy is quadratic in the side length]
  gap derivative: g_k = sum_{i>k} tau_i  (cyclic labels 0..na-1)
  capped simplex (min form): g_k = c (k in I), g_k <= c (k in A).
"""
import numpy as np
import mpmath as mp


def unit(v):
    return (v[0] / mp.sqrt(v[0] ** 2 + v[1] ** 2), v[1] / mp.sqrt(v[0] ** 2 + v[1] ** 2))


def build_edges(anchors, sites, witness_pos, faces, owners):
    na, ns = len(anchors), len(sites)
    E = []
    for i, ss in enumerate(owners):
        for s in ss:
            E.append((i, na + s))
    for k, f in enumerate(faces):
        for s in f:
            E.append((na + ns + k, na + s))
    return E


def all_dirs(anchors, sites, witness_pos, E):
    Z = list(anchors) + list(sites) + list(witness_pos)
    return [unit((Z[v][0] - Z[u][0], Z[v][1] - Z[u][1])) for (u, v) in E]


def A_matrix(anchors, sites, witness_pos, E, dirs):
    na, ns = len(anchors), len(sites)
    A = np.zeros((2 * ns, len(E)))
    for e, (u, v) in enumerate(E):
        dx, dy = float(dirs[e][0]), float(dirs[e][1])
        for node, sgn in ((u, -1.0), (v, +1.0)):
            if na <= node < na + ns:
                r = node - na
                A[2 * r, e] += sgn * dx
                A[2 * r + 1, e] += sgn * dy
    return A


def taus(anchors, E, dirs, alpha):
    """tau_i in mp (alpha: mp list)."""
    na = len(anchors)
    tau = [mp.mpf(0)] * na
    for e, (u, v) in enumerate(E):
        d = dirs[e]
        for node in (u, v):
            if node < na:
                a = anchors[node]
                t = (-a[1], a[0])
                cross = d[0] * t[1] - d[1] * t[0]
                tau[node] += 2 * alpha[e] * cross
    return tau


def gaps_from_taus(tau):
    """g_k = sum_{i>k} tau_i, k=0..na-1 ; g_{na-1} = 0 identically."""
    na = len(tau)
    g = [mp.mpf(0)] * na
    for k in range(na):
        g[k] = sum(tau[k + 1:])
    return g
