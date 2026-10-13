from mpmath import mp, sin, cos, acos, sqrt, pi, mpf, atan2
mp.dps = 30

# Set up the true geometry.
# c1, c2 are the two boundary neighbors; the hub wedge is the set of points
# equidistant-in-angle from c1,c2, i.e. the "inward" wedge at the origin
# between angles (alpha+2b1) and (alpha+pi-2b2) for the cone-frame direction.
# Instead of guessing, we do it exactly:
#   - the hub lies in direction u (unit) with |hub|=rho;
#   - constraints are |hub - C_j| <= r for the two face disks (centers C_j)
#   - and the wedge condition: the apex-angle condition at the hub, which for
#     the boundary chart reduces to delta in [-b2, b1].
# We therefore build the wedge in (v,t) coordinates as the region between
# the two half-plane tangent conditions that bound the face disks THROUGH THE
# ORIGIN, which are the two "rays" of the hub cone.

def centers(r, b1, b2):
    C1 = (r*sin(2*b1),  2*r*sin(b1)**2)
    C2 = (r*sin(2*b2), -2*r*sin(b2)**2)
    return C1, C2

def scan(r, b1, b2, what='far'):
    s = 1-r
    C1, C2 = centers(r, b1, b2)
    # the apex direction of the cone: hub direction is at angle pi+2b1 (opposite ray)
    # and the wedge in the (v,t) plane is the image of delta in [-b2,b1] under the frame
    # We reconstruct the frame from the two cone rays: e1 at angle 2b1, e2 at angle pi-2b2.
    # hub = -(cos b1 e1 + cos b2 e2)/sin(b1+b2)... simpler: parametrize by delta with the
    # polar relation from the file: rho = s cos(delta) +- sqrt((1-r)^2 - s^2 sin^2 delta).
    out = []
    for i in range(0, 401):
        d = -b2 + (b1+b2)*mpf(i)/400
        # hub direction in the XY plane: at angle pi + 2*b1 - delta?  Use the chart:
        # X = rho * cos(pi + 2b1 - delta) ... but the (v,t) chart is what matters.
        # chart: the file's boundary chart.  Use the two conditions directly:
        disc = s*s - s*s*sin(d)**2
        if disc < 0: continue
        rho_m = s*cos(d) - sqrt(max(disc, 0))
        rho_p = s*cos(d) + sqrt(max(disc, 0))
        for tag, rho in (('near', rho_m), ('far', rho_p)):
            if rho <= 0: continue
            # CHART (from the file): v = rho cos delta, t = rho sin delta
            v = rho*cos(d); t = rho*sin(d)
            D1 = (v-C1[0])**2 + (t-C1[1])**2 <= r*r + mpf('1e-20')
            D2 = (v-C2[0])**2 + (t-C2[1])**2 <= r*r + mpf('1e-20')
            if D1 and D2:
                out.append((tag, d, v, t, rho))
    return out

r = mpf('0.38')
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), mpf('1.2')), (mpf('1.18'), mpf('1.18'))]:
    got = scan(r, b1, b2)
    far = [g for g in got if g[0] == 'far']
    near = [g for g in got if g[0] == 'near']
    print("b1=%.4f b2=%.4f: feasible near=%d far=%d" % (b1, b2, len(near), len(far)))
    if far:
        print("   far example: delta=%.6f v=%.6f t=%.6f rho=%.6f" % far[0][1:])
    if near:
        print("   near example: delta=%.6f v=%.6f t=%.6f rho=%.6f" % near[0][1:])
