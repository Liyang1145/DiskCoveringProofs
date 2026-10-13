import io

src = io.open('certify_shared_moments_dense.py', encoding='utf-8').read()
src0 = io.open('certify_q0_moments.py', encoding='utf-8').read()
for name, s0 in [('q1', src), ('q0', src0)]:
    for t, tag in [(0.125, 'e'), (0.05, 'f')]:
        s = s0.replace('R=iv.mpf(19)/50', 'R=iv.mpf(19)/50*iv.mpf(%r)' % t)
        if name == 'q1':
            s = s.replace("shared_moment_dense_certificate_{start}_{span}.json",
                          "SCALETEST_%s_{start}_{span}.json" % tag)
            s = s.replace("shared_moment_dense_certificate_{start}_{span}.partial.json",
                          "SCALETEST_%s_{start}_{span}.partial.json" % tag)
        else:
            s = s.replace("q0_moment_dual_certificate_{start}_{span}.json",
                          "SCALETEST_%s_{start}_{span}.json" % tag)
            s = s.replace("q0_moment_dual_certificate_{start}_{span}.partial.json",
                          "SCALETEST_%s_{start}_{span}.partial.json" % tag)
        io.open('scaletest_%s_%s.py' % (name, tag), 'w', encoding='utf-8').write(s)
        print('wrote scaletest_%s_%s.py  (R = 19/50 * %s)' % (name, tag, t))
