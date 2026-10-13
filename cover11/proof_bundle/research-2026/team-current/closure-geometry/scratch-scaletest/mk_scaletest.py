import io

src = io.open('certify_shared_moments_dense.py', encoding='utf-8').read()
for t, tag in [(0.25, 'q'), (0.5, 'h')]:
    s = src.replace('R=iv.mpf(19)/50', 'R=iv.mpf(19)/50*iv.mpf(%r)' % t)
    s = s.replace("shared_moment_dense_certificate_{start}_{span}.json",
                  "SCALETEST_%s_{start}_{span}.json" % tag)
    s = s.replace("shared_moment_dense_certificate_{start}_{span}.partial.json",
                  "SCALETEST_%s_{start}_{span}.partial.json" % tag)
    io.open('scaletest_%s.py' % tag, 'w', encoding='utf-8').write(s)
    print('wrote scaletest_%s.py  R = 19/50 * %s' % (tag, t))
