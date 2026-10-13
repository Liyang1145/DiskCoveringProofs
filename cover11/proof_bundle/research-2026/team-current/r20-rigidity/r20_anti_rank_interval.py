"""SUPERSEDED (2026-09-25) — do not run.

This was the first attempt at an interval anti-rank instrument.  It is broken: it stores mpmath
`iv.mpf` values inside `mp.matrix` (the mpf-context matrix converts to mpf and raises
"can only create mpf from zero-width interval"), and it predates the corrected kernel/quotient
construction.

Successor (rank *and* the anti-quotient PD certificate, interval Gauss-Jordan from an explicit
8x8 minor, integer anti basis with diagonal Gram, Sylvester on exact endpoints):

    r20_anti_block_interval.py     (box mode: certificate;  R20_POINT=1: point-mode controls)

See `R20-PHYSICAL-KKT-KERNEL.md` and STATUS W15.  Kept only as a record of the failed instrument.
"""
