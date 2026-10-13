# Independent polynomial-test comparison recovery

Observed 2026-10-12 04:36:38 Asia/Shanghai.

The first newly written algebraic control invocation terminated1 at the
independent `positive-a` comparison. The primary exact identity gate had
already passed, but no certificate/control file was written.

Read-only diagnosis reconstructed the coordinate-norm expression independently:
its difference from the certificate residual was exactly0, and the resulting
polynomial's is_zero property was true. SymPy's zero polynomial over QQ was
not object-equal to the default zero polynomial over ZZ. The test compared
those coefficient-domain-tagged objects, giving a false mismatch.

Fix ONLY the new unbound independent tester to check the expanded difference
polynomial's exact is_zero property. No algebraic expression, inequality,
hypothesis, equality owner, sign case, frozen verifier, source, receipt or
geometry flag changes. No prior result is promoted. Retain this failure record
and rerun the actual tests with all corruption controls.
