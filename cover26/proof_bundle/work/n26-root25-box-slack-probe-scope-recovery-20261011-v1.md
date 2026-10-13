# Actual box-slack probe scope failure and unsealed-producer repair

Observed2026-10-11 21:12 Asia/Shanghai. Original session76854 TERMINAL1.
Fresh diagnosis target remained absent; no acceptance or payment was created.

Original unsealed producer SHA:
3e9fafb666bf5ba1fd47bb26dc292c6050c1cdcdf2ebe44376b4f441793a31e3.
New pure arithmetic checker SHA:
c5e0f5e5322697b9c9b25ba9fa5486a8ceb246fb18dcff54053cdae49093cd6c.

The exact checker rejected the attempted known-tiny positive control because
the producer's target-only box-slack intervals did not contain the entire
different tiny control box. This is a valid domain rejection, not a false
geometric exclusion or a checker defect. The failed producer did not publish
its report. Preserve the actual terminal traceback and this diagnosis.

Only the UNSEALED producer is repaired: explicitly choose each box-slack
interval to contain BOTH the actual target interval and known tiny control
interval. The checker still requires exact containment, nonnegative weights
and all original constant/gradient/curvature charges. The target Hessian
domain is not enlarged or replaced, and the tiny test separately reconstructs
its own exact Hessian.

No old executor, source root, bound historical forest, fixed arithmetic
resource, verified receipt or running process was modified. The pure new
checker is unchanged. All scope flags remain verified=false and zero payments.
Rerun only this failed new diagnostic to its still-absent fresh target.
