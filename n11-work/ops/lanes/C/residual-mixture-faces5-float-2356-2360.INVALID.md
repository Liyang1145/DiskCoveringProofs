# INVALID report

`residual-mixture-faces5-float-2356-2360.json` was produced by a search that
maximized gain, but `PaidCellCertificateMCap.not_valid_of_frozen_cap` requires
`F0 + gain < T^2`. Its `PASS` labels are therefore false. Preserve the JSON as
an audit artifact, but do not emit witnesses or Lean modules from it. See
`NOTES.md`, part 186, for the corrected minimization criterion.
