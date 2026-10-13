# Unsealed all-face structural diagnostic: structured slack DATA decoder

Observed2026-10-11 22:56 Asia/Shanghai. First actual structural diagnostic
TERMINAL1; target report absent;no proof/acceptance/payment was produced.
Failed unsealed diagnostic SHA:
b795bbe633f5807ff386e34008dd59b07158a46bfde942ef79c08321ac465cd6.

Read-only inspection showed SYSTEM.slack_faces is a list of structured
records with keys face and floating_squared_slack,not a plain face list.
The old new-driver decoder accidentally interpreted dictionary keys as
vertex triples and correctly failed its classification-union check.
This was a new diagnostic decoding error,not contradictory source faces.

Only the UNSEALED diagnostic is repaired to require the exact structured
record keys and decode item.face. Floating slack numbers remain DATA only,
not radius or geometric inequality proofs. Exact native-face bijection,
complete34face terminal reconstruction,original92edge retention and distinct
new witness grounding checks are unchanged. The overlapping-classification
negative test uses a well-formed structured record,so it tests real overlap.

No arithmetic resource,accepted original model,old reference edges/current
source/history/forest,running job or frozen checker was modified. Keep the
original terminal traceback and this recovery evidence. Rerun only the new
failed structural diagnostic to the still-absent fresh target.
