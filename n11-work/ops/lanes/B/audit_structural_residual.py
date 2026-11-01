#!/usr/bin/env python3
"""Source audit for the structural 373-residual wrapper; not a kernel check."""
import hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
LEAN=ROOT/'n11-work'/'lean'
TARGETS=HERE/'TARGETS.txt'
REPORT=HERE/'audit_structural_residual-report.json'
S='N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructural'
D='N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus'
M=S+'Main'
BADMOD='N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus'
IMPORT=re.compile(r'^import\s+(N11Formalization(?:\.\w+)+)\s*$',re.M)
BANNED=('sorry','admit','native_decide','ofReduceBool','implemented_by','maxHeartbeats 0','maxRecDepth')
ENDPOINTS={D:('residual373_card','residualIDs_eq_residual373','residualIDs_card'),S:('residualIDs_eq_residual373','residual373_card','residualIDs_card','remaining_of_residual373_radius_certificates','b13_remaining_of_residual373_radius_certificates'),M:('main_of_residual373_radius_certificates_and_seven_classes','full_disk_bound_of_residual373_radius_certificates_and_seven_classes','main_of_residual373_packet_producers_and_seven_classes','full_disk_bound_of_residual373_packet_producers_and_seven_classes')}
def path(m): return LEAN.joinpath(*m.split('.')).with_suffix('.lean')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest().upper()
def closure(m, depth=2):
    seen={m}; frontier={m}
    for _ in range(depth):
        nxt={y for x in frontier for y in IMPORT.findall(path(x).read_text())}-seen
        seen |= nxt; frontier=nxt
    return seen
fails=[]; targets=[x.strip() for x in TARGETS.read_text().splitlines() if x.strip() and not x.lstrip().startswith('#')]
for m in (D,S,M):
    if targets.count(m)!=1: fails.append(f'{m} must occur exactly once')
if D not in targets or S not in targets or M not in targets or not (targets.index(D)<targets.index(S)<targets.index(M)): fails.append('Structural must precede StructuralMain')
texts={m:path(m).read_text() for m in (D,S,M)}
for m,text in texts.items():
    for tok in BANNED:
        if re.search(r'(?<![\w.])'+re.escape(tok)+r'(?![\w])',text): fails.append(f'{m} contains {tok}')
    for e in ENDPOINTS[m]:
        if not re.search(r'\btheorem\s+'+re.escape(e)+r'\b',text): fails.append(f'{m} lacks {e}')
cl=closure(S)
if BADMOD in cl: fails.append('wrapper closure imports conflicted literal census')
if set(IMPORT.findall(texts[S]))!={'N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual',D}: fails.append('unexpected Structural direct imports')
if set(IMPORT.findall(texts[M]))!={S,'N11Formalization.EnergyTerminalBatchB13Main'}: fails.append('unexpected StructuralMain direct imports')

# The generated census pays cardinality through four literal chunks and pays
# equality through 502 ten-index subtheorems dispatched by 51 contiguous blocks.
# Check that the checked-in source still has exactly that cover; a missing or
# duplicated block would otherwise look like harmless generated code.
chunks={int(i):{int(x) for x in re.findall(r'\d+',body)} for i,body in re.findall(
    r'^def chunk(\d+) : Finset \(Fin 5011\) := \{([^}]*)\}',texts[D],re.M)}
card_lines={int(i):int(n) for i,n in re.findall(
    r'^theorem chunk(\d+)_card : chunk\d+\.card = (\d+) := by decide \+kernel$',texts[D],re.M)}
subs=[int(i) for i in re.findall(r'^private theorem mem_sub_(\d{3}) ',texts[D],re.M)]
blocks=[int(i) for i in re.findall(r'^private theorem mem_iff_block(\d{2}) ',texts[D],re.M)]
expected=[100,100,100,73]
if sorted(chunks)!=list(range(4)): fails.append('literal chunks are not 0..3')
if [len(chunks.get(i,set())) for i in range(4)]!=expected: fails.append('literal chunk cardinalities differ from [100,100,100,73]')
if any(not 0<=x<5011 for c in chunks.values() for x in c): fails.append('literal chunk has out-of-range Fin 5011 id')
if any(chunks[i]&chunks[j] for i in range(4) for j in range(i+1,4)): fails.append('literal chunks overlap')
if card_lines!={0:100,1:100,2:100,3:73}: fails.append('kernel cardinality theorem coverage differs')
if subs!=list(range(502)): fails.append('ten-index subtheorem cover is not exactly 000..501')
if blocks!=list(range(51)): fails.append('hundred-index dispatch cover is not exactly 00..50')
if len(re.findall(r'\.symm$',texts[D],re.M))<51: fails.append('root equality dispatch has fewer than 51 branches')
result={'scope':'source/import/cover audit only; not a Lean kernel check and pays no radius','ok':not fails,'failures':fails,'closure_size':len(cl),'conflicted_module_absent':BADMOD not in cl,'census_shape':{'chunks':[len(chunks.get(i,set())) for i in range(4)],'subtheorems':len(subs),'blocks':len(blocks)},'sha256':{str(path(m).relative_to(ROOT)):digest(path(m)) for m in (S,M)},'targets_sha256':digest(TARGETS)}
REPORT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
raise SystemExit(0 if result['ok'] else 1)
