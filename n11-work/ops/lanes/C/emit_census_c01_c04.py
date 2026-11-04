#!/usr/bin/env python3
"""Regenerate EnergyTerminalResidualCensusC01..C04.

Motivation (lane C, part 296): the previous files closed every 100-index block
with a single declaration `interval_cases k <;> rw [..] <;> decide +kernel`.
CI (run 41706645384) reports C01..C04 exit 1 (and every consumer red).  The
dominant risk is that one *declaration* accumulates 100 heavy kernel decisions
(data unfold + 1997-literal paidIDs membership), exceeding the per-declaration
heartbeat budget / memory.  Fix: isolate every single source index in its own
theorem (`mem_iff_id_<id>`), each with its own heartbeat budget, and let each
block lemma delegate to the 100 per-index lemmas via explicit bullets.  The
exported interface (`mem_iff_blockNN`) is unchanged.
"""
import os

ROOT = os.path.join(os.path.dirname(__file__), '..', '..', '..', 'lean', 'N11Formalization')

# Part 301: split every `∪` in the paid-chain value BEFORE deciding.  The
# kernel failure (run 41769569707) is that `decide +kernel` reduced the
# `Finset.union` value `s - t + t` (Mathlib/Data/Multiset/UnionInter.lean:45)
# over the full ~1997-element paid set, ~10^6 diff comparisons per terminal id.
# Rewriting with `Finset.mem_union`/`Finset.mem_insert`/`Finset.mem_singleton`
# first makes every `decide` atom a literal `idsNN` / image membership instead.
PAID_SIMP = [
    'EnergyTerminalBatchB13.paidIDs', 'EnergyTerminalBatchB12.paidIDs',
    'EnergyTerminalBatchB11.paidIDs', 'EnergyTerminalBatchB10.paidIDs',
    'EnergyTerminalBatchB09.paidIDs', 'EnergyTerminalBatchB08.paidIDs',
    'EnergyTerminalBatchB07.paidIDs', 'EnergyTerminalBatchB06.paidIDs',
    'EnergyTerminalBatchB05.paidIDs', 'EnergyTerminalBatchB04.paidIDs',
    'EnergyTerminalBatchB03.paidIDs', 'EnergyTerminalBatchB02.paidIDs',
    'EnergyTerminalBatchB01.paidIDs',
    'Paid16GeneralFirst42.newIDs',
    'Paid16GeneralRemaining210.newIDs',
    'Paid16GeneralNext505.newIDs',
    'Paid16GeneralNext1182.new_mem',
    'Paid16GeneralNext1182S01.newIDs', 'Paid16GeneralNext1182S02.newIDs',
    'Paid16GeneralNext1182S03.newIDs', 'Paid16GeneralNext1182S04.newIDs',
    'Paid16GeneralNext1182S05.newIDs', 'Paid16GeneralNext1182S06.newIDs',
    'Paid16GeneralNext1182S07.newIDs', 'Paid16GeneralNext1182S08.newIDs',
    'Finset.mem_union', 'Finset.mem_insert', 'Finset.mem_singleton', 'not_or',
]
PAID_SIMP_BLOCK = '  simp only [\n' + ',\n'.join(
    '    ' + x for x in PAID_SIMP) + ']'

BLOCK_FILES = {
    'C01': [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48],
    'C02': [1, 5, 9, 13, 17, 21, 25, 29, 33, 37, 41, 45, 49],
    'C03': [2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 42, 46, 50],
    'C04': [3, 7, 11, 15, 19, 23, 27, 31, 35, 39, 43, 47],
}
N = 5011

def ids_of_block(bb):
    return [i for i in range(100 * bb, min(100 * bb + 100, N))]

def emit_part(name, blocks):
    L = []
    L.append('import N11Formalization.EnergyTerminalResidualCensusBase')
    L.append('')
    L.append('/-! Census part %s.  Every single source index has its own'
             ' theorem so no' % name[1:])
    L.append('declaration carries more than one heavy `decide +kernel`; each block')
    L.append('lemma (`mem_iff_blockNN`) delegates to its 100 per-index lemmas via')
    L.append('explicit bullets.  The exported interface is unchanged.')
    L.append('-/')
    L.append('set_option autoImplicit false')
    L.append('namespace N11Formalization.EnergyTerminalResidualCensus')
    L.append('open Finset')
    L.append('noncomputable section')
    L.append('')
    for bb in blocks:
        for i in ids_of_block(bb):
            L.append('theorem mem_iff_id_%04d (n : Fin 5011) (hn : n.val = %d) :'
                     % (i, i))
            L.append('    n \u2208 residualIDs \u2194 n \u2208 EnergyTerminalBatchB13.residualIDs := by')
            L.append('  rcases n with \u27e8k, hk\u27e9')
            L.append('  change k = %d at hn' % i)
            L.append('  subst hn')
            L.append('  rw [EnergyTerminalBatchB13.mem_residualIDs_iff]')
            L.append(PAID_SIMP_BLOCK)
            L.append('  decide +kernel +revert')
            L.append('')
    for bb in blocks:
        lo = 100 * bb
        hi = min(100 * bb + 100, N)
        L.append('theorem mem_iff_block%02d (n : Fin 5011) (hlo : %d \u2264 n.val) (hhi : n.val < %d) :'
                 % (bb, lo, hi))
        L.append('    n \u2208 residualIDs \u2194 n \u2208 EnergyTerminalBatchB13.residualIDs := by')
        L.append('  rcases n with \u27e8k, hk\u27e9')
        L.append('  interval_cases k')
        for i in ids_of_block(bb):
            L.append('  \u00b7 exact mem_iff_id_%04d _ rfl' % i)
        L.append('')
    L.append('end')
    L.append('end N11Formalization.EnergyTerminalResidualCensus')
    return '\n'.join(L) + '\n'

def main():
    total_ids = 0
    for name, blocks in BLOCK_FILES.items():
        txt = emit_part(name, blocks)
        path = os.path.join(ROOT, 'EnergyTerminalResidualCensus%s.lean' % name)
        with open(path, 'w') as f:
            f.write(txt)
        nid = sum(len(ids_of_block(b)) for b in blocks)
        total_ids += nid
        print('%s: blocks=%d ids=%d bytes=%d' % (name, len(blocks), nid, len(txt)))
    assert total_ids == N, total_ids
    print('self-check: total ids =', total_ids)

if __name__ == '__main__':
    main()
