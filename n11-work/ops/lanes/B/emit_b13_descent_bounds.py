from pathlib import Path
root = Path('n11-work/lean/N11Formalization')
lines = []
lines += [f'import N11Formalization.Paid16GeneralG{i:02d}' for i in range(3,13)]
lines += ['import N11Formalization.EnergyTerminalBatchB10',
          'import N11Formalization.Paid16GeneralRemaining210', '', '/-! Bounded descent facts used by B13. Each kernel decision covers at most',
          '58 literal ids; the 210-id remainder is assembled from ten 21-id blocks. -/',
          'set_option autoImplicit false',
          'namespace N11Formalization.EnergyTerminalBatchB13DescentBounds', 'open Finset', 'noncomputable section', '']
for i in range(3,13):
    G = f'Paid16GeneralG{i:02d}'
    lines += [f'private theorem g{i:02d}_lt (n : Fin 5011) (hn : n ∈ {G}.newIDs) :',
              f'    n.val < 2565 := by',
              f'  have h : ∀ m ∈ {G}.newIDs, m.val < 2565 := by decide +kernel',
              f'  exact h n hn', '']
lines += ['theorem b09_lt (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB09.paidIDs) :',
          '    n.val < 2565 := by',
          '  have h : ∀ m ∈ EnergyTerminalBatchB09.paidIDs, m.val < 2565 := by',
          '    decide +kernel',
          '  exact h n hn', '',
          'theorem first42_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralFirst42.newIDs) :',
          '    n.val < 2565 := by',
          '  have h : ∀ m ∈ Paid16GeneralFirst42.newIDs, m.val < 2565 := by',
          '    decide +kernel',
          '  exact h n hn', '',
          'theorem b10_lt (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB10.paidIDs) :',
          '    n.val < 2565 := by',
          '  rw [EnergyTerminalBatchB10.paidIDs] at hn',
          '  rcases Finset.mem_union.mp hn with hn | hn',
          '  · exact b09_lt n hn',
          '  · exact first42_lt n hn', '',
          'theorem remaining210_lt (n : Fin 5011)',
          '    (hn : n ∈ Paid16GeneralRemaining210.newIDs) : n.val < 2565 := by',
          '  have hm : n ∈ Paid16GeneralG03.newIDs ∨',
          '      n ∈ Paid16GeneralG04.newIDs ∨',
          '      n ∈ Paid16GeneralG05.newIDs ∨',
          '      n ∈ Paid16GeneralG06.newIDs ∨',
          '      n ∈ Paid16GeneralG07.newIDs ∨',
          '      n ∈ Paid16GeneralG08.newIDs ∨',
          '      n ∈ Paid16GeneralG09.newIDs ∨',
          '      n ∈ Paid16GeneralG10.newIDs ∨',
          '      n ∈ Paid16GeneralG11.newIDs ∨',
          '      n ∈ Paid16GeneralG12.newIDs := by',
          '    simpa only [Paid16GeneralRemaining210.newIDs, Finset.mem_union] using hn',
          '  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn']
for i in range(3,13):
    lines += [f'  · exact g{i:02d}_lt n hn']
lines += ['', 'end', 'end N11Formalization.EnergyTerminalBatchB13DescentBounds',
          '#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.b10_lt',
          '#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.remaining210_lt',
          '#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.b10_lt',
          '#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.remaining210_lt', '']
(root / 'EnergyTerminalBatchB13DescentBounds.lean').write_text('\n'.join(lines))
print('wrote', root / 'EnergyTerminalBatchB13DescentBounds.lean')
