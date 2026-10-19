import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P477
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(31/32 : Rat),(23/32 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (61/64 : Rat),.S 2 (47/64 : Rat),.S 1 (121/128 : Rat),.L (836543/524288 : Rat) (1763413/1048576 : Rat) (40371/131072 : Rat) (341029/1048576 : Rat),.L (1680989/1048576 : Rat) (1771671/1048576 : Rat) (5071/16384 : Rat) (171343/524288 : Rat),.S 1 (121/128 : Rat),.L (1688897/1048576 : Rat) (889813/524288 : Rat) (163061/524288 : Rat) (172141/524288 : Rat),.L (848397/524288 : Rat) (1787885/1048576 : Rat) (327699/1048576 : Rat) (86485/262144 : Rat),.S 2 (47/64 : Rat),.S 1 (123/128 : Rat),.L (844447/524288 : Rat) (222491/131072 : Rat) (163061/524288 : Rat) (344343/1048576 : Rat),.L (848401/524288 : Rat) (1788185/1048576 : Rat) (81925/262144 : Rat) (21625/65536 : Rat),.S 1 (123/128 : Rat),.L (1704693/1048576 : Rat) (898071/524288 : Rat) (82319/262144 : Rat) (347599/1048576 : Rat),.L (428149/262144 : Rat) (1804399/1048576 : Rat) (330855/1048576 : Rat) (174629/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P477
