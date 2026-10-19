import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P78
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (5/8 : Rat) (892747/1048576 : Rat) (31203/262144 : Rat) (170371/1048576 : Rat),.S 0 (3/2 : Rat),.L (723915/1048576 : Rat) (247779/262144 : Rat) (137941/1048576 : Rat) (47335/262144 : Rat),.S 1 (27/32 : Rat),.L (783525/1048576 : Rat) (1059385/1048576 : Rat) (74687/524288 : Rat) (202541/1048576 : Rat),.L (815493/1048576 : Rat) (1092379/1048576 : Rat) (155513/1048576 : Rat) (52233/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P78
