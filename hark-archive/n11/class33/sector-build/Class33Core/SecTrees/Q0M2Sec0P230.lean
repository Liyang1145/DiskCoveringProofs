import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P230
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(3/8 : Rat),(7/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/2 : Rat) (951605/1048576 : Rat) (99765/1048576 : Rat) (90857/524288 : Rat),.S 0 (3/2 : Rat),.L (97001/131072 : Rat) (295775/262144 : Rat) (147931/1048576 : Rat) (56637/262144 : Rat),.S 0 (7/4 : Rat),.L (7637/8192 : Rat) (1275079/1048576 : Rat) (186717/1048576 : Rat) (122237/524288 : Rat),.L (1062913/1048576 : Rat) (685773/524288 : Rat) (203223/1048576 : Rat) (131677/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P230
