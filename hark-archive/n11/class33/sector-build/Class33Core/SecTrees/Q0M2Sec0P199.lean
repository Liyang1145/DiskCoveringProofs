import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P199
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (5/8 : Rat) (489519/524288 : Rat) (31203/262144 : Rat) (187007/1048576 : Rat),.S 0 (3/2 : Rat),.L (12575/16384 : Rat) (572603/524288 : Rat) (153459/1048576 : Rat) (109591/524288 : Rat),.S 0 (7/4 : Rat),.L (469919/524288 : Rat) (1213671/1048576 : Rat) (179443/1048576 : Rat) (116249/524288 : Rat),.L (999717/1048576 : Rat) (1286609/1048576 : Rat) (23875/131072 : Rat) (246727/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P199
