import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P413
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/8 : Rat) (934057/1048576 : Rat) (12453/524288 : Rat) (89165/524288 : Rat),.S 0 (3/2 : Rat),.L (725487/1048576 : Rat) (322749/262144 : Rat) (69121/524288 : Rat) (7737/32768 : Rat),.S 0 (7/4 : Rat),.L (518663/524288 : Rat) (712399/524288 : Rat) (198271/1048576 : Rat) (273813/1048576 : Rat),.S 2 (11/16 : Rat),.L (1169833/1048576 : Rat) (749325/524288 : Rat) (223967/1048576 : Rat) (288365/1048576 : Rat),.L (1216561/1048576 : Rat) (774873/524288 : Rat) (58265/262144 : Rat) (149233/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P413
