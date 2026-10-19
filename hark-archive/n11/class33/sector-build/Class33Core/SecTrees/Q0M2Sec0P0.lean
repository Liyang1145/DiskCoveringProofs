import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P0
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(314159265358979323847/100000000000000000000 : Rat),(0 : Rat),(1/4 : Rat),(0 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 2 (1/4 : Rat),.L (0 : Rat) (146543/262144 : Rat) (0 : Rat) (3487/32768 : Rat),.S 1 (1/8 : Rat),.L (1/8 : Rat) (46341/65536 : Rat) (12453/524288 : Rat) (17663/131072 : Rat),.L (0 : Rat) (839271/1048576 : Rat) (0 : Rat) (160083/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P0
