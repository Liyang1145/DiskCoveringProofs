import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P313
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (3/16 : Rat) (865845/1048576 : Rat) (37363/1048576 : Rat) (82597/524288 : Rat),.S 0 (3/2 : Rat),.L (645663/1048576 : Rat) (1169361/1048576 : Rat) (122957/1048576 : Rat) (55969/262144 : Rat),.S 0 (7/4 : Rat),.L (908427/1048576 : Rat) (160567/131072 : Rat) (86695/524288 : Rat) (123161/524288 : Rat),.S 2 (9/16 : Rat),.L (256979/262144 : Rat) (668527/524288 : Rat) (196451/1048576 : Rat) (128297/524288 : Rat),.L (268099/262144 : Rat) (1386335/1048576 : Rat) (205059/1048576 : Rat) (16641/65536 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P313
