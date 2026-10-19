import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P85
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (9/16 : Rat) (870471/1048576 : Rat) (112281/1048576 : Rat) (41521/262144 : Rat),.S 0 (3/2 : Rat),.L (699805/1048576 : Rat) (31325/32768 : Rat) (133321/1048576 : Rat) (5985/32768 : Rat),.L (790263/1048576 : Rat) (1134069/1048576 : Rat) (150667/1048576 : Rat) (54255/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P85
