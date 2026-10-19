import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P107
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(29/32 : Rat),(15/16 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 2 (5/32 : Rat),.S 0 (9/4 : Rat),.L (243185/262144 : Rat) (1135941/1048576 : Rat) (185791/1048576 : Rat) (217383/1048576 : Rat),.L (995589/1048576 : Rat) (1164987/1048576 : Rat) (190203/1048576 : Rat) (111513/524288 : Rat),.S 0 (9/4 : Rat),.L (61799/65536 : Rat) (1161251/1048576 : Rat) (23611/131072 : Rat) (55575/262144 : Rat),.S 1 (59/64 : Rat),.L (1016815/1048576 : Rat) (1178771/1048576 : Rat) (759/4096 : Rat) (112853/524288 : Rat),.L (1032913/1048576 : Rat) (298821/262144 : Rat) (197417/1048576 : Rat) (228919/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P107
