import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P190
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(5/16 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/2 : Rat) (901133/1048576 : Rat) (99765/1048576 : Rat) (85993/524288 : Rat),.S 0 (3/2 : Rat),.L (727635/1048576 : Rat) (1099611/1048576 : Rat) (69327/524288 : Rat) (105167/524288 : Rat),.S 0 (7/4 : Rat),.L (896833/1048576 : Rat) (147417/131072 : Rat) (171157/1048576 : Rat) (28227/131072 : Rat),.L (969435/1048576 : Rat) (631663/524288 : Rat) (185153/1048576 : Rat) (60545/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P190
