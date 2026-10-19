import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P142
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(27/32 : Rat),(7/8 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 2 (9/32 : Rat),.L (978867/1048576 : Rat) (586915/524288 : Rat) (186973/1048576 : Rat) (224745/1048576 : Rat),.L (499221/524288 : Rat) (1200573/1048576 : Rat) (95377/524288 : Rat) (57487/262144 : Rat),.S 2 (9/32 : Rat),.S 0 (19/8 : Rat),.L (258957/262144 : Rat) (591443/524288 : Rat) (197981/1048576 : Rat) (113253/524288 : Rat),.L (1054409/1048576 : Rat) (601601/524288 : Rat) (25197/131072 : Rat) (57615/262144 : Rat),.S 0 (19/8 : Rat),.L (530563/524288 : Rat) (1210409/1048576 : Rat) (202877/1048576 : Rat) (231863/1048576 : Rat),.L (1081519/1048576 : Rat) (1232457/1048576 : Rat) (206827/1048576 : Rat) (236159/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P142
