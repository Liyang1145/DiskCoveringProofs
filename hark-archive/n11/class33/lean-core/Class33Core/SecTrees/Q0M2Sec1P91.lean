import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P91
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(1 : Rat),(3/2 : Rat),(15/16 : Rat),(1 : Rat),(1/4 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 1 (31/32 : Rat),.S 0 (5/4 : Rat),.S 2 (5/16 : Rat),.L (811157/1048576 : Rat) (1020121/1048576 : Rat) (19335/131072 : Rat) (194945/1048576 : Rat),.L (397961/524288 : Rat) (1020139/1048576 : Rat) (75877/524288 : Rat) (48737/262144 : Rat),.S 2 (5/16 : Rat),.L (875717/1048576 : Rat) (551143/524288 : Rat) (41773/262144 : Rat) (210853/1048576 : Rat),.L (877281/1048576 : Rat) (279503/262144 : Rat) (167393/1048576 : Rat) (213903/1048576 : Rat),.S 0 (5/4 : Rat),.S 2 (5/16 : Rat),.L (842387/1048576 : Rat) (262959/262144 : Rat) (160681/1048576 : Rat) (201079/1048576 : Rat),.S 0 (9/8 : Rat),.L (829749/1048576 : Rat) (998407/1048576 : Rat) (39563/262144 : Rat) (47687/262144 : Rat),.L (435637/524288 : Rat) (1046523/1048576 : Rat) (166237/1048576 : Rat) (200051/1048576 : Rat),.S 2 (5/16 : Rat),.L (906725/1048576 : Rat) (141773/131072 : Rat) (86531/524288 : Rat) (108521/524288 : Rat),.L (907419/1048576 : Rat) (287355/262144 : Rat) (43299/262144 : Rat) (220001/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P91
