import Class33Core.SecTrees.Q0M2Sec6Base
namespace Class33Core.SecTrees.Q0M2Sec6.P26
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec6
def box : Box := ⟨(7/4 : Rat),(2 : Rat),(3/4 : Rat),(1 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 1 (7/8 : Rat),.S 2 (9/16 : Rat),.L (243741/262144 : Rat) (668527/524288 : Rat) (46555/262144 : Rat) (128297/524288 : Rat),.S 0 (15/8 : Rat),.L (1038013/1048576 : Rat) (1310915/1048576 : Rat) (49601/262144 : Rat) (125739/524288 : Rat),.L (1088003/1048576 : Rat) (1366523/1048576 : Rat) (208083/1048576 : Rat) (262369/1048576 : Rat),.S 2 (9/16 : Rat),.S 1 (15/16 : Rat),.L (1082247/1048576 : Rat) (1400071/1048576 : Rat) (25871/131072 : Rat) (268953/1048576 : Rat),.L (568879/524288 : Rat) (1463309/1048576 : Rat) (217735/1048576 : Rat) (281395/1048576 : Rat),.S 0 (15/8 : Rat),.S 1 (15/16 : Rat),.L (285671/262144 : Rat) (1371431/1048576 : Rat) (218691/1048576 : Rat) (65833/262144 : Rat),.L (1196971/1048576 : Rat) (1432389/1048576 : Rat) (114623/524288 : Rat) (275307/1048576 : Rat),.S 1 (15/16 : Rat),.L (1195709/1048576 : Rat) (1428407/1048576 : Rat) (28625/131072 : Rat) (274523/1048576 : Rat),.L (1251235/1048576 : Rat) (745301/524288 : Rat) (239819/1048576 : Rat) (286777/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec6.P26
