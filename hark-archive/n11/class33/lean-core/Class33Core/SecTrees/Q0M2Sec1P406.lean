import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P406
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(3/2 : Rat),(13/8 : Rat),(7/8 : Rat),(29/32 : Rat),(15/16 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (31/32 : Rat),.S 1 (57/64 : Rat),.S 0 (25/16 : Rat),.L (643765/524288 : Rat) (86491/65536 : Rat) (123453/524288 : Rat) (132885/524288 : Rat),.L (332411/262144 : Rat) (1426971/1048576 : Rat) (127571/524288 : Rat) (274241/1048576 : Rat),.S 0 (25/16 : Rat),.L (649221/524288 : Rat) (1394823/1048576 : Rat) (124519/524288 : Rat) (267923/1048576 : Rat),.S 2 (61/64 : Rat),.L (1340947/1048576 : Rat) (1425893/1048576 : Rat) (257355/1048576 : Rat) (274029/1048576 : Rat),.L (1352565/1048576 : Rat) (1438349/1048576 : Rat) (16227/65536 : Rat) (276479/1048576 : Rat),.S 1 (57/64 : Rat),.S 0 (25/16 : Rat),.L (655211/524288 : Rat) (1408559/1048576 : Rat) (251381/1048576 : Rat) (270621/1048576 : Rat),.L (1353181/1048576 : Rat) (726143/524288 : Rat) (32469/131072 : Rat) (279223/1048576 : Rat),.S 0 (25/16 : Rat),.L (1321111/1048576 : Rat) (1419337/1048576 : Rat) (7921/32768 : Rat) (272739/1048576 : Rat),.L (1364281/1048576 : Rat) (365873/262144 : Rat) (32741/131072 : Rat) (281431/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P406
