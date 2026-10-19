import Class33Core.SecTrees.Q0M2Sec5Base
namespace Class33Core.SecTrees.Q0M2Sec5.P23
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec5
def box : Box := ⟨(1 : Rat),(5/4 : Rat),(3/4 : Rat),(1 : Rat),(3/4 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 1 (7/8 : Rat),.S 2 (7/8 : Rat),.S 0 (9/8 : Rat),.L (373839/524288 : Rat) (497823/524288 : Rat) (142497/1048576 : Rat) (190215/1048576 : Rat),.L (830823/1048576 : Rat) (545939/524288 : Rat) (79229/524288 : Rat) (208835/1048576 : Rat),.S 0 (9/8 : Rat),.L (807585/1048576 : Rat) (271801/262144 : Rat) (76997/524288 : Rat) (207929/1048576 : Rat),.L (897391/1048576 : Rat) (594053/524288 : Rat) (669/4096 : Rat) (113761/524288 : Rat),.S 2 (7/8 : Rat),.S 0 (9/8 : Rat),.L (807585/1048576 : Rat) (271801/262144 : Rat) (76997/524288 : Rat) (207929/1048576 : Rat),.L (897391/1048576 : Rat) (594053/524288 : Rat) (669/4096 : Rat) (113761/524288 : Rat),.S 0 (9/8 : Rat),.L (218073/262144 : Rat) (70973/65536 : Rat) (166433/1048576 : Rat) (217311/1048576 : Rat),.L (969293/1048576 : Rat) (1245751/1048576 : Rat) (185125/1048576 : Rat) (238751/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec5.P23
