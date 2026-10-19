import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P8
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(0 : Rat),(1 : Rat),(5/8 : Rat),(11/16 : Rat),(0 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (1/2 : Rat),.S 2 (1/8 : Rat),.S 1 (21/32 : Rat),.L (1/2 : Rat) (88035/131072 : Rat) (99765/1048576 : Rat) (33545/262144 : Rat),.S 2 (1/16 : Rat),.L (19/32 : Rat) (729021/1048576 : Rat) (7409/65536 : Rat) (138921/1048576 : Rat),.L (17/32 : Rat) (84137/131072 : Rat) (106021/1048576 : Rat) (8013/65536 : Rat),.S 1 (21/32 : Rat),.L (3/8 : Rat) (18627/32768 : Rat) (37387/524288 : Rat) (56737/524288 : Rat),.S 2 (3/16 : Rat),.L (15/32 : Rat) (619059/1048576 : Rat) (11689/131072 : Rat) (58935/524288 : Rat),.L (13/32 : Rat) (567451/1048576 : Rat) (81017/1048576 : Rat) (108007/1048576 : Rat),.S 2 (1/8 : Rat),.L (1/2 : Rat) (97701/131072 : Rat) (99765/1048576 : Rat) (149007/1048576 : Rat),.S 1 (21/32 : Rat),.L (104469/262144 : Rat) (348015/524288 : Rat) (4967/65536 : Rat) (132599/1048576 : Rat),.L (56245/131072 : Rat) (728239/1048576 : Rat) (85587/1048576 : Rat) (138771/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P8
