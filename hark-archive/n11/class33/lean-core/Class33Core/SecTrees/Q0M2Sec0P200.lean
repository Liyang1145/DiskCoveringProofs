import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P200
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(15/16 : Rat),(31/32 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 2 (9/32 : Rat),.L (1073135/1048576 : Rat) (1272007/1048576 : Rat) (102601/524288 : Rat) (121937/524288 : Rat),.L (1091951/1048576 : Rat) (1298595/1048576 : Rat) (13053/65536 : Rat) (249069/1048576 : Rat),.S 2 (9/32 : Rat),.S 0 (19/8 : Rat),.L (1130985/1048576 : Rat) (1281261/1048576 : Rat) (54105/262144 : Rat) (122841/524288 : Rat),.L (574953/524288 : Rat) (1302037/1048576 : Rat) (110047/524288 : Rat) (124871/524288 : Rat),.S 0 (19/8 : Rat),.L (577885/524288 : Rat) (1308665/1048576 : Rat) (110617/524288 : Rat) (125519/524288 : Rat),.L (588293/524288 : Rat) (1331253/1048576 : Rat) (55/256 : Rat) (127729/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P200
