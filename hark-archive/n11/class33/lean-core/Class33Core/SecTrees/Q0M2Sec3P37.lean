import Class33Core.SecTrees.Q0M2Sec3Base
namespace Class33Core.SecTrees.Q0M2Sec3.P37
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec3
def box : Box := ⟨(15/8 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(7/8 : Rat),(15/16 : Rat)⟩
def toks : List Tok := [.S 0 (31/16 : Rat),.S 2 (29/32 : Rat),.S 1 (31/32 : Rat),.L (379783/262144 : Rat) (204447/131072 : Rat) (146205/524288 : Rat) (315499/1048576 : Rat),.L (1545275/1048576 : Rat) (1663913/1048576 : Rat) (74395/262144 : Rat) (321141/1048576 : Rat),.S 1 (31/32 : Rat),.L (772831/524288 : Rat) (830911/524288 : Rat) (297657/1048576 : Rat) (80181/262144 : Rat),.L (785777/524288 : Rat) (211245/131072 : Rat) (302785/1048576 : Rat) (326335/1048576 : Rat),.S 2 (29/32 : Rat),.S 1 (31/32 : Rat),.L (1552739/1048576 : Rat) (1670289/1048576 : Rat) (149529/524288 : Rat) (80603/262144 : Rat),.L (789707/524288 : Rat) (26549/16384 : Rat) (304343/1048576 : Rat) (328167/1048576 : Rat),.S 1 (31/32 : Rat),.L (1579871/1048576 : Rat) (424291/262144 : Rat) (152217/524288 : Rat) (163887/524288 : Rat),.S 0 (63/32 : Rat),.L (806563/524288 : Rat) (1701183/1048576 : Rat) (311035/1048576 : Rat) (2567/8192 : Rat),.L (1630113/1048576 : Rat) (1718711/1048576 : Rat) (314411/1048576 : Rat) (332079/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec3.P37
