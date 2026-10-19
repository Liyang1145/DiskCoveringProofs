import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P40
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(0 : Rat),(1/2 : Rat),(5/8 : Rat),(3/4 : Rat),(1/8 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 1 (11/16 : Rat),.S 0 (1/4 : Rat),.S 2 (3/16 : Rat),.S 1 (21/32 : Rat),.L (7/16 : Rat) (282295/524288 : Rat) (87263/1048576 : Rat) (107461/1048576 : Rat),.L (15/32 : Rat) (298641/524288 : Rat) (11689/131072 : Rat) (113707/1048576 : Rat),.L (3/8 : Rat) (535427/1048576 : Rat) (37387/524288 : Rat) (25473/262144 : Rat),.L (399867/1048576 : Rat) (628271/1048576 : Rat) (76041/1048576 : Rat) (119631/1048576 : Rat),.S 0 (1/4 : Rat),.S 2 (3/16 : Rat),.S 1 (23/32 : Rat),.L (1/2 : Rat) (629981/1048576 : Rat) (99765/1048576 : Rat) (59979/524288 : Rat),.L (17/32 : Rat) (20709/32768 : Rat) (106021/1048576 : Rat) (15777/131072 : Rat),.S 1 (23/32 : Rat),.L (7/16 : Rat) (568025/1048576 : Rat) (87263/1048576 : Rat) (108117/1048576 : Rat),.L (15/32 : Rat) (600641/1048576 : Rat) (11689/131072 : Rat) (114349/1048576 : Rat),.S 2 (3/16 : Rat),.L (4139/8192 : Rat) (683969/1048576 : Rat) (100815/1048576 : Rat) (65145/524288 : Rat),.L (234071/524288 : Rat) (315825/524288 : Rat) (89053/1048576 : Rat) (60139/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P40
