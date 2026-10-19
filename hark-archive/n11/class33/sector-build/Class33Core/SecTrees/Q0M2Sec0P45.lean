import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P45
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(11/16 : Rat),(3/4 : Rat),(3/8 : Rat),(7/16 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 1 (23/32 : Rat),.L (902567/1048576 : Rat) (1158335/1048576 : Rat) (172261/1048576 : Rat) (221733/1048576 : Rat),.L (931013/1048576 : Rat) (595635/524288 : Rat) (88871/524288 : Rat) (228137/1048576 : Rat),.S 1 (23/32 : Rat),.S 0 (19/8 : Rat),.L (30537/32768 : Rat) (9141/8192 : Rat) (186649/1048576 : Rat) (112005/524288 : Rat),.S 2 (13/32 : Rat),.L (505127/524288 : Rat) (1156729/1048576 : Rat) (48259/262144 : Rat) (221421/1048576 : Rat),.L (259827/262144 : Rat) (593381/524288 : Rat) (99327/524288 : Rat) (56815/262144 : Rat),.S 0 (19/8 : Rat),.L (31459/32768 : Rat) (1203155/1048576 : Rat) (192347/1048576 : Rat) (230451/1048576 : Rat),.S 2 (13/32 : Rat),.L (520445/524288 : Rat) (148705/131072 : Rat) (12435/65536 : Rat) (56955/262144 : Rat),.L (534881/524288 : Rat) (1219639/1048576 : Rat) (204549/1048576 : Rat) (233661/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P45
