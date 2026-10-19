import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P482
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(31/32 : Rat),(1 : Rat),(11/16 : Rat),(23/32 : Rat)⟩
def toks : List Tok := [.S 1 (63/64 : Rat),.S 2 (45/64 : Rat),.S 1 (125/128 : Rat),.L (1673171/1048576 : Rat) (882011/524288 : Rat) (322985/1048576 : Rat) (341151/1048576 : Rat),.L (210137/131072 : Rat) (1772277/1048576 : Rat) (162283/524288 : Rat) (342807/1048576 : Rat),.S 1 (125/128 : Rat),.L (211117/131072 : Rat) (890115/524288 : Rat) (163065/524288 : Rat) (344403/1048576 : Rat),.L (1696855/1048576 : Rat) (1788485/1048576 : Rat) (327711/1048576 : Rat) (346061/1048576 : Rat),.S 2 (45/64 : Rat),.S 1 (127/128 : Rat),.L (1689023/1048576 : Rat) (1780531/1048576 : Rat) (326147/1048576 : Rat) (21529/65536 : Rat),.L (1696953/1048576 : Rat) (1788785/1048576 : Rat) (163865/524288 : Rat) (346121/1048576 : Rat),.S 1 (127/128 : Rat),.L (213097/131072 : Rat) (449185/262144 : Rat) (329293/1048576 : Rat) (347719/1048576 : Rat),.L (1712701/1048576 : Rat) (902497/524288 : Rat) (82719/262144 : Rat) (174689/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P482
