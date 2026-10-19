import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P441
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(29/32 : Rat),(23/32 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (57/64 : Rat),.S 2 (47/64 : Rat),.S 1 (113/128 : Rat),.L (804985/524288 : Rat) (1697327/1048576 : Rat) (38801/131072 : Rat) (163903/524288 : Rat),.L (1617849/1048576 : Rat) (852795/524288 : Rat) (311973/1048576 : Rat) (20591/65536 : Rat),.S 1 (113/128 : Rat),.L (406457/262144 : Rat) (1713539/1048576 : Rat) (313559/1048576 : Rat) (331045/1048576 : Rat),.L (1633701/1048576 : Rat) (860901/524288 : Rat) (315125/1048576 : Rat) (332697/1048576 : Rat),.S 2 (47/64 : Rat),.S 1 (115/128 : Rat),.L (1625731/1048576 : Rat) (428463/262144 : Rat) (78385/262144 : Rat) (331107/1048576 : Rat),.L (1633617/1048576 : Rat) (861057/524288 : Rat) (78777/262144 : Rat) (332759/1048576 : Rat),.S 1 (115/128 : Rat),.L (1641577/1048576 : Rat) (1730065/1048576 : Rat) (79173/262144 : Rat) (167175/524288 : Rat),.L (103091/65536 : Rat) (1738327/1048576 : Rat) (79565/262144 : Rat) (336003/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P441
