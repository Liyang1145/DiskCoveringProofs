import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P423
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(29/32 : Rat),(21/32 : Rat),(11/16 : Rat)⟩
def toks : List Tok := [.S 1 (57/64 : Rat),.S 2 (43/64 : Rat),.S 1 (113/128 : Rat),.L (773325/524288 : Rat) (6377/4096 : Rat) (74463/262144 : Rat) (314889/1048576 : Rat),.L (1554553/1048576 : Rat) (820387/524288 : Rat) (299417/1048576 : Rat) (316533/1048576 : Rat),.S 1 (113/128 : Rat),.L (1562463/1048576 : Rat) (824355/524288 : Rat) (37623/131072 : Rat) (318113/1048576 : Rat),.L (196295/131072 : Rat) (1656973/1048576 : Rat) (75637/262144 : Rat) (159879/524288 : Rat),.S 2 (43/64 : Rat),.S 1 (115/128 : Rat),.L (390615/262144 : Rat) (412259/262144 : Rat) (300983/1048576 : Rat) (159089/524288 : Rat),.L (1570369/1048576 : Rat) (1657297/1048576 : Rat) (151275/524288 : Rat) (319823/1048576 : Rat),.S 1 (115/128 : Rat),.L (394565/262144 : Rat) (1665235/1048576 : Rat) (152057/524288 : Rat) (80351/262144 : Rat),.L (1586163/1048576 : Rat) (209187/131072 : Rat) (152841/524288 : Rat) (323051/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P423
