import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P438
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(29/32 : Rat),(11/16 : Rat),(23/32 : Rat)⟩
def toks : List Tok := [.S 1 (57/64 : Rat),.S 2 (45/64 : Rat),.S 1 (113/128 : Rat),.L (98643/65536 : Rat) (104057/65536 : Rat) (38015/131072 : Rat) (80335/262144 : Rat),.L (1586179/1048576 : Rat) (1673175/1048576 : Rat) (305685/1048576 : Rat) (322987/1048576 : Rat),.S 1 (113/128 : Rat),.L (398531/262144 : Rat) (840559/524288 : Rat) (307261/1048576 : Rat) (324571/1048576 : Rat),.L (1602009/1048576 : Rat) (1689381/1048576 : Rat) (308827/1048576 : Rat) (81555/262144 : Rat),.S 2 (45/64 : Rat),.S 1 (115/128 : Rat),.L (1594073/1048576 : Rat) (1681437/1048576 : Rat) (307251/1048576 : Rat) (324635/1048576 : Rat),.L (800985/524288 : Rat) (1689699/1048576 : Rat) (308819/1048576 : Rat) (326283/1048576 : Rat),.S 1 (115/128 : Rat),.L (1609897/1048576 : Rat) (1697643/1048576 : Rat) (310393/1048576 : Rat) (327869/1048576 : Rat),.L (404447/262144 : Rat) (1705905/1048576 : Rat) (311961/1048576 : Rat) (329519/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P438
