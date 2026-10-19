import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P546
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(3/4 : Rat),(25/32 : Rat),(15/16 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (31/32 : Rat),.S 1 (49/64 : Rat),.L (1704719/1048576 : Rat) (227577/131072 : Rat) (329281/1048576 : Rat) (352521/1048576 : Rat),.S 2 (61/64 : Rat),.L (1720551/1048576 : Rat) (1820321/1048576 : Rat) (166223/524288 : Rat) (352461/1048576 : Rat),.L (434081/262144 : Rat) (459209/262144 : Rat) (335601/1048576 : Rat) (355787/1048576 : Rat),.S 1 (49/64 : Rat),.L (434075/262144 : Rat) (1853639/1048576 : Rat) (335597/1048576 : Rat) (179587/524288 : Rat),.S 2 (63/64 : Rat),.L (1752109/1048576 : Rat) (1853349/1048576 : Rat) (338763/1048576 : Rat) (89779/262144 : Rat),.L (1767905/1048576 : Rat) (1869859/1048576 : Rat) (341929/1048576 : Rat) (22653/65536 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P546
