import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P355
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(19/8 : Rat),(5/2 : Rat),(3/4 : Rat),(13/16 : Rat),(7/8 : Rat),(15/16 : Rat)⟩
def toks : List Tok := [.S 1 (25/32 : Rat),.S 2 (29/32 : Rat),.S 0 (39/16 : Rat),.L (195237/131072 : Rat) (841123/524288 : Rat) (300871/1048576 : Rat) (81199/262144 : Rat),.L (790083/524288 : Rat) (1701171/1048576 : Rat) (76123/262144 : Rat) (164287/524288 : Rat),.S 0 (39/16 : Rat),.L (1591797/1048576 : Rat) (1714183/1048576 : Rat) (19175/65536 : Rat) (165587/524288 : Rat),.L (402591/262144 : Rat) (433349/262144 : Rat) (155243/524288 : Rat) (41877/131072 : Rat),.S 0 (39/16 : Rat),.S 2 (29/32 : Rat),.L (1592293/1048576 : Rat) (1712429/1048576 : Rat) (153449/524288 : Rat) (330823/1048576 : Rat),.S 1 (51/64 : Rat),.L (1623161/1048576 : Rat) (863801/524288 : Rat) (313029/1048576 : Rat) (333857/1048576 : Rat),.L (1638167/1048576 : Rat) (1742843/1048576 : Rat) (316013/1048576 : Rat) (336907/1048576 : Rat),.S 2 (29/32 : Rat),.L (100685/65536 : Rat) (1731763/1048576 : Rat) (77651/262144 : Rat) (167345/524288 : Rat),.L (1641065/1048576 : Rat) (881971/524288 : Rat) (158295/524288 : Rat) (341135/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P355
