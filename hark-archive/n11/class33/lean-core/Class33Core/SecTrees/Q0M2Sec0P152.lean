import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P152
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(27/32 : Rat),(7/8 : Rat),(11/32 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 1 (55/64 : Rat),.S 2 (23/64 : Rat),.S 0 (21/8 : Rat),.L (290949/262144 : Rat) (1273801/1048576 : Rat) (222793/1048576 : Rat) (244225/1048576 : Rat),.L (1180043/1048576 : Rat) (1284761/1048576 : Rat) (7061/32768 : Rat) (246365/1048576 : Rat),.S 0 (21/8 : Rat),.L (589043/524288 : Rat) (1289557/1048576 : Rat) (56393/262144 : Rat) (247303/1048576 : Rat),.L (1194863/1048576 : Rat) (1300853/1048576 : Rat) (57209/262144 : Rat) (124755/524288 : Rat),.S 2 (23/64 : Rat),.S 0 (21/8 : Rat),.L (1179677/1048576 : Rat) (161281/131072 : Rat) (225881/1048576 : Rat) (123719/524288 : Rat),.L (1196003/1048576 : Rat) (650633/524288 : Rat) (229057/1048576 : Rat) (249591/1048576 : Rat),.S 0 (21/8 : Rat),.L (596969/524288 : Rat) (1306003/1048576 : Rat) (14291/65536 : Rat) (250517/1048576 : Rat),.L (75675/65536 : Rat) (82335/65536 : Rat) (115969/524288 : Rat) (252739/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P152
