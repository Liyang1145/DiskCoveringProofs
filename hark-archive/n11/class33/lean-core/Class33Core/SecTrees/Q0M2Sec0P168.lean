import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P168
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(13/16 : Rat),(27/32 : Rat),(3/8 : Rat),(13/32 : Rat)⟩
def toks : List Tok := [.S 1 (53/64 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (290207/262144 : Rat) (1272435/1048576 : Rat) (27777/131072 : Rat) (121979/524288 : Rat),.L (294483/262144 : Rat) (1283925/1048576 : Rat) (112771/524288 : Rat) (123101/524288 : Rat),.S 0 (21/8 : Rat),.L (587641/524288 : Rat) (1288225/1048576 : Rat) (112513/524288 : Rat) (123521/524288 : Rat),.L (596439/524288 : Rat) (1300027/1048576 : Rat) (228449/1048576 : Rat) (249349/1048576 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (1176621/1048576 : Rat) (1288883/1048576 : Rat) (225287/1048576 : Rat) (247171/1048576 : Rat),.L (1193821/1048576 : Rat) (162555/131072 : Rat) (228633/1048576 : Rat) (124715/524288 : Rat),.S 0 (21/8 : Rat),.L (1191045/1048576 : Rat) (1304671/1048576 : Rat) (228093/1048576 : Rat) (250257/1048576 : Rat),.L (1208743/1048576 : Rat) (20571/16384 : Rat) (115769/524288 : Rat) (252579/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P168
