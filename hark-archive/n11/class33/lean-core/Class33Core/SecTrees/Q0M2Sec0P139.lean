import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P139
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(13/16 : Rat),(27/32 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 2 (9/32 : Rat),.L (947627/1048576 : Rat) (1141109/1048576 : Rat) (180945/1048576 : Rat) (218387/1048576 : Rat),.L (967483/1048576 : Rat) (583955/524288 : Rat) (23097/131072 : Rat) (111797/524288 : Rat),.S 2 (9/32 : Rat),.S 0 (19/8 : Rat),.L (1004243/1048576 : Rat) (1150091/1048576 : Rat) (191875/1048576 : Rat) (220131/1048576 : Rat),.L (1022695/1048576 : Rat) (1170237/1048576 : Rat) (195441/1048576 : Rat) (112023/524288 : Rat),.S 0 (19/8 : Rat),.L (1029731/1048576 : Rat) (1177659/1048576 : Rat) (98401/524288 : Rat) (112745/524288 : Rat),.L (1049963/1048576 : Rat) (1199507/1048576 : Rat) (50179/262144 : Rat) (57435/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P139
