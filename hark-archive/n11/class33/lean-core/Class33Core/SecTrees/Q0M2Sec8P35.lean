import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P35
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(1/4 : Rat),(3/8 : Rat),(3/4 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (7/8 : Rat),.S 0 (5/2 : Rat),.S 1 (5/16 : Rat),.L (420907/524288 : Rat) (319383/262144 : Rat) (160571/1048576 : Rat) (244953/1048576 : Rat),.S 0 (9/4 : Rat),.L (912533/1048576 : Rat) (634901/524288 : Rat) (174181/1048576 : Rat) (60861/262144 : Rat),.L (962169/1048576 : Rat) (1327443/1048576 : Rat) (183751/1048576 : Rat) (31839/131072 : Rat),.L (847519/1048576 : Rat) (85527/65536 : Rat) (40417/262144 : Rat) (262743/1048576 : Rat),.S 0 (5/2 : Rat),.S 1 (5/16 : Rat),.L (481955/524288 : Rat) (1411689/1048576 : Rat) (184087/1048576 : Rat) (67809/262144 : Rat),.S 0 (9/4 : Rat),.S 2 (15/16 : Rat),.L (1032469/1048576 : Rat) (667893/524288 : Rat) (197331/1048576 : Rat) (128173/524288 : Rat),.L (273349/262144 : Rat) (10951/8192 : Rat) (26141/131072 : Rat) (269279/1048576 : Rat),.L (135471/131072 : Rat) (1461483/1048576 : Rat) (103631/524288 : Rat) (281035/1048576 : Rat),.L (965657/1048576 : Rat) (1505903/1048576 : Rat) (23053/131072 : Rat) (289797/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P35
