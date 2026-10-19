import Class33Core.SecTrees.Q0M2Sec6Base
namespace Class33Core.SecTrees.Q0M2Sec6.P94
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec6
def box : Box := ⟨(21/8 : Rat),(11/4 : Rat),(15/16 : Rat),(1 : Rat),(15/16 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (43/16 : Rat),.S 1 (31/32 : Rat),.S 2 (31/32 : Rat),.L (234719/131072 : Rat) (2004101/1048576 : Rat) (182021/524288 : Rat) (48711/131072 : Rat),.L (238599/131072 : Rat) (2036951/1048576 : Rat) (23145/65536 : Rat) (396395/1048576 : Rat),.S 2 (31/32 : Rat),.L (238599/131072 : Rat) (2036951/1048576 : Rat) (23145/65536 : Rat) (396395/1048576 : Rat),.S 0 (85/32 : Rat),.L (976171/524288 : Rat) (64011/32768 : Rat) (379153/1048576 : Rat) (398727/1048576 : Rat),.L (979985/524288 : Rat) (2056225/1048576 : Rat) (380703/1048576 : Rat) (400339/1048576 : Rat),.S 1 (31/32 : Rat),.S 2 (31/32 : Rat),.L (945791/524288 : Rat) (1009195/524288 : Rat) (366837/1048576 : Rat) (392603/1048576 : Rat),.L (961425/524288 : Rat) (2051463/1048576 : Rat) (23323/65536 : Rat) (99841/262144 : Rat),.S 2 (31/32 : Rat),.L (961425/524288 : Rat) (2051463/1048576 : Rat) (23323/65536 : Rat) (99841/262144 : Rat),.L (1954635/1048576 : Rat) (1041741/524288 : Rat) (379619/1048576 : Rat) (405925/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec6.P94
