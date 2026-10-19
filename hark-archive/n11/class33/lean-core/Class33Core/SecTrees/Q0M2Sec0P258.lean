import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P258
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(11/16 : Rat),(3/4 : Rat),(9/16 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 0 (17/8 : Rat),.L (135015/131072 : Rat) (1291771/1048576 : Rat) (51639/262144 : Rat) (247735/1048576 : Rat),.L (34991/32768 : Rat) (1334947/1048576 : Rat) (26779/131072 : Rat) (256181/1048576 : Rat),.S 0 (19/8 : Rat),.S 1 (23/32 : Rat),.L (1154793/1048576 : Rat) (1340511/1048576 : Rat) (55261/262144 : Rat) (257271/1048576 : Rat),.L (147867/131072 : Rat) (171653/131072 : Rat) (226515/1048576 : Rat) (263683/1048576 : Rat),.S 1 (23/32 : Rat),.S 2 (19/32 : Rat),.L (593743/524288 : Rat) (1338853/1048576 : Rat) (28425/131072 : Rat) (128473/524288 : Rat),.L (1217603/1048576 : Rat) (342399/262144 : Rat) (233263/1048576 : Rat) (65743/262144 : Rat),.S 2 (19/32 : Rat),.L (1217085/1048576 : Rat) (685767/524288 : Rat) (116581/524288 : Rat) (32919/131072 : Rat),.L (1247045/1048576 : Rat) (350559/262144 : Rat) (119501/524288 : Rat) (269379/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P258
