import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P300
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/8 : Rat) (406183/524288 : Rat) (12453/524288 : Rat) (154913/1048576 : Rat),.S 0 (3/2 : Rat),.L (605237/1048576 : Rat) (1110645/1048576 : Rat) (57613/524288 : Rat) (106237/524288 : Rat),.S 0 (7/4 : Rat),.L (862125/1048576 : Rat) (1223099/1048576 : Rat) (164477/1048576 : Rat) (234335/1048576 : Rat),.S 2 (9/16 : Rat),.L (243741/262144 : Rat) (318573/262144 : Rat) (46555/262144 : Rat) (244321/1048576 : Rat),.L (1021307/1048576 : Rat) (662129/524288 : Rat) (195173/1048576 : Rat) (254089/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P300
