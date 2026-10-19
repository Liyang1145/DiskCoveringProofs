import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P188
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(1 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 2 (9/16 : Rat),.S 1 (31/32 : Rat),.L (625259/524288 : Rat) (1624249/1048576 : Rat) (3745/16384 : Rat) (156623/524288 : Rat),.L (319923/262144 : Rat) (1657945/1048576 : Rat) (122687/524288 : Rat) (19997/65536 : Rat),.S 1 (31/32 : Rat),.S 0 (11/4 : Rat),.S 2 (19/32 : Rat),.L (1423603/1048576 : Rat) (411643/262144 : Rat) (273577/1048576 : Rat) (317687/1048576 : Rat),.L (726201/524288 : Rat) (1678541/1048576 : Rat) (279245/1048576 : Rat) (324057/1048576 : Rat),.L (1405273/1048576 : Rat) (843259/524288 : Rat) (134987/524288 : Rat) (20353/65536 : Rat),.S 0 (11/4 : Rat),.S 2 (19/32 : Rat),.L (1454155/1048576 : Rat) (419955/262144 : Rat) (139795/524288 : Rat) (40539/131072 : Rat),.S 1 (63/64 : Rat),.L (370705/262144 : Rat) (1695171/1048576 : Rat) (35655/131072 : Rat) (20461/65536 : Rat),.L (1498067/1048576 : Rat) (1711795/1048576 : Rat) (288249/1048576 : Rat) (41337/131072 : Rat),.L (1435127/1048576 : Rat) (860121/524288 : Rat) (68961/262144 : Rat) (332385/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P188
