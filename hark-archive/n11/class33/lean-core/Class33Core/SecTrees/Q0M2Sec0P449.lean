import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P449
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(29/32 : Rat),(15/16 : Rat),(23/32 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (59/64 : Rat),.S 2 (47/64 : Rat),.S 1 (117/128 : Rat),.L (1641505/1048576 : Rat) (1730375/1048576 : Rat) (158339/524288 : Rat) (83603/262144 : Rat),.L (412349/262144 : Rat) (434659/262144 : Rat) (39781/131072 : Rat) (336065/1048576 : Rat),.S 1 (117/128 : Rat),.L (1657339/1048576 : Rat) (436647/262144 : Rat) (159915/524288 : Rat) (168829/524288 : Rat),.L (208153/131072 : Rat) (1754849/1048576 : Rat) (321401/1048576 : Rat) (339313/1048576 : Rat),.S 2 (47/64 : Rat),.S 1 (119/128 : Rat),.L (828645/524288 : Rat) (1746895/1048576 : Rat) (79955/262144 : Rat) (337719/1048576 : Rat),.L (1665187/1048576 : Rat) (877577/524288 : Rat) (160697/524288 : Rat) (169687/524288 : Rat),.S 1 (119/128 : Rat),.L (209139/131072 : Rat) (440777/262144 : Rat) (322973/1048576 : Rat) (42621/131072 : Rat),.L (1681003/1048576 : Rat) (221421/131072 : Rat) (324547/1048576 : Rat) (342625/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P449
