import Class33Core.SecTrees.Q0M2Sec5Base
namespace Class33Core.SecTrees.Q0M2Sec5.P64
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec5
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(1 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 2 (11/16 : Rat),.S 1 (15/16 : Rat),.L (1297187/1048576 : Rat) (857621/524288 : Rat) (248793/1048576 : Rat) (331385/1048576 : Rat),.L (1352845/1048576 : Rat) (445693/262144 : Rat) (259687/1048576 : Rat) (344913/1048576 : Rat),.S 1 (15/16 : Rat),.S 0 (11/4 : Rat),.S 0 (21/8 : Rat),.L (378427/262144 : Rat) (879951/524288 : Rat) (145669/524288 : Rat) (340325/1048576 : Rat),.L (1539575/1048576 : Rat) (444487/262144 : Rat) (74113/262144 : Rat) (343945/1048576 : Rat),.L (22897/16384 : Rat) (444487/262144 : Rat) (281807/1048576 : Rat) (343945/1048576 : Rat),.S 0 (11/4 : Rat),.S 0 (21/8 : Rat),.S 0 (41/16 : Rat),.L (1591739/1048576 : Rat) (1790883/1048576 : Rat) (76697/262144 : Rat) (173271/524288 : Rat),.L (1606647/1048576 : Rat) (56463/32768 : Rat) (77437/262144 : Rat) (21859/65536 : Rat),.L (99997/65536 : Rat) (1845511/1048576 : Rat) (154209/524288 : Rat) (357535/1048576 : Rat),.L (1523501/1048576 : Rat) (1845511/1048576 : Rat) (293273/1048576 : Rat) (357535/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec5.P64
