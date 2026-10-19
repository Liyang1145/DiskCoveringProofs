import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P391
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(29/32 : Rat),(15/16 : Rat),(19/32 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 1 (59/64 : Rat),.S 2 (39/64 : Rat),.S 1 (117/128 : Rat),.L (757627/524288 : Rat) (800399/524288 : Rat) (291643/1048576 : Rat) (308587/1048576 : Rat),.L (761597/524288 : Rat) (50283/32768 : Rat) (293213/1048576 : Rat) (310227/1048576 : Rat),.S 1 (117/128 : Rat),.L (1530991/1048576 : Rat) (808491/524288 : Rat) (147377/524288 : Rat) (155901/524288 : Rat),.L (1538925/1048576 : Rat) (203155/131072 : Rat) (74081/262144 : Rat) (313443/1048576 : Rat),.S 2 (39/64 : Rat),.S 1 (119/128 : Rat),.L (1531137/1048576 : Rat) (808657/524288 : Rat) (294783/1048576 : Rat) (77967/262144 : Rat),.L (769541/524288 : Rat) (1625571/1048576 : Rat) (296355/1048576 : Rat) (313509/1048576 : Rat),.S 1 (119/128 : Rat),.L (1546861/1048576 : Rat) (816749/524288 : Rat) (148947/524288 : Rat) (315085/1048576 : Rat),.L (97175/65536 : Rat) (410439/262144 : Rat) (149733/524288 : Rat) (39591/131072 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P391
