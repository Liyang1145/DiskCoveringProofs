import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P389
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(29/32 : Rat),(15/16 : Rat),(9/16 : Rat),(19/32 : Rat)⟩
def toks : List Tok := [.S 1 (59/64 : Rat),.S 2 (37/64 : Rat),.S 1 (117/128 : Rat),.L (741911/524288 : Rat) (784221/524288 : Rat) (142719/524288 : Rat) (302169/1048576 : Rat),.L (1491775/1048576 : Rat) (394175/262144 : Rat) (287007/1048576 : Rat) (151903/524288 : Rat),.S 1 (117/128 : Rat),.L (1499531/1048576 : Rat) (792309/524288 : Rat) (144269/524288 : Rat) (9543/32768 : Rat),.L (1507477/1048576 : Rat) (398219/262144 : Rat) (290107/1048576 : Rat) (307015/1048576 : Rat),.S 2 (37/64 : Rat),.S 1 (119/128 : Rat),.L (749865/524288 : Rat) (1584957/1048576 : Rat) (288577/1048576 : Rat) (76361/262144 : Rat),.L (188461/131072 : Rat) (1593213/1048576 : Rat) (290149/1048576 : Rat) (153541/524288 : Rat),.S 1 (119/128 : Rat),.L (757713/524288 : Rat) (1601133/1048576 : Rat) (291677/1048576 : Rat) (154327/524288 : Rat),.L (761689/524288 : Rat) (804695/524288 : Rat) (293249/1048576 : Rat) (310293/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P389
