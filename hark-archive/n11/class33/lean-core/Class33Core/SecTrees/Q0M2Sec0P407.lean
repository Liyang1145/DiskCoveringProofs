import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P407
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(31/32 : Rat),(19/32 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 1 (61/64 : Rat),.S 2 (39/64 : Rat),.S 1 (121/128 : Rat),.L (773515/524288 : Rat) (1633827/1048576 : Rat) (37241/131072 : Rat) (315151/1048576 : Rat),.L (388745/262144 : Rat) (1642083/1048576 : Rat) (299501/1048576 : Rat) (158397/524288 : Rat),.S 1 (121/128 : Rat),.L (781371/524288 : Rat) (412503/262144 : Rat) (301039/1048576 : Rat) (79593/262144 : Rat),.L (785343/524288 : Rat) (1658269/1048576 : Rat) (302613/1048576 : Rat) (20001/65536 : Rat),.S 2 (39/64 : Rat),.S 1 (123/128 : Rat),.L (1562933/1048576 : Rat) (825169/524288 : Rat) (301077/1048576 : Rat) (318437/1048576 : Rat),.L (196361/131072 : Rat) (51831/32768 : Rat) (302653/1048576 : Rat) (320081/1048576 : Rat),.S 1 (123/128 : Rat),.L (197329/131072 : Rat) (416631/262144 : Rat) (76047/262144 : Rat) (321661/1048576 : Rat),.L (793291/524288 : Rat) (1674779/1048576 : Rat) (305765/1048576 : Rat) (323307/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P407
