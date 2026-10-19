import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P502
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(25/32 : Rat),(13/16 : Rat),(13/16 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 2 (27/32 : Rat),.S 1 (51/64 : Rat),.S 2 (53/64 : Rat),.L (805369/524288 : Rat) (852165/524288 : Rat) (9705/32768 : Rat) (329205/1048576 : Rat),.L (813199/524288 : Rat) (1720867/1048576 : Rat) (39209/131072 : Rat) (166255/524288 : Rat),.S 2 (53/64 : Rat),.L (1626681/1048576 : Rat) (1720555/1048576 : Rat) (313729/1048576 : Rat) (10389/32768 : Rat),.L (821165/524288 : Rat) (1737091/1048576 : Rat) (158421/524288 : Rat) (83939/262144 : Rat),.S 1 (51/64 : Rat),.S 2 (55/64 : Rat),.L (205259/131072 : Rat) (217175/131072 : Rat) (158395/524288 : Rat) (167909/524288 : Rat),.L (51805/32768 : Rat) (876965/524288 : Rat) (159957/524288 : Rat) (42391/131072 : Rat),.S 2 (55/64 : Rat),.L (207249/131072 : Rat) (219203/131072 : Rat) (39995/131072 : Rat) (339067/1048576 : Rat),.L (1673669/1048576 : Rat) (1770155/1048576 : Rat) (80771/262144 : Rat) (342381/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P502
