import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P420
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(29/32 : Rat),(5/8 : Rat),(21/32 : Rat)⟩
def toks : List Tok := [.S 1 (57/64 : Rat),.S 2 (41/64 : Rat),.S 1 (113/128 : Rat),.L (378765/262144 : Rat) (1600127/1048576 : Rat) (291605/1048576 : Rat) (154227/524288 : Rat),.L (47593/32768 : Rat) (1608389/1048576 : Rat) (146585/524288 : Rat) (310095/1048576 : Rat),.S 1 (113/128 : Rat),.L (1530849/1048576 : Rat) (808159/524288 : Rat) (147363/524288 : Rat) (155835/524288 : Rat),.L (1538759/1048576 : Rat) (406145/262144 : Rat) (296291/1048576 : Rat) (9791/32768 : Rat),.S 2 (41/64 : Rat),.S 1 (115/128 : Rat),.L (1530895/1048576 : Rat) (808325/524288 : Rat) (294735/1048576 : Rat) (38967/131072 : Rat),.L (1538817/1048576 : Rat) (812455/524288 : Rat) (148151/524288 : Rat) (156689/524288 : Rat),.S 1 (115/128 : Rat),.L (1546671/1048576 : Rat) (1632841/1048576 : Rat) (297857/1048576 : Rat) (314955/1048576 : Rat),.L (1554587/1048576 : Rat) (820551/524288 : Rat) (9357/32768 : Rat) (158299/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P420
