import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P405
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(31/32 : Rat),(9/16 : Rat),(19/32 : Rat)⟩
def toks : List Tok := [.S 1 (61/64 : Rat),.S 2 (37/64 : Rat),.S 1 (121/128 : Rat),.L (1515649/1048576 : Rat) (400367/262144 : Rat) (291721/1048576 : Rat) (19295/65536 : Rat),.L (1523611/1048576 : Rat) (1609723/1048576 : Rat) (293295/1048576 : Rat) (38795/131072 : Rat),.S 1 (121/128 : Rat),.L (382833/262144 : Rat) (808823/524288 : Rat) (147411/524288 : Rat) (155967/524288 : Rat),.L (192411/131072 : Rat) (1625901/1048576 : Rat) (296395/1048576 : Rat) (313575/1048576 : Rat),.S 2 (37/64 : Rat),.S 1 (123/128 : Rat),.L (1531577/1048576 : Rat) (808989/524288 : Rat) (147435/524288 : Rat) (4875/16384 : Rat),.L (192443/131072 : Rat) (1626231/1048576 : Rat) (148223/524288 : Rat) (39205/131072 : Rat),.S 1 (123/128 : Rat),.L (1547247/1048576 : Rat) (408539/262144 : Rat) (297971/1048576 : Rat) (19701/65536 : Rat),.L (1555209/1048576 : Rat) (821205/524288 : Rat) (299547/1048576 : Rat) (316859/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P405
