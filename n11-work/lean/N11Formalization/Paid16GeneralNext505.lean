import N11Formalization.Paid16GeneralH01
import N11Formalization.Paid16GeneralH02
import N11Formalization.Paid16GeneralH03
import N11Formalization.Paid16GeneralH04
import N11Formalization.Paid16GeneralH05
import N11Formalization.Paid16GeneralH06
import N11Formalization.Paid16GeneralH07
import N11Formalization.Paid16GeneralH08
import N11Formalization.Paid16GeneralH09
import N11Formalization.Paid16GeneralH10
import N11Formalization.Paid16GeneralH11
import N11Formalization.Paid16GeneralH12
import N11Formalization.Paid16GeneralH13
import N11Formalization.Paid16GeneralH14
import N11Formalization.Paid16GeneralH15
import N11Formalization.Paid16GeneralH16
import N11Formalization.Paid16GeneralH17
import N11Formalization.Paid16GeneralH18
import N11Formalization.Paid16GeneralH19
import N11Formalization.Paid16GeneralH20
import N11Formalization.Paid16GeneralH21
import N11Formalization.Paid16GeneralH22
import N11Formalization.Paid16GeneralH23
import N11Formalization.Paid16GeneralH24
import N11Formalization.Paid16GeneralH25

/-! CHEAP aggregate of the 505 packets emitted for `next505`.

`newIDs` is a union of LITERAL finsets (`idscount`), one per packet module, and
`subcount : idscount ⊆ Paid16GeneralH01.newIDs`-style facts route each literal back to the
`Valid packet`-backed theorem of its own module. No `Finset.univ` is unfolded
and no large set is kernel-searched. -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralNext505
open Finset
noncomputable section

def ids00 : Finset (Fin 5011) := {1160,1165,1168,1170,1171,1172,1177,1184,1188,1189,1191,1193,1195,1201,1205,1207,1209,1214,1215,1223,1227}
theorem mem_ids00 (n : Fin 5011) : n ∈ ids00 ↔ n = 1160 ∨ n = 1165 ∨ n = 1168 ∨ n = 1170 ∨ n = 1171 ∨ n = 1172 ∨ n = 1177 ∨ n = 1184 ∨ n = 1188 ∨ n = 1189 ∨ n = 1191 ∨ n = 1193 ∨ n = 1195 ∨ n = 1201 ∨ n = 1205 ∨ n = 1207 ∨ n = 1209 ∨ n = 1214 ∨ n = 1215 ∨ n = 1223 ∨ n = 1227 := by
  simp [ids00]
theorem ids00_card : ids00.card = 21 := by decide +kernel
theorem sub00 (n : Fin 5011) (hn : n ∈ ids00) : n ∈ Paid16GeneralH01.newIDs := by
  rcases (mem_ids00 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids01 : Finset (Fin 5011) := {1229,1232,1234,1235,1240,1241,1244,1252,1253,1257,1261,1266,1268,1277,1279,1290,1291,1293,1305,1311,1313}
theorem mem_ids01 (n : Fin 5011) : n ∈ ids01 ↔ n = 1229 ∨ n = 1232 ∨ n = 1234 ∨ n = 1235 ∨ n = 1240 ∨ n = 1241 ∨ n = 1244 ∨ n = 1252 ∨ n = 1253 ∨ n = 1257 ∨ n = 1261 ∨ n = 1266 ∨ n = 1268 ∨ n = 1277 ∨ n = 1279 ∨ n = 1290 ∨ n = 1291 ∨ n = 1293 ∨ n = 1305 ∨ n = 1311 ∨ n = 1313 := by
  simp [ids01]
theorem ids01_card : ids01.card = 21 := by decide +kernel
theorem sub01 (n : Fin 5011) (hn : n ∈ ids01) : n ∈ Paid16GeneralH02.newIDs := by
  rcases (mem_ids01 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids02 : Finset (Fin 5011) := {1315,1317,1319,1322,1327,1338,1340,1359,1372,1376,1378,1380,1382,1388,1392,1398,1399,1402,1404,1406,1408}
theorem mem_ids02 (n : Fin 5011) : n ∈ ids02 ↔ n = 1315 ∨ n = 1317 ∨ n = 1319 ∨ n = 1322 ∨ n = 1327 ∨ n = 1338 ∨ n = 1340 ∨ n = 1359 ∨ n = 1372 ∨ n = 1376 ∨ n = 1378 ∨ n = 1380 ∨ n = 1382 ∨ n = 1388 ∨ n = 1392 ∨ n = 1398 ∨ n = 1399 ∨ n = 1402 ∨ n = 1404 ∨ n = 1406 ∨ n = 1408 := by
  simp [ids02]
theorem ids02_card : ids02.card = 21 := by decide +kernel
theorem sub02 (n : Fin 5011) (hn : n ∈ ids02) : n ∈ Paid16GeneralH03.newIDs := by
  rcases (mem_ids02 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids03 : Finset (Fin 5011) := {1418,1420,1422,1424,1426,1432,1434,1437,1439,1448,1450,1452,1455,1457,1459,1465,1468,1470,1473,1475,1490}
theorem mem_ids03 (n : Fin 5011) : n ∈ ids03 ↔ n = 1418 ∨ n = 1420 ∨ n = 1422 ∨ n = 1424 ∨ n = 1426 ∨ n = 1432 ∨ n = 1434 ∨ n = 1437 ∨ n = 1439 ∨ n = 1448 ∨ n = 1450 ∨ n = 1452 ∨ n = 1455 ∨ n = 1457 ∨ n = 1459 ∨ n = 1465 ∨ n = 1468 ∨ n = 1470 ∨ n = 1473 ∨ n = 1475 ∨ n = 1490 := by
  simp [ids03]
theorem ids03_card : ids03.card = 21 := by decide +kernel
theorem sub03 (n : Fin 5011) (hn : n ∈ ids03) : n ∈ Paid16GeneralH04.newIDs := by
  rcases (mem_ids03 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids04 : Finset (Fin 5011) := {1492,1493,1494,1495,1498,1506,1507,1510,1512,1514,1528,1532,1540,1551,1553,1555,1558,1561,1580,1584,1585}
theorem mem_ids04 (n : Fin 5011) : n ∈ ids04 ↔ n = 1492 ∨ n = 1493 ∨ n = 1494 ∨ n = 1495 ∨ n = 1498 ∨ n = 1506 ∨ n = 1507 ∨ n = 1510 ∨ n = 1512 ∨ n = 1514 ∨ n = 1528 ∨ n = 1532 ∨ n = 1540 ∨ n = 1551 ∨ n = 1553 ∨ n = 1555 ∨ n = 1558 ∨ n = 1561 ∨ n = 1580 ∨ n = 1584 ∨ n = 1585 := by
  simp [ids04]
theorem ids04_card : ids04.card = 21 := by decide +kernel
theorem sub04 (n : Fin 5011) (hn : n ∈ ids04) : n ∈ Paid16GeneralH05.newIDs := by
  rcases (mem_ids04 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids05 : Finset (Fin 5011) := {1587,1589,1590,1595,1597,1599,1601,1606,1609,1616,1620,1622,1624,1626,1628,1648,1656,1658,1670,1671,1673}
theorem mem_ids05 (n : Fin 5011) : n ∈ ids05 ↔ n = 1587 ∨ n = 1589 ∨ n = 1590 ∨ n = 1595 ∨ n = 1597 ∨ n = 1599 ∨ n = 1601 ∨ n = 1606 ∨ n = 1609 ∨ n = 1616 ∨ n = 1620 ∨ n = 1622 ∨ n = 1624 ∨ n = 1626 ∨ n = 1628 ∨ n = 1648 ∨ n = 1656 ∨ n = 1658 ∨ n = 1670 ∨ n = 1671 ∨ n = 1673 := by
  simp [ids05]
theorem ids05_card : ids05.card = 21 := by decide +kernel
theorem sub05 (n : Fin 5011) (hn : n ∈ ids05) : n ∈ Paid16GeneralH06.newIDs := by
  rcases (mem_ids05 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids06 : Finset (Fin 5011) := {1675,1677,1692,1696,1698,1722,1724,1732,1734,1740,1742,1745,1748,1750,1752,1769,1772,1773,1776,1777,1779}
theorem mem_ids06 (n : Fin 5011) : n ∈ ids06 ↔ n = 1675 ∨ n = 1677 ∨ n = 1692 ∨ n = 1696 ∨ n = 1698 ∨ n = 1722 ∨ n = 1724 ∨ n = 1732 ∨ n = 1734 ∨ n = 1740 ∨ n = 1742 ∨ n = 1745 ∨ n = 1748 ∨ n = 1750 ∨ n = 1752 ∨ n = 1769 ∨ n = 1772 ∨ n = 1773 ∨ n = 1776 ∨ n = 1777 ∨ n = 1779 := by
  simp [ids06]
theorem ids06_card : ids06.card = 21 := by decide +kernel
theorem sub06 (n : Fin 5011) (hn : n ∈ ids06) : n ∈ Paid16GeneralH07.newIDs := by
  rcases (mem_ids06 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids07 : Finset (Fin 5011) := {1781,1783,1788,1789,1792,1795,1802,1804,1805,1807,1812,1815,1820,1823,1825,1829,1832,1834,1835,1838,1849}
theorem mem_ids07 (n : Fin 5011) : n ∈ ids07 ↔ n = 1781 ∨ n = 1783 ∨ n = 1788 ∨ n = 1789 ∨ n = 1792 ∨ n = 1795 ∨ n = 1802 ∨ n = 1804 ∨ n = 1805 ∨ n = 1807 ∨ n = 1812 ∨ n = 1815 ∨ n = 1820 ∨ n = 1823 ∨ n = 1825 ∨ n = 1829 ∨ n = 1832 ∨ n = 1834 ∨ n = 1835 ∨ n = 1838 ∨ n = 1849 := by
  simp [ids07]
theorem ids07_card : ids07.card = 21 := by decide +kernel
theorem sub07 (n : Fin 5011) (hn : n ∈ ids07) : n ∈ Paid16GeneralH08.newIDs := by
  rcases (mem_ids07 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids08 : Finset (Fin 5011) := {1851,1853,1861,1869,1875,1882,1883,1897,1903,1905,1907,1909,1911,1913,1918,1919,1921,1925,1928,1932,1934}
theorem mem_ids08 (n : Fin 5011) : n ∈ ids08 ↔ n = 1851 ∨ n = 1853 ∨ n = 1861 ∨ n = 1869 ∨ n = 1875 ∨ n = 1882 ∨ n = 1883 ∨ n = 1897 ∨ n = 1903 ∨ n = 1905 ∨ n = 1907 ∨ n = 1909 ∨ n = 1911 ∨ n = 1913 ∨ n = 1918 ∨ n = 1919 ∨ n = 1921 ∨ n = 1925 ∨ n = 1928 ∨ n = 1932 ∨ n = 1934 := by
  simp [ids08]
theorem ids08_card : ids08.card = 21 := by decide +kernel
theorem sub08 (n : Fin 5011) (hn : n ∈ ids08) : n ∈ Paid16GeneralH09.newIDs := by
  rcases (mem_ids08 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids09 : Finset (Fin 5011) := {1943,1945,1947,1950,1954,1956,1958,1959,1962,1964,1968,1988,1990,1997,2016,2022,2024,2025,2059,2065,2069}
theorem mem_ids09 (n : Fin 5011) : n ∈ ids09 ↔ n = 1943 ∨ n = 1945 ∨ n = 1947 ∨ n = 1950 ∨ n = 1954 ∨ n = 1956 ∨ n = 1958 ∨ n = 1959 ∨ n = 1962 ∨ n = 1964 ∨ n = 1968 ∨ n = 1988 ∨ n = 1990 ∨ n = 1997 ∨ n = 2016 ∨ n = 2022 ∨ n = 2024 ∨ n = 2025 ∨ n = 2059 ∨ n = 2065 ∨ n = 2069 := by
  simp [ids09]
theorem ids09_card : ids09.card = 21 := by decide +kernel
theorem sub09 (n : Fin 5011) (hn : n ∈ ids09) : n ∈ Paid16GeneralH10.newIDs := by
  rcases (mem_ids09 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids10 : Finset (Fin 5011) := {2072,2074,2082,2084,2086,2087,2089,2098,2103,2106,2108,2122,2126,2127,2129,2134,2135,2139,2141,2143,2145}
theorem mem_ids10 (n : Fin 5011) : n ∈ ids10 ↔ n = 2072 ∨ n = 2074 ∨ n = 2082 ∨ n = 2084 ∨ n = 2086 ∨ n = 2087 ∨ n = 2089 ∨ n = 2098 ∨ n = 2103 ∨ n = 2106 ∨ n = 2108 ∨ n = 2122 ∨ n = 2126 ∨ n = 2127 ∨ n = 2129 ∨ n = 2134 ∨ n = 2135 ∨ n = 2139 ∨ n = 2141 ∨ n = 2143 ∨ n = 2145 := by
  simp [ids10]
theorem ids10_card : ids10.card = 21 := by decide +kernel
theorem sub10 (n : Fin 5011) (hn : n ∈ ids10) : n ∈ Paid16GeneralH11.newIDs := by
  rcases (mem_ids10 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids11 : Finset (Fin 5011) := {2150,2151,2153,2163,2168,2176,2177,2179,2183,2188,2196,2197,2206,2208,2214,2216,2218,2220,2221,2224,2234}
theorem mem_ids11 (n : Fin 5011) : n ∈ ids11 ↔ n = 2150 ∨ n = 2151 ∨ n = 2153 ∨ n = 2163 ∨ n = 2168 ∨ n = 2176 ∨ n = 2177 ∨ n = 2179 ∨ n = 2183 ∨ n = 2188 ∨ n = 2196 ∨ n = 2197 ∨ n = 2206 ∨ n = 2208 ∨ n = 2214 ∨ n = 2216 ∨ n = 2218 ∨ n = 2220 ∨ n = 2221 ∨ n = 2224 ∨ n = 2234 := by
  simp [ids11]
theorem ids11_card : ids11.card = 21 := by decide +kernel
theorem sub11 (n : Fin 5011) (hn : n ∈ ids11) : n ∈ Paid16GeneralH12.newIDs := by
  rcases (mem_ids11 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids12 : Finset (Fin 5011) := {2236,2238,2242,2244,2245,2249,2252,2253,2258,2262,2263,2267,2286,2288,2290,2292,2296,2302,2303,2304,2306}
theorem mem_ids12 (n : Fin 5011) : n ∈ ids12 ↔ n = 2236 ∨ n = 2238 ∨ n = 2242 ∨ n = 2244 ∨ n = 2245 ∨ n = 2249 ∨ n = 2252 ∨ n = 2253 ∨ n = 2258 ∨ n = 2262 ∨ n = 2263 ∨ n = 2267 ∨ n = 2286 ∨ n = 2288 ∨ n = 2290 ∨ n = 2292 ∨ n = 2296 ∨ n = 2302 ∨ n = 2303 ∨ n = 2304 ∨ n = 2306 := by
  simp [ids12]
theorem ids12_card : ids12.card = 21 := by decide +kernel
theorem sub12 (n : Fin 5011) (hn : n ∈ ids12) : n ∈ Paid16GeneralH13.newIDs := by
  rcases (mem_ids12 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids13 : Finset (Fin 5011) := {2307,2308,2309,2311,2313,2315,2318,2320,2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2336}
theorem mem_ids13 (n : Fin 5011) : n ∈ ids13 ↔ n = 2307 ∨ n = 2308 ∨ n = 2309 ∨ n = 2311 ∨ n = 2313 ∨ n = 2315 ∨ n = 2318 ∨ n = 2320 ∨ n = 2324 ∨ n = 2325 ∨ n = 2326 ∨ n = 2327 ∨ n = 2328 ∨ n = 2329 ∨ n = 2330 ∨ n = 2331 ∨ n = 2332 ∨ n = 2333 ∨ n = 2334 ∨ n = 2335 ∨ n = 2336 := by
  simp [ids13]
theorem ids13_card : ids13.card = 21 := by decide +kernel
theorem sub13 (n : Fin 5011) (hn : n ∈ ids13) : n ∈ Paid16GeneralH14.newIDs := by
  rcases (mem_ids13 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids14 : Finset (Fin 5011) := {2338,2339,2340,2342,2344,2347,2348,2349,2350,2351,2352,2353,2354,2357,2358,2362,2363,2364,2365,2366,2367}
theorem mem_ids14 (n : Fin 5011) : n ∈ ids14 ↔ n = 2338 ∨ n = 2339 ∨ n = 2340 ∨ n = 2342 ∨ n = 2344 ∨ n = 2347 ∨ n = 2348 ∨ n = 2349 ∨ n = 2350 ∨ n = 2351 ∨ n = 2352 ∨ n = 2353 ∨ n = 2354 ∨ n = 2357 ∨ n = 2358 ∨ n = 2362 ∨ n = 2363 ∨ n = 2364 ∨ n = 2365 ∨ n = 2366 ∨ n = 2367 := by
  simp [ids14]
theorem ids14_card : ids14.card = 21 := by decide +kernel
theorem sub14 (n : Fin 5011) (hn : n ∈ ids14) : n ∈ Paid16GeneralH15.newIDs := by
  rcases (mem_ids14 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids15 : Finset (Fin 5011) := {2369,2372,2373,2374,2375,2376,2377,2378,2379,2380,2381,2382,2383,2384,2385,2386,2387,2388,2389,2390,2391}
theorem mem_ids15 (n : Fin 5011) : n ∈ ids15 ↔ n = 2369 ∨ n = 2372 ∨ n = 2373 ∨ n = 2374 ∨ n = 2375 ∨ n = 2376 ∨ n = 2377 ∨ n = 2378 ∨ n = 2379 ∨ n = 2380 ∨ n = 2381 ∨ n = 2382 ∨ n = 2383 ∨ n = 2384 ∨ n = 2385 ∨ n = 2386 ∨ n = 2387 ∨ n = 2388 ∨ n = 2389 ∨ n = 2390 ∨ n = 2391 := by
  simp [ids15]
theorem ids15_card : ids15.card = 21 := by decide +kernel
theorem sub15 (n : Fin 5011) (hn : n ∈ ids15) : n ∈ Paid16GeneralH16.newIDs := by
  rcases (mem_ids15 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids16 : Finset (Fin 5011) := {2392,2393,2394,2395,2396,2397,2398,2399,2400,2401,2402,2403,2404,2405,2406,2407,2408,2409,2410,2411,2412}
theorem mem_ids16 (n : Fin 5011) : n ∈ ids16 ↔ n = 2392 ∨ n = 2393 ∨ n = 2394 ∨ n = 2395 ∨ n = 2396 ∨ n = 2397 ∨ n = 2398 ∨ n = 2399 ∨ n = 2400 ∨ n = 2401 ∨ n = 2402 ∨ n = 2403 ∨ n = 2404 ∨ n = 2405 ∨ n = 2406 ∨ n = 2407 ∨ n = 2408 ∨ n = 2409 ∨ n = 2410 ∨ n = 2411 ∨ n = 2412 := by
  simp [ids16]
theorem ids16_card : ids16.card = 21 := by decide +kernel
theorem sub16 (n : Fin 5011) (hn : n ∈ ids16) : n ∈ Paid16GeneralH17.newIDs := by
  rcases (mem_ids16 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids17 : Finset (Fin 5011) := {2413,2414,2415,2416,2417,2418,2419,2420,2421,2422,2423,2424,2425,2426,2427,2428,2429,2430,2431,2432,2433}
theorem mem_ids17 (n : Fin 5011) : n ∈ ids17 ↔ n = 2413 ∨ n = 2414 ∨ n = 2415 ∨ n = 2416 ∨ n = 2417 ∨ n = 2418 ∨ n = 2419 ∨ n = 2420 ∨ n = 2421 ∨ n = 2422 ∨ n = 2423 ∨ n = 2424 ∨ n = 2425 ∨ n = 2426 ∨ n = 2427 ∨ n = 2428 ∨ n = 2429 ∨ n = 2430 ∨ n = 2431 ∨ n = 2432 ∨ n = 2433 := by
  simp [ids17]
theorem ids17_card : ids17.card = 21 := by decide +kernel
theorem sub17 (n : Fin 5011) (hn : n ∈ ids17) : n ∈ Paid16GeneralH18.newIDs := by
  rcases (mem_ids17 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids18 : Finset (Fin 5011) := {2434,2435,2436,2437,2438,2439,2440,2441,2442,2443,2444,2445,2446,2448,2449,2450,2451,2452,2453,2454,2455}
theorem mem_ids18 (n : Fin 5011) : n ∈ ids18 ↔ n = 2434 ∨ n = 2435 ∨ n = 2436 ∨ n = 2437 ∨ n = 2438 ∨ n = 2439 ∨ n = 2440 ∨ n = 2441 ∨ n = 2442 ∨ n = 2443 ∨ n = 2444 ∨ n = 2445 ∨ n = 2446 ∨ n = 2448 ∨ n = 2449 ∨ n = 2450 ∨ n = 2451 ∨ n = 2452 ∨ n = 2453 ∨ n = 2454 ∨ n = 2455 := by
  simp [ids18]
theorem ids18_card : ids18.card = 21 := by decide +kernel
theorem sub18 (n : Fin 5011) (hn : n ∈ ids18) : n ∈ Paid16GeneralH19.newIDs := by
  rcases (mem_ids18 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids19 : Finset (Fin 5011) := {2456,2457,2458,2459,2460,2461,2462,2463,2464,2465,2466,2467,2468,2469,2470,2471,2473,2474,2475,2476,2477}
theorem mem_ids19 (n : Fin 5011) : n ∈ ids19 ↔ n = 2456 ∨ n = 2457 ∨ n = 2458 ∨ n = 2459 ∨ n = 2460 ∨ n = 2461 ∨ n = 2462 ∨ n = 2463 ∨ n = 2464 ∨ n = 2465 ∨ n = 2466 ∨ n = 2467 ∨ n = 2468 ∨ n = 2469 ∨ n = 2470 ∨ n = 2471 ∨ n = 2473 ∨ n = 2474 ∨ n = 2475 ∨ n = 2476 ∨ n = 2477 := by
  simp [ids19]
theorem ids19_card : ids19.card = 21 := by decide +kernel
theorem sub19 (n : Fin 5011) (hn : n ∈ ids19) : n ∈ Paid16GeneralH20.newIDs := by
  rcases (mem_ids19 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids20 : Finset (Fin 5011) := {2478,2479,2480,2481,2482,2483,2484,2485,2486,2487,2488,2489,2490,2491,2492,2493,2494,2495,2496,2497,2498}
theorem mem_ids20 (n : Fin 5011) : n ∈ ids20 ↔ n = 2478 ∨ n = 2479 ∨ n = 2480 ∨ n = 2481 ∨ n = 2482 ∨ n = 2483 ∨ n = 2484 ∨ n = 2485 ∨ n = 2486 ∨ n = 2487 ∨ n = 2488 ∨ n = 2489 ∨ n = 2490 ∨ n = 2491 ∨ n = 2492 ∨ n = 2493 ∨ n = 2494 ∨ n = 2495 ∨ n = 2496 ∨ n = 2497 ∨ n = 2498 := by
  simp [ids20]
theorem ids20_card : ids20.card = 21 := by decide +kernel
theorem sub20 (n : Fin 5011) (hn : n ∈ ids20) : n ∈ Paid16GeneralH21.newIDs := by
  rcases (mem_ids20 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids21 : Finset (Fin 5011) := {2499,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514,2515,2516,2517,2518,2519}
theorem mem_ids21 (n : Fin 5011) : n ∈ ids21 ↔ n = 2499 ∨ n = 2500 ∨ n = 2501 ∨ n = 2502 ∨ n = 2503 ∨ n = 2504 ∨ n = 2505 ∨ n = 2506 ∨ n = 2507 ∨ n = 2508 ∨ n = 2509 ∨ n = 2510 ∨ n = 2511 ∨ n = 2512 ∨ n = 2513 ∨ n = 2514 ∨ n = 2515 ∨ n = 2516 ∨ n = 2517 ∨ n = 2518 ∨ n = 2519 := by
  simp [ids21]
theorem ids21_card : ids21.card = 21 := by decide +kernel
theorem sub21 (n : Fin 5011) (hn : n ∈ ids21) : n ∈ Paid16GeneralH22.newIDs := by
  rcases (mem_ids21 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids22 : Finset (Fin 5011) := {2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533,2534,2535,2536,2538,2539,2540,2541}
theorem mem_ids22 (n : Fin 5011) : n ∈ ids22 ↔ n = 2520 ∨ n = 2521 ∨ n = 2522 ∨ n = 2523 ∨ n = 2524 ∨ n = 2525 ∨ n = 2526 ∨ n = 2527 ∨ n = 2528 ∨ n = 2529 ∨ n = 2530 ∨ n = 2531 ∨ n = 2532 ∨ n = 2533 ∨ n = 2534 ∨ n = 2535 ∨ n = 2536 ∨ n = 2538 ∨ n = 2539 ∨ n = 2540 ∨ n = 2541 := by
  simp [ids22]
theorem ids22_card : ids22.card = 21 := by decide +kernel
theorem sub22 (n : Fin 5011) (hn : n ∈ ids22) : n ∈ Paid16GeneralH23.newIDs := by
  rcases (mem_ids22 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids23 : Finset (Fin 5011) := {2542,2543,2544,2545,2546,2547,2548,2549,2550,2551,2552,2553,2554,2556,2557,2558,2559,2560,2561,2562,2563}
theorem mem_ids23 (n : Fin 5011) : n ∈ ids23 ↔ n = 2542 ∨ n = 2543 ∨ n = 2544 ∨ n = 2545 ∨ n = 2546 ∨ n = 2547 ∨ n = 2548 ∨ n = 2549 ∨ n = 2550 ∨ n = 2551 ∨ n = 2552 ∨ n = 2553 ∨ n = 2554 ∨ n = 2556 ∨ n = 2557 ∨ n = 2558 ∨ n = 2559 ∨ n = 2560 ∨ n = 2561 ∨ n = 2562 ∨ n = 2563 := by
  simp [ids23]
theorem ids23_card : ids23.card = 21 := by decide +kernel
theorem sub23 (n : Fin 5011) (hn : n ∈ ids23) : n ∈ Paid16GeneralH24.newIDs := by
  rcases (mem_ids23 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids24 : Finset (Fin 5011) := {2564}
theorem mem_ids24 (n : Fin 5011) : n ∈ ids24 ↔ n = 2564 := by
  simp [ids24]
theorem ids24_card : ids24.card = 1 := by decide +kernel
theorem sub24 (n : Fin 5011) (hn : n ∈ ids24) : n ∈ Paid16GeneralH25.newIDs := by
  rcases (mem_ids24 n).mp hn with rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
def newIDs : Finset (Fin 5011) := ids00 ∪ (ids01 ∪ (ids02 ∪ (ids03 ∪ (ids04 ∪ (ids05 ∪ (ids06 ∪ (ids07 ∪ (ids08 ∪ (ids09 ∪ (ids10 ∪ (ids11 ∪ (ids12 ∪ (ids13 ∪ (ids14 ∪ (ids15 ∪ (ids16 ∪ (ids17 ∪ (ids18 ∪ (ids19 ∪ (ids20 ∪ (ids21 ∪ (ids22 ∪ (ids23 ∪ (ids24))))))))))))))))))))))))
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ ids00 ∨ n ∈ ids01 ∨ n ∈ ids02 ∨ n ∈ ids03 ∨ n ∈ ids04 ∨ n ∈ ids05 ∨ n ∈ ids06 ∨ n ∈ ids07 ∨ n ∈ ids08 ∨ n ∈ ids09 ∨ n ∈ ids10 ∨ n ∈ ids11 ∨ n ∈ ids12 ∨ n ∈ ids13 ∨ n ∈ ids14 ∨ n ∈ ids15 ∨ n ∈ ids16 ∨ n ∈ ids17 ∨ n ∈ ids18 ∨ n ∈ ids19 ∨ n ∈ ids20 ∨ n ∈ ids21 ∨ n ∈ ids22 ∨ n ∈ ids23 ∨ n ∈ ids24 := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 505 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Paid16GeneralH01.new_terminal n (sub00 n h)
  · exact Paid16GeneralH02.new_terminal n (sub01 n h)
  · exact Paid16GeneralH03.new_terminal n (sub02 n h)
  · exact Paid16GeneralH04.new_terminal n (sub03 n h)
  · exact Paid16GeneralH05.new_terminal n (sub04 n h)
  · exact Paid16GeneralH06.new_terminal n (sub05 n h)
  · exact Paid16GeneralH07.new_terminal n (sub06 n h)
  · exact Paid16GeneralH08.new_terminal n (sub07 n h)
  · exact Paid16GeneralH09.new_terminal n (sub08 n h)
  · exact Paid16GeneralH10.new_terminal n (sub09 n h)
  · exact Paid16GeneralH11.new_terminal n (sub10 n h)
  · exact Paid16GeneralH12.new_terminal n (sub11 n h)
  · exact Paid16GeneralH13.new_terminal n (sub12 n h)
  · exact Paid16GeneralH14.new_terminal n (sub13 n h)
  · exact Paid16GeneralH15.new_terminal n (sub14 n h)
  · exact Paid16GeneralH16.new_terminal n (sub15 n h)
  · exact Paid16GeneralH17.new_terminal n (sub16 n h)
  · exact Paid16GeneralH18.new_terminal n (sub17 n h)
  · exact Paid16GeneralH19.new_terminal n (sub18 n h)
  · exact Paid16GeneralH20.new_terminal n (sub19 n h)
  · exact Paid16GeneralH21.new_terminal n (sub20 n h)
  · exact Paid16GeneralH22.new_terminal n (sub21 n h)
  · exact Paid16GeneralH23.new_terminal n (sub22 n h)
  · exact Paid16GeneralH24.new_terminal n (sub23 n h)
  · exact Paid16GeneralH25.new_terminal n (sub24 n h)
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Paid16GeneralH01.new_radius n (sub00 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH02.new_radius n (sub01 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH03.new_radius n (sub02 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH04.new_radius n (sub03 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH05.new_radius n (sub04 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH06.new_radius n (sub05 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH07.new_radius n (sub06 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH08.new_radius n (sub07 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH09.new_radius n (sub08 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH10.new_radius n (sub09 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH11.new_radius n (sub10 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH12.new_radius n (sub11 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH13.new_radius n (sub12 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH14.new_radius n (sub13 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH15.new_radius n (sub14 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH16.new_radius n (sub15 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH17.new_radius n (sub16 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH18.new_radius n (sub17 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH19.new_radius n (sub18 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH20.new_radius n (sub19 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH21.new_radius n (sub20 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH22.new_radius n (sub21 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH23.new_radius n (sub22 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH24.new_radius n (sub23 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH25.new_radius n (sub24 n h) y hy0 hy1 hc C Z r hf
theorem disjoint_paid : Disjoint EnergyTerminalBatchB11.paidIDs newIDs := by decide +kernel
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext505
#check @N11Formalization.Paid16GeneralNext505.new_count
#check @N11Formalization.Paid16GeneralNext505.new_radius
#print axioms N11Formalization.Paid16GeneralNext505.new_radius
#print axioms N11Formalization.Paid16GeneralNext505.new_count
#print axioms N11Formalization.Paid16GeneralNext505.new_terminal

