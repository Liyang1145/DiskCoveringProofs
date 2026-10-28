import N11Formalization.Paid16GeneralH26
import N11Formalization.Paid16GeneralH27
import N11Formalization.Paid16GeneralH28
import N11Formalization.Paid16GeneralH29
import N11Formalization.Paid16GeneralH30
import N11Formalization.Paid16GeneralH31
import N11Formalization.Paid16GeneralH32
import N11Formalization.Paid16GeneralH33

/-! Sub-aggregate 1/8: 8 packet modules, 168 ids.
Cardinality is kernel-checked on <= 168-element literal sets only. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.Paid16GeneralNext1182S01
open Finset
noncomputable section

def ids00 : Finset (Fin 5011) := {2565,2566,2567,2568,2569,2570,2571,2572,2573,2574,2575,2576,2577,2578,2579,2580,2581,2582,2583,2584,2585}
theorem mem_ids00 (n : Fin 5011) : n ∈ ids00 ↔ n = 2565 ∨ n = 2566 ∨ n = 2567 ∨ n = 2568 ∨ n = 2569 ∨ n = 2570 ∨ n = 2571 ∨ n = 2572 ∨ n = 2573 ∨ n = 2574 ∨ n = 2575 ∨ n = 2576 ∨ n = 2577 ∨ n = 2578 ∨ n = 2579 ∨ n = 2580 ∨ n = 2581 ∨ n = 2582 ∨ n = 2583 ∨ n = 2584 ∨ n = 2585 := by
  simp only [ids00, Finset.mem_insert, Finset.mem_singleton]
theorem ids00_card : ids00.card = 21 := by decide +kernel
theorem sub00 (n : Fin 5011) (hn : n ∈ ids00) : n ∈ Paid16GeneralH26.newIDs := by
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
def ids01 : Finset (Fin 5011) := {2586,2587,2588,2589,2590,2591,2592,2593,2594,2595,2596,2597,2598,2599,2600,2601,2602,2603,2604,2605,2606}
theorem mem_ids01 (n : Fin 5011) : n ∈ ids01 ↔ n = 2586 ∨ n = 2587 ∨ n = 2588 ∨ n = 2589 ∨ n = 2590 ∨ n = 2591 ∨ n = 2592 ∨ n = 2593 ∨ n = 2594 ∨ n = 2595 ∨ n = 2596 ∨ n = 2597 ∨ n = 2598 ∨ n = 2599 ∨ n = 2600 ∨ n = 2601 ∨ n = 2602 ∨ n = 2603 ∨ n = 2604 ∨ n = 2605 ∨ n = 2606 := by
  simp only [ids01, Finset.mem_insert, Finset.mem_singleton]
theorem ids01_card : ids01.card = 21 := by decide +kernel
theorem sub01 (n : Fin 5011) (hn : n ∈ ids01) : n ∈ Paid16GeneralH27.newIDs := by
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
def ids02 : Finset (Fin 5011) := {2607,2608,2609,2610,2611,2612,2613,2615,2616,2617,2618,2619,2620,2621,2623,2624,2625,2626,2627,2628,2629}
theorem mem_ids02 (n : Fin 5011) : n ∈ ids02 ↔ n = 2607 ∨ n = 2608 ∨ n = 2609 ∨ n = 2610 ∨ n = 2611 ∨ n = 2612 ∨ n = 2613 ∨ n = 2615 ∨ n = 2616 ∨ n = 2617 ∨ n = 2618 ∨ n = 2619 ∨ n = 2620 ∨ n = 2621 ∨ n = 2623 ∨ n = 2624 ∨ n = 2625 ∨ n = 2626 ∨ n = 2627 ∨ n = 2628 ∨ n = 2629 := by
  simp only [ids02, Finset.mem_insert, Finset.mem_singleton]
theorem ids02_card : ids02.card = 21 := by decide +kernel
theorem sub02 (n : Fin 5011) (hn : n ∈ ids02) : n ∈ Paid16GeneralH28.newIDs := by
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
def ids03 : Finset (Fin 5011) := {2630,2631,2632,2633,2634,2635,2636,2637,2638,2639,2640,2641,2642,2643,2644,2645,2646,2647,2648,2649,2650}
theorem mem_ids03 (n : Fin 5011) : n ∈ ids03 ↔ n = 2630 ∨ n = 2631 ∨ n = 2632 ∨ n = 2633 ∨ n = 2634 ∨ n = 2635 ∨ n = 2636 ∨ n = 2637 ∨ n = 2638 ∨ n = 2639 ∨ n = 2640 ∨ n = 2641 ∨ n = 2642 ∨ n = 2643 ∨ n = 2644 ∨ n = 2645 ∨ n = 2646 ∨ n = 2647 ∨ n = 2648 ∨ n = 2649 ∨ n = 2650 := by
  simp only [ids03, Finset.mem_insert, Finset.mem_singleton]
theorem ids03_card : ids03.card = 21 := by decide +kernel
theorem sub03 (n : Fin 5011) (hn : n ∈ ids03) : n ∈ Paid16GeneralH29.newIDs := by
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
def ids04 : Finset (Fin 5011) := {2651,2652,2653,2654,2655,2656,2657,2658,2659,2660,2662,2663,2664,2665,2666,2667,2668,2669,2670,2671,2672}
theorem mem_ids04 (n : Fin 5011) : n ∈ ids04 ↔ n = 2651 ∨ n = 2652 ∨ n = 2653 ∨ n = 2654 ∨ n = 2655 ∨ n = 2656 ∨ n = 2657 ∨ n = 2658 ∨ n = 2659 ∨ n = 2660 ∨ n = 2662 ∨ n = 2663 ∨ n = 2664 ∨ n = 2665 ∨ n = 2666 ∨ n = 2667 ∨ n = 2668 ∨ n = 2669 ∨ n = 2670 ∨ n = 2671 ∨ n = 2672 := by
  simp only [ids04, Finset.mem_insert, Finset.mem_singleton]
theorem ids04_card : ids04.card = 21 := by decide +kernel
theorem sub04 (n : Fin 5011) (hn : n ∈ ids04) : n ∈ Paid16GeneralH30.newIDs := by
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
def ids05 : Finset (Fin 5011) := {2673,2674,2676,2677,2678,2679,2680,2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2691,2692,2693,2694}
theorem mem_ids05 (n : Fin 5011) : n ∈ ids05 ↔ n = 2673 ∨ n = 2674 ∨ n = 2676 ∨ n = 2677 ∨ n = 2678 ∨ n = 2679 ∨ n = 2680 ∨ n = 2681 ∨ n = 2682 ∨ n = 2683 ∨ n = 2684 ∨ n = 2685 ∨ n = 2686 ∨ n = 2687 ∨ n = 2688 ∨ n = 2689 ∨ n = 2690 ∨ n = 2691 ∨ n = 2692 ∨ n = 2693 ∨ n = 2694 := by
  simp only [ids05, Finset.mem_insert, Finset.mem_singleton]
theorem ids05_card : ids05.card = 21 := by decide +kernel
theorem sub05 (n : Fin 5011) (hn : n ∈ ids05) : n ∈ Paid16GeneralH31.newIDs := by
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
def ids06 : Finset (Fin 5011) := {2695,2696,2697,2698,2699,2700,2701,2702,2703,2704,2705,2706,2707,2708,2709,2710,2711,2712,2713,2714,2715}
theorem mem_ids06 (n : Fin 5011) : n ∈ ids06 ↔ n = 2695 ∨ n = 2696 ∨ n = 2697 ∨ n = 2698 ∨ n = 2699 ∨ n = 2700 ∨ n = 2701 ∨ n = 2702 ∨ n = 2703 ∨ n = 2704 ∨ n = 2705 ∨ n = 2706 ∨ n = 2707 ∨ n = 2708 ∨ n = 2709 ∨ n = 2710 ∨ n = 2711 ∨ n = 2712 ∨ n = 2713 ∨ n = 2714 ∨ n = 2715 := by
  simp only [ids06, Finset.mem_insert, Finset.mem_singleton]
theorem ids06_card : ids06.card = 21 := by decide +kernel
theorem sub06 (n : Fin 5011) (hn : n ∈ ids06) : n ∈ Paid16GeneralH32.newIDs := by
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
def ids07 : Finset (Fin 5011) := {2716,2717,2718,2719,2720,2721,2722,2723,2724,2725,2726,2727,2728,2729,2730,2731,2732,2733,2734,2735,2736}
theorem mem_ids07 (n : Fin 5011) : n ∈ ids07 ↔ n = 2716 ∨ n = 2717 ∨ n = 2718 ∨ n = 2719 ∨ n = 2720 ∨ n = 2721 ∨ n = 2722 ∨ n = 2723 ∨ n = 2724 ∨ n = 2725 ∨ n = 2726 ∨ n = 2727 ∨ n = 2728 ∨ n = 2729 ∨ n = 2730 ∨ n = 2731 ∨ n = 2732 ∨ n = 2733 ∨ n = 2734 ∨ n = 2735 ∨ n = 2736 := by
  simp only [ids07, Finset.mem_insert, Finset.mem_singleton]
theorem ids07_card : ids07.card = 21 := by decide +kernel
theorem sub07 (n : Fin 5011) (hn : n ∈ ids07) : n ∈ Paid16GeneralH33.newIDs := by
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
def newIDs : Finset (Fin 5011) := ids00 ∪ (ids01 ∪ (ids02 ∪ (ids03 ∪ (ids04 ∪ (ids05 ∪ (ids06 ∪ (ids07)))))))
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ ids00 ∨ n ∈ ids01 ∨ n ∈ ids02 ∨ n ∈ ids03 ∨ n ∈ ids04 ∨ n ∈ ids05 ∨ n ∈ ids06 ∨ n ∈ ids07 := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 168 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH26.new_terminal n (sub00 n h)
  · exact Paid16GeneralH27.new_terminal n (sub01 n h)
  · exact Paid16GeneralH28.new_terminal n (sub02 n h)
  · exact Paid16GeneralH29.new_terminal n (sub03 n h)
  · exact Paid16GeneralH30.new_terminal n (sub04 n h)
  · exact Paid16GeneralH31.new_terminal n (sub05 n h)
  · exact Paid16GeneralH32.new_terminal n (sub06 n h)
  · exact Paid16GeneralH33.new_terminal n (sub07 n h)
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH26.new_radius n (sub00 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH27.new_radius n (sub01 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH28.new_radius n (sub02 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH29.new_radius n (sub03 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH30.new_radius n (sub04 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH31.new_radius n (sub05 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH32.new_radius n (sub06 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH33.new_radius n (sub07 n h) y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext1182S01
#print axioms N11Formalization.Paid16GeneralNext1182S01.new_count
#print axioms N11Formalization.Paid16GeneralNext1182S01.new_radius
