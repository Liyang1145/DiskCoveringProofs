import N11Formalization.Paid16GeneralH34
import N11Formalization.Paid16GeneralH35
import N11Formalization.Paid16GeneralH36
import N11Formalization.Paid16GeneralH37
import N11Formalization.Paid16GeneralH38
import N11Formalization.Paid16GeneralH39
import N11Formalization.Paid16GeneralH40
import N11Formalization.Paid16GeneralH41

/-! Sub-aggregate 2/8: 8 packet modules, 168 ids.
Cardinality is kernel-checked on <= 168-element literal sets only. -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralNext1182S02
open Finset
noncomputable section

def ids08 : Finset (Fin 5011) := {2737,2738,2739,2740,2741,2742,2743,2744,2745,2746,2747,2748,2749,2750,2751,2752,2753,2754,2755,2756,2757}
theorem mem_ids08 (n : Fin 5011) : n ∈ ids08 ↔ n = 2737 ∨ n = 2738 ∨ n = 2739 ∨ n = 2740 ∨ n = 2741 ∨ n = 2742 ∨ n = 2743 ∨ n = 2744 ∨ n = 2745 ∨ n = 2746 ∨ n = 2747 ∨ n = 2748 ∨ n = 2749 ∨ n = 2750 ∨ n = 2751 ∨ n = 2752 ∨ n = 2753 ∨ n = 2754 ∨ n = 2755 ∨ n = 2756 ∨ n = 2757 := by
  simp only [ids08, Finset.mem_insert, Finset.mem_singleton]
theorem ids08_card : ids08.card = 21 := by decide +kernel
theorem sub08 (n : Fin 5011) (hn : n ∈ ids08) : n ∈ Paid16GeneralH34.newIDs := by
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
def ids09 : Finset (Fin 5011) := {2758,2759,2760,2761,2762,2763,2764,2765,2766,2767,2768,2769,2770,2771,2772,2773,2774,2775,2776,2777,2778}
theorem mem_ids09 (n : Fin 5011) : n ∈ ids09 ↔ n = 2758 ∨ n = 2759 ∨ n = 2760 ∨ n = 2761 ∨ n = 2762 ∨ n = 2763 ∨ n = 2764 ∨ n = 2765 ∨ n = 2766 ∨ n = 2767 ∨ n = 2768 ∨ n = 2769 ∨ n = 2770 ∨ n = 2771 ∨ n = 2772 ∨ n = 2773 ∨ n = 2774 ∨ n = 2775 ∨ n = 2776 ∨ n = 2777 ∨ n = 2778 := by
  simp only [ids09, Finset.mem_insert, Finset.mem_singleton]
theorem ids09_card : ids09.card = 21 := by decide +kernel
theorem sub09 (n : Fin 5011) (hn : n ∈ ids09) : n ∈ Paid16GeneralH35.newIDs := by
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
def ids10 : Finset (Fin 5011) := {2779,2780,2781,2782,2783,2784,2785,2786,2787,2788,2789,2790,2791,2792,2793,2794,2795,2796,2797,2798,2799}
theorem mem_ids10 (n : Fin 5011) : n ∈ ids10 ↔ n = 2779 ∨ n = 2780 ∨ n = 2781 ∨ n = 2782 ∨ n = 2783 ∨ n = 2784 ∨ n = 2785 ∨ n = 2786 ∨ n = 2787 ∨ n = 2788 ∨ n = 2789 ∨ n = 2790 ∨ n = 2791 ∨ n = 2792 ∨ n = 2793 ∨ n = 2794 ∨ n = 2795 ∨ n = 2796 ∨ n = 2797 ∨ n = 2798 ∨ n = 2799 := by
  simp only [ids10, Finset.mem_insert, Finset.mem_singleton]
theorem ids10_card : ids10.card = 21 := by decide +kernel
theorem sub10 (n : Fin 5011) (hn : n ∈ ids10) : n ∈ Paid16GeneralH36.newIDs := by
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
def ids11 : Finset (Fin 5011) := {2800,2801,2802,2803,2804,2805,2806,2807,2808,2809,2810,2811,2812,2813,2814,2815,2816,2817,2818,2819,2820}
theorem mem_ids11 (n : Fin 5011) : n ∈ ids11 ↔ n = 2800 ∨ n = 2801 ∨ n = 2802 ∨ n = 2803 ∨ n = 2804 ∨ n = 2805 ∨ n = 2806 ∨ n = 2807 ∨ n = 2808 ∨ n = 2809 ∨ n = 2810 ∨ n = 2811 ∨ n = 2812 ∨ n = 2813 ∨ n = 2814 ∨ n = 2815 ∨ n = 2816 ∨ n = 2817 ∨ n = 2818 ∨ n = 2819 ∨ n = 2820 := by
  simp only [ids11, Finset.mem_insert, Finset.mem_singleton]
theorem ids11_card : ids11.card = 21 := by decide +kernel
theorem sub11 (n : Fin 5011) (hn : n ∈ ids11) : n ∈ Paid16GeneralH37.newIDs := by
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
def ids12 : Finset (Fin 5011) := {2821,2822,2823,2824,2825,2826,2827,2828,2829,2830,2831,2832,2833,2834,2835,2836,2837,2838,2839,2840,2841}
theorem mem_ids12 (n : Fin 5011) : n ∈ ids12 ↔ n = 2821 ∨ n = 2822 ∨ n = 2823 ∨ n = 2824 ∨ n = 2825 ∨ n = 2826 ∨ n = 2827 ∨ n = 2828 ∨ n = 2829 ∨ n = 2830 ∨ n = 2831 ∨ n = 2832 ∨ n = 2833 ∨ n = 2834 ∨ n = 2835 ∨ n = 2836 ∨ n = 2837 ∨ n = 2838 ∨ n = 2839 ∨ n = 2840 ∨ n = 2841 := by
  simp only [ids12, Finset.mem_insert, Finset.mem_singleton]
theorem ids12_card : ids12.card = 21 := by decide +kernel
theorem sub12 (n : Fin 5011) (hn : n ∈ ids12) : n ∈ Paid16GeneralH38.newIDs := by
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
def ids13 : Finset (Fin 5011) := {2842,2843,2844,2845,2846,2847,2848,2849,2850,2851,2852,2853,2854,2855,2856,2857,2858,2859,2860,2861,2862}
theorem mem_ids13 (n : Fin 5011) : n ∈ ids13 ↔ n = 2842 ∨ n = 2843 ∨ n = 2844 ∨ n = 2845 ∨ n = 2846 ∨ n = 2847 ∨ n = 2848 ∨ n = 2849 ∨ n = 2850 ∨ n = 2851 ∨ n = 2852 ∨ n = 2853 ∨ n = 2854 ∨ n = 2855 ∨ n = 2856 ∨ n = 2857 ∨ n = 2858 ∨ n = 2859 ∨ n = 2860 ∨ n = 2861 ∨ n = 2862 := by
  simp only [ids13, Finset.mem_insert, Finset.mem_singleton]
theorem ids13_card : ids13.card = 21 := by decide +kernel
theorem sub13 (n : Fin 5011) (hn : n ∈ ids13) : n ∈ Paid16GeneralH39.newIDs := by
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
def ids14 : Finset (Fin 5011) := {2863,2864,2865,2866,2867,2868,2869,2870,2871,2872,2873,2874,2875,2876,2877,2878,2879,2881,2882,2883,2884}
theorem mem_ids14 (n : Fin 5011) : n ∈ ids14 ↔ n = 2863 ∨ n = 2864 ∨ n = 2865 ∨ n = 2866 ∨ n = 2867 ∨ n = 2868 ∨ n = 2869 ∨ n = 2870 ∨ n = 2871 ∨ n = 2872 ∨ n = 2873 ∨ n = 2874 ∨ n = 2875 ∨ n = 2876 ∨ n = 2877 ∨ n = 2878 ∨ n = 2879 ∨ n = 2881 ∨ n = 2882 ∨ n = 2883 ∨ n = 2884 := by
  simp only [ids14, Finset.mem_insert, Finset.mem_singleton]
theorem ids14_card : ids14.card = 21 := by decide +kernel
theorem sub14 (n : Fin 5011) (hn : n ∈ ids14) : n ∈ Paid16GeneralH40.newIDs := by
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
def ids15 : Finset (Fin 5011) := {2885,2886,2887,2889,2890,2891,2892,2893,2894,2895,2896,2897,2898,2899,2900,2901,2902,2903,2904,2905,2906}
theorem mem_ids15 (n : Fin 5011) : n ∈ ids15 ↔ n = 2885 ∨ n = 2886 ∨ n = 2887 ∨ n = 2889 ∨ n = 2890 ∨ n = 2891 ∨ n = 2892 ∨ n = 2893 ∨ n = 2894 ∨ n = 2895 ∨ n = 2896 ∨ n = 2897 ∨ n = 2898 ∨ n = 2899 ∨ n = 2900 ∨ n = 2901 ∨ n = 2902 ∨ n = 2903 ∨ n = 2904 ∨ n = 2905 ∨ n = 2906 := by
  simp only [ids15, Finset.mem_insert, Finset.mem_singleton]
theorem ids15_card : ids15.card = 21 := by decide +kernel
theorem sub15 (n : Fin 5011) (hn : n ∈ ids15) : n ∈ Paid16GeneralH41.newIDs := by
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
def newIDs : Finset (Fin 5011) := ids08 ∪ (ids09 ∪ (ids10 ∪ (ids11 ∪ (ids12 ∪ (ids13 ∪ (ids14 ∪ (ids15)))))))
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ ids08 ∨ n ∈ ids09 ∨ n ∈ ids10 ∨ n ∈ ids11 ∨ n ∈ ids12 ∨ n ∈ ids13 ∨ n ∈ ids14 ∨ n ∈ ids15 := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 168 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH34.new_terminal n (sub08 n h)
  · exact Paid16GeneralH35.new_terminal n (sub09 n h)
  · exact Paid16GeneralH36.new_terminal n (sub10 n h)
  · exact Paid16GeneralH37.new_terminal n (sub11 n h)
  · exact Paid16GeneralH38.new_terminal n (sub12 n h)
  · exact Paid16GeneralH39.new_terminal n (sub13 n h)
  · exact Paid16GeneralH40.new_terminal n (sub14 n h)
  · exact Paid16GeneralH41.new_terminal n (sub15 n h)
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH34.new_radius n (sub08 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH35.new_radius n (sub09 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH36.new_radius n (sub10 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH37.new_radius n (sub11 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH38.new_radius n (sub12 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH39.new_radius n (sub13 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH40.new_radius n (sub14 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH41.new_radius n (sub15 n h) y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext1182S02
#print axioms N11Formalization.Paid16GeneralNext1182S02.new_count
#print axioms N11Formalization.Paid16GeneralNext1182S02.new_radius
