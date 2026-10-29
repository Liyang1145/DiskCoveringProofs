import N11Formalization.Paid16GeneralH42
import N11Formalization.Paid16GeneralH43
import N11Formalization.Paid16GeneralH44
import N11Formalization.Paid16GeneralH45
import N11Formalization.Paid16GeneralH46
import N11Formalization.Paid16GeneralH47
import N11Formalization.Paid16GeneralH48
import N11Formalization.Paid16GeneralH49

/-! Sub-aggregate 3/8: 8 packet modules, 168 ids.
Cardinality is kernel-checked on <= 168-element literal sets only. -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralNext1182S03
open Finset
noncomputable section

def ids16 : Finset (Fin 5011) := {2907,2908,2909,2910,2911,2912,2913,2914,2915,2916,2917,2918,2919,2920,2921,2922,2923,2924,2925,2926,2927}
theorem mem_ids16 (n : Fin 5011) : n ∈ ids16 ↔ n = 2907 ∨ n = 2908 ∨ n = 2909 ∨ n = 2910 ∨ n = 2911 ∨ n = 2912 ∨ n = 2913 ∨ n = 2914 ∨ n = 2915 ∨ n = 2916 ∨ n = 2917 ∨ n = 2918 ∨ n = 2919 ∨ n = 2920 ∨ n = 2921 ∨ n = 2922 ∨ n = 2923 ∨ n = 2924 ∨ n = 2925 ∨ n = 2926 ∨ n = 2927 := by
  simp only [ids16, Finset.mem_insert, Finset.mem_singleton]
theorem ids16_card : ids16.card = 21 := by decide +kernel
theorem sub16 (n : Fin 5011) (hn : n ∈ ids16) : n ∈ Paid16GeneralH42.newIDs := by
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
def ids17 : Finset (Fin 5011) := {2928,2929,2930,2931,2932,2933,2934,2935,2936,2937,2938,2939,2940,2941,2942,2943,2944,2945,2946,2947,2948}
theorem mem_ids17 (n : Fin 5011) : n ∈ ids17 ↔ n = 2928 ∨ n = 2929 ∨ n = 2930 ∨ n = 2931 ∨ n = 2932 ∨ n = 2933 ∨ n = 2934 ∨ n = 2935 ∨ n = 2936 ∨ n = 2937 ∨ n = 2938 ∨ n = 2939 ∨ n = 2940 ∨ n = 2941 ∨ n = 2942 ∨ n = 2943 ∨ n = 2944 ∨ n = 2945 ∨ n = 2946 ∨ n = 2947 ∨ n = 2948 := by
  simp only [ids17, Finset.mem_insert, Finset.mem_singleton]
theorem ids17_card : ids17.card = 21 := by decide +kernel
theorem sub17 (n : Fin 5011) (hn : n ∈ ids17) : n ∈ Paid16GeneralH43.newIDs := by
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
def ids18 : Finset (Fin 5011) := {2949,2950,2951,2952,2953,2954,2955,2956,2958,2959,2960,2961,2963,2964,2968,2969,2970,2972,2974,2975,2976}
theorem mem_ids18 (n : Fin 5011) : n ∈ ids18 ↔ n = 2949 ∨ n = 2950 ∨ n = 2951 ∨ n = 2952 ∨ n = 2953 ∨ n = 2954 ∨ n = 2955 ∨ n = 2956 ∨ n = 2958 ∨ n = 2959 ∨ n = 2960 ∨ n = 2961 ∨ n = 2963 ∨ n = 2964 ∨ n = 2968 ∨ n = 2969 ∨ n = 2970 ∨ n = 2972 ∨ n = 2974 ∨ n = 2975 ∨ n = 2976 := by
  simp only [ids18, Finset.mem_insert, Finset.mem_singleton]
theorem ids18_card : ids18.card = 21 := by decide +kernel
theorem sub18 (n : Fin 5011) (hn : n ∈ ids18) : n ∈ Paid16GeneralH44.newIDs := by
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
def ids19 : Finset (Fin 5011) := {2977,2978,2979,2980,2981,2982,2985,2986,2987,2989,2990,2991,2992,2993,2994,2995,2996,2997,2998,2999,3000}
theorem mem_ids19 (n : Fin 5011) : n ∈ ids19 ↔ n = 2977 ∨ n = 2978 ∨ n = 2979 ∨ n = 2980 ∨ n = 2981 ∨ n = 2982 ∨ n = 2985 ∨ n = 2986 ∨ n = 2987 ∨ n = 2989 ∨ n = 2990 ∨ n = 2991 ∨ n = 2992 ∨ n = 2993 ∨ n = 2994 ∨ n = 2995 ∨ n = 2996 ∨ n = 2997 ∨ n = 2998 ∨ n = 2999 ∨ n = 3000 := by
  simp only [ids19, Finset.mem_insert, Finset.mem_singleton]
theorem ids19_card : ids19.card = 21 := by decide +kernel
theorem sub19 (n : Fin 5011) (hn : n ∈ ids19) : n ∈ Paid16GeneralH45.newIDs := by
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
def ids20 : Finset (Fin 5011) := {3001,3002,3003,3004,3005,3006,3007,3008,3009,3010,3011,3012,3013,3014,3015,3016,3017,3018,3019,3020,3021}
theorem mem_ids20 (n : Fin 5011) : n ∈ ids20 ↔ n = 3001 ∨ n = 3002 ∨ n = 3003 ∨ n = 3004 ∨ n = 3005 ∨ n = 3006 ∨ n = 3007 ∨ n = 3008 ∨ n = 3009 ∨ n = 3010 ∨ n = 3011 ∨ n = 3012 ∨ n = 3013 ∨ n = 3014 ∨ n = 3015 ∨ n = 3016 ∨ n = 3017 ∨ n = 3018 ∨ n = 3019 ∨ n = 3020 ∨ n = 3021 := by
  simp only [ids20, Finset.mem_insert, Finset.mem_singleton]
theorem ids20_card : ids20.card = 21 := by decide +kernel
theorem sub20 (n : Fin 5011) (hn : n ∈ ids20) : n ∈ Paid16GeneralH46.newIDs := by
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
def ids21 : Finset (Fin 5011) := {3022,3023,3024,3025,3026,3027,3028,3029,3030,3031,3032,3033,3034,3035,3036,3037,3038,3039,3041,3042,3043}
theorem mem_ids21 (n : Fin 5011) : n ∈ ids21 ↔ n = 3022 ∨ n = 3023 ∨ n = 3024 ∨ n = 3025 ∨ n = 3026 ∨ n = 3027 ∨ n = 3028 ∨ n = 3029 ∨ n = 3030 ∨ n = 3031 ∨ n = 3032 ∨ n = 3033 ∨ n = 3034 ∨ n = 3035 ∨ n = 3036 ∨ n = 3037 ∨ n = 3038 ∨ n = 3039 ∨ n = 3041 ∨ n = 3042 ∨ n = 3043 := by
  simp only [ids21, Finset.mem_insert, Finset.mem_singleton]
theorem ids21_card : ids21.card = 21 := by decide +kernel
theorem sub21 (n : Fin 5011) (hn : n ∈ ids21) : n ∈ Paid16GeneralH47.newIDs := by
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
def ids22 : Finset (Fin 5011) := {3044,3046,3048,3049,3050,3051,3052,3053,3054,3055,3056,3057,3058,3059,3060,3061,3062,3063,3064,3065,3066}
theorem mem_ids22 (n : Fin 5011) : n ∈ ids22 ↔ n = 3044 ∨ n = 3046 ∨ n = 3048 ∨ n = 3049 ∨ n = 3050 ∨ n = 3051 ∨ n = 3052 ∨ n = 3053 ∨ n = 3054 ∨ n = 3055 ∨ n = 3056 ∨ n = 3057 ∨ n = 3058 ∨ n = 3059 ∨ n = 3060 ∨ n = 3061 ∨ n = 3062 ∨ n = 3063 ∨ n = 3064 ∨ n = 3065 ∨ n = 3066 := by
  simp only [ids22, Finset.mem_insert, Finset.mem_singleton]
theorem ids22_card : ids22.card = 21 := by decide +kernel
theorem sub22 (n : Fin 5011) (hn : n ∈ ids22) : n ∈ Paid16GeneralH48.newIDs := by
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
def ids23 : Finset (Fin 5011) := {3067,3068,3069,3070,3071,3072,3073,3074,3075,3076,3077,3078,3079,3080,3081,3082,3083,3084,3085,3086,3087}
theorem mem_ids23 (n : Fin 5011) : n ∈ ids23 ↔ n = 3067 ∨ n = 3068 ∨ n = 3069 ∨ n = 3070 ∨ n = 3071 ∨ n = 3072 ∨ n = 3073 ∨ n = 3074 ∨ n = 3075 ∨ n = 3076 ∨ n = 3077 ∨ n = 3078 ∨ n = 3079 ∨ n = 3080 ∨ n = 3081 ∨ n = 3082 ∨ n = 3083 ∨ n = 3084 ∨ n = 3085 ∨ n = 3086 ∨ n = 3087 := by
  simp only [ids23, Finset.mem_insert, Finset.mem_singleton]
theorem ids23_card : ids23.card = 21 := by decide +kernel
theorem sub23 (n : Fin 5011) (hn : n ∈ ids23) : n ∈ Paid16GeneralH49.newIDs := by
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
def newIDs : Finset (Fin 5011) := ids16 ∪ (ids17 ∪ (ids18 ∪ (ids19 ∪ (ids20 ∪ (ids21 ∪ (ids22 ∪ (ids23)))))))
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ ids16 ∨ n ∈ ids17 ∨ n ∈ ids18 ∨ n ∈ ids19 ∨ n ∈ ids20 ∨ n ∈ ids21 ∨ n ∈ ids22 ∨ n ∈ ids23 := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 168 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH42.new_terminal n (sub16 n h)
  · exact Paid16GeneralH43.new_terminal n (sub17 n h)
  · exact Paid16GeneralH44.new_terminal n (sub18 n h)
  · exact Paid16GeneralH45.new_terminal n (sub19 n h)
  · exact Paid16GeneralH46.new_terminal n (sub20 n h)
  · exact Paid16GeneralH47.new_terminal n (sub21 n h)
  · exact Paid16GeneralH48.new_terminal n (sub22 n h)
  · exact Paid16GeneralH49.new_terminal n (sub23 n h)
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH42.new_radius n (sub16 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH43.new_radius n (sub17 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH44.new_radius n (sub18 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH45.new_radius n (sub19 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH46.new_radius n (sub20 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH47.new_radius n (sub21 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH48.new_radius n (sub22 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH49.new_radius n (sub23 n h) y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext1182S03
#print axioms N11Formalization.Paid16GeneralNext1182S03.new_count
#print axioms N11Formalization.Paid16GeneralNext1182S03.new_radius
