import D4.PaperOrbitFixedC1B0
import D4.PaperOrbitFixedC1B1
import D4.PaperOrbitFixedC1B2
import D4.PaperOrbitFixedC1B3
import D4.PaperOrbitFixedC1B4
import D4.PaperOrbitFixedC1B5
import D4.PaperOrbitFixedC1B6
import D4.PaperOrbitFixedC1B7
import D4.PaperOrbitFixedC1B8
import D4.PaperOrbitFixedC1B9
namespace D4.PaperSymmetry.C1
theorem fixedCounts_total : (elements.map fixedCount).sum=4200 := by
  simp (config := {implicitDefEqProofs := false}) only [elements,vertices,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    fixedCount_0,fixedCount_1,fixedCount_2,fixedCount_3,fixedCount_4,fixedCount_5,fixedCount_6,fixedCount_7,fixedCount_8,fixedCount_9,fixedCount_10,fixedCount_11,fixedCount_12,fixedCount_13,fixedCount_14,fixedCount_15,fixedCount_16,fixedCount_17,fixedCount_18,fixedCount_19,fixedCount_20,fixedCount_21,fixedCount_22,fixedCount_23,fixedCount_24,fixedCount_25,fixedCount_26,fixedCount_27,fixedCount_28,fixedCount_29,fixedCount_30,fixedCount_31,fixedCount_32,fixedCount_33,fixedCount_34,fixedCount_35,fixedCount_36,fixedCount_37,fixedCount_38,fixedCount_39,fixedCount_40,fixedCount_41,fixedCount_42,fixedCount_43,fixedCount_44,fixedCount_45,fixedCount_46,fixedCount_47,fixedCount_48,fixedCount_49,fixedCount_50,fixedCount_51,fixedCount_52,fixedCount_53,fixedCount_54,fixedCount_55,fixedCount_56,fixedCount_57,fixedCount_58,fixedCount_59,fixedCount_60,fixedCount_61,fixedCount_62,fixedCount_63,fixedCount_64,fixedCount_65,fixedCount_66,fixedCount_67,fixedCount_68,fixedCount_69,fixedCount_70,fixedCount_71,fixedCount_72,fixedCount_73,fixedCount_74,fixedCount_75,fixedCount_76,fixedCount_77,fixedCount_78,fixedCount_79,fixedCount_80,fixedCount_81,fixedCount_82,fixedCount_83,fixedCount_84,fixedCount_85,fixedCount_86,fixedCount_87,fixedCount_88,fixedCount_89,fixedCount_90,fixedCount_91,fixedCount_92,fixedCount_93,fixedCount_94,fixedCount_95,fixedCount_96,fixedCount_97,fixedCount_98,fixedCount_99,fixedCount_100,fixedCount_101,fixedCount_102,fixedCount_103,fixedCount_104,fixedCount_105,fixedCount_106,fixedCount_107,fixedCount_108,fixedCount_109,fixedCount_110,fixedCount_111,fixedCount_112,fixedCount_113,fixedCount_114,fixedCount_115,fixedCount_116,fixedCount_117,fixedCount_118,fixedCount_119]
  norm_num
theorem orbit_count : orbitCount subgroup=35 := by
  have h := sum_fixedCount subgroup elements elements_complete elements_nodup
  rw [fixedCounts_total,elements_length] at h
  omega
end D4.PaperSymmetry.C1
