import D4.PaperOrbitFixedC3B0
import D4.PaperOrbitFixedC3B1
import D4.PaperOrbitFixedC3B2
namespace D4.PaperSymmetry.C3
theorem elements_nodup : elements.Nodup := by decide +kernel
theorem elements_length : elements.length=36 := by kernel_rfl
theorem elements_complete (p:Perm) : p∈elements ↔ p∈subgroup := Iff.rfl
theorem fixedCounts_total : (elements.map fixedCount).sum=3276 := by
  simp (config := {implicitDefEqProofs := false}) only [elements,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    fixedCount_0,fixedCount_1,fixedCount_2,fixedCount_3,fixedCount_4,fixedCount_5,fixedCount_6,fixedCount_7,fixedCount_8,fixedCount_9,fixedCount_10,fixedCount_11,fixedCount_12,fixedCount_13,fixedCount_14,fixedCount_15,fixedCount_16,fixedCount_17,fixedCount_18,fixedCount_19,fixedCount_20,fixedCount_21,fixedCount_22,fixedCount_23,fixedCount_24,fixedCount_25,fixedCount_26,fixedCount_27,fixedCount_28,fixedCount_29,fixedCount_30,fixedCount_31,fixedCount_32,fixedCount_33,fixedCount_34,fixedCount_35]
  norm_num
theorem orbit_count : orbitCount subgroup=91 := by
  have h := sum_fixedCount subgroup elements elements_complete elements_nodup
  rw [fixedCounts_total,elements_length] at h
  omega
end D4.PaperSymmetry.C3
