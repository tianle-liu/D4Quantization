import D4.PaperOrbitFixedC2B0
namespace D4.PaperSymmetry.C2
theorem elements_nodup : elements.Nodup := by decide +kernel
theorem elements_length : elements.length=12 := by kernel_rfl
theorem elements_complete (p:Perm) : p∈elements ↔ p∈subgroup := Iff.rfl
theorem fixedCounts_total : (elements.map fixedCount).sum=2700 := by
  simp (config := {implicitDefEqProofs := false}) only [elements,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    fixedCount_0,fixedCount_1,fixedCount_2,fixedCount_3,fixedCount_4,fixedCount_5,fixedCount_6,fixedCount_7,fixedCount_8,fixedCount_9,fixedCount_10,fixedCount_11]
  norm_num
theorem orbit_count : orbitCount subgroup=225 := by
  have h := sum_fixedCount subgroup elements elements_complete elements_nodup
  rw [fixedCounts_total,elements_length] at h
  omega
end D4.PaperSymmetry.C2
