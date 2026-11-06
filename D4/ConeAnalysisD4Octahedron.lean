import D4.ConeAnalysisD4Facets

/-! Coordinates of an actual octahedral D4 facet. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace D4.PhysicalD4
open Set Euclidean Analytic FacetGeometry
open scoped InnerProductSpace

def standardRoot : Point := integerPoint ![1,1,0,0]

theorem standardRoot_isFacet : IsFacetVector lattice standardRoot := by
  apply root_isFacet
  norm_num [IsRoot, Fin.sum_univ_succ]

theorem standard_face_iff (x : Point) : x ∈ face lattice standardRoot ↔
    x 0+x 1=1 ∧ |x 2| ≤ min (x 0) (x 1) ∧ |x 3| ≤ min (x 0) (x 1) := by
  have hn : ‖standardRoot‖^2 = 2 := by
    rw [standardRoot, integerPoint_norm_sq]
    norm_num [Fin.sum_univ_succ]
  have hin : ⟪x,standardRoot⟫_ℝ = x 0+x 1 := by
    rw [standardRoot, integerPoint_inner]
    norm_num [Fin.sum_univ_succ]
    rfl
  constructor
  · rintro ⟨hx,he⟩
    rw [hn,hin] at he
    have he' : x 0+x 1=1 := by linarith
    rw [voronoi_eq_rootPolytope] at hx
    have h01 := hx 0 1 (by decide)
    have ha : 0 ≤ x 0 := by linarith [neg_le_abs (x 0), le_abs_self (x 1)]
    have hb : 0 ≤ x 1 := by linarith [le_abs_self (x 0), neg_le_abs (x 1)]
    have h02 := hx 0 2 (by decide)
    have h12 := hx 1 2 (by decide)
    have h03 := hx 0 3 (by decide)
    have h13 := hx 1 3 (by decide)
    rw [abs_of_nonneg ha] at h02 h03
    rw [abs_of_nonneg hb] at h12 h13
    exact ⟨he', le_min (by linarith) (by linarith), le_min (by linarith) (by linarith)⟩
  · rintro ⟨he,hc,hd⟩
    have hc0 := hc.trans (min_le_left _ _)
    have hc1 := hc.trans (min_le_right _ _)
    have hd0 := hd.trans (min_le_left _ _)
    have hd1 := hd.trans (min_le_right _ _)
    have ha := (abs_nonneg (x 2)).trans hc0
    have hb := (abs_nonneg (x 2)).trans hc1
    refine ⟨?_, by rw [hn,hin,he]; norm_num⟩
    rw [voronoi_eq_rootPolytope]
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change |x 0|+|x 1| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 0|+|x 2| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 0|+|x 3| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 1|+|x 0| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 1|+|x 2| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 1|+|x 3| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 2|+|x 0| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 2|+|x 1| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 2|+|x 3| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 3|+|x 0| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 3|+|x 1| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith
    · change |x 3|+|x 2| ≤ 1
      simp only [abs_of_nonneg ha,abs_of_nonneg hb]
      linarith

def octahedronChart (a : Fin 3 → ℝ) : Point :=
  (WithLp.equiv 2 Vec).symm ![a 0/2,-a 0/2,(a 1+a 2)/2,(a 1-a 2)/2]

theorem octahedronChart_norm_sq (a : Fin 3 → ℝ) :
    ‖octahedronChart a‖^2 = ((a 0)^2+(a 1)^2+(a 2)^2)/2 := by
  rw [point_norm_sq]
  norm_num [octahedronChart, Fin.sum_univ_succ]
  ring

private theorem max_abs_add_sub (a b : ℝ) : max |a+b| |a-b| = |a|+|b| := by
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

private theorem min_half (a : ℝ) : min ((1+a)/2) ((1-a)/2) = (1-|a|)/2 := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha, min_eq_right (by linarith)]
  · rw [abs_of_nonpos ha, min_eq_left (by linarith)]
    ring

theorem standard_chart_coordinates (a : Fin 3 → ℝ) : (1/2:ℝ) • standardRoot+octahedronChart a =
    (WithLp.equiv 2 Vec).symm ![(1+a 0)/2,(1-a 0)/2,(a 1+a 2)/2,(a 1-a 2)/2] := by
  ext i
  fin_cases i <;> norm_num [standardRoot,integerPoint,castVec,octahedronChart] <;> ring

theorem standard_face_chart (a : Fin 3 → ℝ) :
    (1/2:ℝ) • standardRoot+octahedronChart a ∈ face lattice standardRoot ↔
      |a 0|+|a 1|+|a 2| ≤ 1 := by
  rw [standard_face_iff]
  rw [standard_chart_coordinates]
  change (1+a 0)/2+(1-a 0)/2=1 ∧
    |(a 1+a 2)/2| ≤ min ((1+a 0)/2) ((1-a 0)/2) ∧
    |(a 1-a 2)/2| ≤ min ((1+a 0)/2) ((1-a 0)/2) ↔ _
  rw [min_half]
  simp only [abs_div, show |(2:ℝ)| = 2 by norm_num]
  have hm := max_abs_add_sub (a 1) (a 2)
  constructor
  · rintro ⟨_,h1,h2⟩
    have hmax : max |a 1+a 2| |a 1-a 2| ≤ 1-|a 0| := max_le (by linarith) (by linarith)
    rw [hm] at hmax
    linarith
  · intro h
    refine ⟨by ring, ?_, ?_⟩
    · have h1 := le_max_left |a 1+a 2| |a 1-a 2|
      rw [hm] at h1
      linarith
    · have h2 := le_max_right |a 1+a 2| |a 1-a 2|
      rw [hm] at h2
      linarith

/-- A facet is an affine image of the standard regular cross-polytope.
The chart's norm identity above gives its common Euclidean scale. -/
theorem standard_face_eq_octahedron : face lattice standardRoot =
    {x | ∃ a : Fin 3 → ℝ, |a 0|+|a 1|+|a 2| ≤ 1 ∧
      (1/2:ℝ) • standardRoot+octahedronChart a=x} := by
  ext x
  constructor
  · intro hx
    let a : Fin 3 → ℝ := ![x 0-x 1,x 2+x 3,x 2-x 3]
    have he := (standard_face_iff x).mp hx
    have hc : (1/2:ℝ) • standardRoot+octahedronChart a=x := by
      rw [standard_chart_coordinates]
      ext i
      fin_cases i
      · change (1+(x 0-x 1))/2=x 0
        linarith [he.1]
      · change (1-(x 0-x 1))/2=x 1
        linarith [he.1]
      · change ((x 2+x 3)+(x 2-x 3))/2=x 2
        ring
      · change ((x 2+x 3)-(x 2-x 3))/2=x 3
        ring
    exact ⟨a,(standard_face_chart a).mp (hc ▸ hx),hc⟩
  · rintro ⟨a,ha,rfl⟩
    exact (standard_face_chart a).mpr ha


def coordinateSigns (s t : Bool) : Point ≃ₗᵢ[ℝ] Point :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin 4 =>
    if (i=0 ∧ s=true) ∨ (i=1 ∧ t=true) then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

def signedPermutation (π : Equiv.Perm (Fin 4)) (s t : Bool) : Point ≃ₗᵢ[ℝ] Point :=
  (coordinateSigns s t).trans (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ π)

theorem abs_signedPermutation (π : Equiv.Perm (Fin 4)) (s t : Bool) (x : Point) (i : Fin 4) :
    |signedPermutation π s t x i| = |x (π.symm i)| := by
  simp only [signedPermutation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  change |coordinateSigns s t x (π.symm i)| = _
  simp only [coordinateSigns, LinearIsometryEquiv.piLpCongrRight_apply]
  change |(if (π.symm i=0 ∧ s=true) ∨ (π.symm i=1 ∧ t=true) then
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) else LinearIsometryEquiv.refl ℝ ℝ) (x (π.symm i))| = _
  split_ifs <;> simp

theorem signedPermutation_mem_voronoi (π : Equiv.Perm (Fin 4)) (s t : Bool) (x : Point) :
    signedPermutation π s t x ∈ voronoi lattice ↔ x ∈ voronoi lattice := by
  rw [voronoi_eq_rootPolytope]
  constructor
  · intro h i j hij
    have hh := h (π i) (π j) (fun he => hij (π.injective he))
    rw [abs_signedPermutation,abs_signedPermutation] at hh
    change |x (π.symm (π i))|+|x (π.symm (π j))| ≤ 1 at hh
    rw [π.symm_apply_apply i,π.symm_apply_apply j] at hh
    exact hh
  · intro h i j hij
    rw [abs_signedPermutation, abs_signedPermutation]
    exact h _ _ (fun he => hij (π.symm.injective he))

theorem signedPermutation_face_image (π : Equiv.Perm (Fin 4)) (s t : Bool) (z : Point) :
    signedPermutation π s t '' face lattice z = face lattice (signedPermutation π s t z) := by
  let e := signedPermutation π s t
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(signedPermutation_mem_voronoi π s t x).mpr hx.1, ?_⟩
    rw [e.inner_map_map, e.norm_map]
    exact hx.2
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    refine ⟨(signedPermutation_mem_voronoi π s t (e.symm y)).mp (by simpa [e] using hy.1), ?_⟩
    have hh := hy.2
    rw [← e.apply_symm_apply y, e.inner_map_map, e.norm_map] at hh
    exact hh

def signedIntegerPermutation (π : Equiv.Perm (Fin 4)) (s t : Bool) (z : IntVec) : IntVec :=
  fun i => if (π.symm i=0 ∧ s=true) ∨ (π.symm i=1 ∧ t=true) then
    -z (π.symm i) else z (π.symm i)

theorem signedPermutation_integerPoint (π : Equiv.Perm (Fin 4)) (s t : Bool) (z : IntVec) :
    signedPermutation π s t (integerPoint z) = integerPoint (signedIntegerPermutation π s t z) := by
  ext i
  simp only [signedPermutation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  change coordinateSigns s t (integerPoint z) (π.symm i) = _
  simp only [coordinateSigns, LinearIsometryEquiv.piLpCongrRight_apply]
  change (if (π.symm i=0 ∧ s=true) ∨ (π.symm i=1 ∧ t=true) then
      (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) else LinearIsometryEquiv.refl ℝ ℝ)
      (z (π.symm i) : ℝ) =
    ((if (π.symm i=0 ∧ s=true) ∨ (π.symm i=1 ∧ t=true) then
      -z (π.symm i) else z (π.symm i) : ℤ) : ℝ)
  split_ifs <;> simp

theorem rootTable_face_isometric (k : Fin 24) :
    ∃ e : Point ≃ₗᵢ[ℝ] Point, e '' face lattice standardRoot = face lattice (integerPoint (rootTable k)) := by
  fin_cases k
  · refine ⟨signedPermutation (Equiv.refl (Fin 4)) true true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.refl (Fin 4)) true false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.refl (Fin 4)) false true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.refl (Fin 4)) false false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.swap (1:Fin 4) 2) true true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.swap (1:Fin 4) 2) true false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.swap (1:Fin 4) 2) false true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.swap (1:Fin 4) 2) false false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.swap (1:Fin 4) 3) true true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.swap (1:Fin 4) 3) true false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.swap (1:Fin 4) 3) false true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation (Equiv.swap (1:Fin 4) 3) false false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (0:Fin 4) 2)) true true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (0:Fin 4) 2)) true false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (0:Fin 4) 2)) false true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (0:Fin 4) 2)) false false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (0:Fin 4) 3)) true true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (0:Fin 4) 3)) true false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (0:Fin 4) 3)) false true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (0:Fin 4) 3)) false false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 2).trans (Equiv.swap (1:Fin 4) 3)) true true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 2).trans (Equiv.swap (1:Fin 4) 3)) true false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 2).trans (Equiv.swap (1:Fin 4) 3)) false true, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide
  · refine ⟨signedPermutation ((Equiv.swap (0:Fin 4) 2).trans (Equiv.swap (1:Fin 4) 3)) false false, ?_⟩
    rw [signedPermutation_face_image]
    apply congrArg (face lattice)
    rw [standardRoot, signedPermutation_integerPoint]
    apply congrArg integerPoint
    decide

/-- Every actual D4 facet is isometric to the explicitly parametrized regular octahedron. -/
theorem facet_isometric_octahedron {z : Point} (hz : IsFacetVector lattice z) :
    ∃ e : Point ≃ₗᵢ[ℝ] Point, face lattice z =
      e '' {x | ∃ a : Fin 3 → ℝ, |a 0|+|a 1|+|a 2| ≤ 1 ∧
        (1/2:ℝ) • standardRoot+octahedronChart a=x} := by
  obtain ⟨w,hw,rfl⟩ := facet_isRoot hz
  obtain ⟨k,rfl⟩ := rootTable_complete hw
  obtain ⟨e,he⟩ := rootTable_face_isometric k
  exact ⟨e, by rw [← standard_face_eq_octahedron]; exact he.symm⟩

end D4.PhysicalD4
