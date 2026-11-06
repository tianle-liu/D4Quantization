import D4.EuclideanSemantics
import D4.VoronoiLatticeCompact
import D4.ParityQuantizer

/-! The actual root-lattice Voronoi polytope and its facets. -/
noncomputable section
open Set Matrix
open scoped InnerProductSpace
namespace D4.PhysicalD4
open Euclidean Analytic FacetGeometry

/-- Integer coordinates embedded in the genuine Euclidean space. -/
def integerPoint (z : IntVec) : Point := (WithLp.equiv 2 Vec).symm (castVec z)

@[simp] theorem integerPoint_apply (z : IntVec) (i : Fin 4) : integerPoint z i = z i := rfl

@[simp] theorem integerPoint_zero : integerPoint 0 = 0 := by ext i; simp
@[simp] theorem integerPoint_add (z w : IntVec) : integerPoint (z+w) = integerPoint z+integerPoint w := by
  ext i; simp
@[simp] theorem integerPoint_zsmul (k : ℤ) (z : IntVec) : integerPoint (k • z) = k • integerPoint z := by
  ext i; simp

def integerPointLinear : IntVec →ₗ[ℤ] Point where
  toFun := integerPoint
  map_add' := integerPoint_add
  map_smul' := integerPoint_zsmul

def evenModule : Submodule ℤ IntVec where
  carrier := evenSumLattice
  zero_mem' := by simp [evenSumLattice]
  add_mem' := by
    intro z w hz hw
    simpa only [evenSumLattice, mem_setOf_eq, Pi.add_apply, Finset.sum_add_distrib] using dvd_add hz hw
  smul_mem' := by
    intro k z hz
    change (2 : ℤ) ∣ ∑ i, k * z i
    rw [← Finset.mul_sum]
    exact dvd_mul_of_dvd_right hz k

/-- The full lattice of even-sum integer points, as an actual submodule. -/
def lattice : Submodule ℤ Point := evenModule.map integerPointLinear

theorem mem_lattice (x : Point) : x ∈ lattice ↔ ∃ z ∈ evenSumLattice, integerPoint z = x := Iff.rfl

theorem integerPoint_injective : Function.Injective integerPoint := by
  intro z w h
  ext i
  have hh := congrArg (fun x : Point => x i) h
  change (z i : ℝ) = w i at hh
  exact_mod_cast hh

theorem integerPoint_norm_sq (z : IntVec) : ‖integerPoint z‖^2 = ((∑ i, z i^2 : ℤ) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  simp [PiLp.inner_apply, star_trivial, pow_two]

theorem point_norm_sq (x : Point) : ‖x‖^2 = ∑ i, (x i)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp [PiLp.inner_apply, star_trivial, pow_two]

theorem integerPoint_inner (x : Point) (z : IntVec) : ⟪x, integerPoint z⟫_ℝ = ∑ i, x i * z i := by
  simp [PiLp.inner_apply, star_trivial, mul_comm]

/-- The 24 roots are exactly the even integer vectors of squared length two. -/
def IsRoot (z : IntVec) : Prop := ∑ i, z i^2 = 2

theorem square_mod_two (z : ℤ) : z^2 % 2 = z % 2 := by
  rw [pow_two, Int.mul_emod]
  have h : z % 2 = 0 ∨ z % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

theorem even_norm_sq {z : IntVec} (hz : z ∈ evenSumLattice) : (2 : ℤ) ∣ ∑ i, z i^2 := by
  change (2 : ℤ) ∣ ∑ i, z i at hz
  rw [Int.dvd_iff_emod_eq_zero] at hz ⊢
  simpa only [Fin.sum_univ_succ, Int.add_emod, square_mod_two, Int.emod_emod] using hz

theorem root_even {z : IntVec} (hz : IsRoot z) : z ∈ evenSumLattice := by
  change (2 : ℤ) ∣ ∑ i, z i
  rw [Int.dvd_iff_emod_eq_zero]
  have h : (∑ i, z i^2) % 2 = 0 := by rw [hz]; norm_num
  simpa only [Fin.sum_univ_succ, Int.add_emod, square_mod_two, Int.emod_emod] using h

theorem nonroot_norm_sq_ge_four {z : IntVec} (hz : z ∈ evenSumLattice)
    (hz0 : z ≠ 0) (hr : ¬ IsRoot z) : (4 : ℤ) ≤ ∑ i, z i^2 := by
  have hpos : 0 < ∑ i, z i^2 := by
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := Function.ne_iff.mp hz0
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hi)
      (Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i))
  have he := even_norm_sq hz
  change ∑ i, z i^2 ≠ 2 at hr
  omega

/-- The explicit finite root halfspace description. -/
def rootPolytope : Set Point := {x | ∀ i j : Fin 4, i ≠ j → |x i| + |x j| ≤ 1}

theorem rootPolytope_norm_le {x : Point} (hx : x ∈ rootPolytope) : ‖x‖ ≤ 1 := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i : Fin 4 => |x i|) (by simp)
  have ha : |x i| ≤ 1 := by
    obtain ⟨j, hj⟩ : ∃ j : Fin 4, j ≠ i := exists_ne i
    have h := hx i j (Ne.symm hj)
    linarith [abs_nonneg (x j)]
  have hs : ∀ j, (x j)^2 ≤ if j=i then (x i)^2 else (1-|x i|)^2 := by
    intro j
    by_cases hji : j=i
    · subst j; simp
    · simp only [if_neg hji]
      have h := hx i j (Ne.symm hji)
      nlinarith [abs_nonneg (x j), sq_abs (x j)]
  have hsq : ‖x‖^2 ≤ 1 := by
    rw [point_norm_sq]
    by_cases hhalf : |x i| ≤ 1/2
    · calc
        ∑ j, (x j)^2 ≤ ∑ _j : Fin 4, (1/2:ℝ)^2 := by
          apply Finset.sum_le_sum
          intro j hj
          have h := (hmax j hj).trans hhalf
          nlinarith [abs_nonneg (x j), sq_abs (x j)]
        _ = 1 := by norm_num
    · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j)
      have he : (∑ j : Fin 4, if j=i then (x i)^2 else (1-|x i|)^2) =
          (x i)^2+3*(1-|x i|)^2 := by
        have hite (j : Fin 4) : (if j=i then (x i)^2 else (1-|x i|)^2) =
            (1-|x i|)^2 + if j=i then (x i)^2-(1-|x i|)^2 else 0 := by
          split_ifs <;> ring
        simp_rw [hite]
        rw [Finset.sum_add_distrib]
        simp
        ring
      rw [he] at hsum
      have hprod := mul_nonneg (by linarith : 0 ≤ |x i|-1/2) (by linarith : 0 ≤ 1-|x i|)
      nlinarith [sq_abs (x i)]
  nlinarith [norm_nonneg x]


/-- The complete root list, without multiplicity. -/
def rootTable : Fin 24 → IntVec :=
  ![![-1,-1,0,0],
    ![-1,1,0,0],
    ![1,-1,0,0],
    ![1,1,0,0],
    ![-1,0,-1,0],
    ![-1,0,1,0],
    ![1,0,-1,0],
    ![1,0,1,0],
    ![-1,0,0,-1],
    ![-1,0,0,1],
    ![1,0,0,-1],
    ![1,0,0,1],
    ![0,-1,-1,0],
    ![0,-1,1,0],
    ![0,1,-1,0],
    ![0,1,1,0],
    ![0,-1,0,-1],
    ![0,-1,0,1],
    ![0,1,0,-1],
    ![0,1,0,1],
    ![0,0,-1,-1],
    ![0,0,-1,1],
    ![0,0,1,-1],
    ![0,0,1,1]]

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem rootTable_isRoot : ∀ k, IsRoot (rootTable k) := by unfold IsRoot; decide

theorem rootTable_injective : Function.Injective rootTable := by decide

theorem rootTable_complete_small : ∀ v : Fin 4 → Fin 3,
    (∑ i, ((v i : ℤ)-1)^2) = 2 → ∃ k : Fin 24, rootTable k = fun i => (v i : ℤ)-1 := by decide

theorem root_coordinate_bound {z : IntVec} (hz : IsRoot z) (i : Fin 4) : -1 ≤ z i ∧ z i ≤ 1 := by
  have hs : z i^2 ≤ 2 := by
    rw [← hz]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  constructor <;> by_contra h
  · have : z i ≤ -2 := by omega
    nlinarith
  · have : 2 ≤ z i := by omega
    nlinarith

theorem rootTable_complete {z : IntVec} (hz : IsRoot z) : ∃ k, rootTable k = z := by
  let v : Fin 4 → Fin 3 := fun i => ⟨(z i+1).toNat, by have h := root_coordinate_bound hz i; omega⟩
  have he (i : Fin 4) : (v i : ℤ)-1 = z i := by
    dsimp [v]
    have h := root_coordinate_bound hz i
    omega
  have hv : (∑ i, ((v i : ℤ)-1)^2) = 2 := by simp_rw [he]; exact hz
  obtain ⟨k, hk⟩ := rootTable_complete_small v hv
  exact ⟨k, hk.trans (funext he)⟩

theorem rootPolytope_root_inner {x : Point} (hx : x ∈ rootPolytope) {z : IntVec} (hz : IsRoot z) :
    ⟪x,integerPoint z⟫_ℝ ≤ 1 := by
  obtain ⟨k, rfl⟩ := rootTable_complete hz
  rw [integerPoint_inner]
  fin_cases k
  · have h := hx 0 1 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change -x 0 ≤ 1+x 1
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 1), neg_le_abs (x 1)]
  · have h := hx 0 1 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 1 ≤ x 0+1
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 1), neg_le_abs (x 1)]
  · have h := hx 0 1 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 0 ≤ 1+x 1
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 1), neg_le_abs (x 1)]
  · have h := hx 0 1 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 0+x 1 ≤ 1
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 1), neg_le_abs (x 1)]
  · have h := hx 0 2 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change -x 0 ≤ 1+x 2
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 2), neg_le_abs (x 2)]
  · have h := hx 0 2 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 2 ≤ x 0+1
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 2), neg_le_abs (x 2)]
  · have h := hx 0 2 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 0 ≤ 1+x 2
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 2), neg_le_abs (x 2)]
  · have h := hx 0 2 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 0+x 2 ≤ 1
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 2), neg_le_abs (x 2)]
  · have h := hx 0 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change -x 0 ≤ 1+x 3
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 0 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 3 ≤ x 0+1
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 0 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 0 ≤ 1+x 3
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 0 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 0+x 3 ≤ 1
    linarith [le_abs_self (x 0), neg_le_abs (x 0), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 1 2 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change -x 1 ≤ 1+x 2
    linarith [le_abs_self (x 1), neg_le_abs (x 1), le_abs_self (x 2), neg_le_abs (x 2)]
  · have h := hx 1 2 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 2 ≤ x 1+1
    linarith [le_abs_self (x 1), neg_le_abs (x 1), le_abs_self (x 2), neg_le_abs (x 2)]
  · have h := hx 1 2 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 1 ≤ 1+x 2
    linarith [le_abs_self (x 1), neg_le_abs (x 1), le_abs_self (x 2), neg_le_abs (x 2)]
  · have h := hx 1 2 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 1+x 2 ≤ 1
    linarith [le_abs_self (x 1), neg_le_abs (x 1), le_abs_self (x 2), neg_le_abs (x 2)]
  · have h := hx 1 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change -x 1 ≤ 1+x 3
    linarith [le_abs_self (x 1), neg_le_abs (x 1), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 1 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 3 ≤ x 1+1
    linarith [le_abs_self (x 1), neg_le_abs (x 1), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 1 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 1 ≤ 1+x 3
    linarith [le_abs_self (x 1), neg_le_abs (x 1), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 1 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 1+x 3 ≤ 1
    linarith [le_abs_self (x 1), neg_le_abs (x 1), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 2 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change -x 2 ≤ 1+x 3
    linarith [le_abs_self (x 2), neg_le_abs (x 2), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 2 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 3 ≤ x 2+1
    linarith [le_abs_self (x 2), neg_le_abs (x 2), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 2 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 2 ≤ 1+x 3
    linarith [le_abs_self (x 2), neg_le_abs (x 2), le_abs_self (x 3), neg_le_abs (x 3)]
  · have h := hx 2 3 (by decide)
    norm_num [rootTable, Fin.sum_univ_succ]
    change x 2+x 3 ≤ 1
    linarith [le_abs_self (x 2), neg_le_abs (x 2), le_abs_self (x 3), neg_le_abs (x 3)]


theorem rootPolytope_of_root_inner {x : Point}
    (h : ∀ z, IsRoot z → ⟪x,integerPoint z⟫_ℝ ≤ 1) : x ∈ rootPolytope := by
  have hp (i j : Fin 4) (hij : i < j) : |x i|+|x j| ≤ 1 := by
    fin_cases i <;> fin_cases j <;> simp only [Fin.lt_def] at hij <;> norm_num at hij
    · have h0 := h (rootTable 0) (rootTable_isRoot 0)
      have h1 := h (rootTable 1) (rootTable_isRoot 1)
      have h2 := h (rootTable 2) (rootTable_isRoot 2)
      have h3 := h (rootTable 3) (rootTable_isRoot 3)
      change ⟪x,integerPoint ![-1,-1,0,0]⟫_ℝ ≤ 1 at h0
      change ⟪x,integerPoint ![-1,1,0,0]⟫_ℝ ≤ 1 at h1
      change ⟪x,integerPoint ![1,-1,0,0]⟫_ℝ ≤ 1 at h2
      change ⟪x,integerPoint ![1,1,0,0]⟫_ℝ ≤ 1 at h3
      norm_num [integerPoint_inner, Fin.sum_univ_succ] at h0 h1 h2 h3
      change -x 0 ≤ 1+x 1 at h0
      change x 1 ≤ x 0+1 at h1
      change x 0 ≤ 1+x 1 at h2
      change x 0+x 1 ≤ 1 at h3
      change |x 0|+|x 1| ≤ 1
      rcases le_total 0 (x 0) with hi | hi <;> rcases le_total 0 (x 1) with hj | hj
      · rw [abs_of_nonneg hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonneg hi, abs_of_nonpos hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonpos hj]; linarith
    · have h0 := h (rootTable 4) (rootTable_isRoot 4)
      have h1 := h (rootTable 5) (rootTable_isRoot 5)
      have h2 := h (rootTable 6) (rootTable_isRoot 6)
      have h3 := h (rootTable 7) (rootTable_isRoot 7)
      change ⟪x,integerPoint ![-1,0,-1,0]⟫_ℝ ≤ 1 at h0
      change ⟪x,integerPoint ![-1,0,1,0]⟫_ℝ ≤ 1 at h1
      change ⟪x,integerPoint ![1,0,-1,0]⟫_ℝ ≤ 1 at h2
      change ⟪x,integerPoint ![1,0,1,0]⟫_ℝ ≤ 1 at h3
      norm_num [integerPoint_inner, Fin.sum_univ_succ] at h0 h1 h2 h3
      change -x 0 ≤ 1+x 2 at h0
      change x 2 ≤ x 0+1 at h1
      change x 0 ≤ 1+x 2 at h2
      change x 0+x 2 ≤ 1 at h3
      change |x 0|+|x 2| ≤ 1
      rcases le_total 0 (x 0) with hi | hi <;> rcases le_total 0 (x 2) with hj | hj
      · rw [abs_of_nonneg hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonneg hi, abs_of_nonpos hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonpos hj]; linarith
    · have h0 := h (rootTable 8) (rootTable_isRoot 8)
      have h1 := h (rootTable 9) (rootTable_isRoot 9)
      have h2 := h (rootTable 10) (rootTable_isRoot 10)
      have h3 := h (rootTable 11) (rootTable_isRoot 11)
      change ⟪x,integerPoint ![-1,0,0,-1]⟫_ℝ ≤ 1 at h0
      change ⟪x,integerPoint ![-1,0,0,1]⟫_ℝ ≤ 1 at h1
      change ⟪x,integerPoint ![1,0,0,-1]⟫_ℝ ≤ 1 at h2
      change ⟪x,integerPoint ![1,0,0,1]⟫_ℝ ≤ 1 at h3
      norm_num [integerPoint_inner, Fin.sum_univ_succ] at h0 h1 h2 h3
      change -x 0 ≤ 1+x 3 at h0
      change x 3 ≤ x 0+1 at h1
      change x 0 ≤ 1+x 3 at h2
      change x 0+x 3 ≤ 1 at h3
      change |x 0|+|x 3| ≤ 1
      rcases le_total 0 (x 0) with hi | hi <;> rcases le_total 0 (x 3) with hj | hj
      · rw [abs_of_nonneg hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonneg hi, abs_of_nonpos hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonpos hj]; linarith
    · have h0 := h (rootTable 12) (rootTable_isRoot 12)
      have h1 := h (rootTable 13) (rootTable_isRoot 13)
      have h2 := h (rootTable 14) (rootTable_isRoot 14)
      have h3 := h (rootTable 15) (rootTable_isRoot 15)
      change ⟪x,integerPoint ![0,-1,-1,0]⟫_ℝ ≤ 1 at h0
      change ⟪x,integerPoint ![0,-1,1,0]⟫_ℝ ≤ 1 at h1
      change ⟪x,integerPoint ![0,1,-1,0]⟫_ℝ ≤ 1 at h2
      change ⟪x,integerPoint ![0,1,1,0]⟫_ℝ ≤ 1 at h3
      norm_num [integerPoint_inner, Fin.sum_univ_succ] at h0 h1 h2 h3
      change -x 1 ≤ 1+x 2 at h0
      change x 2 ≤ x 1+1 at h1
      change x 1 ≤ 1+x 2 at h2
      change x 1+x 2 ≤ 1 at h3
      change |x 1|+|x 2| ≤ 1
      rcases le_total 0 (x 1) with hi | hi <;> rcases le_total 0 (x 2) with hj | hj
      · rw [abs_of_nonneg hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonneg hi, abs_of_nonpos hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonpos hj]; linarith
    · have h0 := h (rootTable 16) (rootTable_isRoot 16)
      have h1 := h (rootTable 17) (rootTable_isRoot 17)
      have h2 := h (rootTable 18) (rootTable_isRoot 18)
      have h3 := h (rootTable 19) (rootTable_isRoot 19)
      change ⟪x,integerPoint ![0,-1,0,-1]⟫_ℝ ≤ 1 at h0
      change ⟪x,integerPoint ![0,-1,0,1]⟫_ℝ ≤ 1 at h1
      change ⟪x,integerPoint ![0,1,0,-1]⟫_ℝ ≤ 1 at h2
      change ⟪x,integerPoint ![0,1,0,1]⟫_ℝ ≤ 1 at h3
      norm_num [integerPoint_inner, Fin.sum_univ_succ] at h0 h1 h2 h3
      change -x 1 ≤ 1+x 3 at h0
      change x 3 ≤ x 1+1 at h1
      change x 1 ≤ 1+x 3 at h2
      change x 1+x 3 ≤ 1 at h3
      change |x 1|+|x 3| ≤ 1
      rcases le_total 0 (x 1) with hi | hi <;> rcases le_total 0 (x 3) with hj | hj
      · rw [abs_of_nonneg hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonneg hi, abs_of_nonpos hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonpos hj]; linarith
    · have h0 := h (rootTable 20) (rootTable_isRoot 20)
      have h1 := h (rootTable 21) (rootTable_isRoot 21)
      have h2 := h (rootTable 22) (rootTable_isRoot 22)
      have h3 := h (rootTable 23) (rootTable_isRoot 23)
      change ⟪x,integerPoint ![0,0,-1,-1]⟫_ℝ ≤ 1 at h0
      change ⟪x,integerPoint ![0,0,-1,1]⟫_ℝ ≤ 1 at h1
      change ⟪x,integerPoint ![0,0,1,-1]⟫_ℝ ≤ 1 at h2
      change ⟪x,integerPoint ![0,0,1,1]⟫_ℝ ≤ 1 at h3
      norm_num [integerPoint_inner, Fin.sum_univ_succ] at h0 h1 h2 h3
      change -x 2 ≤ 1+x 3 at h0
      change x 3 ≤ x 2+1 at h1
      change x 2 ≤ 1+x 3 at h2
      change x 2+x 3 ≤ 1 at h3
      change |x 2|+|x 3| ≤ 1
      rcases le_total 0 (x 2) with hi | hi <;> rcases le_total 0 (x 3) with hj | hj
      · rw [abs_of_nonneg hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonneg hi, abs_of_nonpos hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonneg hj]; linarith
      · rw [abs_of_nonpos hi, abs_of_nonpos hj]; linarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hp i j hij
  · simpa only [add_comm] using hp j i hij

theorem voronoi_eq_rootPolytope : voronoi lattice = rootPolytope := by
  ext x
  constructor
  · intro hx
    apply rootPolytope_of_root_inner
    intro z hz
    have h := (mem_voronoi_iff lattice x).mp hx (integerPoint z) ⟨z, root_even hz, rfl⟩
    rw [integerPoint_norm_sq, hz] at h
    norm_num only [Int.cast_ofNat] at h
    linarith
  · intro hx
    rw [mem_voronoi_iff]
    rintro _ ⟨z, hz, rfl⟩
    change 2*⟪x,integerPoint z⟫_ℝ ≤ ‖integerPoint z‖^2
    by_cases hz0 : z = 0
    · simp [hz0]
    by_cases hr : IsRoot z
    · rw [integerPoint_norm_sq, hr]
      have h := rootPolytope_root_inner hx hr
      norm_num only [Int.cast_ofNat]
      linarith
    · have h4 : (4 : ℝ) ≤ ‖integerPoint z‖^2 := by
        rw [integerPoint_norm_sq]
        exact_mod_cast nonroot_norm_sq_ge_four hz hz0 hr
      have hn : 2 ≤ ‖integerPoint z‖ := by nlinarith [norm_nonneg (integerPoint z)]
      have hb := rootPolytope_norm_le hx
      have hc := real_inner_le_norm x (integerPoint z)
      have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg (integerPoint z))
      nlinarith


theorem root_inner_gap {z w : IntVec} (hz : IsRoot z) (hw : IsRoot w) (hne : z ≠ w) :
    ⟪integerPoint z, integerPoint w⟫_ℝ ≤ 1 := by
  have hne' : integerPoint z-integerPoint w ≠ 0 := sub_ne_zero.mpr (fun h => hne (integerPoint_injective h))
  have hpos := sq_pos_of_pos (norm_pos_iff.mpr hne')
  rw [norm_sub_sq_real, integerPoint_norm_sq, integerPoint_norm_sq, hz, hw] at hpos
  have he : ⟪integerPoint z,integerPoint w⟫_ℝ = ((∑ i, z i*w i : ℤ) : ℝ) := by
    rw [integerPoint_inner]
    simp
  rw [he] at hpos ⊢
  have hi : (∑ i, z i*w i : ℤ) < 2 := by
    apply_mod_cast (show ((∑ i, z i*w i : ℤ) : ℝ) < 2 by norm_num only [Int.cast_ofNat] at hpos; linarith)
  exact_mod_cast (show (∑ i, z i*w i : ℤ) ≤ 1 by omega)

theorem root_isFacet {z : IntVec} (hz : IsRoot z) : IsFacetVector lattice (integerPoint z) := by
  refine ⟨⟨z, root_even hz, rfl⟩, ?_, ?_⟩
  · intro he
    have hn := integerPoint_norm_sq z
    rw [he, norm_zero, zero_pow (by decide), hz] at hn
    norm_num at hn
  · refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
    apply Metric.mem_nhds_iff.mpr
    refine ⟨1/4, by norm_num, ?_⟩
    intro y hy
    have hyn : ‖(y:Point)‖ < 1/4 := by simpa only [Metric.mem_ball, dist_zero_right, Submodule.coe_norm] using hy
    change (1/2:ℝ) • integerPoint z+(y:Point) ∈ voronoi lattice
    rw [voronoi_eq_rootPolytope]
    apply rootPolytope_of_root_inner
    intro w hw
    rw [inner_add_left, real_inner_smul_left]
    by_cases hzw : z=w
    · subst w
      have hyz : ⟪(y:Point),integerPoint z⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact y.property
      rw [hyz, real_inner_self_eq_norm_sq, integerPoint_norm_sq, hz]
      norm_num
    · have hg := root_inner_gap hz hw hzw
      have hn : ‖integerPoint w‖ ≤ 2 := by
        have hs := integerPoint_norm_sq w
        rw [hw] at hs
        norm_num only [Int.cast_ofNat] at hs
        nlinarith [norm_nonneg (integerPoint w)]
      have hc := real_inner_le_norm (y:Point) (integerPoint w)
      have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (y:Point))
      nlinarith

theorem facet_isRoot {x : Point} (hx : IsFacetVector lattice x) :
    ∃ z, IsRoot z ∧ integerPoint z=x := by
  obtain ⟨z, hz, rfl⟩ := hx.1
  change IsFacetVector lattice (integerPoint z) at hx
  change ∃ w, IsRoot w ∧ integerPoint w=integerPoint z
  have hdim := tangent_finrank hx.2.1
  have hdim4 : Module.finrank ℝ Point = 4 := by simp [Point]
  haveI : Nontrivial (tangent (integerPoint z)) := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp (facet_center_interior hx))
  obtain ⟨y, hy⟩ : (Metric.sphere (0 : tangent (integerPoint z)) (ε/2)).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by positivity)
  have hyn : ‖(y:Point)‖ = ε/2 := by simpa only [Metric.mem_sphere, dist_zero_right, Submodule.coe_norm] using hy
  have hybase : y ∈ base lattice (integerPoint z) := hball (by
    simpa only [Metric.mem_ball, dist_zero_right, Submodule.coe_norm, hyn] using (by linarith : ε/2 < ε))
  have hyV : (1/2:ℝ) • integerPoint z+(y:Point) ∈ voronoi lattice := hybase
  have hnorm := rootPolytope_norm_le (voronoi_eq_rootPolytope ▸ hyV)
  have horth : ⟪integerPoint z,(y:Point)⟫_ℝ = 0 := y.property
  have hsq : ‖(1/2:ℝ) • integerPoint z+(y:Point)‖^2 =
      ‖integerPoint z‖^2/4+‖(y:Point)‖^2 := by
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left, horth]
    norm_num
    ring
  have hlt : ‖integerPoint z‖^2 < 4 := by
    have hpos : 0 < ‖(y:Point)‖^2 := by rw [hyn]; positivity
    nlinarith [norm_nonneg ((1/2:ℝ) • integerPoint z+(y:Point))]
  have hz0 : z ≠ 0 := fun h => hx.2.1 (by rw [h, integerPoint_zero])
  refine ⟨z, ?_, rfl⟩
  by_contra hr
  have h4 := nonroot_norm_sq_ge_four hz hz0 hr
  rw [integerPoint_norm_sq] at hlt
  have h4' : (4:ℝ) ≤ ((∑ i, z i^2 : ℤ) : ℝ) := by exact_mod_cast h4
  linarith


def rootFacet (k : Fin 24) : FacetVectors lattice :=
  ⟨⟨integerPoint (rootTable k), ⟨rootTable k, root_even (rootTable_isRoot k), rfl⟩⟩,
    root_isFacet (rootTable_isRoot k)⟩

theorem rootFacet_bijective : Function.Bijective rootFacet := by
  constructor
  · intro k j h
    apply rootTable_injective
    apply integerPoint_injective
    exact congrArg (fun z : FacetVectors lattice => (z.val:Point)) h
  · intro x
    obtain ⟨z, hz, he⟩ := facet_isRoot x.property
    obtain ⟨k, hk⟩ := rootTable_complete hz
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change integerPoint (rootTable k) = (x.val:Point)
    rw [hk, he]

/-- The number counts actual facets of the infinite-competitor Voronoi cell. -/
theorem card_facets : Nat.card (FacetVectors lattice) = 24 := by
  have h := Nat.card_congr (Equiv.ofBijective rootFacet rootFacet_bijective)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h.symm

theorem integerPoint_basis (z : IntVec) :
    integerPoint (basisMatrixZ *ᵥ z) = realization (basisMatrix ℝ) (castVec z) := by
  ext i
  change ((basisMatrixZ *ᵥ z) i : ℝ) = ((basisMatrix ℝ) *ᵥ castVec z) i
  rw [basisMatrixZ_mulVec]
  fin_cases i <;> norm_num [basisMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, castVec] <;> ring <;> rfl

/-- Identification with the article's actual integer-basis lattice. -/
theorem lattice_eq_basis_lattice : (lattice : Set Point) = Euclidean.lattice (basisMatrix ℝ) := by
  ext x
  change (∃ z ∈ evenSumLattice, integerPoint z=x) ↔ x ∈ Euclidean.lattice (basisMatrix ℝ)
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := evenSumLattice_has_preimage z hz
    refine ⟨w, ?_⟩
    exact (integerPoint_basis w).symm.trans (congrArg integerPoint hw)
  · rintro ⟨z, rfl⟩
    exact ⟨basisMatrixZ *ᵥ z, basisMatrixZ_mulVec_mem z, integerPoint_basis z⟩

end D4.PhysicalD4
