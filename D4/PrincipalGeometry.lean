import D4.Targets
import D4.Voronoi
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Topology

/-!
# The principal-cone zonotope and its integer support inequalities

This is the actual image of a ten-dimensional box under the displayed
incidence generators. The support inequality is proved for every integer
vector, with no finite-site or Voronoi-completeness hypothesis.
-/

noncomputable section
open Matrix Set
namespace D4.Principal
open Analytic

def integerGenerators : Fin 10 → Fin 4 → ℤ :=
  ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1],
    ![1,-1,0,0], ![1,0,-1,0], ![1,0,0,-1],
    ![0,1,-1,0], ![0,1,0,-1], ![0,0,1,-1]]

theorem generators_cast (e : Fin 10) (i : Fin 4) :
    (integerGenerators e i : ℝ) = cone1Vectors e i := by
  fin_cases e <;> fin_cases i <;> norm_num [integerGenerators, cone1Vectors]

def generatorMap : (Fin 10 → ℝ) →ₗ[ℝ] Vec :=
  Matrix.toLin' (fun i e => cone1Vectors e i)

def zonotope (w : Fin 10 → ℝ) : Set Vec :=
  generatorMap '' Icc (-w) w

theorem generatorMap_eq (t : Fin 10 → ℝ) :
    generatorMap t = ∑ e, t e • cone1Vectors e := by
  ext i
  simp [generatorMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Finset.sum_apply, mul_comm]

theorem zonotope_isCompact (w : Fin 10 → ℝ) : IsCompact (zonotope w) :=
  isCompact_Icc.image generatorMap.continuous_of_finiteDimensional

theorem zonotope_convex (w : Fin 10 → ℝ) : Convex ℝ (zonotope w) :=
  (convex_Icc (-w) w).linear_image generatorMap

theorem zero_mem_zonotope {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e) :
    (0 : Vec) ∈ zonotope w := by
  refine ⟨0, ⟨?_, ?_⟩, by simp⟩
  · intro e
    exact neg_nonpos.mpr (hw e)
  · exact hw

theorem quadratic_rankOne (v x : Vec) :
    quadratic (rankOne v) x = (dotProduct x v)^2 := by
  have hm : rankOne v *ᵥ x = dotProduct v x • v := by
    ext i
    simp [Matrix.mulVec, rankOne, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [quadratic, hm, dotProduct_smul, smul_eq_mul, dotProduct_comm v x]
  ring

theorem quadratic_sum {ι : Type*} [Fintype ι] (A : ι → Gram) (x : Vec) :
    quadratic (∑ e, A e) x = ∑ e, quadratic (A e) x := by
  let f : Gram →+ ℝ := {
    toFun := fun Q => quadratic Q x
    map_zero' := by simp [quadratic]
    map_add' := by intro Q R; simp [quadratic, Matrix.add_mulVec, dotProduct_add] }
  exact map_sum f A Finset.univ

theorem quadratic_principal (w : Fin 10 → ℝ) (x : Vec) :
    quadratic (principalForm w) x = ∑ e, w e * (dotProduct x (cone1Vectors e))^2 := by
  unfold principalForm
  rw [quadratic_sum]
  simp only [quadratic_smul, quadratic_rankOne]

theorem principal_isHermitian (w : Fin 10 → ℝ) : (principalForm w).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [principalForm, rankOne, Matrix.sum_apply, mul_comm, mul_left_comm]

theorem principal_posSemidef {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e) :
    (principalForm w).PosSemidef := by
  refine ⟨principal_isHermitian w, ?_⟩
  intro x
  have h : 0 ≤ quadratic (principalForm w) x := by
    rw [quadratic_principal]
    exact Finset.sum_nonneg (fun e _ => mul_nonneg (hw e) (sq_nonneg _))
  simpa only [quadratic, star_trivial] using h

theorem abs_intCast_le_sq (k : ℤ) : |(k : ℝ)| ≤ (k : ℝ)^2 := by
  rcases (show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega) with h | h | h
  · have hr : (k : ℝ) ≤ -1 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  · subst k
    norm_num
  · have hr : (1 : ℝ) ≤ k := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    nlinarith

theorem integer_generator_dot (z : IntVec) (e : Fin 10) :
    dotProduct (castVec z) (cone1Vectors e) =
      ((∑ i, z i * integerGenerators e i : ℤ) : ℝ) := by
  simp only [dotProduct, castVec, Int.cast_sum, Int.cast_mul, generators_cast]

theorem generatorMap_dot (z : Vec) (t : Fin 10 → ℝ) :
    dotProduct z (generatorMap t) = ∑ e, t e * dotProduct z (cone1Vectors e) := by
  change dotProduct z ((fun i e => cone1Vectors e i) *ᵥ t) = _
  rw [Matrix.dotProduct_mulVec]
  simp [Matrix.vecMul, dotProduct, mul_comm]

/-- The key support bound in the article, for all integer competitors. -/
theorem zonotope_integer_support {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e)
    {r : Vec} (hr : r ∈ zonotope w) (z : IntVec) :
    dotProduct (castVec z) r ≤ quadratic (principalForm w) (castVec z) := by
  obtain ⟨t, ht, rfl⟩ := hr
  rw [generatorMap_dot, quadratic_principal]
  apply Finset.sum_le_sum
  intro e _
  have ht' : |t e| ≤ w e := abs_le.mpr ⟨ht.1 e, ht.2 e⟩
  have hz : |dotProduct (castVec z) (cone1Vectors e)| ≤
      (dotProduct (castVec z) (cone1Vectors e))^2 := by
    rw [integer_generator_dot]
    exact abs_intCast_le_sq _
  calc
    t e * dotProduct (castVec z) (cone1Vectors e) ≤
        |t e * dotProduct (castVec z) (cone1Vectors e)| := le_abs_self _
    _ = |t e| * |dotProduct (castVec z) (cone1Vectors e)| := abs_mul _ _
    _ ≤ w e * |dotProduct (castVec z) (cone1Vectors e)| :=
      mul_le_mul_of_nonneg_right ht' (abs_nonneg _)
    _ ≤ w e * (dotProduct (castVec z) (cone1Vectors e))^2 :=
      mul_le_mul_of_nonneg_left hz (hw e)

/-- In primal coordinates, the zonotope is contained in the genuine Voronoi cell. -/
theorem zonotope_preimage_subset_voronoi {w : Fin 10 → ℝ}
    (hw : ∀ e, 0 ≤ w e) :
    (fun x : Vec => (2 : ℝ) • (principalForm w *ᵥ x)) ⁻¹' zonotope w ⊆
      voronoi (principalForm w) := by
  intro x hx z
  have hQ := principal_isHermitian w
  have hs := zonotope_integer_support hw hx z
  simp only [dotProduct_smul, smul_eq_mul] at hs
  rw [quadratic_pair_symmetric hQ (castVec z) x] at hs
  rw [quadratic_sub_vec hQ]
  linarith

theorem nearest_eq_quadratic_on_zonotope_preimage {w : Fin 10 → ℝ}
    (hw : ∀ e, 0 ≤ w e) {x : Vec}
    (hx : (2 : ℝ) • (principalForm w *ᵥ x) ∈ zonotope w) :
    nearest (principalForm w) x = quadratic (principalForm w) x :=
  nearest_eq_quadratic_on_voronoi (principal_posSemidef hw)
    (zonotope_preimage_subset_voronoi hw hx)

end D4.Principal
