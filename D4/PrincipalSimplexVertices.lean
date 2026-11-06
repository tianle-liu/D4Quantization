import D4.PrincipalSimplexAffine
import Mathlib.Analysis.Convex.Combination

/-! Vertex-based simplex semantics and exact second moments. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def simplexMatrix (v : Fin 5 → Vec) : Gram := fun i j => v j.succ i - v 0 i

def vertexSimplex (v : Fin 5 → Vec) : Set Vec := affineSimplex (simplexMatrix v) (v 0)

theorem vertexSimplex_compact (v : Fin 5 → Vec) : IsCompact (vertexSimplex v) :=
  affineSimplex_compact _ _

theorem vertexSimplex_volume (v : Fin 5 → Vec) (hv : (simplexMatrix v).det ≠ 0) :
    volume (vertexSimplex v) = ENNReal.ofReal (|(simplexMatrix v).det| / 24) :=
  affineSimplex_volume _ hv _

theorem simplex_vertex_numerator {Q : Gram} (hQ : Q.IsHermitian) (v : Fin 5 → Vec) :
    quadratic Q (∑ i, v i) + ∑ i, quadratic Q (v i) =
      30 * quadratic Q (v 0) + 12 * dotProduct (v 0) (Q *ᵥ (simplexMatrix v *ᵥ 1)) +
        quadratic Q (simplexMatrix v *ᵥ 1) +
          ((simplexMatrix v).transpose * Q * simplexMatrix v).trace := by
  let B := simplexMatrix v
  let c := v 0
  have hsum : ∑ i, v i = (5 : ℝ) • c + B *ᵥ 1 := by
    ext k
    simp only [Fin.sum_univ_succ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, B, c, simplexMatrix,
      Fin.sum_univ_four]
    ring
  have hv (j : Fin 4) : v j.succ = c + (fun i => B i j) := by
    ext k
    simp only [c, B, simplexMatrix, Pi.add_apply]
    ring
  have hcols : (∑ j, fun i => B i j) = B *ᵥ 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  let L : Vec →ₗ[ℝ] ℝ := {
    toFun := fun x => dotProduct c (Q *ᵥ x)
    map_add' := by intros; simp [Matrix.mulVec_add, dotProduct_add]
    map_smul' := by intros; simp [Matrix.mulVec_smul, dotProduct_smul] }
  have hlinear : (∑ j, dotProduct c (Q *ᵥ (fun i => B i j))) =
      dotProduct c (Q *ᵥ (B *ᵥ 1)) := by
    have h := map_sum L (fun j : Fin 4 => fun i => B i j) Finset.univ
    change dotProduct c (Q *ᵥ (∑ j, fun i => B i j)) = _ at h
    rw [hcols] at h
    exact h.symm
  have hqsum : (∑ i, quadratic Q (v i)) = 5 * quadratic Q c +
      2 * dotProduct c (Q *ᵥ (B *ᵥ 1)) + (B.transpose * Q * B).trace := by
    rw [Fin.sum_univ_succ]
    simp_rw [hv, quadratic_add_vec hQ]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, hlinear, ← trace_congruence_columns]
    change quadratic Q c + _ = _
    ring
  rw [hsum, hqsum, quadratic_add_vec hQ, quadratic_smul_vec]
  simp only [smul_dotProduct, smul_eq_mul]
  change _ = 30 * quadratic Q c + 12 * dotProduct c (Q *ᵥ (B *ᵥ 1)) +
    quadratic Q (B *ᵥ 1) + (B.transpose * Q * B).trace
  ring

/-- The actual Lebesgue integral on the simplex with the given five vertices. -/
theorem vertexSimplex_quadratic {Q : Gram} (hQ : Q.IsHermitian)
    (v : Fin 5 → Vec) (hv : (simplexMatrix v).det ≠ 0) :
    (∫ x in vertexSimplex v, quadratic Q x) = |(simplexMatrix v).det| / 720 *
      (quadratic Q (∑ i, v i) + ∑ i, quadratic Q (v i)) := by
  rw [simplex_vertex_numerator hQ]
  exact affineSimplex_quadratic hQ _ hv _

end D4.Principal
