import D4.C23JointC2AnalyticPieces
import D4.C23JointWindowAffine
import D4.C23WindowPartition2

noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope Analytic Filter Topology

private def diagonalMatrix2 : PlaneMatrix := !![0,1;1,-1]

private theorem diagonal_triangle_image (a b : ℝ) (B : PlaneMatrix) (c : Plane) :
    diagonalEquiv2 a b '' affineTriangle B c =
      affineTriangle (diagonalMatrix2 * B) (![a,b]+diagonalMatrix2*ᵥc) := by
  unfold affineTriangle
  rw [Set.image_image]
  apply Set.image_congr
  intro x hx
  rw [diagonalEquiv2_affine,Matrix.mulVec_add,Matrix.mulVec_mulVec]
  exact (add_assoc _ _ _).symm

private theorem diagonal_image_volume (a b : ℝ) (S : Set Plane) :
    volume (diagonalEquiv2 a b '' S)=volume S := by
  have h := (diagonalEquiv2_preserving a b).measure_preimage_emb
    (diagonalEquiv2 a b).measurableEmbedding (diagonalEquiv2 a b '' S)
  rw [Set.preimage_image_eq _ (diagonalEquiv2 a b).injective] at h
  exact h.symm

private theorem diagonal_triangle_cover (a b : ℝ) (T : Trapezoid) (hT : T.Valid) :
    (⋃i : Fin 2,affineTriangle (diagonalMatrix2*T.matrix i)
      (![a,b]+diagonalMatrix2*ᵥT.origin))=diagonalEquiv2 a b '' T.body := by
  simp_rw [←diagonal_triangle_image]
  rw [←Set.image_iUnion,T.cover hT]

private theorem diagonal_triangle_pairwise (a b : ℝ) (T : Trapezoid) (hT : T.Valid) :
    Pairwise fun i j : Fin 2 => volume
      (affineTriangle (diagonalMatrix2*T.matrix i) (![a,b]+diagonalMatrix2*ᵥT.origin) ∩
       affineTriangle (diagonalMatrix2*T.matrix j) (![a,b]+diagonalMatrix2*ᵥT.origin))=0 := by
  intro i j hij
  rw [←diagonal_triangle_image,←diagonal_triangle_image,
    ←Set.image_inter (diagonalEquiv2 a b).injective,diagonal_image_volume]
  exact T.pairwise_null hT hij

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem localWindow2_diagonal_trapezoid_quadratic_analytic
    (R : ℝ) (Q H : P → Gram) (u : P → Fin 3 → ℝ)
    (a b : P → ℝ) (T : P → Trapezoid) (x₀ : P)
    (hQ : ∀i j,AnalyticAt ℝ (fun x => Q x i j) x₀)
    (hH : ∀i j,AnalyticAt ℝ (fun x => H x i j) x₀)
    (hu : ∀i,AnalyticAt ℝ (fun x => u x i) x₀)
    (ha : AnalyticAt ℝ a x₀) (hb : AnalyticAt ℝ b x₀)
    (hT : ∀i,AnalyticAt ℝ (fun x => (T x).coordinate i) x₀)
    (hvalid : (T x₀).Valid) :
    AnalyticAt ℝ (fun x => ∫y in localWindow2 (Q x) (affineEval (u x))
      (diagonalEquiv2 (a x) (b x) '' (T x).body) R,quadratic (H x) y) x₀ := by
  have hB (i j k : Fin 2) : AnalyticAt ℝ
      (fun x => (diagonalMatrix2*(T x).matrix i) j k) x₀ := by
    simp only [Matrix.mul_apply]
    apply Finset.analyticAt_sum
    intro l hl
    exact analyticAt_const.mul (ParameterArea.trapezoid_matrix T x₀ hT i l k)
  have hc (i : Fin 2) : AnalyticAt ℝ
      (fun x => (![a x,b x]+diagonalMatrix2*ᵥ(T x).origin) i) x₀ := by
    apply AnalyticAt.add
    · fin_cases i
      · exact ha
      · exact hb
    · simp only [Matrix.mulVec,dotProduct]
      apply Finset.analyticAt_sum
      intro l hl
      exact analyticAt_const.mul (ParameterArea.trapezoid_origin T x₀ hT l)
  have had (i : Fin 2) := localWindow2_affine_quadratic_analytic
    (Principal.standardSimplex 2 1) (Principal.standardSimplex_compact 2 1) R Q H
    (fun x => diagonalMatrix2*(T x).matrix i)
    (fun x => ![a x,b x]+diagonalMatrix2*ᵥ(T x).origin) u x₀ hQ hH (hB i) hc hu
    (by
      rw [Matrix.det_mul]
      apply mul_ne_zero
      · norm_num [diagonalMatrix2,Matrix.det_fin_two]
      · exact ((T x₀).matrix_det_pos hvalid i).ne')
  apply (Finset.analyticAt_sum Finset.univ fun i _ => had i).congr
  filter_upwards [ParameterArea.trapezoid_valid_eventually T x₀ hT hvalid] with x hx
  symm
  exact localWindow2_integral_partition (Q x) (affineEval (u x)) (by
    change Continuous (fun y : Plane => affineEval (u x) y)
    simp_rw [affineEval_eq]; fun_prop)
    _ ((T x).compact hx |>.image (by
      apply continuous_pi; intro i; fin_cases i <;> dsimp [diagonalEquiv2] <;> fun_prop))
    _ (fun i => affineTriangle_compact _ _)
    (diagonal_triangle_cover _ _ _ hx) (diagonal_triangle_pairwise _ _ _ hx)
    R _ (by unfold quadratic; fun_prop)

end D4.C23Local
