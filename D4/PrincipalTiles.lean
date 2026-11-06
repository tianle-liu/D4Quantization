import D4.PrincipalTiling

/-!
# Identification of an upper tile with an explicit parallelotope

The hypotheses are elementary finite matrix and sign facts. They will be
instantiated by the independently checked 125 spanning-tree data.
-/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def edgeMatrix (b : Fin 4 → Fin 10) : Gram := fun i j => cone1Vectors (b j) i

def weightedEdgeMatrix (w : Fin 10 → ℝ) (b : Fin 4 → Fin 10) : Gram :=
  fun i j => w (b j) * cone1Vectors (b j) i

def signedCenter (w ε : Fin 10 → ℝ) : Vec := generatorMap (fun e => ε e * w e)

def insertCoefficients (b : Fin 4 → Fin 10) (v : Vec) : Fin 10 → ℝ :=
  fun e => ∑ j, if b j = e then v j else 0

theorem insertCoefficients_at (b : Fin 4 → Fin 10) (hb : Function.Injective b)
    (v : Vec) (j : Fin 4) : insertCoefficients b v (b j) = v j := by
  simp [insertCoefficients, hb.eq_iff]

theorem insertCoefficients_off (b : Fin 4 → Fin 10) (v : Vec) {e : Fin 10}
    (he : e ∉ range b) : insertCoefficients b v e = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (fun h => he ⟨j, h⟩)]

theorem generatorMap_insertCoefficients (b : Fin 4 → Fin 10) (v : Vec) :
    generatorMap (insertCoefficients b v) = edgeMatrix b *ᵥ v := by
  ext i
  simp only [generatorMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    insertCoefficients, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero]
  simp [edgeMatrix]

theorem weightedEdgeMatrix_mulVec (w : Fin 10 → ℝ) (b : Fin 4 → Fin 10) (x : Vec) :
    weightedEdgeMatrix w b *ᵥ x = edgeMatrix b *ᵥ (fun j => w (b j) * x j) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, weightedEdgeMatrix, edgeMatrix]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem upperTile_eq_parallelotope (h w ε : Fin 10 → ℝ) (u : Vec)
    (b : Fin 4 → Fin 10) (hb : Function.Injective b)
    (hw : ∀ e, 0 < w e)
    (hz : ∀ j, reducedCost h u (b j) = 0)
    (hnz : ∀ e, e ∉ range b → reducedCost h u e ≠ 0)
    (hεz : ∀ j, ε (b j) = 0)
    (hεabs : ∀ e, e ∉ range b → |ε e| = 1)
    (hεsign : ∀ e, reducedCost h u e * ε e = |reducedCost h u e|) :
    upperTile h w u = parallelotope (weightedEdgeMatrix w b) (signedCenter w ε) := by
  ext r
  constructor
  · rintro ⟨t, ht, rfl⟩
    let x : Vec := fun j => t (b j) / w (b j)
    have hxc : x ∈ centeredCube := by
      constructor <;> intro j <;> change _ ≤ _
      · exact (le_div_iff₀ (hw (b j))).mpr (by simpa using ht.1.1 (b j))
      · exact (div_le_iff₀ (hw (b j))).mpr (by simpa using ht.1.2 (b j))
    have hcoeff : t = (fun e => ε e * w e) +
        insertCoefficients b (fun j => w (b j) * x j) := by
      ext e
      by_cases he : e ∈ range b
      · obtain ⟨j, rfl⟩ := he
        rw [Pi.add_apply, hεz, zero_mul, zero_add, insertCoefficients_at b hb]
        dsimp [x]
        field_simp [(hw (b j)).ne']
      · rw [Pi.add_apply, insertCoefficients_off b _ he, add_zero]
        apply mul_left_cancel₀ (hnz e he)
        rw [ht.2 e, ← mul_assoc, hεsign]
        ring
    refine ⟨x, hxc, ?_⟩
    rw [hcoeff, map_add, generatorMap_insertCoefficients, ← weightedEdgeMatrix_mulVec]
    rfl
  · rintro ⟨x, hx, rfl⟩
    let t : Fin 10 → ℝ := (fun e => ε e * w e) +
      insertCoefficients b (fun j => w (b j) * x j)
    have htb (j : Fin 4) : t (b j) = w (b j) * x j := by
      simp only [t, Pi.add_apply, hεz, zero_mul, zero_add, insertCoefficients_at b hb]
    have hto {e : Fin 10} (he : e ∉ range b) : t e = ε e * w e := by
      simp only [t, Pi.add_apply, insertCoefficients_off b _ he, add_zero]
    have ht : t ∈ upperFace h w u := by
      constructor
      · constructor <;> intro e
        · by_cases he : e ∈ range b
          · obtain ⟨j, rfl⟩ := he
            rw [htb]
            have hh := mul_le_mul_of_nonneg_left (hx.1 j) (hw (b j)).le
            simpa using hh
          · rw [hto he]
            have ha : |ε e * w e| ≤ w e := by rw [abs_mul, hεabs e he, one_mul, abs_of_pos (hw e)]
            exact (abs_le.mp ha).1
        · by_cases he : e ∈ range b
          · obtain ⟨j, rfl⟩ := he
            rw [htb]
            have hh := mul_le_mul_of_nonneg_left (hx.2 j) (hw (b j)).le
            simpa using hh
          · rw [hto he]
            have ha : |ε e * w e| ≤ w e := by rw [abs_mul, hεabs e he, one_mul, abs_of_pos (hw e)]
            exact (abs_le.mp ha).2
      · intro e
        by_cases he : e ∈ range b
        · obtain ⟨j, rfl⟩ := he
          simp only [hz, zero_mul, abs_zero, mul_zero]
        · rw [hto he, ← mul_assoc, hεsign]
          ring
    refine ⟨t, ht, ?_⟩
    dsimp [t]
    rw [map_add, generatorMap_insertCoefficients, ← weightedEdgeMatrix_mulVec]
    rfl

theorem weightedEdgeMatrix_eq (w : Fin 10 → ℝ) (b : Fin 4 → Fin 10) :
    weightedEdgeMatrix w b = edgeMatrix b * diagonal (fun j => w (b j)) := by
  ext i j
  simp [weightedEdgeMatrix, edgeMatrix, Matrix.mul_diagonal, mul_comm]

theorem weightedEdgeMatrix_det (w : Fin 10 → ℝ) (b : Fin 4 → Fin 10) :
    (weightedEdgeMatrix w b).det = (edgeMatrix b).det * ∏ j, w (b j) := by
  rw [weightedEdgeMatrix_eq, Matrix.det_mul, Matrix.det_diagonal]

theorem parallelotope_compact (B : Gram) (c : Vec) : IsCompact (parallelotope B c) := by
  apply isCompact_Icc.image
  exact continuous_const.add (Matrix.toLin' B).continuous_of_finiteDimensional

theorem parallelotope_volume (B : Gram) (hB : B.det ≠ 0) (c : Vec) :
    volume (parallelotope B c) = ENNReal.ofReal (16 * |B.det|) := by
  have h := parallelotope_integral B hB c (fun _ => (1 : ℝ))
  rw [centeredCube_one] at h
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ] at h
  rw [← ENNReal.ofReal_toReal (parallelotope_compact B c).measure_lt_top.ne, h, mul_comm]

theorem trace_congruence_columns (Q B : Gram) :
    (B.transpose * Q * B).trace = ∑ j, quadratic Q (fun i => B i j) := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    quadratic, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem trace_weightedEdgeMatrix (Q : Gram) (w : Fin 10 → ℝ) (b : Fin 4 → Fin 10) :
    ((weightedEdgeMatrix w b).transpose * Q * weightedEdgeMatrix w b).trace =
      ∑ j, w (b j)^2 * quadratic Q (cone1Vectors (b j)) := by
  rw [trace_congruence_columns]
  apply Finset.sum_congr rfl
  intro j _
  exact quadratic_smul_vec Q (w (b j)) (cone1Vectors (b j))

end D4.Principal
