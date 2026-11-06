import D4.Voronoi

noncomputable section
open Matrix MeasureTheory Set

namespace D4.Analytic

/-- Integer translates reduce every point to the compact unit cube. -/
theorem fractional_coordinates_mem_unitCube (x : Vec) :
    x - castVec (fun i => ⌊x i⌋) ∈ unitCube := by
  constructor <;> intro i
  · change 0 ≤ x i - (⌊x i⌋ : ℝ)
    exact sub_nonneg.mpr (Int.floor_le _)
  · change x i - (⌊x i⌋ : ℝ) ≤ 1
    linarith [Int.lt_floor_add_one (x i)]

theorem nearest_uniform_bound {Q : Gram} (hQ : Q.PosSemidef) :
    ∃ C : ℝ, ∀ x : Vec, nearest Q x ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact unitCube).bddAbove_image
    (quadratic_continuous Q).continuousOn
  refine ⟨C, fun x => ?_⟩
  apply (nearest_le hQ x (fun i => ⌊x i⌋)).trans
  exact hC (mem_image_of_mem _ (fractional_coordinates_mem_unitCube x))

theorem voronoi_bounded {Q : Gram} (hQ : Q.PosDef) : Bornology.IsBounded (voronoi Q) := by
  obtain ⟨C, hC⟩ := nearest_uniform_bound hQ.posSemidef
  obtain ⟨c, hc, hcoerce⟩ := quadratic_coercive hQ
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C/c + 1, fun x hx => ?_⟩
  have hb : c * ‖x‖^2 ≤ C := by
    apply (hcoerce x).trans
    rw [← nearest_eq_quadratic_on_voronoi hQ.posSemidef hx]
    exact hC x
  have hs : ‖x‖^2 ≤ C/c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hb)
  nlinarith only [hs, sq_nonneg (‖x‖ - 1/2)]

theorem voronoi_compact {Q : Gram} (hQ : Q.PosDef) : IsCompact (voronoi Q) :=
  Metric.isCompact_of_isClosed_isBounded (voronoi_closed Q) (voronoi_bounded hQ)

theorem quadratic_integrableOn_voronoi {Q : Gram} (hQ : Q.PosDef) :
    IntegrableOn (quadratic Q) (voronoi Q) :=
  (quadratic_continuous Q).continuousOn.integrableOn_compact (voronoi_compact hQ)

end D4.Analytic
