import D4.C23PathWindowGeometry

/-! Quantitative containment of moving local windows in fixed larger windows. -/
noncomputable section
namespace D4.C23Local
open Analytic AreaEnvelope Matrix Set Filter Topology Principal
attribute [local instance] Matrix.normedAddCommGroup

theorem min4_le_min4_add {a b c d A B C D ε : ℝ}
    (ha : a ≤ A+ε) (hb : b ≤ B+ε) (hc : c ≤ C+ε) (hd : d ≤ D+ε) :
    min4 a b c d ≤ min4 A B C D+ε := by
  have h := min_le_min ha (min_le_min hb (min_le_min hc hd))
  simpa only [min4, min_add_add_right] using h

theorem lower2_sub_abs_le (r s : ℝ) (L : Plane) :
    |lower2 r L-lower2 s L| ≤ 2*|r-s| := by
  have hd := abs_nonneg (r-s)
  have hle := le_abs_self (r-s)
  have hge := neg_abs_le (r-s)
  have h1 : lower2 r L ≤ lower2 s L+2*|r-s| :=
    min4_le_min4_add (by linarith) (by linarith) (by linarith) (by linarith)
  have h2 : lower2 s L ≤ lower2 r L+2*|r-s| :=
    min4_le_min4_add (by linarith) (by linarith) (by linarith) (by linarith)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem gap2_parameter_le (p q r P Q R : ℝ) (L : Plane) :
    gap2 P Q R L ≤ gap2 p q r L+2*|p-P|+2*|q-Q|+4*|r-R| := by
  have hp := le_abs_self (p-P)
  have hq := le_abs_self (q-Q)
  have hr := le_abs_self (r-R)
  have hp0 := abs_nonneg (p-P)
  have hq0 := abs_nonneg (q-Q)
  have hr0 := abs_nonneg (r-R)
  have hu : upper2 p q r L ≤ upper2 P Q R L+
      (2*|p-P|+2*|q-Q|+2*|r-R|) :=
    min4_le_min4_add (by linarith) (by linarith) (by linarith) (by linarith)
  have hl := (abs_le.mp (lower2_sub_abs_le r R L)).2
  unfold gap2
  linarith

theorem localWindow2_subset_of_shift (Q : Gram) (U V : Plane → ℝ)
    (K H : Set Plane) (r R : ℝ) (hK : K ⊆ H)
    (hUV : ∀ L∈K,|U L-V L|≤R-r) :
    localWindow2 Q U K r ⊆ localWindow2 Q V H R := by
  rintro x ⟨⟨L,a,b⟩,⟨hL,ha,hb⟩,rfl⟩
  have hshift := abs_le.mp (hUV L hL)
  refine ⟨(L,(a+U L-V L,b+U L-V L)),⟨hK hL,?_,?_⟩,?_⟩
  · change -R ≤ a+U L-V L ∧ a+U L-V L ≤ R
    constructor <;> linarith [ha.1,ha.2,hshift.1,hshift.2]
  · change -R ≤ b+U L-V L ∧ b+U L-V L ≤ R
    constructor <;> linarith [hb.1,hb.2,hshift.1,hshift.2]
  · unfold windowPoint2
    congr 1
    ext i
    fin_cases i <;> simp only [fiberCoordinates, Fin.reduceFinMk, Matrix.cons_val] <;> ring

theorem localWindow3_subset (Q : Gram) (U : Plane → ℝ)
    (K H : Set Plane) {r R : ℝ} (hr : r ≤ R) (hK : K ⊆ H) :
    localWindow3 Q U K r ⊆ localWindow3 Q U H R := by
  apply Set.image_mono
  rintro ⟨L,a,b⟩ ⟨hL,ha,hb⟩
  exact ⟨hK hL,⟨by linarith [ha.1],by linarith [ha.2]⟩,
    ⟨by linarith [hb.1],by linarith [hb.2]⟩⟩

theorem posDef_eventually_of_continuous_parameter {P : Type*} [TopologicalSpace P]
    (Q : P → Gram) (p₀ : P) (hc : ContinuousAt Q p₀) (hp : (Q p₀).PosDef)
    (hh : ∀ p,(Q p).IsHermitian) : ∀ᶠ p in nhds p₀,(Q p).PosDef := by
  obtain ⟨ε,c,hε,hcpos,hbound⟩ := nearby_quadratic_coercive hp
  have he : ∀ᶠ p in nhds p₀,‖Q p-Q p₀‖<ε :=
    hc.eventually (by simpa only [Metric.mem_ball,dist_eq_norm] using Metric.ball_mem_nhds (Q p₀) hε)
  filter_upwards [he] with p hp'
  refine ⟨hh p,?_⟩
  intro x hx
  have hn : 0<c*‖x‖^2 := mul_pos hcpos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))
  simpa only [quadratic,star_trivial] using lt_of_lt_of_le hn (hbound (Q p) hp' x)

end D4.C23Local
