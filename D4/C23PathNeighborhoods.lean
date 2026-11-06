import D4.C23AnalyticPaths
import D4.NearestUniform

/-! Actual positive-definite neighborhoods and the signs on both sides of each path. -/
noncomputable section
namespace D4.C23Local
open Matrix Analytic Principal Set Filter
attribute [local instance] Matrix.normedAddCommGroup

theorem posDef_eventually_of_continuous_path (Q : ℝ → Gram) (t₀ : ℝ)
    (hc : ContinuousAt Q t₀) (hp : (Q t₀).PosDef)
    (hh : ∀ t,(Q t).IsHermitian) : ∀ᶠ t in nhds t₀,(Q t).PosDef := by
  obtain ⟨ε,c,hε,hcpos,hbound⟩ := nearby_quadratic_coercive hp
  have he : ∀ᶠ t in nhds t₀,‖Q t-Q t₀‖<ε :=
    hc.eventually (by simpa only [Metric.mem_ball,dist_eq_norm] using Metric.ball_mem_nhds (Q t₀) hε)
  filter_upwards [he] with t ht
  refine ⟨hh t,?_⟩
  intro x hx
  have hn : 0<c*‖x‖^2 := mul_pos hcpos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))
  simpa only [quadratic,star_trivial] using lt_of_lt_of_le hn (hbound (Q t) ht x)

theorem path2_posDef_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ a in nhds (0:ℝ),(form2 (path2 z a)).PosDef := by
  apply posDef_eventually_of_continuous_path
  · exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
      (form2_analyticAt (path2 z) 0 (path2_analytic z 0) i j).continuousAt
  · rw [path2_at_zero]
    exact boundary2_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  · intro a
    exact secondary_isHermitian cone2Vectors _ _

theorem path3_posDef_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ b in nhds (0:ℝ),(form3 (path3 z b)).PosDef := by
  apply posDef_eventually_of_continuous_path
  · exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
      (form3_analyticAt (path3 z) 0 (path3_analytic z 0) i j).continuousAt
  · rw [path3_at_zero]
    exact boundary3_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  · intro b
    exact secondary_isHermitian cone3Vectors _ _

theorem nonneg_path_except (w : ℝ → Parameters) (e : Fin 10)
    (hw : ∀ i,ContinuousAt (fun t => w t i) 0)
    (h0 : ∀ i,i≠e → 0<w 0 i) :
    ∀ᶠ t in nhds (0:ℝ),0≤w t e → ∀ i,0≤w t i := by
  have he : ∀ᶠ t in nhds (0:ℝ),∀ i : Fin 10,i≠e → 0<w t i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i=e
    · subst i; exact Filter.Eventually.of_forall (by simp)
    · exact ((hw i).eventually (Ioi_mem_nhds (h0 i hi))).mono fun t ht _ => ht
  exact he.mono fun t ht he i => by
    by_cases hi : i=e
    · simpa only [hi] using he
    · exact (ht i hi).le

theorem path2_nonneg (z : Parameters) (hz : ∀ i,0<z i)
    (a : ℝ) (ha : 0≤a) : ∀ i,0≤path2 z a i := by
  intro i
  fin_cases i <;> first | exact ha | exact (hz _).le

theorem principalPath2_nonneg_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ a in nhds (0:ℝ),a≤0 → ∀ i,0≤principalPath2 z a i := by
  have he := nonneg_path_except (principalPath2 z) 4
    (fun i => (principalPath2_analytic z 0 i).continuousAt) (by
      intro i hi
      fin_cases i <;> norm_num [principalPath2] at hi ⊢ <;> first | exact hz _ | contradiction)
  exact he.mono fun a ha han => ha (by change 0≤-a; linarith)

theorem path3_nonneg_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ b in nhds (0:ℝ),0≤b → ∀ i,0≤path3 z b i := by
  have he := nonneg_path_except (path3 z) 9
    (fun i => (path3_analytic z 0 i).continuousAt) (by
      intro i hi
      fin_cases i <;> norm_num [path3] at hi ⊢ <;> first | exact hz _ | contradiction)
  exact he.mono fun b hb hbn => hb hbn

theorem theta_path3_nonneg_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ b in nhds (0:ℝ),b≤0 → ∀ i,0≤theta (path3 z b) i := by
  have he := nonneg_path_except (fun b => theta (path3 z b)) 9
    (fun i => (theta_analytic (path3 z) 0 (path3_analytic z 0) i).continuousAt) (by
      intro i hi
      fin_cases i <;> norm_num [path3,theta] at hi ⊢ <;> first
        | exact hz _
        | contradiction
        | (change 0<z 0+0; simpa using hz 0))
  exact he.mono fun b hb hbn => hb (by change 0≤-b; linarith)

end D4.C23Local
