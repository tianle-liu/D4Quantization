import D4.C23PathNeighborhoods
import D4.C23PathPolynomials
import Mathlib.Analysis.Analytic.Linear

/-! Joint dependence on the tangential parameters and the transverse coordinate. -/
noncomputable section
namespace D4.C23Local.Joint
open Matrix Analytic Principal Certificate CertificateMoments Set Filter
attribute [local instance] Matrix.normedAddCommGroup

abbrev ParameterSpace := Parameters × ℝ

theorem coordinate_analytic (p₀ : ParameterSpace) (i : Fin 10) :
    AnalyticAt ℝ (fun p : ParameterSpace => p.1 i) p₀ :=
  ((ContinuousLinearMap.proj (R := ℝ) i).analyticAt p₀.1).comp analyticAt_fst

theorem path2_analytic (p₀ : ParameterSpace) (i : Fin 10) :
    AnalyticAt ℝ (fun p : ParameterSpace => path2 p.1 p.2 i) p₀ := by
  fin_cases i <;> first | exact analyticAt_snd | exact coordinate_analytic p₀ _

theorem principalPath2_analytic (p₀ : ParameterSpace) (i : Fin 10) :
    AnalyticAt ℝ (fun p : ParameterSpace => principalPath2 p.1 p.2 i) p₀ := by
  fin_cases i <;> first
    | exact coordinate_analytic p₀ _
    | exact analyticAt_snd.neg
    | exact (coordinate_analytic p₀ _).add analyticAt_snd

theorem path3_analytic (p₀ : ParameterSpace) (i : Fin 10) :
    AnalyticAt ℝ (fun p : ParameterSpace => path3 p.1 p.2 i) p₀ := by
  fin_cases i <;> first
    | exact analyticAt_snd
    | exact coordinate_analytic p₀ _
    | exact (coordinate_analytic p₀ _).sub analyticAt_snd
    | exact (coordinate_analytic p₀ _).add analyticAt_snd

section ArbitraryParameters
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem theta_analytic (z : P → Parameters) (p₀ : P)
    (hz : ∀ i,AnalyticAt ℝ (fun p => z p i) p₀) (i : Fin 10) :
    AnalyticAt ℝ (fun p => theta (z p) i) p₀ := by
  fin_cases i
  · exact (hz 0).add (hz 9)
  · exact (hz 1).sub (hz 9)
  · exact (hz 2).sub (hz 9)
  · exact hz 3
  · exact hz 4
  · exact hz 5
  · exact hz 6
  · exact hz 7
  · exact hz 8
  · exact (hz 9).neg

theorem extendWeight_analytic (z : P → Parameters) (p₀ : P)
    (hz : ∀ i,AnalyticAt ℝ (fun p => z p i) p₀) (n : Nat) :
    AnalyticAt ℝ (fun p => extendWeight (z p) n) p₀ := by
  by_cases hn : n<10
  · simpa only [extendWeight,dif_pos hn] using hz ⟨n,hn⟩
  · simp only [extendWeight,dif_neg hn]
    exact analyticAt_const

theorem secondaryForm_analytic (v : Fin 9 → Vec) (a : P → ℝ)
    (w : P → Fin 9 → ℝ) (p₀ : P) (ha : AnalyticAt ℝ a p₀)
    (hw : ∀ k,AnalyticAt ℝ (fun p => w p k) p₀) (i j : Fin 4) :
    AnalyticAt ℝ (fun p => secondaryForm v (a p) (w p) i j) p₀ := by
  simp only [secondaryForm,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  exact (ha.mul analyticAt_const).add
    (Finset.analyticAt_sum _ (fun k _ => (hw k).mul analyticAt_const))

theorem form2_analytic (z : P → Parameters) (p₀ : P)
    (hz : ∀ i,AnalyticAt ℝ (fun p => z p i) p₀) (i j : Fin 4) :
    AnalyticAt ℝ (fun p => form2 (z p) i j) p₀ :=
  secondaryForm_analytic cone2Vectors _ _ p₀ (hz 0) (fun k => hz ⟨k.val+1,by omega⟩) i j

theorem form3_analytic (z : P → Parameters) (p₀ : P)
    (hz : ∀ i,AnalyticAt ℝ (fun p => z p i) p₀) (i j : Fin 4) :
    AnalyticAt ℝ (fun p => form3 (z p) i j) p₀ :=
  secondaryForm_analytic cone3Vectors _ _ p₀ (hz 0) (fun k => hz ⟨k.val+1,by omega⟩) i j

theorem monomial_analytic (x : P → Nat → ℝ) (p₀ : P)
    (hx : ∀ i,AnalyticAt ℝ (fun p => x p i) p₀) (m : Monomial) :
    AnalyticAt ℝ (fun p => monomial (x p) m) p₀ := by
  induction m with
  | nil => exact analyticAt_const
  | cons i m ih =>
    simpa only [monomial,List.map_cons,List.prod_cons] using (hx i).mul ih

theorem eval_analytic (x : P → Nat → ℝ) (p₀ : P)
    (hx : ∀ i,AnalyticAt ℝ (fun p => x p i) p₀) (q : Poly) :
    AnalyticAt ℝ (fun p => eval (x p) q) p₀ := by
  induction q with
  | nil => exact analyticAt_const
  | cons s q ih =>
    simpa only [eval_cons] using
      (analyticAt_const.mul (monomial_analytic x p₀ hx s.1)).add ih

theorem posDef_eventually (Q : P → Gram) (p₀ : P)
    (hc : ContinuousAt Q p₀) (hp : (Q p₀).PosDef)
    (hh : ∀ p,(Q p).IsHermitian) : ∀ᶠ p in nhds p₀,(Q p).PosDef := by
  obtain ⟨ε,c,hε,hcpos,hbound⟩ := nearby_quadratic_coercive hp
  have he : ∀ᶠ p in nhds p₀,‖Q p-Q p₀‖<ε :=
    hc.eventually (by simpa only [Metric.mem_ball,dist_eq_norm] using Metric.ball_mem_nhds (Q p₀) hε)
  filter_upwards [he] with p ht
  refine ⟨hh p,?_⟩
  intro x hx
  have hn : 0<c*‖x‖^2 := mul_pos hcpos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))
  simpa only [quadratic,star_trivial] using lt_of_lt_of_le hn (hbound (Q p) ht x)

theorem nonneg_except (w : P → Parameters) (p₀ : P) (e : Fin 10)
    (hw : ∀ i,ContinuousAt (fun p => w p i) p₀)
    (h0 : ∀ i,i≠e → 0<w p₀ i) :
    ∀ᶠ p in nhds p₀,0≤w p e → ∀ i,0≤w p i := by
  have he : ∀ᶠ p in nhds p₀,∀ i : Fin 10,i≠e → 0<w p i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i=e
    · subst i; exact Filter.Eventually.of_forall (by simp)
    · exact ((hw i).eventually (Ioi_mem_nhds (h0 i hi))).mono fun p hp _ => hp
  exact he.mono fun p hp he i => by
    by_cases hi : i=e
    · simpa only [hi] using he
    · exact (hp i hi).le
end ArbitraryParameters

theorem path2Base_analytic (p₀ : ParameterSpace) :
    AnalyticAt ℝ (fun p : ParameterSpace => path2Base p.1 p.2) p₀ := by
  apply analyticAt_const.mul
  apply eval_analytic
  intro n
  exact eval_analytic (fun p : ParameterSpace => extendWeight (path2 p.1 p.2)) p₀
    (extendWeight_analytic _ p₀ (path2_analytic p₀)) (CompactMoments.z2Substitution n)

theorem path3Base_analytic (p₀ : ParameterSpace) :
    AnalyticAt ℝ (fun p : ParameterSpace => path3Base p.1 p.2) p₀ := by
  apply eval_analytic
  intro n
  exact eval_analytic (fun p : ParameterSpace => extendWeight (path3 p.1 p.2)) p₀
    (extendWeight_analytic _ p₀ (path3_analytic p₀)) (CompactMoments.thetaSubstitution n)

theorem positive_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : ParameterSpace in nhds (z,0),∀ i,0<p.1 i := by
  rw [Filter.eventually_all]
  intro i
  exact (coordinate_analytic (z,0) i).continuousAt.eventually_const_lt (hz i)

theorem path2_posDef_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : ParameterSpace in nhds (z,0),(form2 (path2 p.1 p.2)).PosDef := by
  apply posDef_eventually
  · exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
      (form2_analytic _ (z,0) (path2_analytic (z,0)) i j).continuousAt
  · rw [path2_at_zero]
    exact boundary2_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  · intro p
    exact secondary_isHermitian cone2Vectors _ _

theorem path3_posDef_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : ParameterSpace in nhds (z,0),(form3 (path3 p.1 p.2)).PosDef := by
  apply posDef_eventually
  · exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
      (form3_analytic _ (z,0) (path3_analytic (z,0)) i j).continuousAt
  · rw [path3_at_zero]
    exact boundary3_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  · intro p
    exact secondary_isHermitian cone3Vectors _ _

theorem principalPath2_nonneg_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : ParameterSpace in nhds (z,0),p.2≤0 → ∀ i,0≤principalPath2 p.1 p.2 i := by
  have he := nonneg_except (fun p : ParameterSpace => principalPath2 p.1 p.2) (z,0) 4
    (fun i => (principalPath2_analytic (z,0) i).continuousAt) (by
      intro i hi
      fin_cases i <;> norm_num [principalPath2] at hi ⊢ <;> first | exact hz _ | contradiction)
  exact he.mono fun p hp han => hp (by change 0≤-p.2; linarith)

theorem path3_nonneg_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : ParameterSpace in nhds (z,0),0≤p.2 → ∀ i,0≤path3 p.1 p.2 i := by
  have he := nonneg_except (fun p : ParameterSpace => path3 p.1 p.2) (z,0) 9
    (fun i => (path3_analytic (z,0) i).continuousAt) (by
      intro i hi
      fin_cases i <;> norm_num [path3] at hi ⊢ <;> first | exact hz _ | contradiction)
  exact he.mono fun p hp hpn => hp hpn

theorem theta_path3_nonneg_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : ParameterSpace in nhds (z,0),p.2≤0 → ∀ i,0≤theta (path3 p.1 p.2) i := by
  have he := nonneg_except (fun p : ParameterSpace => theta (path3 p.1 p.2)) (z,0) 9
    (fun i => (theta_analytic _ (z,0) (path3_analytic (z,0)) i).continuousAt) (by
      intro i hi
      fin_cases i <;> norm_num [path3,theta] at hi ⊢ <;> first
        | exact hz _
        | contradiction
        | (change 0<z 0+0; simpa using hz 0))
  exact he.mono fun p hp hpn => hp (by change 0≤-p.2; linarith)

end D4.C23Local.Joint
