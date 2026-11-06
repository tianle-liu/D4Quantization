import D4.SecondaryClosedMoment
import D4.C23PathPolynomials
import D4.C23PathNeighborhoods

/-! The independently integrated total moments on both sides of the actual paths. -/
noncomputable section
namespace D4.C23Local
open Matrix Analytic Principal Secondary Certificate CertificateMoments

theorem eval_z2_extension_path2 (z : Parameters) (a : ℝ) :
    eval (CompactMoments.z2 (extendWeight (path2 z a))) momentC1=
      eval (extendWeight (principalPath2 z a)) momentC1 := by
  apply eval_congr_bounded momentC1 10 _ _ momentC1_support
  intro n hn
  have he := congrFun (z2_extension_path2 z a) ⟨n,hn⟩
  simpa only [extendWeight,dif_pos hn] using he

theorem eval_theta_extension (z : Parameters) :
    eval (CompactMoments.theta (extendWeight z)) momentC2=
      eval (extendWeight (theta z)) momentC2 := by
  apply eval_congr_bounded momentC2 10 _ _ momentC2_support
  intro n hn
  have he := congrFun (theta_extension z) ⟨n,hn⟩
  simpa only [extendWeight,dif_pos hn] using he

theorem path2_moment_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ a in nhds (0:ℝ),60*(form2 (path2 z a)).det*moment (form2 (path2 z a))=
      path2Base z a+path2Correction z a := by
  filter_upwards [path2_posDef_eventually z hz,principalPath2_nonneg_eventually z hz]
    with a hQ hneg
  by_cases ha : 0≤a
  · exact (c2_moment_identity (path2 z a) (path2_nonneg z hz a ha) hQ).trans
      (path2_polynomial_positive z a ha)
  · have hQp : (principalForm (principalPath2 z a)).PosDef := by
      rwa [← form2_path2_eq_principal]
    have hm := principal_moment_identity (principalPath2 z a)
      (hneg (le_of_lt (lt_of_not_ge ha))) hQp
    rw [← form2_path2_eq_principal] at hm
    rw [path2Correction,if_neg ha,add_zero,path2Base,eval_z2_extension_path2]
    linarith

theorem path3_moment_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ b in nhds (0:ℝ),60*(form3 (path3 z b)).det*moment (form3 (path3 z b))=
      path3Base z b+path3Correction z b := by
  filter_upwards [path3_posDef_eventually z hz,path3_nonneg_eventually z hz,
    theta_path3_nonneg_eventually z hz] with b hQ hpos hneg
  by_cases hb : 0≤b
  · exact (c3_moment_identity (path3 z b) (hpos hb) hQ).trans
      (path3_polynomial_positive z b hb)
  · have hQ2 : (form2 (theta (path3 z b))).PosDef := by
      rwa [← form3_eq_form2_theta]
    have hm := c2_moment_identity (theta (path3 z b))
      (hneg (le_of_lt (lt_of_not_ge hb))) hQ2
    change 60*(form2 (theta (path3 z b))).det*moment (form2 (theta (path3 z b)))=_ at hm
    rw [← form3_eq_form2_theta] at hm
    rw [path3Correction,if_neg hb,add_zero,path3Base,eval_theta_extension]
    exact hm

end D4.C23Local
