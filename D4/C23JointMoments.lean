import D4.C23JointPaths
import D4.C23PathMoments

/-! The actual total moment formulas in joint neighborhoods of the two walls. -/
noncomputable section
namespace D4.C23Local.Joint
open Matrix Analytic Principal Secondary Certificate CertificateMoments

theorem path2_moment_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : ParameterSpace in nhds (z,0),
      60*(form2 (path2 p.1 p.2)).det*moment (form2 (path2 p.1 p.2))=
        path2Base p.1 p.2+path2Correction p.1 p.2 := by
  filter_upwards [path2_posDef_eventually z hz,principalPath2_nonneg_eventually z hz,
    positive_eventually z hz] with p hQ hneg hz'
  by_cases ha : 0≤p.2
  · exact (c2_moment_identity (path2 p.1 p.2) (path2_nonneg p.1 hz' p.2 ha) hQ).trans
      (path2_polynomial_positive p.1 p.2 ha)
  · have hQp : (principalForm (principalPath2 p.1 p.2)).PosDef := by
      rwa [← form2_path2_eq_principal]
    have hm := principal_moment_identity (principalPath2 p.1 p.2)
      (hneg (le_of_lt (lt_of_not_ge ha))) hQp
    rw [← form2_path2_eq_principal] at hm
    rw [path2Correction,if_neg ha,add_zero,path2Base,eval_z2_extension_path2]
    linarith

theorem path3_moment_eventually (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : ParameterSpace in nhds (z,0),
      60*(form3 (path3 p.1 p.2)).det*moment (form3 (path3 p.1 p.2))=
        path3Base p.1 p.2+path3Correction p.1 p.2 := by
  filter_upwards [path3_posDef_eventually z hz,path3_nonneg_eventually z hz,
    theta_path3_nonneg_eventually z hz] with p hQ hpos hneg
  by_cases hb : 0≤p.2
  · exact (c3_moment_identity (path3 p.1 p.2) (hpos hb) hQ).trans
      (path3_polynomial_positive p.1 p.2 hb)
  · have hQ2 : (form2 (theta (path3 p.1 p.2))).PosDef := by
      rwa [← form3_eq_form2_theta]
    have hm := c2_moment_identity (theta (path3 p.1 p.2))
      (hneg (le_of_lt (lt_of_not_ge hb))) hQ2
    change 60*(form2 (theta (path3 p.1 p.2))).det*moment (form2 (theta (path3 p.1 p.2)))=_ at hm
    rw [← form3_eq_form2_theta] at hm
    rw [path3Correction,if_neg hb,add_zero,path3Base,eval_theta_extension]
    exact hm

end D4.C23Local.Joint
