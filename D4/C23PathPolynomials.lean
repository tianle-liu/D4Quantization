import D4.C23AnalyticPaths
import D4.CompactMomentFormulas

/-! The analytic polynomial branches and their explicit local corrections. -/
noncomputable section
namespace D4.C23Local
open Matrix Analytic Principal Certificate CertificateMoments

def path2Base (z : Parameters) (a : ℝ) : ℝ :=
  5*eval (CompactMoments.z2 (extendWeight (path2 z a))) momentC1

def path3Base (z : Parameters) (b : ℝ) : ℝ :=
  eval (CompactMoments.theta (extendWeight (path3 z b))) momentC2

def path2Correction (z : Parameters) (a : ℝ) : ℝ :=
  if 0≤a then 2*a^3*(2*a^2+5*a*(z 3+z 4+z 9)+
    10*(z 3*z 4+z 3*z 9+z 4*z 9)) else 0

def path3Correction (z : Parameters) (b : ℝ) : ℝ :=
  if 0≤b then 2*b^3*(3*b^2-5*b*(z 1+z 2)+10*z 1*z 2) else 0

theorem path2Base_analytic (z : Parameters) (a₀ : ℝ) :
    AnalyticAt ℝ (path2Base z) a₀ := by
  apply analyticAt_const.mul
  apply eval_analyticAt
  intro n
  exact eval_analyticAt (fun a => extendWeight (path2 z a)) a₀
    (extendWeight_analyticAt (path2 z) a₀ (path2_analytic z a₀))
    (CompactMoments.z2Substitution n)

theorem path3Base_analytic (z : Parameters) (b₀ : ℝ) :
    AnalyticAt ℝ (path3Base z) b₀ := by
  apply eval_analyticAt
  intro n
  exact eval_analyticAt (fun b => extendWeight (path3 z b)) b₀
    (extendWeight_analyticAt (path3 z) b₀ (path3_analytic z b₀))
    (CompactMoments.thetaSubstitution n)

theorem z2_extension_path2 (z : Parameters) (a : ℝ) :
    (fun i : Fin 10 => CompactMoments.z2 (extendWeight (path2 z a)) i)=
      principalPath2 z a := by
  rw [CompactMoments.z2_coordinates]
  rfl

theorem theta_extension (z : Parameters) :
    (fun i : Fin 10 => CompactMoments.theta (extendWeight z) i)=theta z := by
  rw [CompactMoments.theta_coordinates]
  rfl

theorem path2_polynomial_positive (z : Parameters) (a : ℝ) (ha : 0≤a) :
    eval (extendWeight (path2 z a)) momentC2=path2Base z a+path2Correction z a := by
  rw [CompactMoments.momentC2_compact]
  change path2Base z a+2*a^3*(2*a^2+5*a*(z 3+z 4+z 9)+
    10*(z 3*z 4+z 3*z 9+z 4*z 9))=_
  rw [path2Correction,if_pos ha]

theorem path3_polynomial_positive (z : Parameters) (b : ℝ) (hb : 0≤b) :
    eval (extendWeight (path3 z b)) momentC3=path3Base z b+path3Correction z b := by
  rw [CompactMoments.momentC3_compact]
  change path3Base z b+2*b^3*(3*b^2-5*b*(z 1+z 2)+10*z 1*z 2)=_
  rw [path3Correction,if_pos hb]

end D4.C23Local
