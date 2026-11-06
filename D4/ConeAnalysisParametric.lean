import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! A Cauchy mean-value argument for strict concavity after an increasing
change of parameter. The derivative hypotheses are ordinary analytic
premises of this general lemma, to be discharged by the cone formulas. -/
noncomputable section
namespace D4.ConeAnalysis
open Set

def reparametrize (s : Set ℝ) (ω f : ℝ → ℝ) (u : ℝ) : ℝ :=
  f (Function.invFunOn ω s u)

theorem reparametrize_apply {s : Set ℝ} {ω f : ℝ → ℝ}
    (hω : StrictMonoOn ω s) {r : ℝ} (hr : r ∈ s) :
    reparametrize s ω f (ω r) = f r := by
  unfold reparametrize
  rw [hω.injOn.leftInvOn_invFunOn hr]

private theorem slope_eq_some_parameter {s : Set ℝ} (hs : Convex ℝ s)
    {ω f g h : ℝ → ℝ} (hω : StrictMonoOn ω s)
    (hcω : ContinuousOn ω s) (hcf : ContinuousOn f s)
    (hω' : ∀ r ∈ s, HasDerivAt ω (g r) r)
    (hf' : ∀ r ∈ s, HasDerivAt f (h r * g r) r)
    (hg : ∀ r ∈ s, 0 < g r) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) :
    ∃ r ∈ Ioo a b, (f b - f a) / (ω b - ω a) = h r := by
  have hsub : Icc a b ⊆ s := hs.ordConnected.out ha hb
  obtain ⟨r, hr, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    f (fun r => h r * g r) hab (hcf.mono hsub)
    (fun r hr => hf' r (hsub (Ioo_subset_Icc_self hr)))
    ω g (hcω.mono hsub) (fun r hr => hω' r (hsub (Ioo_subset_Icc_self hr)))
  refine ⟨r, hr, ?_⟩
  apply (div_eq_iff (sub_ne_zero.mpr (hω ha hb hab).ne')).mpr
  apply mul_right_cancel₀ (hg r (hsub (Ioo_subset_Icc_self hr))).ne'
  linear_combination -he

/-- A strictly decreasing slope `df/dω` gives strict concavity in ω.
The reparametrization is explicitly constructed from the true inverse
on the image, rather than assumed to exist. -/
theorem strictConcaveOn_reparametrize {s : Set ℝ} (hs : Convex ℝ s)
    {ω f g h : ℝ → ℝ} (hω : StrictMonoOn ω s)
    (hcω : ContinuousOn ω s) (hcf : ContinuousOn f s)
    (hω' : ∀ r ∈ s, HasDerivAt ω (g r) r)
    (hf' : ∀ r ∈ s, HasDerivAt f (h r * g r) r)
    (hg : ∀ r ∈ s, 0 < g r) (hh : StrictAntiOn h s) :
    StrictConcaveOn ℝ (ω '' s) (reparametrize s ω f) := by
  have hconv : Convex ℝ (ω '' s) := (hs.isPreconnected.image ω hcω).convex
  apply strictConcaveOn_of_slope_strict_anti_adjacent hconv
  intro x y z hx hz hxy hyz
  have hy : y ∈ ω '' s := hconv.ordConnected.out hx hz ⟨hxy.le, hyz.le⟩
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨c, hc, rfl⟩ := hz
  have hab : a < b := (hω.lt_iff_lt ha hb).mp hxy
  have hbc : b < c := (hω.lt_iff_lt hb hc).mp hyz
  obtain ⟨u, hu, heu⟩ := slope_eq_some_parameter hs hω hcω hcf hω' hf' hg ha hb hab
  obtain ⟨v, hv, hev⟩ := slope_eq_some_parameter hs hω hcω hcf hω' hf' hg hb hc hbc
  rw [reparametrize_apply hω ha, reparametrize_apply hω hb,
    reparametrize_apply hω hc, heu, hev]
  exact hh (hs.ordConnected.out ha hb (Ioo_subset_Icc_self hu))
    (hs.ordConnected.out hb hc (Ioo_subset_Icc_self hv)) (hu.2.trans hv.1)

end D4.ConeAnalysis
