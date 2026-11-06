import D4.ConeAnalysisLimits

/-! The ratio monotonicity and facet-count comparison from concavity and
the proved zero limit, for the actual cone-angle function. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Filter
open scoped Topology

theorem profile_div_antitone (n : ℕ) (hn : 2 ≤ n) (K D : ℝ)
    (hK : 0 < K) (hD : 0 < D) :
    AntitoneOn (fun u => profile n K D u / u) (Ioo 0 (angle n D (Real.pi/2))) := by
  intro x hx y hy hxy
  rcases lt_or_eq_of_le hxy with hxy | rfl
  · have hlim : Tendsto (fun t => (profile n K D x - profile n K D t) / (x-t))
        (𝓝[>] (0:ℝ)) (𝓝 (profile n K D x / x)) := by
      have H := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => profile n K D x)
        (𝓝[>] (0:ℝ)) (𝓝 (profile n K D x))).sub
        (profile_tendsto_zero n hn K D hD)).div
        (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds))
        (by simpa using hx.1.ne')
      simpa only [sub_zero] using H
    have H : (profile n K D y - profile n K D x) / (y-x) ≤ profile n K D x / x := by
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hx.1).filter_mono nhdsWithin_le_nhds] with t ht htx
      exact (profile_strictConcave_interval n hn K D hK hD).concaveOn.slope_anti_adjacent
        (show t ∈ Ioo 0 (angle n D (Real.pi/2)) from ⟨ht, htx.trans hx.2⟩) hy htx hxy
    have H' := (div_le_div_iff₀ (sub_pos.mpr hxy) hx.1).mp H
    apply (div_le_div_iff₀ hy.1 hx.1).mpr
    nlinarith only [H']
  · exact le_rfl

/-- Increasing an upper bound for the number of facets weakens the
resulting cone comparison in exactly the direction used in the paper. -/
theorem count_profile_mono (n : ℕ) (hn : 2 ≤ n) (K D A m f : ℝ)
    (hK : 0 < K) (hD : 0 < D) (hA : 0 < A) (hm : 0 < m) (hmf : m ≤ f)
    (hangle : A/m < angle n D (Real.pi/2)) :
    m * profile n K D (A/m) ≤ f * profile n K D (A/f) := by
  have hf : 0 < f := hm.trans_le hmf
  have hfm : A/f ≤ A/m :=
    (div_le_div_iff₀ hf hm).mpr (mul_le_mul_of_nonneg_left hmf hA.le)
  have H := profile_div_antitone n hn K D hK hD
    (show A/f ∈ Ioo 0 (angle n D (Real.pi/2)) from
      ⟨div_pos hA hf, hfm.trans_lt hangle⟩)
    (show A/m ∈ Ioo 0 (angle n D (Real.pi/2)) from ⟨div_pos hA hm, hangle⟩) hfm
  have H' := mul_le_mul_of_nonneg_left H hA.le
  convert H' using 1 <;> field_simp <;> ring

end D4.ConeAnalysis
