import D4.DualPeriodMoment

/-! A complete nearest-site list gives the actual finite lower envelope. -/
noncomputable section
namespace D4.Analytic
open Matrix MeasureTheory Set

theorem dualNearest_eq_finite_minimum {ι : Type*} [Fintype ι] [Nonempty ι]
    {Q : Gram} (hQ : Q.PosDef) (r : Vec) (sites : ι → IntVec)
    (hcomplete : ∀ n : IntVec,
      quadratic Q (dualInverse Q r-castVec n)=dualNearest Q r → n∈Set.range sites) :
    dualNearest Q r = quadratic Q⁻¹ r/4 +
      Finset.univ.inf' Finset.univ_nonempty (fun i => dualSiteCost Q r (sites i)) := by
  have he (n : IntVec) : quadratic Q (dualInverse Q r-castVec n)=
      quadratic Q⁻¹ r/4+dualSiteCost Q r n := by
    rw [quadratic_eq_dualSiteCost hQ.1,dualMap_dualInverse hQ]
    have hq := Principal.quadratic_inverse_dual hQ (dualInverse Q r)
    change quadratic Q⁻¹ (dualMap Q (dualInverse Q r)) = _ at hq
    rw [dualMap_dualInverse hQ] at hq
    linarith
  apply le_antisymm
  · have hmin : dualNearest Q r-quadratic Q⁻¹ r/4 ≤
        Finset.univ.inf' Finset.univ_nonempty (fun i => dualSiteCost Q r (sites i)) := by
      apply Finset.le_inf'
      intro i _
      have hn := nearest_le hQ.posSemidef (dualInverse Q r) (sites i)
      rw [he] at hn
      change dualNearest Q r ≤ _ at hn
      linarith
    linarith
  · obtain ⟨n,hn⟩ := nearest_attained hQ (dualInverse Q r)
    obtain ⟨i,rfl⟩ := hcomplete n hn.symm
    have hm := Finset.inf'_le (fun i => dualSiteCost Q r (sites i)) (Finset.mem_univ i)
    rw [he] at hn
    change dualNearest Q r = _ at hn
    linarith

end D4.Analytic
