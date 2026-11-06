import D4.C23WindowPartition

noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope

theorem localWindow2_integral_partition {ι : Type*} [Fintype ι]
    (Q : Gram) (U : Plane→ℝ) (hU : Continuous U)
    (K : Set Plane) (hK : IsCompact K) (Ks : ι→Set Plane)
    (hKs : ∀i,IsCompact (Ks i)) (hc : (⋃i,Ks i)=K)
    (hn : Pairwise fun i j=>volume (Ks i∩Ks j)=0) (R : ℝ)
    (f : Vec→ℝ) (hf : Continuous f) :
    (∫r in localWindow2 Q U K R,f r)=∑i,∫r in localWindow2 Q U (Ks i) R,f r := by
  simp_rw [localWindow2_integral Q U hU]
  have hc' : (⋃i,referenceWindow (Ks i) R)=referenceWindow K R := by
    ext x; simp only [Set.mem_iUnion,referenceWindow,Set.mem_prod]
    rw [←hc]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi,hs⟩; exact ⟨⟨i,hi⟩,hs⟩
    · rintro ⟨⟨i,hi⟩,hs⟩; exact ⟨i,hi,hs⟩
  rw [←hc',integral_iUnion_ae,tsum_fintype]
  · intro i
    exact ((hKs i).prod (isCompact_Icc.prod isCompact_Icc)).measurableSet.nullMeasurableSet
  · intro i j hij; exact referenceWindow_inter_null _ _ R (hn hij)
  · rw [hc']
    exact (hf.comp (windowPoint2_continuous Q hU)).continuousOn.integrableOn_compact
      (hK.prod (isCompact_Icc.prod isCompact_Icc))

theorem localWindow2_congr_upper (Q : Gram) (U V : Plane → ℝ) (K : Set Plane) (R : ℝ)
    (hUV : ∀ x∈K,U x=V x) : localWindow2 Q U K R=localWindow2 Q V K R := by
  apply Set.image_congr
  intro x hx
  have hu := hUV x.1 hx.1
  simp only [windowPoint2,fiberCoordinates,hu]

end D4.C23Local
