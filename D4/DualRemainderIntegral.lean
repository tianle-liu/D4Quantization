import D4.DualWindowIntegral

/-! Exact separation of a local embedded window from the moving dual period.
No integral formula for the remaining region is assumed. -/
noncomputable section
namespace D4.Analytic
open Set Matrix MeasureTheory

def dualRemainder (Q : Gram) (c : Vec) (W : Set Vec) : Set Vec :=
  dualPeriod Q c \ ⋃ n : IntVec,dualTranslate Q n W

theorem dualTranslate_pairwise_disjoint (Q : Gram) (W : Set Vec)
    (hinj : ∀ x∈W,∀ n : IntVec,x+dualMap Q (castVec n)∈W → n=0) :
    Pairwise fun n m : IntVec => Disjoint (dualTranslate Q n W) (dualTranslate Q m W) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  rintro _ ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
  have hn : castVec (n-m)=castVec n-castVec m := by
    ext i; simp [castVec]
  have hx : u+dualMap Q (castVec (n-m))=v := by
    rw [hn]
    change u+((2:ℝ) • Q)*ᵥ(castVec n-castVec m)=v
    rw [Matrix.mulVec_sub]
    change v+dualMap Q (castVec m)=u+dualMap Q (castVec n) at he
    change u+(dualMap Q (castVec n)-dualMap Q (castVec m))=v
    linear_combination -he
  have hz := hinj u hu (n-m) (by rw [hx]; exact hv)
  exact hnm (sub_eq_zero.mp hz)

theorem dualNearest_continuous {Q : Gram} (hQ : Q.PosDef) : Continuous (dualNearest Q) := by
  unfold dualNearest
  exact (nearest_continuous_point hQ).comp (by unfold dualInverse; fun_prop)

theorem dualPeriod_compact (Q : Gram) (c : Vec) : IsCompact (dualPeriod Q c) :=
  isCompact_Icc.image (by unfold dualMap; fun_prop)

theorem dualRemainder_integral {Q : Gram} (hQ : Q.PosDef)
    (c : Vec) (W : Set Vec) (hW : IsCompact W)
    (hinj : ∀ x∈W,∀ n : IntVec,x+dualMap Q (castVec n)∈W → n=0) :
    (∫ r in dualRemainder Q c W,dualNearest Q r) +
      (∫ r in W,dualNearest Q r) = ∫ r in dualPeriod Q c,dualNearest Q r := by
  let S : IntVec → Set Vec := fun n => dualTranslate Q n W∩dualPeriod Q c
  have hm (n : IntVec) : MeasurableSet (S n) :=
    ((hW.image (by fun_prop)).inter (dualPeriod_compact Q c)).measurableSet
  have hsub : (⋃ n,S n) ⊆ dualPeriod Q c := by
    intro r hr
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hr
    exact hn.2
  have hi : IntegrableOn (dualNearest Q) (dualPeriod Q c) :=
    (dualNearest_continuous hQ).continuousOn.integrableOn_compact (dualPeriod_compact Q c)
  have hsum : (∫ r in ⋃ n,S n,dualNearest Q r) = ∫ r in W,dualNearest Q r := by
    rw [integral_iUnion hm (fun n m hnm =>
      (dualTranslate_pairwise_disjoint Q W hinj hnm).mono inter_subset_left inter_subset_left)
      (hi.mono_set hsub)]
    exact (dualNearest_window_periodization hQ c W hW).symm
  have hdiff := integral_diff (MeasurableSet.iUnion hm) hi hsub
  have he : dualRemainder Q c W=dualPeriod Q c\⋃ n,S n := by
    ext r
    simp only [dualRemainder,S,mem_diff,mem_iUnion,mem_inter_iff]
    constructor
    · rintro ⟨hp,hn⟩
      exact ⟨hp,fun ⟨n,hx,_⟩ => hn ⟨n,hx⟩⟩
    · rintro ⟨hp,hn⟩
      exact ⟨hp,fun ⟨n,hx⟩ => hn ⟨n,hx,hp⟩⟩
  rw [he,hdiff,hsum]
  ring

theorem dualRemainder_normalization {Q : Gram} (hQ : Q.PosDef)
    (c : Vec) (W : Set Vec) (hW : IsCompact W)
    (hinj : ∀ x∈W,∀ n : IntVec,x+dualMap Q (castVec n)∈W → n=0) :
    (15/4:ℝ)*(∫ r in dualRemainder Q c W,dualNearest Q r) +
      (15/4:ℝ)*(∫ r in W,dualNearest Q r)=60*Q.det*moment Q := by
  rw [← mul_add,dualRemainder_integral hQ c W hW hinj,dualPeriod_integral hQ]

end D4.Analytic
