import D4.C23Masks

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal MeasureTheory

/-- All hypotheses here are finite mask identities or linear supporting
inequalities. The output concerns the genuine Lebesgue measure of simplices. -/
theorem cells_pairwise_null {n : Nat} (c : Fin n → SecondaryCell)
    (mask : Fin 30 → Nat) (apex : Fin 30 → Fin 120)
    (faceApex : Fin 30 → Fin 30 → Fin 120)
    (s : Fin 30 → AffineSlack) (V : Fin 120 → Vec)
    (hb : ∀ f, mask f < 2^120) (hm : Function.Injective mask)
    (hkeys : Function.Injective (fun i => cellKey (c i)))
    (hap : ∀ t, (c t).p = apex (c t).f ∧ (c t).q = faceApex (c t).f (c t).g)
    (hinc : ∀ t,
      OnMask mask (c t).f (c t).p ∧ OnMask mask (c t).f (c t).q ∧
      OnMask mask (c t).f (c t).u ∧ OnMask mask (c t).f (c t).v ∧
      ¬OnMask mask (c t).g (c t).p ∧ OnMask mask (c t).g (c t).q ∧
      OnMask mask (c t).g (c t).u ∧ OnMask mask (c t).g (c t).v ∧
      ¬OnMask mask (c t).h (c t).q ∧ OnMask mask (c t).h (c t).u ∧
      OnMask mask (c t).h (c t).v)
    (hcanon2 : ∀ t g, mask (c t).f &&& mask g = mask (c t).f &&& mask (c t).g → (c t).g ≤ g)
    (hcanon3 : ∀ t h, mask (c t).f &&& mask (c t).g &&& mask h =
        mask (c t).f &&& mask (c t).g &&& mask (c t).h → (c t).h ≤ h)
    (hs : ∀ f r, (OnMask mask f r → (s f).eval (V r) = 0) ∧
      (¬OnMask mask f r → 0 < (s f).eval (V r)))
    (h0 : ∀ f, 0 < (s f).eval 0) :
    Pairwise fun i j => volume (vertexSimplex (cellVertices V (c i)) ∩
      vertexSimplex (cellVertices V (c j))) = 0 := by
  classical
  apply fanCells_pairwise_null s V c
  · intro f r
    by_cases h : OnMask mask f r
    · rw [(hs f r).1 h]
    · exact ((hs f r).2 h).le
  · exact h0
  · intro t
    rcases hinc t with ⟨hfp,hfq,hfu,hfv,hgp,hgq,hgu,hgv,hhq,hhu,hhv⟩
    exact ⟨(hs _ _).1 hfp,(hs _ _).1 hfq,(hs _ _).1 hfu,(hs _ _).1 hfv,
      (hs _ _).2 hgp,(hs _ _).1 hgq,(hs _ _).1 hgu,(hs _ _).1 hgv,
      (hs _ _).2 hhq,(hs _ _).1 hhu,(hs _ _).1 hhv⟩
  · intro i j hf
    rw [(hap i).1,(hap j).1,hf]
  · intro i j hf hg
    rw [(hap i).2,(hap j).2,hf,hg]
  · intro i j hf hg hh
    apply hkeys
    simp only [cellKey,hf,hg,hh]
  · intro i j hne
    obtain ⟨r,hr|hr⟩ := mask_ne_witness (hb (c i).f) (hb (c j).f)
      (fun h => hne (hm h))
    · exact ⟨r,Or.inl ⟨(hs _ _).1 hr.1,(hs _ _).2 hr.2⟩⟩
    · exact ⟨r,Or.inr ⟨(hs _ _).1 hr.1,(hs _ _).2 hr.2⟩⟩
  · intro i j hf hg
    have hne : mask (c i).f &&& mask (c i).g ≠ mask (c i).f &&& mask (c j).g := by
      intro he
      apply hg
      exact le_antisymm (hcanon2 i _ he.symm) (hcanon2 j _ (by simpa only [← hf] using he))
    obtain ⟨r,hr|hr⟩ := mask_ne_witness (Nat.and_le_left.trans_lt (hb (c i).f))
      (Nat.and_le_left.trans_lt (hb (c i).f)) hne
    · simp only [Nat.testBit_and,Bool.and_eq_true] at hr
      exact ⟨r,(hs _ _).1 hr.1.1,Or.inl ⟨(hs _ _).1 hr.1.2,
        (hs _ _).2 (fun h => hr.2 (by simpa only [OnMask, hr.1.1, Bool.true_and] using h))⟩⟩
    · simp only [Nat.testBit_and,Bool.and_eq_true] at hr
      exact ⟨r,(hs _ _).1 hr.1.1,Or.inr ⟨(hs _ _).1 hr.1.2,
        (hs _ _).2 (fun h => hr.2 (by simpa only [OnMask, hr.1.1, Bool.true_and] using h))⟩⟩
  · intro i j hf hg hh
    have hne : mask (c i).f &&& mask (c i).g &&& mask (c i).h ≠
        mask (c i).f &&& mask (c i).g &&& mask (c j).h := by
      intro he
      apply hh
      exact le_antisymm (hcanon3 i _ he.symm)
        (hcanon3 j _ (by simpa only [← hf,← hg] using he))
    have hb' : mask (c i).f &&& mask (c i).g < 2^120 := Nat.and_le_left.trans_lt (hb _)
    obtain ⟨r,hr|hr⟩ := mask_ne_witness (Nat.and_le_left.trans_lt hb')
      (Nat.and_le_left.trans_lt hb') hne
    · simp only [Nat.testBit_and,Bool.and_eq_true] at hr
      exact ⟨r,(hs _ _).1 hr.1.1.1,(hs _ _).1 hr.1.1.2,
        Or.inl ⟨(hs _ _).1 hr.1.2,(hs _ _).2 (fun h => hr.2 (by simpa only [OnMask, hr.1.1.1, hr.1.1.2, Bool.true_and] using h))⟩⟩
    · simp only [Nat.testBit_and,Bool.and_eq_true] at hr
      exact ⟨r,(hs _ _).1 hr.1.1.1,(hs _ _).1 hr.1.1.2,
        Or.inr ⟨(hs _ _).1 hr.1.2,(hs _ _).2 (fun h => hr.2 (by simpa only [OnMask, hr.1.1.1, hr.1.1.2, Bool.true_and] using h))⟩⟩

end D4.Secondary
