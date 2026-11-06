import D4.C23CellGeometry
import D4.C23CoefficientSupport

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal

def CellMaskIncidence (mask : Fin 30 → Nat) (c : SecondaryCell) : Prop :=
  OnMask mask c.f c.p ∧ OnMask mask c.f c.q ∧ OnMask mask c.f c.u ∧ OnMask mask c.f c.v ∧
  ¬OnMask mask c.g c.p ∧ OnMask mask c.g c.q ∧ OnMask mask c.g c.u ∧ OnMask mask c.g c.v ∧
  ¬OnMask mask c.h c.q ∧ OnMask mask c.h c.u ∧ OnMask mask c.h c.v

theorem fanCellGeometry_of_mask (mask : Fin 30 → Nat) (s : Fin 30 → AffineSlack)
    (V : Fin 120 → Vec) (c : SecondaryCell)
    (hs : ∀ f r, (OnMask mask f r → (s f).eval (V r) = 0) ∧
      (¬OnMask mask f r → 0 < (s f).eval (V r)))
    (hinc : CellMaskIncidence mask c) : FanCellGeometry s V c := by
  rcases hinc with ⟨hfp,hfq,hfu,hfv,hgp,hgq,hgu,hgv,hhq,hhu,hhv⟩
  exact ⟨(hs _ _).1 hfp,(hs _ _).1 hfq,(hs _ _).1 hfu,(hs _ _).1 hfv,
    (hs _ _).2 hgp,(hs _ _).1 hgq,(hs _ _).1 hgu,(hs _ _).1 hgv,
    (hs _ _).2 hhq,(hs _ _).1 hhu,(hs _ _).1 hhv⟩

theorem facetSlack_origin_pos {Q : Gram} (hQ : Q.PosDef) (n : IntVec) (hn : n ≠ 0) :
    0 < (facetSlack Q n).eval 0 := by
  have hcast : castVec n ≠ 0 := by
    intro h
    apply hn
    apply castVec_injective
    have hz : castVec (0 : IntVec) = 0 := by
      ext i
      simp [castVec]
    exact h.trans hz.symm
  simpa only [facetSlack,AffineSlack.eval,dotProduct_zero,sub_zero,quadratic,star_trivial]
    using hQ.2 (castVec n) hcast

end D4.Secondary
