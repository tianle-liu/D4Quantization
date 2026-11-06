import D4.Certificate
import D4.KernelCompute
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card

/-! Exhaustive enumeration of the homogeneous degree-five monomials in
exactly ten variables, with a proof of completeness and no duplicate terms. -/
namespace D4.PaperStatistics
open Certificate

def monomialsFrom : Nat → Nat → List Monomial :=
  Nat.rec (fun _ => [[]]) (fun _ prev lo =>
    (List.range (10-lo)).flatMap fun k => (prev (lo+k)).map (List.cons (lo+k)))

theorem mem_monomialsFrom (d lo : Nat) (m : Monomial) :
    m ∈ monomialsFrom d lo ↔ m.length=d ∧ m.Pairwise (· ≤ ·) ∧
      ∀ i ∈ m, lo ≤ i ∧ i < 10 := by
  induction d generalizing lo m with
  | zero => cases m <;> simp [monomialsFrom]
  | succ d ih =>
    cases m with
    | nil => simp [monomialsFrom]
    | cons a as =>
      constructor
      · intro h
        change a::as ∈ (List.range (10-lo)).flatMap (fun k => (monomialsFrom d (lo+k)).map (List.cons (lo+k))) at h
        obtain ⟨k,hk,hms⟩ := List.mem_flatMap.mp h
        have hk' : k < 10-lo := List.mem_range.mp hk
        obtain ⟨tail,htail,he⟩ := List.mem_map.mp hms
        rcases List.cons.inj he with ⟨rfl,rfl⟩
        have hh := (ih (lo+k) tail).mp htail
        refine ⟨by simp [hh.1],List.pairwise_cons.mpr ⟨?_,hh.2.1⟩,?_⟩
        · exact fun i hi => (hh.2.2 i hi).1
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · omega
          · have := hh.2.2 i hi
            omega
      · rintro ⟨hlen,hs,hb⟩
        have ha := hb a (by simp)
        have htail : as ∈ monomialsFrom d a := (ih a as).mpr
          ⟨by simpa using hlen,(List.pairwise_cons.mp hs).2,
            fun i hi => ⟨(List.pairwise_cons.mp hs).1 i hi,(hb i (by simp [hi])).2⟩⟩
        apply List.mem_flatMap.mpr
        refine ⟨a-lo,List.mem_range.mpr (by omega),?_⟩
        have he : lo+(a-lo)=a := by omega
        rw [he]
        exact List.mem_map.mpr ⟨as,htail,rfl⟩

theorem monomialsFrom_nodup (d lo : Nat) : (monomialsFrom d lo).Nodup := by
  induction d generalizing lo with
  | zero => simp [monomialsFrom]
  | succ d ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨fun k _ => (ih (lo+k)).map (by intro x y h; exact List.cons.inj h |>.2),?_⟩
    apply List.nodup_range.imp
    intro a b hab m hm hn
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
    obtain ⟨y,hy,hf⟩ := List.mem_map.mp hn
    have hc := List.cons.inj (he.trans hf.symm) |>.1
    exact hab (Nat.add_left_cancel hc)

def degreeFive : List Monomial := monomialsFrom 5 0

theorem degreeFive_complete (m : Monomial) :
    m ∈ degreeFive ↔ m.length=5 ∧ m.Pairwise (· ≤ ·) ∧ ∀ i ∈ m, i<10 := by
  simpa [degreeFive] using mem_monomialsFrom 5 0 m

theorem degreeFive_nodup : degreeFive.Nodup := monomialsFrom_nodup 5 0

theorem degreeFive_length : degreeFive.length=2002 := by kernel_rfl

theorem degreeFive_card : degreeFive.toFinset.card=2002 := by
  rw [List.toFinset_card_of_nodup degreeFive_nodup,degreeFive_length]

end D4.PaperStatistics
