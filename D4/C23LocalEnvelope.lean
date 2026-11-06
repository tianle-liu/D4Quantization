import D4.C23LocalCosts
import D4.C23SublevelGeometry

/-! The minimum of the actual ten/eight site costs is the square envelope
used in the area-integral calculation. -/
noncomputable section
namespace D4.C23Local
open Analytic AreaEnvelope

private theorem inf10_grouped (v : Fin 10 → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty v =
      min4 (min4 (v 0) (v 4) (v 5) (v 6)) (v 1) (v 2)
        (min4 (v 3) (v 7) (v 8) (v 9)) := by
  have he (a : ℝ) : a ≤ min4 (min4 (v 0) (v 4) (v 5) (v 6)) (v 1) (v 2)
      (min4 (v 3) (v 7) (v 8) (v 9)) ↔ ∀ i, a ≤ v i := by
    simp only [min4,le_min_iff,Fin.forall_fin_succ, and_true]
    simp only [Fin.reduceSucc,Fin.reduceFinMk]
    aesop
  apply le_antisymm
  · exact (he _).mpr fun i => Finset.inf'_le _ (Finset.mem_univ i)
  · exact Finset.le_inf' _ _ fun i _ => (he _).mp le_rfl i

private theorem inf8_grouped (v : Fin 8 → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty v =
      min4 (min3 (v 0) (v 4) (v 5)) (v 1) (v 2)
        (min3 (v 3) (v 6) (v 7)) := by
  have he (a : ℝ) : a ≤ min4 (min3 (v 0) (v 4) (v 5)) (v 1) (v 2)
      (min3 (v 3) (v 6) (v 7)) ↔ ∀ i, a ≤ v i := by
    simp only [min4,min3,le_min_iff,Fin.forall_fin_succ, and_true]
    simp only [Fin.reduceSucc,Fin.reduceFinMk]
    aesop
  apply le_antisymm
  · exact (he _).mpr fun i => Finset.inf'_le _ (Finset.mem_univ i)
  · exact Finset.le_inf' _ _ fun i _ => (he _).mp le_rfl i

theorem siteMinimum2 (z : Parameters) (r : Vec) :
    let c := coordinates2 (form2 z) r
    let L : Plane := ![c 2,c 3]
    let U := lower2 (z 9) L
    Finset.univ.inf' Finset.univ_nonempty (fun i => siteCost (form2 z) r (sites2 i)) =
      U+min4 0 (c 0-U) (c 1-U)
        ((c 0-U)+(c 1-U)+2*z 0-gap2 (z 3) (z 4) (z 9) L) := by
  dsimp only
  simp_rw [siteCosts2]
  rw [inf10_grouped]
  simp only [costValues2,Matrix.cons_val]
  have he (x y t p q r L₁ L₂ : ℝ) :
      min4 (x+y+t) (x+y+t+2*(p+r)-L₁) (x+y+t+2*(q+r)-L₂)
        (x+y+t+2*(p+q)-(L₁+L₂-2*r)) =
        x+y+t+upper2 p q r ![L₁,L₂] := by
    simp only [upper2,min4,Matrix.cons_val,add_min]
    congr 1
    · ring
    congr 1
    · ring
    congr 1 <;> ring
  rw [he]
  convert minimum_square_recenter (lower2 (z 9) ![(coordinates2 (form2 z) r) 2,
    (coordinates2 (form2 z) r) 3]) (upper2 (z 3) (z 4) (z 9)
      ![(coordinates2 (form2 z) r) 2,(coordinates2 (form2 z) r) 3])
      ((coordinates2 (form2 z) r) 0) ((coordinates2 (form2 z) r) 1) (2*z 0) using 1

theorem siteMinimum3 (z : Parameters) (r : Vec) :
    let Q := form3 z
    let c := coordinates3 Q r
    let t := 2*Q 2 3
    let u := Q 0 0+Q 0 2+Q 0 3+t/2
    let v := Q 1 1+Q 1 2+Q 1 3+t/2
    let L : Plane := ![c 2,c 3]
    let U := lower3 L
    Finset.univ.inf' Finset.univ_nonempty (fun i => siteCost Q r (sites3 i)) =
      U+min4 0 (c 0-U) (c 1-U)
        ((c 0-U)+(c 1-U)+t-gap3 (2*u-t) (2*v-t) L) := by
  dsimp only
  simp_rw [siteCosts3]
  rw [inf8_grouped]
  simp only [costValues3,Matrix.cons_val]
  have he (x y t u v L₁ L₂ : ℝ) :
      min3 (x+y+t) (2*u-L₁+x+y) (2*v-L₂+x+y) =
        x+y+t+upper3 (2*u-t) (2*v-t) ![L₁,L₂] := by
    simp only [upper3,min3,Matrix.cons_val,add_min]
    congr 1
    · ring
    congr 1 <;> ring
  rw [he]
  exact minimum_square_recenter _ _ _ _ _

end D4.C23Local
