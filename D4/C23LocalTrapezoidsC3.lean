import D4.C23LocalPartitionC3
import D4.AreaTrapezoidAffine
import D4.AreaPlaneSwap

noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope

def localTrapezoid3 (A B η ρ : ℝ) (i : Fin 7) : Trapezoid := ![
  Trapezoid.ofAffine 0 A 0 0 B 0,
  Trapezoid.ofAffine (-η) η 0 1 B 0,
  Trapezoid.ofAffine (-η) η 0 1 A 0,
  Trapezoid.ofAffine A ρ 0 0 (B-A) 1,
  Trapezoid.ofAffine B ρ 0 0 (A-B) 1,
  Trapezoid.ofAffine (-η) η B 0 (B+ρ) 0,
  Trapezoid.ofAffine A ρ (-η) 0 0 0] i

def localSwap3 (i : Fin 7) : Prop := i=2 ∨ i=4

instance (i : Fin 7) : Decidable (localSwap3 i) := inferInstanceAs (Decidable (i=2 ∨ i=4))

private theorem planeSwap_mem_image (x : Plane) (S : Set Plane) :
    x∈planeSwap '' S ↔ planeSwap x∈S := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [planeSwap_involutive] using hy
  · intro hx
    exact ⟨planeSwap x,hx,planeSwap_involutive x⟩

theorem localTrapezoid3_valid (A B η ρ : ℝ) (hA : 0<A) (hB : 0<B)
    (hη : 0<η) (hρ : 0<ρ) (i : Fin 7) : (localTrapezoid3 A B η ρ i).Valid := by
  fin_cases i <;> dsimp [localTrapezoid3,Trapezoid.ofAffine,Trapezoid.Valid] <;>
    constructor <;> try positivity
  all_goals constructor <;> nlinarith

theorem localRegion3_eq_trapezoid (A B η ρ : ℝ) (hA : 0<A) (hB : 0<B)
    (hη : 0<η) (hρ : 0<ρ) (i : Fin 7) :
    localRegion3 A B η ρ i=
      if localSwap3 i then planeSwap '' (localTrapezoid3 A B η ρ i).body
      else (localTrapezoid3 A B η ρ i).body := by
  classical
  ext x
  fin_cases i <;> simp only [localSwap3,Fin.reduceFinMk,show (0:Fin 7)≠2 by decide,
    show (0:Fin 7)≠4 by decide,show (1:Fin 7)≠2 by decide,show (1:Fin 7)≠4 by decide,
    show (3:Fin 7)≠2 by decide,show (3:Fin 7)≠4 by decide,
    show (5:Fin 7)≠2 by decide,show (5:Fin 7)≠4 by decide,
    show (6:Fin 7)≠2 by decide,show (6:Fin 7)≠4 by decide,
    false_or,or_false,or_true,true_or,↓reduceIte,planeSwap_mem_image]
  all_goals dsimp [localRegion3,localTrapezoid3]
  all_goals rw [Trapezoid.ofAffine_body _ _ _ _ _ _ (by assumption)]
  all_goals simp only [planeSwap_zero,planeSwap_one,zero_add,add_zero,zero_mul,one_mul,
    neg_add_cancel,add_neg_cancel]
  all_goals constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;>
    refine ⟨by linarith,by linarith,by linarith,by linarith⟩

end D4.C23Local
