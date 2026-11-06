import D4.C23LocalPartitionC3

set_option maxHeartbeats 10000
noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope

theorem affineEquality_volume (a b : Fin 3 → ℝ) (hab : a 1≠b 1 ∨ a 2≠b 2) :
    volume {x : Plane | affineEval a x=affineEval b x}=0 := by
  let s : PlaneSlack := ⟨![a 1-b 1,a 2-b 2],b 0-a 0⟩
  have hn : s.normal≠0 := by
    intro h
    rcases hab with h1|h2
    · apply h1
      have hh := congrFun h 0
      change a 1-b 1=0 at hh
      exact sub_eq_zero.mp hh
    · apply h2
      have hh := congrFun h 1
      change a 2-b 2=0 at hh
      exact sub_eq_zero.mp hh
  apply measure_mono_null (t := (s.hyperplane : Set Plane)) ?_ (s.hyperplane_volume hn)
  intro x hx
  change dotProduct s.normal x=s.offset
  simp only [dotProduct,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change (a 1-b 1)*x 0+(a 2-b 2)*x 1=b 0-a 0
  change affineEval a x=affineEval b x at hx
  rw [affineEval_eq,affineEval_eq] at hx
  linarith

private def integerSlopes3 (i : Fin 7) : Fin 4 → ℤ := ![
  ![0,0,0,0],![1,0,0,0],![0,1,0,0],![0,0,-1,0],![0,0,0,-1],![1,0,0,-1],![0,1,-1,0]] i

private theorem integerSlopes3_injective : Function.Injective integerSlopes3 := by
  decide +kernel

private theorem realSlopes3_eq (A B : ℝ) (i : Fin 7) :
    (![localLower3 i 1,localLower3 i 2,localUpper3 A B i 1,localUpper3 A B i 2] : Fin 4 → ℝ) =
      fun k => (integerSlopes3 i k : ℝ) := by
  ext k
  fin_cases i <;> fin_cases k
  all_goals first
    | change (0:ℝ)=((0:ℤ):ℝ)
    | change (1:ℝ)=((1:ℤ):ℝ)
    | change (-1:ℝ)=((-1:ℤ):ℝ)
  all_goals norm_num

theorem localRegion3_distinct_slopes (A B : ℝ) (i j : Fin 7) (hij : i≠j) :
    ((localLower3 i) 1≠(localLower3 j) 1 ∨ (localLower3 i) 2≠(localLower3 j) 2) ∨
    ((localUpper3 A B i) 1≠(localUpper3 A B j) 1 ∨
      (localUpper3 A B i) 2≠(localUpper3 A B j) 2) := by
  by_contra h
  push_neg at h
  apply hij
  apply integerSlopes3_injective
  have hr : (![localLower3 i 1,localLower3 i 2,localUpper3 A B i 1,localUpper3 A B i 2] : Fin 4 → ℝ) =
      ![localLower3 j 1,localLower3 j 2,localUpper3 A B j 1,localUpper3 A B j 2] := by
    ext k
    fin_cases k
    · exact h.1.1
    · exact h.1.2
    · exact h.2.1
    · exact h.2.2
  rw [realSlopes3_eq,realSlopes3_eq] at hr
  ext k
  exact_mod_cast congrFun hr k

theorem localRegion3_pairwise_null (A B η ρ : ℝ) (hA : 0≤A) (hB : 0≤B) :
    Pairwise fun i j : Fin 7 => volume
      (localRegion3 A B η ρ i∩localRegion3 A B η ρ j)=0 := by
  intro i j hij
  rcases localRegion3_distinct_slopes A B i j hij with hl|hu
  · apply measure_mono_null (t := {x | affineEval (localLower3 i) x=affineEval (localLower3 j) x})
      ?_ (affineEquality_volume _ _ hl)
    intro x hx
    exact (localRegion3_affine A B η ρ hA hB i x hx.1).1.symm.trans
      (localRegion3_affine A B η ρ hA hB j x hx.2).1
  · apply measure_mono_null (t := {x | affineEval (localUpper3 A B i) x=affineEval (localUpper3 A B j) x})
      ?_ (affineEquality_volume _ _ hu)
    intro x hx
    exact (localRegion3_affine A B η ρ hA hB i x hx.1).2.symm.trans
      (localRegion3_affine A B η ρ hA hB j x hx.2).2

end D4.C23Local
