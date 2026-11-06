import D4.DelaunaySupport

noncomputable section
namespace D4.Delaunay
open Matrix Analytic Secondary

 def rankOneZ (v : IntVec) : IntegerGram := fun i j => v i*v j
 def cubeSite (σ : IntVec) (b : Fin 4 → Bool) : IntVec := fun i => if b i then σ i else 0

 theorem unit_quadraticZ (i : Fin 4) (n : IntVec) :
    quadraticZ (rankOneZ (Pi.single i 1)) n=(n i)^2 := by
  simp [quadraticZ, rankOneZ, Matrix.mulVec, dotProduct, Pi.single_apply, sq]

 theorem integer_tight_sites (g : Fin 10 → IntegerGram) (v : Fin 10 → IntVec)
    (S : LatticeSimplex) (σ : IntVec) (u : Fin 4 → Fin 10)
    (hu : ∀ i, g (u i)=rankOneZ (Pi.single i 1) ∧ v (u i)=Pi.single i (σ i))
    (hc : ∀ b : Fin 4 → Bool,
      (∀ k, quadraticZ (g k) (cubeSite σ b)=dotProduct (cubeSite σ b) (v k)) →
      ∃ j, cubeSite σ b=S j)
    (n : IntVec) (hn : ∀ k, quadraticZ (g k) n=dotProduct n (v k)) : ∃ j, n=S j := by
  classical
  have hcoord (i : Fin 4) : n i=0 ∨ n i=σ i := by
    have h := hn (u i)
    rw [(hu i).1,(hu i).2,unit_quadraticZ] at h
    simp only [dotProduct_single] at h
    have hf : n i*(n i-σ i)=0 := by nlinarith [h]
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  let b : Fin 4 → Bool := fun i => decide (n i≠0)
  have hb : cubeSite σ b=n := by
    ext i
    rcases hcoord i with h | h
    · simp [cubeSite,b,h]
    · by_cases hi : n i=0
      · simp [cubeSite,b,hi]
      · simpa [cubeSite,b,hi] using h.symm
  simpa only [hb] using hc b (by simpa only [hb] using hn)

 theorem component_support (g : Fin 10 → IntegerGram) (v : Fin 10 → IntVec)
    (h : ∀ w : Fin 10 → ℝ, (∀ k, 0 ≤ w k) →
      DualSupport (generatedForm g w) (∑ k, w k • castVec (v k))) (k : Fin 10) :
    DualSupport (realMatrix (g k)) (castVec (v k)) := by
  classical
  let w : Fin 10 → ℝ := Pi.single k 1
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    simp only [w,Pi.single_apply]
    split_ifs <;> norm_num
  simpa [w,generatedForm,Pi.single_apply] using h w hw

 theorem tight_sum_iff (g : Fin 10 → IntegerGram) (v : Fin 10 → IntVec)
    (hs : ∀ k, DualSupport (realMatrix (g k)) (castVec (v k)))
    (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (n : IntVec) :
    quadratic (generatedForm g w) (castVec n)=
      dotProduct (castVec n) (∑ k, w k • castVec (v k)) ↔
      ∀ k, quadraticZ (g k) n=dotProduct n (v k) := by
  have hnon (k : Fin 10) :
      0 ≤ w k*((quadraticZ (g k) n:ℝ)-((dotProduct n (v k):ℤ):ℝ)) := by
    apply mul_nonneg (hw k).le
    have h := hs k n
    rw [quadraticZ_cast,cast_dotProduct] at h
    exact sub_nonneg.mpr h
  have he : quadratic (generatedForm g w) (castVec n)-
      dotProduct (castVec n) (∑ k, w k • castVec (v k))=
      ∑ k, w k*((quadraticZ (g k) n:ℝ)-((dotProduct n (v k):ℤ):ℝ)) := by
    rw [quadratic_generated,dotProduct_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [dotProduct_smul,smul_eq_mul,cast_dotProduct,mul_sub]
  constructor
  · intro h k
    have hz : (∑ k, w k*((quadraticZ (g k) n:ℝ)-((dotProduct n (v k):ℤ):ℝ)))=0 := by
      rw [← he,h,sub_self]
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnon k)).mp hz k (Finset.mem_univ k)
    have ht := (mul_eq_zero.mp hk).resolve_left (hw k).ne'
    exact_mod_cast sub_eq_zero.mp ht
  · intro h
    apply sub_eq_zero.mp
    rw [he]
    apply Finset.sum_eq_zero
    intro k _
    rw [h,sub_self,mul_zero]

end D4.Delaunay
