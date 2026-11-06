import D4.C23LocalCosts
import D4.PrincipalGeometry

/-! Equality in the all-integer zonotope support bound forces individual
positive rank-one generators to be tight. -/
noncomputable section
namespace D4.C23Local
open Matrix Analytic Principal Set

theorem tight_generator (w t : Fin 10 → ℝ) (hw : ∀ e, 0 ≤ w e)
    (ht : t ∈ Icc (-w) w) (n : IntVec)
    (hn : siteCost (principalForm w) (generatorMap t) n = 0)
    (e : Fin 10) (he : 0 < w e) (hte : t e=w e) :
    (∑ i, n i*integerGenerators e i : ℤ)=0 ∨
      (∑ i, n i*integerGenerators e i : ℤ)=1 := by
  let k : Fin 10 → ℝ := fun e => dotProduct (castVec n) (cone1Vectors e)
  have hnon (j : Fin 10) : 0 ≤ w j*(k j)^2-t j*k j := by
    have htj : |t j| ≤ w j := abs_le.mpr ⟨ht.1 j,ht.2 j⟩
    have hk : |k j| ≤ (k j)^2 := by
      dsimp [k]
      rw [integer_generator_dot]
      exact abs_intCast_le_sq _
    have hb : t j*k j ≤ w j*(k j)^2 := calc
      _ ≤ |t j*k j| := le_abs_self _
      _ = |t j| * |k j| := abs_mul _ _
      _ ≤ w j * |k j| := mul_le_mul_of_nonneg_right htj (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (hw j)
    linarith
  have hsum : ∑ j, (w j*(k j)^2-t j*k j) = 0 := by
    rw [Finset.sum_sub_distrib]
    simpa only [siteCost,quadratic_principal,generatorMap_dot,k] using hn
  have hj : w e*(k e)^2-t e*k e=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnon j)).mp hsum e (Finset.mem_univ e)
  rw [hte] at hj
  have hf : w e*(k e*(k e-1))=0 := by nlinarith [hj]
  have hk : k e=0 ∨ k e=1 := by
    have hh := (mul_eq_zero.mp hf).resolve_left he.ne'
    rcases mul_eq_zero.mp hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by linarith)
  dsimp [k] at hk
  rw [integer_generator_dot] at hk
  exact_mod_cast hk

theorem tight_generator_negative (w t : Fin 10 → ℝ) (hw : ∀ e, 0 ≤ w e)
    (ht : t ∈ Icc (-w) w) (n : IntVec)
    (hn : siteCost (principalForm w) (generatorMap t) n=0)
    (e : Fin 10) (he : 0 < w e) (hte : t e= -w e) :
    (∑ i, n i*integerGenerators e i : ℤ)=0 ∨
      (∑ i, n i*integerGenerators e i : ℤ)= -1 := by
  have ht' : -t ∈ Icc (-w) w := by
    constructor <;> intro i
    · exact neg_le_neg (ht.2 i)
    · exact (neg_le).mpr (ht.1 i)
  have hn' : siteCost (principalForm w) (generatorMap (-t)) (-n)=0 := by
    have hc : castVec (-n)= -castVec n := by ext i; simp [castVec]
    rw [map_neg]
    simpa [siteCost,hc,quadratic,Matrix.mulVec_neg,dotProduct_neg,neg_dotProduct] using hn
  have hh := tight_generator w (-t) hw ht' (-n) hn' e he (by simp [hte])
  simp only [Pi.neg_apply,neg_mul,Finset.sum_neg_distrib] at hh
  omega

/-- The six saturated generators already restrict every possible zero-cost
integer competitor to the ten sites listed in the paper. -/
theorem six_generator_sites (n : IntVec)
    (h0 : n 0=0 ∨ n 0=1) (h1 : n 1=0 ∨ n 1=1)
    (h02 : n 0-n 2=0 ∨ n 0-n 2=1) (h03 : n 0-n 3=0 ∨ n 0-n 3=1)
    (h12 : n 1-n 2=0 ∨ n 1-n 2=1) (h13 : n 1-n 3=0 ∨ n 1-n 3=1) :
    ∃ i : Fin 10, n=sites2 i := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · have h2 : n 2=0 ∨ n 2= -1 := by omega
    have h3 : n 3=0 ∨ n 3= -1 := by omega
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
    · refine ⟨0,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]
    · refine ⟨5,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]
    · refine ⟨4,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]
    · refine ⟨6,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]
  · have h2 : n 2=0 := by omega
    have h3 : n 3=0 := by omega
    refine ⟨2,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]
  · have h2 : n 2=0 := by omega
    have h3 : n 3=0 := by omega
    refine ⟨1,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]
  · have h2 : n 2=0 ∨ n 2=1 := by omega
    have h3 : n 3=0 ∨ n 3=1 := by omega
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
    · refine ⟨3,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]
    · refine ⟨8,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]
    · refine ⟨7,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]
    · refine ⟨9,?_⟩; ext i; fin_cases i <;> simp [sites2,h0,h1,h2,h3]

theorem saturated_zonotope_sites (w t : Fin 10 → ℝ) (hw : ∀ e, 0 ≤ w e)
    (ht : t ∈ Icc (-w) w)
    (hp : ∀ e ∈ ({0,1,5,6,7,8} : Finset (Fin 10)), 0 < w e)
    (hs : ∀ e ∈ ({0,1,5,6,7,8} : Finset (Fin 10)), t e=w e)
    (n : IntVec) (hn : siteCost (principalForm w) (generatorMap t) n=0) :
    ∃ i : Fin 10, n=sites2 i := by
  have h0 := tight_generator w t hw ht n hn 0 (hp 0 (by simp)) (hs 0 (by simp))
  have h1 := tight_generator w t hw ht n hn 1 (hp 1 (by simp)) (hs 1 (by simp))
  have h5 := tight_generator w t hw ht n hn 5 (hp 5 (by simp)) (hs 5 (by simp))
  have h6 := tight_generator w t hw ht n hn 6 (hp 6 (by simp)) (hs 6 (by simp))
  have h7 := tight_generator w t hw ht n hn 7 (hp 7 (by simp)) (hs 7 (by simp))
  have h8 := tight_generator w t hw ht n hn 8 (hp 8 (by simp)) (hs 8 (by simp))
  norm_num [integerGenerators,Fin.sum_univ_succ] at h0 h1 h5 h6 h7 h8
  simp only [Matrix.cons_val,Fin.reduceSucc,Fin.reduceFinMk] at h0 h1 h5 h6 h7 h8
  norm_num at h0 h1 h5 h6 h7 h8
  exact six_generator_sites n h0 h1 h5 h6 h7 h8

end D4.C23Local
