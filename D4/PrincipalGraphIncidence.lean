import D4.PrincipalGraphFourDefs

namespace D4.PrincipalGraphs
open Principal Matrix

/-- The reduced incidence matrix obtained by deleting vertex zero from K₅. -/
def reducedIncidence : Matrix (Fin 4) (Fin 10) ℤ := fun i e =>
  (if edgeLo e = i.succ then 1 else 0) - (if edgeHi e = i.succ then 1 else 0)

def generatorSign (e : Fin 10) : ℤ := if edgeLo e=0 then -1 else 1

theorem integerGenerators_eq_incidence : ∀ (e : Fin 10) (i : Fin 4),
    integerGenerators e i = generatorSign e * reducedIncidence i e := by decide +kernel

def incidenceMinor (H : Finset (Fin 10)) : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => reducedIncidence i (minorEdges H j)

theorem canonicalMinor_eq_incidence (H : Finset (Fin 10)) :
    canonicalMinor H = incidenceMinor H * diagonal (fun j => generatorSign (minorEdges H j)) := by
  ext i j
  simp only [mul_diagonal, canonicalMinor, incidenceMinor]
  rw [integerGenerators_eq_incidence, mul_comm]

theorem abs_generatorSign (e : Fin 10) : |generatorSign e|=1 := by
  unfold generatorSign
  split_ifs <;> norm_num

theorem canonicalMinor_abs_det_eq_incidence (H : Finset (Fin 10)) :
    |(canonicalMinor H).det| = |(incidenceMinor H).det| := by
  rw [canonicalMinor_eq_incidence, det_mul, det_diagonal, abs_mul, Finset.abs_prod]
  simp only [abs_generatorSign, Finset.prod_const_one, mul_one]

theorem canonicalMinor_nonzero_iff_incidence (H : Finset (Fin 10)) :
    (canonicalMinor H).det ≠ 0 ↔ (incidenceMinor H).det ≠ 0 := by
  apply not_congr
  simpa only [abs_eq_zero] using
    (show |(canonicalMinor H).det|=0 ↔ |(incidenceMinor H).det|=0 by
      rw [canonicalMinor_abs_det_eq_incidence])

end D4.PrincipalGraphs
