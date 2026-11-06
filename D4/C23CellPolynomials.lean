import D4.C23CellDeterminant
import D4.PrincipalTreeWeights
import D4.CertificateProduct

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate

def integerSupportRows (n : Fin 30 → IntVec) (c : SecondaryCell) (k : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℤ := ![n c.f,n c.g,n c.h,Pi.single k 1]

def linearPoly (a : Fin 10 → ℤ) : Poly :=
  normalize (List.ofFn fun k => ([k.val],a k))

def cellFactorCoefficients (g : Fin 9 → IntVec) (V : Fin 120 → Fin 10 → IntVec)
    (n : Fin 30 → IntVec) (c : SecondaryCell) (k : Fin 4) (d : ℤ) : Fin 4 → Fin 10 → ℤ :=
  ![fun j => dotProduct (n c.f) (integerSecondaryGenerator g j *ᵥ n c.f),
    integerSlack g V (n c.g) c.p,
    integerSlack g V (n c.h) c.q,
    fun j => d * (V c.v j k - V c.u j k)]

def cellFactorProduct (g : Fin 9 → IntVec) (V : Fin 120 → Fin 10 → IntVec)
    (n : Fin 30 → IntVec) (c : SecondaryCell) (k : Fin 4) (d : ℤ) : Poly :=
  let f := fun j => linearPoly (cellFactorCoefficients g V n c k d j)
  mulMerge (mulMerge (mulMerge (f 0) (f 1)) (f 2)) (f 3)

theorem linearPoly_eval (w : Fin 10 → ℝ) (a : Fin 10 → ℤ) :
    eval (extendWeight w) (linearPoly a) = ∑ j, w j * (a j : ℝ) := by
  rw [linearPoly,eval_normalize]
  simp only [eval,List.map_ofFn,List.sum_ofFn,Function.comp_apply,monomial,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,extendWeight_fin]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integerQuadratic_cast (g : Fin 9 → IntVec) (n : IntVec) (k : Fin 10) :
    ((dotProduct n (integerSecondaryGenerator g k *ᵥ n) : ℤ) : ℝ) =
      quadratic (secondaryGenerator (fun j => castVec (g j)) k) (castVec n) := by
  rw [← integerSecondaryGenerator_cast]
  simp [quadratic,dotProduct,Matrix.mulVec,castVec,realMatrix,Int.cast_sum,Int.cast_mul]

theorem heightPoly_eval (g : Fin 9 → IntVec) (w : Fin 10 → ℝ) (n : IntVec) :
    eval (extendWeight w) (linearPoly fun k => dotProduct n (integerSecondaryGenerator g k *ᵥ n)) =
      quadratic (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) (castVec n) := by
  rw [linearPoly_eval,← secondaryGenerator_sum,quadratic_sum]
  simp only [quadratic_smul,integerQuadratic_cast]

theorem edgePoly_eval (V : Fin 120 → Fin 10 → IntVec) (w : Fin 10 → ℝ)
    (c : SecondaryCell) (k : Fin 4) (d : ℤ) :
    eval (extendWeight w) (linearPoly fun j => d * (V c.v j k - V c.u j k)) =
      (d : ℝ) * (secondaryVertex V w c.v k - secondaryVertex V w c.u k) := by
  rw [linearPoly_eval]
  simp only [Int.cast_mul,Int.cast_sub,secondaryVertex,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,castVec,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integerSupportRows_cast (Q : Gram) (n : Fin 30 → IntVec) (c : SecondaryCell)
    (k : Fin 4) :
    realMatrix (integerSupportRows n c k) = supportRows (fun f => facetSlack Q (n f)) c k := by
  ext i j
  fin_cases i <;> simp [realMatrix,integerSupportRows,supportRows,facetSlack,castVec,Pi.single_apply]

theorem integerSupportRows_det_cast (Q : Gram) (n : Fin 30 → IntVec) (c : SecondaryCell)
    (k : Fin 4) :
    ((integerSupportRows n c k).det : ℝ) =
      (supportRows (fun f => facetSlack Q (n f)) c k).det := by
  rw [← integerSupportRows_cast]
  exact (Int.castRingHom ℝ).map_det _

theorem cellFactorProduct_eval (g : Fin 9 → IntVec) (V : Fin 120 → Fin 10 → IntVec)
    (n : Fin 30 → IntVec) (w : Fin 10 → ℝ) (c : SecondaryCell) (k : Fin 4) (d : ℤ)
    (hd : d^2 = 1) (hdet : (integerSupportRows n c k).det = d)
    (hc : FanCellGeometry
      (fun f => facetSlack (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) (n f))
      (secondaryVertex V w) c) :
    eval (extendWeight w) (cellFactorProduct g V n c k d) =
      (simplexMatrix (cellVertices (secondaryVertex V w) c)).det := by
  let Q := secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)
  let s := fun f => facetSlack Q (n f)
  have hh := cell_determinant_factor s (secondaryVertex V w) c k hc
  have hdc : (supportRows s c k).det = (d : ℝ) := by
    rw [← integerSupportRows_det_cast Q n c k,hdet]
  rw [hdc] at hh
  have hd' : (d : ℝ)^2 = 1 := by exact_mod_cast hd
  simp only [cellFactorProduct,eval_mulMerge]
  change eval (extendWeight w) (linearPoly _) * eval (extendWeight w) (linearPoly _) *
      eval (extendWeight w) (linearPoly _) * eval (extendWeight w) (linearPoly _) = _
  change eval (extendWeight w) (linearPoly fun j => dotProduct (n c.f) (integerSecondaryGenerator g j *ᵥ n c.f)) *
      eval (extendWeight w) (linearPoly (integerSlack g V (n c.g) c.p)) *
      eval (extendWeight w) (linearPoly (integerSlack g V (n c.h) c.q)) *
      eval (extendWeight w) (linearPoly fun j => d * (V c.v j k - V c.u j k)) = _
  rw [heightPoly_eval,linearPoly_eval,linearPoly_eval,edgePoly_eval,
    ← facetSlack_secondaryVertex,← facetSlack_secondaryVertex]
  change (s c.f).offset * (s c.g).eval (secondaryVertex V w c.p) *
      (s c.h).eval (secondaryVertex V w c.q) *
      ((d : ℝ) * (secondaryVertex V w c.v k - secondaryVertex V w c.u k)) = _
  calc
    _ = (d : ℝ) * ((s c.f).offset * (s c.g).eval (secondaryVertex V w c.p) *
      (s c.h).eval (secondaryVertex V w c.q) *
      (secondaryVertex V w c.v k - secondaryVertex V w c.u k)) := by ring
    _ = (d : ℝ) * ((d : ℝ) * (simplexMatrix (cellVertices (secondaryVertex V w) c)).det) := by rw [hh]
    _ = _ := by rw [← mul_assoc,← pow_two,hd',one_mul]

end D4.Secondary
