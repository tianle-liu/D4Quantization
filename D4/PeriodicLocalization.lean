import D4.DualPeriodMoment
import D4.NearestUniform

/-! Only uniformly finitely many translates of a bounded neighborhood can
meet a moving dual period parallelepiped near a positive-definite form. -/
noncomputable section
namespace D4.Analytic
open Set Matrix MeasureTheory
attribute [local instance] Matrix.normedAddCommGroup

theorem abs_dotProduct_le_sup (x y : Vec) :
    |dotProduct x y|≤4*‖x‖*‖y‖ := by
  unfold dotProduct
  calc
    |∑ i,x i*y i| ≤ ∑ i,|x i*y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 4,‖x‖*‖y‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem norm_le_of_dualMap_bound (R : Gram) {c B : ℝ} (hc : 0<c)
    (hcoerce : ∀ x : Vec,c*‖x‖^2≤quadratic R x)
    (y : Vec) (hy : ‖dualMap R y‖≤B) : ‖y‖≤2*|B|/c := by
  have he : dotProduct y (dualMap R y)=2*quadratic R y := by
    simp only [dualMap,Matrix.smul_mulVec_assoc,dotProduct_smul,smul_eq_mul,quadratic]
  have hd := abs_dotProduct_le_sup y (dualMap R y)
  have hd' : 2*quadratic R y ≤ 4*‖y‖*|B| := by
    calc
      _ ≤ |dotProduct y (dualMap R y)| := by rw [he]; exact le_abs_self _
      _ ≤ 4*‖y‖*‖dualMap R y‖ := hd
      _ ≤ _ := mul_le_mul_of_nonneg_left (hy.trans (le_abs_self B)) (by positivity)
  have hco := hcoerce y
  by_cases hz : ‖y‖=0
  · rw [hz]
    positivity
  have hp : 0<‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  apply (le_div_iff₀ hc).mpr
  nlinarith

theorem norm_unitCube {x : Vec} (hx : x∈unitCube) : ‖x‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  rw [Real.norm_eq_abs,abs_le]
  exact ⟨le_trans (by norm_num) (hx.1 i),hx.2 i⟩

def dualTranslate (R : Gram) (n : IntVec) (W : Set Vec) : Set Vec :=
  (fun w => w+dualMap R (castVec n)) '' W

theorem uniform_finite_dualPeriod_translates {Q : Gram} (hQ : Q.PosDef)
    (c : Vec) (B : ℝ) :
    ∃ ε : ℝ,0<ε ∧ ∃ s : Finset IntVec,
      ∀ R : Gram,‖R-Q‖<ε → ∀ W : Set Vec,(∀ w∈W,‖w‖≤B) →
        ∀ n : IntVec,(dualPeriod R c ∩ dualTranslate R n W).Nonempty → n∈s := by
  obtain ⟨ε,k,hε,hk,hcoerce⟩ := nearby_quadratic_coercive hQ
  obtain ⟨N,hN⟩ := exists_nat_gt (‖c‖+1+2*|B|/k)
  let F : Set IntVec := {n | ∀ i : Fin 4,n i∈Icc (-(N:ℤ)) N}
  have hF : F.Finite := Set.Finite.pi' (fun _ : Fin 4 => Set.finite_Icc (-(N:ℤ)) N)
  refine ⟨ε,hε,hF.toFinset,?_⟩
  intro R hR W hW n hn
  obtain ⟨r,⟨x,hx,hxr⟩,w,hw,hwr⟩ := hn
  have he : dualMap R (c+x-castVec n)=w := by
    unfold dualMap at *
    dsimp only at hxr hwr
    rw [Matrix.mulVec_sub,hxr]
    rw [← hwr]
    abel
  have hy : ‖c+x-castVec n‖≤2*|B|/k :=
    norm_le_of_dualMap_bound R hk (hcoerce R hR) _ (by rw [he]; exact hW w hw)
  have hb : ‖castVec n‖≤‖c‖+1+2*|B|/k := by
    calc
      ‖castVec n‖=‖(c+x)-(c+x-castVec n)‖ := by congr 1; abel
      _ ≤ ‖c+x‖+‖c+x-castVec n‖ := norm_sub_le _ _
      _ ≤ (‖c‖+‖x‖)+2*|B|/k := add_le_add (norm_add_le _ _) hy
      _ ≤ _ := by linarith [norm_unitCube hx]
  apply hF.mem_toFinset.mpr
  intro i
  have hi : |(n i:ℝ)|≤(N:ℝ) := by
    have hh : |(n i:ℝ)|≤‖castVec n‖ := by
      simpa only [castVec,Real.norm_eq_abs] using norm_le_pi_norm (castVec n) i
    linarith
  obtain ⟨hl,hu⟩ := abs_le.mp hi
  exact ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩

end D4.Analytic
