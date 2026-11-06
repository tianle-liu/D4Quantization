import D4.C23LocalCosts
import D4.C23BoundaryPosDef
import D4.CompactMomentMatrices
import D4.CertificateAnalytic
import D4.PrincipalTreeWeights

/-! The two actual paths of quadratic forms and their analytic parameter maps. -/
noncomputable section
namespace D4.C23Local
open Matrix Analytic Principal Certificate

def path2 (z : Parameters) (a : ℝ) : Parameters :=
  ![a,z 1,z 2,z 3,z 4,z 5,z 6,z 7,z 8,z 9]

def principalPath2 (z : Parameters) (a : ℝ) : Parameters :=
  ![z 1+a,z 2+a,z 3,z 4,-a,z 5+a,z 6+a,z 7+a,z 8+a,z 9]

theorem path2_analytic (z : Parameters) (a₀ : ℝ) (i : Fin 10) :
    AnalyticAt ℝ (fun a => path2 z a i) a₀ := by
  fin_cases i <;> first | exact analyticAt_id | exact analyticAt_const

theorem principalPath2_analytic (z : Parameters) (a₀ : ℝ) (i : Fin 10) :
    AnalyticAt ℝ (fun a => principalPath2 z a i) a₀ := by
  fin_cases i <;> first
    | exact analyticAt_const
    | exact analyticAt_id.neg
    | exact analyticAt_const.add analyticAt_id

theorem path3_analytic (z : Parameters) (b₀ : ℝ) (i : Fin 10) :
    AnalyticAt ℝ (fun b => path3 z b i) b₀ := by
  fin_cases i <;> first
    | exact analyticAt_id
    | exact analyticAt_const
    | exact analyticAt_const.sub analyticAt_id
    | exact analyticAt_const.add analyticAt_id

theorem theta_analytic (z : ℝ → Parameters) (t₀ : ℝ)
    (hz : ∀ i,AnalyticAt ℝ (fun t => z t i) t₀) (i : Fin 10) :
    AnalyticAt ℝ (fun t => theta (z t) i) t₀ := by
  fin_cases i
  · exact (hz 0).add (hz 9)
  · exact (hz 1).sub (hz 9)
  · exact (hz 2).sub (hz 9)
  · exact hz 3
  · exact hz 4
  · exact hz 5
  · exact hz 6
  · exact hz 7
  · exact hz 8
  · exact (hz 9).neg

theorem extendWeight_analyticAt (z : ℝ → Parameters) (t₀ : ℝ)
    (hz : ∀ i,AnalyticAt ℝ (fun t => z t i) t₀) (n : Nat) :
    AnalyticAt ℝ (fun t => extendWeight (z t) n) t₀ := by
  by_cases hn : n<10
  · simpa only [extendWeight,dif_pos hn] using hz ⟨n,hn⟩
  · simp only [extendWeight,dif_neg hn]
    exact analyticAt_const

theorem secondaryForm_analyticAt (v : Fin 9 → Vec) (a : ℝ → ℝ)
    (w : ℝ → Fin 9 → ℝ) (t₀ : ℝ) (ha : AnalyticAt ℝ a t₀)
    (hw : ∀ k,AnalyticAt ℝ (fun t => w t k) t₀) (i j : Fin 4) :
    AnalyticAt ℝ (fun t => secondaryForm v (a t) (w t) i j) t₀ := by
  simp only [secondaryForm,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  exact (ha.mul analyticAt_const).add
    (Finset.analyticAt_sum _ (fun k _ => (hw k).mul analyticAt_const))

theorem form2_analyticAt (z : ℝ → Parameters) (t₀ : ℝ)
    (hz : ∀ i,AnalyticAt ℝ (fun t => z t i) t₀) (i j : Fin 4) :
    AnalyticAt ℝ (fun t => form2 (z t) i j) t₀ :=
  secondaryForm_analyticAt cone2Vectors _ _ t₀ (hz 0) (fun k => hz ⟨k.val+1,by omega⟩) i j

theorem form3_analyticAt (z : ℝ → Parameters) (t₀ : ℝ)
    (hz : ∀ i,AnalyticAt ℝ (fun t => z t i) t₀) (i j : Fin 4) :
    AnalyticAt ℝ (fun t => form3 (z t) i j) t₀ :=
  secondaryForm_analyticAt cone3Vectors _ _ t₀ (hz 0) (fun k => hz ⟨k.val+1,by omega⟩) i j

theorem path2_at_zero (z : Parameters) : form2 (path2 z 0)=boundary2Form z :=
  (boundary2_form z).symm

theorem path3_at_zero (z : Parameters) : form3 (path3 z 0)=boundary3Form z := by
  rw [boundary3_form]
  congr 1
  ext i
  fin_cases i <;> simp [path3,boundary3Parameters]

theorem form2_path2_eq_principal (z : Parameters) (a : ℝ) :
    form2 (path2 z a)=principalForm (principalPath2 z a) := by
  have hm := CompactMoments.secondary2_eq_principal (extendWeight (path2 z a))
  have hc := CompactMoments.z2_coordinates (extendWeight (path2 z a))
  have hleft : secondaryForm cone2Vectors (extendWeight (path2 z a) 0)
      (fun i => extendWeight (path2 z a) (i+1))=form2 (path2 z a) := by
    unfold form2
    congr 1
  rw [hleft,hc] at hm
  convert hm using 1

end D4.C23Local
