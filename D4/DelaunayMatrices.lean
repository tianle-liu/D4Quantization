import D4.DelaunayData
import D4.DelaunaySemantics
import D4.C23VertexSupport

noncomputable section
namespace D4.Delaunay
open Matrix Analytic Secondary
set_option maxHeartbeats 0

theorem generators1_cast (k : Fin 10) :
    realMatrix (generators1 k)=rankOne (cone1Vectors k) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [realMatrix, generators1, cone1Vectors, rankOne]

theorem generators2_cast (k : Fin 10) :
    realMatrix (generators2 k)=secondaryGenerator cone2Vectors k := by
  refine Fin.cases ?_ (fun j => ?_) k
  · change realMatrix (generators2 0)=gramMatrix ℝ
    ext i l
    fin_cases i <;> fin_cases l <;> norm_num [realMatrix, generators2, gramMatrix]
  · change realMatrix (generators2 j.succ)=rankOne (cone2Vectors j)
    ext i l
    fin_cases j <;> fin_cases i <;> fin_cases l <;>
      norm_num [realMatrix, generators2, cone2Vectors, rankOne] <;>
      norm_num [Matrix.cons_val, Fin.reduceSucc, Fin.reduceFinMk] <;> rfl

theorem generators3_cast (k : Fin 10) :
    realMatrix (generators3 k)=secondaryGenerator cone3Vectors k := by
  refine Fin.cases ?_ (fun j => ?_) k
  · change realMatrix (generators3 0)=gramMatrix ℝ
    ext i l
    fin_cases i <;> fin_cases l <;> norm_num [realMatrix, generators3, gramMatrix]
  · change realMatrix (generators3 j.succ)=rankOne (cone3Vectors j)
    ext i l
    fin_cases j <;> fin_cases i <;> fin_cases l <;>
      norm_num [realMatrix, generators3, cone3Vectors, rankOne] <;>
      norm_num [Matrix.cons_val, Fin.reduceSucc, Fin.reduceFinMk] <;> rfl

theorem generatedForm1 (w : Fin 10 → ℝ) : generatedForm generators1 w=principalForm w := by
  simp only [generatedForm, principalForm, generators1_cast]

theorem generatedForm2 (w : Fin 10 → ℝ) :
    generatedForm generators2 w=secondaryForm cone2Vectors (w 0) (fun j => w j.succ) := by
  simp only [generatedForm, generators2_cast, secondaryGenerator_sum]

theorem generatedForm3 (w : Fin 10 → ℝ) :
    generatedForm generators3 w=secondaryForm cone3Vectors (w 0) (fun j => w j.succ) := by
  simp only [generatedForm, generators3_cast, secondaryGenerator_sum]

end D4.Delaunay
