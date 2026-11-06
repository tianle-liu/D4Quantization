import D4.AreaTrapezoidAnalytic
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace D4.AreaEnvelope
open Set Matrix MeasureTheory

def planeSwap : Plane ≃ᵐ Plane :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => ℝ) (Equiv.swap 0 1)

@[simp] theorem planeSwap_zero (x : Plane) : planeSwap x 0=x 1 := by
  simp [planeSwap,MeasurableEquiv.piCongrLeft]
@[simp] theorem planeSwap_one (x : Plane) : planeSwap x 1=x 0 := by
  simp [planeSwap,MeasurableEquiv.piCongrLeft]

theorem planeSwap_involutive (x : Plane) : planeSwap (planeSwap x)=x := by
  ext i; fin_cases i <;> simp

theorem planeSwap_preserving : MeasurePreserving planeSwap volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin 2 => ℝ) (Equiv.swap 0 1)

theorem planeSwap_integral (S : Set Plane) (f : Plane → ℝ) :
    (∫ x in planeSwap '' S,f x)=∫ x in S,f (planeSwap x) :=
  planeSwap_preserving.setIntegral_image_emb planeSwap.measurableEmbedding f S

def swapCoefficients (a : Fin 3 → ℝ) : Fin 3 → ℝ := ![a 0,a 2,a 1]

theorem swapCoefficients_eval (a : Fin 3 → ℝ) (x : Plane) :
    affineEval a (planeSwap x)=affineEval (swapCoefficients a) x := by
  simp [affineEval_eq,swapCoefficients]
  ring

theorem analyticAt_negativeSwappedTrapezoidIntegral (R : ℝ) (u d : ℝ → Fin 3 → ℝ)
    (T : ℝ → Trapezoid) (t₀ : ℝ)
    (hu : ∀ i,AnalyticAt ℝ (fun t => u t i) t₀)
    (hd : ∀ i,AnalyticAt ℝ (fun t => d t i) t₀)
    (hT : ∀ k,AnalyticAt ℝ (fun t => (T t).coordinate k) t₀)
    (hvalid : (T t₀).Valid) :
    AnalyticAt ℝ (fun t => ∫ x in planeSwap '' (T t).body,
      4*R^2*affineEval (u t) x+squareNegativePolynomial R (t-affineEval (d t) x)) t₀ := by
  simp_rw [planeSwap_integral,swapCoefficients_eval]
  apply analyticAt_negativeTrapezoidIntegral R _ _ T t₀ _ _ hT hvalid
  · intro i; fin_cases i
    · exact hu 0
    · exact hu 2
    · exact hu 1
  · intro i; fin_cases i
    · exact hd 0
    · exact hd 2
    · exact hd 1

end D4.AreaEnvelope
