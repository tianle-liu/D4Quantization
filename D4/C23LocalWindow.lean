import D4.C23LocalCoordinates
import D4.C23LocalEnvelope
import D4.DualPeriodMoment
import Mathlib.MeasureTheory.Constructions.Pi

/-! The actual four-dimensional windows used in the local calculations. -/
noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope

abbrev WindowCoordinates := Plane × (ℝ × ℝ)

def inverseCoordinates2 (Q : Gram) (c : Vec) : Vec :=
  ![Q 0 0-c 0,Q 1 1-c 1,c 2-Q 2 2,c 3-Q 3 3]

def inverseCoordinates3 (Q : Gram) (c : Vec) : Vec :=
  ![c 2-Q 0 0,c 3-Q 1 1,Q 2 2-c 0,Q 3 3-c 1]

@[simp] theorem coordinates2_inverse (Q : Gram) (c : Vec) :
    coordinates2 Q (inverseCoordinates2 Q c)=c := by
  ext i; fin_cases i <;> simp [coordinates2,inverseCoordinates2]

@[simp] theorem inverse_coordinates2 (Q : Gram) (r : Vec) :
    inverseCoordinates2 Q (coordinates2 Q r)=r := by
  ext i; fin_cases i <;> simp [coordinates2,inverseCoordinates2]

@[simp] theorem coordinates3_inverse (Q : Gram) (c : Vec) :
    coordinates3 Q (inverseCoordinates3 Q c)=c := by
  ext i; fin_cases i <;> simp [coordinates3,inverseCoordinates3]

@[simp] theorem inverse_coordinates3 (Q : Gram) (r : Vec) :
    inverseCoordinates3 Q (coordinates3 Q r)=r := by
  ext i; fin_cases i <;> simp [coordinates3,inverseCoordinates3]

def fiberCoordinates (U : Plane → ℝ) (p : WindowCoordinates) : Vec :=
  ![p.2.1+U p.1,p.2.2+U p.1,p.1 0,p.1 1]

def windowPoint2 (Q : Gram) (U : Plane → ℝ) (p : WindowCoordinates) : Vec :=
  inverseCoordinates2 Q (fiberCoordinates U p)

def windowPoint3 (Q : Gram) (U : Plane → ℝ) (p : WindowCoordinates) : Vec :=
  inverseCoordinates3 Q (fiberCoordinates U p)

def referenceWindow (K : Set Plane) (R : ℝ) : Set WindowCoordinates :=
  K ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)

def localWindow2 (Q : Gram) (U : Plane → ℝ) (K : Set Plane) (R : ℝ) : Set Vec :=
  windowPoint2 Q U '' referenceWindow K R

def localWindow3 (Q : Gram) (U : Plane → ℝ) (K : Set Plane) (R : ℝ) : Set Vec :=
  windowPoint3 Q U '' referenceWindow K R

theorem windowPoint2_continuous (Q : Gram) {U : Plane → ℝ} (hU : Continuous U) :
    Continuous (windowPoint2 Q U) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : WindowCoordinates => Q 0 0-(p.2.1+U p.1)); fun_prop
  · change Continuous (fun p : WindowCoordinates => Q 1 1-(p.2.2+U p.1)); fun_prop
  · change Continuous (fun p : WindowCoordinates => p.1 0-Q 2 2); fun_prop
  · change Continuous (fun p : WindowCoordinates => p.1 1-Q 3 3); fun_prop

theorem windowPoint3_continuous (Q : Gram) {U : Plane → ℝ} (hU : Continuous U) :
    Continuous (windowPoint3 Q U) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : WindowCoordinates => p.1 0-Q 0 0); fun_prop
  · change Continuous (fun p : WindowCoordinates => p.1 1-Q 1 1); fun_prop
  · change Continuous (fun p : WindowCoordinates => Q 2 2-(p.2.1+U p.1)); fun_prop
  · change Continuous (fun p : WindowCoordinates => Q 3 3-(p.2.2+U p.1)); fun_prop

theorem localWindow2_compact (Q : Gram) {U : Plane → ℝ} (hU : Continuous U)
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) : IsCompact (localWindow2 Q U K R) :=
  (hK.prod (isCompact_Icc.prod isCompact_Icc)).image (windowPoint2_continuous Q hU)

theorem localWindow3_compact (Q : Gram) {U : Plane → ℝ} (hU : Continuous U)
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) : IsCompact (localWindow3 Q U K R) :=
  (hK.prod (isCompact_Icc.prod isCompact_Icc)).image (windowPoint3_continuous Q hU)

def splitCoordinates : Vec ≃ᵐ WindowCoordinates :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
    (((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).trans
      (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm))

theorem splitCoordinates_apply (c : Vec) :
    splitCoordinates c=(![c 2,c 3],(c 0,c 1)) := by
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · rfl

theorem splitCoordinates_symm_apply (p : WindowCoordinates) :
    splitCoordinates.symm p=![p.2.1,p.2.2,p.1 0,p.1 1] := by
  ext i; fin_cases i <;> rfl

theorem splitCoordinates_preserving : MeasurePreserving splitCoordinates volume volume := by
  exact Measure.measurePreserving_swap.comp
    ((volume_preserving_prodAssoc.symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id volume).prod
        (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0)))

end D4.C23Local
