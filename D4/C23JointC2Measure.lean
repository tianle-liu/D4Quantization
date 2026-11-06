import D4.C23JointC2Geometry
import D4.C23SublevelArea

noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope

def localDistance2 (p q r : ℝ) (i : Fin 9) : Fin 3 → ℝ :=
  fun j => -localLower2 r i j-localUpper2 p q r i j

theorem localDistance2_eval (p q r : ℝ) (i : Fin 9) (x : Plane) :
    affineEval (localDistance2 p q r i) x=
      -affineEval (localLower2 r i) x-affineEval (localUpper2 p q r i) x := by
  simp only [affineEval_eq,localDistance2]
  ring

theorem localRegion2_isClosed (p q r η : ℝ) (i : Fin 9) : IsClosed (localRegion2 p q r η i) := by
  fin_cases i
  · exact (isClosed_le (f := fun x : Plane => 0) (g := fun x : Plane => x 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 0) (g := fun x : Plane => 2*(p+r)) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 0) (g := fun x : Plane => x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 1) (g := fun x : Plane => 2*(q+r)) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 2*r) (g := fun x : Plane => x 0+x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 0+x 1) (g := fun x : Plane => 2*(p+q+r)) (by fun_prop) (by fun_prop)))))))
  · exact (isClosed_le (f := fun x : Plane => -η) (g := fun x : Plane => x 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 0) (g := fun x : Plane => 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 2*r) (g := fun x : Plane => x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 1) (g := fun x : Plane => 2*(q+r)) (by fun_prop) (by fun_prop)))))
  · exact (isClosed_le (f := fun x : Plane => -η) (g := fun x : Plane => x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 1) (g := fun x : Plane => 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 2*r) (g := fun x : Plane => x 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 0) (g := fun x : Plane => 2*(p+r)) (by fun_prop) (by fun_prop)))))
  · exact (isClosed_le (f := fun x : Plane => x 0) (g := fun x : Plane => 2*r) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 1) (g := fun x : Plane => 2*r) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 2*r-η) (g := fun x : Plane => x 0+x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 0+x 1) (g := fun x : Plane => 2*r) (by fun_prop) (by fun_prop)))))
  · exact (isClosed_le (f := fun x : Plane => 2*(p+r)) (g := fun x : Plane => x 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 0) (g := fun x : Plane => 2*(p+r)+η) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 0) (g := fun x : Plane => x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 1) (g := fun x : Plane => 2*q) (by fun_prop) (by fun_prop)))))
  · exact (isClosed_le (f := fun x : Plane => 2*(q+r)) (g := fun x : Plane => x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 1) (g := fun x : Plane => 2*(q+r)+η) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 0) (g := fun x : Plane => x 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 0) (g := fun x : Plane => 2*p) (by fun_prop) (by fun_prop)))))
  · exact (isClosed_le (f := fun x : Plane => 2*p) (g := fun x : Plane => x 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 2*q) (g := fun x : Plane => x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 2*(p+q+r)) (g := fun x : Plane => x 0+x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 0+x 1) (g := fun x : Plane => 2*(p+q+r)+η) (by fun_prop) (by fun_prop)))))
  · exact (isClosed_le (f := fun x : Plane => x 0) (g := fun x : Plane => 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 2*(q+r)) (g := fun x : Plane => x 1) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 1-x 0) (g := fun x : Plane => 2*(q+r)+η) (by fun_prop) (by fun_prop))))
  · exact (isClosed_le (f := fun x : Plane => x 1) (g := fun x : Plane => 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => 2*(p+r)) (g := fun x : Plane => x 0) (by fun_prop) (by fun_prop)).inter ((isClosed_le (f := fun x : Plane => x 0-x 1) (g := fun x : Plane => 2*(p+r)+η) (by fun_prop) (by fun_prop))))

theorem localRegion2_compact (p q r η : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r)
    (hη : 0≤η) (i : Fin 9) : IsCompact (localRegion2 p q r η i) :=
  (gap2_sublevel_compact p q r η hp hq hr hη).of_isClosed_subset
    (localRegion2_isClosed p q r η i) (localRegion2_subset p q r η hp hq hr hη i)

theorem localRegion2_integral (p q r η : ℝ) (hp : 0<p) (hq : 0<q) (hr : 0≤r)
    (hη : 0≤η) (f : Plane → ℝ) (hf : Continuous f) :
    (∫ x in {L | gap2 p q r L≤η},f x)=∑ i : Fin 9,∫ x in localRegion2 p q r η i,f x := by
  have hi : IntegrableOn f (⋃ i : Fin 9,localRegion2 p q r η i) := by
    rw [localRegion2_union p q r η hp hq hr hη]
    exact hf.continuousOn.integrableOn_compact (gap2_sublevel_compact p q r η hp.le hq.le hr hη)
  rw [← localRegion2_union p q r η hp hq hr hη,integral_iUnion_ae
    (fun i => (localRegion2_compact p q r η hp.le hq.le hr hη i).measurableSet.nullMeasurableSet)
    (localRegion2_pairwise_null p q r η hp.le hq.le hr) hi,tsum_fintype]

theorem centralRegion2_eq_zero_sublevel (p q r η : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r) :
    localRegion2 p q r η 0={L | gap2 p q r L≤0} := by
  ext x
  change (0≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*(q+r) ∧
    2*r≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r)) ↔ gap2 p q r x≤0
  rw [gap2_le_iff p q r 0 hp hq hr le_rfl]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩
    (repeat' constructor) <;> linarith
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
    (repeat' constructor) <;> linarith

theorem centralRegion2_area (p q r η : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r) :
    volume.real (localRegion2 p q r η 0)=4*(p*q+p*r+q*r) := by
  rw [centralRegion2_eq_zero_sublevel p q r η hp hq hr,
    gap2_sublevel_area p q r 0 hp hq hr le_rfl]
  ring

end D4.C23Local
