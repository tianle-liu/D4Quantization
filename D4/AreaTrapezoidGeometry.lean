import D4.AreaTrapezoid
import D4.AreaSubdivision

noncomputable section
namespace D4.AreaEnvelope
open Set Matrix MeasureTheory

theorem Trapezoid.matrix_det_pos (T : Trapezoid) (hT : T.Valid) (i : Fin 2) :
    0<(T.matrix i).det := by
  rw [Matrix.det_fin_two]
  fin_cases i
  · change 0<T.width*(T.topRight-T.bottomLeft)-T.width*(T.bottomRight-T.bottomLeft)
    nlinarith [mul_pos hT.1 (sub_pos.mpr hT.2.2)]
  · change 0<T.width*(T.topLeft-T.bottomLeft)-0*(T.topRight-T.bottomLeft)
    simpa using mul_pos hT.1 (sub_pos.mpr hT.2.1)

theorem Trapezoid.first_second_null (T : Trapezoid) (hT : T.Valid) :
    volume (affineTriangle (T.matrix 0) T.origin∩affineTriangle (T.matrix 1) T.origin)=0 := by
  let s : PlaneSlack := ⟨![-(T.topRight-T.bottomLeft),T.width],
    T.width*T.bottomLeft-(T.topRight-T.bottomLeft)*T.left⟩
  have hn : s.normal≠0 := by
    intro h
    have hh := congrFun h 1
    change T.width=0 at hh
    exact hT.1.ne' hh
  apply measure_mono_null (t := (s.hyperplane : Set Plane)) ?_ (s.hyperplane_volume hn)
  intro x hx
  have hfirst := (T.first_mem_iff hT x).mp hx.1
  have hsecond := (T.second_mem_iff hT x).mp hx.2
  have hy : x 1=T.bottomLeft+(T.topRight-T.bottomLeft)*T.parameter x :=
    le_antisymm hfirst.2.2.2 hsecond.2.2.1
  have hx : x 0=T.width*T.parameter x+T.left := by
    unfold Trapezoid.parameter
    field_simp [hT.1.ne']
  change dotProduct s.normal x=s.offset
  simp only [dotProduct,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change -(T.topRight-T.bottomLeft)*x 0+T.width*x 1=
    T.width*T.bottomLeft-(T.topRight-T.bottomLeft)*T.left
  rw [hx,hy]
  ring

theorem Trapezoid.pairwise_null (T : Trapezoid) (hT : T.Valid) :
    Pairwise fun i j : Fin 2 => volume
      (affineTriangle (T.matrix i) T.origin∩affineTriangle (T.matrix j) T.origin)=0 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact T.first_second_null hT
  · rw [Set.inter_comm]
    exact T.first_second_null hT
  · exact (hij rfl).elim

theorem Trapezoid.compact (T : Trapezoid) (hT : T.Valid) : IsCompact T.body := by
  rw [← T.cover hT]
  exact isCompact_iUnion fun i => affineTriangle_compact _ _

theorem Trapezoid.integral_triangles (T : Trapezoid) (hT : T.Valid)
    (f : Plane → ℝ) (hf : ContinuousOn f T.body) :
    (∫ x in T.body,f x)=∑ i : Fin 2,∫ x in affineTriangle (T.matrix i) T.origin,f x :=
  integral_eq_sum_affineTriangles T.body (T.compact hT) T.matrix (fun _ => T.origin)
    (T.cover hT) (T.pairwise_null hT) f hf

end D4.AreaEnvelope
