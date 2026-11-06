import D4.ConeAnalysisGeometry
import D4.ConeAnalysisScaling
import D4.ConeAnalysisHexagon

/-! The unit-diagonal cone is a positive homothetic copy of the actual
height-one cone. Its volume-normalized moment is exactly the paper's g. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Pointwise

 def heightCircularCone {E : Type*} [NormedAddCommGroup E] (h r : ℝ) : Set (E × ℝ) :=
  {p | p.2∈Ioo (0:ℝ) h ∧ ‖p.1‖<p.2*r}

 def unitDiagonalHeight (r : ℝ) : ℝ := (Real.sqrt (1+r^2))⁻¹

 def unitDiagonalCone {E : Type*} [NormedAddCommGroup E] (r : ℝ) : Set (E × ℝ) :=
  heightCircularCone (unitDiagonalHeight r) r

 theorem unitDiagonalHeight_pos (r : ℝ) : 0<unitDiagonalHeight r := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

 theorem unitDiagonalHeight_eq_rpow (r : ℝ) :
    unitDiagonalHeight r=(1+r^2)^(-(1:ℝ)/2) := by
  rw [unitDiagonalHeight,Real.sqrt_eq_rpow,show -(1:ℝ)/2=-(1/2) by ring,
    Real.rpow_neg (by positivity)]

 theorem unitDiagonalHeight_diagonal (r : ℝ) :
    (unitDiagonalHeight r*r)^2+(unitDiagonalHeight r)^2=1 := by
  have hs := Real.sq_sqrt (show 0≤1+r^2 by positivity)
  have hn : Real.sqrt (1+r^2)≠0 := (Real.sqrt_pos.mpr (by positivity : 0<1+r^2)).ne'
  unfold unitDiagonalHeight
  field_simp
  nlinarith

 theorem unitDiagonalHeight_lt_one (r : ℝ) (hr : 0<r) : unitDiagonalHeight r<1 := by
  have hh := unitDiagonalHeight_pos r
  have hd := unitDiagonalHeight_diagonal r
  have hp := sq_pos_of_pos (mul_pos hh hr)
  nlinarith

 theorem unitDiagonal_base_radius (r : ℝ) (hr : 0≤r) :
    Real.sqrt (1-(unitDiagonalHeight r)^2)=unitDiagonalHeight r*r := by
  have hd := unitDiagonalHeight_diagonal r
  have hnon : 0≤1-(unitDiagonalHeight r)^2 := by nlinarith [sq_nonneg (unitDiagonalHeight r*r)]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (unitDiagonalHeight_pos r).le hr)).mp
  rw [Real.sq_sqrt hnon]
  linarith

 theorem heightCircularCone_eq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r h : ℝ) (hh : 0<h) : heightCircularCone (E:=E) h r=h • circularCone r := by
  ext p
  rw [mem_smul_set_iff_inv_smul_mem₀ hh.ne']
  change (0<p.2 ∧ p.2<h) ∧ ‖p.1‖<p.2*r ↔
    (0<h⁻¹*p.2 ∧ h⁻¹*p.2<1) ∧ ‖h⁻¹ • p.1‖<(h⁻¹*p.2)*r
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),mul_assoc,
    mul_lt_mul_left (inv_pos.mpr hh),mul_pos_iff_of_pos_left (inv_pos.mpr hh)]
  have he : h⁻¹*p.2<1 ↔ p.2<h := by
    rw [inv_mul_lt_iff₀ hh,mul_one]
  rw [he]

 theorem unitDiagonalCone_eq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) : unitDiagonalCone (E:=E) r=unitDiagonalHeight r • circularCone r :=
  heightCircularCone_eq_smul r _ (unitDiagonalHeight_pos r)

 theorem unitDiagonal_base_norm_sq {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (y : E) (hy : ‖y‖=unitDiagonalHeight r*r) :
    ‖y‖^2+(unitDiagonalHeight r)^2=1 := by
  rw [hy]
  exact unitDiagonalHeight_diagonal r

 theorem unitDiagonal_base_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) (y : E) (hy : ‖y‖=unitDiagonalHeight r*r) :
    ‖(WithLp.equiv 2 (E × ℝ)).symm (y,unitDiagonalHeight r)‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simpa only [Real.norm_eq_abs,sq_abs,one_pow] using unitDiagonal_base_norm_sq r y hy

 theorem coordinateSecondMoment_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (S : Set (E × ℝ)) (c : ℝ) (hc : 0<c) :
    (∫ p in c • S,(‖p.1‖^2+p.2^2) ∂μ.prod volume)=
      c^(Module.finrank ℝ E+3)*(∫ p in S,(‖p.1‖^2+p.2^2) ∂μ.prod volume) := by
  have H := setIntegral_comp_smul_of_pos (μ.prod volume)
    (fun p : E × ℝ => ‖p.1‖^2+p.2^2) S hc
  simp only [Prod.smul_fst,Prod.smul_snd,norm_smul,Real.norm_eq_abs,
    abs_of_pos hc,smul_eq_mul,mul_pow,← mul_add,integral_const_mul] at H
  have H' := congrArg (fun a : ℝ => c^(Module.finrank ℝ (E × ℝ))*a) H
  dsimp only at H'
  rw [← mul_assoc (c^(Module.finrank ℝ (E × ℝ))) ((c^(Module.finrank ℝ (E × ℝ)))⁻¹),
    mul_inv_cancel₀ (pow_ne_zero _ hc.ne'),one_mul] at H'
  rw [← H',← mul_assoc,← pow_add]
  congr 1
  simp only [Module.finrank_prod,Module.finrank_self]

 theorem normalizedMoment_scale (d v j c : ℝ) (hd : d≠0) (hv : 0≤v) (hc : 0<c) :
    ConePerspective.normalizedMoment d (c^d*v) (c^(d+2)*j)=
      ConePerspective.normalizedMoment d v j := by
  unfold ConePerspective.normalizedMoment
  have he : d*(1+2/d)=d+2 := by field_simp
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hc d).le hv,← Real.rpow_mul hc.le,he]
  have hn := (Real.rpow_pos_of_pos hc (d+2)).ne'
  convert mul_div_mul_left j (d*v^(1+2/d)) hn using 1 <;> congr 1 <;> ring

 theorem unitDiagonalCone_volume {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (r : ℝ) (hr : 0≤r) :
    (μ.prod volume).real (unitDiagonalCone (E:=E) r)=
      unitDiagonalHeight r^(Module.finrank ℝ E+1)*
        coneVolume (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)) r := by
  rw [unitDiagonalCone_eq_smul,real_measure_smul _ _ _ (unitDiagonalHeight_pos r).le,
    circularCone_volume_eq_formula μ r hr]
  simp only [Module.finrank_prod,Module.finrank_self]

 theorem unitDiagonalCone_secondMoment {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (r : ℝ) (hr : 0≤r) :
    (∫ p in unitDiagonalCone r,(‖p.1‖^2+p.2^2) ∂μ.prod volume)=
      unitDiagonalHeight r^(Module.finrank ℝ E+3)*
        coneMoment (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)) r := by
  rw [unitDiagonalCone_eq_smul,coordinateSecondMoment_smul μ _ _ (unitDiagonalHeight_pos r),
    circularCone_secondMoment_eq_formula μ r hr]

 theorem unitDiagonalCone_normalizedMoment {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (r : ℝ) (hr : 0<r) :
    ConePerspective.normalizedMoment (Module.finrank ℝ E+1)
      ((μ.prod volume).real (unitDiagonalCone (E:=E) r))
      (∫ p in unitDiagonalCone r,(‖p.1‖^2+p.2^2) ∂μ.prod volume)=
    coneNormalizedMoment (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1))
      (radiusAngle (Module.finrank ℝ E+1)
        ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1)) r) := by
  have hd : 2≤Module.finrank ℝ E+1 := by have := Module.finrank_pos (R:=ℝ) (M:=E); omega
  rw [unitDiagonalCone_volume μ r hr.le,unitDiagonalCone_secondMoment μ r hr.le]
  have hn := normalizedMoment_scale (Module.finrank ℝ E+1)
    (coneVolume (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)) r)
    (coneMoment (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)) r)
    (unitDiagonalHeight r) (by positivity)
    (coneVolume_pos _ _ _ (by exact_mod_cast hd) (unitBall_measure_pos μ) hr).le
    (unitDiagonalHeight_pos r)
  have he : ((Module.finrank ℝ E:ℝ)+1)+2=(Module.finrank ℝ E+3:ℕ) := by push_cast; ring
  have he1 : (Module.finrank ℝ E:ℝ)+1=(Module.finrank ℝ E+1:ℕ) := by push_cast; ring
  rw [he,he1,Real.rpow_natCast,Real.rpow_natCast] at hn
  have hg := coneNormalizedMoment_at_radius (Module.finrank ℝ E+1) hd
    (μ.real (ball (0:E) 1)) r (unitBall_measure_pos μ) hr
  simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hn hg
  exact hn.trans hg.symm

/-- The volume-normalized second moment without the factor `1/d`, called
`ξ` in the source's comparison with the unit-diagonal convention. -/
def unitDiagonalXi {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (r : ℝ) : ℝ :=
  (∫ p in unitDiagonalCone r,(‖p.1‖^2+p.2^2) ∂μ.prod volume) /
    (μ.prod volume).real (unitDiagonalCone (E:=E) r) ^
      (1+2/((Module.finrank ℝ E:ℝ)+1))

theorem unitDiagonalXi_eq_dim_mul_g {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (r : ℝ) (hr : 0<r) :
    unitDiagonalXi μ r=((Module.finrank ℝ E:ℝ)+1)*
      coneNormalizedMoment (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1))
        (radiusAngle (Module.finrank ℝ E+1)
          ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1)) r) := by
  rw [← unitDiagonalCone_normalizedMoment μ r hr]
  unfold unitDiagonalXi ConePerspective.normalizedMoment
  have hd : (Module.finrank ℝ E:ℝ)+1≠0 := by positivity
  rw [← mul_div_assoc,mul_div_mul_left _ _ hd]

theorem unitDiagonalXi_facet_bound_convention {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (r f : ℝ) (hr : 0<r) (hf : 0<f) :
    unitDiagonalXi μ r / (((Module.finrank ℝ E:ℝ)+1)*f^(2/((Module.finrank ℝ E:ℝ)+1)))=
      f^(-2/((Module.finrank ℝ E:ℝ)+1))*
        coneNormalizedMoment (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1))
          (radiusAngle (Module.finrank ℝ E+1)
            ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1)) r) := by
  have hd : (Module.finrank ℝ E:ℝ)+1≠0 := by positivity
  rw [unitDiagonalXi_eq_dim_mul_g μ r hr,mul_div_mul_left _ _ hd,
    show -2/((Module.finrank ℝ E:ℝ)+1)=-(2/((Module.finrank ℝ E:ℝ)+1)) by ring,
    Real.rpow_neg hf.le]
  simp only [div_eq_mul_inv,mul_comm]

end D4.ConeAnalysis
