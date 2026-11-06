import D4.GramCubeCoordinates

/-! The actual nearest-lattice integral on a fundamental parallelepiped. -/
noncomputable section
open Matrix Module MeasureTheory Set
open scoped ENNReal
namespace D4.GramCoordinates

section Nearest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def nearest (L : Submodule ℤ E) (p : E) : ℝ :=
  sInf (Set.range (fun z : L => ‖p-(z:E)‖^2))

theorem nearest_periodic (L : Submodule ℤ E) (z : L) (p : E) :
    nearest L ((z:E)+p) = nearest L p := by
  unfold nearest
  congr 1
  ext t
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨w-z, ?_⟩
    change ‖p-((w:E)-(z:E))‖^2 = ‖(z:E)+p-(w:E)‖^2
    congr 2
    abel
  · rintro ⟨w,rfl⟩
    refine ⟨z+w, ?_⟩
    change ‖(z:E)+p-((z:E)+(w:E))‖^2 = ‖p-(w:E)‖^2
    congr 2
    abel

theorem nearest_on_voronoi (L : Submodule ℤ E) {p : E}
    (hp : p ∈ FacetGeometry.voronoi L) : nearest L p = ‖p‖^2 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨0, by simp⟩
  · rintro t ⟨z,rfl⟩
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hp z z.property)

theorem nearest_fundamental_integral (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {s : Set E}
    (hs : IsAddFundamentalDomain L s volume) :
    (∫ p in s, nearest L p) = ∫ p in FacetGeometry.voronoi L, ‖p‖^2 := by
  rw [hs.setIntegral_eq (f := nearest L) (FacetGeometry.voronoi_fundamental_lattice L)
    (fun z p => nearest_periodic L z p)]
  apply setIntegral_congr_fun (FacetGeometry.voronoi_closed L).measurableSet
  exact fun p hp => nearest_on_voronoi L hp

end Nearest

def cube (n : ℕ) : Set (Coord n) := Icc (0:Coord n) 1
def halfCube (n : ℕ) : Set (Coord n) := Set.pi Set.univ (fun _ => Ico (0:ℝ) 1)

def gramNearest {n : ℕ} (Q : Form n) (x : Coord n) : ℝ :=
  sInf (Set.range (fun z : Fin n → ℤ =>
    let v : Coord n := x-(fun i => (z i:ℝ))
    v ⬝ᵥ (Q *ᵥ v)))

theorem nearest_realize {n : ℕ} (B : Form n) (hB : B.det ≠ 0) (x : Coord n) :
    nearest (lattice B hB) (realize B x) = gramNearest (gram B) x := by
  unfold nearest gramNearest
  congr 1
  ext t
  constructor
  · rintro ⟨p,rfl⟩
    obtain ⟨z,hz⟩ := (show (p:Point n) ∈ Set.range
      (fun z : Fin n → ℤ => realize B (fun i => (z i:ℝ))) by
      rw [← lattice_eq_integer_image B hB]; exact p.property)
    refine ⟨z, ?_⟩
    change (x-(fun i => (z i:ℝ))) ⬝ᵥ
      (gram B *ᵥ (x-(fun i => (z i:ℝ)))) = ‖realize B x-(p:Point n)‖^2
    rw [← hz, ← realize_sub, norm_sq_realize]
  · rintro ⟨z,rfl⟩
    have hz : realize B (fun i => (z i:ℝ)) ∈ lattice B hB := by
      change realize B (fun i => (z i:ℝ)) ∈ (lattice B hB : Set (Point n))
      rw [lattice_eq_integer_image B hB]
      exact ⟨z,rfl⟩
    refine ⟨⟨_,hz⟩, ?_⟩
    change ‖realize B x-realize B (fun i => (z i:ℝ))‖^2 = _
    rw [← realize_sub, norm_sq_realize]

theorem fundamentalDomain_preimage {n : ℕ} (B : Form n) (hB : B.det ≠ 0) :
    realize B ⁻¹' ZSpan.fundamentalDomain (columnBasis B hB) = halfCube n := by
  ext x
  simp [ZSpan.fundamentalDomain, halfCube]

theorem fundamentalDomain_volume {n : ℕ} (B : Form n) (hB : B.det ≠ 0) :
    volume (ZSpan.fundamentalDomain (columnBasis B hB)) = ENNReal.ofReal |B.det| := by
  have h := congrArg (fun μ : Measure (Point n) =>
    μ (ZSpan.fundamentalDomain (columnBasis B hB))) (map_realize_volume B hB)
  change (Measure.map (realize B) volume) (ZSpan.fundamentalDomain (columnBasis B hB)) =
    (ENNReal.ofReal |B.det|⁻¹ • volume) (ZSpan.fundamentalDomain (columnBasis B hB)) at h
  have hm : Measurable (realize B) := (realizeEquiv B hB).continuous.measurable
  rw [Measure.map_apply hm
      (ZSpan.fundamentalDomain_measurableSet _), fundamentalDomain_preimage] at h
  have hc : volume (halfCube n) = 1 := by
    simp [halfCube, volume_pi, Measure.pi_pi]
  rw [hc, Measure.smul_apply, smul_eq_mul,
    ENNReal.ofReal_inv_of_pos (abs_pos.mpr hB)] at h
  have hd : (ENNReal.ofReal |B.det| : ℝ≥0∞) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr hB))
  calc
    _ = ENNReal.ofReal |B.det| *
      ((ENNReal.ofReal |B.det|)⁻¹ *
        volume (ZSpan.fundamentalDomain (columnBasis B hB))) :=
      (ENNReal.mul_inv_cancel_left hd ENNReal.ofReal_ne_top).symm
    _ = ENNReal.ofReal |B.det| := by rw [← h, mul_one]

theorem voronoi_volume {n : ℕ} (B : Form n) (hB : B.det ≠ 0) :
    volume (FacetGeometry.voronoi (lattice B hB)) = ENNReal.ofReal |B.det| := by
  rw [(FacetGeometry.voronoi_fundamental_lattice (lattice B hB)).measure_eq
    (ZSpan.isAddFundamentalDomain (columnBasis B hB) volume)]
  exact fundamentalDomain_volume B hB

theorem voronoi_moment {n : ℕ} (B : Form n) (hB : B.det ≠ 0) :
    (∫ p in FacetGeometry.voronoi (lattice B hB), ‖p‖^2) =
      |B.det| * ∫ x in cube n, gramNearest (gram B) x := by
  let e := (realizeEquiv B hB).toHomeomorph.toMeasurableEquiv
  have h := setIntegral_map_equiv (μ := (volume : Measure (Coord n))) e
    (nearest (lattice B hB)) (ZSpan.fundamentalDomain (columnBasis B hB))
  change (∫ p in ZSpan.fundamentalDomain (columnBasis B hB), nearest (lattice B hB) p
    ∂Measure.map (realize B) volume) =
    (∫ x in realize B ⁻¹' ZSpan.fundamentalDomain (columnBasis B hB),
      nearest (lattice B hB) (realize B x)) at h
  rw [map_realize_volume B hB, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), smul_eq_mul,
    fundamentalDomain_preimage] at h
  have hs : IsAddFundamentalDomain (lattice B hB)
      (ZSpan.fundamentalDomain (columnBasis B hB)) volume :=
    ZSpan.isAddFundamentalDomain (columnBasis B hB) volume
  rw [nearest_fundamental_integral (lattice B hB) hs] at h
  simp_rw [nearest_realize] at h
  have hc : (∫ x in halfCube n, gramNearest (gram B) x) =
      ∫ x in cube n, gramNearest (gram B) x :=
    setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc
  rw [hc] at h
  calc
    _ = |B.det| * (|B.det|⁻¹ *
      (∫ p in FacetGeometry.voronoi (lattice B hB), ‖p‖^2)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hB), one_mul]
    _ = _ := by rw [h]

end D4.GramCoordinates
