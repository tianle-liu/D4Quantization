import D4.GramCubeIntegral

/-! The infimum in the Gram-cube formula is a genuine attained minimum. -/
noncomputable section
open Matrix Set
namespace D4.GramCoordinates

theorem gramNearest_le {n : ℕ} (B : Form n) (x : Coord n) (z : Fin n → ℤ) :
    gramNearest (gram B) x ≤
      (x-(fun i => (z i:ℝ))) ⬝ᵥ (gram B *ᵥ (x-(fun i => (z i:ℝ)))) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨w,rfl⟩
    change 0 ≤ (x-(fun i => (w i:ℝ))) ⬝ᵥ (gram B *ᵥ (x-(fun i => (w i:ℝ))))
    rw [← norm_sq_realize]
    positivity
  · exact ⟨z,rfl⟩

theorem gramNearest_attained {n : ℕ} (B : Form n) (hB : B.det ≠ 0) (x : Coord n) :
    ∃ z : Fin n → ℤ, gramNearest (gram B) x =
      (x-(fun i => (z i:ℝ))) ⬝ᵥ (gram B *ᵥ (x-(fun i => (z i:ℝ)))) := by
  obtain ⟨p,hp⟩ := FacetGeometry.nearest_lattice_exists (lattice B hB) (realize B x)
  obtain ⟨z,hz⟩ := (show (p:Point n) ∈ Set.range
    (fun z : Fin n → ℤ => realize B (fun i => (z i:ℝ))) by
    rw [← lattice_eq_integer_image B hB]; exact p.property)
  refine ⟨z, ?_⟩
  rw [← nearest_realize B hB x]
  have hh : nearest (lattice B hB) (realize B x) =
      nearest (lattice B hB) (realize B x-(p:Point n)) := by
    have h := nearest_periodic (lattice B hB) p (realize B x-(p:Point n))
    rw [show (p:Point n)+(realize B x-(p:Point n)) = realize B x by abel] at h
    exact h
  rw [hh, nearest_on_voronoi (lattice B hB) hp, ← hz, ← realize_sub, norm_sq_realize]

end D4.GramCoordinates
