import D4.DelaunayExactData
namespace D4.Delaunay
open Matrix Analytic Secondary
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
 theorem exact_cells1_1_check : ([4, 5, 6, 7] : List (Fin 24)).all (fun s => decide
    (∀ b : Fin 4 → Bool,
      (∀ k, quadraticZ (generators1 k) (cubeSite (cellSigns1 s) b)=
        dotProduct (cubeSite (cellSigns1 s) b) ((principalNormals s) k)) →
      ∃ j : Fin 5, cubeSite (cellSigns1 s) b=cells1 s j))=true := by kernel_rfl
end D4.Delaunay
