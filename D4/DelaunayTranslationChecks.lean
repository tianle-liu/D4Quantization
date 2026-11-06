import D4.DelaunayData

import D4.DelaunayTranslations

namespace D4.Delaunay

set_option maxHeartbeats 0

set_option maxRecDepth 1000000

theorem cells1_zero : ∀ s, cells1 s 0=0 := by decide +kernel

theorem cells1_height : ∀ (s : Fin 24) (i : Fin 5),
    0 ≤ height (cells1 s i) ∧ (height (cells1 s i)=0 → cells1 s i=0) := by decide +kernel

theorem cells1_distinct : Function.Injective (fun s => simplexVertices (cells1 s)) := by decide +kernel

theorem cells1_translation_unique (s t : Fin 24) (n : D4.Analytic.IntVec)
    (h : (simplexVertices (cells1 s)).image (fun z => z+n)=simplexVertices (cells1 t)) :
    s=t ∧ n=0 := no_translation_repetitions cells1 cells1_zero cells1_height cells1_distinct s t n h

theorem cells2_zero : ∀ s, cells2 s 0=0 := by decide +kernel

theorem cells2_height : ∀ (s : Fin 24) (i : Fin 5),
    0 ≤ height (cells2 s i) ∧ (height (cells2 s i)=0 → cells2 s i=0) := by decide +kernel

theorem cells2_distinct : Function.Injective (fun s => simplexVertices (cells2 s)) := by decide +kernel

theorem cells2_translation_unique (s t : Fin 24) (n : D4.Analytic.IntVec)
    (h : (simplexVertices (cells2 s)).image (fun z => z+n)=simplexVertices (cells2 t)) :
    s=t ∧ n=0 := no_translation_repetitions cells2 cells2_zero cells2_height cells2_distinct s t n h

theorem cells3_zero : ∀ s, cells3 s 0=0 := by decide +kernel

theorem cells3_height : ∀ (s : Fin 24) (i : Fin 5),
    0 ≤ height (cells3 s i) ∧ (height (cells3 s i)=0 → cells3 s i=0) := by decide +kernel

theorem cells3_distinct : Function.Injective (fun s => simplexVertices (cells3 s)) := by decide +kernel

theorem cells3_translation_unique (s t : Fin 24) (n : D4.Analytic.IntVec)
    (h : (simplexVertices (cells3 s)).image (fun z => z+n)=simplexVertices (cells3 t)) :
    s=t ∧ n=0 := no_translation_repetitions cells3 cells3_zero cells3_height cells3_distinct s t n h

end D4.Delaunay
