import D4.DelaunaySupportData

import D4.DelaunayExactSupport

namespace D4.Delaunay

open Matrix Analytic Secondary

set_option maxHeartbeats 0

set_option maxRecDepth 1000000

def principalUnitIndex (i : Fin 4) : Fin 10 := ⟨i.val,by omega⟩

def secondaryUnitIndex (i : Fin 4) : Fin 10 := ⟨i.val+1,by omega⟩

def cellSigns1 (s : Fin 24) : IntVec := fun i => (principalNormals s) (principalUnitIndex i) i

theorem unit_generators1_check : ∀ (s : Fin 24) (i : Fin 4),
    generators1 (principalUnitIndex i)=rankOneZ (Pi.single i 1) ∧
    (principalNormals s) (principalUnitIndex i)=Pi.single i (cellSigns1 s i) := by decide +kernel

def cellSigns2 (s : Fin 24) : IntVec := fun i => (c2VertexCoefficients (cellVertexIndex2 s)) (secondaryUnitIndex i) i

theorem unit_generators2_check : ∀ (s : Fin 24) (i : Fin 4),
    generators2 (secondaryUnitIndex i)=rankOneZ (Pi.single i 1) ∧
    (c2VertexCoefficients (cellVertexIndex2 s)) (secondaryUnitIndex i)=Pi.single i (cellSigns2 s i) := by decide +kernel

def cellSigns3 (s : Fin 24) : IntVec := fun i => (c3VertexCoefficients (cellVertexIndex3 s)) (secondaryUnitIndex i) i

theorem unit_generators3_check : ∀ (s : Fin 24) (i : Fin 4),
    generators3 (secondaryUnitIndex i)=rankOneZ (Pi.single i 1) ∧
    (c3VertexCoefficients (cellVertexIndex3 s)) (secondaryUnitIndex i)=Pi.single i (cellSigns3 s i) := by decide +kernel

end D4.Delaunay
