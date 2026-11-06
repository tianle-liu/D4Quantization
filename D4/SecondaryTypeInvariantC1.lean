import D4.SecondaryTypeInvariantFinite
import D4.DelaunayData

namespace D4.Delaunay
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

theorem cells1_finiteValenceCount_24 : finiteValenceCount cells1 24 = 10 := by
  kernel_rfl

theorem cells1_valenceCount_24 : valenceCount (periodicVertexFamily cells1) 24 = 10 := by
  rw [valenceCount_eq_finiteValenceCount cells1 24 (by decide), cells1_finiteValenceCount_24]

end D4.Delaunay
