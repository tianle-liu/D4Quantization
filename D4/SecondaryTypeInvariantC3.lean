import D4.SecondaryTypeInvariantFinite
import D4.DelaunayData

namespace D4.Delaunay
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

theorem cells3_finiteValenceCount_24 : finiteValenceCount cells3 24 = 0 := by
  kernel_rfl

theorem cells3_valenceCount_24 : valenceCount (periodicVertexFamily cells3) 24 = 0 := by
  rw [valenceCount_eq_finiteValenceCount cells3 24 (by decide), cells3_finiteValenceCount_24]

end D4.Delaunay
