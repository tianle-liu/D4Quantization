import D4.C3CellDetData
import D4.C3CellBatches
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
private def c3GeometryVolumePart29Chunk0 : Poly := [([0,0,5,7], 64),([0,1,5,7], 32),([0,2,5,7], 32),([0,3,5,7], 32),([0,4,5,7], 32),([0,5,6,7], 32),([0,5,7,8], 32),([0,5,7,9], 32),([1,5,6,7], 16),([1,5,7,8], 16),([1,5,7,9], 16),([2,5,6,7], 16),([2,5,7,8], 16),([2,5,7,9], 16),([3,5,6,7], 16),([3,5,7,8], 16),([3,5,7,9], 16),([4,5,6,7], 16),([4,5,7,8], 16),([4,5,7,9], 16)]
def c3GeometryVolumePart29 : Poly := List.flatten [c3GeometryVolumePart29Chunk0]
theorem c3GeometryVolumePart29_check : sumFast (c3CellBatch29.map c3CellDetPoly) = c3GeometryVolumePart29 := by kernel_rfl
end D4.Secondary
