import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup29_det_check : c3TensorGroup29.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 43)) = true := by kernel_rfl
private def c3GroupHessian29_00Chunk0 : Poly := [([0,0], 64),([0,5], 64),([0,6], 64),([1,1], 80),([1,9], -160),([5,5], 24),([5,6], 16),([6,6], 24),([9,9], 80)]
def c3GroupHessian29_00 : Poly := List.flatten [c3GroupHessian29_00Chunk0]
theorem c3GroupHessian29_00_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian29_00 := by kernel_rfl
private def c3GroupHessian29_01Chunk0 : Poly := [([0,0], 24),([0,1], -80),([0,2], -8),([0,5], 12),([0,6], 12),([0,9], 80),([1,7], -80),([1,8], -80),([1,9], -80),([2,5], -4),([2,6], -4),([7,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian29_01 : Poly := List.flatten [c3GroupHessian29_01Chunk0]
theorem c3GroupHessian29_01_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian29_01 := by kernel_rfl
private def c3GroupHessian29_02Chunk0 : Poly := [([0,0], -32),([0,1], 80),([0,5], -56),([0,6], -8),([0,9], -80),([1,3], 80),([1,7], 80),([1,9], 80),([3,9], -80),([5,5], -24),([5,6], -8),([7,9], -80),([9,9], -80)]
def c3GroupHessian29_02 : Poly := List.flatten [c3GroupHessian29_02Chunk0]
theorem c3GroupHessian29_02_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian29_02 := by kernel_rfl
private def c3GroupHessian29_03Chunk0 : Poly := [([0,0], -32),([0,1], 80),([0,5], -8),([0,6], -56),([0,9], -80),([1,4], 80),([1,8], 80),([1,9], 80),([4,9], -80),([5,6], -8),([6,6], -24),([8,9], -80),([9,9], -80)]
def c3GroupHessian29_03 : Poly := List.flatten [c3GroupHessian29_03Chunk0]
theorem c3GroupHessian29_03_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian29_03 := by kernel_rfl
private def c3GroupHessian29_11Chunk0 : Poly := [([0,0], 96),([0,2], 16),([0,7], 160),([0,8], 160),([0,9], 160),([2,2], 32),([7,7], 80),([7,8], 160),([7,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian29_11 : Poly := List.flatten [c3GroupHessian29_11Chunk0]
theorem c3GroupHessian29_11_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian29_11 := by kernel_rfl
private def c3GroupHessian29_12Chunk0 : Poly := [([0,0], -92),([0,2], 4),([0,3], -80),([0,5], -12),([0,7], -160),([0,8], -80),([0,9], -160),([2,5], 4),([3,7], -80),([3,8], -80),([3,9], -80),([7,7], -80),([7,8], -80),([7,9], -160),([8,9], -80),([9,9], -80)]
def c3GroupHessian29_12 : Poly := List.flatten [c3GroupHessian29_12Chunk0]
theorem c3GroupHessian29_12_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian29_12 := by kernel_rfl
private def c3GroupHessian29_13Chunk0 : Poly := [([0,0], -92),([0,2], 4),([0,4], -80),([0,6], -12),([0,7], -80),([0,8], -160),([0,9], -160),([2,6], 4),([4,7], -80),([4,8], -80),([4,9], -80),([7,8], -80),([7,9], -80),([8,8], -80),([8,9], -160),([9,9], -80)]
def c3GroupHessian29_13 : Poly := List.flatten [c3GroupHessian29_13Chunk0]
theorem c3GroupHessian29_13_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian29_13 := by kernel_rfl
private def c3GroupHessian29_22Chunk0 : Poly := [([0,0], 104),([0,3], 160),([0,5], 48),([0,7], 160),([0,9], 160),([3,3], 80),([3,7], 160),([3,9], 160),([5,5], 24),([7,7], 80),([7,9], 160),([9,9], 80)]
def c3GroupHessian29_22 : Poly := List.flatten [c3GroupHessian29_22Chunk0]
theorem c3GroupHessian29_22_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian29_22 := by kernel_rfl
private def c3GroupHessian29_23Chunk0 : Poly := [([0,0], 88),([0,3], 80),([0,4], 80),([0,5], 8),([0,6], 8),([0,7], 80),([0,8], 80),([0,9], 160),([3,4], 80),([3,8], 80),([3,9], 80),([4,7], 80),([4,9], 80),([5,6], 8),([7,8], 80),([7,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian29_23 : Poly := List.flatten [c3GroupHessian29_23Chunk0]
theorem c3GroupHessian29_23_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian29_23 := by kernel_rfl
private def c3GroupHessian29_33Chunk0 : Poly := [([0,0], 104),([0,4], 160),([0,6], 48),([0,8], 160),([0,9], 160),([4,4], 80),([4,8], 160),([4,9], 160),([6,6], 24),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian29_33 : Poly := List.flatten [c3GroupHessian29_33Chunk0]
theorem c3GroupHessian29_33_check : sumFast (c3TensorGroup29.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian29_33 := by kernel_rfl
end D4.Secondary
