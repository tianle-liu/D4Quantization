import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup110_det_check : c3TensorGroup110.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 144)) = true := by kernel_rfl
private def c3GroupHessian110_00Chunk0 : Poly := [([0,0], 96),([0,1], 16),([0,5], 160),([0,6], 160),([0,9], 160),([1,1], 32),([5,5], 80),([5,6], 160),([5,9], 160),([6,6], 80),([6,9], 160),([9,9], 80)]
def c3GroupHessian110_00 : Poly := List.flatten [c3GroupHessian110_00Chunk0]
theorem c3GroupHessian110_00_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian110_00 := by kernel_rfl
private def c3GroupHessian110_01Chunk0 : Poly := [([0,0], 24),([0,1], -8),([0,2], -80),([0,7], 12),([0,8], 12),([0,9], 80),([1,7], -4),([1,8], -4),([2,5], -80),([2,6], -80),([2,9], -80),([5,9], 80),([6,9], 80),([9,9], 80)]
def c3GroupHessian110_01 : Poly := List.flatten [c3GroupHessian110_01Chunk0]
theorem c3GroupHessian110_01_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian110_01 := by kernel_rfl
private def c3GroupHessian110_02Chunk0 : Poly := [([0,0], -92),([0,1], 4),([0,3], -80),([0,5], -160),([0,6], -80),([0,7], -12),([0,9], -160),([1,7], 4),([3,5], -80),([3,6], -80),([3,9], -80),([5,5], -80),([5,6], -80),([5,9], -160),([6,9], -80),([9,9], -80)]
def c3GroupHessian110_02 : Poly := List.flatten [c3GroupHessian110_02Chunk0]
theorem c3GroupHessian110_02_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian110_02 := by kernel_rfl
private def c3GroupHessian110_03Chunk0 : Poly := [([0,0], -92),([0,1], 4),([0,4], -80),([0,5], -80),([0,6], -160),([0,8], -12),([0,9], -160),([1,8], 4),([4,5], -80),([4,6], -80),([4,9], -80),([5,6], -80),([5,9], -80),([6,6], -80),([6,9], -160),([9,9], -80)]
def c3GroupHessian110_03 : Poly := List.flatten [c3GroupHessian110_03Chunk0]
theorem c3GroupHessian110_03_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian110_03 := by kernel_rfl
private def c3GroupHessian110_11Chunk0 : Poly := [([0,0], 64),([0,7], 64),([0,8], 64),([2,2], 80),([2,9], -160),([7,7], 24),([7,8], 16),([8,8], 24),([9,9], 80)]
def c3GroupHessian110_11 : Poly := List.flatten [c3GroupHessian110_11Chunk0]
theorem c3GroupHessian110_11_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian110_11 := by kernel_rfl
private def c3GroupHessian110_12Chunk0 : Poly := [([0,0], -32),([0,2], 80),([0,7], -56),([0,8], -8),([0,9], -80),([2,3], 80),([2,5], 80),([2,9], 80),([3,9], -80),([5,9], -80),([7,7], -24),([7,8], -8),([9,9], -80)]
def c3GroupHessian110_12 : Poly := List.flatten [c3GroupHessian110_12Chunk0]
theorem c3GroupHessian110_12_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian110_12 := by kernel_rfl
private def c3GroupHessian110_13Chunk0 : Poly := [([0,0], -32),([0,2], 80),([0,7], -8),([0,8], -56),([0,9], -80),([2,4], 80),([2,6], 80),([2,9], 80),([4,9], -80),([6,9], -80),([7,8], -8),([8,8], -24),([9,9], -80)]
def c3GroupHessian110_13 : Poly := List.flatten [c3GroupHessian110_13Chunk0]
theorem c3GroupHessian110_13_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian110_13 := by kernel_rfl
private def c3GroupHessian110_22Chunk0 : Poly := [([0,0], 104),([0,3], 160),([0,5], 160),([0,7], 48),([0,9], 160),([3,3], 80),([3,5], 160),([3,9], 160),([5,5], 80),([5,9], 160),([7,7], 24),([9,9], 80)]
def c3GroupHessian110_22 : Poly := List.flatten [c3GroupHessian110_22Chunk0]
theorem c3GroupHessian110_22_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian110_22 := by kernel_rfl
private def c3GroupHessian110_23Chunk0 : Poly := [([0,0], 88),([0,3], 80),([0,4], 80),([0,5], 80),([0,6], 80),([0,7], 8),([0,8], 8),([0,9], 160),([3,4], 80),([3,6], 80),([3,9], 80),([4,5], 80),([4,9], 80),([5,6], 80),([5,9], 80),([6,9], 80),([7,8], 8),([9,9], 80)]
def c3GroupHessian110_23 : Poly := List.flatten [c3GroupHessian110_23Chunk0]
theorem c3GroupHessian110_23_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian110_23 := by kernel_rfl
private def c3GroupHessian110_33Chunk0 : Poly := [([0,0], 104),([0,4], 160),([0,6], 160),([0,8], 48),([0,9], 160),([4,4], 80),([4,6], 160),([4,9], 160),([6,6], 80),([6,9], 160),([8,8], 24),([9,9], 80)]
def c3GroupHessian110_33 : Poly := List.flatten [c3GroupHessian110_33Chunk0]
theorem c3GroupHessian110_33_check : sumFast (c3TensorGroup110.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian110_33 := by kernel_rfl
end D4.Secondary
