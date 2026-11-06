import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup147_det_check : c3TensorGroup147.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 190)) = true := by kernel_rfl
private def c3GroupHessian147_00Chunk0 : Poly := [([0,0], 32),([0,1], 32),([0,5], 32),([0,9], 32),([1,1], 24),([1,5], -8),([1,9], 16),([5,5], 32),([5,9], -8),([6,6], 80),([9,9], 24)]
def c3GroupHessian147_00 : Poly := List.flatten [c3GroupHessian147_00Chunk0]
theorem c3GroupHessian147_00_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian147_00 := by kernel_rfl
private def c3GroupHessian147_01Chunk0 : Poly := [([0,0], 16),([0,1], 8),([0,5], -4),([0,6], -80),([0,8], 16),([0,9], 40),([1,8], 8),([1,9], 8),([2,6], -80),([5,8], -4),([5,9], -4),([6,7], -80),([8,9], 24),([9,9], 24)]
def c3GroupHessian147_01 : Poly := List.flatten [c3GroupHessian147_01Chunk0]
theorem c3GroupHessian147_01_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian147_01 := by kernel_rfl
private def c3GroupHessian147_02Chunk0 : Poly := [([0,0], -16),([0,1], 8),([0,3], 16),([0,5], -36),([0,6], 80),([0,9], -24),([1,3], 24),([1,5], 4),([1,9], -8),([3,5], -4),([3,9], 8),([5,5], -32),([5,9], 8),([6,7], 80),([9,9], -24)]
def c3GroupHessian147_02 : Poly := List.flatten [c3GroupHessian147_02Chunk0]
theorem c3GroupHessian147_02_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian147_02 := by kernel_rfl
private def c3GroupHessian147_03Chunk0 : Poly := [([0,0], -16),([0,1], -8),([0,5], 4),([0,6], -80),([0,8], -16),([0,9], -40),([1,8], -8),([1,9], -8),([4,6], -80),([5,8], 4),([5,9], 4),([6,6], -80),([8,9], -24),([9,9], -24)]
def c3GroupHessian147_03 : Poly := List.flatten [c3GroupHessian147_03Chunk0]
theorem c3GroupHessian147_03_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian147_03 := by kernel_rfl
private def c3GroupHessian147_11Chunk0 : Poly := [([0,0], 104),([0,2], 160),([0,7], 160),([0,8], 48),([0,9], 48),([2,2], 80),([2,7], 160),([7,7], 80),([8,8], 24),([8,9], 48),([9,9], 24)]
def c3GroupHessian147_11 : Poly := List.flatten [c3GroupHessian147_11Chunk0]
theorem c3GroupHessian147_11_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian147_11 := by kernel_rfl
private def c3GroupHessian147_12Chunk0 : Poly := [([0,0], -88),([0,2], -80),([0,3], 8),([0,5], 4),([0,7], -160),([0,8], -8),([0,9], -32),([2,7], -80),([3,8], 8),([3,9], 8),([5,8], 4),([5,9], 4),([7,7], -80),([8,9], -24),([9,9], -24)]
def c3GroupHessian147_12 : Poly := List.flatten [c3GroupHessian147_12Chunk0]
theorem c3GroupHessian147_12_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian147_12 := by kernel_rfl
private def c3GroupHessian147_13Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,4], 80),([0,6], 80),([0,7], 80),([0,8], -48),([0,9], -48),([2,4], 80),([2,6], 80),([4,7], 80),([6,7], 80),([8,8], -24),([8,9], -48),([9,9], -24)]
def c3GroupHessian147_13 : Poly := List.flatten [c3GroupHessian147_13Chunk0]
theorem c3GroupHessian147_13_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian147_13 := by kernel_rfl
private def c3GroupHessian147_22Chunk0 : Poly := [([0,0], 104),([0,3], 16),([0,5], 40),([0,7], 160),([0,9], 16),([3,3], 24),([3,5], 8),([3,9], -16),([5,5], 32),([5,9], -8),([7,7], 80),([9,9], 24)]
def c3GroupHessian147_22 : Poly := List.flatten [c3GroupHessian147_22Chunk0]
theorem c3GroupHessian147_22_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian147_22 := by kernel_rfl
private def c3GroupHessian147_23Chunk0 : Poly := [([0,0], -72),([0,3], -8),([0,4], -80),([0,5], -4),([0,6], -80),([0,7], -80),([0,8], 8),([0,9], 32),([3,8], -8),([3,9], -8),([4,7], -80),([5,8], -4),([5,9], -4),([6,7], -80),([8,9], 24),([9,9], 24)]
def c3GroupHessian147_23 : Poly := List.flatten [c3GroupHessian147_23Chunk0]
theorem c3GroupHessian147_23_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian147_23 := by kernel_rfl
private def c3GroupHessian147_33Chunk0 : Poly := [([0,0], 104),([0,4], 160),([0,6], 160),([0,8], 48),([0,9], 48),([4,4], 80),([4,6], 160),([6,6], 80),([8,8], 24),([8,9], 48),([9,9], 24)]
def c3GroupHessian147_33 : Poly := List.flatten [c3GroupHessian147_33Chunk0]
theorem c3GroupHessian147_33_check : sumFast (c3TensorGroup147.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian147_33 := by kernel_rfl
end D4.Secondary
