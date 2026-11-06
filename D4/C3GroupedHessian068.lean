import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup68_det_check : c3TensorGroup68.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 91)) = true := by kernel_rfl
private def c3GroupHessian68_00Chunk0 : Poly := [([0,0], 104),([0,1], 160),([0,5], 160),([0,6], 48),([0,9], 48),([1,1], 80),([1,5], 160),([5,5], 80),([6,6], 24),([6,9], 48),([9,9], 24)]
def c3GroupHessian68_00 : Poly := List.flatten [c3GroupHessian68_00Chunk0]
theorem c3GroupHessian68_00_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian68_00 := by kernel_rfl
private def c3GroupHessian68_01Chunk0 : Poly := [([0,0], 16),([0,2], 8),([0,6], 16),([0,7], -4),([0,8], -80),([0,9], 40),([1,8], -80),([2,6], 8),([2,9], 8),([5,8], -80),([6,7], -4),([6,9], 24),([7,9], -4),([9,9], 24)]
def c3GroupHessian68_01 : Poly := List.flatten [c3GroupHessian68_01Chunk0]
theorem c3GroupHessian68_01_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian68_01 := by kernel_rfl
private def c3GroupHessian68_02Chunk0 : Poly := [([0,0], -88),([0,1], -80),([0,3], 8),([0,5], -160),([0,6], -8),([0,7], 4),([0,9], -32),([1,5], -80),([3,6], 8),([3,9], 8),([5,5], -80),([6,7], 4),([6,9], -24),([7,9], 4),([9,9], -24)]
def c3GroupHessian68_02 : Poly := List.flatten [c3GroupHessian68_02Chunk0]
theorem c3GroupHessian68_02_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian68_02 := by kernel_rfl
private def c3GroupHessian68_03Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,4], 80),([0,5], 80),([0,6], -48),([0,8], 80),([0,9], -48),([1,4], 80),([1,8], 80),([4,5], 80),([5,8], 80),([6,6], -24),([6,9], -48),([9,9], -24)]
def c3GroupHessian68_03 : Poly := List.flatten [c3GroupHessian68_03Chunk0]
theorem c3GroupHessian68_03_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian68_03 := by kernel_rfl
private def c3GroupHessian68_11Chunk0 : Poly := [([0,0], 32),([0,2], 32),([0,7], 32),([0,9], 32),([2,2], 24),([2,7], -8),([2,9], 16),([7,7], 32),([7,9], -8),([8,8], 80),([9,9], 24)]
def c3GroupHessian68_11 : Poly := List.flatten [c3GroupHessian68_11Chunk0]
theorem c3GroupHessian68_11_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian68_11 := by kernel_rfl
private def c3GroupHessian68_12Chunk0 : Poly := [([0,0], -16),([0,2], 8),([0,3], 16),([0,7], -36),([0,8], 80),([0,9], -24),([2,3], 24),([2,7], 4),([2,9], -8),([3,7], -4),([3,9], 8),([5,8], 80),([7,7], -32),([7,9], 8),([9,9], -24)]
def c3GroupHessian68_12 : Poly := List.flatten [c3GroupHessian68_12Chunk0]
theorem c3GroupHessian68_12_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian68_12 := by kernel_rfl
private def c3GroupHessian68_13Chunk0 : Poly := [([0,0], -16),([0,2], -8),([0,6], -16),([0,7], 4),([0,8], -80),([0,9], -40),([2,6], -8),([2,9], -8),([4,8], -80),([6,7], 4),([6,9], -24),([7,9], 4),([8,8], -80),([9,9], -24)]
def c3GroupHessian68_13 : Poly := List.flatten [c3GroupHessian68_13Chunk0]
theorem c3GroupHessian68_13_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian68_13 := by kernel_rfl
private def c3GroupHessian68_22Chunk0 : Poly := [([0,0], 104),([0,3], 16),([0,5], 160),([0,7], 40),([0,9], 16),([3,3], 24),([3,7], 8),([3,9], -16),([5,5], 80),([7,7], 32),([7,9], -8),([9,9], 24)]
def c3GroupHessian68_22 : Poly := List.flatten [c3GroupHessian68_22Chunk0]
theorem c3GroupHessian68_22_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian68_22 := by kernel_rfl
private def c3GroupHessian68_23Chunk0 : Poly := [([0,0], -72),([0,3], -8),([0,4], -80),([0,5], -80),([0,6], 8),([0,7], -4),([0,8], -80),([0,9], 32),([3,6], -8),([3,9], -8),([4,5], -80),([5,8], -80),([6,7], -4),([6,9], 24),([7,9], -4),([9,9], 24)]
def c3GroupHessian68_23 : Poly := List.flatten [c3GroupHessian68_23Chunk0]
theorem c3GroupHessian68_23_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian68_23 := by kernel_rfl
private def c3GroupHessian68_33Chunk0 : Poly := [([0,0], 104),([0,4], 160),([0,6], 48),([0,8], 160),([0,9], 48),([4,4], 80),([4,8], 160),([6,6], 24),([6,9], 48),([8,8], 80),([9,9], 24)]
def c3GroupHessian68_33 : Poly := List.flatten [c3GroupHessian68_33Chunk0]
theorem c3GroupHessian68_33_check : sumFast (c3TensorGroup68.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian68_33 := by kernel_rfl
end D4.Secondary
