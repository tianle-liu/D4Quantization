import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup66_det_check : c3TensorGroup66.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 89)) = true := by kernel_rfl
private def c3GroupHessian66_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 32),([0,9], 32),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16),([6,9], 32),([9,9], 16)]
def c3GroupHessian66_00 : Poly := List.flatten [c3GroupHessian66_00Chunk0]
theorem c3GroupHessian66_00_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian66_00 := by kernel_rfl
private def c3GroupHessian66_01Chunk0 : Poly := [([0,0], -4),([0,2], -8),([0,6], -4),([0,7], -20),([0,8], -40),([0,9], 12),([1,8], -40),([2,6], -8),([2,9], -8),([5,8], -40),([6,7], -20),([6,9], 16),([7,9], -20),([9,9], 16)]
def c3GroupHessian66_01 : Poly := List.flatten [c3GroupHessian66_01Chunk0]
theorem c3GroupHessian66_01_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian66_01 := by kernel_rfl
private def c3GroupHessian66_02Chunk0 : Poly := [([0,0], -32),([0,1], -40),([0,3], 4),([0,5], -80),([0,6], 8),([0,7], 20),([0,9], -8),([1,5], -40),([3,6], 4),([3,9], 4),([5,5], -40),([6,7], 20),([6,9], -16),([7,9], 20),([9,9], -16)]
def c3GroupHessian66_02 : Poly := List.flatten [c3GroupHessian66_02Chunk0]
theorem c3GroupHessian66_02_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian66_02 := by kernel_rfl
private def c3GroupHessian66_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -32),([0,8], 40),([0,9], -32),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -16),([6,9], -32),([9,9], -16)]
def c3GroupHessian66_03 : Poly := List.flatten [c3GroupHessian66_03Chunk0]
theorem c3GroupHessian66_03_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian66_03 := by kernel_rfl
private def c3GroupHessian66_11Chunk0 : Poly := [([0,0], 16),([0,2], 24),([0,7], 40),([0,9], -8),([2,2], 16),([2,7], 40),([2,9], -16),([7,7], 40),([7,9], -40),([8,8], 40),([9,9], 16)]
def c3GroupHessian66_11 : Poly := List.flatten [c3GroupHessian66_11Chunk0]
theorem c3GroupHessian66_11_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian66_11 := by kernel_rfl
private def c3GroupHessian66_12Chunk0 : Poly := [([0,0], -12),([0,2], -8),([0,3], 4),([0,7], -40),([0,8], 40),([0,9], 12),([2,3], 4),([2,7], -20),([2,9], 8),([3,9], 4),([5,8], 40),([7,7], -40),([7,9], 40),([9,9], -16)]
def c3GroupHessian66_12 : Poly := List.flatten [c3GroupHessian66_12Chunk0]
theorem c3GroupHessian66_12_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian66_12 := by kernel_rfl
private def c3GroupHessian66_13Chunk0 : Poly := [([0,0], 4),([0,2], 8),([0,6], 4),([0,7], 20),([0,8], -40),([0,9], -12),([2,6], 8),([2,9], 8),([4,8], -40),([6,7], 20),([6,9], -16),([7,9], 20),([8,8], -40),([9,9], -16)]
def c3GroupHessian66_13 : Poly := List.flatten [c3GroupHessian66_13Chunk0]
theorem c3GroupHessian66_13_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian66_13 := by kernel_rfl
private def c3GroupHessian66_22Chunk0 : Poly := [([0,0], 56),([0,3], 8),([0,5], 80),([0,7], 40),([0,9], -16),([3,3], 8),([3,9], -8),([5,5], 40),([7,7], 40),([7,9], -40),([9,9], 16)]
def c3GroupHessian66_22 : Poly := List.flatten [c3GroupHessian66_22Chunk0]
theorem c3GroupHessian66_22_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian66_22 := by kernel_rfl
private def c3GroupHessian66_23Chunk0 : Poly := [([0,0], -48),([0,3], -4),([0,4], -40),([0,5], -40),([0,6], -8),([0,7], -20),([0,8], -40),([0,9], 8),([3,6], -4),([3,9], -4),([4,5], -40),([5,8], -40),([6,7], -20),([6,9], 16),([7,9], -20),([9,9], 16)]
def c3GroupHessian66_23 : Poly := List.flatten [c3GroupHessian66_23Chunk0]
theorem c3GroupHessian66_23_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian66_23 := by kernel_rfl
private def c3GroupHessian66_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 32),([0,8], 80),([0,9], 32),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], 32),([8,8], 40),([9,9], 16)]
def c3GroupHessian66_33 : Poly := List.flatten [c3GroupHessian66_33Chunk0]
theorem c3GroupHessian66_33_check : sumFast (c3TensorGroup66.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian66_33 := by kernel_rfl
end D4.Secondary
