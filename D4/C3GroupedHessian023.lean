import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup23_det_check : c3TensorGroup23.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 26)) = true := by kernel_rfl
private def c3GroupHessian23_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], -8),([0,6], 64),([0,9], 64),([1,1], 80),([5,5], 24),([5,6], -8),([5,9], -8),([6,6], 32),([6,9], 64),([9,9], 32)]
def c3GroupHessian23_00 : Poly := List.flatten [c3GroupHessian23_00Chunk0]
theorem c3GroupHessian23_00_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian23_00 := by kernel_rfl
private def c3GroupHessian23_01Chunk0 : Poly := [([0,0], 112),([0,1], 80),([0,2], 80),([0,5], -4),([0,6], 32),([0,7], -4),([0,8], 32),([0,9], 64),([1,2], 80),([5,7], 8),([5,8], -4),([5,9], -4),([6,7], -4),([6,8], 32),([6,9], 32),([7,9], -4),([8,9], 32),([9,9], 32)]
def c3GroupHessian23_01 : Poly := List.flatten [c3GroupHessian23_01Chunk0]
theorem c3GroupHessian23_01_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian23_01 := by kernel_rfl
private def c3GroupHessian23_02Chunk0 : Poly := [([0,3], 80),([0,5], 4),([0,7], 4),([0,9], -32),([1,3], 80),([5,5], -24),([5,6], 4),([5,7], -8),([5,9], 8),([6,7], 4),([6,9], -32),([7,9], 4),([9,9], -32)]
def c3GroupHessian23_02 : Poly := List.flatten [c3GroupHessian23_02Chunk0]
theorem c3GroupHessian23_02_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian23_02 := by kernel_rfl
private def c3GroupHessian23_03Chunk0 : Poly := [([0,0], -64),([0,4], 80),([0,5], 8),([0,6], -96),([0,8], -32),([0,9], -96),([1,4], 80),([5,6], 4),([5,8], 4),([5,9], 4),([6,6], -32),([6,8], -32),([6,9], -64),([8,9], -32),([9,9], -32)]
def c3GroupHessian23_03 : Poly := List.flatten [c3GroupHessian23_03Chunk0]
theorem c3GroupHessian23_03_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian23_03 := by kernel_rfl
private def c3GroupHessian23_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], -8),([0,8], 64),([0,9], 64),([2,2], 80),([7,7], 24),([7,8], -8),([7,9], -8),([8,8], 32),([8,9], 64),([9,9], 32)]
def c3GroupHessian23_11 : Poly := List.flatten [c3GroupHessian23_11Chunk0]
theorem c3GroupHessian23_11_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian23_11 := by kernel_rfl
private def c3GroupHessian23_12Chunk0 : Poly := [([0,3], 80),([0,5], 4),([0,7], 4),([0,9], -32),([2,3], 80),([5,7], -8),([5,8], 4),([5,9], 4),([7,7], -24),([7,8], 4),([7,9], 8),([8,9], -32),([9,9], -32)]
def c3GroupHessian23_12 : Poly := List.flatten [c3GroupHessian23_12Chunk0]
theorem c3GroupHessian23_12_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian23_12 := by kernel_rfl
private def c3GroupHessian23_13Chunk0 : Poly := [([0,0], -64),([0,4], 80),([0,6], -32),([0,7], 8),([0,8], -96),([0,9], -96),([2,4], 80),([6,7], 4),([6,8], -32),([6,9], -32),([7,8], 4),([7,9], 4),([8,8], -32),([8,9], -64),([9,9], -32)]
def c3GroupHessian23_13 : Poly := List.flatten [c3GroupHessian23_13Chunk0]
theorem c3GroupHessian23_13_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian23_13 := by kernel_rfl
private def c3GroupHessian23_22Chunk0 : Poly := [([3,3], 80),([5,5], 24),([5,7], 16),([5,9], -8),([7,7], 24),([7,9], -8),([9,9], 32)]
def c3GroupHessian23_22 : Poly := List.flatten [c3GroupHessian23_22Chunk0]
theorem c3GroupHessian23_22_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian23_22 := by kernel_rfl
private def c3GroupHessian23_23Chunk0 : Poly := [([0,5], -8),([0,7], -8),([0,9], 64),([3,4], 80),([5,6], -4),([5,8], -4),([5,9], -4),([6,7], -4),([6,9], 32),([7,8], -4),([7,9], -4),([8,9], 32),([9,9], 32)]
def c3GroupHessian23_23 : Poly := List.flatten [c3GroupHessian23_23Chunk0]
theorem c3GroupHessian23_23_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian23_23 := by kernel_rfl
private def c3GroupHessian23_33Chunk0 : Poly := [([0,0], 128),([0,6], 128),([0,8], 128),([0,9], 128),([4,4], 80),([6,6], 32),([6,8], 64),([6,9], 64),([8,8], 32),([8,9], 64),([9,9], 32)]
def c3GroupHessian23_33 : Poly := List.flatten [c3GroupHessian23_33Chunk0]
theorem c3GroupHessian23_33_check : sumFast (c3TensorGroup23.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian23_33 := by kernel_rfl
end D4.Secondary
