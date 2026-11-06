import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup100_det_check : c3TensorGroup100.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 131)) = true := by kernel_rfl
private def c3GroupHessian100_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 80),([0,9], 8),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40),([9,9], 16)]
def c3GroupHessian100_00 : Poly := List.flatten [c3GroupHessian100_00Chunk0]
theorem c3GroupHessian100_00_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian100_00 := by kernel_rfl
private def c3GroupHessian100_01Chunk0 : Poly := [([0,0], -32),([0,1], -40),([0,2], -40),([0,5], -40),([0,6], -40),([0,7], -40),([0,8], -40),([0,9], 8),([1,2], -40),([1,7], -40),([1,8], -40),([2,5], -40),([2,6], -40),([5,7], -40),([5,8], -40),([6,7], -40),([6,8], -40),([9,9], 16)]
def c3GroupHessian100_01 : Poly := List.flatten [c3GroupHessian100_01Chunk0]
theorem c3GroupHessian100_01_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian100_01 := by kernel_rfl
private def c3GroupHessian100_02Chunk0 : Poly := [([0,0], -4),([0,5], -40),([0,7], 40),([0,9], -16),([1,5], -40),([1,7], 40),([3,9], -20),([5,5], -40),([5,6], -40),([5,7], 40),([6,7], 40),([9,9], -16)]
def c3GroupHessian100_02 : Poly := List.flatten [c3GroupHessian100_02Chunk0]
theorem c3GroupHessian100_02_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian100_02 := by kernel_rfl
private def c3GroupHessian100_03Chunk0 : Poly := [([0,0], -4),([0,6], -40),([0,8], 40),([0,9], -16),([1,6], -40),([1,8], 40),([4,9], -20),([5,6], -40),([5,8], 40),([6,6], -40),([6,8], 40),([9,9], -16)]
def c3GroupHessian100_03 : Poly := List.flatten [c3GroupHessian100_03Chunk0]
theorem c3GroupHessian100_03_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian100_03 := by kernel_rfl
private def c3GroupHessian100_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,8], 80),([0,9], 8),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40),([9,9], 16)]
def c3GroupHessian100_11 : Poly := List.flatten [c3GroupHessian100_11Chunk0]
theorem c3GroupHessian100_11_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian100_11 := by kernel_rfl
private def c3GroupHessian100_12Chunk0 : Poly := [([0,0], -4),([0,5], 40),([0,7], -40),([0,9], -16),([2,5], 40),([2,7], -40),([3,9], -20),([5,7], 40),([5,8], 40),([7,7], -40),([7,8], -40),([9,9], -16)]
def c3GroupHessian100_12 : Poly := List.flatten [c3GroupHessian100_12Chunk0]
theorem c3GroupHessian100_12_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian100_12 := by kernel_rfl
private def c3GroupHessian100_13Chunk0 : Poly := [([0,0], -4),([0,6], 40),([0,8], -40),([0,9], -16),([2,6], 40),([2,8], -40),([4,9], -20),([6,7], 40),([6,8], 40),([7,8], -40),([8,8], -40),([9,9], -16)]
def c3GroupHessian100_13 : Poly := List.flatten [c3GroupHessian100_13Chunk0]
theorem c3GroupHessian100_13_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian100_13 := by kernel_rfl
private def c3GroupHessian100_22Chunk0 : Poly := [([0,0], 16),([0,3], 40),([0,9], 24),([3,3], 40),([3,9], 40),([5,5], 40),([5,7], -80),([7,7], 40),([9,9], 16)]
def c3GroupHessian100_22 : Poly := List.flatten [c3GroupHessian100_22Chunk0]
theorem c3GroupHessian100_22_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian100_22 := by kernel_rfl
private def c3GroupHessian100_23Chunk0 : Poly := [([0,0], 8),([0,3], 20),([0,4], 20),([0,9], 24),([3,4], 40),([3,9], 20),([4,9], 20),([5,6], 40),([5,8], -40),([6,7], -40),([7,8], 40),([9,9], 16)]
def c3GroupHessian100_23 : Poly := List.flatten [c3GroupHessian100_23Chunk0]
theorem c3GroupHessian100_23_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian100_23 := by kernel_rfl
private def c3GroupHessian100_33Chunk0 : Poly := [([0,0], 16),([0,4], 40),([0,9], 24),([4,4], 40),([4,9], 40),([6,6], 40),([6,8], -80),([8,8], 40),([9,9], 16)]
def c3GroupHessian100_33 : Poly := List.flatten [c3GroupHessian100_33Chunk0]
theorem c3GroupHessian100_33_check : sumFast (c3TensorGroup100.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian100_33 := by kernel_rfl
end D4.Secondary
