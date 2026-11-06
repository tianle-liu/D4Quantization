import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup128_det_check : c3TensorGroup128.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 168)) = true := by kernel_rfl
private def c3GroupHessian128_00Chunk0 : Poly := [([0,0], 48),([0,1], 48),([0,6], 80),([0,9], 80),([1,1], 16),([1,6], 40),([1,9], 40),([5,5], 40),([6,6], 40),([6,9], 80),([9,9], 40)]
def c3GroupHessian128_00 : Poly := List.flatten [c3GroupHessian128_00Chunk0]
theorem c3GroupHessian128_00_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian128_00 := by kernel_rfl
private def c3GroupHessian128_01Chunk0 : Poly := [([0,0], 8),([0,1], 4),([0,5], -40),([0,7], 8),([0,9], 40),([1,7], 4),([1,9], 20),([2,5], -40),([5,8], -40),([6,9], 40),([9,9], 40)]
def c3GroupHessian128_01 : Poly := List.flatten [c3GroupHessian128_01Chunk0]
theorem c3GroupHessian128_01_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian128_01 := by kernel_rfl
private def c3GroupHessian128_02Chunk0 : Poly := [([0,0], -8),([0,1], -4),([0,5], -40),([0,7], -8),([0,9], -40),([1,7], -4),([1,9], -20),([3,5], -40),([5,5], -40),([6,9], -40),([9,9], -40)]
def c3GroupHessian128_02 : Poly := List.flatten [c3GroupHessian128_02Chunk0]
theorem c3GroupHessian128_02_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian128_02 := by kernel_rfl
private def c3GroupHessian128_03Chunk0 : Poly := [([0,0], -40),([0,1], -20),([0,4], -16),([0,5], 40),([0,6], -80),([0,9], -80),([1,4], -8),([1,6], -20),([1,9], -20),([4,6], -20),([4,9], -20),([5,8], 40),([6,6], -40),([6,9], -80),([9,9], -40)]
def c3GroupHessian128_03 : Poly := List.flatten [c3GroupHessian128_03Chunk0]
theorem c3GroupHessian128_03_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian128_03 := by kernel_rfl
private def c3GroupHessian128_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 16),([0,8], 80),([2,2], 40),([2,8], 80),([7,7], 8),([8,8], 40),([9,9], 40)]
def c3GroupHessian128_11 : Poly := List.flatten [c3GroupHessian128_11Chunk0]
theorem c3GroupHessian128_11_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian128_11 := by kernel_rfl
private def c3GroupHessian128_12Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -16),([0,8], 40),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -8),([9,9], -40)]
def c3GroupHessian128_12 : Poly := List.flatten [c3GroupHessian128_12Chunk0]
theorem c3GroupHessian128_12_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian128_12 := by kernel_rfl
private def c3GroupHessian128_13Chunk0 : Poly := [([0,0], -40),([0,2], -40),([0,4], 4),([0,8], -80),([0,9], -40),([2,8], -40),([4,7], 4),([4,9], -20),([6,9], -40),([8,8], -40),([9,9], -40)]
def c3GroupHessian128_13 : Poly := List.flatten [c3GroupHessian128_13Chunk0]
theorem c3GroupHessian128_13_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian128_13 := by kernel_rfl
private def c3GroupHessian128_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,7], 16),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 8),([9,9], 40)]
def c3GroupHessian128_22 : Poly := List.flatten [c3GroupHessian128_22Chunk0]
theorem c3GroupHessian128_22_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian128_22 := by kernel_rfl
private def c3GroupHessian128_23Chunk0 : Poly := [([0,0], -40),([0,3], -40),([0,4], -4),([0,5], -40),([0,8], -40),([0,9], 40),([3,8], -40),([4,7], -4),([4,9], 20),([5,8], -40),([6,9], 40),([9,9], 40)]
def c3GroupHessian128_23 : Poly := List.flatten [c3GroupHessian128_23Chunk0]
theorem c3GroupHessian128_23_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian128_23 := by kernel_rfl
private def c3GroupHessian128_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,6], 40),([4,9], 40),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian128_33 : Poly := List.flatten [c3GroupHessian128_33Chunk0]
theorem c3GroupHessian128_33_check : sumFast (c3TensorGroup128.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian128_33 := by kernel_rfl
end D4.Secondary
