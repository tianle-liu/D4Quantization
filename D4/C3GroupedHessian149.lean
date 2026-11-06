import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup149_det_check : c3TensorGroup149.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 194)) = true := by kernel_rfl
private def c3GroupHessian149_00Chunk0 : Poly := [([0,0], 48),([0,1], 48),([0,5], 80),([0,9], 80),([1,1], 16),([1,5], 40),([1,9], 40),([5,5], 40),([5,9], 80),([6,6], 40),([9,9], 40)]
def c3GroupHessian149_00 : Poly := List.flatten [c3GroupHessian149_00Chunk0]
theorem c3GroupHessian149_00_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian149_00 := by kernel_rfl
private def c3GroupHessian149_01Chunk0 : Poly := [([0,0], 8),([0,1], 4),([0,6], -40),([0,8], 8),([0,9], 40),([1,8], 4),([1,9], 20),([2,6], -40),([5,9], 40),([6,7], -40),([9,9], 40)]
def c3GroupHessian149_01 : Poly := List.flatten [c3GroupHessian149_01Chunk0]
theorem c3GroupHessian149_01_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian149_01 := by kernel_rfl
private def c3GroupHessian149_02Chunk0 : Poly := [([0,0], -40),([0,1], -20),([0,3], -16),([0,5], -80),([0,6], 40),([0,9], -80),([1,3], -8),([1,5], -20),([1,9], -20),([3,5], -20),([3,9], -20),([5,5], -40),([5,9], -80),([6,7], 40),([9,9], -40)]
def c3GroupHessian149_02 : Poly := List.flatten [c3GroupHessian149_02Chunk0]
theorem c3GroupHessian149_02_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian149_02 := by kernel_rfl
private def c3GroupHessian149_03Chunk0 : Poly := [([0,0], -8),([0,1], -4),([0,6], -40),([0,8], -8),([0,9], -40),([1,8], -4),([1,9], -20),([4,6], -40),([5,9], -40),([6,6], -40),([9,9], -40)]
def c3GroupHessian149_03 : Poly := List.flatten [c3GroupHessian149_03Chunk0]
theorem c3GroupHessian149_03_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian149_03 := by kernel_rfl
private def c3GroupHessian149_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,8], 16),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 8),([9,9], 40)]
def c3GroupHessian149_11 : Poly := List.flatten [c3GroupHessian149_11Chunk0]
theorem c3GroupHessian149_11_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian149_11 := by kernel_rfl
private def c3GroupHessian149_12Chunk0 : Poly := [([0,0], -40),([0,2], -40),([0,3], 4),([0,7], -80),([0,9], -40),([2,7], -40),([3,8], 4),([3,9], -20),([5,9], -40),([7,7], -40),([9,9], -40)]
def c3GroupHessian149_12 : Poly := List.flatten [c3GroupHessian149_12Chunk0]
theorem c3GroupHessian149_12_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian149_12 := by kernel_rfl
private def c3GroupHessian149_13Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -16),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -8),([9,9], -40)]
def c3GroupHessian149_13 : Poly := List.flatten [c3GroupHessian149_13Chunk0]
theorem c3GroupHessian149_13_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian149_13 := by kernel_rfl
private def c3GroupHessian149_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,7], 80),([0,9], 80),([3,3], 16),([3,5], 40),([3,9], 40),([5,5], 40),([5,9], 80),([7,7], 40),([9,9], 40)]
def c3GroupHessian149_22 : Poly := List.flatten [c3GroupHessian149_22Chunk0]
theorem c3GroupHessian149_22_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian149_22 := by kernel_rfl
private def c3GroupHessian149_23Chunk0 : Poly := [([0,0], -40),([0,3], -4),([0,4], -40),([0,6], -40),([0,7], -40),([0,9], 40),([3,8], -4),([3,9], 20),([4,7], -40),([5,9], 40),([6,7], -40),([9,9], 40)]
def c3GroupHessian149_23 : Poly := List.flatten [c3GroupHessian149_23Chunk0]
theorem c3GroupHessian149_23_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian149_23 := by kernel_rfl
private def c3GroupHessian149_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 16),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 8),([9,9], 40)]
def c3GroupHessian149_33 : Poly := List.flatten [c3GroupHessian149_33Chunk0]
theorem c3GroupHessian149_33_check : sumFast (c3TensorGroup149.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian149_33 := by kernel_rfl
end D4.Secondary
