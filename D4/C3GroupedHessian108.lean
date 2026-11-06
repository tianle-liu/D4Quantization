import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup108_det_check : c3TensorGroup108.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 142)) = true := by kernel_rfl
private def c3GroupHessian108_00Chunk0 : Poly := [([0,0], 56),([0,1], 40),([0,5], 80),([0,6], 80),([0,9], 80),([1,1], 40),([5,5], 40),([5,6], 80),([5,9], 80),([6,6], 40),([6,9], 80),([9,9], 40)]
def c3GroupHessian108_00 : Poly := List.flatten [c3GroupHessian108_00Chunk0]
theorem c3GroupHessian108_00_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian108_00 := by kernel_rfl
private def c3GroupHessian108_01Chunk0 : Poly := [([0,0], 8),([0,2], -40),([0,7], -8),([0,8], -8),([0,9], 40),([1,7], -20),([1,8], -20),([2,5], -40),([2,6], -40),([2,9], -40),([5,9], 40),([6,9], 40),([9,9], 40)]
def c3GroupHessian108_01 : Poly := List.flatten [c3GroupHessian108_01Chunk0]
theorem c3GroupHessian108_01_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian108_01 := by kernel_rfl
private def c3GroupHessian108_02Chunk0 : Poly := [([0,0], -44),([0,3], -40),([0,5], -80),([0,6], -40),([0,7], 8),([0,9], -80),([1,7], 20),([3,5], -40),([3,6], -40),([3,9], -40),([5,5], -40),([5,6], -40),([5,9], -80),([6,9], -40),([9,9], -40)]
def c3GroupHessian108_02 : Poly := List.flatten [c3GroupHessian108_02Chunk0]
theorem c3GroupHessian108_02_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian108_02 := by kernel_rfl
private def c3GroupHessian108_03Chunk0 : Poly := [([0,0], -44),([0,4], -40),([0,5], -40),([0,6], -80),([0,8], 8),([0,9], -80),([1,8], 20),([4,5], -40),([4,6], -40),([4,9], -40),([5,6], -40),([5,9], -40),([6,6], -40),([6,9], -80),([9,9], -40)]
def c3GroupHessian108_03 : Poly := List.flatten [c3GroupHessian108_03Chunk0]
theorem c3GroupHessian108_03_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian108_03 := by kernel_rfl
private def c3GroupHessian108_11Chunk0 : Poly := [([0,0], 16),([0,7], 16),([0,8], 16),([2,2], 40),([2,9], -80),([7,7], 16),([7,8], 32),([8,8], 16),([9,9], 40)]
def c3GroupHessian108_11 : Poly := List.flatten [c3GroupHessian108_11Chunk0]
theorem c3GroupHessian108_11_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian108_11 := by kernel_rfl
private def c3GroupHessian108_12Chunk0 : Poly := [([0,0], -8),([0,2], 40),([0,7], -12),([0,8], -4),([0,9], -40),([2,3], 40),([2,5], 40),([2,9], 40),([3,9], -40),([5,9], -40),([7,7], -16),([7,8], -16),([9,9], -40)]
def c3GroupHessian108_12 : Poly := List.flatten [c3GroupHessian108_12Chunk0]
theorem c3GroupHessian108_12_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian108_12 := by kernel_rfl
private def c3GroupHessian108_13Chunk0 : Poly := [([0,0], -8),([0,2], 40),([0,7], -4),([0,8], -12),([0,9], -40),([2,4], 40),([2,6], 40),([2,9], 40),([4,9], -40),([6,9], -40),([7,8], -16),([8,8], -16),([9,9], -40)]
def c3GroupHessian108_13 : Poly := List.flatten [c3GroupHessian108_13Chunk0]
theorem c3GroupHessian108_13_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian108_13 := by kernel_rfl
private def c3GroupHessian108_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,7], 8),([0,9], 80),([3,3], 40),([3,5], 80),([3,9], 80),([5,5], 40),([5,9], 80),([7,7], 16),([9,9], 40)]
def c3GroupHessian108_22 : Poly := List.flatten [c3GroupHessian108_22Chunk0]
theorem c3GroupHessian108_22_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian108_22 := by kernel_rfl
private def c3GroupHessian108_23Chunk0 : Poly := [([0,0], 40),([0,3], 40),([0,4], 40),([0,5], 40),([0,6], 40),([0,7], 4),([0,8], 4),([0,9], 80),([3,4], 40),([3,6], 40),([3,9], 40),([4,5], 40),([4,9], 40),([5,6], 40),([5,9], 40),([6,9], 40),([7,8], 16),([9,9], 40)]
def c3GroupHessian108_23 : Poly := List.flatten [c3GroupHessian108_23Chunk0]
theorem c3GroupHessian108_23_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian108_23 := by kernel_rfl
private def c3GroupHessian108_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 80),([4,4], 40),([4,6], 80),([4,9], 80),([6,6], 40),([6,9], 80),([8,8], 16),([9,9], 40)]
def c3GroupHessian108_33 : Poly := List.flatten [c3GroupHessian108_33Chunk0]
theorem c3GroupHessian108_33_check : sumFast (c3TensorGroup108.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian108_33 := by kernel_rfl
end D4.Secondary
