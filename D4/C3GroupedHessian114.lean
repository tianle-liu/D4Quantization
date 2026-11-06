import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup114_det_check : c3TensorGroup114.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 150)) = true := by kernel_rfl
private def c3GroupHessian114_00Chunk0 : Poly := [([0,0], 56),([0,1], 32),([0,5], 80),([0,6], 80),([0,9], 80),([1,1], 16),([5,5], 40),([5,6], 80),([5,9], 80),([6,6], 40),([6,9], 80),([9,9], 40)]
def c3GroupHessian114_00 : Poly := List.flatten [c3GroupHessian114_00Chunk0]
theorem c3GroupHessian114_00_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian114_00 := by kernel_rfl
private def c3GroupHessian114_01Chunk0 : Poly := [([0,0], -4),([0,1], -4),([0,2], -40),([0,7], -20),([0,8], -8),([0,9], 40),([1,7], -20),([1,8], -8),([2,5], -40),([2,6], -40),([2,9], -40),([5,9], 40),([6,9], 40),([9,9], 40)]
def c3GroupHessian114_01 : Poly := List.flatten [c3GroupHessian114_01Chunk0]
theorem c3GroupHessian114_01_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian114_01 := by kernel_rfl
private def c3GroupHessian114_02Chunk0 : Poly := [([0,0], -32),([0,1], 8),([0,3], -40),([0,5], -80),([0,6], -40),([0,7], 20),([0,9], -80),([1,7], 20),([3,5], -40),([3,6], -40),([3,9], -40),([5,5], -40),([5,6], -40),([5,9], -80),([6,9], -40),([9,9], -40)]
def c3GroupHessian114_02 : Poly := List.flatten [c3GroupHessian114_02Chunk0]
theorem c3GroupHessian114_02_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian114_02 := by kernel_rfl
private def c3GroupHessian114_03Chunk0 : Poly := [([0,0], -44),([0,1], -4),([0,4], -40),([0,5], -40),([0,6], -80),([0,8], 8),([0,9], -80),([1,8], 8),([4,5], -40),([4,6], -40),([4,9], -40),([5,6], -40),([5,9], -40),([6,6], -40),([6,9], -80),([9,9], -40)]
def c3GroupHessian114_03 : Poly := List.flatten [c3GroupHessian114_03Chunk0]
theorem c3GroupHessian114_03_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian114_03 := by kernel_rfl
private def c3GroupHessian114_11Chunk0 : Poly := [([0,0], 16),([0,7], 40),([0,8], 24),([2,2], 40),([2,9], -80),([7,7], 40),([7,8], 40),([8,8], 16),([9,9], 40)]
def c3GroupHessian114_11 : Poly := List.flatten [c3GroupHessian114_11Chunk0]
theorem c3GroupHessian114_11_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian114_11 := by kernel_rfl
private def c3GroupHessian114_12Chunk0 : Poly := [([0,0], -12),([0,2], 40),([0,7], -40),([0,8], -8),([0,9], -40),([2,3], 40),([2,5], 40),([2,9], 40),([3,9], -40),([5,9], -40),([7,7], -40),([7,8], -20),([9,9], -40)]
def c3GroupHessian114_12 : Poly := List.flatten [c3GroupHessian114_12Chunk0]
theorem c3GroupHessian114_12_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian114_12 := by kernel_rfl
private def c3GroupHessian114_13Chunk0 : Poly := [([0,0], -4),([0,2], 40),([0,8], -16),([0,9], -40),([2,4], 40),([2,6], 40),([2,9], 40),([4,9], -40),([6,9], -40),([7,8], -20),([8,8], -16),([9,9], -40)]
def c3GroupHessian114_13 : Poly := List.flatten [c3GroupHessian114_13Chunk0]
theorem c3GroupHessian114_13_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian114_13 := by kernel_rfl
private def c3GroupHessian114_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], 80),([3,3], 40),([3,5], 80),([3,9], 80),([5,5], 40),([5,9], 80),([7,7], 40),([9,9], 40)]
def c3GroupHessian114_22 : Poly := List.flatten [c3GroupHessian114_22Chunk0]
theorem c3GroupHessian114_22_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian114_22 := by kernel_rfl
private def c3GroupHessian114_23Chunk0 : Poly := [([0,0], 36),([0,3], 40),([0,4], 40),([0,5], 40),([0,6], 40),([0,8], 8),([0,9], 80),([3,4], 40),([3,6], 40),([3,9], 40),([4,5], 40),([4,9], 40),([5,6], 40),([5,9], 40),([6,9], 40),([7,8], 20),([9,9], 40)]
def c3GroupHessian114_23 : Poly := List.flatten [c3GroupHessian114_23Chunk0]
theorem c3GroupHessian114_23_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian114_23 := by kernel_rfl
private def c3GroupHessian114_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 80),([4,4], 40),([4,6], 80),([4,9], 80),([6,6], 40),([6,9], 80),([8,8], 16),([9,9], 40)]
def c3GroupHessian114_33 : Poly := List.flatten [c3GroupHessian114_33Chunk0]
theorem c3GroupHessian114_33_check : sumFast (c3TensorGroup114.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian114_33 := by kernel_rfl
end D4.Secondary
