import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup200_det_check : c3TensorGroup200.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 255)) = true := by kernel_rfl
private def c3GroupHessian200_00Chunk0 : Poly := [([0,0], 48),([0,1], 8),([0,5], 80),([0,6], 16),([0,9], 80),([1,1], 16),([1,6], 8),([5,5], 40),([5,9], 80),([6,6], 8),([9,9], 40)]
def c3GroupHessian200_00 : Poly := List.flatten [c3GroupHessian200_00Chunk0]
theorem c3GroupHessian200_00_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian200_00 := by kernel_rfl
private def c3GroupHessian200_01Chunk0 : Poly := [([0,0], 44),([0,1], -8),([0,2], 4),([0,5], 40),([0,6], 4),([0,7], 40),([0,9], 80),([1,2], -8),([1,8], -20),([2,6], 4),([5,7], 40),([5,9], 40),([7,9], 40),([9,9], 40)]
def c3GroupHessian200_01 : Poly := List.flatten [c3GroupHessian200_01Chunk0]
theorem c3GroupHessian200_01_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian200_01 := by kernel_rfl
private def c3GroupHessian200_02Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -120),([0,7], -40),([0,9], -120),([3,5], -40),([3,9], -40),([5,5], -40),([5,7], -40),([5,9], -80),([7,9], -40),([9,9], -40)]
def c3GroupHessian200_02 : Poly := List.flatten [c3GroupHessian200_02Chunk0]
theorem c3GroupHessian200_02_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian200_02 := by kernel_rfl
private def c3GroupHessian200_03Chunk0 : Poly := [([0,0], -4),([0,1], 12),([0,4], 4),([0,6], -12),([0,9], -40),([1,4], 16),([1,6], -4),([1,8], 20),([4,6], 4),([5,9], -40),([6,6], -8),([9,9], -40)]
def c3GroupHessian200_03 : Poly := List.flatten [c3GroupHessian200_03Chunk0]
theorem c3GroupHessian200_03_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian200_03 := by kernel_rfl
private def c3GroupHessian200_11Chunk0 : Poly := [([0,0], 56),([0,2], 32),([0,7], 80),([0,8], 40),([0,9], 80),([2,2], 16),([2,8], 40),([7,7], 40),([7,9], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian200_11 : Poly := List.flatten [c3GroupHessian200_11Chunk0]
theorem c3GroupHessian200_11_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian200_11 := by kernel_rfl
private def c3GroupHessian200_12Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -40),([0,7], -120),([0,9], -120),([3,7], -40),([3,9], -40),([5,7], -40),([5,9], -40),([7,7], -40),([7,9], -80),([9,9], -40)]
def c3GroupHessian200_12 : Poly := List.flatten [c3GroupHessian200_12Chunk0]
theorem c3GroupHessian200_12_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian200_12 := by kernel_rfl
private def c3GroupHessian200_13Chunk0 : Poly := [([0,0], -12),([0,2], -12),([0,4], -8),([0,6], -4),([0,8], -40),([0,9], -40),([2,4], -8),([2,6], -4),([2,8], -20),([4,8], -20),([7,9], -40),([8,8], -40),([9,9], -40)]
def c3GroupHessian200_13 : Poly := List.flatten [c3GroupHessian200_13Chunk0]
theorem c3GroupHessian200_13_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian200_13 := by kernel_rfl
private def c3GroupHessian200_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 40),([3,5], 80),([3,7], 80),([3,9], 80),([5,5], 40),([5,7], 80),([5,9], 80),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian200_22 : Poly := List.flatten [c3GroupHessian200_22Chunk0]
theorem c3GroupHessian200_22_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian200_22 := by kernel_rfl
private def c3GroupHessian200_23Chunk0 : Poly := [([0,9], 80),([3,9], 40),([5,9], 40),([7,9], 40),([9,9], 40)]
def c3GroupHessian200_23 : Poly := List.flatten [c3GroupHessian200_23Chunk0]
theorem c3GroupHessian200_23_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian200_23 := by kernel_rfl
private def c3GroupHessian200_33Chunk0 : Poly := [([0,0], 16),([0,4], 24),([0,6], 8),([0,8], 40),([4,4], 16),([4,6], -8),([4,8], 40),([6,6], 8),([8,8], 40),([9,9], 40)]
def c3GroupHessian200_33 : Poly := List.flatten [c3GroupHessian200_33Chunk0]
theorem c3GroupHessian200_33_check : sumFast (c3TensorGroup200.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian200_33 := by kernel_rfl
end D4.Secondary
