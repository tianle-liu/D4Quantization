import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup89_det_check : c3TensorGroup89.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 118)) = true := by kernel_rfl
private def c3GroupHessian89_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([0,9], 160),([1,1], 40),([1,5], 80),([1,6], 80),([1,9], 80),([5,5], 40),([5,6], 80),([5,9], 80),([6,6], 40),([6,9], 80),([9,9], 40)]
def c3GroupHessian89_00 : Poly := List.flatten [c3GroupHessian89_00Chunk0]
theorem c3GroupHessian89_00_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian89_00 := by kernel_rfl
private def c3GroupHessian89_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40),([0,9], 120),([1,9], 40),([5,9], 40),([6,9], 40),([9,9], 40)]
def c3GroupHessian89_01 : Poly := List.flatten [c3GroupHessian89_01Chunk0]
theorem c3GroupHessian89_01_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian89_01 := by kernel_rfl
private def c3GroupHessian89_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([0,9], -120),([1,5], -40),([1,9], -40),([5,5], -40),([5,6], -40),([5,9], -80),([6,9], -40),([9,9], -40)]
def c3GroupHessian89_02 : Poly := List.flatten [c3GroupHessian89_02Chunk0]
theorem c3GroupHessian89_02_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian89_02 := by kernel_rfl
private def c3GroupHessian89_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([0,9], -120),([1,6], -40),([1,9], -40),([5,6], -40),([5,9], -40),([6,6], -40),([6,9], -80),([9,9], -40)]
def c3GroupHessian89_03 : Poly := List.flatten [c3GroupHessian89_03Chunk0]
theorem c3GroupHessian89_03_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian89_03 := by kernel_rfl
private def c3GroupHessian89_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 16),([0,9], 80),([2,2], 8),([2,7], 16),([7,7], 8),([8,8], 40),([9,9], 40)]
def c3GroupHessian89_11 : Poly := List.flatten [c3GroupHessian89_11Chunk0]
theorem c3GroupHessian89_11_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian89_11 := by kernel_rfl
private def c3GroupHessian89_12Chunk0 : Poly := [([0,0], -40),([0,3], 4),([0,5], -40),([0,7], -8),([0,8], 40),([0,9], -80),([2,3], 4),([2,7], -8),([3,7], 4),([3,8], 20),([5,9], -40),([7,7], -8),([9,9], -40)]
def c3GroupHessian89_12 : Poly := List.flatten [c3GroupHessian89_12Chunk0]
theorem c3GroupHessian89_12_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian89_12 := by kernel_rfl
private def c3GroupHessian89_13Chunk0 : Poly := [([0,0], -40),([0,4], 4),([0,6], -40),([0,8], -40),([0,9], -80),([2,4], 4),([4,7], 4),([4,8], -20),([6,9], -40),([8,8], -40),([9,9], -40)]
def c3GroupHessian89_13 : Poly := List.flatten [c3GroupHessian89_13Chunk0]
theorem c3GroupHessian89_13_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian89_13 := by kernel_rfl
private def c3GroupHessian89_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,9], 80),([3,3], 16),([3,7], -8),([5,5], 40),([5,9], 80),([7,7], 8),([9,9], 40)]
def c3GroupHessian89_22 : Poly := List.flatten [c3GroupHessian89_22Chunk0]
theorem c3GroupHessian89_22_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian89_22 := by kernel_rfl
private def c3GroupHessian89_23Chunk0 : Poly := [([0,3], -20),([0,4], -20),([0,5], 40),([0,6], 40),([0,8], -40),([0,9], 80),([3,4], -8),([3,8], -20),([4,7], -4),([5,6], 40),([5,9], 40),([6,9], 40),([9,9], 40)]
def c3GroupHessian89_23 : Poly := List.flatten [c3GroupHessian89_23Chunk0]
theorem c3GroupHessian89_23_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian89_23 := by kernel_rfl
private def c3GroupHessian89_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,8], 40),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian89_33 : Poly := List.flatten [c3GroupHessian89_33Chunk0]
theorem c3GroupHessian89_33_check : sumFast (c3TensorGroup89.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian89_33 := by kernel_rfl
end D4.Secondary
