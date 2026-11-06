import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup5_det_check : c3TensorGroup5.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 6)) = true := by kernel_rfl
private def c3GroupHessian5_00Chunk0 : Poly := [([0,0], 80),([0,1], 80),([0,5], 80),([0,6], 80),([0,9], 40),([1,1], 40),([5,5], 40),([5,6], 80),([5,9], 40),([6,6], 40),([6,9], 40),([9,9], 16)]
def c3GroupHessian5_00 : Poly := List.flatten [c3GroupHessian5_00Chunk0]
theorem c3GroupHessian5_00_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian5_00 := by kernel_rfl
private def c3GroupHessian5_01Chunk0 : Poly := [([0,0], 40),([0,1], 40),([0,2], 40),([0,7], -20),([0,9], 24),([1,2], 40),([5,7], -20),([5,9], 20),([6,7], -20),([6,9], 20),([7,9], -8),([8,9], 4),([9,9], 16)]
def c3GroupHessian5_01 : Poly := List.flatten [c3GroupHessian5_01Chunk0]
theorem c3GroupHessian5_01_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian5_01 := by kernel_rfl
private def c3GroupHessian5_02Chunk0 : Poly := [([0,3], 40),([0,5], -40),([0,7], 20),([0,9], -20),([1,3], 40),([5,5], -40),([5,6], -40),([5,7], 20),([5,9], -40),([6,7], 20),([6,9], -20),([7,9], 8),([9,9], -16)]
def c3GroupHessian5_02 : Poly := List.flatten [c3GroupHessian5_02Chunk0]
theorem c3GroupHessian5_02_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian5_02 := by kernel_rfl
private def c3GroupHessian5_03Chunk0 : Poly := [([0,0], -40),([0,4], 40),([0,5], -40),([0,6], -80),([0,9], -44),([1,4], 40),([5,6], -40),([5,9], -20),([6,6], -40),([6,9], -40),([8,9], -4),([9,9], -16)]
def c3GroupHessian5_03 : Poly := List.flatten [c3GroupHessian5_03Chunk0]
theorem c3GroupHessian5_03_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian5_03 := by kernel_rfl
private def c3GroupHessian5_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 16),([0,9], 8),([2,2], 40),([7,7], 16),([7,8], 8),([7,9], -16),([8,8], 8),([8,9], 8),([9,9], 16)]
def c3GroupHessian5_11 : Poly := List.flatten [c3GroupHessian5_11Chunk0]
theorem c3GroupHessian5_11_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian5_11 := by kernel_rfl
private def c3GroupHessian5_12Chunk0 : Poly := [([0,3], 40),([0,7], -4),([0,9], -4),([2,3], 40),([5,7], 20),([5,9], -20),([7,7], -16),([7,8], -4),([7,9], 16),([8,9], -4),([9,9], -16)]
def c3GroupHessian5_12 : Poly := List.flatten [c3GroupHessian5_12Chunk0]
theorem c3GroupHessian5_12_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian5_12 := by kernel_rfl
private def c3GroupHessian5_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,7], 16),([0,8], -16),([0,9], -28),([2,4], 40),([6,7], 20),([6,9], -20),([7,8], -4),([7,9], 8),([8,8], -8),([8,9], -8),([9,9], -16)]
def c3GroupHessian5_13 : Poly := List.flatten [c3GroupHessian5_13Chunk0]
theorem c3GroupHessian5_13_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian5_13 := by kernel_rfl
private def c3GroupHessian5_22Chunk0 : Poly := [([3,3], 40),([5,5], 40),([5,7], -40),([5,9], 40),([7,7], 16),([7,9], -16),([9,9], 16)]
def c3GroupHessian5_22 : Poly := List.flatten [c3GroupHessian5_22Chunk0]
theorem c3GroupHessian5_22_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian5_22 := by kernel_rfl
private def c3GroupHessian5_23Chunk0 : Poly := [([0,5], 40),([0,7], -16),([0,9], 24),([3,4], 40),([5,6], 40),([5,9], 20),([6,7], -20),([6,9], 20),([7,8], 4),([7,9], -8),([8,9], 4),([9,9], 16)]
def c3GroupHessian5_23 : Poly := List.flatten [c3GroupHessian5_23Chunk0]
theorem c3GroupHessian5_23_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian5_23 := by kernel_rfl
private def c3GroupHessian5_33Chunk0 : Poly := [([0,0], 48),([0,6], 80),([0,8], 16),([0,9], 48),([4,4], 40),([6,6], 40),([6,9], 40),([8,8], 8),([8,9], 8),([9,9], 16)]
def c3GroupHessian5_33 : Poly := List.flatten [c3GroupHessian5_33Chunk0]
theorem c3GroupHessian5_33_check : sumFast (c3TensorGroup5.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian5_33 := by kernel_rfl
end D4.Secondary
