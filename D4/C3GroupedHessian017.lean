import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup17_det_check : c3TensorGroup17.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 19)) = true := by kernel_rfl
private def c3GroupHessian17_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 8),([0,6], 8),([0,9], 16),([1,1], 40),([5,5], 16),([5,6], -16),([5,9], 8),([6,6], 16),([6,9], 8),([9,9], 8)]
def c3GroupHessian17_00 : Poly := List.flatten [c3GroupHessian17_00Chunk0]
theorem c3GroupHessian17_00_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian17_00 := by kernel_rfl
private def c3GroupHessian17_01Chunk0 : Poly := [([0,0], 48),([0,1], 40),([0,2], 40),([0,5], 4),([0,6], 4),([0,7], 8),([0,9], 16),([1,2], 40),([5,7], 4),([5,8], -20),([5,9], 4),([6,7], 4),([6,8], 20),([6,9], 4),([7,9], 8),([9,9], 8)]
def c3GroupHessian17_01 : Poly := List.flatten [c3GroupHessian17_01Chunk0]
theorem c3GroupHessian17_01_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian17_01 := by kernel_rfl
private def c3GroupHessian17_02Chunk0 : Poly := [([0,0], -8),([0,3], 40),([0,5], -28),([0,6], 16),([0,7], -8),([0,9], -16),([1,3], 40),([5,5], -16),([5,6], 8),([5,7], -4),([5,9], -8),([6,7], -4),([6,9], -4),([7,9], -8),([9,9], -8)]
def c3GroupHessian17_02 : Poly := List.flatten [c3GroupHessian17_02Chunk0]
theorem c3GroupHessian17_02_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian17_02 := by kernel_rfl
private def c3GroupHessian17_03Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,5], 16),([0,6], -28),([0,9], -16),([1,4], 40),([5,6], 8),([5,8], 20),([5,9], -4),([6,6], -16),([6,8], -20),([6,9], -8),([9,9], -8)]
def c3GroupHessian17_03 : Poly := List.flatten [c3GroupHessian17_03Chunk0]
theorem c3GroupHessian17_03_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian17_03 := by kernel_rfl
private def c3GroupHessian17_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 16),([0,9], 16),([2,2], 40),([7,7], 8),([7,9], 16),([8,8], 40),([9,9], 8)]
def c3GroupHessian17_11 : Poly := List.flatten [c3GroupHessian17_11Chunk0]
theorem c3GroupHessian17_11_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian17_11 := by kernel_rfl
private def c3GroupHessian17_12Chunk0 : Poly := [([0,0], -8),([0,3], 40),([0,5], -4),([0,7], -16),([0,8], 40),([0,9], -16),([2,3], 40),([5,7], -4),([5,8], 20),([5,9], -4),([7,7], -8),([7,9], -16),([9,9], -8)]
def c3GroupHessian17_12 : Poly := List.flatten [c3GroupHessian17_12Chunk0]
theorem c3GroupHessian17_12_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian17_12 := by kernel_rfl
private def c3GroupHessian17_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,6], -4),([0,7], -8),([0,8], -40),([0,9], -16),([2,4], 40),([6,7], -4),([6,8], -20),([6,9], -4),([7,9], -8),([8,8], -40),([9,9], -8)]
def c3GroupHessian17_13 : Poly := List.flatten [c3GroupHessian17_13Chunk0]
theorem c3GroupHessian17_13_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian17_13 := by kernel_rfl
private def c3GroupHessian17_22Chunk0 : Poly := [([0,0], 48),([0,5], 48),([0,7], 16),([0,9], 16),([3,3], 40),([5,5], 16),([5,7], 8),([5,9], 8),([7,7], 8),([7,9], 16),([9,9], 8)]
def c3GroupHessian17_22 : Poly := List.flatten [c3GroupHessian17_22Chunk0]
theorem c3GroupHessian17_22_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian17_22 := by kernel_rfl
private def c3GroupHessian17_23Chunk0 : Poly := [([0,0], -32),([0,5], -16),([0,6], -16),([0,7], 8),([0,8], -40),([0,9], 16),([3,4], 40),([5,6], -8),([5,8], -20),([5,9], 4),([6,7], 4),([6,9], 4),([7,9], 8),([9,9], 8)]
def c3GroupHessian17_23 : Poly := List.flatten [c3GroupHessian17_23Chunk0]
theorem c3GroupHessian17_23_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian17_23 := by kernel_rfl
private def c3GroupHessian17_33Chunk0 : Poly := [([0,0], 48),([0,6], 48),([0,8], 80),([0,9], 16),([4,4], 40),([6,6], 16),([6,8], 40),([6,9], 8),([8,8], 40),([9,9], 8)]
def c3GroupHessian17_33 : Poly := List.flatten [c3GroupHessian17_33Chunk0]
theorem c3GroupHessian17_33_check : sumFast (c3TensorGroup17.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian17_33 := by kernel_rfl
end D4.Secondary
