import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup15_det_check : c3TensorGroup15.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 17)) = true := by kernel_rfl
private def c3GroupHessian15_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 8),([0,6], 16),([0,9], 16),([1,1], 40),([5,5], 16),([5,6], 8),([5,9], 8),([6,6], 8),([6,9], 16),([9,9], 8)]
def c3GroupHessian15_00 : Poly := List.flatten [c3GroupHessian15_00Chunk0]
theorem c3GroupHessian15_00_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian15_00 := by kernel_rfl
private def c3GroupHessian15_01Chunk0 : Poly := [([0,0], 44),([0,1], 40),([0,2], 40),([0,5], -8),([0,6], 4),([0,7], 4),([0,9], 12),([1,2], 40),([5,7], -8),([5,8], -20),([5,9], 4),([6,7], 4),([6,9], 8),([7,9], 4),([9,9], 8)]
def c3GroupHessian15_01 : Poly := List.flatten [c3GroupHessian15_01Chunk0]
theorem c3GroupHessian15_01_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian15_01 := by kernel_rfl
private def c3GroupHessian15_02Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,5], -16),([0,6], -4),([0,7], -4),([0,9], -12),([1,3], 40),([5,5], -16),([5,6], -4),([5,7], 8),([5,9], -8),([6,7], -4),([6,9], -8),([7,9], -4),([9,9], -8)]
def c3GroupHessian15_02 : Poly := List.flatten [c3GroupHessian15_02Chunk0]
theorem c3GroupHessian15_02_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian15_02 := by kernel_rfl
private def c3GroupHessian15_03Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,5], 16),([0,6], -16),([0,9], -16),([1,4], 40),([5,6], -4),([5,8], 20),([5,9], -4),([6,6], -8),([6,9], -16),([9,9], -8)]
def c3GroupHessian15_03 : Poly := List.flatten [c3GroupHessian15_03Chunk0]
theorem c3GroupHessian15_03_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian15_03 := by kernel_rfl
private def c3GroupHessian15_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 40),([0,9], 8),([2,2], 40),([7,7], 16),([7,8], 40),([7,9], 8),([8,8], 40),([9,9], 8)]
def c3GroupHessian15_11 : Poly := List.flatten [c3GroupHessian15_11Chunk0]
theorem c3GroupHessian15_11_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian15_11 := by kernel_rfl
private def c3GroupHessian15_12Chunk0 : Poly := [([0,0], 4),([0,3], 40),([0,5], 8),([0,7], -12),([0,8], 20),([0,9], -8),([2,3], 40),([5,7], 8),([5,8], 20),([5,9], -4),([7,7], -16),([7,8], -20),([7,9], -8),([9,9], -8)]
def c3GroupHessian15_12 : Poly := List.flatten [c3GroupHessian15_12Chunk0]
theorem c3GroupHessian15_12_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian15_12 := by kernel_rfl
private def c3GroupHessian15_13Chunk0 : Poly := [([0,0], -24),([0,4], 40),([0,6], -4),([0,7], -24),([0,8], -60),([0,9], -12),([2,4], 40),([6,7], -4),([6,9], -8),([7,8], -20),([7,9], -4),([8,8], -40),([9,9], -8)]
def c3GroupHessian15_13 : Poly := List.flatten [c3GroupHessian15_13Chunk0]
theorem c3GroupHessian15_13_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian15_13 := by kernel_rfl
private def c3GroupHessian15_22Chunk0 : Poly := [([0,0], 16),([0,5], 24),([0,7], -8),([0,9], 8),([3,3], 40),([5,5], 16),([5,7], -16),([5,9], 8),([7,7], 16),([7,9], 8),([9,9], 8)]
def c3GroupHessian15_22 : Poly := List.flatten [c3GroupHessian15_22Chunk0]
theorem c3GroupHessian15_22_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian15_22 := by kernel_rfl
private def c3GroupHessian15_23Chunk0 : Poly := [([0,0], -16),([0,5], -16),([0,6], 4),([0,7], 24),([0,8], -20),([0,9], 12),([3,4], 40),([5,6], 4),([5,8], -20),([5,9], 4),([6,7], 4),([6,9], 8),([7,8], 20),([7,9], 4),([9,9], 8)]
def c3GroupHessian15_23 : Poly := List.flatten [c3GroupHessian15_23Chunk0]
theorem c3GroupHessian15_23_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian15_23 := by kernel_rfl
private def c3GroupHessian15_33Chunk0 : Poly := [([0,0], 48),([0,6], 16),([0,8], 80),([0,9], 16),([4,4], 40),([6,6], 8),([6,9], 16),([8,8], 40),([9,9], 8)]
def c3GroupHessian15_33 : Poly := List.flatten [c3GroupHessian15_33Chunk0]
theorem c3GroupHessian15_33_check : sumFast (c3TensorGroup15.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian15_33 := by kernel_rfl
end D4.Secondary
