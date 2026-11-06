import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup124_det_check : c3TensorGroup124.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 162)) = true := by kernel_rfl
private def c3GroupHessian124_00Chunk0 : Poly := [([0,0], 16),([0,1], 24),([0,6], 40),([0,9], -8),([1,1], 16),([1,6], 40),([1,9], -16),([5,5], 40),([6,6], 40),([6,9], -40),([9,9], 16)]
def c3GroupHessian124_00 : Poly := List.flatten [c3GroupHessian124_00Chunk0]
theorem c3GroupHessian124_00_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian124_00 := by kernel_rfl
private def c3GroupHessian124_01Chunk0 : Poly := [([0,0], -4),([0,1], -8),([0,5], -40),([0,6], -20),([0,7], -4),([0,9], 12),([1,7], -8),([1,9], -8),([2,5], -40),([5,8], -40),([6,7], -20),([6,9], -20),([7,9], 16),([9,9], 16)]
def c3GroupHessian124_01 : Poly := List.flatten [c3GroupHessian124_01Chunk0]
theorem c3GroupHessian124_01_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian124_01 := by kernel_rfl
private def c3GroupHessian124_02Chunk0 : Poly := [([0,0], 4),([0,1], 8),([0,5], -40),([0,6], 20),([0,7], 4),([0,9], -12),([1,7], 8),([1,9], 8),([3,5], -40),([5,5], -40),([6,7], 20),([6,9], 20),([7,9], -16),([9,9], -16)]
def c3GroupHessian124_02 : Poly := List.flatten [c3GroupHessian124_02Chunk0]
theorem c3GroupHessian124_02_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian124_02 := by kernel_rfl
private def c3GroupHessian124_03Chunk0 : Poly := [([0,0], -12),([0,1], -8),([0,4], 4),([0,5], 40),([0,6], -40),([0,9], 12),([1,4], 4),([1,6], -20),([1,9], 8),([4,9], 4),([5,8], 40),([6,6], -40),([6,9], 40),([9,9], -16)]
def c3GroupHessian124_03 : Poly := List.flatten [c3GroupHessian124_03Chunk0]
theorem c3GroupHessian124_03_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian124_03 := by kernel_rfl
private def c3GroupHessian124_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 80),([0,9], 32),([2,2], 40),([2,8], 80),([7,7], 16),([7,9], 32),([8,8], 40),([9,9], 16)]
def c3GroupHessian124_11 : Poly := List.flatten [c3GroupHessian124_11Chunk0]
theorem c3GroupHessian124_11_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian124_11 := by kernel_rfl
private def c3GroupHessian124_12Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -32),([0,8], 40),([0,9], -32),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -16),([7,9], -32),([9,9], -16)]
def c3GroupHessian124_12 : Poly := List.flatten [c3GroupHessian124_12Chunk0]
theorem c3GroupHessian124_12_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian124_12 := by kernel_rfl
private def c3GroupHessian124_13Chunk0 : Poly := [([0,0], -32),([0,2], -40),([0,4], 4),([0,6], 20),([0,7], 8),([0,8], -80),([0,9], -8),([2,8], -40),([4,7], 4),([4,9], 4),([6,7], 20),([6,9], 20),([7,9], -16),([8,8], -40),([9,9], -16)]
def c3GroupHessian124_13 : Poly := List.flatten [c3GroupHessian124_13Chunk0]
theorem c3GroupHessian124_13_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian124_13 := by kernel_rfl
private def c3GroupHessian124_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 32),([0,9], 32),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 16),([7,9], 32),([9,9], 16)]
def c3GroupHessian124_22 : Poly := List.flatten [c3GroupHessian124_22Chunk0]
theorem c3GroupHessian124_22_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian124_22 := by kernel_rfl
private def c3GroupHessian124_23Chunk0 : Poly := [([0,0], -48),([0,3], -40),([0,4], -4),([0,5], -40),([0,6], -20),([0,7], -8),([0,8], -40),([0,9], 8),([3,8], -40),([4,7], -4),([4,9], -4),([5,8], -40),([6,7], -20),([6,9], -20),([7,9], 16),([9,9], 16)]
def c3GroupHessian124_23 : Poly := List.flatten [c3GroupHessian124_23Chunk0]
theorem c3GroupHessian124_23_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian124_23 := by kernel_rfl
private def c3GroupHessian124_33Chunk0 : Poly := [([0,0], 56),([0,4], 8),([0,6], 40),([0,8], 80),([0,9], -16),([4,4], 8),([4,9], -8),([6,6], 40),([6,9], -40),([8,8], 40),([9,9], 16)]
def c3GroupHessian124_33 : Poly := List.flatten [c3GroupHessian124_33Chunk0]
theorem c3GroupHessian124_33_check : sumFast (c3TensorGroup124.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian124_33 := by kernel_rfl
end D4.Secondary
