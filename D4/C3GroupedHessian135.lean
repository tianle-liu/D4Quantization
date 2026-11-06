import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup135_det_check : c3TensorGroup135.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 177)) = true := by kernel_rfl
private def c3GroupHessian135_00Chunk0 : Poly := [([0,0], 16),([0,1], 16),([0,6], 16),([0,9], 16),([1,1], 16),([1,6], 8),([1,9], -16),([5,5], 40),([6,6], 8),([6,9], 8),([9,9], 16)]
def c3GroupHessian135_00 : Poly := List.flatten [c3GroupHessian135_00Chunk0]
theorem c3GroupHessian135_00_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian135_00 := by kernel_rfl
private def c3GroupHessian135_01Chunk0 : Poly := [([0,0], 8),([0,1], -8),([0,5], -40),([0,6], 4),([0,9], 24),([1,7], -20),([1,9], -8),([2,5], -40),([5,8], -40),([6,9], 4),([7,9], 20),([9,9], 16)]
def c3GroupHessian135_01 : Poly := List.flatten [c3GroupHessian135_01Chunk0]
theorem c3GroupHessian135_01_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian135_01 := by kernel_rfl
private def c3GroupHessian135_02Chunk0 : Poly := [([0,0], -8),([0,1], 8),([0,5], -40),([0,6], -4),([0,9], -24),([1,7], 20),([1,9], 8),([3,5], -40),([5,5], -40),([6,9], -4),([7,9], -20),([9,9], -16)]
def c3GroupHessian135_02 : Poly := List.flatten [c3GroupHessian135_02Chunk0]
theorem c3GroupHessian135_02_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian135_02 := by kernel_rfl
private def c3GroupHessian135_03Chunk0 : Poly := [([0,0], -8),([0,1], 8),([0,4], 8),([0,5], 40),([0,6], -12),([0,9], -24),([1,4], 16),([1,6], -4),([1,9], 8),([4,6], 4),([4,9], -8),([5,8], 40),([6,6], -8),([6,9], -8),([9,9], -16)]
def c3GroupHessian135_03 : Poly := List.flatten [c3GroupHessian135_03Chunk0]
theorem c3GroupHessian135_03_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian135_03 := by kernel_rfl
private def c3GroupHessian135_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 40),([0,8], 80),([0,9], 32),([2,2], 40),([2,8], 80),([7,7], 40),([7,9], 40),([8,8], 40),([9,9], 16)]
def c3GroupHessian135_11 : Poly := List.flatten [c3GroupHessian135_11Chunk0]
theorem c3GroupHessian135_11_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian135_11 := by kernel_rfl
private def c3GroupHessian135_12Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -40),([0,8], 40),([0,9], -32),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -40),([7,9], -40),([9,9], -16)]
def c3GroupHessian135_12 : Poly := List.flatten [c3GroupHessian135_12Chunk0]
theorem c3GroupHessian135_12_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian135_12 := by kernel_rfl
private def c3GroupHessian135_13Chunk0 : Poly := [([0,0], -56),([0,2], -40),([0,4], -8),([0,6], -4),([0,7], -20),([0,8], -80),([0,9], -32),([2,8], -40),([4,7], -20),([4,9], -8),([6,9], -4),([7,9], -20),([8,8], -40),([9,9], -16)]
def c3GroupHessian135_13 : Poly := List.flatten [c3GroupHessian135_13Chunk0]
theorem c3GroupHessian135_13_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian135_13 := by kernel_rfl
private def c3GroupHessian135_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], 32),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 40),([7,9], 40),([9,9], 16)]
def c3GroupHessian135_22 : Poly := List.flatten [c3GroupHessian135_22Chunk0]
theorem c3GroupHessian135_22_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian135_22 := by kernel_rfl
private def c3GroupHessian135_23Chunk0 : Poly := [([0,0], -24),([0,3], -40),([0,4], 8),([0,5], -40),([0,6], 4),([0,7], 20),([0,8], -40),([0,9], 32),([3,8], -40),([4,7], 20),([4,9], 8),([5,8], -40),([6,9], 4),([7,9], 20),([9,9], 16)]
def c3GroupHessian135_23 : Poly := List.flatten [c3GroupHessian135_23Chunk0]
theorem c3GroupHessian135_23_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian135_23 := by kernel_rfl
private def c3GroupHessian135_33Chunk0 : Poly := [([0,0], 56),([0,4], 16),([0,6], 8),([0,8], 80),([0,9], 32),([4,4], 16),([4,6], -8),([4,9], 16),([6,6], 8),([6,9], 8),([8,8], 40),([9,9], 16)]
def c3GroupHessian135_33 : Poly := List.flatten [c3GroupHessian135_33Chunk0]
theorem c3GroupHessian135_33_check : sumFast (c3TensorGroup135.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian135_33 := by kernel_rfl
end D4.Secondary
