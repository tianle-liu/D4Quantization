import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup40_det_check : c3TensorGroup40.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 58)) = true := by kernel_rfl
private def c3GroupHessian40_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 40),([0,6], 80),([0,9], 32),([1,1], 40),([1,6], 80),([5,5], 40),([5,9], 40),([6,6], 40),([9,9], 16)]
def c3GroupHessian40_00 : Poly := List.flatten [c3GroupHessian40_00Chunk0]
theorem c3GroupHessian40_00_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian40_00 := by kernel_rfl
private def c3GroupHessian40_01Chunk0 : Poly := [([0,0], 8),([0,2], -8),([0,7], -40),([0,8], -8),([0,9], 24),([1,7], -40),([2,5], -20),([2,9], -8),([5,8], -20),([5,9], 20),([6,7], -40),([8,9], -8),([9,9], 16)]
def c3GroupHessian40_01 : Poly := List.flatten [c3GroupHessian40_01Chunk0]
theorem c3GroupHessian40_01_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian40_01 := by kernel_rfl
private def c3GroupHessian40_02Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,3], 40),([0,5], -40),([0,6], 40),([0,7], 40),([0,9], -32),([1,3], 40),([1,7], 40),([3,6], 40),([5,5], -40),([5,9], -40),([6,7], 40),([9,9], -16)]
def c3GroupHessian40_02 : Poly := List.flatten [c3GroupHessian40_02Chunk0]
theorem c3GroupHessian40_02_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian40_02 := by kernel_rfl
private def c3GroupHessian40_03Chunk0 : Poly := [([0,0], -44),([0,1], -40),([0,4], 4),([0,6], -80),([0,8], 8),([0,9], -20),([1,6], -40),([4,9], 4),([5,8], 20),([5,9], -20),([6,6], -40),([8,9], 8),([9,9], -16)]
def c3GroupHessian40_03 : Poly := List.flatten [c3GroupHessian40_03Chunk0]
theorem c3GroupHessian40_03_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian40_03 := by kernel_rfl
private def c3GroupHessian40_11Chunk0 : Poly := [([0,0], 16),([0,2], 16),([0,8], 16),([0,9], 16),([2,2], 16),([2,8], 32),([2,9], -16),([7,7], 40),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian40_11 : Poly := List.flatten [c3GroupHessian40_11Chunk0]
theorem c3GroupHessian40_11_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian40_11 := by kernel_rfl
private def c3GroupHessian40_12Chunk0 : Poly := [([0,0], -8),([0,2], 8),([0,7], -40),([0,8], 8),([0,9], -24),([2,5], 20),([2,9], 8),([3,7], -40),([5,8], 20),([5,9], -20),([7,7], -40),([8,9], 8),([9,9], -16)]
def c3GroupHessian40_12 : Poly := List.flatten [c3GroupHessian40_12Chunk0]
theorem c3GroupHessian40_12_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian40_12 := by kernel_rfl
private def c3GroupHessian40_13Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,4], 8),([0,7], 40),([0,8], -12),([0,9], -12),([2,4], 4),([2,8], -16),([2,9], 8),([4,8], 4),([4,9], 4),([6,7], 40),([8,8], -16),([8,9], 16),([9,9], -16)]
def c3GroupHessian40_13 : Poly := List.flatten [c3GroupHessian40_13Chunk0]
theorem c3GroupHessian40_13_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian40_13 := by kernel_rfl
private def c3GroupHessian40_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 40),([0,7], 80),([0,9], 32),([3,3], 40),([3,7], 80),([5,5], 40),([5,9], 40),([7,7], 40),([9,9], 16)]
def c3GroupHessian40_22 : Poly := List.flatten [c3GroupHessian40_22Chunk0]
theorem c3GroupHessian40_22_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian40_22 := by kernel_rfl
private def c3GroupHessian40_23Chunk0 : Poly := [([0,0], -36),([0,3], -40),([0,4], -4),([0,6], -40),([0,7], -40),([0,8], -8),([0,9], 20),([3,6], -40),([4,9], -4),([5,8], -20),([5,9], 20),([6,7], -40),([8,9], -8),([9,9], 16)]
def c3GroupHessian40_23 : Poly := List.flatten [c3GroupHessian40_23Chunk0]
theorem c3GroupHessian40_23_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian40_23 := by kernel_rfl
private def c3GroupHessian40_33Chunk0 : Poly := [([0,0], 48),([0,6], 80),([0,8], 8),([0,9], 8),([4,4], 8),([4,8], -8),([4,9], -8),([6,6], 40),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian40_33 : Poly := List.flatten [c3GroupHessian40_33Chunk0]
theorem c3GroupHessian40_33_check : sumFast (c3TensorGroup40.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian40_33 := by kernel_rfl
end D4.Secondary
