import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup146_det_check : c3TensorGroup146.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 189)) = true := by kernel_rfl
private def c3GroupHessian146_00Chunk0 : Poly := [([0,0], 32),([0,1], 24),([0,5], 24),([0,9], 40),([1,1], 8),([1,5], 16),([1,9], 8),([5,5], 8),([5,9], 8),([6,6], 40),([9,9], 16)]
def c3GroupHessian146_00 : Poly := List.flatten [c3GroupHessian146_00Chunk0]
theorem c3GroupHessian146_00_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian146_00 := by kernel_rfl
private def c3GroupHessian146_01Chunk0 : Poly := [([0,0], 20),([0,1], 4),([0,5], 4),([0,6], -40),([0,8], 20),([0,9], 36),([1,8], 4),([1,9], 4),([2,6], -40),([5,8], 4),([5,9], 4),([6,7], -40),([8,9], 16),([9,9], 16)]
def c3GroupHessian146_01 : Poly := List.flatten [c3GroupHessian146_01Chunk0]
theorem c3GroupHessian146_01_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian146_01 := by kernel_rfl
private def c3GroupHessian146_02Chunk0 : Poly := [([0,0], -20),([0,1], -4),([0,3], -4),([0,5], -16),([0,6], 40),([0,9], -36),([1,3], 4),([1,5], -8),([1,9], -4),([3,5], 4),([3,9], -8),([5,5], -8),([5,9], -8),([6,7], 40),([9,9], -16)]
def c3GroupHessian146_02 : Poly := List.flatten [c3GroupHessian146_02Chunk0]
theorem c3GroupHessian146_02_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian146_02 := by kernel_rfl
private def c3GroupHessian146_03Chunk0 : Poly := [([0,0], -20),([0,1], -4),([0,5], -4),([0,6], -40),([0,8], -20),([0,9], -36),([1,8], -4),([1,9], -4),([4,6], -40),([5,8], -4),([5,9], -4),([6,6], -40),([8,9], -16),([9,9], -16)]
def c3GroupHessian146_03 : Poly := List.flatten [c3GroupHessian146_03Chunk0]
theorem c3GroupHessian146_03_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian146_03 := by kernel_rfl
private def c3GroupHessian146_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 32),([0,9], 32),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian146_11 : Poly := List.flatten [c3GroupHessian146_11Chunk0]
theorem c3GroupHessian146_11_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian146_11 := by kernel_rfl
private def c3GroupHessian146_12Chunk0 : Poly := [([0,0], -56),([0,2], -40),([0,3], -8),([0,5], -4),([0,7], -80),([0,8], -16),([0,9], -32),([2,7], -40),([3,8], -8),([3,9], -8),([5,8], -4),([5,9], -4),([7,7], -40),([8,9], -16),([9,9], -16)]
def c3GroupHessian146_12 : Poly := List.flatten [c3GroupHessian146_12Chunk0]
theorem c3GroupHessian146_12_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian146_12 := by kernel_rfl
private def c3GroupHessian146_13Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -32),([0,9], -32),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -16),([8,9], -32),([9,9], -16)]
def c3GroupHessian146_13 : Poly := List.flatten [c3GroupHessian146_13Chunk0]
theorem c3GroupHessian146_13_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian146_13 := by kernel_rfl
private def c3GroupHessian146_22Chunk0 : Poly := [([0,0], 56),([0,3], 16),([0,5], 8),([0,7], 80),([0,9], 32),([3,3], 16),([3,5], -8),([3,9], 16),([5,5], 8),([5,9], 8),([7,7], 40),([9,9], 16)]
def c3GroupHessian146_22 : Poly := List.flatten [c3GroupHessian146_22Chunk0]
theorem c3GroupHessian146_22_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian146_22 := by kernel_rfl
private def c3GroupHessian146_23Chunk0 : Poly := [([0,0], -24),([0,3], 8),([0,4], -40),([0,5], 4),([0,6], -40),([0,7], -40),([0,8], 16),([0,9], 32),([3,8], 8),([3,9], 8),([4,7], -40),([5,8], 4),([5,9], 4),([6,7], -40),([8,9], 16),([9,9], 16)]
def c3GroupHessian146_23 : Poly := List.flatten [c3GroupHessian146_23Chunk0]
theorem c3GroupHessian146_23_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian146_23 := by kernel_rfl
private def c3GroupHessian146_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 32),([0,9], 32),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian146_33 : Poly := List.flatten [c3GroupHessian146_33Chunk0]
theorem c3GroupHessian146_33_check : sumFast (c3TensorGroup146.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian146_33 := by kernel_rfl
end D4.Secondary
