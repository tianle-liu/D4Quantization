import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup125_det_check : c3TensorGroup125.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 163)) = true := by kernel_rfl
private def c3GroupHessian125_00Chunk0 : Poly := [([0,0], 32),([0,1], 24),([0,6], 24),([0,9], 40),([1,1], 8),([1,6], 16),([1,9], 8),([5,5], 40),([6,6], 8),([6,9], 8),([9,9], 16)]
def c3GroupHessian125_00 : Poly := List.flatten [c3GroupHessian125_00Chunk0]
theorem c3GroupHessian125_00_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian125_00 := by kernel_rfl
private def c3GroupHessian125_01Chunk0 : Poly := [([0,0], 20),([0,1], 4),([0,5], -40),([0,6], 4),([0,7], 20),([0,9], 36),([1,7], 4),([1,9], 4),([2,5], -40),([5,8], -40),([6,7], 4),([6,9], 4),([7,9], 16),([9,9], 16)]
def c3GroupHessian125_01 : Poly := List.flatten [c3GroupHessian125_01Chunk0]
theorem c3GroupHessian125_01_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian125_01 := by kernel_rfl
private def c3GroupHessian125_02Chunk0 : Poly := [([0,0], -20),([0,1], -4),([0,5], -40),([0,6], -4),([0,7], -20),([0,9], -36),([1,7], -4),([1,9], -4),([3,5], -40),([5,5], -40),([6,7], -4),([6,9], -4),([7,9], -16),([9,9], -16)]
def c3GroupHessian125_02 : Poly := List.flatten [c3GroupHessian125_02Chunk0]
theorem c3GroupHessian125_02_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian125_02 := by kernel_rfl
private def c3GroupHessian125_03Chunk0 : Poly := [([0,0], -20),([0,1], -4),([0,4], -4),([0,5], 40),([0,6], -16),([0,9], -36),([1,4], 4),([1,6], -8),([1,9], -4),([4,6], 4),([4,9], -8),([5,8], 40),([6,6], -8),([6,9], -8),([9,9], -16)]
def c3GroupHessian125_03 : Poly := List.flatten [c3GroupHessian125_03Chunk0]
theorem c3GroupHessian125_03_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian125_03 := by kernel_rfl
private def c3GroupHessian125_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 80),([0,9], 32),([2,2], 40),([2,8], 80),([7,7], 16),([7,9], 32),([8,8], 40),([9,9], 16)]
def c3GroupHessian125_11 : Poly := List.flatten [c3GroupHessian125_11Chunk0]
theorem c3GroupHessian125_11_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian125_11 := by kernel_rfl
private def c3GroupHessian125_12Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -32),([0,8], 40),([0,9], -32),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -16),([7,9], -32),([9,9], -16)]
def c3GroupHessian125_12 : Poly := List.flatten [c3GroupHessian125_12Chunk0]
theorem c3GroupHessian125_12_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian125_12 := by kernel_rfl
private def c3GroupHessian125_13Chunk0 : Poly := [([0,0], -56),([0,2], -40),([0,4], -8),([0,6], -4),([0,7], -16),([0,8], -80),([0,9], -32),([2,8], -40),([4,7], -8),([4,9], -8),([6,7], -4),([6,9], -4),([7,9], -16),([8,8], -40),([9,9], -16)]
def c3GroupHessian125_13 : Poly := List.flatten [c3GroupHessian125_13Chunk0]
theorem c3GroupHessian125_13_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian125_13 := by kernel_rfl
private def c3GroupHessian125_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 32),([0,9], 32),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 16),([7,9], 32),([9,9], 16)]
def c3GroupHessian125_22 : Poly := List.flatten [c3GroupHessian125_22Chunk0]
theorem c3GroupHessian125_22_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian125_22 := by kernel_rfl
private def c3GroupHessian125_23Chunk0 : Poly := [([0,0], -24),([0,3], -40),([0,4], 8),([0,5], -40),([0,6], 4),([0,7], 16),([0,8], -40),([0,9], 32),([3,8], -40),([4,7], 8),([4,9], 8),([5,8], -40),([6,7], 4),([6,9], 4),([7,9], 16),([9,9], 16)]
def c3GroupHessian125_23 : Poly := List.flatten [c3GroupHessian125_23Chunk0]
theorem c3GroupHessian125_23_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian125_23 := by kernel_rfl
private def c3GroupHessian125_33Chunk0 : Poly := [([0,0], 56),([0,4], 16),([0,6], 8),([0,8], 80),([0,9], 32),([4,4], 16),([4,6], -8),([4,9], 16),([6,6], 8),([6,9], 8),([8,8], 40),([9,9], 16)]
def c3GroupHessian125_33 : Poly := List.flatten [c3GroupHessian125_33Chunk0]
theorem c3GroupHessian125_33_check : sumFast (c3TensorGroup125.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian125_33 := by kernel_rfl
end D4.Secondary
