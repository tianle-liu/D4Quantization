import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup102_det_check : c3TensorGroup102.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 133)) = true := by kernel_rfl
private def c3GroupHessian102_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 80),([0,9], 32),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40),([9,9], 16)]
def c3GroupHessian102_00 : Poly := List.flatten [c3GroupHessian102_00Chunk0]
theorem c3GroupHessian102_00_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian102_00 := by kernel_rfl
private def c3GroupHessian102_01Chunk0 : Poly := [([0,0], -24),([0,1], -40),([0,2], -40),([0,5], -40),([0,6], -40),([0,7], -40),([0,8], -40),([0,9], 32),([1,2], -40),([1,7], -40),([1,8], -40),([2,5], -40),([2,6], -40),([5,7], -40),([5,8], -40),([6,7], -40),([6,8], -40),([9,9], 16)]
def c3GroupHessian102_01 : Poly := List.flatten [c3GroupHessian102_01Chunk0]
theorem c3GroupHessian102_01_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian102_01 := by kernel_rfl
private def c3GroupHessian102_02Chunk0 : Poly := [([0,0], -24),([0,3], -8),([0,5], -40),([0,7], 40),([0,9], -40),([1,5], -40),([1,7], 40),([3,9], -8),([5,5], -40),([5,6], -40),([5,7], 40),([6,7], 40),([9,9], -16)]
def c3GroupHessian102_02 : Poly := List.flatten [c3GroupHessian102_02Chunk0]
theorem c3GroupHessian102_02_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian102_02 := by kernel_rfl
private def c3GroupHessian102_03Chunk0 : Poly := [([0,4], 4),([0,6], -40),([0,8], 40),([0,9], -16),([1,6], -40),([1,8], 40),([4,9], 4),([5,6], -40),([5,8], 40),([6,6], -40),([6,8], 40),([9,9], -16)]
def c3GroupHessian102_03 : Poly := List.flatten [c3GroupHessian102_03Chunk0]
theorem c3GroupHessian102_03_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian102_03 := by kernel_rfl
private def c3GroupHessian102_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 80),([0,9], 32),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40),([9,9], 16)]
def c3GroupHessian102_11 : Poly := List.flatten [c3GroupHessian102_11Chunk0]
theorem c3GroupHessian102_11_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian102_11 := by kernel_rfl
private def c3GroupHessian102_12Chunk0 : Poly := [([0,0], -24),([0,3], -8),([0,5], 40),([0,7], -40),([0,9], -40),([2,5], 40),([2,7], -40),([3,9], -8),([5,7], 40),([5,8], 40),([7,7], -40),([7,8], -40),([9,9], -16)]
def c3GroupHessian102_12 : Poly := List.flatten [c3GroupHessian102_12Chunk0]
theorem c3GroupHessian102_12_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian102_12 := by kernel_rfl
private def c3GroupHessian102_13Chunk0 : Poly := [([0,4], 4),([0,6], 40),([0,8], -40),([0,9], -16),([2,6], 40),([2,8], -40),([4,9], 4),([6,7], 40),([6,8], 40),([7,8], -40),([8,8], -40),([9,9], -16)]
def c3GroupHessian102_13 : Poly := List.flatten [c3GroupHessian102_13Chunk0]
theorem c3GroupHessian102_13_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian102_13 := by kernel_rfl
private def c3GroupHessian102_22Chunk0 : Poly := [([0,0], 48),([0,3], 48),([0,9], 48),([3,3], 16),([3,9], 16),([5,5], 40),([5,7], -80),([7,7], 40),([9,9], 16)]
def c3GroupHessian102_22 : Poly := List.flatten [c3GroupHessian102_22Chunk0]
theorem c3GroupHessian102_22_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian102_22 := by kernel_rfl
private def c3GroupHessian102_23Chunk0 : Poly := [([0,9], 24),([3,4], 4),([3,9], 8),([4,9], -4),([5,6], 40),([5,8], -40),([6,7], -40),([7,8], 40),([9,9], 16)]
def c3GroupHessian102_23 : Poly := List.flatten [c3GroupHessian102_23Chunk0]
theorem c3GroupHessian102_23_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian102_23 := by kernel_rfl
private def c3GroupHessian102_33Chunk0 : Poly := [([4,4], 8),([4,9], -8),([6,6], 40),([6,8], -80),([8,8], 40),([9,9], 16)]
def c3GroupHessian102_33 : Poly := List.flatten [c3GroupHessian102_33Chunk0]
theorem c3GroupHessian102_33_check : sumFast (c3TensorGroup102.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian102_33 := by kernel_rfl
end D4.Secondary
