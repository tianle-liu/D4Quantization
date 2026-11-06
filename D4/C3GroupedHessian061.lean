import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup61_det_check : c3TensorGroup61.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 84)) = true := by kernel_rfl
private def c3GroupHessian61_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 40),([0,9], 32),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 40),([6,9], 40),([9,9], 16)]
def c3GroupHessian61_00 : Poly := List.flatten [c3GroupHessian61_00Chunk0]
theorem c3GroupHessian61_00_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian61_00 := by kernel_rfl
private def c3GroupHessian61_01Chunk0 : Poly := [([0,0], 8),([0,2], -8),([0,7], -8),([0,8], -40),([0,9], 24),([1,8], -40),([2,6], -20),([2,9], -8),([5,8], -40),([6,7], -20),([6,9], 20),([7,9], -8),([9,9], 16)]
def c3GroupHessian61_01 : Poly := List.flatten [c3GroupHessian61_01Chunk0]
theorem c3GroupHessian61_01_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian61_01 := by kernel_rfl
private def c3GroupHessian61_02Chunk0 : Poly := [([0,0], -44),([0,1], -40),([0,3], 4),([0,5], -80),([0,7], 8),([0,9], -20),([1,5], -40),([3,9], 4),([5,5], -40),([6,7], 20),([6,9], -20),([7,9], 8),([9,9], -16)]
def c3GroupHessian61_02 : Poly := List.flatten [c3GroupHessian61_02Chunk0]
theorem c3GroupHessian61_02_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian61_02 := by kernel_rfl
private def c3GroupHessian61_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -40),([0,8], 40),([0,9], -32),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -40),([6,9], -40),([9,9], -16)]
def c3GroupHessian61_03 : Poly := List.flatten [c3GroupHessian61_03Chunk0]
theorem c3GroupHessian61_03_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian61_03 := by kernel_rfl
private def c3GroupHessian61_11Chunk0 : Poly := [([0,0], 16),([0,2], 16),([0,7], 16),([0,9], 16),([2,2], 16),([2,7], 32),([2,9], -16),([7,7], 16),([7,9], -16),([8,8], 40),([9,9], 16)]
def c3GroupHessian61_11 : Poly := List.flatten [c3GroupHessian61_11Chunk0]
theorem c3GroupHessian61_11_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian61_11 := by kernel_rfl
private def c3GroupHessian61_12Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,3], 8),([0,7], -12),([0,8], 40),([0,9], -12),([2,3], 4),([2,7], -16),([2,9], 8),([3,7], 4),([3,9], 4),([5,8], 40),([7,7], -16),([7,9], 16),([9,9], -16)]
def c3GroupHessian61_12 : Poly := List.flatten [c3GroupHessian61_12Chunk0]
theorem c3GroupHessian61_12_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian61_12 := by kernel_rfl
private def c3GroupHessian61_13Chunk0 : Poly := [([0,0], -8),([0,2], 8),([0,7], 8),([0,8], -40),([0,9], -24),([2,6], 20),([2,9], 8),([4,8], -40),([6,7], 20),([6,9], -20),([7,9], 8),([8,8], -40),([9,9], -16)]
def c3GroupHessian61_13 : Poly := List.flatten [c3GroupHessian61_13Chunk0]
theorem c3GroupHessian61_13_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian61_13 := by kernel_rfl
private def c3GroupHessian61_22Chunk0 : Poly := [([0,0], 48),([0,5], 80),([0,7], 8),([0,9], 8),([3,3], 8),([3,7], -8),([3,9], -8),([5,5], 40),([7,7], 16),([7,9], -16),([9,9], 16)]
def c3GroupHessian61_22 : Poly := List.flatten [c3GroupHessian61_22Chunk0]
theorem c3GroupHessian61_22_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian61_22 := by kernel_rfl
private def c3GroupHessian61_23Chunk0 : Poly := [([0,0], -36),([0,3], -4),([0,4], -40),([0,5], -40),([0,7], -8),([0,8], -40),([0,9], 20),([3,9], -4),([4,5], -40),([5,8], -40),([6,7], -20),([6,9], 20),([7,9], -8),([9,9], 16)]
def c3GroupHessian61_23 : Poly := List.flatten [c3GroupHessian61_23Chunk0]
theorem c3GroupHessian61_23_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian61_23 := by kernel_rfl
private def c3GroupHessian61_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 40),([0,8], 80),([0,9], 32),([4,4], 40),([4,8], 80),([6,6], 40),([6,9], 40),([8,8], 40),([9,9], 16)]
def c3GroupHessian61_33 : Poly := List.flatten [c3GroupHessian61_33Chunk0]
theorem c3GroupHessian61_33_check : sumFast (c3TensorGroup61.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian61_33 := by kernel_rfl
end D4.Secondary
