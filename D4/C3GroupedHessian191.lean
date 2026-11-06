import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup191_det_check : c3TensorGroup191.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 245)) = true := by kernel_rfl
private def c3GroupHessian191_00Chunk0 : Poly := [([0,0], 104),([0,1], 48),([0,5], 160),([0,6], 48),([0,9], 160),([1,1], 24),([1,6], 48),([5,5], 80),([5,9], 160),([6,6], 24),([9,9], 80)]
def c3GroupHessian191_00 : Poly := List.flatten [c3GroupHessian191_00Chunk0]
theorem c3GroupHessian191_00_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian191_00 := by kernel_rfl
private def c3GroupHessian191_01Chunk0 : Poly := [([0,0], 88),([0,1], 8),([0,2], 8),([0,5], 80),([0,6], 8),([0,7], 80),([0,8], 8),([0,9], 160),([1,2], 8),([1,8], 8),([2,6], 8),([5,7], 80),([5,9], 80),([6,8], 8),([7,9], 80),([9,9], 80)]
def c3GroupHessian191_01 : Poly := List.flatten [c3GroupHessian191_01Chunk0]
theorem c3GroupHessian191_01_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian191_01 := by kernel_rfl
private def c3GroupHessian191_02Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -240),([0,7], -80),([0,9], -240),([3,5], -80),([3,9], -80),([5,5], -80),([5,7], -80),([5,9], -160),([7,9], -80),([9,9], -80)]
def c3GroupHessian191_02 : Poly := List.flatten [c3GroupHessian191_02Chunk0]
theorem c3GroupHessian191_02_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian191_02 := by kernel_rfl
private def c3GroupHessian191_03Chunk0 : Poly := [([0,0], -16),([0,1], -16),([0,4], -4),([0,6], -40),([0,8], -8),([0,9], -80),([1,4], -4),([1,6], -24),([1,8], -8),([4,6], -4),([5,9], -80),([6,6], -24),([6,8], -8),([9,9], -80)]
def c3GroupHessian191_03 : Poly := List.flatten [c3GroupHessian191_03Chunk0]
theorem c3GroupHessian191_03_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian191_03 := by kernel_rfl
private def c3GroupHessian191_11Chunk0 : Poly := [([0,0], 104),([0,2], 48),([0,7], 160),([0,8], 48),([0,9], 160),([2,2], 24),([2,8], 48),([7,7], 80),([7,9], 160),([8,8], 24),([9,9], 80)]
def c3GroupHessian191_11 : Poly := List.flatten [c3GroupHessian191_11Chunk0]
theorem c3GroupHessian191_11_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian191_11 := by kernel_rfl
private def c3GroupHessian191_12Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -80),([0,7], -240),([0,9], -240),([3,7], -80),([3,9], -80),([5,7], -80),([5,9], -80),([7,7], -80),([7,9], -160),([9,9], -80)]
def c3GroupHessian191_12 : Poly := List.flatten [c3GroupHessian191_12Chunk0]
theorem c3GroupHessian191_12_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian191_12 := by kernel_rfl
private def c3GroupHessian191_13Chunk0 : Poly := [([0,0], -16),([0,2], -16),([0,4], -4),([0,6], -8),([0,8], -40),([0,9], -80),([2,4], -4),([2,6], -8),([2,8], -24),([4,8], -4),([6,8], -8),([7,9], -80),([8,8], -24),([9,9], -80)]
def c3GroupHessian191_13 : Poly := List.flatten [c3GroupHessian191_13Chunk0]
theorem c3GroupHessian191_13_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian191_13 := by kernel_rfl
private def c3GroupHessian191_22Chunk0 : Poly := [([0,0], 320),([0,3], 320),([0,5], 320),([0,7], 320),([0,9], 320),([3,3], 80),([3,5], 160),([3,7], 160),([3,9], 160),([5,5], 80),([5,7], 160),([5,9], 160),([7,7], 80),([7,9], 160),([9,9], 80)]
def c3GroupHessian191_22 : Poly := List.flatten [c3GroupHessian191_22Chunk0]
theorem c3GroupHessian191_22_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian191_22 := by kernel_rfl
private def c3GroupHessian191_23Chunk0 : Poly := [([0,9], 160),([3,9], 80),([5,9], 80),([7,9], 80),([9,9], 80)]
def c3GroupHessian191_23 : Poly := List.flatten [c3GroupHessian191_23Chunk0]
theorem c3GroupHessian191_23_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian191_23 := by kernel_rfl
private def c3GroupHessian191_33Chunk0 : Poly := [([0,0], 32),([0,4], 48),([0,6], 32),([0,8], 32),([4,4], 32),([4,6], 8),([4,8], 8),([6,6], 24),([6,8], 16),([8,8], 24),([9,9], 80)]
def c3GroupHessian191_33 : Poly := List.flatten [c3GroupHessian191_33Chunk0]
theorem c3GroupHessian191_33_check : sumFast (c3TensorGroup191.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian191_33 := by kernel_rfl
end D4.Secondary
