import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup204_det_check : c3TensorGroup204.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 265)) = true := by kernel_rfl
private def c3GroupHessian204_00Chunk0 : Poly := [([0,0], 112),([0,1], 80),([0,5], -8),([0,6], 160),([0,9], 160),([1,1], 80),([1,5], -40),([5,5], 24),([6,6], 80),([6,9], 160),([9,9], 80)]
def c3GroupHessian204_00 : Poly := List.flatten [c3GroupHessian204_00Chunk0]
theorem c3GroupHessian204_00_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian204_00 := by kernel_rfl
private def c3GroupHessian204_01Chunk0 : Poly := [([0,0], 112),([0,1], 40),([0,2], 40),([0,5], -4),([0,6], 80),([0,7], -4),([0,8], 80),([0,9], 160),([1,2], 80),([1,7], -20),([2,5], -20),([5,7], 8),([6,8], 80),([6,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian204_01 : Poly := List.flatten [c3GroupHessian204_01Chunk0]
theorem c3GroupHessian204_01_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian204_01 := by kernel_rfl
private def c3GroupHessian204_02Chunk0 : Poly := [([0,0], 8),([0,1], 40),([0,3], 40),([0,5], -12),([0,7], 4),([0,9], -80),([1,3], 80),([1,5], 20),([1,7], 20),([3,5], -20),([5,5], -24),([5,7], -8),([6,9], -80),([9,9], -80)]
def c3GroupHessian204_02 : Poly := List.flatten [c3GroupHessian204_02Chunk0]
theorem c3GroupHessian204_02_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian204_02 := by kernel_rfl
private def c3GroupHessian204_03Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -240),([0,8], -80),([0,9], -240),([4,6], -80),([4,9], -80),([6,6], -80),([6,8], -80),([6,9], -160),([8,9], -80),([9,9], -80)]
def c3GroupHessian204_03 : Poly := List.flatten [c3GroupHessian204_03Chunk0]
theorem c3GroupHessian204_03_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian204_03 := by kernel_rfl
private def c3GroupHessian204_11Chunk0 : Poly := [([0,0], 112),([0,2], 80),([0,7], -8),([0,8], 160),([0,9], 160),([2,2], 80),([2,7], -40),([7,7], 24),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian204_11 : Poly := List.flatten [c3GroupHessian204_11Chunk0]
theorem c3GroupHessian204_11_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian204_11 := by kernel_rfl
private def c3GroupHessian204_12Chunk0 : Poly := [([0,0], 8),([0,2], 40),([0,3], 40),([0,5], 4),([0,7], -12),([0,9], -80),([2,3], 80),([2,5], 20),([2,7], 20),([3,7], -20),([5,7], -8),([7,7], -24),([8,9], -80),([9,9], -80)]
def c3GroupHessian204_12 : Poly := List.flatten [c3GroupHessian204_12Chunk0]
theorem c3GroupHessian204_12_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian204_12 := by kernel_rfl
private def c3GroupHessian204_13Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -80),([0,8], -240),([0,9], -240),([4,8], -80),([4,9], -80),([6,8], -80),([6,9], -80),([8,8], -80),([8,9], -160),([9,9], -80)]
def c3GroupHessian204_13 : Poly := List.flatten [c3GroupHessian204_13Chunk0]
theorem c3GroupHessian204_13_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian204_13 := by kernel_rfl
private def c3GroupHessian204_22Chunk0 : Poly := [([0,0], 32),([0,3], 80),([0,5], 32),([0,7], 32),([3,3], 80),([3,5], 40),([3,7], 40),([5,5], 24),([5,7], 16),([7,7], 24),([9,9], 80)]
def c3GroupHessian204_22 : Poly := List.flatten [c3GroupHessian204_22Chunk0]
theorem c3GroupHessian204_22_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian204_22 := by kernel_rfl
private def c3GroupHessian204_23Chunk0 : Poly := [([0,9], 160),([4,9], 80),([6,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian204_23 : Poly := List.flatten [c3GroupHessian204_23Chunk0]
theorem c3GroupHessian204_23_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian204_23 := by kernel_rfl
private def c3GroupHessian204_33Chunk0 : Poly := [([0,0], 320),([0,4], 320),([0,6], 320),([0,8], 320),([0,9], 320),([4,4], 80),([4,6], 160),([4,8], 160),([4,9], 160),([6,6], 80),([6,8], 160),([6,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian204_33 : Poly := List.flatten [c3GroupHessian204_33Chunk0]
theorem c3GroupHessian204_33_check : sumFast (c3TensorGroup204.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian204_33 := by kernel_rfl
end D4.Secondary
