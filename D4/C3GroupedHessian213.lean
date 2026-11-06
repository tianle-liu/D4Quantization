import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup213_det_check : c3TensorGroup213.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 277)) = true := by kernel_rfl
private def c3GroupHessian213_00Chunk0 : Poly := [([0,0], 104),([0,1], 48),([0,5], 48),([0,6], 160),([0,9], 160),([1,1], 24),([1,5], 48),([5,5], 24),([6,6], 80),([6,9], 160),([9,9], 80)]
def c3GroupHessian213_00 : Poly := List.flatten [c3GroupHessian213_00Chunk0]
theorem c3GroupHessian213_00_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian213_00 := by kernel_rfl
private def c3GroupHessian213_01Chunk0 : Poly := [([0,0], 88),([0,1], 8),([0,2], 8),([0,5], 8),([0,6], 80),([0,7], 8),([0,8], 80),([0,9], 160),([1,2], 8),([1,7], 8),([2,5], 8),([5,7], 8),([6,8], 80),([6,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian213_01 : Poly := List.flatten [c3GroupHessian213_01Chunk0]
theorem c3GroupHessian213_01_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian213_01 := by kernel_rfl
private def c3GroupHessian213_02Chunk0 : Poly := [([0,0], -16),([0,1], -16),([0,3], -4),([0,5], -40),([0,7], -8),([0,9], -80),([1,3], -4),([1,5], -24),([1,7], -8),([3,5], -4),([5,5], -24),([5,7], -8),([6,9], -80),([9,9], -80)]
def c3GroupHessian213_02 : Poly := List.flatten [c3GroupHessian213_02Chunk0]
theorem c3GroupHessian213_02_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian213_02 := by kernel_rfl
private def c3GroupHessian213_03Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -240),([0,8], -80),([0,9], -240),([4,6], -80),([4,9], -80),([6,6], -80),([6,8], -80),([6,9], -160),([8,9], -80),([9,9], -80)]
def c3GroupHessian213_03 : Poly := List.flatten [c3GroupHessian213_03Chunk0]
theorem c3GroupHessian213_03_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian213_03 := by kernel_rfl
private def c3GroupHessian213_11Chunk0 : Poly := [([0,0], 104),([0,2], 48),([0,7], 48),([0,8], 160),([0,9], 160),([2,2], 24),([2,7], 48),([7,7], 24),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian213_11 : Poly := List.flatten [c3GroupHessian213_11Chunk0]
theorem c3GroupHessian213_11_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian213_11 := by kernel_rfl
private def c3GroupHessian213_12Chunk0 : Poly := [([0,0], -16),([0,2], -16),([0,3], -4),([0,5], -8),([0,7], -40),([0,9], -80),([2,3], -4),([2,5], -8),([2,7], -24),([3,7], -4),([5,7], -8),([7,7], -24),([8,9], -80),([9,9], -80)]
def c3GroupHessian213_12 : Poly := List.flatten [c3GroupHessian213_12Chunk0]
theorem c3GroupHessian213_12_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian213_12 := by kernel_rfl
private def c3GroupHessian213_13Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -80),([0,8], -240),([0,9], -240),([4,8], -80),([4,9], -80),([6,8], -80),([6,9], -80),([8,8], -80),([8,9], -160),([9,9], -80)]
def c3GroupHessian213_13 : Poly := List.flatten [c3GroupHessian213_13Chunk0]
theorem c3GroupHessian213_13_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian213_13 := by kernel_rfl
private def c3GroupHessian213_22Chunk0 : Poly := [([0,0], 32),([0,3], 48),([0,5], 32),([0,7], 32),([3,3], 32),([3,5], 8),([3,7], 8),([5,5], 24),([5,7], 16),([7,7], 24),([9,9], 80)]
def c3GroupHessian213_22 : Poly := List.flatten [c3GroupHessian213_22Chunk0]
theorem c3GroupHessian213_22_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian213_22 := by kernel_rfl
private def c3GroupHessian213_23Chunk0 : Poly := [([0,9], 160),([4,9], 80),([6,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian213_23 : Poly := List.flatten [c3GroupHessian213_23Chunk0]
theorem c3GroupHessian213_23_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian213_23 := by kernel_rfl
private def c3GroupHessian213_33Chunk0 : Poly := [([0,0], 320),([0,4], 320),([0,6], 320),([0,8], 320),([0,9], 320),([4,4], 80),([4,6], 160),([4,8], 160),([4,9], 160),([6,6], 80),([6,8], 160),([6,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian213_33 : Poly := List.flatten [c3GroupHessian213_33Chunk0]
theorem c3GroupHessian213_33_check : sumFast (c3TensorGroup213.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian213_33 := by kernel_rfl
end D4.Secondary
