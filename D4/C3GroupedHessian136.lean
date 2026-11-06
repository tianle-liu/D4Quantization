import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup136_det_check : c3TensorGroup136.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 178)) = true := by kernel_rfl
private def c3GroupHessian136_00Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,6], 24),([0,9], 24),([1,1], 16),([1,6], 8),([1,9], 8),([5,5], 40),([6,6], 8),([6,9], 16),([9,9], 8)]
def c3GroupHessian136_00 : Poly := List.flatten [c3GroupHessian136_00Chunk0]
theorem c3GroupHessian136_00_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian136_00 := by kernel_rfl
private def c3GroupHessian136_01Chunk0 : Poly := [([0,0], 12),([0,1], 4),([0,5], -40),([0,6], 8),([0,7], -4),([0,9], 20),([1,7], -8),([1,9], 4),([2,5], -40),([5,8], -40),([6,7], 4),([6,9], 8),([7,9], 4),([9,9], 8)]
def c3GroupHessian136_01 : Poly := List.flatten [c3GroupHessian136_01Chunk0]
theorem c3GroupHessian136_01_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian136_01 := by kernel_rfl
private def c3GroupHessian136_02Chunk0 : Poly := [([0,0], -12),([0,1], -4),([0,5], -40),([0,6], -8),([0,7], 4),([0,9], -20),([1,7], 8),([1,9], -4),([3,5], -40),([5,5], -40),([6,7], -4),([6,9], -8),([7,9], -4),([9,9], -8)]
def c3GroupHessian136_02 : Poly := List.flatten [c3GroupHessian136_02Chunk0]
theorem c3GroupHessian136_02_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian136_02 := by kernel_rfl
private def c3GroupHessian136_03Chunk0 : Poly := [([0,0], -12),([0,1], -4),([0,4], 20),([0,5], 40),([0,6], -20),([0,9], -20),([1,4], 16),([1,6], -4),([1,9], -4),([4,6], 4),([4,9], 4),([5,8], 40),([6,6], -8),([6,9], -16),([9,9], -8)]
def c3GroupHessian136_03 : Poly := List.flatten [c3GroupHessian136_03Chunk0]
theorem c3GroupHessian136_03_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian136_03 := by kernel_rfl
private def c3GroupHessian136_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 80),([0,9], 16),([2,2], 40),([2,8], 80),([7,7], 16),([7,9], 8),([8,8], 40),([9,9], 8)]
def c3GroupHessian136_11 : Poly := List.flatten [c3GroupHessian136_11Chunk0]
theorem c3GroupHessian136_11_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian136_11 := by kernel_rfl
private def c3GroupHessian136_12Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -8),([0,8], 40),([0,9], -16),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -16),([7,9], -8),([9,9], -8)]
def c3GroupHessian136_12 : Poly := List.flatten [c3GroupHessian136_12Chunk0]
theorem c3GroupHessian136_12_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian136_12 := by kernel_rfl
private def c3GroupHessian136_13Chunk0 : Poly := [([0,0], -48),([0,2], -40),([0,4], 4),([0,6], -8),([0,7], -4),([0,8], -80),([0,9], -16),([2,8], -40),([4,7], -8),([4,9], 4),([6,7], -4),([6,9], -8),([7,9], -4),([8,8], -40),([9,9], -8)]
def c3GroupHessian136_13 : Poly := List.flatten [c3GroupHessian136_13Chunk0]
theorem c3GroupHessian136_13_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian136_13 := by kernel_rfl
private def c3GroupHessian136_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,7], 8),([0,9], 16),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 16),([7,9], 8),([9,9], 8)]
def c3GroupHessian136_22 : Poly := List.flatten [c3GroupHessian136_22Chunk0]
theorem c3GroupHessian136_22_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian136_22 := by kernel_rfl
private def c3GroupHessian136_23Chunk0 : Poly := [([0,0], -32),([0,3], -40),([0,4], -4),([0,5], -40),([0,6], 8),([0,7], 4),([0,8], -40),([0,9], 16),([3,8], -40),([4,7], 8),([4,9], -4),([5,8], -40),([6,7], 4),([6,9], 8),([7,9], 4),([9,9], 8)]
def c3GroupHessian136_23 : Poly := List.flatten [c3GroupHessian136_23Chunk0]
theorem c3GroupHessian136_23_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian136_23 := by kernel_rfl
private def c3GroupHessian136_33Chunk0 : Poly := [([0,0], 48),([0,4], -8),([0,6], 16),([0,8], 80),([0,9], 16),([4,4], 16),([4,6], -8),([4,9], -8),([6,6], 8),([6,9], 16),([8,8], 40),([9,9], 8)]
def c3GroupHessian136_33 : Poly := List.flatten [c3GroupHessian136_33Chunk0]
theorem c3GroupHessian136_33_check : sumFast (c3TensorGroup136.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian136_33 := by kernel_rfl
end D4.Secondary
