import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup133_det_check : c3TensorGroup133.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 173)) = true := by kernel_rfl
private def c3GroupHessian133_00Chunk0 : Poly := [([0,0], 128),([0,1], 128),([0,6], 128),([0,9], 128),([1,1], 32),([1,6], 64),([1,9], 64),([5,5], 80),([6,6], 32),([6,9], 64),([9,9], 32)]
def c3GroupHessian133_00 : Poly := List.flatten [c3GroupHessian133_00Chunk0]
theorem c3GroupHessian133_00_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian133_00 := by kernel_rfl
private def c3GroupHessian133_01Chunk0 : Poly := [([0,0], 64),([0,1], 32),([0,5], -80),([0,6], 32),([0,7], -8),([0,9], 96),([1,7], -4),([1,9], 32),([2,5], -80),([5,8], -80),([6,7], -4),([6,9], 32),([7,9], -4),([9,9], 32)]
def c3GroupHessian133_01 : Poly := List.flatten [c3GroupHessian133_01Chunk0]
theorem c3GroupHessian133_01_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian133_01 := by kernel_rfl
private def c3GroupHessian133_02Chunk0 : Poly := [([0,0], -64),([0,1], -32),([0,5], -80),([0,6], -32),([0,7], 8),([0,9], -96),([1,7], 4),([1,9], -32),([3,5], -80),([5,5], -80),([6,7], 4),([6,9], -32),([7,9], 4),([9,9], -32)]
def c3GroupHessian133_02 : Poly := List.flatten [c3GroupHessian133_02Chunk0]
theorem c3GroupHessian133_02_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian133_02 := by kernel_rfl
private def c3GroupHessian133_03Chunk0 : Poly := [([0,0], -64),([0,1], -32),([0,4], -8),([0,5], 80),([0,6], -96),([0,9], -96),([1,4], -4),([1,6], -32),([1,9], -32),([4,6], -4),([4,9], -4),([5,8], 80),([6,6], -32),([6,9], -64),([9,9], -32)]
def c3GroupHessian133_03 : Poly := List.flatten [c3GroupHessian133_03Chunk0]
theorem c3GroupHessian133_03_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian133_03 := by kernel_rfl
private def c3GroupHessian133_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], -8),([0,8], 160),([0,9], 64),([2,2], 80),([2,8], 160),([7,7], 24),([7,9], -8),([8,8], 80),([9,9], 32)]
def c3GroupHessian133_11 : Poly := List.flatten [c3GroupHessian133_11Chunk0]
theorem c3GroupHessian133_11_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian133_11 := by kernel_rfl
private def c3GroupHessian133_12Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,3], 80),([0,5], 80),([0,7], 8),([0,8], 80),([0,9], -64),([2,3], 80),([2,5], 80),([3,8], 80),([5,8], 80),([7,7], -24),([7,9], 8),([9,9], -32)]
def c3GroupHessian133_12 : Poly := List.flatten [c3GroupHessian133_12Chunk0]
theorem c3GroupHessian133_12_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian133_12 := by kernel_rfl
private def c3GroupHessian133_13Chunk0 : Poly := [([0,0], -112),([0,2], -80),([0,4], -4),([0,6], -32),([0,7], 4),([0,8], -160),([0,9], -64),([2,8], -80),([4,7], 8),([4,9], -4),([6,7], 4),([6,9], -32),([7,9], 4),([8,8], -80),([9,9], -32)]
def c3GroupHessian133_13 : Poly := List.flatten [c3GroupHessian133_13Chunk0]
theorem c3GroupHessian133_13_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian133_13 := by kernel_rfl
private def c3GroupHessian133_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], 160),([0,7], -8),([0,9], 64),([3,3], 80),([3,5], 160),([5,5], 80),([7,7], 24),([7,9], -8),([9,9], 32)]
def c3GroupHessian133_22 : Poly := List.flatten [c3GroupHessian133_22Chunk0]
theorem c3GroupHessian133_22_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian133_22 := by kernel_rfl
private def c3GroupHessian133_23Chunk0 : Poly := [([0,0], -48),([0,3], -80),([0,4], 4),([0,5], -80),([0,6], 32),([0,7], -4),([0,8], -80),([0,9], 64),([3,8], -80),([4,7], -8),([4,9], 4),([5,8], -80),([6,7], -4),([6,9], 32),([7,9], -4),([9,9], 32)]
def c3GroupHessian133_23 : Poly := List.flatten [c3GroupHessian133_23Chunk0]
theorem c3GroupHessian133_23_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian133_23 := by kernel_rfl
private def c3GroupHessian133_33Chunk0 : Poly := [([0,0], 112),([0,4], 8),([0,6], 64),([0,8], 160),([0,9], 64),([4,4], 24),([4,6], 8),([4,9], 8),([6,6], 32),([6,9], 64),([8,8], 80),([9,9], 32)]
def c3GroupHessian133_33 : Poly := List.flatten [c3GroupHessian133_33Chunk0]
theorem c3GroupHessian133_33_check : sumFast (c3TensorGroup133.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian133_33 := by kernel_rfl
end D4.Secondary
