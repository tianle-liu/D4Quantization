import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup133_det_check : c2TensorGroup133.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 168)) = true := by kernel_rfl
private def c2GroupHessian133_00Chunk0 : Poly := [([0,0], 32),([0,1], 32),([0,6], 32),([1,1], 24),([1,6], -8),([5,5], 80),([6,6], 32)]
def c2GroupHessian133_00 : Poly := List.flatten [c2GroupHessian133_00Chunk0]
theorem c2GroupHessian133_00_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian133_00 := by kernel_rfl
private def c2GroupHessian133_01Chunk0 : Poly := [([0,0], 16),([0,1], 8),([0,5], -80),([0,6], -4),([0,7], 16),([1,7], 8),([2,5], -80),([5,8], -80),([6,7], -4)]
def c2GroupHessian133_01 : Poly := List.flatten [c2GroupHessian133_01Chunk0]
theorem c2GroupHessian133_01_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian133_01 := by kernel_rfl
private def c2GroupHessian133_02Chunk0 : Poly := [([0,0], -16),([0,1], -8),([0,5], -80),([0,6], 4),([0,7], -16),([1,7], -8),([3,5], -80),([5,5], -80),([5,9], -80),([6,7], 4)]
def c2GroupHessian133_02 : Poly := List.flatten [c2GroupHessian133_02Chunk0]
theorem c2GroupHessian133_02_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian133_02 := by kernel_rfl
private def c2GroupHessian133_03Chunk0 : Poly := [([0,0], -16),([0,1], 8),([0,4], 16),([0,5], 80),([0,6], -36),([1,4], 24),([1,6], 4),([4,6], -4),([5,8], 80),([5,9], 80),([6,6], -32)]
def c2GroupHessian133_03 : Poly := List.flatten [c2GroupHessian133_03Chunk0]
theorem c2GroupHessian133_03_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian133_03 := by kernel_rfl
private def c2GroupHessian133_11Chunk0 : Poly := [([0,0], 104),([0,2], 160),([0,7], 48),([0,8], 160),([2,2], 80),([2,8], 160),([7,7], 24),([8,8], 80)]
def c2GroupHessian133_11 : Poly := List.flatten [c2GroupHessian133_11Chunk0]
theorem c2GroupHessian133_11_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian133_11 := by kernel_rfl
private def c2GroupHessian133_12Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,3], 80),([0,5], 80),([0,7], -48),([0,8], 80),([0,9], 80),([2,3], 80),([2,5], 80),([2,9], 80),([3,8], 80),([5,8], 80),([7,7], -24),([8,9], 80)]
def c2GroupHessian133_12 : Poly := List.flatten [c2GroupHessian133_12Chunk0]
theorem c2GroupHessian133_12_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian133_12 := by kernel_rfl
private def c2GroupHessian133_13Chunk0 : Poly := [([0,0], -88),([0,2], -80),([0,4], 8),([0,6], 4),([0,7], -8),([0,8], -160),([0,9], -80),([2,8], -80),([2,9], -80),([4,7], 8),([6,7], 4),([8,8], -80),([8,9], -80)]
def c2GroupHessian133_13 : Poly := List.flatten [c2GroupHessian133_13Chunk0]
theorem c2GroupHessian133_13_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian133_13 := by kernel_rfl
private def c2GroupHessian133_22Chunk0 : Poly := [([0,0], 104),([0,3], 160),([0,5], 160),([0,7], 48),([0,9], 160),([3,3], 80),([3,5], 160),([3,9], 160),([5,5], 80),([5,9], 160),([7,7], 24),([9,9], 80)]
def c2GroupHessian133_22 : Poly := List.flatten [c2GroupHessian133_22Chunk0]
theorem c2GroupHessian133_22_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian133_22 := by kernel_rfl
private def c2GroupHessian133_23Chunk0 : Poly := [([0,0], -72),([0,3], -80),([0,4], -8),([0,5], -80),([0,6], -4),([0,7], 8),([0,8], -80),([0,9], -160),([3,8], -80),([3,9], -80),([4,7], -8),([5,8], -80),([5,9], -80),([6,7], -4),([8,9], -80),([9,9], -80)]
def c2GroupHessian133_23 : Poly := List.flatten [c2GroupHessian133_23Chunk0]
theorem c2GroupHessian133_23_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian133_23 := by kernel_rfl
private def c2GroupHessian133_33Chunk0 : Poly := [([0,0], 104),([0,4], 16),([0,6], 40),([0,8], 160),([0,9], 160),([4,4], 24),([4,6], 8),([6,6], 32),([8,8], 80),([8,9], 160),([9,9], 80)]
def c2GroupHessian133_33 : Poly := List.flatten [c2GroupHessian133_33Chunk0]
theorem c2GroupHessian133_33_check : sumFast (c2TensorGroup133.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian133_33 := by kernel_rfl
end D4.Secondary
