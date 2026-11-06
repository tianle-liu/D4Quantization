import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup149_det_check : c2TensorGroup149.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 187)) = true := by kernel_rfl
private def c2GroupHessian149_00Chunk0 : Poly := [([0,0], 32),([0,1], 32),([0,5], 32),([1,1], 24),([1,5], -8),([5,5], 32),([6,6], 80)]
def c2GroupHessian149_00 : Poly := List.flatten [c2GroupHessian149_00Chunk0]
theorem c2GroupHessian149_00_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian149_00 := by kernel_rfl
private def c2GroupHessian149_01Chunk0 : Poly := [([0,0], 16),([0,1], 8),([0,5], -4),([0,6], -80),([0,8], 16),([1,8], 8),([2,6], -80),([5,8], -4),([6,7], -80)]
def c2GroupHessian149_01 : Poly := List.flatten [c2GroupHessian149_01Chunk0]
theorem c2GroupHessian149_01_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian149_01 := by kernel_rfl
private def c2GroupHessian149_02Chunk0 : Poly := [([0,0], -16),([0,1], 8),([0,3], 16),([0,5], -36),([0,6], 80),([1,3], 24),([1,5], 4),([3,5], -4),([5,5], -32),([6,7], 80),([6,9], 80)]
def c2GroupHessian149_02 : Poly := List.flatten [c2GroupHessian149_02Chunk0]
theorem c2GroupHessian149_02_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian149_02 := by kernel_rfl
private def c2GroupHessian149_03Chunk0 : Poly := [([0,0], -16),([0,1], -8),([0,5], 4),([0,6], -80),([0,8], -16),([1,8], -8),([4,6], -80),([5,8], 4),([6,6], -80),([6,9], -80)]
def c2GroupHessian149_03 : Poly := List.flatten [c2GroupHessian149_03Chunk0]
theorem c2GroupHessian149_03_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian149_03 := by kernel_rfl
private def c2GroupHessian149_11Chunk0 : Poly := [([0,0], 104),([0,2], 160),([0,7], 160),([0,8], 48),([2,2], 80),([2,7], 160),([7,7], 80),([8,8], 24)]
def c2GroupHessian149_11 : Poly := List.flatten [c2GroupHessian149_11Chunk0]
theorem c2GroupHessian149_11_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian149_11 := by kernel_rfl
private def c2GroupHessian149_12Chunk0 : Poly := [([0,0], -88),([0,2], -80),([0,3], 8),([0,5], 4),([0,7], -160),([0,8], -8),([0,9], -80),([2,7], -80),([2,9], -80),([3,8], 8),([5,8], 4),([7,7], -80),([7,9], -80)]
def c2GroupHessian149_12 : Poly := List.flatten [c2GroupHessian149_12Chunk0]
theorem c2GroupHessian149_12_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian149_12 := by kernel_rfl
private def c2GroupHessian149_13Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,4], 80),([0,6], 80),([0,7], 80),([0,8], -48),([0,9], 80),([2,4], 80),([2,6], 80),([2,9], 80),([4,7], 80),([6,7], 80),([7,9], 80),([8,8], -24)]
def c2GroupHessian149_13 : Poly := List.flatten [c2GroupHessian149_13Chunk0]
theorem c2GroupHessian149_13_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian149_13 := by kernel_rfl
private def c2GroupHessian149_22Chunk0 : Poly := [([0,0], 104),([0,3], 16),([0,5], 40),([0,7], 160),([0,9], 160),([3,3], 24),([3,5], 8),([5,5], 32),([7,7], 80),([7,9], 160),([9,9], 80)]
def c2GroupHessian149_22 : Poly := List.flatten [c2GroupHessian149_22Chunk0]
theorem c2GroupHessian149_22_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian149_22 := by kernel_rfl
private def c2GroupHessian149_23Chunk0 : Poly := [([0,0], -72),([0,3], -8),([0,4], -80),([0,5], -4),([0,6], -80),([0,7], -80),([0,8], 8),([0,9], -160),([3,8], -8),([4,7], -80),([4,9], -80),([5,8], -4),([6,7], -80),([6,9], -80),([7,9], -80),([9,9], -80)]
def c2GroupHessian149_23 : Poly := List.flatten [c2GroupHessian149_23Chunk0]
theorem c2GroupHessian149_23_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian149_23 := by kernel_rfl
private def c2GroupHessian149_33Chunk0 : Poly := [([0,0], 104),([0,4], 160),([0,6], 160),([0,8], 48),([0,9], 160),([4,4], 80),([4,6], 160),([4,9], 160),([6,6], 80),([6,9], 160),([8,8], 24),([9,9], 80)]
def c2GroupHessian149_33 : Poly := List.flatten [c2GroupHessian149_33Chunk0]
theorem c2GroupHessian149_33_check : sumFast (c2TensorGroup149.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian149_33 := by kernel_rfl
end D4.Secondary
