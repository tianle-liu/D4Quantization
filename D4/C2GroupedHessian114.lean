import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup114_det_check : c2TensorGroup114.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 146)) = true := by kernel_rfl
private def c2GroupHessian114_00Chunk0 : Poly := [([0,0], 112),([0,1], -8),([0,5], 160),([0,6], 160),([1,1], 24),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian114_00 : Poly := List.flatten [c2GroupHessian114_00Chunk0]
theorem c2GroupHessian114_00_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian114_00 := by kernel_rfl
private def c2GroupHessian114_01Chunk0 : Poly := [([0,0], 64),([0,1], -8),([0,2], -80),([0,7], 32),([0,8], 32),([1,7], -4),([1,8], -4),([2,5], -80),([2,6], -80)]
def c2GroupHessian114_01 : Poly := List.flatten [c2GroupHessian114_01Chunk0]
theorem c2GroupHessian114_01_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian114_01 := by kernel_rfl
private def c2GroupHessian114_02Chunk0 : Poly := [([0,0], -112),([0,1], 4),([0,3], -80),([0,5], -160),([0,6], -80),([0,7], -32),([0,9], -4),([1,7], 4),([1,9], 8),([3,5], -80),([3,6], -80),([5,5], -80),([5,6], -80)]
def c2GroupHessian114_02 : Poly := List.flatten [c2GroupHessian114_02Chunk0]
theorem c2GroupHessian114_02_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian114_02 := by kernel_rfl
private def c2GroupHessian114_03Chunk0 : Poly := [([0,0], -112),([0,1], 4),([0,4], -80),([0,5], -80),([0,6], -160),([0,8], -32),([0,9], 4),([1,8], 4),([1,9], -8),([4,5], -80),([4,6], -80),([5,6], -80),([6,6], -80)]
def c2GroupHessian114_03 : Poly := List.flatten [c2GroupHessian114_03Chunk0]
theorem c2GroupHessian114_03_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian114_03 := by kernel_rfl
private def c2GroupHessian114_11Chunk0 : Poly := [([0,0], 128),([0,7], 128),([0,8], 128),([2,2], 80),([7,7], 32),([7,8], 64),([8,8], 32)]
def c2GroupHessian114_11 : Poly := List.flatten [c2GroupHessian114_11Chunk0]
theorem c2GroupHessian114_11_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian114_11 := by kernel_rfl
private def c2GroupHessian114_12Chunk0 : Poly := [([0,0], -64),([0,2], 80),([0,7], -96),([0,8], -32),([0,9], -8),([2,3], 80),([2,5], 80),([7,7], -32),([7,8], -32),([7,9], -4),([8,9], -4)]
def c2GroupHessian114_12 : Poly := List.flatten [c2GroupHessian114_12Chunk0]
theorem c2GroupHessian114_12_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian114_12 := by kernel_rfl
private def c2GroupHessian114_13Chunk0 : Poly := [([0,0], -64),([0,2], 80),([0,7], -32),([0,8], -96),([0,9], 8),([2,4], 80),([2,6], 80),([7,8], -32),([7,9], 4),([8,8], -32),([8,9], 4)]
def c2GroupHessian114_13 : Poly := List.flatten [c2GroupHessian114_13Chunk0]
theorem c2GroupHessian114_13_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian114_13 := by kernel_rfl
private def c2GroupHessian114_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], 160),([0,7], 64),([0,9], 8),([3,3], 80),([3,5], 160),([5,5], 80),([7,7], 32),([7,9], 8),([9,9], 24)]
def c2GroupHessian114_22 : Poly := List.flatten [c2GroupHessian114_22Chunk0]
theorem c2GroupHessian114_22_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian114_22 := by kernel_rfl
private def c2GroupHessian114_23Chunk0 : Poly := [([0,0], 112),([0,3], 80),([0,4], 80),([0,5], 80),([0,6], 80),([0,7], 32),([0,8], 32),([3,4], 80),([3,6], 80),([4,5], 80),([5,6], 80),([7,8], 32),([7,9], -4),([8,9], 4),([9,9], -24)]
def c2GroupHessian114_23 : Poly := List.flatten [c2GroupHessian114_23Chunk0]
theorem c2GroupHessian114_23_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian114_23 := by kernel_rfl
private def c2GroupHessian114_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], 160),([0,8], 64),([0,9], -8),([4,4], 80),([4,6], 160),([6,6], 80),([8,8], 32),([8,9], -8),([9,9], 24)]
def c2GroupHessian114_33 : Poly := List.flatten [c2GroupHessian114_33Chunk0]
theorem c2GroupHessian114_33_check : sumFast (c2TensorGroup114.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian114_33 := by kernel_rfl
end D4.Secondary
