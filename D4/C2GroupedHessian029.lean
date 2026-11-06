import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup29_det_check : c2TensorGroup29.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 45)) = true := by kernel_rfl
private def c2GroupHessian29_00Chunk0 : Poly := [([0,0], 128),([0,5], 128),([0,6], 128),([1,1], 80),([5,5], 32),([5,6], 64),([6,6], 32)]
def c2GroupHessian29_00 : Poly := List.flatten [c2GroupHessian29_00Chunk0]
theorem c2GroupHessian29_00_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian29_00 := by kernel_rfl
private def c2GroupHessian29_01Chunk0 : Poly := [([0,0], 64),([0,1], -80),([0,2], -8),([0,5], 32),([0,6], 32),([1,7], -80),([1,8], -80),([2,5], -4),([2,6], -4)]
def c2GroupHessian29_01 : Poly := List.flatten [c2GroupHessian29_01Chunk0]
theorem c2GroupHessian29_01_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian29_01 := by kernel_rfl
private def c2GroupHessian29_02Chunk0 : Poly := [([0,0], -64),([0,1], 80),([0,5], -96),([0,6], -32),([0,9], -8),([1,3], 80),([1,7], 80),([5,5], -32),([5,6], -32),([5,9], -4),([6,9], -4)]
def c2GroupHessian29_02 : Poly := List.flatten [c2GroupHessian29_02Chunk0]
theorem c2GroupHessian29_02_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian29_02 := by kernel_rfl
private def c2GroupHessian29_03Chunk0 : Poly := [([0,0], -64),([0,1], 80),([0,5], -32),([0,6], -96),([0,9], 8),([1,4], 80),([1,8], 80),([5,6], -32),([5,9], 4),([6,6], -32),([6,9], 4)]
def c2GroupHessian29_03 : Poly := List.flatten [c2GroupHessian29_03Chunk0]
theorem c2GroupHessian29_03_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian29_03 := by kernel_rfl
private def c2GroupHessian29_11Chunk0 : Poly := [([0,0], 112),([0,2], -8),([0,7], 160),([0,8], 160),([2,2], 24),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian29_11 : Poly := List.flatten [c2GroupHessian29_11Chunk0]
theorem c2GroupHessian29_11_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian29_11 := by kernel_rfl
private def c2GroupHessian29_12Chunk0 : Poly := [([0,0], -112),([0,2], 4),([0,3], -80),([0,5], -32),([0,7], -160),([0,8], -80),([0,9], -4),([2,5], 4),([2,9], 8),([3,7], -80),([3,8], -80),([7,7], -80),([7,8], -80)]
def c2GroupHessian29_12 : Poly := List.flatten [c2GroupHessian29_12Chunk0]
theorem c2GroupHessian29_12_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian29_12 := by kernel_rfl
private def c2GroupHessian29_13Chunk0 : Poly := [([0,0], -112),([0,2], 4),([0,4], -80),([0,6], -32),([0,7], -80),([0,8], -160),([0,9], 4),([2,6], 4),([2,9], -8),([4,7], -80),([4,8], -80),([7,8], -80),([8,8], -80)]
def c2GroupHessian29_13 : Poly := List.flatten [c2GroupHessian29_13Chunk0]
theorem c2GroupHessian29_13_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian29_13 := by kernel_rfl
private def c2GroupHessian29_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], 64),([0,7], 160),([0,9], 8),([3,3], 80),([3,7], 160),([5,5], 32),([5,9], 8),([7,7], 80),([9,9], 24)]
def c2GroupHessian29_22 : Poly := List.flatten [c2GroupHessian29_22Chunk0]
theorem c2GroupHessian29_22_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian29_22 := by kernel_rfl
private def c2GroupHessian29_23Chunk0 : Poly := [([0,0], 112),([0,3], 80),([0,4], 80),([0,5], 32),([0,6], 32),([0,7], 80),([0,8], 80),([3,4], 80),([3,8], 80),([4,7], 80),([5,6], 32),([5,9], -4),([6,9], 4),([7,8], 80),([9,9], -24)]
def c2GroupHessian29_23 : Poly := List.flatten [c2GroupHessian29_23Chunk0]
theorem c2GroupHessian29_23_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian29_23 := by kernel_rfl
private def c2GroupHessian29_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], 64),([0,8], 160),([0,9], -8),([4,4], 80),([4,8], 160),([6,6], 32),([6,9], -8),([8,8], 80),([9,9], 24)]
def c2GroupHessian29_33 : Poly := List.flatten [c2GroupHessian29_33Chunk0]
theorem c2GroupHessian29_33_check : sumFast (c2TensorGroup29.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian29_33 := by kernel_rfl
end D4.Secondary
