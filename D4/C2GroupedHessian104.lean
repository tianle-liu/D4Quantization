import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup104_det_check : c2TensorGroup104.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 134)) = true := by kernel_rfl
private def c2GroupHessian104_00Chunk0 : Poly := [([0,0], 104),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 80),([1,5], 160),([1,6], 160),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian104_00 : Poly := List.flatten [c2GroupHessian104_00Chunk0]
theorem c2GroupHessian104_00_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian104_00 := by kernel_rfl
private def c2GroupHessian104_01Chunk0 : Poly := [([0,0], -56),([0,1], -80),([0,2], -80),([0,5], -80),([0,6], -80),([0,7], -80),([0,8], -80),([1,2], -80),([1,7], -80),([1,8], -80),([2,5], -80),([2,6], -80),([5,7], -80),([5,8], -80),([6,7], -80),([6,8], -80)]
def c2GroupHessian104_01 : Poly := List.flatten [c2GroupHessian104_01Chunk0]
theorem c2GroupHessian104_01_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian104_01 := by kernel_rfl
private def c2GroupHessian104_02Chunk0 : Poly := [([0,0], -12),([0,3], 8),([0,5], -80),([0,7], 80),([0,9], -4),([1,5], -80),([1,7], 80),([5,5], -80),([5,6], -80),([5,7], 80),([6,7], 80)]
def c2GroupHessian104_02 : Poly := List.flatten [c2GroupHessian104_02Chunk0]
theorem c2GroupHessian104_02_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian104_02 := by kernel_rfl
private def c2GroupHessian104_03Chunk0 : Poly := [([0,0], -4),([0,4], 8),([0,6], -80),([0,8], 80),([0,9], 4),([1,6], -80),([1,8], 80),([5,6], -80),([5,8], 80),([6,6], -80),([6,8], 80)]
def c2GroupHessian104_03 : Poly := List.flatten [c2GroupHessian104_03Chunk0]
theorem c2GroupHessian104_03_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian104_03 := by kernel_rfl
private def c2GroupHessian104_11Chunk0 : Poly := [([0,0], 104),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 80),([2,7], 160),([2,8], 160),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian104_11 : Poly := List.flatten [c2GroupHessian104_11Chunk0]
theorem c2GroupHessian104_11_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian104_11 := by kernel_rfl
private def c2GroupHessian104_12Chunk0 : Poly := [([0,0], -12),([0,3], 8),([0,5], 80),([0,7], -80),([0,9], -4),([2,5], 80),([2,7], -80),([5,7], 80),([5,8], 80),([7,7], -80),([7,8], -80)]
def c2GroupHessian104_12 : Poly := List.flatten [c2GroupHessian104_12Chunk0]
theorem c2GroupHessian104_12_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian104_12 := by kernel_rfl
private def c2GroupHessian104_13Chunk0 : Poly := [([0,0], -4),([0,4], 8),([0,6], 80),([0,8], -80),([0,9], 4),([2,6], 80),([2,8], -80),([6,7], 80),([6,8], 80),([7,8], -80),([8,8], -80)]
def c2GroupHessian104_13 : Poly := List.flatten [c2GroupHessian104_13Chunk0]
theorem c2GroupHessian104_13_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian104_13 := by kernel_rfl
private def c2GroupHessian104_22Chunk0 : Poly := [([0,0], 16),([0,3], 8),([0,9], 24),([3,3], 24),([3,9], -8),([5,5], 80),([5,7], -160),([7,7], 80),([9,9], 32)]
def c2GroupHessian104_22 : Poly := List.flatten [c2GroupHessian104_22Chunk0]
theorem c2GroupHessian104_22_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian104_22 := by kernel_rfl
private def c2GroupHessian104_23Chunk0 : Poly := [([0,3], 12),([0,4], 4),([0,9], -24),([3,4], 24),([3,9], 4),([4,9], -4),([5,6], 80),([5,8], -80),([6,7], -80),([7,8], 80),([9,9], -32)]
def c2GroupHessian104_23 : Poly := List.flatten [c2GroupHessian104_23Chunk0]
theorem c2GroupHessian104_23_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian104_23 := by kernel_rfl
private def c2GroupHessian104_33Chunk0 : Poly := [([0,0], 16),([0,4], 24),([0,9], 24),([4,4], 24),([4,9], 8),([6,6], 80),([6,8], -160),([8,8], 80),([9,9], 32)]
def c2GroupHessian104_33 : Poly := List.flatten [c2GroupHessian104_33Chunk0]
theorem c2GroupHessian104_33_check : sumFast (c2TensorGroup104.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian104_33 := by kernel_rfl
end D4.Secondary
