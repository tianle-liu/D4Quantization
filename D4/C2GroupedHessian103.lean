import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup103_det_check : c2TensorGroup103.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 133)) = true := by kernel_rfl
private def c2GroupHessian103_00Chunk0 : Poly := [([0,0], 104),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 80),([1,5], 160),([1,6], 160),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian103_00 : Poly := List.flatten [c2GroupHessian103_00Chunk0]
theorem c2GroupHessian103_00_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian103_00 := by kernel_rfl
private def c2GroupHessian103_01Chunk0 : Poly := [([0,0], -56),([0,1], -80),([0,2], -80),([0,5], -80),([0,6], -80),([0,7], -80),([0,8], -80),([1,2], -80),([1,7], -80),([1,8], -80),([2,5], -80),([2,6], -80),([5,7], -80),([5,8], -80),([6,7], -80),([6,8], -80)]
def c2GroupHessian103_01 : Poly := List.flatten [c2GroupHessian103_01Chunk0]
theorem c2GroupHessian103_01_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian103_01 := by kernel_rfl
private def c2GroupHessian103_02Chunk0 : Poly := [([0,0], -16),([0,3], 8),([0,5], -80),([0,7], 80),([0,9], 8),([1,5], -80),([1,7], 80),([5,5], -80),([5,6], -80),([5,7], 80),([6,7], 80)]
def c2GroupHessian103_02 : Poly := List.flatten [c2GroupHessian103_02Chunk0]
theorem c2GroupHessian103_02_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian103_02 := by kernel_rfl
private def c2GroupHessian103_03Chunk0 : Poly := [([0,0], -16),([0,4], -4),([0,6], -80),([0,8], 80),([0,9], -8),([1,6], -80),([1,8], 80),([5,6], -80),([5,8], 80),([6,6], -80),([6,8], 80)]
def c2GroupHessian103_03 : Poly := List.flatten [c2GroupHessian103_03Chunk0]
theorem c2GroupHessian103_03_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian103_03 := by kernel_rfl
private def c2GroupHessian103_11Chunk0 : Poly := [([0,0], 104),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 80),([2,7], 160),([2,8], 160),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian103_11 : Poly := List.flatten [c2GroupHessian103_11Chunk0]
theorem c2GroupHessian103_11_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian103_11 := by kernel_rfl
private def c2GroupHessian103_12Chunk0 : Poly := [([0,0], -16),([0,3], 8),([0,5], 80),([0,7], -80),([0,9], 8),([2,5], 80),([2,7], -80),([5,7], 80),([5,8], 80),([7,7], -80),([7,8], -80)]
def c2GroupHessian103_12 : Poly := List.flatten [c2GroupHessian103_12Chunk0]
theorem c2GroupHessian103_12_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian103_12 := by kernel_rfl
private def c2GroupHessian103_13Chunk0 : Poly := [([0,0], -16),([0,4], -4),([0,6], 80),([0,8], -80),([0,9], -8),([2,6], 80),([2,8], -80),([6,7], 80),([6,8], 80),([7,8], -80),([8,8], -80)]
def c2GroupHessian103_13 : Poly := List.flatten [c2GroupHessian103_13Chunk0]
theorem c2GroupHessian103_13_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian103_13 := by kernel_rfl
private def c2GroupHessian103_22Chunk0 : Poly := [([0,0], 32),([0,3], 32),([0,9], 32),([3,3], 24),([3,9], 48),([5,5], 80),([5,7], -160),([7,7], 80),([9,9], 24)]
def c2GroupHessian103_22 : Poly := List.flatten [c2GroupHessian103_22Chunk0]
theorem c2GroupHessian103_22_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian103_22 := by kernel_rfl
private def c2GroupHessian103_23Chunk0 : Poly := [([0,3], -16),([0,9], -32),([3,4], -4),([3,9], -24),([4,9], -4),([5,6], 80),([5,8], -80),([6,7], -80),([7,8], 80),([9,9], -24)]
def c2GroupHessian103_23 : Poly := List.flatten [c2GroupHessian103_23Chunk0]
theorem c2GroupHessian103_23_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian103_23 := by kernel_rfl
private def c2GroupHessian103_33Chunk0 : Poly := [([0,0], 32),([0,4], 48),([0,9], 32),([4,4], 32),([4,9], 8),([6,6], 80),([6,8], -160),([8,8], 80),([9,9], 24)]
def c2GroupHessian103_33 : Poly := List.flatten [c2GroupHessian103_33Chunk0]
theorem c2GroupHessian103_33_check : sumFast (c2TensorGroup103.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian103_33 := by kernel_rfl
end D4.Secondary
