import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup142_det_check : c2TensorGroup142.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 180)) = true := by kernel_rfl
private def c2GroupHessian142_00Chunk0 : Poly := [([0,0], 192),([0,1], 240),([0,5], 240),([1,1], 80),([1,5], 160),([5,5], 80),([6,6], 80)]
def c2GroupHessian142_00 : Poly := List.flatten [c2GroupHessian142_00Chunk0]
theorem c2GroupHessian142_00_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian142_00 := by kernel_rfl
private def c2GroupHessian142_01Chunk0 : Poly := [([0,0], 72),([0,1], 40),([0,5], 40),([0,6], -80),([0,8], -24),([1,8], -20),([2,6], -80),([5,8], -20),([6,7], -80)]
def c2GroupHessian142_01 : Poly := List.flatten [c2GroupHessian142_01Chunk0]
theorem c2GroupHessian142_01_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian142_01 := by kernel_rfl
private def c2GroupHessian142_02Chunk0 : Poly := [([0,0], -120),([0,1], -80),([0,3], -24),([0,5], -200),([0,6], 80),([1,3], -20),([1,5], -80),([3,5], -20),([5,5], -80),([6,7], 80),([6,9], 80)]
def c2GroupHessian142_02 : Poly := List.flatten [c2GroupHessian142_02Chunk0]
theorem c2GroupHessian142_02_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian142_02 := by kernel_rfl
private def c2GroupHessian142_03Chunk0 : Poly := [([0,0], -72),([0,1], -40),([0,5], -40),([0,6], -80),([0,8], 24),([1,8], 20),([4,6], -80),([5,8], 20),([6,6], -80),([6,9], -80)]
def c2GroupHessian142_03 : Poly := List.flatten [c2GroupHessian142_03Chunk0]
theorem c2GroupHessian142_03_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian142_03 := by kernel_rfl
private def c2GroupHessian142_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], 160),([0,8], -8),([2,2], 80),([2,7], 160),([7,7], 80),([8,8], 24)]
def c2GroupHessian142_11 : Poly := List.flatten [c2GroupHessian142_11Chunk0]
theorem c2GroupHessian142_11_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian142_11 := by kernel_rfl
private def c2GroupHessian142_12Chunk0 : Poly := [([0,0], -120),([0,2], -80),([0,3], -4),([0,5], -40),([0,7], -160),([0,8], 20),([0,9], -80),([2,7], -80),([2,9], -80),([3,8], 8),([5,8], 20),([7,7], -80),([7,9], -80)]
def c2GroupHessian142_12 : Poly := List.flatten [c2GroupHessian142_12Chunk0]
theorem c2GroupHessian142_12_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian142_12 := by kernel_rfl
private def c2GroupHessian142_13Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,4], 80),([0,6], 80),([0,7], 80),([0,8], 8),([0,9], 80),([2,4], 80),([2,6], 80),([2,9], 80),([4,7], 80),([6,7], 80),([7,9], 80),([8,8], -24)]
def c2GroupHessian142_13 : Poly := List.flatten [c2GroupHessian142_13Chunk0]
theorem c2GroupHessian142_13_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian142_13 := by kernel_rfl
private def c2GroupHessian142_22Chunk0 : Poly := [([0,0], 160),([0,3], 40),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 24),([3,5], 40),([5,5], 80),([7,7], 80),([7,9], 160),([9,9], 80)]
def c2GroupHessian142_22 : Poly := List.flatten [c2GroupHessian142_22Chunk0]
theorem c2GroupHessian142_22_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian142_22 := by kernel_rfl
private def c2GroupHessian142_23Chunk0 : Poly := [([0,0], -40),([0,3], 4),([0,4], -80),([0,5], 40),([0,6], -80),([0,7], -80),([0,8], -20),([0,9], -160),([3,8], -8),([4,7], -80),([4,9], -80),([5,8], -20),([6,7], -80),([6,9], -80),([7,9], -80),([9,9], -80)]
def c2GroupHessian142_23 : Poly := List.flatten [c2GroupHessian142_23Chunk0]
theorem c2GroupHessian142_23_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian142_23 := by kernel_rfl
private def c2GroupHessian142_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], 160),([0,8], -8),([0,9], 160),([4,4], 80),([4,6], 160),([4,9], 160),([6,6], 80),([6,9], 160),([8,8], 24),([9,9], 80)]
def c2GroupHessian142_33 : Poly := List.flatten [c2GroupHessian142_33Chunk0]
theorem c2GroupHessian142_33_check : sumFast (c2TensorGroup142.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian142_33 := by kernel_rfl
end D4.Secondary
