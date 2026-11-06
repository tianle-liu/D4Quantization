import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup89_det_check : c2TensorGroup89.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 116)) = true := by kernel_rfl
private def c2GroupHessian89_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian89_00 : Poly := List.flatten [c2GroupHessian89_00Chunk0]
theorem c2GroupHessian89_00_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian89_00 := by kernel_rfl
private def c2GroupHessian89_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian89_01 : Poly := List.flatten [c2GroupHessian89_01Chunk0]
theorem c2GroupHessian89_01_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian89_01 := by kernel_rfl
private def c2GroupHessian89_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian89_02 : Poly := List.flatten [c2GroupHessian89_02Chunk0]
theorem c2GroupHessian89_02_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian89_02 := by kernel_rfl
private def c2GroupHessian89_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian89_03 : Poly := List.flatten [c2GroupHessian89_03Chunk0]
theorem c2GroupHessian89_03_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian89_03 := by kernel_rfl
private def c2GroupHessian89_11Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 80),([0,8], 80),([2,2], 16),([2,7], 40),([2,8], 40),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian89_11 : Poly := List.flatten [c2GroupHessian89_11Chunk0]
theorem c2GroupHessian89_11_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian89_11 := by kernel_rfl
private def c2GroupHessian89_12Chunk0 : Poly := [([0,0], -60),([0,2], -8),([0,3], -20),([0,5], -40),([0,7], -60),([0,8], -20),([0,9], -20),([2,3], -8),([2,7], -20),([2,9], -8),([3,7], -20),([3,8], -20),([7,7], -40),([7,8], -40),([7,9], -20),([8,9], -20)]
def c2GroupHessian89_12 : Poly := List.flatten [c2GroupHessian89_12Chunk0]
theorem c2GroupHessian89_12_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian89_12 := by kernel_rfl
private def c2GroupHessian89_13Chunk0 : Poly := [([0,0], -60),([0,2], -8),([0,6], -40),([0,7], -20),([0,8], -60),([0,9], 20),([2,4], 4),([2,8], -20),([2,9], 8),([7,8], -40),([7,9], 20),([8,8], -40),([8,9], 20)]
def c2GroupHessian89_13 : Poly := List.flatten [c2GroupHessian89_13Chunk0]
theorem c2GroupHessian89_13_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian89_13 := by kernel_rfl
private def c2GroupHessian89_22Chunk0 : Poly := [([0,0], 56),([0,3], 32),([0,5], 80),([0,7], 40),([0,9], 32),([3,3], 16),([3,7], 40),([3,9], 32),([5,5], 40),([7,7], 40),([7,9], 40),([9,9], 16)]
def c2GroupHessian89_22 : Poly := List.flatten [c2GroupHessian89_22Chunk0]
theorem c2GroupHessian89_22_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian89_22 := by kernel_rfl
private def c2GroupHessian89_23Chunk0 : Poly := [([0,0], 48),([0,3], 8),([0,4], 4),([0,5], 40),([0,6], 40),([0,7], 20),([0,8], 20),([0,9], -8),([3,4], 4),([3,8], 20),([3,9], -16),([4,9], 4),([5,6], 40),([7,8], 40),([7,9], -20),([8,9], 20),([9,9], -16)]
def c2GroupHessian89_23 : Poly := List.flatten [c2GroupHessian89_23Chunk0]
theorem c2GroupHessian89_23_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian89_23 := by kernel_rfl
private def c2GroupHessian89_33Chunk0 : Poly := [([0,0], 56),([0,4], 8),([0,6], 80),([0,8], 40),([0,9], -16),([4,4], 8),([4,9], -8),([6,6], 40),([8,8], 40),([8,9], -40),([9,9], 16)]
def c2GroupHessian89_33 : Poly := List.flatten [c2GroupHessian89_33Chunk0]
theorem c2GroupHessian89_33_check : sumFast (c2TensorGroup89.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian89_33 := by kernel_rfl
end D4.Secondary
