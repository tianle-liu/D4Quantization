import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup38_det_check : c2TensorGroup38.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 55)) = true := by kernel_rfl
private def c2GroupHessian38_00Chunk0 : Poly := [([0,0], 16),([0,5], 16),([0,6], 16),([1,1], 40),([5,5], 8),([5,6], 8),([6,6], 16)]
def c2GroupHessian38_00 : Poly := List.flatten [c2GroupHessian38_00Chunk0]
theorem c2GroupHessian38_00_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian38_00 := by kernel_rfl
private def c2GroupHessian38_01Chunk0 : Poly := [([0,0], 8),([0,1], -40),([0,2], 8),([0,5], 4),([0,6], -8),([1,7], -40),([1,8], -40),([2,5], 4),([2,6], -8)]
def c2GroupHessian38_01 : Poly := List.flatten [c2GroupHessian38_01Chunk0]
theorem c2GroupHessian38_01_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian38_01 := by kernel_rfl
private def c2GroupHessian38_02Chunk0 : Poly := [([0,0], -8),([0,1], 40),([0,5], -12),([0,6], 8),([1,3], 40),([1,7], 40),([5,5], -8),([5,6], -4),([6,9], 20)]
def c2GroupHessian38_02 : Poly := List.flatten [c2GroupHessian38_02Chunk0]
theorem c2GroupHessian38_02_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian38_02 := by kernel_rfl
private def c2GroupHessian38_03Chunk0 : Poly := [([0,0], -8),([0,1], 40),([0,5], -4),([0,6], -24),([1,4], 40),([1,8], 40),([5,6], -4),([6,6], -16),([6,9], -20)]
def c2GroupHessian38_03 : Poly := List.flatten [c2GroupHessian38_03Chunk0]
theorem c2GroupHessian38_03_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian38_03 := by kernel_rfl
private def c2GroupHessian38_11Chunk0 : Poly := [([0,0], 56),([0,2], 32),([0,7], 80),([0,8], 80),([2,2], 16),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian38_11 : Poly := List.flatten [c2GroupHessian38_11Chunk0]
theorem c2GroupHessian38_11_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian38_11 := by kernel_rfl
private def c2GroupHessian38_12Chunk0 : Poly := [([0,0], -56),([0,2], -16),([0,3], -40),([0,5], -4),([0,7], -80),([0,8], -40),([0,9], -20),([2,5], -4),([2,9], -20),([3,7], -40),([3,8], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian38_12 : Poly := List.flatten [c2GroupHessian38_12Chunk0]
theorem c2GroupHessian38_12_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian38_12 := by kernel_rfl
private def c2GroupHessian38_13Chunk0 : Poly := [([0,0], -32),([0,2], 8),([0,4], -40),([0,6], 8),([0,7], -40),([0,8], -80),([0,9], 20),([2,6], 8),([2,9], 20),([4,7], -40),([4,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian38_13 : Poly := List.flatten [c2GroupHessian38_13Chunk0]
theorem c2GroupHessian38_13_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian38_13 := by kernel_rfl
private def c2GroupHessian38_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 8),([0,7], 80),([0,9], 40),([3,3], 40),([3,7], 80),([5,5], 8),([7,7], 40),([9,9], 40)]
def c2GroupHessian38_22 : Poly := List.flatten [c2GroupHessian38_22Chunk0]
theorem c2GroupHessian38_22_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian38_22 := by kernel_rfl
private def c2GroupHessian38_23Chunk0 : Poly := [([0,0], 32),([0,3], 40),([0,4], 40),([0,5], 4),([0,6], -8),([0,7], 40),([0,8], 40),([0,9], -40),([3,4], 40),([3,8], 40),([4,7], 40),([5,6], 4),([6,9], -20),([7,8], 40),([9,9], -40)]
def c2GroupHessian38_23 : Poly := List.flatten [c2GroupHessian38_23Chunk0]
theorem c2GroupHessian38_23_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian38_23 := by kernel_rfl
private def c2GroupHessian38_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 32),([0,8], 80),([0,9], 40),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], 40),([8,8], 40),([9,9], 40)]
def c2GroupHessian38_33 : Poly := List.flatten [c2GroupHessian38_33Chunk0]
theorem c2GroupHessian38_33_check : sumFast (c2TensorGroup38.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian38_33 := by kernel_rfl
end D4.Secondary
