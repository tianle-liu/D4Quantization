import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup14_det_check : c2TensorGroup14.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 17)) = true := by kernel_rfl
private def c2GroupHessian14_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 8),([0,6], 16),([1,1], 40),([5,5], 16),([5,6], 8),([6,6], 8)]
def c2GroupHessian14_00 : Poly := List.flatten [c2GroupHessian14_00Chunk0]
theorem c2GroupHessian14_00_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian14_00 := by kernel_rfl
private def c2GroupHessian14_01Chunk0 : Poly := [([0,0], 44),([0,1], 40),([0,2], 40),([0,5], -8),([0,6], 4),([0,7], 4),([1,2], 40),([5,7], -8),([5,8], -20),([6,7], 4)]
def c2GroupHessian14_01 : Poly := List.flatten [c2GroupHessian14_01Chunk0]
theorem c2GroupHessian14_01_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian14_01 := by kernel_rfl
private def c2GroupHessian14_02Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,5], -16),([0,6], -4),([0,7], -4),([1,3], 40),([5,5], -16),([5,6], -4),([5,7], 8),([5,9], -20),([6,7], -4)]
def c2GroupHessian14_02 : Poly := List.flatten [c2GroupHessian14_02Chunk0]
theorem c2GroupHessian14_02_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian14_02 := by kernel_rfl
private def c2GroupHessian14_03Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,5], 16),([0,6], -16),([1,4], 40),([5,6], -4),([5,8], 20),([5,9], 20),([6,6], -8)]
def c2GroupHessian14_03 : Poly := List.flatten [c2GroupHessian14_03Chunk0]
theorem c2GroupHessian14_03_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian14_03 := by kernel_rfl
private def c2GroupHessian14_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 40),([2,2], 40),([7,7], 16),([7,8], 40),([8,8], 40)]
def c2GroupHessian14_11 : Poly := List.flatten [c2GroupHessian14_11Chunk0]
theorem c2GroupHessian14_11_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian14_11 := by kernel_rfl
private def c2GroupHessian14_12Chunk0 : Poly := [([0,0], 4),([0,3], 40),([0,5], 8),([0,7], -12),([0,8], 20),([0,9], 20),([2,3], 40),([5,7], 8),([5,8], 20),([7,7], -16),([7,8], -20),([7,9], 20),([8,9], 40)]
def c2GroupHessian14_12 : Poly := List.flatten [c2GroupHessian14_12Chunk0]
theorem c2GroupHessian14_12_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian14_12 := by kernel_rfl
private def c2GroupHessian14_13Chunk0 : Poly := [([0,0], -24),([0,4], 40),([0,6], -4),([0,7], -24),([0,8], -60),([0,9], -20),([2,4], 40),([6,7], -4),([7,8], -20),([7,9], -20),([8,8], -40),([8,9], -40)]
def c2GroupHessian14_13 : Poly := List.flatten [c2GroupHessian14_13Chunk0]
theorem c2GroupHessian14_13_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian14_13 := by kernel_rfl
private def c2GroupHessian14_22Chunk0 : Poly := [([0,0], 16),([0,5], 24),([0,7], -8),([0,9], 40),([3,3], 40),([5,5], 16),([5,7], -16),([5,9], 40),([7,7], 16),([7,9], -40),([9,9], 40)]
def c2GroupHessian14_22 : Poly := List.flatten [c2GroupHessian14_22Chunk0]
theorem c2GroupHessian14_22_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian14_22 := by kernel_rfl
private def c2GroupHessian14_23Chunk0 : Poly := [([0,0], -16),([0,5], -16),([0,6], 4),([0,7], 24),([0,8], -20),([0,9], -60),([3,4], 40),([5,6], 4),([5,8], -20),([5,9], -20),([6,7], 4),([7,8], 20),([7,9], 20),([8,9], -40),([9,9], -40)]
def c2GroupHessian14_23 : Poly := List.flatten [c2GroupHessian14_23Chunk0]
theorem c2GroupHessian14_23_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian14_23 := by kernel_rfl
private def c2GroupHessian14_33Chunk0 : Poly := [([0,0], 48),([0,6], 16),([0,8], 80),([0,9], 80),([4,4], 40),([6,6], 8),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian14_33 : Poly := List.flatten [c2GroupHessian14_33Chunk0]
theorem c2GroupHessian14_33_check : sumFast (c2TensorGroup14.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian14_33 := by kernel_rfl
end D4.Secondary
