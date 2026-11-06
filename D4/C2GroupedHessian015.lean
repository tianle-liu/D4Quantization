import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup15_det_check : c2TensorGroup15.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 18)) = true := by kernel_rfl
private def c2GroupHessian15_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 8),([0,6], 8),([1,1], 40),([5,5], 16),([5,6], -16),([6,6], 16)]
def c2GroupHessian15_00 : Poly := List.flatten [c2GroupHessian15_00Chunk0]
theorem c2GroupHessian15_00_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian15_00 := by kernel_rfl
private def c2GroupHessian15_01Chunk0 : Poly := [([0,0], 48),([0,1], 40),([0,2], 40),([0,5], 4),([0,6], 4),([0,7], 8),([1,2], 40),([5,7], 4),([5,8], -20),([6,7], 4),([6,8], 20)]
def c2GroupHessian15_01 : Poly := List.flatten [c2GroupHessian15_01Chunk0]
theorem c2GroupHessian15_01_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian15_01 := by kernel_rfl
private def c2GroupHessian15_02Chunk0 : Poly := [([0,0], -8),([0,3], 40),([0,5], -28),([0,6], 16),([0,7], -8),([1,3], 40),([5,5], -16),([5,6], 8),([5,7], -4),([5,9], -20),([6,7], -4),([6,9], 20)]
def c2GroupHessian15_02 : Poly := List.flatten [c2GroupHessian15_02Chunk0]
theorem c2GroupHessian15_02_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian15_02 := by kernel_rfl
private def c2GroupHessian15_03Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,5], 16),([0,6], -28),([1,4], 40),([5,6], 8),([5,8], 20),([5,9], 20),([6,6], -16),([6,8], -20),([6,9], -20)]
def c2GroupHessian15_03 : Poly := List.flatten [c2GroupHessian15_03Chunk0]
theorem c2GroupHessian15_03_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian15_03 := by kernel_rfl
private def c2GroupHessian15_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 16),([2,2], 40),([7,7], 8),([8,8], 40)]
def c2GroupHessian15_11 : Poly := List.flatten [c2GroupHessian15_11Chunk0]
theorem c2GroupHessian15_11_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian15_11 := by kernel_rfl
private def c2GroupHessian15_12Chunk0 : Poly := [([0,0], -8),([0,3], 40),([0,5], -4),([0,7], -16),([0,8], 40),([2,3], 40),([5,7], -4),([5,8], 20),([7,7], -8),([8,9], 40)]
def c2GroupHessian15_12 : Poly := List.flatten [c2GroupHessian15_12Chunk0]
theorem c2GroupHessian15_12_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian15_12 := by kernel_rfl
private def c2GroupHessian15_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,6], -4),([0,7], -8),([0,8], -40),([2,4], 40),([6,7], -4),([6,8], -20),([8,8], -40),([8,9], -40)]
def c2GroupHessian15_13 : Poly := List.flatten [c2GroupHessian15_13Chunk0]
theorem c2GroupHessian15_13_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian15_13 := by kernel_rfl
private def c2GroupHessian15_22Chunk0 : Poly := [([0,0], 48),([0,5], 48),([0,7], 16),([0,9], 80),([3,3], 40),([5,5], 16),([5,7], 8),([5,9], 40),([7,7], 8),([9,9], 40)]
def c2GroupHessian15_22 : Poly := List.flatten [c2GroupHessian15_22Chunk0]
theorem c2GroupHessian15_22_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian15_22 := by kernel_rfl
private def c2GroupHessian15_23Chunk0 : Poly := [([0,0], -32),([0,5], -16),([0,6], -16),([0,7], 8),([0,8], -40),([0,9], -80),([3,4], 40),([5,6], -8),([5,8], -20),([5,9], -20),([6,7], 4),([6,9], -20),([8,9], -40),([9,9], -40)]
def c2GroupHessian15_23 : Poly := List.flatten [c2GroupHessian15_23Chunk0]
theorem c2GroupHessian15_23_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian15_23 := by kernel_rfl
private def c2GroupHessian15_33Chunk0 : Poly := [([0,0], 48),([0,6], 48),([0,8], 80),([0,9], 80),([4,4], 40),([6,6], 16),([6,8], 40),([6,9], 40),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian15_33 : Poly := List.flatten [c2GroupHessian15_33Chunk0]
theorem c2GroupHessian15_33_check : sumFast (c2TensorGroup15.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian15_33 := by kernel_rfl
end D4.Secondary
