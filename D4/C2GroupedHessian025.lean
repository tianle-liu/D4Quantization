import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup25_det_check : c2TensorGroup25.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 40)) = true := by kernel_rfl
private def c2GroupHessian25_00Chunk0 : Poly := [([0,0], 48),([0,5], 80),([0,6], 48),([1,1], 40),([5,5], 40),([5,6], 40),([6,6], 16)]
def c2GroupHessian25_00 : Poly := List.flatten [c2GroupHessian25_00Chunk0]
theorem c2GroupHessian25_00_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian25_00 := by kernel_rfl
private def c2GroupHessian25_01Chunk0 : Poly := [([0,0], 8),([0,1], -40),([0,2], 8),([0,6], 4),([1,7], -40),([1,8], -40),([2,6], 4)]
def c2GroupHessian25_01 : Poly := List.flatten [c2GroupHessian25_01Chunk0]
theorem c2GroupHessian25_01_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian25_01 := by kernel_rfl
private def c2GroupHessian25_02Chunk0 : Poly := [([0,0], -40),([0,1], 40),([0,5], -80),([0,6], -20),([0,9], -16),([1,3], 40),([1,7], 40),([5,5], -40),([5,6], -20),([5,9], -20),([6,9], -8)]
def c2GroupHessian25_02 : Poly := List.flatten [c2GroupHessian25_02Chunk0]
theorem c2GroupHessian25_02_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian25_02 := by kernel_rfl
private def c2GroupHessian25_03Chunk0 : Poly := [([0,0], -8),([0,1], 40),([0,6], -28),([0,9], 16),([1,4], 40),([1,8], 40),([5,6], -20),([5,9], 20),([6,6], -16),([6,9], 8)]
def c2GroupHessian25_03 : Poly := List.flatten [c2GroupHessian25_03Chunk0]
theorem c2GroupHessian25_03_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian25_03 := by kernel_rfl
private def c2GroupHessian25_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 80),([0,8], 80),([2,2], 8),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian25_11 : Poly := List.flatten [c2GroupHessian25_11Chunk0]
theorem c2GroupHessian25_11_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian25_11 := by kernel_rfl
private def c2GroupHessian25_12Chunk0 : Poly := [([0,0], -40),([0,3], -40),([0,7], -80),([0,8], -40),([0,9], 4),([2,9], 4),([3,7], -40),([3,8], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian25_12 : Poly := List.flatten [c2GroupHessian25_12Chunk0]
theorem c2GroupHessian25_12_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian25_12 := by kernel_rfl
private def c2GroupHessian25_13Chunk0 : Poly := [([0,0], -48),([0,2], -8),([0,4], -40),([0,6], -4),([0,7], -40),([0,8], -80),([0,9], -4),([2,6], -4),([2,9], -4),([4,7], -40),([4,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian25_13 : Poly := List.flatten [c2GroupHessian25_13Chunk0]
theorem c2GroupHessian25_13_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian25_13 := by kernel_rfl
private def c2GroupHessian25_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 80),([0,7], 80),([0,9], 40),([3,3], 40),([3,7], 80),([5,5], 40),([5,9], 40),([7,7], 40),([9,9], 16)]
def c2GroupHessian25_22 : Poly := List.flatten [c2GroupHessian25_22Chunk0]
theorem c2GroupHessian25_22_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian25_22 := by kernel_rfl
private def c2GroupHessian25_23Chunk0 : Poly := [([0,0], 40),([0,3], 40),([0,4], 40),([0,6], 20),([0,7], 40),([0,8], 40),([0,9], -24),([3,4], 40),([3,8], 40),([4,7], 40),([5,6], 20),([5,9], -20),([6,9], 8),([7,8], 40),([9,9], -16)]
def c2GroupHessian25_23 : Poly := List.flatten [c2GroupHessian25_23Chunk0]
theorem c2GroupHessian25_23_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian25_23 := by kernel_rfl
private def c2GroupHessian25_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 8),([0,8], 80),([0,9], 8),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], -16),([8,8], 40),([9,9], 16)]
def c2GroupHessian25_33 : Poly := List.flatten [c2GroupHessian25_33Chunk0]
theorem c2GroupHessian25_33_check : sumFast (c2TensorGroup25.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian25_33 := by kernel_rfl
end D4.Secondary
