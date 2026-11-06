import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup202_det_check : c2TensorGroup202.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 258)) = true := by kernel_rfl
private def c2GroupHessian202_00Chunk0 : Poly := [([0,0], 56),([0,1], 32),([0,5], 80),([0,6], 32),([1,1], 16),([1,6], 32),([5,5], 40),([6,6], 16)]
def c2GroupHessian202_00 : Poly := List.flatten [c2GroupHessian202_00Chunk0]
theorem c2GroupHessian202_00_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian202_00 := by kernel_rfl
private def c2GroupHessian202_01Chunk0 : Poly := [([0,0], 44),([0,1], 4),([0,2], 4),([0,5], 40),([0,6], 4),([0,7], 40),([0,8], -8),([1,2], 4),([1,8], -8),([2,6], 4),([5,7], 40),([6,8], -8)]
def c2GroupHessian202_01 : Poly := List.flatten [c2GroupHessian202_01Chunk0]
theorem c2GroupHessian202_01_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian202_01 := by kernel_rfl
private def c2GroupHessian202_02Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -120),([0,7], -40),([0,9], -40),([3,5], -40),([5,5], -40),([5,7], -40),([5,9], -40)]
def c2GroupHessian202_02 : Poly := List.flatten [c2GroupHessian202_02Chunk0]
theorem c2GroupHessian202_02_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian202_02 := by kernel_rfl
private def c2GroupHessian202_03Chunk0 : Poly := [([0,4], 4),([0,6], -16),([0,8], 8),([0,9], 40),([1,4], 4),([1,6], -16),([1,8], 8),([4,6], 4),([5,9], 40),([6,6], -16),([6,8], 8)]
def c2GroupHessian202_03 : Poly := List.flatten [c2GroupHessian202_03Chunk0]
theorem c2GroupHessian202_03_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian202_03 := by kernel_rfl
private def c2GroupHessian202_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 80),([0,8], 8),([2,2], 8),([2,8], 8),([7,7], 40),([8,8], 16)]
def c2GroupHessian202_11 : Poly := List.flatten [c2GroupHessian202_11Chunk0]
theorem c2GroupHessian202_11_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian202_11 := by kernel_rfl
private def c2GroupHessian202_12Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -40),([0,7], -120),([0,9], -40),([3,7], -40),([5,7], -40),([7,7], -40),([7,9], -40)]
def c2GroupHessian202_12 : Poly := List.flatten [c2GroupHessian202_12Chunk0]
theorem c2GroupHessian202_12_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian202_12 := by kernel_rfl
private def c2GroupHessian202_13Chunk0 : Poly := [([0,4], 8),([0,6], -4),([0,8], -4),([0,9], 40),([2,4], 8),([2,6], -4),([2,8], -4),([4,8], 4),([6,8], 8),([7,9], 40),([8,8], -16)]
def c2GroupHessian202_13 : Poly := List.flatten [c2GroupHessian202_13Chunk0]
theorem c2GroupHessian202_13_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian202_13 := by kernel_rfl
private def c2GroupHessian202_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 40),([3,5], 80),([3,7], 80),([3,9], 80),([5,5], 40),([5,7], 80),([5,9], 80),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian202_22 : Poly := List.flatten [c2GroupHessian202_22Chunk0]
theorem c2GroupHessian202_22_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian202_22 := by kernel_rfl
private def c2GroupHessian202_23Chunk0 : Poly := [([0,9], -80),([3,9], -40),([5,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian202_23 : Poly := List.flatten [c2GroupHessian202_23Chunk0]
theorem c2GroupHessian202_23_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian202_23 := by kernel_rfl
private def c2GroupHessian202_33Chunk0 : Poly := [([4,4], 8),([4,6], -8),([4,8], -8),([6,6], 16),([6,8], -16),([8,8], 16),([9,9], 40)]
def c2GroupHessian202_33 : Poly := List.flatten [c2GroupHessian202_33Chunk0]
theorem c2GroupHessian202_33_check : sumFast (c2TensorGroup202.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian202_33 := by kernel_rfl
end D4.Secondary
