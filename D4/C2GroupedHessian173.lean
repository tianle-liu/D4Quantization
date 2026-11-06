import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup173_det_check : c2TensorGroup173.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 217)) = true := by kernel_rfl
private def c2GroupHessian173_00Chunk0 : Poly := [([0,0], 56),([0,1], 8),([0,5], 40),([0,6], 32),([1,1], 8),([1,6], 8),([5,5], 40),([5,6], 40),([6,6], 16)]
def c2GroupHessian173_00 : Poly := List.flatten [c2GroupHessian173_00Chunk0]
theorem c2GroupHessian173_00_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian173_00 := by kernel_rfl
private def c2GroupHessian173_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40)]
def c2GroupHessian173_01 : Poly := List.flatten [c2GroupHessian173_01Chunk0]
theorem c2GroupHessian173_01_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian173_01 := by kernel_rfl
private def c2GroupHessian173_02Chunk0 : Poly := [([0,0], -48),([0,1], 4),([0,3], -8),([0,5], -40),([0,6], -8),([0,7], -40),([0,9], -8),([1,3], 4),([1,9], 4),([3,5], -20),([3,6], -8),([5,5], -40),([5,6], -20),([5,9], -20),([6,9], -8)]
def c2GroupHessian173_02 : Poly := List.flatten [c2GroupHessian173_02Chunk0]
theorem c2GroupHessian173_02_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian173_02 := by kernel_rfl
private def c2GroupHessian173_03Chunk0 : Poly := [([0,0], -44),([0,4], 4),([0,6], -20),([0,8], -40),([0,9], 8),([1,4], 8),([1,6], -4),([1,9], -4),([4,6], 4),([5,6], -20),([5,9], 20),([6,6], -16),([6,9], 8)]
def c2GroupHessian173_03 : Poly := List.flatten [c2GroupHessian173_03Chunk0]
theorem c2GroupHessian173_03_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian173_03 := by kernel_rfl
private def c2GroupHessian173_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian173_11 : Poly := List.flatten [c2GroupHessian173_11Chunk0]
theorem c2GroupHessian173_11_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian173_11 := by kernel_rfl
private def c2GroupHessian173_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([2,7], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian173_12 : Poly := List.flatten [c2GroupHessian173_12Chunk0]
theorem c2GroupHessian173_12_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian173_12 := by kernel_rfl
private def c2GroupHessian173_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([2,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian173_13 : Poly := List.flatten [c2GroupHessian173_13Chunk0]
theorem c2GroupHessian173_13_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian173_13 := by kernel_rfl
private def c2GroupHessian173_22Chunk0 : Poly := [([0,0], 56),([0,3], 32),([0,5], 40),([0,7], 80),([0,9], 32),([3,3], 16),([3,5], 40),([3,9], 32),([5,5], 40),([5,9], 40),([7,7], 40),([9,9], 16)]
def c2GroupHessian173_22 : Poly := List.flatten [c2GroupHessian173_22Chunk0]
theorem c2GroupHessian173_22_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian173_22 := by kernel_rfl
private def c2GroupHessian173_23Chunk0 : Poly := [([0,0], 36),([0,3], -4),([0,4], 4),([0,6], 8),([0,7], 40),([0,8], 40),([0,9], -20),([3,4], 4),([3,6], 8),([3,9], -16),([4,9], 4),([5,6], 20),([5,9], -20),([6,9], 8),([7,8], 40),([9,9], -16)]
def c2GroupHessian173_23 : Poly := List.flatten [c2GroupHessian173_23Chunk0]
theorem c2GroupHessian173_23_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian173_23 := by kernel_rfl
private def c2GroupHessian173_33Chunk0 : Poly := [([0,0], 48),([0,6], 8),([0,8], 80),([0,9], 8),([4,4], 8),([4,6], -8),([4,9], -8),([6,6], 16),([6,9], -16),([8,8], 40),([9,9], 16)]
def c2GroupHessian173_33 : Poly := List.flatten [c2GroupHessian173_33Chunk0]
theorem c2GroupHessian173_33_check : sumFast (c2TensorGroup173.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian173_33 := by kernel_rfl
end D4.Secondary
