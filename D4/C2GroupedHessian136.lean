import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup136_det_check : c2TensorGroup136.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 172)) = true := by kernel_rfl
private def c2GroupHessian136_00Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,6], 40),([1,1], 16),([1,6], 32),([5,5], 40),([6,6], 16)]
def c2GroupHessian136_00 : Poly := List.flatten [c2GroupHessian136_00Chunk0]
theorem c2GroupHessian136_00_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian136_00 := by kernel_rfl
private def c2GroupHessian136_01Chunk0 : Poly := [([0,0], 12),([0,1], 4),([0,5], -40),([0,6], 4),([0,7], -20),([1,7], -20),([2,5], -40),([5,8], -40),([6,7], -20)]
def c2GroupHessian136_01 : Poly := List.flatten [c2GroupHessian136_01Chunk0]
theorem c2GroupHessian136_01_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian136_01 := by kernel_rfl
private def c2GroupHessian136_02Chunk0 : Poly := [([0,0], -12),([0,1], -4),([0,5], -40),([0,6], -4),([0,7], 20),([1,7], 20),([3,5], -40),([5,5], -40),([5,9], -40),([6,7], 20)]
def c2GroupHessian136_02 : Poly := List.flatten [c2GroupHessian136_02Chunk0]
theorem c2GroupHessian136_02_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian136_02 := by kernel_rfl
private def c2GroupHessian136_03Chunk0 : Poly := [([0,0], -20),([0,1], -16),([0,4], -4),([0,5], 40),([0,6], -36),([1,4], -8),([1,6], -16),([4,6], -8),([5,8], 40),([5,9], 40),([6,6], -16)]
def c2GroupHessian136_03 : Poly := List.flatten [c2GroupHessian136_03Chunk0]
theorem c2GroupHessian136_03_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian136_03 := by kernel_rfl
private def c2GroupHessian136_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,8], 80),([2,2], 40),([2,8], 80),([7,7], 40),([8,8], 40)]
def c2GroupHessian136_11 : Poly := List.flatten [c2GroupHessian136_11Chunk0]
theorem c2GroupHessian136_11_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian136_11 := by kernel_rfl
private def c2GroupHessian136_12Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,3], 40),([0,5], 40),([0,8], 40),([0,9], 40),([2,3], 40),([2,5], 40),([2,9], 40),([3,8], 40),([5,8], 40),([7,7], -40),([8,9], 40)]
def c2GroupHessian136_12 : Poly := List.flatten [c2GroupHessian136_12Chunk0]
theorem c2GroupHessian136_12_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian136_12 := by kernel_rfl
private def c2GroupHessian136_13Chunk0 : Poly := [([0,0], -44),([0,2], -40),([0,4], 4),([0,6], -4),([0,7], 20),([0,8], -80),([0,9], -40),([2,8], -40),([2,9], -40),([4,7], 20),([6,7], 20),([8,8], -40),([8,9], -40)]
def c2GroupHessian136_13 : Poly := List.flatten [c2GroupHessian136_13Chunk0]
theorem c2GroupHessian136_13_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian136_13 := by kernel_rfl
private def c2GroupHessian136_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,9], 80),([3,3], 40),([3,5], 80),([3,9], 80),([5,5], 40),([5,9], 80),([7,7], 40),([9,9], 40)]
def c2GroupHessian136_22 : Poly := List.flatten [c2GroupHessian136_22Chunk0]
theorem c2GroupHessian136_22_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian136_22 := by kernel_rfl
private def c2GroupHessian136_23Chunk0 : Poly := [([0,0], -36),([0,3], -40),([0,4], -4),([0,5], -40),([0,6], 4),([0,7], -20),([0,8], -40),([0,9], -80),([3,8], -40),([3,9], -40),([4,7], -20),([5,8], -40),([5,9], -40),([6,7], -20),([8,9], -40),([9,9], -40)]
def c2GroupHessian136_23 : Poly := List.flatten [c2GroupHessian136_23Chunk0]
theorem c2GroupHessian136_23_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian136_23 := by kernel_rfl
private def c2GroupHessian136_33Chunk0 : Poly := [([0,0], 56),([0,4], 16),([0,6], 32),([0,8], 80),([0,9], 80),([4,4], 16),([4,6], 16),([6,6], 16),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian136_33 : Poly := List.flatten [c2GroupHessian136_33Chunk0]
theorem c2GroupHessian136_33_check : sumFast (c2TensorGroup136.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian136_33 := by kernel_rfl
end D4.Secondary
