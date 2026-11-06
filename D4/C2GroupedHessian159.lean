import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup159_det_check : c2TensorGroup159.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 202)) = true := by kernel_rfl
private def c2GroupHessian159_00Chunk0 : Poly := [([0,0], 48),([0,1], 8),([0,5], 8),([0,6], 16),([1,1], 16),([1,5], -16),([1,6], 8),([5,5], 16),([5,6], 8),([6,6], 8)]
def c2GroupHessian159_00 : Poly := List.flatten [c2GroupHessian159_00Chunk0]
theorem c2GroupHessian159_00_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian159_00 := by kernel_rfl
private def c2GroupHessian159_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40)]
def c2GroupHessian159_01 : Poly := List.flatten [c2GroupHessian159_01Chunk0]
theorem c2GroupHessian159_01_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian159_01 := by kernel_rfl
private def c2GroupHessian159_02Chunk0 : Poly := [([0,0], -40),([0,1], 20),([0,5], -24),([0,7], -40),([1,3], 20),([1,5], 8),([1,9], 20),([3,5], -20),([5,5], -16),([5,6], -4),([5,9], -20)]
def c2GroupHessian159_02 : Poly := List.flatten [c2GroupHessian159_02Chunk0]
theorem c2GroupHessian159_02_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian159_02 := by kernel_rfl
private def c2GroupHessian159_03Chunk0 : Poly := [([0,0], -48),([0,1], -4),([0,5], -4),([0,6], -16),([0,8], -40),([1,4], 20),([1,6], -4),([1,9], -20),([4,5], -20),([5,6], -4),([5,9], 20),([6,6], -8)]
def c2GroupHessian159_03 : Poly := List.flatten [c2GroupHessian159_03Chunk0]
theorem c2GroupHessian159_03_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian159_03 := by kernel_rfl
private def c2GroupHessian159_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian159_11 : Poly := List.flatten [c2GroupHessian159_11Chunk0]
theorem c2GroupHessian159_11_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian159_11 := by kernel_rfl
private def c2GroupHessian159_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([2,7], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian159_12 : Poly := List.flatten [c2GroupHessian159_12Chunk0]
theorem c2GroupHessian159_12_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian159_12 := by kernel_rfl
private def c2GroupHessian159_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([2,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian159_13 : Poly := List.flatten [c2GroupHessian159_13Chunk0]
theorem c2GroupHessian159_13_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian159_13 := by kernel_rfl
private def c2GroupHessian159_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 40),([0,7], 80),([0,9], 80),([3,3], 40),([3,5], 40),([3,9], 80),([5,5], 16),([5,9], 40),([7,7], 40),([9,9], 40)]
def c2GroupHessian159_22 : Poly := List.flatten [c2GroupHessian159_22Chunk0]
theorem c2GroupHessian159_22_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian159_22 := by kernel_rfl
private def c2GroupHessian159_23Chunk0 : Poly := [([0,0], 40),([0,4], 40),([0,5], 4),([0,7], 40),([0,8], 40),([0,9], -40),([3,4], 40),([3,9], -40),([4,5], 20),([4,9], 40),([5,6], 4),([5,9], -20),([7,8], 40),([9,9], -40)]
def c2GroupHessian159_23 : Poly := List.flatten [c2GroupHessian159_23Chunk0]
theorem c2GroupHessian159_23_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian159_23 := by kernel_rfl
private def c2GroupHessian159_33Chunk0 : Poly := [([0,0], 48),([0,6], 16),([0,8], 80),([4,4], 40),([4,9], -80),([6,6], 8),([8,8], 40),([9,9], 40)]
def c2GroupHessian159_33 : Poly := List.flatten [c2GroupHessian159_33Chunk0]
theorem c2GroupHessian159_33_check : sumFast (c2TensorGroup159.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian159_33 := by kernel_rfl
end D4.Secondary
