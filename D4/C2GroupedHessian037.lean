import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup37_det_check : c2TensorGroup37.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 54)) = true := by kernel_rfl
private def c2GroupHessian37_00Chunk0 : Poly := [([0,0], 32),([0,5], 24),([0,6], 24),([1,1], 40),([5,5], 8),([5,6], 16),([6,6], 8)]
def c2GroupHessian37_00 : Poly := List.flatten [c2GroupHessian37_00Chunk0]
theorem c2GroupHessian37_00_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian37_00 := by kernel_rfl
private def c2GroupHessian37_01Chunk0 : Poly := [([0,0], 20),([0,1], -40),([0,2], 20),([0,5], 4),([0,6], 4),([1,7], -40),([1,8], -40),([2,5], 4),([2,6], 4)]
def c2GroupHessian37_01 : Poly := List.flatten [c2GroupHessian37_01Chunk0]
theorem c2GroupHessian37_01_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian37_01 := by kernel_rfl
private def c2GroupHessian37_02Chunk0 : Poly := [([0,0], -20),([0,1], 40),([0,5], -16),([0,6], -4),([0,9], -4),([1,3], 40),([1,7], 40),([5,5], -8),([5,6], -8),([5,9], 4),([6,9], 4)]
def c2GroupHessian37_02 : Poly := List.flatten [c2GroupHessian37_02Chunk0]
theorem c2GroupHessian37_02_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian37_02 := by kernel_rfl
private def c2GroupHessian37_03Chunk0 : Poly := [([0,0], -12),([0,1], 40),([0,5], -8),([0,6], -20),([0,9], 4),([1,4], 40),([1,8], 40),([5,6], -8),([5,9], -4),([6,6], -8),([6,9], -4)]
def c2GroupHessian37_03 : Poly := List.flatten [c2GroupHessian37_03Chunk0]
theorem c2GroupHessian37_03_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian37_03 := by kernel_rfl
private def c2GroupHessian37_11Chunk0 : Poly := [([0,0], 56),([0,2], 32),([0,7], 80),([0,8], 80),([2,2], 16),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian37_11 : Poly := List.flatten [c2GroupHessian37_11Chunk0]
theorem c2GroupHessian37_11_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian37_11 := by kernel_rfl
private def c2GroupHessian37_12Chunk0 : Poly := [([0,0], -56),([0,2], -16),([0,3], -40),([0,5], -4),([0,7], -80),([0,8], -40),([0,9], -8),([2,5], -4),([2,9], -8),([3,7], -40),([3,8], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian37_12 : Poly := List.flatten [c2GroupHessian37_12Chunk0]
theorem c2GroupHessian37_12_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian37_12 := by kernel_rfl
private def c2GroupHessian37_13Chunk0 : Poly := [([0,0], -44),([0,2], -4),([0,4], -40),([0,6], -4),([0,7], -40),([0,8], -80),([0,9], 8),([2,6], -4),([2,9], 8),([4,7], -40),([4,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian37_13 : Poly := List.flatten [c2GroupHessian37_13Chunk0]
theorem c2GroupHessian37_13_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian37_13 := by kernel_rfl
private def c2GroupHessian37_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 8),([0,7], 80),([0,9], 16),([3,3], 40),([3,7], 80),([5,5], 8),([5,9], -8),([7,7], 40),([9,9], 16)]
def c2GroupHessian37_22 : Poly := List.flatten [c2GroupHessian37_22Chunk0]
theorem c2GroupHessian37_22_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian37_22 := by kernel_rfl
private def c2GroupHessian37_23Chunk0 : Poly := [([0,0], 44),([0,3], 40),([0,4], 40),([0,5], 8),([0,6], 4),([0,7], 40),([0,8], 40),([0,9], -12),([3,4], 40),([3,8], 40),([4,7], 40),([5,6], 8),([5,9], 4),([6,9], -4),([7,8], 40),([9,9], -16)]
def c2GroupHessian37_23 : Poly := List.flatten [c2GroupHessian37_23Chunk0]
theorem c2GroupHessian37_23_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian37_23 := by kernel_rfl
private def c2GroupHessian37_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 16),([0,8], 80),([0,9], 8),([4,4], 40),([4,8], 80),([6,6], 8),([6,9], 8),([8,8], 40),([9,9], 16)]
def c2GroupHessian37_33 : Poly := List.flatten [c2GroupHessian37_33Chunk0]
theorem c2GroupHessian37_33_check : sumFast (c2TensorGroup37.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian37_33 := by kernel_rfl
end D4.Secondary
