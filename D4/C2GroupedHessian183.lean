import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup183_det_check : c2TensorGroup183.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 230)) = true := by kernel_rfl
private def c2GroupHessian183_00Chunk0 : Poly := [([0,0], 48),([0,1], 8),([0,5], 16),([0,6], 8),([1,1], 16),([1,5], 8),([1,6], -16),([5,5], 8),([5,6], 8),([6,6], 16)]
def c2GroupHessian183_00 : Poly := List.flatten [c2GroupHessian183_00Chunk0]
theorem c2GroupHessian183_00_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian183_00 := by kernel_rfl
private def c2GroupHessian183_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40)]
def c2GroupHessian183_01 : Poly := List.flatten [c2GroupHessian183_01Chunk0]
theorem c2GroupHessian183_01_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian183_01 := by kernel_rfl
private def c2GroupHessian183_02Chunk0 : Poly := [([0,0], -44),([0,1], -8),([0,3], 4),([0,5], -12),([0,6], 8),([0,7], -40),([1,3], 16),([1,5], -4),([1,9], -20),([3,5], 4),([3,6], -8),([5,5], -8),([5,6], -4),([6,9], 20)]
def c2GroupHessian183_02 : Poly := List.flatten [c2GroupHessian183_02Chunk0]
theorem c2GroupHessian183_02_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian183_02 := by kernel_rfl
private def c2GroupHessian183_03Chunk0 : Poly := [([0,0], -40),([0,1], 20),([0,4], 4),([0,6], -24),([0,8], -40),([1,4], 16),([1,6], 8),([1,9], 20),([4,5], 4),([4,6], -8),([5,6], -4),([6,6], -16),([6,9], -20)]
def c2GroupHessian183_03 : Poly := List.flatten [c2GroupHessian183_03Chunk0]
theorem c2GroupHessian183_03_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian183_03 := by kernel_rfl
private def c2GroupHessian183_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian183_11 : Poly := List.flatten [c2GroupHessian183_11Chunk0]
theorem c2GroupHessian183_11_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian183_11 := by kernel_rfl
private def c2GroupHessian183_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([2,7], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian183_12 : Poly := List.flatten [c2GroupHessian183_12Chunk0]
theorem c2GroupHessian183_12_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian183_12 := by kernel_rfl
private def c2GroupHessian183_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([2,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian183_13 : Poly := List.flatten [c2GroupHessian183_13Chunk0]
theorem c2GroupHessian183_13_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian183_13 := by kernel_rfl
private def c2GroupHessian183_22Chunk0 : Poly := [([0,0], 56),([0,3], -16),([0,5], 8),([0,7], 80),([0,9], 40),([3,3], 16),([3,5], -8),([3,9], -40),([5,5], 8),([7,7], 40),([9,9], 40)]
def c2GroupHessian183_22 : Poly := List.flatten [c2GroupHessian183_22Chunk0]
theorem c2GroupHessian183_22_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian183_22 := by kernel_rfl
private def c2GroupHessian183_23Chunk0 : Poly := [([0,0], 20),([0,3], 20),([0,4], -8),([0,6], -8),([0,7], 40),([0,8], 40),([0,9], -60),([3,4], 16),([3,6], 8),([3,9], 20),([4,5], -4),([4,9], -20),([5,6], 4),([6,9], -20),([7,8], 40),([9,9], -40)]
def c2GroupHessian183_23 : Poly := List.flatten [c2GroupHessian183_23Chunk0]
theorem c2GroupHessian183_23_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian183_23 := by kernel_rfl
private def c2GroupHessian183_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 40),([0,8], 80),([0,9], 80),([4,4], 16),([4,6], 16),([4,9], 40),([6,6], 16),([6,9], 40),([8,8], 40),([9,9], 40)]
def c2GroupHessian183_33 : Poly := List.flatten [c2GroupHessian183_33Chunk0]
theorem c2GroupHessian183_33_check : sumFast (c2TensorGroup183.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian183_33 := by kernel_rfl
end D4.Secondary
