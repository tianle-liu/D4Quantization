import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup6_det_check : c2TensorGroup6.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 7)) = true := by kernel_rfl
private def c2GroupHessian6_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], -8),([0,6], 80),([1,1], 80),([5,5], 24),([5,6], -40),([6,6], 80)]
def c2GroupHessian6_00 : Poly := List.flatten [c2GroupHessian6_00Chunk0]
theorem c2GroupHessian6_00_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian6_00 := by kernel_rfl
private def c2GroupHessian6_01Chunk0 : Poly := [([0,0], 112),([0,1], 80),([0,2], 80),([0,5], -4),([0,6], 40),([0,7], -4),([0,8], 40),([1,2], 80),([5,7], 8),([5,8], -20),([6,7], -20),([6,8], 80)]
def c2GroupHessian6_01 : Poly := List.flatten [c2GroupHessian6_01Chunk0]
theorem c2GroupHessian6_01_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian6_01 := by kernel_rfl
private def c2GroupHessian6_02Chunk0 : Poly := [([0,0], 8),([0,3], 80),([0,5], -12),([0,6], 40),([0,7], 4),([0,9], 40),([1,3], 80),([5,5], -24),([5,6], 20),([5,7], -8),([5,9], -20),([6,7], 20),([6,9], 80)]
def c2GroupHessian6_02 : Poly := List.flatten [c2GroupHessian6_02Chunk0]
theorem c2GroupHessian6_02_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian6_02 := by kernel_rfl
private def c2GroupHessian6_03Chunk0 : Poly := [([0,0], -72),([0,4], 80),([0,5], 24),([0,6], -160),([0,8], -40),([0,9], -40),([1,4], 80),([5,6], 20),([5,8], 20),([5,9], 20),([6,6], -80),([6,8], -80),([6,9], -80)]
def c2GroupHessian6_03 : Poly := List.flatten [c2GroupHessian6_03Chunk0]
theorem c2GroupHessian6_03_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian6_03 := by kernel_rfl
private def c2GroupHessian6_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], -8),([0,8], 80),([2,2], 80),([7,7], 24),([7,8], -40),([8,8], 80)]
def c2GroupHessian6_11 : Poly := List.flatten [c2GroupHessian6_11Chunk0]
theorem c2GroupHessian6_11_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian6_11 := by kernel_rfl
private def c2GroupHessian6_12Chunk0 : Poly := [([0,0], 8),([0,3], 80),([0,5], 4),([0,7], -12),([0,8], 40),([0,9], 40),([2,3], 80),([5,7], -8),([5,8], 20),([7,7], -24),([7,8], 20),([7,9], -20),([8,9], 80)]
def c2GroupHessian6_12 : Poly := List.flatten [c2GroupHessian6_12Chunk0]
theorem c2GroupHessian6_12_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian6_12 := by kernel_rfl
private def c2GroupHessian6_13Chunk0 : Poly := [([0,0], -72),([0,4], 80),([0,6], -40),([0,7], 24),([0,8], -160),([0,9], -40),([2,4], 80),([6,7], 20),([6,8], -80),([7,8], 20),([7,9], 20),([8,8], -80),([8,9], -80)]
def c2GroupHessian6_13 : Poly := List.flatten [c2GroupHessian6_13Chunk0]
theorem c2GroupHessian6_13_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian6_13 := by kernel_rfl
private def c2GroupHessian6_22Chunk0 : Poly := [([0,0], 32),([0,5], 32),([0,7], 32),([0,9], 80),([3,3], 80),([5,5], 24),([5,7], 16),([5,9], 40),([7,7], 24),([7,9], 40),([9,9], 80)]
def c2GroupHessian6_22 : Poly := List.flatten [c2GroupHessian6_22Chunk0]
theorem c2GroupHessian6_22_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian6_22 := by kernel_rfl
private def c2GroupHessian6_23Chunk0 : Poly := [([0,0], -48),([0,5], -24),([0,6], -40),([0,7], -24),([0,8], -40),([0,9], -160),([3,4], 80),([5,6], -20),([5,8], -20),([5,9], -20),([6,7], -20),([6,9], -80),([7,8], -20),([7,9], -20),([8,9], -80),([9,9], -80)]
def c2GroupHessian6_23 : Poly := List.flatten [c2GroupHessian6_23Chunk0]
theorem c2GroupHessian6_23_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian6_23 := by kernel_rfl
private def c2GroupHessian6_33Chunk0 : Poly := [([0,0], 192),([0,6], 240),([0,8], 240),([0,9], 240),([4,4], 80),([6,6], 80),([6,8], 160),([6,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c2GroupHessian6_33 : Poly := List.flatten [c2GroupHessian6_33Chunk0]
theorem c2GroupHessian6_33_check : sumFast (c2TensorGroup6.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian6_33 := by kernel_rfl
end D4.Secondary
