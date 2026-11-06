import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup45_det_check : c2TensorGroup45.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 63)) = true := by kernel_rfl
private def c2GroupHessian45_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], -8),([0,6], 160),([1,1], 80),([1,6], 160),([5,5], 24),([6,6], 80)]
def c2GroupHessian45_00 : Poly := List.flatten [c2GroupHessian45_00Chunk0]
theorem c2GroupHessian45_00_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian45_00 := by kernel_rfl
private def c2GroupHessian45_01Chunk0 : Poly := [([0,0], 72),([0,2], 40),([0,5], -24),([0,7], -80),([0,8], 40),([1,7], -80),([2,5], -20),([5,8], -20),([6,7], -80)]
def c2GroupHessian45_01 : Poly := List.flatten [c2GroupHessian45_01Chunk0]
theorem c2GroupHessian45_01_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian45_01 := by kernel_rfl
private def c2GroupHessian45_02Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,3], 80),([0,5], 8),([0,6], 80),([0,7], 80),([0,9], 80),([1,3], 80),([1,7], 80),([1,9], 80),([3,6], 80),([5,5], -24),([6,7], 80),([6,9], 80)]
def c2GroupHessian45_02 : Poly := List.flatten [c2GroupHessian45_02Chunk0]
theorem c2GroupHessian45_02_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian45_02 := by kernel_rfl
private def c2GroupHessian45_03Chunk0 : Poly := [([0,0], -120),([0,1], -80),([0,4], -4),([0,5], 20),([0,6], -160),([0,8], -40),([0,9], -80),([1,6], -80),([1,9], -80),([4,5], 8),([5,8], 20),([6,6], -80),([6,9], -80)]
def c2GroupHessian45_03 : Poly := List.flatten [c2GroupHessian45_03Chunk0]
theorem c2GroupHessian45_03_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian45_03 := by kernel_rfl
private def c2GroupHessian45_11Chunk0 : Poly := [([0,0], 192),([0,2], 240),([0,8], 240),([2,2], 80),([2,8], 160),([7,7], 80),([8,8], 80)]
def c2GroupHessian45_11 : Poly := List.flatten [c2GroupHessian45_11Chunk0]
theorem c2GroupHessian45_11_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian45_11 := by kernel_rfl
private def c2GroupHessian45_12Chunk0 : Poly := [([0,0], -72),([0,2], -40),([0,5], 24),([0,7], -80),([0,8], -40),([2,5], 20),([3,7], -80),([5,8], 20),([7,7], -80),([7,9], -80)]
def c2GroupHessian45_12 : Poly := List.flatten [c2GroupHessian45_12Chunk0]
theorem c2GroupHessian45_12_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian45_12 := by kernel_rfl
private def c2GroupHessian45_13Chunk0 : Poly := [([0,0], -120),([0,2], -80),([0,4], -24),([0,7], 80),([0,8], -200),([2,4], -20),([2,8], -80),([4,8], -20),([6,7], 80),([7,9], 80),([8,8], -80)]
def c2GroupHessian45_13 : Poly := List.flatten [c2GroupHessian45_13Chunk0]
theorem c2GroupHessian45_13_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian45_13 := by kernel_rfl
private def c2GroupHessian45_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], -8),([0,7], 160),([0,9], 160),([3,3], 80),([3,7], 160),([3,9], 160),([5,5], 24),([7,7], 80),([7,9], 160),([9,9], 80)]
def c2GroupHessian45_22 : Poly := List.flatten [c2GroupHessian45_22Chunk0]
theorem c2GroupHessian45_22_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian45_22 := by kernel_rfl
private def c2GroupHessian45_23Chunk0 : Poly := [([0,0], -40),([0,3], -80),([0,4], 4),([0,5], -20),([0,6], -80),([0,7], -80),([0,8], 40),([0,9], -160),([3,6], -80),([3,9], -80),([4,5], -8),([5,8], -20),([6,7], -80),([6,9], -80),([7,9], -80),([9,9], -80)]
def c2GroupHessian45_23 : Poly := List.flatten [c2GroupHessian45_23Chunk0]
theorem c2GroupHessian45_23_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian45_23 := by kernel_rfl
private def c2GroupHessian45_33Chunk0 : Poly := [([0,0], 160),([0,4], 40),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 24),([4,8], 40),([6,6], 80),([6,9], 160),([8,8], 80),([9,9], 80)]
def c2GroupHessian45_33 : Poly := List.flatten [c2GroupHessian45_33Chunk0]
theorem c2GroupHessian45_33_check : sumFast (c2TensorGroup45.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian45_33 := by kernel_rfl
end D4.Secondary
