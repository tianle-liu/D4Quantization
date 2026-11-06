import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup23_det_check : c2TensorGroup23.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 38)) = true := by kernel_rfl
private def c2GroupHessian23_00Chunk0 : Poly := [([0,0], 192),([0,5], 240),([0,6], 240),([1,1], 80),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian23_00 : Poly := List.flatten [c2GroupHessian23_00Chunk0]
theorem c2GroupHessian23_00_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian23_00 := by kernel_rfl
private def c2GroupHessian23_01Chunk0 : Poly := [([0,0], 72),([0,1], -80),([0,2], -24),([0,5], 40),([0,6], 40),([1,7], -80),([1,8], -80),([2,5], -20),([2,6], -20)]
def c2GroupHessian23_01 : Poly := List.flatten [c2GroupHessian23_01Chunk0]
theorem c2GroupHessian23_01_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian23_01 := by kernel_rfl
private def c2GroupHessian23_02Chunk0 : Poly := [([0,0], -120),([0,1], 80),([0,5], -200),([0,6], -80),([0,9], -24),([1,3], 80),([1,7], 80),([5,5], -80),([5,6], -80),([5,9], -20),([6,9], -20)]
def c2GroupHessian23_02 : Poly := List.flatten [c2GroupHessian23_02Chunk0]
theorem c2GroupHessian23_02_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian23_02 := by kernel_rfl
private def c2GroupHessian23_03Chunk0 : Poly := [([0,0], -72),([0,1], 80),([0,5], -40),([0,6], -160),([0,9], 24),([1,4], 80),([1,8], 80),([5,6], -80),([5,9], 20),([6,6], -80),([6,9], 20)]
def c2GroupHessian23_03 : Poly := List.flatten [c2GroupHessian23_03Chunk0]
theorem c2GroupHessian23_03_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian23_03 := by kernel_rfl
private def c2GroupHessian23_11Chunk0 : Poly := [([0,0], 112),([0,2], -8),([0,7], 160),([0,8], 160),([2,2], 24),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian23_11 : Poly := List.flatten [c2GroupHessian23_11Chunk0]
theorem c2GroupHessian23_11_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian23_11 := by kernel_rfl
private def c2GroupHessian23_12Chunk0 : Poly := [([0,0], -120),([0,2], 20),([0,3], -80),([0,5], -40),([0,7], -160),([0,8], -80),([0,9], -4),([2,5], 20),([2,9], 8),([3,7], -80),([3,8], -80),([7,7], -80),([7,8], -80)]
def c2GroupHessian23_12 : Poly := List.flatten [c2GroupHessian23_12Chunk0]
theorem c2GroupHessian23_12_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian23_12 := by kernel_rfl
private def c2GroupHessian23_13Chunk0 : Poly := [([0,0], -112),([0,2], 4),([0,4], -80),([0,6], -40),([0,7], -80),([0,8], -160),([0,9], 4),([2,6], 20),([2,9], -8),([4,7], -80),([4,8], -80),([7,8], -80),([8,8], -80)]
def c2GroupHessian23_13 : Poly := List.flatten [c2GroupHessian23_13Chunk0]
theorem c2GroupHessian23_13_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian23_13 := by kernel_rfl
private def c2GroupHessian23_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 40),([3,3], 80),([3,7], 160),([5,5], 80),([5,9], 40),([7,7], 80),([9,9], 24)]
def c2GroupHessian23_22 : Poly := List.flatten [c2GroupHessian23_22Chunk0]
theorem c2GroupHessian23_22_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian23_22 := by kernel_rfl
private def c2GroupHessian23_23Chunk0 : Poly := [([0,0], 120),([0,3], 80),([0,4], 80),([0,5], 40),([0,6], 80),([0,7], 80),([0,8], 80),([0,9], -16),([3,4], 80),([3,8], 80),([4,7], 80),([5,6], 80),([5,9], -20),([6,9], 20),([7,8], 80),([9,9], -24)]
def c2GroupHessian23_23 : Poly := List.flatten [c2GroupHessian23_23Chunk0]
theorem c2GroupHessian23_23_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian23_23 := by kernel_rfl
private def c2GroupHessian23_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], 80),([0,8], 160),([0,9], -8),([4,4], 80),([4,8], 160),([6,6], 80),([6,9], -40),([8,8], 80),([9,9], 24)]
def c2GroupHessian23_33 : Poly := List.flatten [c2GroupHessian23_33Chunk0]
theorem c2GroupHessian23_33_check : sumFast (c2TensorGroup23.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian23_33 := by kernel_rfl
end D4.Secondary
