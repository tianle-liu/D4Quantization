import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup112_det_check : c2TensorGroup112.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 144)) = true := by kernel_rfl
private def c2GroupHessian112_00Chunk0 : Poly := [([0,0], 112),([0,1], -8),([0,5], 160),([0,6], 160),([1,1], 24),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian112_00 : Poly := List.flatten [c2GroupHessian112_00Chunk0]
theorem c2GroupHessian112_00_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian112_00 := by kernel_rfl
private def c2GroupHessian112_01Chunk0 : Poly := [([0,0], 72),([0,1], -24),([0,2], -80),([0,7], 40),([0,8], 40),([1,7], -20),([1,8], -20),([2,5], -80),([2,6], -80)]
def c2GroupHessian112_01 : Poly := List.flatten [c2GroupHessian112_01Chunk0]
theorem c2GroupHessian112_01_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian112_01 := by kernel_rfl
private def c2GroupHessian112_02Chunk0 : Poly := [([0,0], -120),([0,1], 20),([0,3], -80),([0,5], -160),([0,6], -80),([0,7], -40),([0,9], -4),([1,7], 20),([1,9], 8),([3,5], -80),([3,6], -80),([5,5], -80),([5,6], -80)]
def c2GroupHessian112_02 : Poly := List.flatten [c2GroupHessian112_02Chunk0]
theorem c2GroupHessian112_02_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian112_02 := by kernel_rfl
private def c2GroupHessian112_03Chunk0 : Poly := [([0,0], -112),([0,1], 4),([0,4], -80),([0,5], -80),([0,6], -160),([0,8], -40),([0,9], 4),([1,8], 20),([1,9], -8),([4,5], -80),([4,6], -80),([5,6], -80),([6,6], -80)]
def c2GroupHessian112_03 : Poly := List.flatten [c2GroupHessian112_03Chunk0]
theorem c2GroupHessian112_03_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian112_03 := by kernel_rfl
private def c2GroupHessian112_11Chunk0 : Poly := [([0,0], 192),([0,7], 240),([0,8], 240),([2,2], 80),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian112_11 : Poly := List.flatten [c2GroupHessian112_11Chunk0]
theorem c2GroupHessian112_11_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian112_11 := by kernel_rfl
private def c2GroupHessian112_12Chunk0 : Poly := [([0,0], -120),([0,2], 80),([0,7], -200),([0,8], -80),([0,9], -24),([2,3], 80),([2,5], 80),([7,7], -80),([7,8], -80),([7,9], -20),([8,9], -20)]
def c2GroupHessian112_12 : Poly := List.flatten [c2GroupHessian112_12Chunk0]
theorem c2GroupHessian112_12_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian112_12 := by kernel_rfl
private def c2GroupHessian112_13Chunk0 : Poly := [([0,0], -72),([0,2], 80),([0,7], -40),([0,8], -160),([0,9], 24),([2,4], 80),([2,6], 80),([7,8], -80),([7,9], 20),([8,8], -80),([8,9], 20)]
def c2GroupHessian112_13 : Poly := List.flatten [c2GroupHessian112_13Chunk0]
theorem c2GroupHessian112_13_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian112_13 := by kernel_rfl
private def c2GroupHessian112_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 40),([3,3], 80),([3,5], 160),([5,5], 80),([7,7], 80),([7,9], 40),([9,9], 24)]
def c2GroupHessian112_22 : Poly := List.flatten [c2GroupHessian112_22Chunk0]
theorem c2GroupHessian112_22_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian112_22 := by kernel_rfl
private def c2GroupHessian112_23Chunk0 : Poly := [([0,0], 120),([0,3], 80),([0,4], 80),([0,5], 80),([0,6], 80),([0,7], 40),([0,8], 80),([0,9], -16),([3,4], 80),([3,6], 80),([4,5], 80),([5,6], 80),([7,8], 80),([7,9], -20),([8,9], 20),([9,9], -24)]
def c2GroupHessian112_23 : Poly := List.flatten [c2GroupHessian112_23Chunk0]
theorem c2GroupHessian112_23_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian112_23 := by kernel_rfl
private def c2GroupHessian112_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], 160),([0,8], 80),([0,9], -8),([4,4], 80),([4,6], 160),([6,6], 80),([8,8], 80),([8,9], -40),([9,9], 24)]
def c2GroupHessian112_33 : Poly := List.flatten [c2GroupHessian112_33Chunk0]
theorem c2GroupHessian112_33_check : sumFast (c2TensorGroup112.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian112_33 := by kernel_rfl
end D4.Secondary
