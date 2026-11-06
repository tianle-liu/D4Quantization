import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup92_det_check : c2TensorGroup92.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 119)) = true := by kernel_rfl
private def c2GroupHessian92_00Chunk0 : Poly := [([0,0], 320),([0,1], 320),([0,5], 320),([0,6], 320),([1,1], 80),([1,5], 160),([1,6], 160),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian92_00 : Poly := List.flatten [c2GroupHessian92_00Chunk0]
theorem c2GroupHessian92_00_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian92_00 := by kernel_rfl
private def c2GroupHessian92_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,5], 80),([0,6], 80)]
def c2GroupHessian92_01 : Poly := List.flatten [c2GroupHessian92_01Chunk0]
theorem c2GroupHessian92_01_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian92_01 := by kernel_rfl
private def c2GroupHessian92_02Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -240),([0,6], -80),([1,5], -80),([5,5], -80),([5,6], -80)]
def c2GroupHessian92_02 : Poly := List.flatten [c2GroupHessian92_02Chunk0]
theorem c2GroupHessian92_02_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian92_02 := by kernel_rfl
private def c2GroupHessian92_03Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -80),([0,6], -240),([1,6], -80),([5,6], -80),([6,6], -80)]
def c2GroupHessian92_03 : Poly := List.flatten [c2GroupHessian92_03Chunk0]
theorem c2GroupHessian92_03_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian92_03 := by kernel_rfl
private def c2GroupHessian92_11Chunk0 : Poly := [([0,0], 160),([0,2], 40),([0,7], 160),([0,8], 160),([2,2], 24),([2,7], 40),([2,8], 40),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian92_11 : Poly := List.flatten [c2GroupHessian92_11Chunk0]
theorem c2GroupHessian92_11_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian92_11 := by kernel_rfl
private def c2GroupHessian92_12Chunk0 : Poly := [([0,0], -120),([0,2], -4),([0,3], -40),([0,5], -80),([0,7], -120),([0,8], -40),([0,9], 20),([2,3], -4),([2,7], -20),([2,9], 8),([3,7], -40),([3,8], -40),([7,7], -80),([7,8], -80),([7,9], 20),([8,9], 20)]
def c2GroupHessian92_12 : Poly := List.flatten [c2GroupHessian92_12Chunk0]
theorem c2GroupHessian92_12_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian92_12 := by kernel_rfl
private def c2GroupHessian92_13Chunk0 : Poly := [([0,0], -160),([0,2], -20),([0,4], -40),([0,6], -80),([0,7], -80),([0,8], -160),([0,9], -20),([2,4], -4),([2,8], -20),([2,9], -8),([4,7], -40),([4,8], -40),([7,8], -80),([7,9], -20),([8,8], -80),([8,9], -20)]
def c2GroupHessian92_13 : Poly := List.flatten [c2GroupHessian92_13Chunk0]
theorem c2GroupHessian92_13_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian92_13 := by kernel_rfl
private def c2GroupHessian92_22Chunk0 : Poly := [([0,0], 112),([0,3], 64),([0,5], 160),([0,7], 80),([0,9], -8),([3,3], 32),([3,7], 80),([3,9], -8),([5,5], 80),([7,7], 80),([7,9], -40),([9,9], 24)]
def c2GroupHessian92_22 : Poly := List.flatten [c2GroupHessian92_22Chunk0]
theorem c2GroupHessian92_22_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian92_22 := by kernel_rfl
private def c2GroupHessian92_23Chunk0 : Poly := [([0,0], 120),([0,3], 40),([0,4], 32),([0,5], 80),([0,6], 80),([0,7], 80),([0,8], 40),([0,9], -16),([3,4], 32),([3,8], 40),([3,9], 4),([4,7], 40),([4,9], -4),([5,6], 80),([7,8], 80),([7,9], 20),([8,9], -20),([9,9], -24)]
def c2GroupHessian92_23 : Poly := List.flatten [c2GroupHessian92_23Chunk0]
theorem c2GroupHessian92_23_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian92_23 := by kernel_rfl
private def c2GroupHessian92_33Chunk0 : Poly := [([0,0], 160),([0,4], 80),([0,6], 160),([0,8], 160),([0,9], 40),([4,4], 32),([4,8], 80),([4,9], 8),([6,6], 80),([8,8], 80),([8,9], 40),([9,9], 24)]
def c2GroupHessian92_33 : Poly := List.flatten [c2GroupHessian92_33Chunk0]
theorem c2GroupHessian92_33_check : sumFast (c2TensorGroup92.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian92_33 := by kernel_rfl
end D4.Secondary
