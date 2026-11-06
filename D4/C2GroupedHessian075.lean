import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup75_det_check : c2TensorGroup75.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 101)) = true := by kernel_rfl
private def c2GroupHessian75_00Chunk0 : Poly := [([0,0], 320),([0,1], 320),([0,5], 320),([0,6], 320),([1,1], 80),([1,5], 160),([1,6], 160),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian75_00 : Poly := List.flatten [c2GroupHessian75_00Chunk0]
theorem c2GroupHessian75_00_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian75_00 := by kernel_rfl
private def c2GroupHessian75_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,5], 80),([0,6], 80)]
def c2GroupHessian75_01 : Poly := List.flatten [c2GroupHessian75_01Chunk0]
theorem c2GroupHessian75_01_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian75_01 := by kernel_rfl
private def c2GroupHessian75_02Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -240),([0,6], -80),([1,5], -80),([5,5], -80),([5,6], -80)]
def c2GroupHessian75_02 : Poly := List.flatten [c2GroupHessian75_02Chunk0]
theorem c2GroupHessian75_02_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian75_02 := by kernel_rfl
private def c2GroupHessian75_03Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -80),([0,6], -240),([1,6], -80),([5,6], -80),([6,6], -80)]
def c2GroupHessian75_03 : Poly := List.flatten [c2GroupHessian75_03Chunk0]
theorem c2GroupHessian75_03_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian75_03 := by kernel_rfl
private def c2GroupHessian75_11Chunk0 : Poly := [([0,0], 112),([0,2], 64),([0,7], -8),([0,8], 80),([2,2], 32),([2,7], -8),([2,8], 80),([7,7], 24),([7,8], -40),([8,8], 80)]
def c2GroupHessian75_11 : Poly := List.flatten [c2GroupHessian75_11Chunk0]
theorem c2GroupHessian75_11_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian75_11 := by kernel_rfl
private def c2GroupHessian75_12Chunk0 : Poly := [([0,0], -40),([0,2], 40),([0,3], 40),([0,5], -80),([0,7], -16),([0,8], 80),([0,9], 40),([2,3], 40),([2,7], 4),([2,9], 40),([3,7], -20),([3,8], 80),([7,7], -24),([7,8], 20),([7,9], -20),([8,9], 80)]
def c2GroupHessian75_12 : Poly := List.flatten [c2GroupHessian75_12Chunk0]
theorem c2GroupHessian75_12_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian75_12 := by kernel_rfl
private def c2GroupHessian75_13Chunk0 : Poly := [([0,0], -120),([0,2], -40),([0,4], -4),([0,6], -80),([0,7], 20),([0,8], -120),([0,9], -40),([2,4], -4),([2,8], -40),([2,9], -40),([4,7], 8),([4,8], -20),([7,8], 20),([7,9], 20),([8,8], -80),([8,9], -80)]
def c2GroupHessian75_13 : Poly := List.flatten [c2GroupHessian75_13Chunk0]
theorem c2GroupHessian75_13_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian75_13 := by kernel_rfl
private def c2GroupHessian75_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 40),([0,9], 160),([3,3], 80),([3,7], 40),([3,9], 160),([5,5], 80),([7,7], 24),([7,9], 40),([9,9], 80)]
def c2GroupHessian75_22 : Poly := List.flatten [c2GroupHessian75_22Chunk0]
theorem c2GroupHessian75_22_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian75_22 := by kernel_rfl
private def c2GroupHessian75_23Chunk0 : Poly := [([0,3], -80),([0,4], -20),([0,5], 80),([0,6], 80),([0,7], -20),([0,8], -80),([0,9], -160),([3,4], -20),([3,8], -80),([3,9], -80),([4,7], -8),([4,9], -20),([5,6], 80),([7,8], -20),([7,9], -20),([8,9], -80),([9,9], -80)]
def c2GroupHessian75_23 : Poly := List.flatten [c2GroupHessian75_23Chunk0]
theorem c2GroupHessian75_23_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian75_23 := by kernel_rfl
private def c2GroupHessian75_33Chunk0 : Poly := [([0,0], 160),([0,4], 40),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 24),([4,8], 40),([4,9], 40),([6,6], 80),([8,8], 80),([8,9], 160),([9,9], 80)]
def c2GroupHessian75_33 : Poly := List.flatten [c2GroupHessian75_33Chunk0]
theorem c2GroupHessian75_33_check : sumFast (c2TensorGroup75.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian75_33 := by kernel_rfl
end D4.Secondary
