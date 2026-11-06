import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup160_det_check : c2TensorGroup160.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 203)) = true := by kernel_rfl
private def c2GroupHessian160_00Chunk0 : Poly := [([0,0], 112),([0,1], 64),([0,5], -8),([0,6], 80),([1,1], 32),([1,5], -8),([1,6], 80),([5,5], 24),([5,6], -40),([6,6], 80)]
def c2GroupHessian160_00 : Poly := List.flatten [c2GroupHessian160_00Chunk0]
theorem c2GroupHessian160_00_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian160_00 := by kernel_rfl
private def c2GroupHessian160_01Chunk0 : Poly := [([0,0], 160),([0,2], 80),([0,7], 80),([0,8], 80)]
def c2GroupHessian160_01 : Poly := List.flatten [c2GroupHessian160_01Chunk0]
theorem c2GroupHessian160_01_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian160_01 := by kernel_rfl
private def c2GroupHessian160_02Chunk0 : Poly := [([0,0], -40),([0,1], 40),([0,3], 40),([0,5], -16),([0,6], 80),([0,7], -80),([0,9], 40),([1,3], 40),([1,5], 4),([1,9], 40),([3,5], -20),([3,6], 80),([5,5], -24),([5,6], 20),([5,9], -20),([6,9], 80)]
def c2GroupHessian160_02 : Poly := List.flatten [c2GroupHessian160_02Chunk0]
theorem c2GroupHessian160_02_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian160_02 := by kernel_rfl
private def c2GroupHessian160_03Chunk0 : Poly := [([0,0], -120),([0,1], -40),([0,4], -4),([0,5], 20),([0,6], -120),([0,8], -80),([0,9], -40),([1,4], -4),([1,6], -40),([1,9], -40),([4,5], 8),([4,6], -20),([5,6], 20),([5,9], 20),([6,6], -80),([6,9], -80)]
def c2GroupHessian160_03 : Poly := List.flatten [c2GroupHessian160_03Chunk0]
theorem c2GroupHessian160_03_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian160_03 := by kernel_rfl
private def c2GroupHessian160_11Chunk0 : Poly := [([0,0], 320),([0,2], 320),([0,7], 320),([0,8], 320),([2,2], 80),([2,7], 160),([2,8], 160),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian160_11 : Poly := List.flatten [c2GroupHessian160_11Chunk0]
theorem c2GroupHessian160_11_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian160_11 := by kernel_rfl
private def c2GroupHessian160_12Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -240),([0,8], -80),([2,7], -80),([7,7], -80),([7,8], -80)]
def c2GroupHessian160_12 : Poly := List.flatten [c2GroupHessian160_12Chunk0]
theorem c2GroupHessian160_12_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian160_12 := by kernel_rfl
private def c2GroupHessian160_13Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -80),([0,8], -240),([2,8], -80),([7,8], -80),([8,8], -80)]
def c2GroupHessian160_13 : Poly := List.flatten [c2GroupHessian160_13Chunk0]
theorem c2GroupHessian160_13_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian160_13 := by kernel_rfl
private def c2GroupHessian160_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 40),([0,7], 160),([0,9], 160),([3,3], 80),([3,5], 40),([3,9], 160),([5,5], 24),([5,9], 40),([7,7], 80),([9,9], 80)]
def c2GroupHessian160_22 : Poly := List.flatten [c2GroupHessian160_22Chunk0]
theorem c2GroupHessian160_22_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian160_22 := by kernel_rfl
private def c2GroupHessian160_23Chunk0 : Poly := [([0,3], -80),([0,4], -20),([0,5], -20),([0,6], -80),([0,7], 80),([0,8], 80),([0,9], -160),([3,4], -20),([3,6], -80),([3,9], -80),([4,5], -8),([4,9], -20),([5,6], -20),([5,9], -20),([6,9], -80),([7,8], 80),([9,9], -80)]
def c2GroupHessian160_23 : Poly := List.flatten [c2GroupHessian160_23Chunk0]
theorem c2GroupHessian160_23_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian160_23 := by kernel_rfl
private def c2GroupHessian160_33Chunk0 : Poly := [([0,0], 160),([0,4], 40),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 24),([4,6], 40),([4,9], 40),([6,6], 80),([6,9], 160),([8,8], 80),([9,9], 80)]
def c2GroupHessian160_33 : Poly := List.flatten [c2GroupHessian160_33Chunk0]
theorem c2GroupHessian160_33_check : sumFast (c2TensorGroup160.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian160_33 := by kernel_rfl
end D4.Secondary
