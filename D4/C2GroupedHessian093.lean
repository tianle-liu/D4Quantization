import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup93_det_check : c2TensorGroup93.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 121)) = true := by kernel_rfl
private def c2GroupHessian93_00Chunk0 : Poly := [([0,0], 320),([0,1], 320),([0,5], 320),([0,6], 320),([1,1], 80),([1,5], 160),([1,6], 160),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian93_00 : Poly := List.flatten [c2GroupHessian93_00Chunk0]
theorem c2GroupHessian93_00_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian93_00 := by kernel_rfl
private def c2GroupHessian93_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,5], 80),([0,6], 80)]
def c2GroupHessian93_01 : Poly := List.flatten [c2GroupHessian93_01Chunk0]
theorem c2GroupHessian93_01_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian93_01 := by kernel_rfl
private def c2GroupHessian93_02Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -240),([0,6], -80),([1,5], -80),([5,5], -80),([5,6], -80)]
def c2GroupHessian93_02 : Poly := List.flatten [c2GroupHessian93_02Chunk0]
theorem c2GroupHessian93_02_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian93_02 := by kernel_rfl
private def c2GroupHessian93_03Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -80),([0,6], -240),([1,6], -80),([5,6], -80),([6,6], -80)]
def c2GroupHessian93_03 : Poly := List.flatten [c2GroupHessian93_03Chunk0]
theorem c2GroupHessian93_03_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian93_03 := by kernel_rfl
private def c2GroupHessian93_11Chunk0 : Poly := [([0,0], 112),([0,2], 64),([0,7], 64),([0,8], -8),([2,2], 32),([2,7], 64),([2,8], -8),([7,7], 32),([7,8], -8),([8,8], 24)]
def c2GroupHessian93_11 : Poly := List.flatten [c2GroupHessian93_11Chunk0]
theorem c2GroupHessian93_11_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian93_11 := by kernel_rfl
private def c2GroupHessian93_12Chunk0 : Poly := [([0,0], -120),([0,2], -40),([0,3], -4),([0,5], -80),([0,7], -72),([0,8], 20),([0,9], -40),([2,3], -4),([2,7], -32),([2,9], -40),([3,7], -4),([3,8], 8),([7,7], -32),([7,8], 4),([7,9], -40),([8,9], 20)]
def c2GroupHessian93_12 : Poly := List.flatten [c2GroupHessian93_12Chunk0]
theorem c2GroupHessian93_12_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian93_12 := by kernel_rfl
private def c2GroupHessian93_13Chunk0 : Poly := [([0,0], -40),([0,2], 40),([0,4], 32),([0,6], -80),([0,7], 40),([0,8], -16),([0,9], 40),([2,4], 32),([2,8], 4),([2,9], 40),([4,7], 32),([4,8], -4),([7,8], 4),([7,9], 40),([8,8], -24),([8,9], -20)]
def c2GroupHessian93_13 : Poly := List.flatten [c2GroupHessian93_13Chunk0]
theorem c2GroupHessian93_13_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian93_13 := by kernel_rfl
private def c2GroupHessian93_22Chunk0 : Poly := [([0,0], 160),([0,3], 40),([0,5], 160),([0,7], 80),([0,9], 160),([3,3], 24),([3,7], 8),([3,9], 40),([5,5], 80),([7,7], 32),([7,9], 80),([9,9], 80)]
def c2GroupHessian93_22 : Poly := List.flatten [c2GroupHessian93_22Chunk0]
theorem c2GroupHessian93_22_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian93_22 := by kernel_rfl
private def c2GroupHessian93_23Chunk0 : Poly := [([0,3], -20),([0,4], -40),([0,5], 80),([0,6], 80),([0,7], -40),([0,8], -20),([0,9], -160),([3,4], -4),([3,8], -8),([3,9], -20),([4,7], -32),([4,9], -40),([5,6], 80),([7,8], -4),([7,9], -40),([8,9], -20),([9,9], -80)]
def c2GroupHessian93_23 : Poly := List.flatten [c2GroupHessian93_23Chunk0]
theorem c2GroupHessian93_23_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian93_23 := by kernel_rfl
private def c2GroupHessian93_33Chunk0 : Poly := [([0,0], 160),([0,4], 80),([0,6], 160),([0,8], 40),([0,9], 160),([4,4], 32),([4,8], 8),([4,9], 80),([6,6], 80),([8,8], 24),([8,9], 40),([9,9], 80)]
def c2GroupHessian93_33 : Poly := List.flatten [c2GroupHessian93_33Chunk0]
theorem c2GroupHessian93_33_check : sumFast (c2TensorGroup93.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian93_33 := by kernel_rfl
end D4.Secondary
