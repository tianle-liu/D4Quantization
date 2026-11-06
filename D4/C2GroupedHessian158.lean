import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup158_det_check : c2TensorGroup158.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 200)) = true := by kernel_rfl
private def c2GroupHessian158_00Chunk0 : Poly := [([0,0], 112),([0,1], -8),([0,5], 64),([0,6], 64),([1,1], 24),([1,5], -8),([1,6], -8),([5,5], 32),([5,6], 64),([6,6], 32)]
def c2GroupHessian158_00 : Poly := List.flatten [c2GroupHessian158_00Chunk0]
theorem c2GroupHessian158_00_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian158_00 := by kernel_rfl
private def c2GroupHessian158_01Chunk0 : Poly := [([0,0], 160),([0,2], 80),([0,7], 80),([0,8], 80)]
def c2GroupHessian158_01 : Poly := List.flatten [c2GroupHessian158_01Chunk0]
theorem c2GroupHessian158_01_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian158_01 := by kernel_rfl
private def c2GroupHessian158_02Chunk0 : Poly := [([0,0], -120),([0,1], 20),([0,3], -40),([0,5], -72),([0,6], -40),([0,7], -80),([0,9], -4),([1,3], 20),([1,5], 4),([1,9], 8),([3,5], -40),([3,6], -40),([5,5], -32),([5,6], -32),([5,9], -4),([6,9], -4)]
def c2GroupHessian158_02 : Poly := List.flatten [c2GroupHessian158_02Chunk0]
theorem c2GroupHessian158_02_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian158_02 := by kernel_rfl
private def c2GroupHessian158_03Chunk0 : Poly := [([0,0], -112),([0,1], 4),([0,4], -40),([0,5], -32),([0,6], -64),([0,8], -80),([0,9], 4),([1,4], 20),([1,6], 4),([1,9], -8),([4,5], -40),([4,6], -40),([5,6], -32),([5,9], 4),([6,6], -32),([6,9], 4)]
def c2GroupHessian158_03 : Poly := List.flatten [c2GroupHessian158_03Chunk0]
theorem c2GroupHessian158_03_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian158_03 := by kernel_rfl
private def c2GroupHessian158_11Chunk0 : Poly := [([0,0], 320),([0,2], 320),([0,7], 320),([0,8], 320),([2,2], 80),([2,7], 160),([2,8], 160),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian158_11 : Poly := List.flatten [c2GroupHessian158_11Chunk0]
theorem c2GroupHessian158_11_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian158_11 := by kernel_rfl
private def c2GroupHessian158_12Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -240),([0,8], -80),([2,7], -80),([7,7], -80),([7,8], -80)]
def c2GroupHessian158_12 : Poly := List.flatten [c2GroupHessian158_12Chunk0]
theorem c2GroupHessian158_12_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian158_12 := by kernel_rfl
private def c2GroupHessian158_13Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -80),([0,8], -240),([2,8], -80),([7,8], -80),([8,8], -80)]
def c2GroupHessian158_13 : Poly := List.flatten [c2GroupHessian158_13Chunk0]
theorem c2GroupHessian158_13_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian158_13 := by kernel_rfl
private def c2GroupHessian158_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 80),([0,7], 160),([0,9], 40),([3,3], 80),([3,5], 80),([3,9], 40),([5,5], 32),([5,9], 8),([7,7], 80),([9,9], 24)]
def c2GroupHessian158_22 : Poly := List.flatten [c2GroupHessian158_22Chunk0]
theorem c2GroupHessian158_22_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian158_22 := by kernel_rfl
private def c2GroupHessian158_23Chunk0 : Poly := [([0,0], 120),([0,3], 40),([0,4], 80),([0,5], 32),([0,6], 40),([0,7], 80),([0,8], 80),([0,9], -16),([3,4], 80),([3,6], 40),([3,9], -20),([4,5], 40),([4,9], 20),([5,6], 32),([5,9], -4),([6,9], 4),([7,8], 80),([9,9], -24)]
def c2GroupHessian158_23 : Poly := List.flatten [c2GroupHessian158_23Chunk0]
theorem c2GroupHessian158_23_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian158_23 := by kernel_rfl
private def c2GroupHessian158_33Chunk0 : Poly := [([0,0], 112),([0,4], 80),([0,6], 64),([0,8], 160),([0,9], -8),([4,4], 80),([4,6], 80),([4,9], -40),([6,6], 32),([6,9], -8),([8,8], 80),([9,9], 24)]
def c2GroupHessian158_33 : Poly := List.flatten [c2GroupHessian158_33Chunk0]
theorem c2GroupHessian158_33_check : sumFast (c2TensorGroup158.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian158_33 := by kernel_rfl
end D4.Secondary
