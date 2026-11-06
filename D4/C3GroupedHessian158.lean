import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup158_det_check : c3TensorGroup158.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 205)) = true := by kernel_rfl
private def c3GroupHessian158_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 40),([0,9], 160),([1,1], 80),([1,5], 160),([1,6], 40),([5,5], 80),([5,6], 40),([6,6], 24),([9,9], 80)]
def c3GroupHessian158_00 : Poly := List.flatten [c3GroupHessian158_00Chunk0]
theorem c3GroupHessian158_00_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian158_00 := by kernel_rfl
private def c3GroupHessian158_01Chunk0 : Poly := [([0,0], 160),([0,2], 80),([0,7], 80),([0,8], 80),([0,9], 240),([2,9], 80),([7,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian158_01 : Poly := List.flatten [c3GroupHessian158_01Chunk0]
theorem c3GroupHessian158_01_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian158_01 := by kernel_rfl
private def c3GroupHessian158_02Chunk0 : Poly := [([0,0], -120),([0,1], -40),([0,3], 20),([0,5], -120),([0,6], -4),([0,7], -80),([0,9], -160),([1,3], 20),([1,5], -80),([3,5], 20),([3,6], 8),([5,5], -80),([5,6], -20),([7,9], -80),([9,9], -80)]
def c3GroupHessian158_02 : Poly := List.flatten [c3GroupHessian158_02Chunk0]
theorem c3GroupHessian158_02_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian158_02 := by kernel_rfl
private def c3GroupHessian158_03Chunk0 : Poly := [([0,0], -40),([0,1], 40),([0,4], 80),([0,5], 40),([0,6], -16),([0,8], -80),([0,9], -160),([1,4], 80),([1,6], -20),([4,5], 80),([4,6], 20),([5,6], -20),([6,6], -24),([8,9], -80),([9,9], -80)]
def c3GroupHessian158_03 : Poly := List.flatten [c3GroupHessian158_03Chunk0]
theorem c3GroupHessian158_03_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian158_03 := by kernel_rfl
private def c3GroupHessian158_11Chunk0 : Poly := [([0,0], 320),([0,2], 320),([0,7], 320),([0,8], 320),([0,9], 320),([2,2], 80),([2,7], 160),([2,8], 160),([2,9], 160),([7,7], 80),([7,8], 160),([7,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian158_11 : Poly := List.flatten [c3GroupHessian158_11Chunk0]
theorem c3GroupHessian158_11_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian158_11 := by kernel_rfl
private def c3GroupHessian158_12Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -240),([0,8], -80),([0,9], -240),([2,7], -80),([2,9], -80),([7,7], -80),([7,8], -80),([7,9], -160),([8,9], -80),([9,9], -80)]
def c3GroupHessian158_12 : Poly := List.flatten [c3GroupHessian158_12Chunk0]
theorem c3GroupHessian158_12_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian158_12 := by kernel_rfl
private def c3GroupHessian158_13Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -80),([0,8], -240),([0,9], -240),([2,8], -80),([2,9], -80),([7,8], -80),([7,9], -80),([8,8], -80),([8,9], -160),([9,9], -80)]
def c3GroupHessian158_13 : Poly := List.flatten [c3GroupHessian158_13Chunk0]
theorem c3GroupHessian158_13_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian158_13 := by kernel_rfl
private def c3GroupHessian158_22Chunk0 : Poly := [([0,0], 112),([0,3], -8),([0,5], 80),([0,7], 160),([0,9], 160),([3,3], 24),([3,5], -40),([5,5], 80),([7,7], 80),([7,9], 160),([9,9], 80)]
def c3GroupHessian158_22 : Poly := List.flatten [c3GroupHessian158_22Chunk0]
theorem c3GroupHessian158_22_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian158_22 := by kernel_rfl
private def c3GroupHessian158_23Chunk0 : Poly := [([0,0], 48),([0,3], 4),([0,4], -40),([0,5], -40),([0,6], 4),([0,7], 80),([0,8], 80),([0,9], 160),([3,4], 20),([3,6], -8),([4,5], -80),([5,6], 20),([7,8], 80),([7,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian158_23 : Poly := List.flatten [c3GroupHessian158_23Chunk0]
theorem c3GroupHessian158_23_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian158_23 := by kernel_rfl
private def c3GroupHessian158_33Chunk0 : Poly := [([0,0], 112),([0,4], 80),([0,6], -8),([0,8], 160),([0,9], 160),([4,4], 80),([4,6], -40),([6,6], 24),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian158_33 : Poly := List.flatten [c3GroupHessian158_33Chunk0]
theorem c3GroupHessian158_33_check : sumFast (c3TensorGroup158.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian158_33 := by kernel_rfl
end D4.Secondary
