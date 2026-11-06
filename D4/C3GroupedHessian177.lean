import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup177_det_check : c3TensorGroup177.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 226)) = true := by kernel_rfl
private def c3GroupHessian177_00Chunk0 : Poly := [([0,0], 112),([0,1], 64),([0,5], 64),([0,6], -8),([0,9], 160),([1,1], 32),([1,5], 64),([1,6], -8),([5,5], 32),([5,6], -8),([6,6], 24),([9,9], 80)]
def c3GroupHessian177_00 : Poly := List.flatten [c3GroupHessian177_00Chunk0]
theorem c3GroupHessian177_00_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian177_00 := by kernel_rfl
private def c3GroupHessian177_01Chunk0 : Poly := [([0,0], 160),([0,2], 80),([0,7], 80),([0,8], 80),([0,9], 240),([2,9], 80),([7,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian177_01 : Poly := List.flatten [c3GroupHessian177_01Chunk0]
theorem c3GroupHessian177_01_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian177_01 := by kernel_rfl
private def c3GroupHessian177_02Chunk0 : Poly := [([0,0], -120),([0,1], -40),([0,3], -4),([0,5], -72),([0,6], 20),([0,7], -80),([0,9], -160),([1,3], -4),([1,5], -32),([3,5], -4),([3,6], 8),([5,5], -32),([5,6], 4),([7,9], -80),([9,9], -80)]
def c3GroupHessian177_02 : Poly := List.flatten [c3GroupHessian177_02Chunk0]
theorem c3GroupHessian177_02_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian177_02 := by kernel_rfl
private def c3GroupHessian177_03Chunk0 : Poly := [([0,0], -40),([0,1], 40),([0,4], 32),([0,5], 40),([0,6], -16),([0,8], -80),([0,9], -160),([1,4], 32),([1,6], 4),([4,5], 32),([4,6], -4),([5,6], 4),([6,6], -24),([8,9], -80),([9,9], -80)]
def c3GroupHessian177_03 : Poly := List.flatten [c3GroupHessian177_03Chunk0]
theorem c3GroupHessian177_03_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian177_03 := by kernel_rfl
private def c3GroupHessian177_11Chunk0 : Poly := [([0,0], 320),([0,2], 320),([0,7], 320),([0,8], 320),([0,9], 320),([2,2], 80),([2,7], 160),([2,8], 160),([2,9], 160),([7,7], 80),([7,8], 160),([7,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian177_11 : Poly := List.flatten [c3GroupHessian177_11Chunk0]
theorem c3GroupHessian177_11_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian177_11 := by kernel_rfl
private def c3GroupHessian177_12Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -240),([0,8], -80),([0,9], -240),([2,7], -80),([2,9], -80),([7,7], -80),([7,8], -80),([7,9], -160),([8,9], -80),([9,9], -80)]
def c3GroupHessian177_12 : Poly := List.flatten [c3GroupHessian177_12Chunk0]
theorem c3GroupHessian177_12_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian177_12 := by kernel_rfl
private def c3GroupHessian177_13Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -80),([0,8], -240),([0,9], -240),([2,8], -80),([2,9], -80),([7,8], -80),([7,9], -80),([8,8], -80),([8,9], -160),([9,9], -80)]
def c3GroupHessian177_13 : Poly := List.flatten [c3GroupHessian177_13Chunk0]
theorem c3GroupHessian177_13_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian177_13 := by kernel_rfl
private def c3GroupHessian177_22Chunk0 : Poly := [([0,0], 160),([0,3], 40),([0,5], 80),([0,7], 160),([0,9], 160),([3,3], 24),([3,5], 8),([5,5], 32),([7,7], 80),([7,9], 160),([9,9], 80)]
def c3GroupHessian177_22 : Poly := List.flatten [c3GroupHessian177_22Chunk0]
theorem c3GroupHessian177_22_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian177_22 := by kernel_rfl
private def c3GroupHessian177_23Chunk0 : Poly := [([0,3], -20),([0,4], -40),([0,5], -40),([0,6], -20),([0,7], 80),([0,8], 80),([0,9], 160),([3,4], -4),([3,6], -8),([4,5], -32),([5,6], -4),([7,8], 80),([7,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian177_23 : Poly := List.flatten [c3GroupHessian177_23Chunk0]
theorem c3GroupHessian177_23_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian177_23 := by kernel_rfl
private def c3GroupHessian177_33Chunk0 : Poly := [([0,0], 160),([0,4], 80),([0,6], 40),([0,8], 160),([0,9], 160),([4,4], 32),([4,6], 8),([6,6], 24),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian177_33 : Poly := List.flatten [c3GroupHessian177_33Chunk0]
theorem c3GroupHessian177_33_check : sumFast (c3TensorGroup177.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian177_33 := by kernel_rfl
end D4.Secondary
