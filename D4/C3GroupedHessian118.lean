import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup118_det_check : c3TensorGroup118.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 155)) = true := by kernel_rfl
private def c3GroupHessian118_00Chunk0 : Poly := [([0,0], 192),([0,1], 240),([0,6], 240),([0,9], 240),([1,1], 80),([1,6], 160),([1,9], 160),([5,5], 80),([6,6], 80),([6,9], 160),([9,9], 80)]
def c3GroupHessian118_00 : Poly := List.flatten [c3GroupHessian118_00Chunk0]
theorem c3GroupHessian118_00_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian118_00 := by kernel_rfl
private def c3GroupHessian118_01Chunk0 : Poly := [([0,0], 72),([0,1], 40),([0,5], -80),([0,6], 40),([0,7], -24),([0,9], 160),([1,7], -20),([1,9], 80),([2,5], -80),([5,8], -80),([6,7], -20),([6,9], 80),([7,9], -20),([9,9], 80)]
def c3GroupHessian118_01 : Poly := List.flatten [c3GroupHessian118_01Chunk0]
theorem c3GroupHessian118_01_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian118_01 := by kernel_rfl
private def c3GroupHessian118_02Chunk0 : Poly := [([0,0], -72),([0,1], -40),([0,5], -80),([0,6], -40),([0,7], 24),([0,9], -160),([1,7], 20),([1,9], -80),([3,5], -80),([5,5], -80),([6,7], 20),([6,9], -80),([7,9], 20),([9,9], -80)]
def c3GroupHessian118_02 : Poly := List.flatten [c3GroupHessian118_02Chunk0]
theorem c3GroupHessian118_02_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian118_02 := by kernel_rfl
private def c3GroupHessian118_03Chunk0 : Poly := [([0,0], -120),([0,1], -80),([0,4], -24),([0,5], 80),([0,6], -200),([0,9], -200),([1,4], -20),([1,6], -80),([1,9], -80),([4,6], -20),([4,9], -20),([5,8], 80),([6,6], -80),([6,9], -160),([9,9], -80)]
def c3GroupHessian118_03 : Poly := List.flatten [c3GroupHessian118_03Chunk0]
theorem c3GroupHessian118_03_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian118_03 := by kernel_rfl
private def c3GroupHessian118_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], -8),([0,8], 160),([0,9], 80),([2,2], 80),([2,8], 160),([7,7], 24),([7,9], -40),([8,8], 80),([9,9], 80)]
def c3GroupHessian118_11 : Poly := List.flatten [c3GroupHessian118_11Chunk0]
theorem c3GroupHessian118_11_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian118_11 := by kernel_rfl
private def c3GroupHessian118_12Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,3], 80),([0,5], 80),([0,7], 8),([0,8], 80),([0,9], -80),([2,3], 80),([2,5], 80),([3,8], 80),([5,8], 80),([7,7], -24),([7,9], 40),([9,9], -80)]
def c3GroupHessian118_12 : Poly := List.flatten [c3GroupHessian118_12Chunk0]
theorem c3GroupHessian118_12_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian118_12 := by kernel_rfl
private def c3GroupHessian118_13Chunk0 : Poly := [([0,0], -120),([0,2], -80),([0,4], -4),([0,6], -40),([0,7], 20),([0,8], -160),([0,9], -120),([2,8], -80),([4,7], 8),([4,9], -20),([6,7], 20),([6,9], -80),([7,9], 20),([8,8], -80),([9,9], -80)]
def c3GroupHessian118_13 : Poly := List.flatten [c3GroupHessian118_13Chunk0]
theorem c3GroupHessian118_13_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian118_13 := by kernel_rfl
private def c3GroupHessian118_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], 160),([0,7], -8),([0,9], 80),([3,3], 80),([3,5], 160),([5,5], 80),([7,7], 24),([7,9], -40),([9,9], 80)]
def c3GroupHessian118_22 : Poly := List.flatten [c3GroupHessian118_22Chunk0]
theorem c3GroupHessian118_22_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian118_22 := by kernel_rfl
private def c3GroupHessian118_23Chunk0 : Poly := [([0,0], -40),([0,3], -80),([0,4], 4),([0,5], -80),([0,6], 40),([0,7], -20),([0,8], -80),([0,9], 120),([3,8], -80),([4,7], -8),([4,9], 20),([5,8], -80),([6,7], -20),([6,9], 80),([7,9], -20),([9,9], 80)]
def c3GroupHessian118_23 : Poly := List.flatten [c3GroupHessian118_23Chunk0]
theorem c3GroupHessian118_23_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian118_23 := by kernel_rfl
private def c3GroupHessian118_33Chunk0 : Poly := [([0,0], 160),([0,4], 40),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 24),([4,6], 40),([4,9], 40),([6,6], 80),([6,9], 160),([8,8], 80),([9,9], 80)]
def c3GroupHessian118_33 : Poly := List.flatten [c3GroupHessian118_33Chunk0]
theorem c3GroupHessian118_33_check : sumFast (c3TensorGroup118.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian118_33 := by kernel_rfl
end D4.Secondary
