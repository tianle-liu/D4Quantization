import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup64_det_check : c3TensorGroup64.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 87)) = true := by kernel_rfl
private def c3GroupHessian64_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], 160),([0,6], -8),([0,9], 80),([1,1], 80),([1,5], 160),([5,5], 80),([6,6], 24),([6,9], -40),([9,9], 80)]
def c3GroupHessian64_00 : Poly := List.flatten [c3GroupHessian64_00Chunk0]
theorem c3GroupHessian64_00_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian64_00 := by kernel_rfl
private def c3GroupHessian64_01Chunk0 : Poly := [([0,0], 72),([0,2], 40),([0,6], -24),([0,7], 40),([0,8], -80),([0,9], 160),([1,8], -80),([2,6], -20),([2,9], 80),([5,8], -80),([6,7], -20),([6,9], -20),([7,9], 80),([9,9], 80)]
def c3GroupHessian64_01 : Poly := List.flatten [c3GroupHessian64_01Chunk0]
theorem c3GroupHessian64_01_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian64_01 := by kernel_rfl
private def c3GroupHessian64_02Chunk0 : Poly := [([0,0], -120),([0,1], -80),([0,3], -4),([0,5], -160),([0,6], 20),([0,7], -40),([0,9], -120),([1,5], -80),([3,6], 8),([3,9], -20),([5,5], -80),([6,7], 20),([6,9], 20),([7,9], -80),([9,9], -80)]
def c3GroupHessian64_02 : Poly := List.flatten [c3GroupHessian64_02Chunk0]
theorem c3GroupHessian64_02_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian64_02 := by kernel_rfl
private def c3GroupHessian64_03Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,4], 80),([0,5], 80),([0,6], 8),([0,8], 80),([0,9], -80),([1,4], 80),([1,8], 80),([4,5], 80),([5,8], 80),([6,6], -24),([6,9], 40),([9,9], -80)]
def c3GroupHessian64_03 : Poly := List.flatten [c3GroupHessian64_03Chunk0]
theorem c3GroupHessian64_03_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian64_03 := by kernel_rfl
private def c3GroupHessian64_11Chunk0 : Poly := [([0,0], 192),([0,2], 240),([0,7], 240),([0,9], 240),([2,2], 80),([2,7], 160),([2,9], 160),([7,7], 80),([7,9], 160),([8,8], 80),([9,9], 80)]
def c3GroupHessian64_11 : Poly := List.flatten [c3GroupHessian64_11Chunk0]
theorem c3GroupHessian64_11_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian64_11 := by kernel_rfl
private def c3GroupHessian64_12Chunk0 : Poly := [([0,0], -120),([0,2], -80),([0,3], -24),([0,7], -200),([0,8], 80),([0,9], -200),([2,3], -20),([2,7], -80),([2,9], -80),([3,7], -20),([3,9], -20),([5,8], 80),([7,7], -80),([7,9], -160),([9,9], -80)]
def c3GroupHessian64_12 : Poly := List.flatten [c3GroupHessian64_12Chunk0]
theorem c3GroupHessian64_12_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian64_12 := by kernel_rfl
private def c3GroupHessian64_13Chunk0 : Poly := [([0,0], -72),([0,2], -40),([0,6], 24),([0,7], -40),([0,8], -80),([0,9], -160),([2,6], 20),([2,9], -80),([4,8], -80),([6,7], 20),([6,9], 20),([7,9], -80),([8,8], -80),([9,9], -80)]
def c3GroupHessian64_13 : Poly := List.flatten [c3GroupHessian64_13Chunk0]
theorem c3GroupHessian64_13_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian64_13 := by kernel_rfl
private def c3GroupHessian64_22Chunk0 : Poly := [([0,0], 160),([0,3], 40),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 24),([3,7], 40),([3,9], 40),([5,5], 80),([7,7], 80),([7,9], 160),([9,9], 80)]
def c3GroupHessian64_22 : Poly := List.flatten [c3GroupHessian64_22Chunk0]
theorem c3GroupHessian64_22_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian64_22 := by kernel_rfl
private def c3GroupHessian64_23Chunk0 : Poly := [([0,0], -40),([0,3], 4),([0,4], -80),([0,5], -80),([0,6], -20),([0,7], 40),([0,8], -80),([0,9], 120),([3,6], -8),([3,9], 20),([4,5], -80),([5,8], -80),([6,7], -20),([6,9], -20),([7,9], 80),([9,9], 80)]
def c3GroupHessian64_23 : Poly := List.flatten [c3GroupHessian64_23Chunk0]
theorem c3GroupHessian64_23_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian64_23 := by kernel_rfl
private def c3GroupHessian64_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], -8),([0,8], 160),([0,9], 80),([4,4], 80),([4,8], 160),([6,6], 24),([6,9], -40),([8,8], 80),([9,9], 80)]
def c3GroupHessian64_33 : Poly := List.flatten [c3GroupHessian64_33Chunk0]
theorem c3GroupHessian64_33_check : sumFast (c3TensorGroup64.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian64_33 := by kernel_rfl
end D4.Secondary
