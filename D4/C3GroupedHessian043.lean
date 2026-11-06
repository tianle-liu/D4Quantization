import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup43_det_check : c3TensorGroup43.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 61)) = true := by kernel_rfl
private def c3GroupHessian43_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], -8),([0,6], 160),([0,9], 80),([1,1], 80),([1,6], 160),([5,5], 24),([5,9], -40),([6,6], 80),([9,9], 80)]
def c3GroupHessian43_00 : Poly := List.flatten [c3GroupHessian43_00Chunk0]
theorem c3GroupHessian43_00_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian43_00 := by kernel_rfl
private def c3GroupHessian43_01Chunk0 : Poly := [([0,0], 72),([0,2], 40),([0,5], -24),([0,7], -80),([0,8], 40),([0,9], 160),([1,7], -80),([2,5], -20),([2,9], 80),([5,8], -20),([5,9], -20),([6,7], -80),([8,9], 80),([9,9], 80)]
def c3GroupHessian43_01 : Poly := List.flatten [c3GroupHessian43_01Chunk0]
theorem c3GroupHessian43_01_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian43_01 := by kernel_rfl
private def c3GroupHessian43_02Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,3], 80),([0,5], 8),([0,6], 80),([0,7], 80),([0,9], -80),([1,3], 80),([1,7], 80),([3,6], 80),([5,5], -24),([5,9], 40),([6,7], 80),([9,9], -80)]
def c3GroupHessian43_02 : Poly := List.flatten [c3GroupHessian43_02Chunk0]
theorem c3GroupHessian43_02_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian43_02 := by kernel_rfl
private def c3GroupHessian43_03Chunk0 : Poly := [([0,0], -120),([0,1], -80),([0,4], -4),([0,5], 20),([0,6], -160),([0,8], -40),([0,9], -120),([1,6], -80),([4,5], 8),([4,9], -20),([5,8], 20),([5,9], 20),([6,6], -80),([8,9], -80),([9,9], -80)]
def c3GroupHessian43_03 : Poly := List.flatten [c3GroupHessian43_03Chunk0]
theorem c3GroupHessian43_03_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian43_03 := by kernel_rfl
private def c3GroupHessian43_11Chunk0 : Poly := [([0,0], 192),([0,2], 240),([0,8], 240),([0,9], 240),([2,2], 80),([2,8], 160),([2,9], 160),([7,7], 80),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian43_11 : Poly := List.flatten [c3GroupHessian43_11Chunk0]
theorem c3GroupHessian43_11_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian43_11 := by kernel_rfl
private def c3GroupHessian43_12Chunk0 : Poly := [([0,0], -72),([0,2], -40),([0,5], 24),([0,7], -80),([0,8], -40),([0,9], -160),([2,5], 20),([2,9], -80),([3,7], -80),([5,8], 20),([5,9], 20),([7,7], -80),([8,9], -80),([9,9], -80)]
def c3GroupHessian43_12 : Poly := List.flatten [c3GroupHessian43_12Chunk0]
theorem c3GroupHessian43_12_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian43_12 := by kernel_rfl
private def c3GroupHessian43_13Chunk0 : Poly := [([0,0], -120),([0,2], -80),([0,4], -24),([0,7], 80),([0,8], -200),([0,9], -200),([2,4], -20),([2,8], -80),([2,9], -80),([4,8], -20),([4,9], -20),([6,7], 80),([8,8], -80),([8,9], -160),([9,9], -80)]
def c3GroupHessian43_13 : Poly := List.flatten [c3GroupHessian43_13Chunk0]
theorem c3GroupHessian43_13_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian43_13 := by kernel_rfl
private def c3GroupHessian43_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], -8),([0,7], 160),([0,9], 80),([3,3], 80),([3,7], 160),([5,5], 24),([5,9], -40),([7,7], 80),([9,9], 80)]
def c3GroupHessian43_22 : Poly := List.flatten [c3GroupHessian43_22Chunk0]
theorem c3GroupHessian43_22_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian43_22 := by kernel_rfl
private def c3GroupHessian43_23Chunk0 : Poly := [([0,0], -40),([0,3], -80),([0,4], 4),([0,5], -20),([0,6], -80),([0,7], -80),([0,8], 40),([0,9], 120),([3,6], -80),([4,5], -8),([4,9], 20),([5,8], -20),([5,9], -20),([6,7], -80),([8,9], 80),([9,9], 80)]
def c3GroupHessian43_23 : Poly := List.flatten [c3GroupHessian43_23Chunk0]
theorem c3GroupHessian43_23_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian43_23 := by kernel_rfl
private def c3GroupHessian43_33Chunk0 : Poly := [([0,0], 160),([0,4], 40),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 24),([4,8], 40),([4,9], 40),([6,6], 80),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian43_33 : Poly := List.flatten [c3GroupHessian43_33Chunk0]
theorem c3GroupHessian43_33_check : sumFast (c3TensorGroup43.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian43_33 := by kernel_rfl
end D4.Secondary
