import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup0_det_check : c3TensorGroup0.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 0)) = true := by kernel_rfl
private def c3GroupHessian0_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 40),([0,9], 160),([1,1], 80),([5,5], 80),([5,6], 40),([5,9], 160),([6,6], 24),([6,9], 40),([9,9], 80)]
def c3GroupHessian0_00 : Poly := List.flatten [c3GroupHessian0_00Chunk0]
theorem c3GroupHessian0_00_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian0_00 := by kernel_rfl
private def c3GroupHessian0_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,2], 80),([0,5], 80),([0,6], 20),([0,7], 80),([0,8], 20),([0,9], 160),([1,2], 80),([5,7], 80),([5,8], 20),([5,9], 80),([6,7], 20),([6,8], 8),([6,9], 20),([7,9], 80),([8,9], 20),([9,9], 80)]
def c3GroupHessian0_01 : Poly := List.flatten [c3GroupHessian0_01Chunk0]
theorem c3GroupHessian0_01_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian0_01 := by kernel_rfl
private def c3GroupHessian0_02Chunk0 : Poly := [([0,0], -120),([0,3], 80),([0,5], -200),([0,6], -24),([0,7], -80),([0,9], -200),([1,3], 80),([5,5], -80),([5,6], -20),([5,7], -80),([5,9], -160),([6,7], -20),([6,9], -20),([7,9], -80),([9,9], -80)]
def c3GroupHessian0_02 : Poly := List.flatten [c3GroupHessian0_02Chunk0]
theorem c3GroupHessian0_02_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian0_02 := by kernel_rfl
private def c3GroupHessian0_03Chunk0 : Poly := [([0,0], -40),([0,4], 80),([0,5], -40),([0,6], -36),([0,8], -20),([0,9], -120),([1,4], 80),([5,6], -20),([5,8], -20),([5,9], -80),([6,6], -24),([6,8], -8),([6,9], -40),([8,9], -20),([9,9], -80)]
def c3GroupHessian0_03 : Poly := List.flatten [c3GroupHessian0_03Chunk0]
theorem c3GroupHessian0_03_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian0_03 := by kernel_rfl
private def c3GroupHessian0_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 40),([0,9], 160),([2,2], 80),([7,7], 80),([7,8], 40),([7,9], 160),([8,8], 24),([8,9], 40),([9,9], 80)]
def c3GroupHessian0_11 : Poly := List.flatten [c3GroupHessian0_11Chunk0]
theorem c3GroupHessian0_11_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian0_11 := by kernel_rfl
private def c3GroupHessian0_12Chunk0 : Poly := [([0,0], -120),([0,3], 80),([0,5], -80),([0,7], -200),([0,8], -24),([0,9], -200),([2,3], 80),([5,7], -80),([5,8], -20),([5,9], -80),([7,7], -80),([7,8], -20),([7,9], -160),([8,9], -20),([9,9], -80)]
def c3GroupHessian0_12 : Poly := List.flatten [c3GroupHessian0_12Chunk0]
theorem c3GroupHessian0_12_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian0_12 := by kernel_rfl
private def c3GroupHessian0_13Chunk0 : Poly := [([0,0], -40),([0,4], 80),([0,6], -20),([0,7], -40),([0,8], -36),([0,9], -120),([2,4], 80),([6,7], -20),([6,8], -8),([6,9], -20),([7,8], -20),([7,9], -80),([8,8], -24),([8,9], -40),([9,9], -80)]
def c3GroupHessian0_13 : Poly := List.flatten [c3GroupHessian0_13Chunk0]
theorem c3GroupHessian0_13_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian0_13 := by kernel_rfl
private def c3GroupHessian0_22Chunk0 : Poly := [([0,0], 192),([0,5], 240),([0,7], 240),([0,9], 240),([3,3], 80),([5,5], 80),([5,7], 160),([5,9], 160),([7,7], 80),([7,9], 160),([9,9], 80)]
def c3GroupHessian0_22 : Poly := List.flatten [c3GroupHessian0_22Chunk0]
theorem c3GroupHessian0_22_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian0_22 := by kernel_rfl
private def c3GroupHessian0_23Chunk0 : Poly := [([0,0], 48),([0,5], 40),([0,6], 24),([0,7], 40),([0,8], 24),([0,9], 160),([3,4], 80),([5,6], 20),([5,8], 20),([5,9], 80),([6,7], 20),([6,9], 20),([7,8], 20),([7,9], 80),([8,9], 20),([9,9], 80)]
def c3GroupHessian0_23 : Poly := List.flatten [c3GroupHessian0_23Chunk0]
theorem c3GroupHessian0_23_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian0_23 := by kernel_rfl
private def c3GroupHessian0_33Chunk0 : Poly := [([0,0], 32),([0,6], 32),([0,8], 32),([0,9], 80),([4,4], 80),([6,6], 24),([6,8], 16),([6,9], 40),([8,8], 24),([8,9], 40),([9,9], 80)]
def c3GroupHessian0_33 : Poly := List.flatten [c3GroupHessian0_33Chunk0]
theorem c3GroupHessian0_33_check : sumFast (c3TensorGroup0.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian0_33 := by kernel_rfl
end D4.Secondary
