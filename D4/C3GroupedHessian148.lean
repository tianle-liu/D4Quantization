import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup148_det_check : c3TensorGroup148.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 191)) = true := by kernel_rfl
private def c3GroupHessian148_00Chunk0 : Poly := [([0,0], 32),([0,1], 32),([0,5], 80),([0,9], 32),([1,1], 24),([1,5], 40),([1,9], 16),([5,5], 80),([5,9], 40),([6,6], 80),([9,9], 24)]
def c3GroupHessian148_00 : Poly := List.flatten [c3GroupHessian148_00Chunk0]
theorem c3GroupHessian148_00_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian148_00 := by kernel_rfl
private def c3GroupHessian148_01Chunk0 : Poly := [([0,0], -8),([0,1], -4),([0,5], -40),([0,6], -80),([0,8], -8),([0,9], 12),([1,8], -4),([1,9], 8),([2,6], -80),([5,8], -40),([5,9], 20),([6,7], -80),([8,9], -4),([9,9], 24)]
def c3GroupHessian148_01 : Poly := List.flatten [c3GroupHessian148_01Chunk0]
theorem c3GroupHessian148_01_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian148_01 := by kernel_rfl
private def c3GroupHessian148_02Chunk0 : Poly := [([0,0], -40),([0,1], -20),([0,3], -8),([0,5], -120),([0,6], 80),([0,9], -36),([1,3], -4),([1,5], -20),([1,9], -8),([3,5], -40),([3,9], -4),([5,5], -80),([5,9], -40),([6,7], 80),([9,9], -24)]
def c3GroupHessian148_02 : Poly := List.flatten [c3GroupHessian148_02Chunk0]
theorem c3GroupHessian148_02_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian148_02 := by kernel_rfl
private def c3GroupHessian148_03Chunk0 : Poly := [([0,0], 8),([0,1], 4),([0,5], 40),([0,6], -80),([0,8], 8),([0,9], -12),([1,8], 4),([1,9], -8),([4,6], -80),([5,8], 40),([5,9], -20),([6,6], -80),([8,9], 4),([9,9], -24)]
def c3GroupHessian148_03 : Poly := List.flatten [c3GroupHessian148_03Chunk0]
theorem c3GroupHessian148_03_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian148_03 := by kernel_rfl
private def c3GroupHessian148_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], 160),([0,8], 64),([0,9], -8),([2,2], 80),([2,7], 160),([7,7], 80),([8,8], 32),([8,9], -8),([9,9], 24)]
def c3GroupHessian148_11 : Poly := List.flatten [c3GroupHessian148_11Chunk0]
theorem c3GroupHessian148_11_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian148_11 := by kernel_rfl
private def c3GroupHessian148_12Chunk0 : Poly := [([0,0], -40),([0,2], -80),([0,3], 32),([0,5], 40),([0,7], -160),([0,8], 40),([0,9], -16),([2,7], -80),([3,8], 32),([3,9], -4),([5,8], 40),([5,9], -20),([7,7], -80),([8,9], 4),([9,9], -24)]
def c3GroupHessian148_12 : Poly := List.flatten [c3GroupHessian148_12Chunk0]
theorem c3GroupHessian148_12_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian148_12 := by kernel_rfl
private def c3GroupHessian148_13Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,4], 80),([0,6], 80),([0,7], 80),([0,8], -64),([0,9], 8),([2,4], 80),([2,6], 80),([4,7], 80),([6,7], 80),([8,8], -32),([8,9], 8),([9,9], -24)]
def c3GroupHessian148_13 : Poly := List.flatten [c3GroupHessian148_13Chunk0]
theorem c3GroupHessian148_13_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian148_13 := by kernel_rfl
private def c3GroupHessian148_22Chunk0 : Poly := [([0,0], 160),([0,3], 80),([0,5], 160),([0,7], 160),([0,9], 40),([3,3], 32),([3,5], 80),([3,9], 8),([5,5], 80),([5,9], 40),([7,7], 80),([9,9], 24)]
def c3GroupHessian148_22 : Poly := List.flatten [c3GroupHessian148_22Chunk0]
theorem c3GroupHessian148_22_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian148_22 := by kernel_rfl
private def c3GroupHessian148_23Chunk0 : Poly := [([0,0], -120),([0,3], -32),([0,4], -80),([0,5], -40),([0,6], -80),([0,7], -80),([0,8], -40),([0,9], 16),([3,8], -32),([3,9], 4),([4,7], -80),([5,8], -40),([5,9], 20),([6,7], -80),([8,9], -4),([9,9], 24)]
def c3GroupHessian148_23 : Poly := List.flatten [c3GroupHessian148_23Chunk0]
theorem c3GroupHessian148_23_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian148_23 := by kernel_rfl
private def c3GroupHessian148_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], 160),([0,8], 64),([0,9], -8),([4,4], 80),([4,6], 160),([6,6], 80),([8,8], 32),([8,9], -8),([9,9], 24)]
def c3GroupHessian148_33 : Poly := List.flatten [c3GroupHessian148_33Chunk0]
theorem c3GroupHessian148_33_check : sumFast (c3TensorGroup148.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian148_33 := by kernel_rfl
end D4.Secondary
