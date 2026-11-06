import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup69_det_check : c3TensorGroup69.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 92)) = true := by kernel_rfl
private def c3GroupHessian69_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], 160),([0,6], 64),([0,9], -8),([1,1], 80),([1,5], 160),([5,5], 80),([6,6], 32),([6,9], -8),([9,9], 24)]
def c3GroupHessian69_00 : Poly := List.flatten [c3GroupHessian69_00Chunk0]
theorem c3GroupHessian69_00_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian69_00 := by kernel_rfl
private def c3GroupHessian69_01Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,6], -8),([0,7], -40),([0,8], -80),([0,9], 12),([1,8], -80),([2,6], -4),([2,9], 8),([5,8], -80),([6,7], -40),([6,9], -4),([7,9], 20),([9,9], 24)]
def c3GroupHessian69_01 : Poly := List.flatten [c3GroupHessian69_01Chunk0]
theorem c3GroupHessian69_01_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian69_01 := by kernel_rfl
private def c3GroupHessian69_02Chunk0 : Poly := [([0,0], -40),([0,1], -80),([0,3], 32),([0,5], -160),([0,6], 40),([0,7], 40),([0,9], -16),([1,5], -80),([3,6], 32),([3,9], -4),([5,5], -80),([6,7], 40),([6,9], 4),([7,9], -20),([9,9], -24)]
def c3GroupHessian69_02 : Poly := List.flatten [c3GroupHessian69_02Chunk0]
theorem c3GroupHessian69_02_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian69_02 := by kernel_rfl
private def c3GroupHessian69_03Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,4], 80),([0,5], 80),([0,6], -64),([0,8], 80),([0,9], 8),([1,4], 80),([1,8], 80),([4,5], 80),([5,8], 80),([6,6], -32),([6,9], 8),([9,9], -24)]
def c3GroupHessian69_03 : Poly := List.flatten [c3GroupHessian69_03Chunk0]
theorem c3GroupHessian69_03_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian69_03 := by kernel_rfl
private def c3GroupHessian69_11Chunk0 : Poly := [([0,0], 32),([0,2], 32),([0,7], 80),([0,9], 32),([2,2], 24),([2,7], 40),([2,9], 16),([7,7], 80),([7,9], 40),([8,8], 80),([9,9], 24)]
def c3GroupHessian69_11 : Poly := List.flatten [c3GroupHessian69_11Chunk0]
theorem c3GroupHessian69_11_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian69_11 := by kernel_rfl
private def c3GroupHessian69_12Chunk0 : Poly := [([0,0], -40),([0,2], -20),([0,3], -8),([0,7], -120),([0,8], 80),([0,9], -36),([2,3], -4),([2,7], -20),([2,9], -8),([3,7], -40),([3,9], -4),([5,8], 80),([7,7], -80),([7,9], -40),([9,9], -24)]
def c3GroupHessian69_12 : Poly := List.flatten [c3GroupHessian69_12Chunk0]
theorem c3GroupHessian69_12_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian69_12 := by kernel_rfl
private def c3GroupHessian69_13Chunk0 : Poly := [([0,0], 8),([0,2], 4),([0,6], 8),([0,7], 40),([0,8], -80),([0,9], -12),([2,6], 4),([2,9], -8),([4,8], -80),([6,7], 40),([6,9], 4),([7,9], -20),([8,8], -80),([9,9], -24)]
def c3GroupHessian69_13 : Poly := List.flatten [c3GroupHessian69_13Chunk0]
theorem c3GroupHessian69_13_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian69_13 := by kernel_rfl
private def c3GroupHessian69_22Chunk0 : Poly := [([0,0], 160),([0,3], 80),([0,5], 160),([0,7], 160),([0,9], 40),([3,3], 32),([3,7], 80),([3,9], 8),([5,5], 80),([7,7], 80),([7,9], 40),([9,9], 24)]
def c3GroupHessian69_22 : Poly := List.flatten [c3GroupHessian69_22Chunk0]
theorem c3GroupHessian69_22_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian69_22 := by kernel_rfl
private def c3GroupHessian69_23Chunk0 : Poly := [([0,0], -120),([0,3], -32),([0,4], -80),([0,5], -80),([0,6], -40),([0,7], -40),([0,8], -80),([0,9], 16),([3,6], -32),([3,9], 4),([4,5], -80),([5,8], -80),([6,7], -40),([6,9], -4),([7,9], 20),([9,9], 24)]
def c3GroupHessian69_23 : Poly := List.flatten [c3GroupHessian69_23Chunk0]
theorem c3GroupHessian69_23_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian69_23 := by kernel_rfl
private def c3GroupHessian69_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], 64),([0,8], 160),([0,9], -8),([4,4], 80),([4,8], 160),([6,6], 32),([6,9], -8),([8,8], 80),([9,9], 24)]
def c3GroupHessian69_33 : Poly := List.flatten [c3GroupHessian69_33Chunk0]
theorem c3GroupHessian69_33_check : sumFast (c3TensorGroup69.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian69_33 := by kernel_rfl
end D4.Secondary
