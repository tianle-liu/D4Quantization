import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup48_det_check : c3TensorGroup48.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 66)) = true := by kernel_rfl
private def c3GroupHessian48_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], 64),([0,6], 160),([0,9], -8),([1,1], 80),([1,6], 160),([5,5], 32),([5,9], -8),([6,6], 80),([9,9], 24)]
def c3GroupHessian48_00 : Poly := List.flatten [c3GroupHessian48_00Chunk0]
theorem c3GroupHessian48_00_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian48_00 := by kernel_rfl
private def c3GroupHessian48_01Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,5], -8),([0,7], -80),([0,8], -40),([0,9], 12),([1,7], -80),([2,5], -4),([2,9], 8),([5,8], -40),([5,9], -4),([6,7], -80),([8,9], 20),([9,9], 24)]
def c3GroupHessian48_01 : Poly := List.flatten [c3GroupHessian48_01Chunk0]
theorem c3GroupHessian48_01_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian48_01 := by kernel_rfl
private def c3GroupHessian48_02Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,3], 80),([0,5], -64),([0,6], 80),([0,7], 80),([0,9], 8),([1,3], 80),([1,7], 80),([3,6], 80),([5,5], -32),([5,9], 8),([6,7], 80),([9,9], -24)]
def c3GroupHessian48_02 : Poly := List.flatten [c3GroupHessian48_02Chunk0]
theorem c3GroupHessian48_02_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian48_02 := by kernel_rfl
private def c3GroupHessian48_03Chunk0 : Poly := [([0,0], -40),([0,1], -80),([0,4], 32),([0,5], 40),([0,6], -160),([0,8], 40),([0,9], -16),([1,6], -80),([4,5], 32),([4,9], -4),([5,8], 40),([5,9], 4),([6,6], -80),([8,9], -20),([9,9], -24)]
def c3GroupHessian48_03 : Poly := List.flatten [c3GroupHessian48_03Chunk0]
theorem c3GroupHessian48_03_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian48_03 := by kernel_rfl
private def c3GroupHessian48_11Chunk0 : Poly := [([0,0], 32),([0,2], 32),([0,8], 80),([0,9], 32),([2,2], 24),([2,8], 40),([2,9], 16),([7,7], 80),([8,8], 80),([8,9], 40),([9,9], 24)]
def c3GroupHessian48_11 : Poly := List.flatten [c3GroupHessian48_11Chunk0]
theorem c3GroupHessian48_11_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian48_11 := by kernel_rfl
private def c3GroupHessian48_12Chunk0 : Poly := [([0,0], 8),([0,2], 4),([0,5], 8),([0,7], -80),([0,8], 40),([0,9], -12),([2,5], 4),([2,9], -8),([3,7], -80),([5,8], 40),([5,9], 4),([7,7], -80),([8,9], -20),([9,9], -24)]
def c3GroupHessian48_12 : Poly := List.flatten [c3GroupHessian48_12Chunk0]
theorem c3GroupHessian48_12_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian48_12 := by kernel_rfl
private def c3GroupHessian48_13Chunk0 : Poly := [([0,0], -40),([0,2], -20),([0,4], -8),([0,7], 80),([0,8], -120),([0,9], -36),([2,4], -4),([2,8], -20),([2,9], -8),([4,8], -40),([4,9], -4),([6,7], 80),([8,8], -80),([8,9], -40),([9,9], -24)]
def c3GroupHessian48_13 : Poly := List.flatten [c3GroupHessian48_13Chunk0]
theorem c3GroupHessian48_13_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian48_13 := by kernel_rfl
private def c3GroupHessian48_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], 64),([0,7], 160),([0,9], -8),([3,3], 80),([3,7], 160),([5,5], 32),([5,9], -8),([7,7], 80),([9,9], 24)]
def c3GroupHessian48_22 : Poly := List.flatten [c3GroupHessian48_22Chunk0]
theorem c3GroupHessian48_22_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian48_22 := by kernel_rfl
private def c3GroupHessian48_23Chunk0 : Poly := [([0,0], -120),([0,3], -80),([0,4], -32),([0,5], -40),([0,6], -80),([0,7], -80),([0,8], -40),([0,9], 16),([3,6], -80),([4,5], -32),([4,9], 4),([5,8], -40),([5,9], -4),([6,7], -80),([8,9], 20),([9,9], 24)]
def c3GroupHessian48_23 : Poly := List.flatten [c3GroupHessian48_23Chunk0]
theorem c3GroupHessian48_23_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian48_23 := by kernel_rfl
private def c3GroupHessian48_33Chunk0 : Poly := [([0,0], 160),([0,4], 80),([0,6], 160),([0,8], 160),([0,9], 40),([4,4], 32),([4,8], 80),([4,9], 8),([6,6], 80),([8,8], 80),([8,9], 40),([9,9], 24)]
def c3GroupHessian48_33 : Poly := List.flatten [c3GroupHessian48_33Chunk0]
theorem c3GroupHessian48_33_check : sumFast (c3TensorGroup48.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian48_33 := by kernel_rfl
end D4.Secondary
