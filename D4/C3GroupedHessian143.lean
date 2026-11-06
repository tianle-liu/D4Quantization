import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup143_det_check : c3TensorGroup143.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 185)) = true := by kernel_rfl
private def c3GroupHessian143_00Chunk0 : Poly := [([0,0], 32),([0,1], 32),([0,5], -16),([0,9], 32),([1,1], 24),([1,5], -8),([1,9], 16),([5,5], 32),([5,9], -8),([6,6], 80),([9,9], 24)]
def c3GroupHessian143_00 : Poly := List.flatten [c3GroupHessian143_00Chunk0]
theorem c3GroupHessian143_00_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian143_00 := by kernel_rfl
private def c3GroupHessian143_01Chunk0 : Poly := [([0,0], 40),([0,1], 20),([0,5], -40),([0,6], -80),([0,8], 40),([0,9], 36),([1,8], 20),([1,9], 8),([2,6], -80),([5,8], -40),([5,9], -4),([6,7], -80),([8,9], 20),([9,9], 24)]
def c3GroupHessian143_01 : Poly := List.flatten [c3GroupHessian143_01Chunk0]
theorem c3GroupHessian143_01_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian143_01 := by kernel_rfl
private def c3GroupHessian143_02Chunk0 : Poly := [([0,0], 8),([0,1], 4),([0,3], 40),([0,5], -24),([0,6], 80),([0,9], -12),([1,3], 20),([1,5], 4),([1,9], -8),([3,5], -40),([3,9], 20),([5,5], -32),([5,9], 8),([6,7], 80),([9,9], -24)]
def c3GroupHessian143_02 : Poly := List.flatten [c3GroupHessian143_02Chunk0]
theorem c3GroupHessian143_02_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian143_02 := by kernel_rfl
private def c3GroupHessian143_03Chunk0 : Poly := [([0,0], -40),([0,1], -20),([0,5], 40),([0,6], -80),([0,8], -40),([0,9], -36),([1,8], -20),([1,9], -8),([4,6], -80),([5,8], 40),([5,9], 4),([6,6], -80),([8,9], -20),([9,9], -24)]
def c3GroupHessian143_03 : Poly := List.flatten [c3GroupHessian143_03Chunk0]
theorem c3GroupHessian143_03_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian143_03 := by kernel_rfl
private def c3GroupHessian143_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([0,9], 40),([2,2], 80),([2,7], 160),([7,7], 80),([8,8], 80),([8,9], 40),([9,9], 24)]
def c3GroupHessian143_11 : Poly := List.flatten [c3GroupHessian143_11Chunk0]
theorem c3GroupHessian143_11_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian143_11 := by kernel_rfl
private def c3GroupHessian143_12Chunk0 : Poly := [([0,0], -40),([0,2], -80),([0,3], 80),([0,5], 40),([0,7], -160),([0,8], 40),([0,9], -16),([2,7], -80),([3,8], 80),([3,9], 20),([5,8], 40),([5,9], 4),([7,7], -80),([8,9], -20),([9,9], -24)]
def c3GroupHessian143_12 : Poly := List.flatten [c3GroupHessian143_12Chunk0]
theorem c3GroupHessian143_12_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian143_12 := by kernel_rfl
private def c3GroupHessian143_13Chunk0 : Poly := [([0,2], 80),([0,4], 80),([0,6], 80),([0,7], 80),([0,8], -160),([0,9], -40),([2,4], 80),([2,6], 80),([4,7], 80),([6,7], 80),([8,8], -80),([8,9], -40),([9,9], -24)]
def c3GroupHessian143_13 : Poly := List.flatten [c3GroupHessian143_13Chunk0]
theorem c3GroupHessian143_13_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian143_13 := by kernel_rfl
private def c3GroupHessian143_22Chunk0 : Poly := [([0,0], 112),([0,3], 80),([0,5], 64),([0,7], 160),([0,9], -8),([3,3], 80),([3,5], 80),([3,9], -40),([5,5], 32),([5,9], -8),([7,7], 80),([9,9], 24)]
def c3GroupHessian143_22 : Poly := List.flatten [c3GroupHessian143_22Chunk0]
theorem c3GroupHessian143_22_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian143_22 := by kernel_rfl
private def c3GroupHessian143_23Chunk0 : Poly := [([0,0], -120),([0,3], -80),([0,4], -80),([0,5], -40),([0,6], -80),([0,7], -80),([0,8], -40),([0,9], 16),([3,8], -80),([3,9], -20),([4,7], -80),([5,8], -40),([5,9], -4),([6,7], -80),([8,9], 20),([9,9], 24)]
def c3GroupHessian143_23 : Poly := List.flatten [c3GroupHessian143_23Chunk0]
theorem c3GroupHessian143_23_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian143_23 := by kernel_rfl
private def c3GroupHessian143_33Chunk0 : Poly := [([0,0], 160),([0,4], 160),([0,6], 160),([0,8], 160),([0,9], 40),([4,4], 80),([4,6], 160),([6,6], 80),([8,8], 80),([8,9], 40),([9,9], 24)]
def c3GroupHessian143_33 : Poly := List.flatten [c3GroupHessian143_33Chunk0]
theorem c3GroupHessian143_33_check : sumFast (c3TensorGroup143.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian143_33 := by kernel_rfl
end D4.Secondary
