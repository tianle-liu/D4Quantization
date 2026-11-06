import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup122_det_check : c3TensorGroup122.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 159)) = true := by kernel_rfl
private def c3GroupHessian122_00Chunk0 : Poly := [([0,0], 32),([0,1], 32),([0,6], -16),([0,9], 32),([1,1], 24),([1,6], -8),([1,9], 16),([5,5], 80),([6,6], 32),([6,9], -8),([9,9], 24)]
def c3GroupHessian122_00 : Poly := List.flatten [c3GroupHessian122_00Chunk0]
theorem c3GroupHessian122_00_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian122_00 := by kernel_rfl
private def c3GroupHessian122_01Chunk0 : Poly := [([0,0], 40),([0,1], 20),([0,5], -80),([0,6], -40),([0,7], 40),([0,9], 36),([1,7], 20),([1,9], 8),([2,5], -80),([5,8], -80),([6,7], -40),([6,9], -4),([7,9], 20),([9,9], 24)]
def c3GroupHessian122_01 : Poly := List.flatten [c3GroupHessian122_01Chunk0]
theorem c3GroupHessian122_01_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian122_01 := by kernel_rfl
private def c3GroupHessian122_02Chunk0 : Poly := [([0,0], -40),([0,1], -20),([0,5], -80),([0,6], 40),([0,7], -40),([0,9], -36),([1,7], -20),([1,9], -8),([3,5], -80),([5,5], -80),([6,7], 40),([6,9], 4),([7,9], -20),([9,9], -24)]
def c3GroupHessian122_02 : Poly := List.flatten [c3GroupHessian122_02Chunk0]
theorem c3GroupHessian122_02_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian122_02 := by kernel_rfl
private def c3GroupHessian122_03Chunk0 : Poly := [([0,0], 8),([0,1], 4),([0,4], 40),([0,5], 80),([0,6], -24),([0,9], -12),([1,4], 20),([1,6], 4),([1,9], -8),([4,6], -40),([4,9], 20),([5,8], 80),([6,6], -32),([6,9], 8),([9,9], -24)]
def c3GroupHessian122_03 : Poly := List.flatten [c3GroupHessian122_03Chunk0]
theorem c3GroupHessian122_03_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian122_03 := by kernel_rfl
private def c3GroupHessian122_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([0,9], 40),([2,2], 80),([2,8], 160),([7,7], 80),([7,9], 40),([8,8], 80),([9,9], 24)]
def c3GroupHessian122_11 : Poly := List.flatten [c3GroupHessian122_11Chunk0]
theorem c3GroupHessian122_11_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian122_11 := by kernel_rfl
private def c3GroupHessian122_12Chunk0 : Poly := [([0,2], 80),([0,3], 80),([0,5], 80),([0,7], -160),([0,8], 80),([0,9], -40),([2,3], 80),([2,5], 80),([3,8], 80),([5,8], 80),([7,7], -80),([7,9], -40),([9,9], -24)]
def c3GroupHessian122_12 : Poly := List.flatten [c3GroupHessian122_12Chunk0]
theorem c3GroupHessian122_12_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian122_12 := by kernel_rfl
private def c3GroupHessian122_13Chunk0 : Poly := [([0,0], -40),([0,2], -80),([0,4], 80),([0,6], 40),([0,7], 40),([0,8], -160),([0,9], -16),([2,8], -80),([4,7], 80),([4,9], 20),([6,7], 40),([6,9], 4),([7,9], -20),([8,8], -80),([9,9], -24)]
def c3GroupHessian122_13 : Poly := List.flatten [c3GroupHessian122_13Chunk0]
theorem c3GroupHessian122_13_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian122_13 := by kernel_rfl
private def c3GroupHessian122_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 40),([3,3], 80),([3,5], 160),([5,5], 80),([7,7], 80),([7,9], 40),([9,9], 24)]
def c3GroupHessian122_22 : Poly := List.flatten [c3GroupHessian122_22Chunk0]
theorem c3GroupHessian122_22_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian122_22 := by kernel_rfl
private def c3GroupHessian122_23Chunk0 : Poly := [([0,0], -120),([0,3], -80),([0,4], -80),([0,5], -80),([0,6], -40),([0,7], -40),([0,8], -80),([0,9], 16),([3,8], -80),([4,7], -80),([4,9], -20),([5,8], -80),([6,7], -40),([6,9], -4),([7,9], 20),([9,9], 24)]
def c3GroupHessian122_23 : Poly := List.flatten [c3GroupHessian122_23Chunk0]
theorem c3GroupHessian122_23_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian122_23 := by kernel_rfl
private def c3GroupHessian122_33Chunk0 : Poly := [([0,0], 112),([0,4], 80),([0,6], 64),([0,8], 160),([0,9], -8),([4,4], 80),([4,6], 80),([4,9], -40),([6,6], 32),([6,9], -8),([8,8], 80),([9,9], 24)]
def c3GroupHessian122_33 : Poly := List.flatten [c3GroupHessian122_33Chunk0]
theorem c3GroupHessian122_33_check : sumFast (c3TensorGroup122.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian122_33 := by kernel_rfl
end D4.Secondary
