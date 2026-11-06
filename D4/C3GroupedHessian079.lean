import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup79_det_check : c3TensorGroup79.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 107)) = true := by kernel_rfl
private def c3GroupHessian79_00Chunk0 : Poly := [([0,0], 320),([0,1], 320),([0,5], 320),([0,6], 320),([0,9], 320),([1,1], 80),([1,5], 160),([1,6], 160),([1,9], 160),([5,5], 80),([5,6], 160),([5,9], 160),([6,6], 80),([6,9], 160),([9,9], 80)]
def c3GroupHessian79_00 : Poly := List.flatten [c3GroupHessian79_00Chunk0]
theorem c3GroupHessian79_00_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian79_00 := by kernel_rfl
private def c3GroupHessian79_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,5], 80),([0,6], 80),([0,9], 240),([1,9], 80),([5,9], 80),([6,9], 80),([9,9], 80)]
def c3GroupHessian79_01 : Poly := List.flatten [c3GroupHessian79_01Chunk0]
theorem c3GroupHessian79_01_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian79_01 := by kernel_rfl
private def c3GroupHessian79_02Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -240),([0,6], -80),([0,9], -240),([1,5], -80),([1,9], -80),([5,5], -80),([5,6], -80),([5,9], -160),([6,9], -80),([9,9], -80)]
def c3GroupHessian79_02 : Poly := List.flatten [c3GroupHessian79_02Chunk0]
theorem c3GroupHessian79_02_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian79_02 := by kernel_rfl
private def c3GroupHessian79_03Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -80),([0,6], -240),([0,9], -240),([1,6], -80),([1,9], -80),([5,6], -80),([5,9], -80),([6,6], -80),([6,9], -160),([9,9], -80)]
def c3GroupHessian79_03 : Poly := List.flatten [c3GroupHessian79_03Chunk0]
theorem c3GroupHessian79_03_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian79_03 := by kernel_rfl
private def c3GroupHessian79_11Chunk0 : Poly := [([0,0], 112),([0,2], 64),([0,7], -8),([0,8], 80),([0,9], 160),([2,2], 32),([2,7], -8),([2,8], 80),([7,7], 24),([7,8], -40),([8,8], 80),([9,9], 80)]
def c3GroupHessian79_11 : Poly := List.flatten [c3GroupHessian79_11Chunk0]
theorem c3GroupHessian79_11_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian79_11 := by kernel_rfl
private def c3GroupHessian79_12Chunk0 : Poly := [([0,0], -40),([0,2], 40),([0,3], 40),([0,5], -80),([0,7], -16),([0,8], 80),([0,9], -160),([2,3], 40),([2,7], 4),([3,7], -20),([3,8], 80),([5,9], -80),([7,7], -24),([7,8], 20),([9,9], -80)]
def c3GroupHessian79_12 : Poly := List.flatten [c3GroupHessian79_12Chunk0]
theorem c3GroupHessian79_12_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian79_12 := by kernel_rfl
private def c3GroupHessian79_13Chunk0 : Poly := [([0,0], -120),([0,2], -40),([0,4], -4),([0,6], -80),([0,7], 20),([0,8], -120),([0,9], -160),([2,4], -4),([2,8], -40),([4,7], 8),([4,8], -20),([6,9], -80),([7,8], 20),([8,8], -80),([9,9], -80)]
def c3GroupHessian79_13 : Poly := List.flatten [c3GroupHessian79_13Chunk0]
theorem c3GroupHessian79_13_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian79_13 := by kernel_rfl
private def c3GroupHessian79_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 40),([0,9], 160),([3,3], 80),([3,7], 40),([5,5], 80),([5,9], 160),([7,7], 24),([9,9], 80)]
def c3GroupHessian79_22 : Poly := List.flatten [c3GroupHessian79_22Chunk0]
theorem c3GroupHessian79_22_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian79_22 := by kernel_rfl
private def c3GroupHessian79_23Chunk0 : Poly := [([0,3], -80),([0,4], -20),([0,5], 80),([0,6], 80),([0,7], -20),([0,8], -80),([0,9], 160),([3,4], -20),([3,8], -80),([4,7], -8),([5,6], 80),([5,9], 80),([6,9], 80),([7,8], -20),([9,9], 80)]
def c3GroupHessian79_23 : Poly := List.flatten [c3GroupHessian79_23Chunk0]
theorem c3GroupHessian79_23_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian79_23 := by kernel_rfl
private def c3GroupHessian79_33Chunk0 : Poly := [([0,0], 160),([0,4], 40),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 24),([4,8], 40),([6,6], 80),([6,9], 160),([8,8], 80),([9,9], 80)]
def c3GroupHessian79_33 : Poly := List.flatten [c3GroupHessian79_33Chunk0]
theorem c3GroupHessian79_33_check : sumFast (c3TensorGroup79.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian79_33 := by kernel_rfl
end D4.Secondary
