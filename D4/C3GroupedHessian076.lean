import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup76_det_check : c3TensorGroup76.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 103)) = true := by kernel_rfl
private def c3GroupHessian76_00Chunk0 : Poly := [([0,0], 320),([0,1], 320),([0,5], 320),([0,6], 320),([0,9], 320),([1,1], 80),([1,5], 160),([1,6], 160),([1,9], 160),([5,5], 80),([5,6], 160),([5,9], 160),([6,6], 80),([6,9], 160),([9,9], 80)]
def c3GroupHessian76_00 : Poly := List.flatten [c3GroupHessian76_00Chunk0]
theorem c3GroupHessian76_00_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian76_00 := by kernel_rfl
private def c3GroupHessian76_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,5], 80),([0,6], 80),([0,9], 240),([1,9], 80),([5,9], 80),([6,9], 80),([9,9], 80)]
def c3GroupHessian76_01 : Poly := List.flatten [c3GroupHessian76_01Chunk0]
theorem c3GroupHessian76_01_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian76_01 := by kernel_rfl
private def c3GroupHessian76_02Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -240),([0,6], -80),([0,9], -240),([1,5], -80),([1,9], -80),([5,5], -80),([5,6], -80),([5,9], -160),([6,9], -80),([9,9], -80)]
def c3GroupHessian76_02 : Poly := List.flatten [c3GroupHessian76_02Chunk0]
theorem c3GroupHessian76_02_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian76_02 := by kernel_rfl
private def c3GroupHessian76_03Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -80),([0,6], -240),([0,9], -240),([1,6], -80),([1,9], -80),([5,6], -80),([5,9], -80),([6,6], -80),([6,9], -160),([9,9], -80)]
def c3GroupHessian76_03 : Poly := List.flatten [c3GroupHessian76_03Chunk0]
theorem c3GroupHessian76_03_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian76_03 := by kernel_rfl
private def c3GroupHessian76_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 40),([0,9], 160),([2,2], 80),([2,7], 160),([2,8], 40),([7,7], 80),([7,8], 40),([8,8], 24),([9,9], 80)]
def c3GroupHessian76_11 : Poly := List.flatten [c3GroupHessian76_11Chunk0]
theorem c3GroupHessian76_11_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian76_11 := by kernel_rfl
private def c3GroupHessian76_12Chunk0 : Poly := [([0,0], -120),([0,2], -40),([0,3], 20),([0,5], -80),([0,7], -120),([0,8], -4),([0,9], -160),([2,3], 20),([2,7], -80),([3,7], 20),([3,8], 8),([5,9], -80),([7,7], -80),([7,8], -20),([9,9], -80)]
def c3GroupHessian76_12 : Poly := List.flatten [c3GroupHessian76_12Chunk0]
theorem c3GroupHessian76_12_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian76_12 := by kernel_rfl
private def c3GroupHessian76_13Chunk0 : Poly := [([0,0], -40),([0,2], 40),([0,4], 80),([0,6], -80),([0,7], 40),([0,8], -16),([0,9], -160),([2,4], 80),([2,8], -20),([4,7], 80),([4,8], 20),([6,9], -80),([7,8], -20),([8,8], -24),([9,9], -80)]
def c3GroupHessian76_13 : Poly := List.flatten [c3GroupHessian76_13Chunk0]
theorem c3GroupHessian76_13_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian76_13 := by kernel_rfl
private def c3GroupHessian76_22Chunk0 : Poly := [([0,0], 112),([0,3], -8),([0,5], 160),([0,7], 80),([0,9], 160),([3,3], 24),([3,7], -40),([5,5], 80),([5,9], 160),([7,7], 80),([9,9], 80)]
def c3GroupHessian76_22 : Poly := List.flatten [c3GroupHessian76_22Chunk0]
theorem c3GroupHessian76_22_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian76_22 := by kernel_rfl
private def c3GroupHessian76_23Chunk0 : Poly := [([0,0], 48),([0,3], 4),([0,4], -40),([0,5], 80),([0,6], 80),([0,7], -40),([0,8], 4),([0,9], 160),([3,4], 20),([3,8], -8),([4,7], -80),([5,6], 80),([5,9], 80),([6,9], 80),([7,8], 20),([9,9], 80)]
def c3GroupHessian76_23 : Poly := List.flatten [c3GroupHessian76_23Chunk0]
theorem c3GroupHessian76_23_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian76_23 := by kernel_rfl
private def c3GroupHessian76_33Chunk0 : Poly := [([0,0], 112),([0,4], 80),([0,6], 160),([0,8], -8),([0,9], 160),([4,4], 80),([4,8], -40),([6,6], 80),([6,9], 160),([8,8], 24),([9,9], 80)]
def c3GroupHessian76_33 : Poly := List.flatten [c3GroupHessian76_33Chunk0]
theorem c3GroupHessian76_33_check : sumFast (c3TensorGroup76.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian76_33 := by kernel_rfl
end D4.Secondary
