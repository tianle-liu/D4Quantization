import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup210_det_check : c3TensorGroup210.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 273)) = true := by kernel_rfl
private def c3GroupHessian210_00Chunk0 : Poly := [([0,0], 160),([0,1], 40),([0,5], 160),([0,6], 160),([0,9], 160),([1,1], 24),([1,5], 40),([5,5], 80),([6,6], 80),([6,9], 160),([9,9], 80)]
def c3GroupHessian210_00 : Poly := List.flatten [c3GroupHessian210_00Chunk0]
theorem c3GroupHessian210_00_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian210_00 := by kernel_rfl
private def c3GroupHessian210_01Chunk0 : Poly := [([0,0], 160),([0,1], 20),([0,2], 20),([0,5], 80),([0,6], 80),([0,7], 80),([0,8], 80),([0,9], 160),([1,2], 8),([1,7], 20),([2,5], 20),([5,7], 80),([6,8], 80),([6,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian210_01 : Poly := List.flatten [c3GroupHessian210_01Chunk0]
theorem c3GroupHessian210_01_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian210_01 := by kernel_rfl
private def c3GroupHessian210_02Chunk0 : Poly := [([0,0], -120),([0,1], -24),([0,3], -40),([0,5], -200),([0,7], -80),([0,9], -80),([1,3], -4),([1,5], -20),([1,7], -20),([3,5], -40),([5,5], -80),([5,7], -80),([6,9], -80),([9,9], -80)]
def c3GroupHessian210_02 : Poly := List.flatten [c3GroupHessian210_02Chunk0]
theorem c3GroupHessian210_02_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian210_02 := by kernel_rfl
private def c3GroupHessian210_03Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -240),([0,8], -80),([0,9], -240),([4,6], -80),([4,9], -80),([6,6], -80),([6,8], -80),([6,9], -160),([8,9], -80),([9,9], -80)]
def c3GroupHessian210_03 : Poly := List.flatten [c3GroupHessian210_03Chunk0]
theorem c3GroupHessian210_03_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian210_03 := by kernel_rfl
private def c3GroupHessian210_11Chunk0 : Poly := [([0,0], 160),([0,2], 40),([0,7], 160),([0,8], 160),([0,9], 160),([2,2], 24),([2,7], 40),([7,7], 80),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian210_11 : Poly := List.flatten [c3GroupHessian210_11Chunk0]
theorem c3GroupHessian210_11_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian210_11 := by kernel_rfl
private def c3GroupHessian210_12Chunk0 : Poly := [([0,0], -120),([0,2], -24),([0,3], -40),([0,5], -80),([0,7], -200),([0,9], -80),([2,3], -4),([2,5], -20),([2,7], -20),([3,7], -40),([5,7], -80),([7,7], -80),([8,9], -80),([9,9], -80)]
def c3GroupHessian210_12 : Poly := List.flatten [c3GroupHessian210_12Chunk0]
theorem c3GroupHessian210_12_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian210_12 := by kernel_rfl
private def c3GroupHessian210_13Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -80),([0,8], -240),([0,9], -240),([4,8], -80),([4,9], -80),([6,8], -80),([6,9], -80),([8,8], -80),([8,9], -160),([9,9], -80)]
def c3GroupHessian210_13 : Poly := List.flatten [c3GroupHessian210_13Chunk0]
theorem c3GroupHessian210_13_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian210_13 := by kernel_rfl
private def c3GroupHessian210_22Chunk0 : Poly := [([0,0], 192),([0,3], 144),([0,5], 240),([0,7], 240),([3,3], 32),([3,5], 80),([3,7], 80),([5,5], 80),([5,7], 160),([7,7], 80),([9,9], 80)]
def c3GroupHessian210_22 : Poly := List.flatten [c3GroupHessian210_22Chunk0]
theorem c3GroupHessian210_22_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian210_22 := by kernel_rfl
private def c3GroupHessian210_23Chunk0 : Poly := [([0,9], 160),([4,9], 80),([6,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian210_23 : Poly := List.flatten [c3GroupHessian210_23Chunk0]
theorem c3GroupHessian210_23_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian210_23 := by kernel_rfl
private def c3GroupHessian210_33Chunk0 : Poly := [([0,0], 320),([0,4], 320),([0,6], 320),([0,8], 320),([0,9], 320),([4,4], 80),([4,6], 160),([4,8], 160),([4,9], 160),([6,6], 80),([6,8], 160),([6,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian210_33 : Poly := List.flatten [c3GroupHessian210_33Chunk0]
theorem c3GroupHessian210_33_check : sumFast (c3TensorGroup210.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian210_33 := by kernel_rfl
end D4.Secondary
