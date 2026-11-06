import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup194_det_check : c3TensorGroup194.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 248)) = true := by kernel_rfl
private def c3GroupHessian194_00Chunk0 : Poly := [([0,0], 56),([0,1], 8),([0,5], 80),([0,6], 40),([0,9], 80),([1,1], 8),([5,5], 40),([5,9], 80),([6,6], 40),([9,9], 40)]
def c3GroupHessian194_00 : Poly := List.flatten [c3GroupHessian194_00Chunk0]
theorem c3GroupHessian194_00_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian194_00 := by kernel_rfl
private def c3GroupHessian194_01Chunk0 : Poly := [([0,0], 56),([0,1], 4),([0,2], -8),([0,5], 40),([0,6], 20),([0,7], 40),([0,8], 20),([0,9], 80),([1,2], 4),([2,6], -20),([5,7], 40),([5,9], 40),([6,8], 40),([7,9], 40),([9,9], 40)]
def c3GroupHessian194_01 : Poly := List.flatten [c3GroupHessian194_01Chunk0]
theorem c3GroupHessian194_01_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian194_01 := by kernel_rfl
private def c3GroupHessian194_02Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -120),([0,7], -40),([0,9], -120),([3,5], -40),([3,9], -40),([5,5], -40),([5,7], -40),([5,9], -80),([7,9], -40),([9,9], -40)]
def c3GroupHessian194_02 : Poly := List.flatten [c3GroupHessian194_02Chunk0]
theorem c3GroupHessian194_02_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian194_02 := by kernel_rfl
private def c3GroupHessian194_03Chunk0 : Poly := [([0,0], -24),([0,4], -8),([0,6], -60),([0,8], -20),([0,9], -40),([1,4], 4),([4,6], -20),([5,9], -40),([6,6], -40),([6,8], -40),([9,9], -40)]
def c3GroupHessian194_03 : Poly := List.flatten [c3GroupHessian194_03Chunk0]
theorem c3GroupHessian194_03_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian194_03 := by kernel_rfl
private def c3GroupHessian194_11Chunk0 : Poly := [([0,0], 56),([0,2], -16),([0,7], 80),([0,8], 40),([0,9], 80),([2,2], 16),([2,8], -40),([7,7], 40),([7,9], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian194_11 : Poly := List.flatten [c3GroupHessian194_11Chunk0]
theorem c3GroupHessian194_11_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian194_11 := by kernel_rfl
private def c3GroupHessian194_12Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -40),([0,7], -120),([0,9], -120),([3,7], -40),([3,9], -40),([5,7], -40),([5,9], -40),([7,7], -40),([7,9], -80),([9,9], -40)]
def c3GroupHessian194_12 : Poly := List.flatten [c3GroupHessian194_12Chunk0]
theorem c3GroupHessian194_12_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian194_12 := by kernel_rfl
private def c3GroupHessian194_13Chunk0 : Poly := [([0,0], -24),([0,2], 24),([0,4], -8),([0,6], -20),([0,8], -60),([0,9], -40),([2,4], 16),([2,6], 20),([2,8], 20),([4,8], -20),([6,8], -40),([7,9], -40),([8,8], -40),([9,9], -40)]
def c3GroupHessian194_13 : Poly := List.flatten [c3GroupHessian194_13Chunk0]
theorem c3GroupHessian194_13_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian194_13 := by kernel_rfl
private def c3GroupHessian194_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 40),([3,5], 80),([3,7], 80),([3,9], 80),([5,5], 40),([5,7], 80),([5,9], 80),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian194_22 : Poly := List.flatten [c3GroupHessian194_22Chunk0]
theorem c3GroupHessian194_22_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian194_22 := by kernel_rfl
private def c3GroupHessian194_23Chunk0 : Poly := [([0,9], 80),([3,9], 40),([5,9], 40),([7,9], 40),([9,9], 40)]
def c3GroupHessian194_23 : Poly := List.flatten [c3GroupHessian194_23Chunk0]
theorem c3GroupHessian194_23_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian194_23 := by kernel_rfl
private def c3GroupHessian194_33Chunk0 : Poly := [([0,0], 48),([0,4], 48),([0,6], 80),([0,8], 80),([4,4], 16),([4,6], 40),([4,8], 40),([6,6], 40),([6,8], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian194_33 : Poly := List.flatten [c3GroupHessian194_33Chunk0]
theorem c3GroupHessian194_33_check : sumFast (c3TensorGroup194.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian194_33 := by kernel_rfl
end D4.Secondary
