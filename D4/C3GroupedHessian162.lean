import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup162_det_check : c3TensorGroup162.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 210)) = true := by kernel_rfl
private def c3GroupHessian162_00Chunk0 : Poly := [([0,0], 48),([0,1], 16),([0,5], 8),([0,6], 8),([0,9], 80),([1,1], 8),([1,5], 8),([1,6], 8),([5,5], 16),([5,6], -16),([6,6], 16),([9,9], 40)]
def c3GroupHessian162_00 : Poly := List.flatten [c3GroupHessian162_00Chunk0]
theorem c3GroupHessian162_00_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian162_00 := by kernel_rfl
private def c3GroupHessian162_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40),([0,9], 120),([2,9], 40),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian162_01 : Poly := List.flatten [c3GroupHessian162_01Chunk0]
theorem c3GroupHessian162_01_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian162_01 := by kernel_rfl
private def c3GroupHessian162_02Chunk0 : Poly := [([0,0], -40),([0,5], -24),([0,6], 20),([0,7], -40),([0,9], -80),([1,5], -4),([3,5], -20),([3,6], 20),([5,5], -16),([5,6], 8),([7,9], -40),([9,9], -40)]
def c3GroupHessian162_02 : Poly := List.flatten [c3GroupHessian162_02Chunk0]
theorem c3GroupHessian162_02_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian162_02 := by kernel_rfl
private def c3GroupHessian162_03Chunk0 : Poly := [([0,0], -40),([0,4], 8),([0,5], 20),([0,6], -24),([0,8], -40),([0,9], -80),([1,4], 8),([1,6], -4),([4,5], 4),([4,6], 4),([5,6], 8),([6,6], -16),([8,9], -40),([9,9], -40)]
def c3GroupHessian162_03 : Poly := List.flatten [c3GroupHessian162_03Chunk0]
theorem c3GroupHessian162_03_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian162_03 := by kernel_rfl
private def c3GroupHessian162_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([0,9], 160),([2,2], 40),([2,7], 80),([2,8], 80),([2,9], 80),([7,7], 40),([7,8], 80),([7,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian162_11 : Poly := List.flatten [c3GroupHessian162_11Chunk0]
theorem c3GroupHessian162_11_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian162_11 := by kernel_rfl
private def c3GroupHessian162_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([0,9], -120),([2,7], -40),([2,9], -40),([7,7], -40),([7,8], -40),([7,9], -80),([8,9], -40),([9,9], -40)]
def c3GroupHessian162_12 : Poly := List.flatten [c3GroupHessian162_12Chunk0]
theorem c3GroupHessian162_12_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian162_12 := by kernel_rfl
private def c3GroupHessian162_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([0,9], -120),([2,8], -40),([2,9], -40),([7,8], -40),([7,9], -40),([8,8], -40),([8,9], -80),([9,9], -40)]
def c3GroupHessian162_13 : Poly := List.flatten [c3GroupHessian162_13Chunk0]
theorem c3GroupHessian162_13_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian162_13 := by kernel_rfl
private def c3GroupHessian162_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 40),([0,7], 80),([0,9], 80),([3,3], 40),([3,5], 40),([5,5], 16),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian162_22 : Poly := List.flatten [c3GroupHessian162_22Chunk0]
theorem c3GroupHessian162_22_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian162_22 := by kernel_rfl
private def c3GroupHessian162_23Chunk0 : Poly := [([0,3], -40),([0,5], -20),([0,6], -20),([0,7], 40),([0,8], 40),([0,9], 80),([3,6], -20),([4,5], -4),([5,6], -8),([7,8], 40),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian162_23 : Poly := List.flatten [c3GroupHessian162_23Chunk0]
theorem c3GroupHessian162_23_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian162_23 := by kernel_rfl
private def c3GroupHessian162_33Chunk0 : Poly := [([0,0], 80),([0,6], 40),([0,8], 80),([0,9], 80),([4,4], 8),([4,6], -8),([6,6], 16),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian162_33 : Poly := List.flatten [c3GroupHessian162_33Chunk0]
theorem c3GroupHessian162_33_check : sumFast (c3TensorGroup162.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian162_33 := by kernel_rfl
end D4.Secondary
