import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup63_det_check : c3TensorGroup63.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 86)) = true := by kernel_rfl
private def c3GroupHessian63_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 8),([0,9], 8),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16),([6,9], -16),([9,9], 16)]
def c3GroupHessian63_00 : Poly := List.flatten [c3GroupHessian63_00Chunk0]
theorem c3GroupHessian63_00_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian63_00 := by kernel_rfl
private def c3GroupHessian63_01Chunk0 : Poly := [([0,0], 8),([0,6], -16),([0,8], -40),([0,9], 28),([1,8], -40),([2,6], -20),([2,9], 20),([5,8], -40),([6,7], -20),([6,9], -8),([7,9], 20),([9,9], 16)]
def c3GroupHessian63_01 : Poly := List.flatten [c3GroupHessian63_01Chunk0]
theorem c3GroupHessian63_01_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian63_01 := by kernel_rfl
private def c3GroupHessian63_02Chunk0 : Poly := [([0,0], -40),([0,1], -40),([0,3], 8),([0,5], -80),([0,6], 20),([0,9], -24),([1,5], -40),([3,6], 4),([3,9], 4),([5,5], -40),([6,7], 20),([6,9], 8),([7,9], -20),([9,9], -16)]
def c3GroupHessian63_02 : Poly := List.flatten [c3GroupHessian63_02Chunk0]
theorem c3GroupHessian63_02_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian63_02 := by kernel_rfl
private def c3GroupHessian63_03Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -8),([0,8], 40),([0,9], -8),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -16),([6,9], 16),([9,9], -16)]
def c3GroupHessian63_03 : Poly := List.flatten [c3GroupHessian63_03Chunk0]
theorem c3GroupHessian63_03_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian63_03 := by kernel_rfl
private def c3GroupHessian63_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,9], 48),([2,2], 40),([2,7], 80),([2,9], 40),([7,7], 40),([7,9], 40),([8,8], 40),([9,9], 16)]
def c3GroupHessian63_11 : Poly := List.flatten [c3GroupHessian63_11Chunk0]
theorem c3GroupHessian63_11_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian63_11 := by kernel_rfl
private def c3GroupHessian63_12Chunk0 : Poly := [([0,0], -40),([0,2], -40),([0,3], 8),([0,7], -80),([0,8], 40),([0,9], -44),([2,7], -40),([2,9], -20),([3,9], 4),([5,8], 40),([7,7], -40),([7,9], -40),([9,9], -16)]
def c3GroupHessian63_12 : Poly := List.flatten [c3GroupHessian63_12Chunk0]
theorem c3GroupHessian63_12_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian63_12 := by kernel_rfl
private def c3GroupHessian63_13Chunk0 : Poly := [([0,0], -8),([0,6], 16),([0,8], -40),([0,9], -28),([2,6], 20),([2,9], -20),([4,8], -40),([6,7], 20),([6,9], 8),([7,9], -20),([8,8], -40),([9,9], -16)]
def c3GroupHessian63_13 : Poly := List.flatten [c3GroupHessian63_13Chunk0]
theorem c3GroupHessian63_13_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian63_13 := by kernel_rfl
private def c3GroupHessian63_22Chunk0 : Poly := [([0,0], 80),([0,5], 80),([0,7], 80),([0,9], 40),([3,3], 8),([3,9], -8),([5,5], 40),([7,7], 40),([7,9], 40),([9,9], 16)]
def c3GroupHessian63_22 : Poly := List.flatten [c3GroupHessian63_22Chunk0]
theorem c3GroupHessian63_22_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian63_22 := by kernel_rfl
private def c3GroupHessian63_23Chunk0 : Poly := [([0,0], -40),([0,3], -8),([0,4], -40),([0,5], -40),([0,6], -20),([0,8], -40),([0,9], 24),([3,6], -4),([3,9], -4),([4,5], -40),([5,8], -40),([6,7], -20),([6,9], -8),([7,9], 20),([9,9], 16)]
def c3GroupHessian63_23 : Poly := List.flatten [c3GroupHessian63_23Chunk0]
theorem c3GroupHessian63_23_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian63_23 := by kernel_rfl
private def c3GroupHessian63_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 8),([0,8], 80),([0,9], 8),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], -16),([8,8], 40),([9,9], 16)]
def c3GroupHessian63_33 : Poly := List.flatten [c3GroupHessian63_33Chunk0]
theorem c3GroupHessian63_33_check : sumFast (c3TensorGroup63.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian63_33 := by kernel_rfl
end D4.Secondary
