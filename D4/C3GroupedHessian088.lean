import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup88_det_check : c3TensorGroup88.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 117)) = true := by kernel_rfl
private def c3GroupHessian88_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([0,9], 160),([1,1], 40),([1,5], 80),([1,6], 80),([1,9], 80),([5,5], 40),([5,6], 80),([5,9], 80),([6,6], 40),([6,9], 80),([9,9], 40)]
def c3GroupHessian88_00 : Poly := List.flatten [c3GroupHessian88_00Chunk0]
theorem c3GroupHessian88_00_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian88_00 := by kernel_rfl
private def c3GroupHessian88_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40),([0,9], 120),([1,9], 40),([5,9], 40),([6,9], 40),([9,9], 40)]
def c3GroupHessian88_01 : Poly := List.flatten [c3GroupHessian88_01Chunk0]
theorem c3GroupHessian88_01_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian88_01 := by kernel_rfl
private def c3GroupHessian88_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([0,9], -120),([1,5], -40),([1,9], -40),([5,5], -40),([5,6], -40),([5,9], -80),([6,9], -40),([9,9], -40)]
def c3GroupHessian88_02 : Poly := List.flatten [c3GroupHessian88_02Chunk0]
theorem c3GroupHessian88_02_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian88_02 := by kernel_rfl
private def c3GroupHessian88_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([0,9], -120),([1,6], -40),([1,9], -40),([5,6], -40),([5,9], -40),([6,6], -40),([6,9], -80),([9,9], -40)]
def c3GroupHessian88_03 : Poly := List.flatten [c3GroupHessian88_03Chunk0]
theorem c3GroupHessian88_03_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian88_03 := by kernel_rfl
private def c3GroupHessian88_11Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 80),([0,8], 80),([0,9], 80),([2,2], 16),([2,7], 40),([2,8], 40),([7,7], 40),([7,8], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian88_11 : Poly := List.flatten [c3GroupHessian88_11Chunk0]
theorem c3GroupHessian88_11_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian88_11 := by kernel_rfl
private def c3GroupHessian88_12Chunk0 : Poly := [([0,0], -40),([0,2], 4),([0,5], -40),([0,7], -40),([0,9], -80),([2,3], 4),([2,7], -20),([5,9], -40),([7,7], -40),([7,8], -40),([9,9], -40)]
def c3GroupHessian88_12 : Poly := List.flatten [c3GroupHessian88_12Chunk0]
theorem c3GroupHessian88_12_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian88_12 := by kernel_rfl
private def c3GroupHessian88_13Chunk0 : Poly := [([0,0], -80),([0,2], -20),([0,4], -20),([0,6], -40),([0,7], -40),([0,8], -80),([0,9], -80),([2,4], -8),([2,8], -20),([4,7], -20),([4,8], -20),([6,9], -40),([7,8], -40),([8,8], -40),([9,9], -40)]
def c3GroupHessian88_13 : Poly := List.flatten [c3GroupHessian88_13Chunk0]
theorem c3GroupHessian88_13_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian88_13 := by kernel_rfl
private def c3GroupHessian88_22Chunk0 : Poly := [([0,0], 48),([0,3], 16),([0,5], 80),([0,9], 80),([3,3], 8),([5,5], 40),([5,9], 80),([7,7], 40),([9,9], 40)]
def c3GroupHessian88_22 : Poly := List.flatten [c3GroupHessian88_22Chunk0]
theorem c3GroupHessian88_22_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian88_22 := by kernel_rfl
private def c3GroupHessian88_23Chunk0 : Poly := [([0,0], 40),([0,4], 4),([0,5], 40),([0,6], 40),([0,7], 40),([0,9], 80),([3,4], 4),([4,7], 20),([5,6], 40),([5,9], 40),([6,9], 40),([7,8], 40),([9,9], 40)]
def c3GroupHessian88_23 : Poly := List.flatten [c3GroupHessian88_23Chunk0]
theorem c3GroupHessian88_23_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian88_23 := by kernel_rfl
private def c3GroupHessian88_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,8], 40),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian88_33 : Poly := List.flatten [c3GroupHessian88_33Chunk0]
theorem c3GroupHessian88_33_check : sumFast (c3TensorGroup88.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian88_33 := by kernel_rfl
end D4.Secondary
