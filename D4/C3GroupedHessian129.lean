import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup129_det_check : c3TensorGroup129.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 169)) = true := by kernel_rfl
private def c3GroupHessian129_00Chunk0 : Poly := [([0,0], 48),([0,1], 16),([0,6], 80),([0,9], 80),([1,1], 8),([5,5], 40),([6,6], 40),([6,9], 80),([9,9], 40)]
def c3GroupHessian129_00 : Poly := List.flatten [c3GroupHessian129_00Chunk0]
theorem c3GroupHessian129_00_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian129_00 := by kernel_rfl
private def c3GroupHessian129_01Chunk0 : Poly := [([0,0], 24),([0,1], 4),([0,5], -40),([0,6], 20),([0,7], 24),([0,9], 60),([1,7], 4),([2,5], -40),([5,8], -40),([6,7], 20),([6,9], 40),([7,9], 20),([9,9], 40)]
def c3GroupHessian129_01 : Poly := List.flatten [c3GroupHessian129_01Chunk0]
theorem c3GroupHessian129_01_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian129_01 := by kernel_rfl
private def c3GroupHessian129_02Chunk0 : Poly := [([0,0], -24),([0,1], -4),([0,5], -40),([0,6], -20),([0,7], -24),([0,9], -60),([1,7], -4),([3,5], -40),([5,5], -40),([6,7], -20),([6,9], -40),([7,9], -20),([9,9], -40)]
def c3GroupHessian129_02 : Poly := List.flatten [c3GroupHessian129_02Chunk0]
theorem c3GroupHessian129_02_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian129_02 := by kernel_rfl
private def c3GroupHessian129_03Chunk0 : Poly := [([0,0], -40),([0,4], -16),([0,5], 40),([0,6], -80),([0,9], -80),([1,4], 4),([4,6], -20),([4,9], -20),([5,8], 40),([6,6], -40),([6,9], -80),([9,9], -40)]
def c3GroupHessian129_03 : Poly := List.flatten [c3GroupHessian129_03Chunk0]
theorem c3GroupHessian129_03_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian129_03 := by kernel_rfl
private def c3GroupHessian129_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 80),([0,9], 40),([2,2], 40),([2,8], 80),([7,7], 16),([7,9], 40),([8,8], 40),([9,9], 40)]
def c3GroupHessian129_11 : Poly := List.flatten [c3GroupHessian129_11Chunk0]
theorem c3GroupHessian129_11_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian129_11 := by kernel_rfl
private def c3GroupHessian129_12Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -32),([0,8], 40),([0,9], -40),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -16),([7,9], -40),([9,9], -40)]
def c3GroupHessian129_12 : Poly := List.flatten [c3GroupHessian129_12Chunk0]
theorem c3GroupHessian129_12_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian129_12 := by kernel_rfl
private def c3GroupHessian129_13Chunk0 : Poly := [([0,0], -60),([0,2], -40),([0,4], -8),([0,6], -20),([0,7], -20),([0,8], -80),([0,9], -60),([2,8], -40),([4,7], -8),([4,9], -20),([6,7], -20),([6,9], -40),([7,9], -20),([8,8], -40),([9,9], -40)]
def c3GroupHessian129_13 : Poly := List.flatten [c3GroupHessian129_13Chunk0]
theorem c3GroupHessian129_13_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian129_13 := by kernel_rfl
private def c3GroupHessian129_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 32),([0,9], 40),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 16),([7,9], 40),([9,9], 40)]
def c3GroupHessian129_22 : Poly := List.flatten [c3GroupHessian129_22Chunk0]
theorem c3GroupHessian129_22_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian129_22 := by kernel_rfl
private def c3GroupHessian129_23Chunk0 : Poly := [([0,0], -20),([0,3], -40),([0,4], 8),([0,5], -40),([0,6], 20),([0,7], 20),([0,8], -40),([0,9], 60),([3,8], -40),([4,7], 8),([4,9], 20),([5,8], -40),([6,7], 20),([6,9], 40),([7,9], 20),([9,9], 40)]
def c3GroupHessian129_23 : Poly := List.flatten [c3GroupHessian129_23Chunk0]
theorem c3GroupHessian129_23_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian129_23 := by kernel_rfl
private def c3GroupHessian129_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,6], 40),([4,9], 40),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian129_33 : Poly := List.flatten [c3GroupHessian129_33Chunk0]
theorem c3GroupHessian129_33_check : sumFast (c3TensorGroup129.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian129_33 := by kernel_rfl
end D4.Secondary
