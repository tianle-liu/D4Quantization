import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup115_det_check : c2TensorGroup115.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 148)) = true := by kernel_rfl
private def c2GroupHessian115_00Chunk0 : Poly := [([0,0], 56),([0,1], 40),([0,5], 80),([0,6], 80),([1,1], 40),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian115_00 : Poly := List.flatten [c2GroupHessian115_00Chunk0]
theorem c2GroupHessian115_00_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian115_00 := by kernel_rfl
private def c2GroupHessian115_01Chunk0 : Poly := [([0,0], 8),([0,2], -40),([0,7], -8),([0,8], 4),([1,7], -20),([2,5], -40),([2,6], -40)]
def c2GroupHessian115_01 : Poly := List.flatten [c2GroupHessian115_01Chunk0]
theorem c2GroupHessian115_01_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian115_01 := by kernel_rfl
private def c2GroupHessian115_02Chunk0 : Poly := [([0,0], -32),([0,1], 20),([0,3], -40),([0,5], -80),([0,6], -40),([0,7], 8),([0,9], 20),([1,7], 20),([1,9], 40),([3,5], -40),([3,6], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian115_02 : Poly := List.flatten [c2GroupHessian115_02Chunk0]
theorem c2GroupHessian115_02_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian115_02 := by kernel_rfl
private def c2GroupHessian115_03Chunk0 : Poly := [([0,0], -56),([0,1], -20),([0,4], -40),([0,5], -40),([0,6], -80),([0,8], -4),([0,9], -20),([1,9], -40),([4,5], -40),([4,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian115_03 : Poly := List.flatten [c2GroupHessian115_03Chunk0]
theorem c2GroupHessian115_03_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian115_03 := by kernel_rfl
private def c2GroupHessian115_11Chunk0 : Poly := [([0,0], 16),([0,7], 16),([0,8], 16),([2,2], 40),([7,7], 16),([7,8], 8),([8,8], 8)]
def c2GroupHessian115_11 : Poly := List.flatten [c2GroupHessian115_11Chunk0]
theorem c2GroupHessian115_11_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian115_11 := by kernel_rfl
private def c2GroupHessian115_12Chunk0 : Poly := [([0,0], -8),([0,2], 40),([0,7], -24),([0,8], -4),([2,3], 40),([2,5], 40),([7,7], -16),([7,8], -4),([7,9], -20)]
def c2GroupHessian115_12 : Poly := List.flatten [c2GroupHessian115_12Chunk0]
theorem c2GroupHessian115_12_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian115_12 := by kernel_rfl
private def c2GroupHessian115_13Chunk0 : Poly := [([0,0], -8),([0,2], 40),([0,7], 8),([0,8], -12),([2,4], 40),([2,6], 40),([7,8], -4),([7,9], 20),([8,8], -8)]
def c2GroupHessian115_13 : Poly := List.flatten [c2GroupHessian115_13Chunk0]
theorem c2GroupHessian115_13_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian115_13 := by kernel_rfl
private def c2GroupHessian115_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 32),([0,9], 40),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 16),([7,9], 40),([9,9], 40)]
def c2GroupHessian115_22 : Poly := List.flatten [c2GroupHessian115_22Chunk0]
theorem c2GroupHessian115_22_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian115_22 := by kernel_rfl
private def c2GroupHessian115_23Chunk0 : Poly := [([0,0], 32),([0,3], 40),([0,4], 40),([0,5], 40),([0,6], 40),([0,7], -8),([0,8], 4),([0,9], -40),([3,4], 40),([3,6], 40),([4,5], 40),([5,6], 40),([7,8], 4),([7,9], -20),([9,9], -40)]
def c2GroupHessian115_23 : Poly := List.flatten [c2GroupHessian115_23Chunk0]
theorem c2GroupHessian115_23_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian115_23 := by kernel_rfl
private def c2GroupHessian115_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 40),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 8),([9,9], 40)]
def c2GroupHessian115_33 : Poly := List.flatten [c2GroupHessian115_33Chunk0]
theorem c2GroupHessian115_33_check : sumFast (c2TensorGroup115.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian115_33 := by kernel_rfl
end D4.Secondary
