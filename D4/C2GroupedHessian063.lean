import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup63_det_check : c2TensorGroup63.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 84)) = true := by kernel_rfl
private def c2GroupHessian63_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 32),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16)]
def c2GroupHessian63_00 : Poly := List.flatten [c2GroupHessian63_00Chunk0]
theorem c2GroupHessian63_00_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian63_00 := by kernel_rfl
private def c2GroupHessian63_01Chunk0 : Poly := [([0,0], -4),([0,2], -8),([0,6], -4),([0,7], -20),([0,8], -40),([1,8], -40),([2,6], -8),([5,8], -40),([6,7], -20)]
def c2GroupHessian63_01 : Poly := List.flatten [c2GroupHessian63_01Chunk0]
theorem c2GroupHessian63_01_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian63_01 := by kernel_rfl
private def c2GroupHessian63_02Chunk0 : Poly := [([0,0], -32),([0,1], -40),([0,3], 4),([0,5], -80),([0,6], 8),([0,7], 20),([0,9], -40),([1,5], -40),([1,9], -40),([3,6], 4),([5,5], -40),([5,9], -40),([6,7], 20)]
def c2GroupHessian63_02 : Poly := List.flatten [c2GroupHessian63_02Chunk0]
theorem c2GroupHessian63_02_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian63_02 := by kernel_rfl
private def c2GroupHessian63_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -32),([0,8], 40),([0,9], 40),([1,4], 40),([1,8], 40),([1,9], 40),([4,5], 40),([5,8], 40),([5,9], 40),([6,6], -16)]
def c2GroupHessian63_03 : Poly := List.flatten [c2GroupHessian63_03Chunk0]
theorem c2GroupHessian63_03_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian63_03 := by kernel_rfl
private def c2GroupHessian63_11Chunk0 : Poly := [([0,0], 16),([0,2], 24),([0,7], 40),([2,2], 16),([2,7], 40),([7,7], 40),([8,8], 40)]
def c2GroupHessian63_11 : Poly := List.flatten [c2GroupHessian63_11Chunk0]
theorem c2GroupHessian63_11_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian63_11 := by kernel_rfl
private def c2GroupHessian63_12Chunk0 : Poly := [([0,0], -12),([0,2], -8),([0,3], 4),([0,7], -40),([0,8], 40),([2,3], 4),([2,7], -20),([5,8], 40),([7,7], -40),([8,9], 40)]
def c2GroupHessian63_12 : Poly := List.flatten [c2GroupHessian63_12Chunk0]
theorem c2GroupHessian63_12_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian63_12 := by kernel_rfl
private def c2GroupHessian63_13Chunk0 : Poly := [([0,0], 4),([0,2], 8),([0,6], 4),([0,7], 20),([0,8], -40),([2,6], 8),([4,8], -40),([6,7], 20),([8,8], -40),([8,9], -40)]
def c2GroupHessian63_13 : Poly := List.flatten [c2GroupHessian63_13Chunk0]
theorem c2GroupHessian63_13_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian63_13 := by kernel_rfl
private def c2GroupHessian63_22Chunk0 : Poly := [([0,0], 56),([0,3], 8),([0,5], 80),([0,7], 40),([0,9], 80),([3,3], 8),([5,5], 40),([5,9], 80),([7,7], 40),([9,9], 40)]
def c2GroupHessian63_22 : Poly := List.flatten [c2GroupHessian63_22Chunk0]
theorem c2GroupHessian63_22_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian63_22 := by kernel_rfl
private def c2GroupHessian63_23Chunk0 : Poly := [([0,0], -48),([0,3], -4),([0,4], -40),([0,5], -40),([0,6], -8),([0,7], -20),([0,8], -40),([0,9], -80),([3,6], -4),([4,5], -40),([4,9], -40),([5,8], -40),([5,9], -40),([6,7], -20),([8,9], -40),([9,9], -40)]
def c2GroupHessian63_23 : Poly := List.flatten [c2GroupHessian63_23Chunk0]
theorem c2GroupHessian63_23_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian63_23 := by kernel_rfl
private def c2GroupHessian63_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 32),([0,8], 80),([0,9], 80),([4,4], 40),([4,8], 80),([4,9], 80),([6,6], 16),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian63_33 : Poly := List.flatten [c2GroupHessian63_33Chunk0]
theorem c2GroupHessian63_33_check : sumFast (c2TensorGroup63.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian63_33 := by kernel_rfl
end D4.Secondary
