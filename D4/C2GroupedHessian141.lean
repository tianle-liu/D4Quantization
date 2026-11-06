import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup141_det_check : c2TensorGroup141.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 179)) = true := by kernel_rfl
private def c2GroupHessian141_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 40)]
def c2GroupHessian141_00 : Poly := List.flatten [c2GroupHessian141_00Chunk0]
theorem c2GroupHessian141_00_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian141_00 := by kernel_rfl
private def c2GroupHessian141_01Chunk0 : Poly := [([0,0], 8),([0,6], -40),([0,8], -16),([1,8], -20),([2,6], -40),([5,8], -20),([6,7], -40)]
def c2GroupHessian141_01 : Poly := List.flatten [c2GroupHessian141_01Chunk0]
theorem c2GroupHessian141_01_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian141_01 := by kernel_rfl
private def c2GroupHessian141_02Chunk0 : Poly := [([0,0], -24),([0,1], -20),([0,3], 24),([0,5], -60),([0,6], 40),([1,3], 20),([1,5], -40),([3,5], 20),([5,5], -40),([6,7], 40),([6,9], 40)]
def c2GroupHessian141_02 : Poly := List.flatten [c2GroupHessian141_02Chunk0]
theorem c2GroupHessian141_02_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian141_02 := by kernel_rfl
private def c2GroupHessian141_03Chunk0 : Poly := [([0,0], -8),([0,6], -40),([0,8], 16),([1,8], 20),([4,6], -40),([5,8], 20),([6,6], -40),([6,9], -40)]
def c2GroupHessian141_03 : Poly := List.flatten [c2GroupHessian141_03Chunk0]
theorem c2GroupHessian141_03_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian141_03 := by kernel_rfl
private def c2GroupHessian141_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,8], 8),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16)]
def c2GroupHessian141_11 : Poly := List.flatten [c2GroupHessian141_11Chunk0]
theorem c2GroupHessian141_11_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian141_11 := by kernel_rfl
private def c2GroupHessian141_12Chunk0 : Poly := [([0,0], -44),([0,2], -40),([0,3], 4),([0,7], -80),([0,8], 8),([0,9], -40),([2,7], -40),([2,9], -40),([3,8], -8),([5,8], 20),([7,7], -40),([7,9], -40)]
def c2GroupHessian141_12 : Poly := List.flatten [c2GroupHessian141_12Chunk0]
theorem c2GroupHessian141_12_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian141_12 := by kernel_rfl
private def c2GroupHessian141_13Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -8),([0,9], 40),([2,4], 40),([2,6], 40),([2,9], 40),([4,7], 40),([6,7], 40),([7,9], 40),([8,8], -16)]
def c2GroupHessian141_13 : Poly := List.flatten [c2GroupHessian141_13Chunk0]
theorem c2GroupHessian141_13_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian141_13 := by kernel_rfl
private def c2GroupHessian141_22Chunk0 : Poly := [([0,0], 56),([0,3], -16),([0,5], 40),([0,7], 80),([0,9], 80),([3,3], 16),([3,5], -40),([5,5], 40),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian141_22 : Poly := List.flatten [c2GroupHessian141_22Chunk0]
theorem c2GroupHessian141_22_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian141_22 := by kernel_rfl
private def c2GroupHessian141_23Chunk0 : Poly := [([0,0], -36),([0,3], -4),([0,4], -40),([0,6], -40),([0,7], -40),([0,8], -8),([0,9], -80),([3,8], 8),([4,7], -40),([4,9], -40),([5,8], -20),([6,7], -40),([6,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian141_23 : Poly := List.flatten [c2GroupHessian141_23Chunk0]
theorem c2GroupHessian141_23_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian141_23 := by kernel_rfl
private def c2GroupHessian141_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 80),([4,4], 40),([4,6], 80),([4,9], 80),([6,6], 40),([6,9], 80),([8,8], 16),([9,9], 40)]
def c2GroupHessian141_33 : Poly := List.flatten [c2GroupHessian141_33Chunk0]
theorem c2GroupHessian141_33_check : sumFast (c2TensorGroup141.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian141_33 := by kernel_rfl
end D4.Secondary
