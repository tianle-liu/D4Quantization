import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup121_det_check : c2TensorGroup121.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 155)) = true := by kernel_rfl
private def c2GroupHessian121_00Chunk0 : Poly := [([0,0], 48),([0,1], 8),([0,5], 80),([0,6], 80),([1,1], 16),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian121_00 : Poly := List.flatten [c2GroupHessian121_00Chunk0]
theorem c2GroupHessian121_00_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian121_00 := by kernel_rfl
private def c2GroupHessian121_01Chunk0 : Poly := [([0,0], 8),([0,1], -16),([0,2], -40),([1,7], -20),([1,8], -20),([2,5], -40),([2,6], -40)]
def c2GroupHessian121_01 : Poly := List.flatten [c2GroupHessian121_01Chunk0]
theorem c2GroupHessian121_01_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian121_01 := by kernel_rfl
private def c2GroupHessian121_02Chunk0 : Poly := [([0,0], -44),([0,1], 8),([0,3], -40),([0,5], -80),([0,6], -40),([0,9], 4),([1,7], 20),([1,9], -8),([3,5], -40),([3,6], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian121_02 : Poly := List.flatten [c2GroupHessian121_02Chunk0]
theorem c2GroupHessian121_02_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian121_02 := by kernel_rfl
private def c2GroupHessian121_03Chunk0 : Poly := [([0,0], -44),([0,1], 8),([0,4], -40),([0,5], -40),([0,6], -80),([0,9], -4),([1,8], 20),([1,9], 8),([4,5], -40),([4,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian121_03 : Poly := List.flatten [c2GroupHessian121_03Chunk0]
theorem c2GroupHessian121_03_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian121_03 := by kernel_rfl
private def c2GroupHessian121_11Chunk0 : Poly := [([0,0], 48),([0,7], 80),([0,8], 80),([2,2], 40),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian121_11 : Poly := List.flatten [c2GroupHessian121_11Chunk0]
theorem c2GroupHessian121_11_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian121_11 := by kernel_rfl
private def c2GroupHessian121_12Chunk0 : Poly := [([0,0], -24),([0,2], 40),([0,7], -60),([0,8], -20),([0,9], 24),([2,3], 40),([2,5], 40),([7,7], -40),([7,8], -40),([7,9], 20),([8,9], 20)]
def c2GroupHessian121_12 : Poly := List.flatten [c2GroupHessian121_12Chunk0]
theorem c2GroupHessian121_12_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian121_12 := by kernel_rfl
private def c2GroupHessian121_13Chunk0 : Poly := [([0,0], -24),([0,2], 40),([0,7], -20),([0,8], -60),([0,9], -24),([2,4], 40),([2,6], 40),([7,8], -40),([7,9], -20),([8,8], -40),([8,9], -20)]
def c2GroupHessian121_13 : Poly := List.flatten [c2GroupHessian121_13Chunk0]
theorem c2GroupHessian121_13_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian121_13 := by kernel_rfl
private def c2GroupHessian121_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], -16),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 40),([7,9], -40),([9,9], 16)]
def c2GroupHessian121_22 : Poly := List.flatten [c2GroupHessian121_22Chunk0]
theorem c2GroupHessian121_22_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian121_22 := by kernel_rfl
private def c2GroupHessian121_23Chunk0 : Poly := [([0,0], 48),([0,3], 40),([0,4], 40),([0,5], 40),([0,6], 40),([0,7], 20),([0,8], 20),([0,9], -8),([3,4], 40),([3,6], 40),([4,5], 40),([5,6], 40),([7,8], 40),([7,9], 20),([8,9], -20),([9,9], -16)]
def c2GroupHessian121_23 : Poly := List.flatten [c2GroupHessian121_23Chunk0]
theorem c2GroupHessian121_23_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian121_23 := by kernel_rfl
private def c2GroupHessian121_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 40),([0,9], 32),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 40),([8,9], 40),([9,9], 16)]
def c2GroupHessian121_33 : Poly := List.flatten [c2GroupHessian121_33Chunk0]
theorem c2GroupHessian121_33_check : sumFast (c2TensorGroup121.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian121_33 := by kernel_rfl
end D4.Secondary
