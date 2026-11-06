import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup48_det_check : c2TensorGroup48.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 66)) = true := by kernel_rfl
private def c2GroupHessian48_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 32),([0,6], 80),([1,1], 40),([1,6], 80),([5,5], 16),([6,6], 40)]
def c2GroupHessian48_00 : Poly := List.flatten [c2GroupHessian48_00Chunk0]
theorem c2GroupHessian48_00_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian48_00 := by kernel_rfl
private def c2GroupHessian48_01Chunk0 : Poly := [([0,0], 20),([0,2], 4),([0,5], 20),([0,7], -40),([0,8], 4),([1,7], -40),([2,5], 4),([5,8], 4),([6,7], -40)]
def c2GroupHessian48_01 : Poly := List.flatten [c2GroupHessian48_01Chunk0]
theorem c2GroupHessian48_01_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian48_01 := by kernel_rfl
private def c2GroupHessian48_02Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,3], 40),([0,5], -32),([0,6], 40),([0,7], 40),([0,9], 40),([1,3], 40),([1,7], 40),([1,9], 40),([3,6], 40),([5,5], -16),([6,7], 40),([6,9], 40)]
def c2GroupHessian48_02 : Poly := List.flatten [c2GroupHessian48_02Chunk0]
theorem c2GroupHessian48_02_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian48_02 := by kernel_rfl
private def c2GroupHessian48_03Chunk0 : Poly := [([0,0], -56),([0,1], -40),([0,4], -8),([0,5], -16),([0,6], -80),([0,8], -4),([0,9], -40),([1,6], -40),([1,9], -40),([4,5], -8),([5,8], -4),([6,6], -40),([6,9], -40)]
def c2GroupHessian48_03 : Poly := List.flatten [c2GroupHessian48_03Chunk0]
theorem c2GroupHessian48_03_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian48_03 := by kernel_rfl
private def c2GroupHessian48_11Chunk0 : Poly := [([0,0], 32),([0,2], 24),([0,8], 24),([2,2], 8),([2,8], 16),([7,7], 40),([8,8], 8)]
def c2GroupHessian48_11 : Poly := List.flatten [c2GroupHessian48_11Chunk0]
theorem c2GroupHessian48_11_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian48_11 := by kernel_rfl
private def c2GroupHessian48_12Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,5], -20),([0,7], -40),([0,8], -4),([2,5], -4),([3,7], -40),([5,8], -4),([7,7], -40),([7,9], -40)]
def c2GroupHessian48_12 : Poly := List.flatten [c2GroupHessian48_12Chunk0]
theorem c2GroupHessian48_12_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian48_12 := by kernel_rfl
private def c2GroupHessian48_13Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,4], -4),([0,7], 40),([0,8], -16),([2,4], 4),([2,8], -8),([4,8], 4),([6,7], 40),([7,9], 40),([8,8], -8)]
def c2GroupHessian48_13 : Poly := List.flatten [c2GroupHessian48_13Chunk0]
theorem c2GroupHessian48_13_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian48_13 := by kernel_rfl
private def c2GroupHessian48_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 32),([0,7], 80),([0,9], 80),([3,3], 40),([3,7], 80),([3,9], 80),([5,5], 16),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian48_22 : Poly := List.flatten [c2GroupHessian48_22Chunk0]
theorem c2GroupHessian48_22_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian48_22 := by kernel_rfl
private def c2GroupHessian48_23Chunk0 : Poly := [([0,0], -24),([0,3], -40),([0,4], 8),([0,5], 16),([0,6], -40),([0,7], -40),([0,8], 4),([0,9], -80),([3,6], -40),([3,9], -40),([4,5], 8),([5,8], 4),([6,7], -40),([6,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian48_23 : Poly := List.flatten [c2GroupHessian48_23Chunk0]
theorem c2GroupHessian48_23_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian48_23 := by kernel_rfl
private def c2GroupHessian48_33Chunk0 : Poly := [([0,0], 56),([0,4], 16),([0,6], 80),([0,8], 8),([0,9], 80),([4,4], 16),([4,8], -8),([6,6], 40),([6,9], 80),([8,8], 8),([9,9], 40)]
def c2GroupHessian48_33 : Poly := List.flatten [c2GroupHessian48_33Chunk0]
theorem c2GroupHessian48_33_check : sumFast (c2TensorGroup48.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian48_33 := by kernel_rfl
end D4.Secondary
