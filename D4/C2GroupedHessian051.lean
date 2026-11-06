import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup51_det_check : c2TensorGroup51.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 70)) = true := by kernel_rfl
private def c2GroupHessian51_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 32),([0,6], 80),([1,1], 40),([1,6], 80),([5,5], 16),([6,6], 40)]
def c2GroupHessian51_00 : Poly := List.flatten [c2GroupHessian51_00Chunk0]
theorem c2GroupHessian51_00_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian51_00 := by kernel_rfl
private def c2GroupHessian51_01Chunk0 : Poly := [([0,0], 24),([0,2], 4),([0,5], 24),([0,7], -40),([0,8], 20),([1,7], -40),([2,5], 4),([5,8], 20),([6,7], -40)]
def c2GroupHessian51_01 : Poly := List.flatten [c2GroupHessian51_01Chunk0]
theorem c2GroupHessian51_01_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian51_01 := by kernel_rfl
private def c2GroupHessian51_02Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,3], 40),([0,5], -32),([0,6], 40),([0,7], 40),([0,9], 40),([1,3], 40),([1,7], 40),([1,9], 40),([3,6], 40),([5,5], -16),([6,7], 40),([6,9], 40)]
def c2GroupHessian51_02 : Poly := List.flatten [c2GroupHessian51_02Chunk0]
theorem c2GroupHessian51_02_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian51_02 := by kernel_rfl
private def c2GroupHessian51_03Chunk0 : Poly := [([0,0], -60),([0,1], -40),([0,4], -8),([0,5], -20),([0,6], -80),([0,8], -20),([0,9], -40),([1,6], -40),([1,9], -40),([4,5], -8),([5,8], -20),([6,6], -40),([6,9], -40)]
def c2GroupHessian51_03 : Poly := List.flatten [c2GroupHessian51_03Chunk0]
theorem c2GroupHessian51_03_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian51_03 := by kernel_rfl
private def c2GroupHessian51_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,8], 80),([2,2], 8),([7,7], 40),([8,8], 40)]
def c2GroupHessian51_11 : Poly := List.flatten [c2GroupHessian51_11Chunk0]
theorem c2GroupHessian51_11_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian51_11 := by kernel_rfl
private def c2GroupHessian51_12Chunk0 : Poly := [([0,0], -24),([0,2], -4),([0,5], -24),([0,7], -40),([0,8], -20),([2,5], -4),([3,7], -40),([5,8], -20),([7,7], -40),([7,9], -40)]
def c2GroupHessian51_12 : Poly := List.flatten [c2GroupHessian51_12Chunk0]
theorem c2GroupHessian51_12_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian51_12 := by kernel_rfl
private def c2GroupHessian51_13Chunk0 : Poly := [([0,0], -40),([0,4], -16),([0,7], 40),([0,8], -80),([2,4], 4),([4,8], -20),([6,7], 40),([7,9], 40),([8,8], -40)]
def c2GroupHessian51_13 : Poly := List.flatten [c2GroupHessian51_13Chunk0]
theorem c2GroupHessian51_13_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian51_13 := by kernel_rfl
private def c2GroupHessian51_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 32),([0,7], 80),([0,9], 80),([3,3], 40),([3,7], 80),([3,9], 80),([5,5], 16),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian51_22 : Poly := List.flatten [c2GroupHessian51_22Chunk0]
theorem c2GroupHessian51_22_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian51_22 := by kernel_rfl
private def c2GroupHessian51_23Chunk0 : Poly := [([0,0], -20),([0,3], -40),([0,4], 8),([0,5], 20),([0,6], -40),([0,7], -40),([0,8], 20),([0,9], -80),([3,6], -40),([3,9], -40),([4,5], 8),([5,8], 20),([6,7], -40),([6,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian51_23 : Poly := List.flatten [c2GroupHessian51_23Chunk0]
theorem c2GroupHessian51_23_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian51_23 := by kernel_rfl
private def c2GroupHessian51_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,8], 40),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c2GroupHessian51_33 : Poly := List.flatten [c2GroupHessian51_33Chunk0]
theorem c2GroupHessian51_33_check : sumFast (c2TensorGroup51.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian51_33 := by kernel_rfl
end D4.Secondary
