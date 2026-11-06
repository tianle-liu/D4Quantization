import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup24_det_check : c2TensorGroup24.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 39)) = true := by kernel_rfl
private def c2GroupHessian24_00Chunk0 : Poly := [([0,0], 48),([0,5], 80),([0,6], 16),([1,1], 40),([5,5], 40),([6,6], 8)]
def c2GroupHessian24_00 : Poly := List.flatten [c2GroupHessian24_00Chunk0]
theorem c2GroupHessian24_00_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian24_00 := by kernel_rfl
private def c2GroupHessian24_01Chunk0 : Poly := [([0,0], 24),([0,1], -40),([0,2], 24),([0,5], 20),([0,6], 4),([1,7], -40),([1,8], -40),([2,5], 20),([2,6], 4)]
def c2GroupHessian24_01 : Poly := List.flatten [c2GroupHessian24_01Chunk0]
theorem c2GroupHessian24_01_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian24_01 := by kernel_rfl
private def c2GroupHessian24_02Chunk0 : Poly := [([0,0], -40),([0,1], 40),([0,5], -80),([0,9], -16),([1,3], 40),([1,7], 40),([5,5], -40),([5,9], -20),([6,9], 4)]
def c2GroupHessian24_02 : Poly := List.flatten [c2GroupHessian24_02Chunk0]
theorem c2GroupHessian24_02_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian24_02 := by kernel_rfl
private def c2GroupHessian24_03Chunk0 : Poly := [([0,0], -8),([0,1], 40),([0,6], -16),([0,9], 16),([1,4], 40),([1,8], 40),([5,9], 20),([6,6], -8),([6,9], -4)]
def c2GroupHessian24_03 : Poly := List.flatten [c2GroupHessian24_03Chunk0]
theorem c2GroupHessian24_03_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian24_03 := by kernel_rfl
private def c2GroupHessian24_11Chunk0 : Poly := [([0,0], 56),([0,2], 32),([0,7], 80),([0,8], 80),([2,2], 16),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian24_11 : Poly := List.flatten [c2GroupHessian24_11Chunk0]
theorem c2GroupHessian24_11_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian24_11 := by kernel_rfl
private def c2GroupHessian24_12Chunk0 : Poly := [([0,0], -60),([0,2], -20),([0,3], -40),([0,5], -20),([0,7], -80),([0,8], -40),([0,9], -8),([2,5], -20),([2,9], -8),([3,7], -40),([3,8], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian24_12 : Poly := List.flatten [c2GroupHessian24_12Chunk0]
theorem c2GroupHessian24_12_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian24_12 := by kernel_rfl
private def c2GroupHessian24_13Chunk0 : Poly := [([0,0], -44),([0,2], -4),([0,4], -40),([0,6], -4),([0,7], -40),([0,8], -80),([0,9], 8),([2,6], -4),([2,9], 8),([4,7], -40),([4,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian24_13 : Poly := List.flatten [c2GroupHessian24_13Chunk0]
theorem c2GroupHessian24_13_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian24_13 := by kernel_rfl
private def c2GroupHessian24_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 80),([0,7], 80),([0,9], 40),([3,3], 40),([3,7], 80),([5,5], 40),([5,9], 40),([7,7], 40),([9,9], 16)]
def c2GroupHessian24_22 : Poly := List.flatten [c2GroupHessian24_22Chunk0]
theorem c2GroupHessian24_22_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian24_22 := by kernel_rfl
private def c2GroupHessian24_23Chunk0 : Poly := [([0,0], 40),([0,3], 40),([0,4], 40),([0,7], 40),([0,8], 40),([0,9], -24),([3,4], 40),([3,8], 40),([4,7], 40),([5,9], -20),([6,9], -4),([7,8], 40),([9,9], -16)]
def c2GroupHessian24_23 : Poly := List.flatten [c2GroupHessian24_23Chunk0]
theorem c2GroupHessian24_23_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian24_23 := by kernel_rfl
private def c2GroupHessian24_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 16),([0,8], 80),([0,9], 8),([4,4], 40),([4,8], 80),([6,6], 8),([6,9], 8),([8,8], 40),([9,9], 16)]
def c2GroupHessian24_33 : Poly := List.flatten [c2GroupHessian24_33Chunk0]
theorem c2GroupHessian24_33_check : sumFast (c2TensorGroup24.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian24_33 := by kernel_rfl
end D4.Secondary
