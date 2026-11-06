import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup190_det_check : c2TensorGroup190.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 243)) = true := by kernel_rfl
private def c2GroupHessian190_00Chunk0 : Poly := [([0,0], 48),([0,1], 16),([0,5], 80),([0,6], 8),([1,1], 8),([1,6], 8),([5,5], 40),([6,6], 16)]
def c2GroupHessian190_00 : Poly := List.flatten [c2GroupHessian190_00Chunk0]
theorem c2GroupHessian190_00_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian190_00 := by kernel_rfl
private def c2GroupHessian190_01Chunk0 : Poly := [([0,0], 44),([0,1], 4),([0,5], 40),([0,6], -8),([0,7], 40),([0,8], 4),([1,8], 4),([2,6], -20),([5,7], 40),([6,8], -8)]
def c2GroupHessian190_01 : Poly := List.flatten [c2GroupHessian190_01Chunk0]
theorem c2GroupHessian190_01_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian190_01 := by kernel_rfl
private def c2GroupHessian190_02Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -120),([0,7], -40),([0,9], -40),([3,5], -40),([5,5], -40),([5,7], -40),([5,9], -40)]
def c2GroupHessian190_02 : Poly := List.flatten [c2GroupHessian190_02Chunk0]
theorem c2GroupHessian190_02_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian190_02 := by kernel_rfl
private def c2GroupHessian190_03Chunk0 : Poly := [([0,0], -4),([0,1], -4),([0,6], -16),([0,8], -4),([0,9], 40),([1,6], -4),([1,8], -4),([4,6], -20),([5,9], 40),([6,6], -16),([6,8], 8)]
def c2GroupHessian190_03 : Poly := List.flatten [c2GroupHessian190_03Chunk0]
theorem c2GroupHessian190_03_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian190_03 := by kernel_rfl
private def c2GroupHessian190_11Chunk0 : Poly := [([0,0], 56),([0,2], 40),([0,7], 80),([0,8], 32),([2,2], 40),([2,8], 40),([7,7], 40),([8,8], 16)]
def c2GroupHessian190_11 : Poly := List.flatten [c2GroupHessian190_11Chunk0]
theorem c2GroupHessian190_11_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian190_11 := by kernel_rfl
private def c2GroupHessian190_12Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -40),([0,7], -120),([0,9], -40),([3,7], -40),([5,7], -40),([7,7], -40),([7,9], -40)]
def c2GroupHessian190_12 : Poly := List.flatten [c2GroupHessian190_12Chunk0]
theorem c2GroupHessian190_12_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian190_12 := by kernel_rfl
private def c2GroupHessian190_13Chunk0 : Poly := [([0,0], 4),([0,2], 20),([0,4], 20),([0,6], 8),([0,8], -12),([0,9], 40),([2,4], 40),([2,6], 20),([2,8], -20),([4,8], 20),([6,8], 8),([7,9], 40),([8,8], -16)]
def c2GroupHessian190_13 : Poly := List.flatten [c2GroupHessian190_13Chunk0]
theorem c2GroupHessian190_13_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian190_13 := by kernel_rfl
private def c2GroupHessian190_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 40),([3,5], 80),([3,7], 80),([3,9], 80),([5,5], 40),([5,7], 80),([5,9], 80),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian190_22 : Poly := List.flatten [c2GroupHessian190_22Chunk0]
theorem c2GroupHessian190_22_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian190_22 := by kernel_rfl
private def c2GroupHessian190_23Chunk0 : Poly := [([0,9], -80),([3,9], -40),([5,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian190_23 : Poly := List.flatten [c2GroupHessian190_23Chunk0]
theorem c2GroupHessian190_23_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian190_23 := by kernel_rfl
private def c2GroupHessian190_33Chunk0 : Poly := [([0,0], 16),([0,4], 40),([0,6], 24),([0,8], -8),([4,4], 40),([4,6], 40),([4,8], -40),([6,6], 16),([6,8], -16),([8,8], 16),([9,9], 40)]
def c2GroupHessian190_33 : Poly := List.flatten [c2GroupHessian190_33Chunk0]
theorem c2GroupHessian190_33_check : sumFast (c2TensorGroup190.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian190_33 := by kernel_rfl
end D4.Secondary
