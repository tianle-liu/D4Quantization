import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup77_det_check : c2TensorGroup77.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 103)) = true := by kernel_rfl
private def c2GroupHessian77_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian77_00 : Poly := List.flatten [c2GroupHessian77_00Chunk0]
theorem c2GroupHessian77_00_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian77_00 := by kernel_rfl
private def c2GroupHessian77_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian77_01 : Poly := List.flatten [c2GroupHessian77_01Chunk0]
theorem c2GroupHessian77_01_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian77_01 := by kernel_rfl
private def c2GroupHessian77_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian77_02 : Poly := List.flatten [c2GroupHessian77_02Chunk0]
theorem c2GroupHessian77_02_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian77_02 := by kernel_rfl
private def c2GroupHessian77_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian77_03 : Poly := List.flatten [c2GroupHessian77_03Chunk0]
theorem c2GroupHessian77_03_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian77_03 := by kernel_rfl
private def c2GroupHessian77_11Chunk0 : Poly := [([0,0], 48),([0,2], 8),([0,7], 16),([0,8], 8),([2,2], 16),([2,7], 8),([2,8], -16),([7,7], 8),([7,8], 8),([8,8], 16)]
def c2GroupHessian77_11 : Poly := List.flatten [c2GroupHessian77_11Chunk0]
theorem c2GroupHessian77_11_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian77_11 := by kernel_rfl
private def c2GroupHessian77_12Chunk0 : Poly := [([0,0], -44),([0,2], 8),([0,5], -40),([0,7], -12),([0,8], -8),([0,9], 4),([2,3], 20),([2,7], -4),([2,9], -8),([3,8], -20),([7,7], -8),([7,8], -4),([7,9], 4),([8,9], 16)]
def c2GroupHessian77_12 : Poly := List.flatten [c2GroupHessian77_12Chunk0]
theorem c2GroupHessian77_12_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian77_12 := by kernel_rfl
private def c2GroupHessian77_13Chunk0 : Poly := [([0,0], -44),([0,2], 8),([0,6], -40),([0,7], -4),([0,8], -20),([0,9], -4),([2,4], 20),([2,8], 8),([2,9], 8),([4,8], -20),([7,8], -4),([7,9], -4),([8,8], -16),([8,9], -16)]
def c2GroupHessian77_13 : Poly := List.flatten [c2GroupHessian77_13Chunk0]
theorem c2GroupHessian77_13_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian77_13 := by kernel_rfl
private def c2GroupHessian77_22Chunk0 : Poly := [([0,0], 56),([0,3], 40),([0,5], 80),([0,7], 8),([0,9], -16),([3,3], 40),([3,9], -40),([5,5], 40),([7,7], 8),([7,9], -8),([9,9], 16)]
def c2GroupHessian77_22 : Poly := List.flatten [c2GroupHessian77_22Chunk0]
theorem c2GroupHessian77_22_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian77_22 := by kernel_rfl
private def c2GroupHessian77_23Chunk0 : Poly := [([0,0], 48),([0,3], 20),([0,4], 20),([0,5], 40),([0,6], 40),([0,7], 4),([0,8], 8),([0,9], -8),([3,4], 40),([3,8], 20),([3,9], 20),([4,9], -20),([5,6], 40),([7,8], 4),([7,9], 4),([8,9], -16),([9,9], -16)]
def c2GroupHessian77_23 : Poly := List.flatten [c2GroupHessian77_23Chunk0]
theorem c2GroupHessian77_23_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian77_23 := by kernel_rfl
private def c2GroupHessian77_33Chunk0 : Poly := [([0,0], 56),([0,4], 40),([0,6], 80),([0,8], 32),([0,9], 32),([4,4], 40),([4,8], 40),([4,9], 40),([6,6], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c2GroupHessian77_33 : Poly := List.flatten [c2GroupHessian77_33Chunk0]
theorem c2GroupHessian77_33_check : sumFast (c2TensorGroup77.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian77_33 := by kernel_rfl
end D4.Secondary
