import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup71_det_check : c2TensorGroup71.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 95)) = true := by kernel_rfl
private def c2GroupHessian71_00Chunk0 : Poly := [([0,0], 320),([0,1], 320),([0,5], 320),([0,6], 320),([1,1], 80),([1,5], 160),([1,6], 160),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian71_00 : Poly := List.flatten [c2GroupHessian71_00Chunk0]
theorem c2GroupHessian71_00_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian71_00 := by kernel_rfl
private def c2GroupHessian71_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,5], 80),([0,6], 80)]
def c2GroupHessian71_01 : Poly := List.flatten [c2GroupHessian71_01Chunk0]
theorem c2GroupHessian71_01_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian71_01 := by kernel_rfl
private def c2GroupHessian71_02Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -240),([0,6], -80),([1,5], -80),([5,5], -80),([5,6], -80)]
def c2GroupHessian71_02 : Poly := List.flatten [c2GroupHessian71_02Chunk0]
theorem c2GroupHessian71_02_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian71_02 := by kernel_rfl
private def c2GroupHessian71_03Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -80),([0,6], -240),([1,6], -80),([5,6], -80),([6,6], -80)]
def c2GroupHessian71_03 : Poly := List.flatten [c2GroupHessian71_03Chunk0]
theorem c2GroupHessian71_03_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian71_03 := by kernel_rfl
private def c2GroupHessian71_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 40),([2,2], 80),([2,7], 160),([2,8], 40),([7,7], 80),([7,8], 40),([8,8], 24)]
def c2GroupHessian71_11 : Poly := List.flatten [c2GroupHessian71_11Chunk0]
theorem c2GroupHessian71_11_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian71_11 := by kernel_rfl
private def c2GroupHessian71_12Chunk0 : Poly := [([0,0], -120),([0,2], -40),([0,3], 20),([0,5], -80),([0,7], -120),([0,8], -4),([0,9], -40),([2,3], 20),([2,7], -80),([2,9], -40),([3,7], 20),([3,8], 8),([7,7], -80),([7,8], -20),([7,9], -40),([8,9], -4)]
def c2GroupHessian71_12 : Poly := List.flatten [c2GroupHessian71_12Chunk0]
theorem c2GroupHessian71_12_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian71_12 := by kernel_rfl
private def c2GroupHessian71_13Chunk0 : Poly := [([0,0], -40),([0,2], 40),([0,4], 80),([0,6], -80),([0,7], 40),([0,8], -16),([0,9], 40),([2,4], 80),([2,8], -20),([2,9], 40),([4,7], 80),([4,8], 20),([7,8], -20),([7,9], 40),([8,8], -24),([8,9], 4)]
def c2GroupHessian71_13 : Poly := List.flatten [c2GroupHessian71_13Chunk0]
theorem c2GroupHessian71_13_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian71_13 := by kernel_rfl
private def c2GroupHessian71_22Chunk0 : Poly := [([0,0], 112),([0,3], -8),([0,5], 160),([0,7], 80),([0,9], 64),([3,3], 24),([3,7], -40),([3,9], -8),([5,5], 80),([7,7], 80),([7,9], 80),([9,9], 32)]
def c2GroupHessian71_22 : Poly := List.flatten [c2GroupHessian71_22Chunk0]
theorem c2GroupHessian71_22_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian71_22 := by kernel_rfl
private def c2GroupHessian71_23Chunk0 : Poly := [([0,0], 48),([0,3], 4),([0,4], -40),([0,5], 80),([0,6], 80),([0,7], -40),([0,8], 4),([0,9], -64),([3,4], 20),([3,8], -8),([3,9], 4),([4,7], -80),([4,9], -40),([5,6], 80),([7,8], 20),([7,9], -40),([8,9], 4),([9,9], -32)]
def c2GroupHessian71_23 : Poly := List.flatten [c2GroupHessian71_23Chunk0]
theorem c2GroupHessian71_23_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian71_23 := by kernel_rfl
private def c2GroupHessian71_33Chunk0 : Poly := [([0,0], 112),([0,4], 80),([0,6], 160),([0,8], -8),([0,9], 64),([4,4], 80),([4,8], -40),([4,9], 80),([6,6], 80),([8,8], 24),([8,9], -8),([9,9], 32)]
def c2GroupHessian71_33 : Poly := List.flatten [c2GroupHessian71_33Chunk0]
theorem c2GroupHessian71_33_check : sumFast (c2TensorGroup71.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian71_33 := by kernel_rfl
end D4.Secondary
