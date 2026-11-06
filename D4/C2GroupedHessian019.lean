import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup19_det_check : c2TensorGroup19.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 22)) = true := by kernel_rfl
private def c2GroupHessian19_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], 64),([0,6], -8),([1,1], 80),([5,5], 32),([5,6], -8),([6,6], 24)]
def c2GroupHessian19_00 : Poly := List.flatten [c2GroupHessian19_00Chunk0]
theorem c2GroupHessian19_00_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian19_00 := by kernel_rfl
private def c2GroupHessian19_01Chunk0 : Poly := [([0,0], 112),([0,1], 80),([0,2], 80),([0,5], 32),([0,6], -4),([0,7], 32),([0,8], -4),([1,2], 80),([5,7], 32),([5,8], -4),([6,7], -4),([6,8], 8)]
def c2GroupHessian19_01 : Poly := List.flatten [c2GroupHessian19_01Chunk0]
theorem c2GroupHessian19_01_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian19_01 := by kernel_rfl
private def c2GroupHessian19_02Chunk0 : Poly := [([0,0], -72),([0,3], 80),([0,5], -104),([0,6], 24),([0,7], -32),([0,9], -40),([1,3], 80),([5,5], -32),([5,6], 4),([5,7], -32),([5,9], -40),([6,7], 4),([6,9], 20)]
def c2GroupHessian19_02 : Poly := List.flatten [c2GroupHessian19_02Chunk0]
theorem c2GroupHessian19_02_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian19_02 := by kernel_rfl
private def c2GroupHessian19_03Chunk0 : Poly := [([0,0], 8),([0,4], 80),([0,5], 8),([0,6], -12),([0,8], 4),([0,9], 40),([1,4], 80),([5,6], 4),([5,8], 4),([5,9], 40),([6,6], -24),([6,8], -8),([6,9], -20)]
def c2GroupHessian19_03 : Poly := List.flatten [c2GroupHessian19_03Chunk0]
theorem c2GroupHessian19_03_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian19_03 := by kernel_rfl
private def c2GroupHessian19_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], 64),([0,8], -8),([2,2], 80),([7,7], 32),([7,8], -8),([8,8], 24)]
def c2GroupHessian19_11 : Poly := List.flatten [c2GroupHessian19_11Chunk0]
theorem c2GroupHessian19_11_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian19_11 := by kernel_rfl
private def c2GroupHessian19_12Chunk0 : Poly := [([0,0], -72),([0,3], 80),([0,5], -32),([0,7], -104),([0,8], 24),([0,9], -40),([2,3], 80),([5,7], -32),([5,8], 4),([7,7], -32),([7,8], 4),([7,9], -40),([8,9], 20)]
def c2GroupHessian19_12 : Poly := List.flatten [c2GroupHessian19_12Chunk0]
theorem c2GroupHessian19_12_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian19_12 := by kernel_rfl
private def c2GroupHessian19_13Chunk0 : Poly := [([0,0], 8),([0,4], 80),([0,6], 4),([0,7], 8),([0,8], -12),([0,9], 40),([2,4], 80),([6,7], 4),([6,8], -8),([7,8], 4),([7,9], 40),([8,8], -24),([8,9], -20)]
def c2GroupHessian19_13 : Poly := List.flatten [c2GroupHessian19_13Chunk0]
theorem c2GroupHessian19_13_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian19_13 := by kernel_rfl
private def c2GroupHessian19_22Chunk0 : Poly := [([0,0], 192),([0,5], 144),([0,7], 144),([0,9], 240),([3,3], 80),([5,5], 32),([5,7], 64),([5,9], 80),([7,7], 32),([7,9], 80),([9,9], 80)]
def c2GroupHessian19_22 : Poly := List.flatten [c2GroupHessian19_22Chunk0]
theorem c2GroupHessian19_22_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian19_22 := by kernel_rfl
private def c2GroupHessian19_23Chunk0 : Poly := [([0,0], -48),([0,5], -8),([0,6], -24),([0,7], -8),([0,8], -24),([0,9], -160),([3,4], 80),([5,6], -4),([5,8], -4),([5,9], -40),([6,7], -4),([6,9], -20),([7,8], -4),([7,9], -40),([8,9], -20),([9,9], -80)]
def c2GroupHessian19_23 : Poly := List.flatten [c2GroupHessian19_23Chunk0]
theorem c2GroupHessian19_23_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian19_23 := by kernel_rfl
private def c2GroupHessian19_33Chunk0 : Poly := [([0,0], 32),([0,6], 32),([0,8], 32),([0,9], 80),([4,4], 80),([6,6], 24),([6,8], 16),([6,9], 40),([8,8], 24),([8,9], 40),([9,9], 80)]
def c2GroupHessian19_33 : Poly := List.flatten [c2GroupHessian19_33Chunk0]
theorem c2GroupHessian19_33_check : sumFast (c2TensorGroup19.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian19_33 := by kernel_rfl
end D4.Secondary
