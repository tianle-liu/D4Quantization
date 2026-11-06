import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup73_det_check : c2TensorGroup73.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 99)) = true := by kernel_rfl
private def c2GroupHessian73_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian73_00 : Poly := List.flatten [c2GroupHessian73_00Chunk0]
theorem c2GroupHessian73_00_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian73_00 := by kernel_rfl
private def c2GroupHessian73_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian73_01 : Poly := List.flatten [c2GroupHessian73_01Chunk0]
theorem c2GroupHessian73_01_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian73_01 := by kernel_rfl
private def c2GroupHessian73_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian73_02 : Poly := List.flatten [c2GroupHessian73_02Chunk0]
theorem c2GroupHessian73_02_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian73_02 := by kernel_rfl
private def c2GroupHessian73_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian73_03 : Poly := List.flatten [c2GroupHessian73_03Chunk0]
theorem c2GroupHessian73_03_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian73_03 := by kernel_rfl
private def c2GroupHessian73_11Chunk0 : Poly := [([0,0], 48),([0,2], 8),([0,7], 8),([0,8], 16),([2,2], 16),([2,7], -16),([2,8], 8),([7,7], 16),([7,8], 8),([8,8], 8)]
def c2GroupHessian73_11 : Poly := List.flatten [c2GroupHessian73_11Chunk0]
theorem c2GroupHessian73_11_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian73_11 := by kernel_rfl
private def c2GroupHessian73_12Chunk0 : Poly := [([0,0], -40),([0,2], 20),([0,5], -40),([0,7], -24),([2,3], 20),([2,7], 8),([2,9], 20),([3,7], -20),([7,7], -16),([7,8], -4),([7,9], -20)]
def c2GroupHessian73_12 : Poly := List.flatten [c2GroupHessian73_12Chunk0]
theorem c2GroupHessian73_12_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian73_12 := by kernel_rfl
private def c2GroupHessian73_13Chunk0 : Poly := [([0,0], -48),([0,2], -4),([0,6], -40),([0,7], -4),([0,8], -16),([2,4], 20),([2,8], -4),([2,9], -20),([4,7], -20),([7,8], -4),([7,9], 20),([8,8], -8)]
def c2GroupHessian73_13 : Poly := List.flatten [c2GroupHessian73_13Chunk0]
theorem c2GroupHessian73_13_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian73_13 := by kernel_rfl
private def c2GroupHessian73_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], 80),([3,3], 40),([3,7], 40),([3,9], 80),([5,5], 40),([7,7], 16),([7,9], 40),([9,9], 40)]
def c2GroupHessian73_22 : Poly := List.flatten [c2GroupHessian73_22Chunk0]
theorem c2GroupHessian73_22_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian73_22 := by kernel_rfl
private def c2GroupHessian73_23Chunk0 : Poly := [([0,0], 40),([0,4], 40),([0,5], 40),([0,6], 40),([0,7], 4),([0,9], -40),([3,4], 40),([3,9], -40),([4,7], 20),([4,9], 40),([5,6], 40),([7,8], 4),([7,9], -20),([9,9], -40)]
def c2GroupHessian73_23 : Poly := List.flatten [c2GroupHessian73_23Chunk0]
theorem c2GroupHessian73_23_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian73_23 := by kernel_rfl
private def c2GroupHessian73_33Chunk0 : Poly := [([0,0], 48),([0,6], 80),([0,8], 16),([4,4], 40),([4,9], -80),([6,6], 40),([8,8], 8),([9,9], 40)]
def c2GroupHessian73_33 : Poly := List.flatten [c2GroupHessian73_33Chunk0]
theorem c2GroupHessian73_33_check : sumFast (c2TensorGroup73.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian73_33 := by kernel_rfl
end D4.Secondary
