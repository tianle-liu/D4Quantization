import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup179_det_check : c2TensorGroup179.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 224)) = true := by kernel_rfl
private def c2GroupHessian179_00Chunk0 : Poly := [([0,0], 112),([0,1], 64),([0,5], 64),([0,6], -8),([1,1], 32),([1,5], 64),([1,6], -8),([5,5], 32),([5,6], -8),([6,6], 24)]
def c2GroupHessian179_00 : Poly := List.flatten [c2GroupHessian179_00Chunk0]
theorem c2GroupHessian179_00_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian179_00 := by kernel_rfl
private def c2GroupHessian179_01Chunk0 : Poly := [([0,0], 160),([0,2], 80),([0,7], 80),([0,8], 80)]
def c2GroupHessian179_01 : Poly := List.flatten [c2GroupHessian179_01Chunk0]
theorem c2GroupHessian179_01_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian179_01 := by kernel_rfl
private def c2GroupHessian179_02Chunk0 : Poly := [([0,0], -120),([0,1], -40),([0,3], -4),([0,5], -72),([0,6], 20),([0,7], -80),([0,9], -40),([1,3], -4),([1,5], -32),([1,9], -40),([3,5], -4),([3,6], 8),([5,5], -32),([5,6], 4),([5,9], -40),([6,9], 20)]
def c2GroupHessian179_02 : Poly := List.flatten [c2GroupHessian179_02Chunk0]
theorem c2GroupHessian179_02_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian179_02 := by kernel_rfl
private def c2GroupHessian179_03Chunk0 : Poly := [([0,0], -40),([0,1], 40),([0,4], 32),([0,5], 40),([0,6], -16),([0,8], -80),([0,9], 40),([1,4], 32),([1,6], 4),([1,9], 40),([4,5], 32),([4,6], -4),([5,6], 4),([5,9], 40),([6,6], -24),([6,9], -20)]
def c2GroupHessian179_03 : Poly := List.flatten [c2GroupHessian179_03Chunk0]
theorem c2GroupHessian179_03_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian179_03 := by kernel_rfl
private def c2GroupHessian179_11Chunk0 : Poly := [([0,0], 320),([0,2], 320),([0,7], 320),([0,8], 320),([2,2], 80),([2,7], 160),([2,8], 160),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian179_11 : Poly := List.flatten [c2GroupHessian179_11Chunk0]
theorem c2GroupHessian179_11_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian179_11 := by kernel_rfl
private def c2GroupHessian179_12Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -240),([0,8], -80),([2,7], -80),([7,7], -80),([7,8], -80)]
def c2GroupHessian179_12 : Poly := List.flatten [c2GroupHessian179_12Chunk0]
theorem c2GroupHessian179_12_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian179_12 := by kernel_rfl
private def c2GroupHessian179_13Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -80),([0,8], -240),([2,8], -80),([7,8], -80),([8,8], -80)]
def c2GroupHessian179_13 : Poly := List.flatten [c2GroupHessian179_13Chunk0]
theorem c2GroupHessian179_13_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian179_13 := by kernel_rfl
private def c2GroupHessian179_22Chunk0 : Poly := [([0,0], 160),([0,3], 40),([0,5], 80),([0,7], 160),([0,9], 160),([3,3], 24),([3,5], 8),([3,9], 40),([5,5], 32),([5,9], 80),([7,7], 80),([9,9], 80)]
def c2GroupHessian179_22 : Poly := List.flatten [c2GroupHessian179_22Chunk0]
theorem c2GroupHessian179_22_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian179_22 := by kernel_rfl
private def c2GroupHessian179_23Chunk0 : Poly := [([0,3], -20),([0,4], -40),([0,5], -40),([0,6], -20),([0,7], 80),([0,8], 80),([0,9], -160),([3,4], -4),([3,6], -8),([3,9], -20),([4,5], -32),([4,9], -40),([5,6], -4),([5,9], -40),([6,9], -20),([7,8], 80),([9,9], -80)]
def c2GroupHessian179_23 : Poly := List.flatten [c2GroupHessian179_23Chunk0]
theorem c2GroupHessian179_23_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian179_23 := by kernel_rfl
private def c2GroupHessian179_33Chunk0 : Poly := [([0,0], 160),([0,4], 80),([0,6], 40),([0,8], 160),([0,9], 160),([4,4], 32),([4,6], 8),([4,9], 80),([6,6], 24),([6,9], 40),([8,8], 80),([9,9], 80)]
def c2GroupHessian179_33 : Poly := List.flatten [c2GroupHessian179_33Chunk0]
theorem c2GroupHessian179_33_check : sumFast (c2TensorGroup179.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian179_33 := by kernel_rfl
end D4.Secondary
