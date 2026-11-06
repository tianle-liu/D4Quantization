import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup126_det_check : c2TensorGroup126.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 161)) = true := by kernel_rfl
private def c2GroupHessian126_00Chunk0 : Poly := [([0,0], 192),([0,1], 240),([0,6], 240),([1,1], 80),([1,6], 160),([5,5], 80),([6,6], 80)]
def c2GroupHessian126_00 : Poly := List.flatten [c2GroupHessian126_00Chunk0]
theorem c2GroupHessian126_00_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian126_00 := by kernel_rfl
private def c2GroupHessian126_01Chunk0 : Poly := [([0,0], 72),([0,1], 40),([0,5], -80),([0,6], 40),([0,7], -24),([1,7], -20),([2,5], -80),([5,8], -80),([6,7], -20)]
def c2GroupHessian126_01 : Poly := List.flatten [c2GroupHessian126_01Chunk0]
theorem c2GroupHessian126_01_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian126_01 := by kernel_rfl
private def c2GroupHessian126_02Chunk0 : Poly := [([0,0], -72),([0,1], -40),([0,5], -80),([0,6], -40),([0,7], 24),([1,7], 20),([3,5], -80),([5,5], -80),([5,9], -80),([6,7], 20)]
def c2GroupHessian126_02 : Poly := List.flatten [c2GroupHessian126_02Chunk0]
theorem c2GroupHessian126_02_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian126_02 := by kernel_rfl
private def c2GroupHessian126_03Chunk0 : Poly := [([0,0], -120),([0,1], -80),([0,4], -24),([0,5], 80),([0,6], -200),([1,4], -20),([1,6], -80),([4,6], -20),([5,8], 80),([5,9], 80),([6,6], -80)]
def c2GroupHessian126_03 : Poly := List.flatten [c2GroupHessian126_03Chunk0]
theorem c2GroupHessian126_03_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian126_03 := by kernel_rfl
private def c2GroupHessian126_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], -8),([0,8], 160),([2,2], 80),([2,8], 160),([7,7], 24),([8,8], 80)]
def c2GroupHessian126_11 : Poly := List.flatten [c2GroupHessian126_11Chunk0]
theorem c2GroupHessian126_11_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian126_11 := by kernel_rfl
private def c2GroupHessian126_12Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,3], 80),([0,5], 80),([0,7], 8),([0,8], 80),([0,9], 80),([2,3], 80),([2,5], 80),([2,9], 80),([3,8], 80),([5,8], 80),([7,7], -24),([8,9], 80)]
def c2GroupHessian126_12 : Poly := List.flatten [c2GroupHessian126_12Chunk0]
theorem c2GroupHessian126_12_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian126_12 := by kernel_rfl
private def c2GroupHessian126_13Chunk0 : Poly := [([0,0], -120),([0,2], -80),([0,4], -4),([0,6], -40),([0,7], 20),([0,8], -160),([0,9], -80),([2,8], -80),([2,9], -80),([4,7], 8),([6,7], 20),([8,8], -80),([8,9], -80)]
def c2GroupHessian126_13 : Poly := List.flatten [c2GroupHessian126_13Chunk0]
theorem c2GroupHessian126_13_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian126_13 := by kernel_rfl
private def c2GroupHessian126_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], 160),([0,7], -8),([0,9], 160),([3,3], 80),([3,5], 160),([3,9], 160),([5,5], 80),([5,9], 160),([7,7], 24),([9,9], 80)]
def c2GroupHessian126_22 : Poly := List.flatten [c2GroupHessian126_22Chunk0]
theorem c2GroupHessian126_22_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian126_22 := by kernel_rfl
private def c2GroupHessian126_23Chunk0 : Poly := [([0,0], -40),([0,3], -80),([0,4], 4),([0,5], -80),([0,6], 40),([0,7], -20),([0,8], -80),([0,9], -160),([3,8], -80),([3,9], -80),([4,7], -8),([5,8], -80),([5,9], -80),([6,7], -20),([8,9], -80),([9,9], -80)]
def c2GroupHessian126_23 : Poly := List.flatten [c2GroupHessian126_23Chunk0]
theorem c2GroupHessian126_23_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian126_23 := by kernel_rfl
private def c2GroupHessian126_33Chunk0 : Poly := [([0,0], 160),([0,4], 40),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 24),([4,6], 40),([6,6], 80),([8,8], 80),([8,9], 160),([9,9], 80)]
def c2GroupHessian126_33 : Poly := List.flatten [c2GroupHessian126_33Chunk0]
theorem c2GroupHessian126_33_check : sumFast (c2TensorGroup126.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian126_33 := by kernel_rfl
end D4.Secondary
