import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup224_det_check : c2TensorGroup224.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 285)) = true := by kernel_rfl
private def c2GroupHessian224_00Chunk0 : Poly := [([0,0], 56),([0,1], -16),([0,5], 40),([0,6], 80),([1,1], 16),([1,5], -40),([5,5], 40),([6,6], 40)]
def c2GroupHessian224_00 : Poly := List.flatten [c2GroupHessian224_00Chunk0]
theorem c2GroupHessian224_00_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian224_00 := by kernel_rfl
private def c2GroupHessian224_01Chunk0 : Poly := [([0,0], 56),([0,1], -8),([0,2], 4),([0,5], 20),([0,6], 40),([0,7], 20),([0,8], 40),([1,2], 4),([1,7], -20),([5,7], 40),([6,8], 40)]
def c2GroupHessian224_01 : Poly := List.flatten [c2GroupHessian224_01Chunk0]
theorem c2GroupHessian224_01_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian224_01 := by kernel_rfl
private def c2GroupHessian224_02Chunk0 : Poly := [([0,0], -24),([0,1], 24),([0,3], -8),([0,5], -60),([0,7], -20),([0,9], 40),([1,3], 16),([1,5], 20),([1,7], 20),([3,5], -20),([5,5], -40),([5,7], -40),([6,9], 40)]
def c2GroupHessian224_02 : Poly := List.flatten [c2GroupHessian224_02Chunk0]
theorem c2GroupHessian224_02_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian224_02 := by kernel_rfl
private def c2GroupHessian224_03Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -120),([0,8], -40),([0,9], -40),([4,6], -40),([6,6], -40),([6,8], -40),([6,9], -40)]
def c2GroupHessian224_03 : Poly := List.flatten [c2GroupHessian224_03Chunk0]
theorem c2GroupHessian224_03_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian224_03 := by kernel_rfl
private def c2GroupHessian224_11Chunk0 : Poly := [([0,0], 56),([0,2], 8),([0,7], 40),([0,8], 80),([2,2], 8),([7,7], 40),([8,8], 40)]
def c2GroupHessian224_11 : Poly := List.flatten [c2GroupHessian224_11Chunk0]
theorem c2GroupHessian224_11_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian224_11 := by kernel_rfl
private def c2GroupHessian224_12Chunk0 : Poly := [([0,0], -24),([0,3], -8),([0,5], -20),([0,7], -60),([0,9], 40),([2,3], 4),([3,7], -20),([5,7], -40),([7,7], -40),([8,9], 40)]
def c2GroupHessian224_12 : Poly := List.flatten [c2GroupHessian224_12Chunk0]
theorem c2GroupHessian224_12_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian224_12 := by kernel_rfl
private def c2GroupHessian224_13Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -40),([0,8], -120),([0,9], -40),([4,8], -40),([6,8], -40),([8,8], -40),([8,9], -40)]
def c2GroupHessian224_13 : Poly := List.flatten [c2GroupHessian224_13Chunk0]
theorem c2GroupHessian224_13_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian224_13 := by kernel_rfl
private def c2GroupHessian224_22Chunk0 : Poly := [([0,0], 48),([0,3], 48),([0,5], 80),([0,7], 80),([3,3], 16),([3,5], 40),([3,7], 40),([5,5], 40),([5,7], 80),([7,7], 40),([9,9], 40)]
def c2GroupHessian224_22 : Poly := List.flatten [c2GroupHessian224_22Chunk0]
theorem c2GroupHessian224_22_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian224_22 := by kernel_rfl
private def c2GroupHessian224_23Chunk0 : Poly := [([0,9], -80),([4,9], -40),([6,9], -40),([8,9], -40),([9,9], -40)]
def c2GroupHessian224_23 : Poly := List.flatten [c2GroupHessian224_23Chunk0]
theorem c2GroupHessian224_23_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian224_23 := by kernel_rfl
private def c2GroupHessian224_33Chunk0 : Poly := [([0,0], 160),([0,4], 160),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 40),([4,6], 80),([4,8], 80),([4,9], 80),([6,6], 40),([6,8], 80),([6,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian224_33 : Poly := List.flatten [c2GroupHessian224_33Chunk0]
theorem c2GroupHessian224_33_check : sumFast (c2TensorGroup224.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian224_33 := by kernel_rfl
end D4.Secondary
