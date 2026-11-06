import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup151_det_check : c2TensorGroup151.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 190)) = true := by kernel_rfl
private def c2GroupHessian151_00Chunk0 : Poly := [([0,0], 48),([0,1], 16),([0,5], 80),([1,1], 8),([5,5], 40),([6,6], 40)]
def c2GroupHessian151_00 : Poly := List.flatten [c2GroupHessian151_00Chunk0]
theorem c2GroupHessian151_00_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian151_00 := by kernel_rfl
private def c2GroupHessian151_01Chunk0 : Poly := [([0,0], 24),([0,1], 4),([0,5], 20),([0,6], -40),([0,8], 24),([1,8], 4),([2,6], -40),([5,8], 20),([6,7], -40)]
def c2GroupHessian151_01 : Poly := List.flatten [c2GroupHessian151_01Chunk0]
theorem c2GroupHessian151_01_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian151_01 := by kernel_rfl
private def c2GroupHessian151_02Chunk0 : Poly := [([0,0], -40),([0,3], -16),([0,5], -80),([0,6], 40),([1,3], 4),([3,5], -20),([5,5], -40),([6,7], 40),([6,9], 40)]
def c2GroupHessian151_02 : Poly := List.flatten [c2GroupHessian151_02Chunk0]
theorem c2GroupHessian151_02_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian151_02 := by kernel_rfl
private def c2GroupHessian151_03Chunk0 : Poly := [([0,0], -24),([0,1], -4),([0,5], -20),([0,6], -40),([0,8], -24),([1,8], -4),([4,6], -40),([5,8], -20),([6,6], -40),([6,9], -40)]
def c2GroupHessian151_03 : Poly := List.flatten [c2GroupHessian151_03Chunk0]
theorem c2GroupHessian151_03_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian151_03 := by kernel_rfl
private def c2GroupHessian151_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 32),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16)]
def c2GroupHessian151_11 : Poly := List.flatten [c2GroupHessian151_11Chunk0]
theorem c2GroupHessian151_11_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian151_11 := by kernel_rfl
private def c2GroupHessian151_12Chunk0 : Poly := [([0,0], -60),([0,2], -40),([0,3], -8),([0,5], -20),([0,7], -80),([0,8], -20),([0,9], -40),([2,7], -40),([2,9], -40),([3,8], -8),([5,8], -20),([7,7], -40),([7,9], -40)]
def c2GroupHessian151_12 : Poly := List.flatten [c2GroupHessian151_12Chunk0]
theorem c2GroupHessian151_12_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian151_12 := by kernel_rfl
private def c2GroupHessian151_13Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -32),([0,9], 40),([2,4], 40),([2,6], 40),([2,9], 40),([4,7], 40),([6,7], 40),([7,9], 40),([8,8], -16)]
def c2GroupHessian151_13 : Poly := List.flatten [c2GroupHessian151_13Chunk0]
theorem c2GroupHessian151_13_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian151_13 := by kernel_rfl
private def c2GroupHessian151_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,7], 80),([0,9], 80),([3,3], 16),([3,5], 40),([5,5], 40),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian151_22 : Poly := List.flatten [c2GroupHessian151_22Chunk0]
theorem c2GroupHessian151_22_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian151_22 := by kernel_rfl
private def c2GroupHessian151_23Chunk0 : Poly := [([0,0], -20),([0,3], 8),([0,4], -40),([0,5], 20),([0,6], -40),([0,7], -40),([0,8], 20),([0,9], -80),([3,8], 8),([4,7], -40),([4,9], -40),([5,8], 20),([6,7], -40),([6,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian151_23 : Poly := List.flatten [c2GroupHessian151_23Chunk0]
theorem c2GroupHessian151_23_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian151_23 := by kernel_rfl
private def c2GroupHessian151_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 32),([0,9], 80),([4,4], 40),([4,6], 80),([4,9], 80),([6,6], 40),([6,9], 80),([8,8], 16),([9,9], 40)]
def c2GroupHessian151_33 : Poly := List.flatten [c2GroupHessian151_33Chunk0]
theorem c2GroupHessian151_33_check : sumFast (c2TensorGroup151.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian151_33 := by kernel_rfl
end D4.Secondary
