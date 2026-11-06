import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup168_det_check : c2TensorGroup168.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 212)) = true := by kernel_rfl
private def c2GroupHessian168_00Chunk0 : Poly := [([0,0], 48),([0,1], 16),([0,5], 16),([1,1], 8),([1,5], 16),([5,5], 8),([6,6], 40)]
def c2GroupHessian168_00 : Poly := List.flatten [c2GroupHessian168_00Chunk0]
theorem c2GroupHessian168_00_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian168_00 := by kernel_rfl
private def c2GroupHessian168_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40)]
def c2GroupHessian168_01 : Poly := List.flatten [c2GroupHessian168_01Chunk0]
theorem c2GroupHessian168_01_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian168_01 := by kernel_rfl
private def c2GroupHessian168_02Chunk0 : Poly := [([0,0], -40),([0,3], 4),([0,5], -8),([0,6], 40),([0,7], -40),([1,3], 4),([1,5], -8),([3,5], 4),([3,6], 20),([5,5], -8),([6,9], 40)]
def c2GroupHessian168_02 : Poly := List.flatten [c2GroupHessian168_02Chunk0]
theorem c2GroupHessian168_02_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian168_02 := by kernel_rfl
private def c2GroupHessian168_03Chunk0 : Poly := [([0,0], -40),([0,4], 4),([0,6], -40),([0,8], -40),([1,4], 4),([4,5], 4),([4,6], -20),([6,6], -40),([6,9], -40)]
def c2GroupHessian168_03 : Poly := List.flatten [c2GroupHessian168_03Chunk0]
theorem c2GroupHessian168_03_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian168_03 := by kernel_rfl
private def c2GroupHessian168_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian168_11 : Poly := List.flatten [c2GroupHessian168_11Chunk0]
theorem c2GroupHessian168_11_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian168_11 := by kernel_rfl
private def c2GroupHessian168_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([2,7], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian168_12 : Poly := List.flatten [c2GroupHessian168_12Chunk0]
theorem c2GroupHessian168_12_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian168_12 := by kernel_rfl
private def c2GroupHessian168_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([2,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian168_13 : Poly := List.flatten [c2GroupHessian168_13Chunk0]
theorem c2GroupHessian168_13_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian168_13 := by kernel_rfl
private def c2GroupHessian168_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,7], 80),([0,9], 80),([3,3], 16),([3,5], -8),([3,9], 40),([5,5], 8),([7,7], 40),([9,9], 40)]
def c2GroupHessian168_22 : Poly := List.flatten [c2GroupHessian168_22Chunk0]
theorem c2GroupHessian168_22_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian168_22 := by kernel_rfl
private def c2GroupHessian168_23Chunk0 : Poly := [([0,3], -20),([0,4], -20),([0,6], -40),([0,7], 40),([0,8], 40),([0,9], -80),([3,4], -8),([3,6], -20),([3,9], -20),([4,5], -4),([4,9], -20),([6,9], -40),([7,8], 40),([9,9], -40)]
def c2GroupHessian168_23 : Poly := List.flatten [c2GroupHessian168_23Chunk0]
theorem c2GroupHessian168_23_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian168_23 := by kernel_rfl
private def c2GroupHessian168_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,6], 40),([4,9], 40),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c2GroupHessian168_33 : Poly := List.flatten [c2GroupHessian168_33Chunk0]
theorem c2GroupHessian168_33_check : sumFast (c2TensorGroup168.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian168_33 := by kernel_rfl
end D4.Secondary
