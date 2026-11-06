import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup22_det_check : c2TensorGroup22.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 32)) = true := by kernel_rfl
private def c2GroupHessian22_00Chunk0 : Poly := [([0,0], 960),([0,1], 960),([0,5], 960),([1,1], 240),([1,5], 480),([5,5], 240),([6,6], 80)]
def c2GroupHessian22_00 : Poly := List.flatten [c2GroupHessian22_00Chunk0]
theorem c2GroupHessian22_00_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian22_00 := by kernel_rfl
private def c2GroupHessian22_01Chunk0 : Poly := [([0,0], 960),([0,1], 480),([0,2], 480),([0,5], 480),([0,7], 480),([1,2], 240),([1,7], 240),([2,5], 240),([5,7], 240)]
def c2GroupHessian22_01 : Poly := List.flatten [c2GroupHessian22_01Chunk0]
theorem c2GroupHessian22_01_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian22_01 := by kernel_rfl
private def c2GroupHessian22_02Chunk0 : Poly := [([0,0], -960),([0,1], -480),([0,5], -960),([0,7], -480),([0,9], -480),([1,5], -240),([1,7], -240),([1,9], -240),([5,5], -240),([5,7], -240),([5,9], -240)]
def c2GroupHessian22_02 : Poly := List.flatten [c2GroupHessian22_02Chunk0]
theorem c2GroupHessian22_02_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian22_02 := by kernel_rfl
private def c2GroupHessian22_03Chunk0 : Poly := [([0,4], 480),([0,9], 480),([1,4], 240),([1,9], 240),([4,5], 240),([5,9], 240),([6,6], -80)]
def c2GroupHessian22_03 : Poly := List.flatten [c2GroupHessian22_03Chunk0]
theorem c2GroupHessian22_03_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian22_03 := by kernel_rfl
private def c2GroupHessian22_11Chunk0 : Poly := [([0,0], 960),([0,2], 960),([0,7], 960),([2,2], 240),([2,7], 480),([7,7], 240),([8,8], 80)]
def c2GroupHessian22_11 : Poly := List.flatten [c2GroupHessian22_11Chunk0]
theorem c2GroupHessian22_11_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian22_11 := by kernel_rfl
private def c2GroupHessian22_12Chunk0 : Poly := [([0,0], -960),([0,2], -480),([0,5], -480),([0,7], -960),([0,9], -480),([2,5], -240),([2,7], -240),([2,9], -240),([5,7], -240),([7,7], -240),([7,9], -240)]
def c2GroupHessian22_12 : Poly := List.flatten [c2GroupHessian22_12Chunk0]
theorem c2GroupHessian22_12_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian22_12 := by kernel_rfl
private def c2GroupHessian22_13Chunk0 : Poly := [([0,4], 480),([0,9], 480),([2,4], 240),([2,9], 240),([4,7], 240),([7,9], 240),([8,8], -80)]
def c2GroupHessian22_13 : Poly := List.flatten [c2GroupHessian22_13Chunk0]
theorem c2GroupHessian22_13_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian22_13 := by kernel_rfl
private def c2GroupHessian22_22Chunk0 : Poly := [([0,0], 960),([0,5], 960),([0,7], 960),([0,9], 960),([3,3], 80),([5,5], 240),([5,7], 480),([5,9], 480),([7,7], 240),([7,9], 480),([9,9], 240)]
def c2GroupHessian22_22 : Poly := List.flatten [c2GroupHessian22_22Chunk0]
theorem c2GroupHessian22_22_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian22_22 := by kernel_rfl
private def c2GroupHessian22_23Chunk0 : Poly := [([0,4], -480),([0,9], -480),([4,5], -240),([4,7], -240),([4,9], -240),([5,9], -240),([7,9], -240),([9,9], -240)]
def c2GroupHessian22_23 : Poly := List.flatten [c2GroupHessian22_23Chunk0]
theorem c2GroupHessian22_23_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian22_23 := by kernel_rfl
private def c2GroupHessian22_33Chunk0 : Poly := [([4,4], 240),([4,9], 480),([6,6], 80),([8,8], 80),([9,9], 240)]
def c2GroupHessian22_33 : Poly := List.flatten [c2GroupHessian22_33Chunk0]
theorem c2GroupHessian22_33_check : sumFast (c2TensorGroup22.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian22_33 := by kernel_rfl
end D4.Secondary
