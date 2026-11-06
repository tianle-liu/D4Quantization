import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup103_det_check : c3TensorGroup103.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 134)) = true := by kernel_rfl
private def c3GroupHessian103_00Chunk0 : Poly := [([0,0], 152),([0,1], 240),([0,5], 240),([0,6], 240),([0,9], 64),([1,1], 120),([1,5], 240),([1,6], 240),([5,5], 120),([5,6], 240),([6,6], 120),([9,9], 32)]
def c3GroupHessian103_00 : Poly := List.flatten [c3GroupHessian103_00Chunk0]
theorem c3GroupHessian103_00_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian103_00 := by kernel_rfl
private def c3GroupHessian103_01Chunk0 : Poly := [([0,0], -88),([0,1], -120),([0,2], -120),([0,5], -120),([0,6], -120),([0,7], -120),([0,8], -120),([0,9], 64),([1,2], -120),([1,7], -120),([1,8], -120),([2,5], -120),([2,6], -120),([5,7], -120),([5,8], -120),([6,7], -120),([6,8], -120),([9,9], 32)]
def c3GroupHessian103_01 : Poly := List.flatten [c3GroupHessian103_01Chunk0]
theorem c3GroupHessian103_01_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian103_01 := by kernel_rfl
private def c3GroupHessian103_02Chunk0 : Poly := [([0,0], -20),([0,3], 12),([0,5], -120),([0,7], 120),([0,9], -52),([1,5], -120),([1,7], 120),([3,9], 12),([5,5], -120),([5,6], -120),([5,7], 120),([6,7], 120),([9,9], -32)]
def c3GroupHessian103_02 : Poly := List.flatten [c3GroupHessian103_02Chunk0]
theorem c3GroupHessian103_02_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian103_02 := by kernel_rfl
private def c3GroupHessian103_03Chunk0 : Poly := [([0,0], -20),([0,6], -120),([0,8], 120),([0,9], -52),([1,6], -120),([1,8], 120),([5,6], -120),([5,8], 120),([6,6], -120),([6,8], 120),([9,9], -32)]
def c3GroupHessian103_03 : Poly := List.flatten [c3GroupHessian103_03Chunk0]
theorem c3GroupHessian103_03_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian103_03 := by kernel_rfl
private def c3GroupHessian103_11Chunk0 : Poly := [([0,0], 152),([0,2], 240),([0,7], 240),([0,8], 240),([0,9], 64),([2,2], 120),([2,7], 240),([2,8], 240),([7,7], 120),([7,8], 240),([8,8], 120),([9,9], 32)]
def c3GroupHessian103_11 : Poly := List.flatten [c3GroupHessian103_11Chunk0]
theorem c3GroupHessian103_11_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian103_11 := by kernel_rfl
private def c3GroupHessian103_12Chunk0 : Poly := [([0,0], -20),([0,3], 12),([0,5], 120),([0,7], -120),([0,9], -52),([2,5], 120),([2,7], -120),([3,9], 12),([5,7], 120),([5,8], 120),([7,7], -120),([7,8], -120),([9,9], -32)]
def c3GroupHessian103_12 : Poly := List.flatten [c3GroupHessian103_12Chunk0]
theorem c3GroupHessian103_12_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian103_12 := by kernel_rfl
private def c3GroupHessian103_13Chunk0 : Poly := [([0,0], -20),([0,6], 120),([0,8], -120),([0,9], -52),([2,6], 120),([2,8], -120),([6,7], 120),([6,8], 120),([7,8], -120),([8,8], -120),([9,9], -32)]
def c3GroupHessian103_13 : Poly := List.flatten [c3GroupHessian103_13Chunk0]
theorem c3GroupHessian103_13_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian103_13 := by kernel_rfl
private def c3GroupHessian103_22Chunk0 : Poly := [([0,0], 48),([0,3], 56),([0,9], 40),([3,3], 40),([3,9], -24),([5,5], 120),([5,7], -240),([7,7], 120),([9,9], 32)]
def c3GroupHessian103_22 : Poly := List.flatten [c3GroupHessian103_22Chunk0]
theorem c3GroupHessian103_22_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian103_22 := by kernel_rfl
private def c3GroupHessian103_23Chunk0 : Poly := [([0,0], -8),([0,3], -28),([0,4], -12),([0,9], 40),([3,4], -12),([3,9], -12),([5,6], 120),([5,8], -120),([6,7], -120),([7,8], 120),([9,9], 32)]
def c3GroupHessian103_23 : Poly := List.flatten [c3GroupHessian103_23Chunk0]
theorem c3GroupHessian103_23_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian103_23 := by kernel_rfl
private def c3GroupHessian103_33Chunk0 : Poly := [([0,0], 48),([0,4], 72),([0,9], 40),([4,4], 48),([6,6], 120),([6,8], -240),([8,8], 120),([9,9], 32)]
def c3GroupHessian103_33 : Poly := List.flatten [c3GroupHessian103_33Chunk0]
theorem c3GroupHessian103_33_check : sumFast (c3TensorGroup103.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian103_33 := by kernel_rfl
end D4.Secondary
