import D4.CompactMomentData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.CompactMoments
open Certificate CertificateMoments

theorem inputs2_check : inputs2.flatten = momentC1 := by kernel_rfl

theorem substitution2_00 : substitute z2Substitution input2_00 = output2_00 := by kernel_rfl

theorem substitution2_01 : substitute z2Substitution input2_01 = output2_01 := by kernel_rfl

theorem substitution2_02 : substitute z2Substitution input2_02 = output2_02 := by kernel_rfl

theorem substitution2_03 : substitute z2Substitution input2_03 = output2_03 := by kernel_rfl

theorem substitution2_04 : substitute z2Substitution input2_04 = output2_04 := by kernel_rfl

theorem substitution2_05 : substitute z2Substitution input2_05 = output2_05 := by kernel_rfl

theorem substitution2_06 : substitute z2Substitution input2_06 = output2_06 := by kernel_rfl

theorem substitution2_07 : substitute z2Substitution input2_07 = output2_07 := by kernel_rfl

theorem substitution2_08 : substitute z2Substitution input2_08 = output2_08 := by kernel_rfl

theorem substitution2_09 : substitute z2Substitution input2_09 = output2_09 := by kernel_rfl

theorem substitution2_10 : substitute z2Substitution input2_10 = output2_10 := by kernel_rfl

theorem substitution2_11 : substitute z2Substitution input2_11 = output2_11 := by kernel_rfl

theorem substitution2_12 : substitute z2Substitution input2_12 = output2_12 := by kernel_rfl

theorem substitution2_13 : substitute z2Substitution input2_13 = output2_13 := by kernel_rfl

theorem substitution2_14 : substitute z2Substitution input2_14 = output2_14 := by kernel_rfl

theorem substitution2_15 : substitute z2Substitution input2_15 = output2_15 := by kernel_rfl

theorem substitution2_16 : substitute z2Substitution input2_16 = output2_16 := by kernel_rfl

theorem substitution2_17 : substitute z2Substitution input2_17 = output2_17 := by kernel_rfl

theorem substitution2_18 : substitute z2Substitution input2_18 = output2_18 := by kernel_rfl

theorem substitution2_19 : substitute z2Substitution input2_19 = output2_19 := by kernel_rfl

theorem substitution2_20 : substitute z2Substitution input2_20 = output2_20 := by kernel_rfl

theorem substitution2_21 : substitute z2Substitution input2_21 = output2_21 := by kernel_rfl

theorem substitution2_22 : substitute z2Substitution input2_22 = output2_22 := by kernel_rfl

theorem substitution2_chunks : inputs2.map (substitute z2Substitution) = outputs2 := by
  simp only [inputs2, outputs2, List.map_cons, List.map_nil, substitution2_00, substitution2_01, substitution2_02, substitution2_03, substitution2_04, substitution2_05, substitution2_06, substitution2_07, substitution2_08, substitution2_09, substitution2_10, substitution2_11, substitution2_12, substitution2_13, substitution2_14, substitution2_15, substitution2_16, substitution2_17, substitution2_18, substitution2_19, substitution2_20, substitution2_21, substitution2_22]

theorem compact2_check : sumFast [scale 5 (sumFast outputs2), correction2] = momentC2 := by kernel_rfl

theorem substituted2_eval (x : Nat → ℝ) :
    eval x (sumFast outputs2) = eval (z2 x) momentC1 := by
  simpa only [substitution2_chunks, inputs2_check] using
    eval_substitute_chunks x z2Substitution inputs2

end D4.CompactMoments
