import D4.CompactMomentData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.CompactMoments
open Certificate CertificateMoments

theorem inputs3_check : inputs3.flatten = momentC2 := by kernel_rfl

theorem substitution3_00 : substitute thetaSubstitution input3_00 = output3_00 := by kernel_rfl

theorem substitution3_01 : substitute thetaSubstitution input3_01 = output3_01 := by kernel_rfl

theorem substitution3_02 : substitute thetaSubstitution input3_02 = output3_02 := by kernel_rfl

theorem substitution3_03 : substitute thetaSubstitution input3_03 = output3_03 := by kernel_rfl

theorem substitution3_04 : substitute thetaSubstitution input3_04 = output3_04 := by kernel_rfl

theorem substitution3_05 : substitute thetaSubstitution input3_05 = output3_05 := by kernel_rfl

theorem substitution3_06 : substitute thetaSubstitution input3_06 = output3_06 := by kernel_rfl

theorem substitution3_07 : substitute thetaSubstitution input3_07 = output3_07 := by kernel_rfl

theorem substitution3_08 : substitute thetaSubstitution input3_08 = output3_08 := by kernel_rfl

theorem substitution3_09 : substitute thetaSubstitution input3_09 = output3_09 := by kernel_rfl

theorem substitution3_10 : substitute thetaSubstitution input3_10 = output3_10 := by kernel_rfl

theorem substitution3_11 : substitute thetaSubstitution input3_11 = output3_11 := by kernel_rfl

theorem substitution3_12 : substitute thetaSubstitution input3_12 = output3_12 := by kernel_rfl

theorem substitution3_13 : substitute thetaSubstitution input3_13 = output3_13 := by kernel_rfl

theorem substitution3_14 : substitute thetaSubstitution input3_14 = output3_14 := by kernel_rfl

theorem substitution3_15 : substitute thetaSubstitution input3_15 = output3_15 := by kernel_rfl

theorem substitution3_16 : substitute thetaSubstitution input3_16 = output3_16 := by kernel_rfl

theorem substitution3_17 : substitute thetaSubstitution input3_17 = output3_17 := by kernel_rfl

theorem substitution3_18 : substitute thetaSubstitution input3_18 = output3_18 := by kernel_rfl

theorem substitution3_19 : substitute thetaSubstitution input3_19 = output3_19 := by kernel_rfl

theorem substitution3_20 : substitute thetaSubstitution input3_20 = output3_20 := by kernel_rfl

theorem substitution3_21 : substitute thetaSubstitution input3_21 = output3_21 := by kernel_rfl

theorem substitution3_22 : substitute thetaSubstitution input3_22 = output3_22 := by kernel_rfl

theorem substitution3_23 : substitute thetaSubstitution input3_23 = output3_23 := by kernel_rfl

theorem substitution3_24 : substitute thetaSubstitution input3_24 = output3_24 := by kernel_rfl

theorem substitution3_25 : substitute thetaSubstitution input3_25 = output3_25 := by kernel_rfl

theorem substitution3_26 : substitute thetaSubstitution input3_26 = output3_26 := by kernel_rfl

theorem substitution3_27 : substitute thetaSubstitution input3_27 = output3_27 := by kernel_rfl

theorem substitution3_28 : substitute thetaSubstitution input3_28 = output3_28 := by kernel_rfl

theorem substitution3_29 : substitute thetaSubstitution input3_29 = output3_29 := by kernel_rfl

theorem substitution3_30 : substitute thetaSubstitution input3_30 = output3_30 := by kernel_rfl

theorem substitution3_chunks : inputs3.map (substitute thetaSubstitution) = outputs3 := by
  simp only [inputs3, outputs3, List.map_cons, List.map_nil, substitution3_00, substitution3_01, substitution3_02, substitution3_03, substitution3_04, substitution3_05, substitution3_06, substitution3_07, substitution3_08, substitution3_09, substitution3_10, substitution3_11, substitution3_12, substitution3_13, substitution3_14, substitution3_15, substitution3_16, substitution3_17, substitution3_18, substitution3_19, substitution3_20, substitution3_21, substitution3_22, substitution3_23, substitution3_24, substitution3_25, substitution3_26, substitution3_27, substitution3_28, substitution3_29, substitution3_30]

theorem compact3_check : sumFast [sumFast outputs3, correction3] = momentC3 := by kernel_rfl

theorem substituted3_eval (x : Nat → ℝ) :
    eval x (sumFast outputs3) = eval (theta x) momentC2 := by
  simpa only [substitution3_chunks, inputs3_check] using
    eval_substitute_chunks x thetaSubstitution inputs3

end D4.CompactMoments
