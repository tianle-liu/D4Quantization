import D4.DelaunayData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.Delaunay

theorem unimodular3_check : unimodularCheck cells3=true := by kernel_rfl

theorem occurrences3_check : occurrenceCheck facets3=true := by kernel_rfl

theorem facets3_0_check : ([0,1,2,3,4,5,6,7,8,9] : List (Fin 60)).all (fun i => facetCheck cells3 generators3 (facets3 i))=true := by kernel_rfl

theorem facets3_1_check : ([10,11,12,13,14,15,16,17,18,19] : List (Fin 60)).all (fun i => facetCheck cells3 generators3 (facets3 i))=true := by kernel_rfl

theorem facets3_2_check : ([20,21,22,23,24,25,26,27,28,29] : List (Fin 60)).all (fun i => facetCheck cells3 generators3 (facets3 i))=true := by kernel_rfl

theorem facets3_3_check : ([30,31,32,33,34,35,36,37,38,39] : List (Fin 60)).all (fun i => facetCheck cells3 generators3 (facets3 i))=true := by kernel_rfl

theorem facets3_4_check : ([40,41,42,43,44,45,46,47,48,49] : List (Fin 60)).all (fun i => facetCheck cells3 generators3 (facets3 i))=true := by kernel_rfl

theorem facets3_5_check : ([50,51,52,53,54,55,56,57,58,59] : List (Fin 60)).all (fun i => facetCheck cells3 generators3 (facets3 i))=true := by kernel_rfl

theorem all_facets3_check : (List.finRange 60).all (fun i => facetCheck cells3 generators3 (facets3 i))=true := by
  have hindices : List.finRange 60 = [0,1,2,3,4,5,6,7,8,9] ++ [10,11,12,13,14,15,16,17,18,19] ++ [20,21,22,23,24,25,26,27,28,29] ++ [30,31,32,33,34,35,36,37,38,39] ++ [40,41,42,43,44,45,46,47,48,49] ++ [50,51,52,53,54,55,56,57,58,59] := by kernel_rfl
  rw [hindices]
  simp only [List.all_append, facets3_0_check, facets3_1_check, facets3_2_check, facets3_3_check, facets3_4_check, facets3_5_check, Bool.and_self]

end D4.Delaunay
