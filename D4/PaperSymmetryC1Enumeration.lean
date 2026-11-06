import D4.PaperSymmetryC1
import D4.KernelCompute
set_option maxRecDepth 1000000
namespace D4.PaperSymmetry.C1
def v0 : Equiv.Perm (Fin 5) := ⟨![0,1,2,3,4],![0,1,2,3,4],by decide +kernel,by decide +kernel⟩
def v1 : Equiv.Perm (Fin 5) := ⟨![0,1,2,4,3],![0,1,2,4,3],by decide +kernel,by decide +kernel⟩
def v2 : Equiv.Perm (Fin 5) := ⟨![0,1,3,2,4],![0,1,3,2,4],by decide +kernel,by decide +kernel⟩
def v3 : Equiv.Perm (Fin 5) := ⟨![0,1,3,4,2],![0,1,4,2,3],by decide +kernel,by decide +kernel⟩
def v4 : Equiv.Perm (Fin 5) := ⟨![0,1,4,2,3],![0,1,3,4,2],by decide +kernel,by decide +kernel⟩
def v5 : Equiv.Perm (Fin 5) := ⟨![0,1,4,3,2],![0,1,4,3,2],by decide +kernel,by decide +kernel⟩
def v6 : Equiv.Perm (Fin 5) := ⟨![0,2,1,3,4],![0,2,1,3,4],by decide +kernel,by decide +kernel⟩
def v7 : Equiv.Perm (Fin 5) := ⟨![0,2,1,4,3],![0,2,1,4,3],by decide +kernel,by decide +kernel⟩
def v8 : Equiv.Perm (Fin 5) := ⟨![0,2,3,1,4],![0,3,1,2,4],by decide +kernel,by decide +kernel⟩
def v9 : Equiv.Perm (Fin 5) := ⟨![0,2,3,4,1],![0,4,1,2,3],by decide +kernel,by decide +kernel⟩
def v10 : Equiv.Perm (Fin 5) := ⟨![0,2,4,1,3],![0,3,1,4,2],by decide +kernel,by decide +kernel⟩
def v11 : Equiv.Perm (Fin 5) := ⟨![0,2,4,3,1],![0,4,1,3,2],by decide +kernel,by decide +kernel⟩
def v12 : Equiv.Perm (Fin 5) := ⟨![0,3,1,2,4],![0,2,3,1,4],by decide +kernel,by decide +kernel⟩
def v13 : Equiv.Perm (Fin 5) := ⟨![0,3,1,4,2],![0,2,4,1,3],by decide +kernel,by decide +kernel⟩
def v14 : Equiv.Perm (Fin 5) := ⟨![0,3,2,1,4],![0,3,2,1,4],by decide +kernel,by decide +kernel⟩
def v15 : Equiv.Perm (Fin 5) := ⟨![0,3,2,4,1],![0,4,2,1,3],by decide +kernel,by decide +kernel⟩
def v16 : Equiv.Perm (Fin 5) := ⟨![0,3,4,1,2],![0,3,4,1,2],by decide +kernel,by decide +kernel⟩
def v17 : Equiv.Perm (Fin 5) := ⟨![0,3,4,2,1],![0,4,3,1,2],by decide +kernel,by decide +kernel⟩
def v18 : Equiv.Perm (Fin 5) := ⟨![0,4,1,2,3],![0,2,3,4,1],by decide +kernel,by decide +kernel⟩
def v19 : Equiv.Perm (Fin 5) := ⟨![0,4,1,3,2],![0,2,4,3,1],by decide +kernel,by decide +kernel⟩
def v20 : Equiv.Perm (Fin 5) := ⟨![0,4,2,1,3],![0,3,2,4,1],by decide +kernel,by decide +kernel⟩
def v21 : Equiv.Perm (Fin 5) := ⟨![0,4,2,3,1],![0,4,2,3,1],by decide +kernel,by decide +kernel⟩
def v22 : Equiv.Perm (Fin 5) := ⟨![0,4,3,1,2],![0,3,4,2,1],by decide +kernel,by decide +kernel⟩
def v23 : Equiv.Perm (Fin 5) := ⟨![0,4,3,2,1],![0,4,3,2,1],by decide +kernel,by decide +kernel⟩
def v24 : Equiv.Perm (Fin 5) := ⟨![1,0,2,3,4],![1,0,2,3,4],by decide +kernel,by decide +kernel⟩
def v25 : Equiv.Perm (Fin 5) := ⟨![1,0,2,4,3],![1,0,2,4,3],by decide +kernel,by decide +kernel⟩
def v26 : Equiv.Perm (Fin 5) := ⟨![1,0,3,2,4],![1,0,3,2,4],by decide +kernel,by decide +kernel⟩
def v27 : Equiv.Perm (Fin 5) := ⟨![1,0,3,4,2],![1,0,4,2,3],by decide +kernel,by decide +kernel⟩
def v28 : Equiv.Perm (Fin 5) := ⟨![1,0,4,2,3],![1,0,3,4,2],by decide +kernel,by decide +kernel⟩
def v29 : Equiv.Perm (Fin 5) := ⟨![1,0,4,3,2],![1,0,4,3,2],by decide +kernel,by decide +kernel⟩
def v30 : Equiv.Perm (Fin 5) := ⟨![1,2,0,3,4],![2,0,1,3,4],by decide +kernel,by decide +kernel⟩
def v31 : Equiv.Perm (Fin 5) := ⟨![1,2,0,4,3],![2,0,1,4,3],by decide +kernel,by decide +kernel⟩
def v32 : Equiv.Perm (Fin 5) := ⟨![1,2,3,0,4],![3,0,1,2,4],by decide +kernel,by decide +kernel⟩
def v33 : Equiv.Perm (Fin 5) := ⟨![1,2,3,4,0],![4,0,1,2,3],by decide +kernel,by decide +kernel⟩
def v34 : Equiv.Perm (Fin 5) := ⟨![1,2,4,0,3],![3,0,1,4,2],by decide +kernel,by decide +kernel⟩
def v35 : Equiv.Perm (Fin 5) := ⟨![1,2,4,3,0],![4,0,1,3,2],by decide +kernel,by decide +kernel⟩
def v36 : Equiv.Perm (Fin 5) := ⟨![1,3,0,2,4],![2,0,3,1,4],by decide +kernel,by decide +kernel⟩
def v37 : Equiv.Perm (Fin 5) := ⟨![1,3,0,4,2],![2,0,4,1,3],by decide +kernel,by decide +kernel⟩
def v38 : Equiv.Perm (Fin 5) := ⟨![1,3,2,0,4],![3,0,2,1,4],by decide +kernel,by decide +kernel⟩
def v39 : Equiv.Perm (Fin 5) := ⟨![1,3,2,4,0],![4,0,2,1,3],by decide +kernel,by decide +kernel⟩
def v40 : Equiv.Perm (Fin 5) := ⟨![1,3,4,0,2],![3,0,4,1,2],by decide +kernel,by decide +kernel⟩
def v41 : Equiv.Perm (Fin 5) := ⟨![1,3,4,2,0],![4,0,3,1,2],by decide +kernel,by decide +kernel⟩
def v42 : Equiv.Perm (Fin 5) := ⟨![1,4,0,2,3],![2,0,3,4,1],by decide +kernel,by decide +kernel⟩
def v43 : Equiv.Perm (Fin 5) := ⟨![1,4,0,3,2],![2,0,4,3,1],by decide +kernel,by decide +kernel⟩
def v44 : Equiv.Perm (Fin 5) := ⟨![1,4,2,0,3],![3,0,2,4,1],by decide +kernel,by decide +kernel⟩
def v45 : Equiv.Perm (Fin 5) := ⟨![1,4,2,3,0],![4,0,2,3,1],by decide +kernel,by decide +kernel⟩
def v46 : Equiv.Perm (Fin 5) := ⟨![1,4,3,0,2],![3,0,4,2,1],by decide +kernel,by decide +kernel⟩
def v47 : Equiv.Perm (Fin 5) := ⟨![1,4,3,2,0],![4,0,3,2,1],by decide +kernel,by decide +kernel⟩
def v48 : Equiv.Perm (Fin 5) := ⟨![2,0,1,3,4],![1,2,0,3,4],by decide +kernel,by decide +kernel⟩
def v49 : Equiv.Perm (Fin 5) := ⟨![2,0,1,4,3],![1,2,0,4,3],by decide +kernel,by decide +kernel⟩
def v50 : Equiv.Perm (Fin 5) := ⟨![2,0,3,1,4],![1,3,0,2,4],by decide +kernel,by decide +kernel⟩
def v51 : Equiv.Perm (Fin 5) := ⟨![2,0,3,4,1],![1,4,0,2,3],by decide +kernel,by decide +kernel⟩
def v52 : Equiv.Perm (Fin 5) := ⟨![2,0,4,1,3],![1,3,0,4,2],by decide +kernel,by decide +kernel⟩
def v53 : Equiv.Perm (Fin 5) := ⟨![2,0,4,3,1],![1,4,0,3,2],by decide +kernel,by decide +kernel⟩
def v54 : Equiv.Perm (Fin 5) := ⟨![2,1,0,3,4],![2,1,0,3,4],by decide +kernel,by decide +kernel⟩
def v55 : Equiv.Perm (Fin 5) := ⟨![2,1,0,4,3],![2,1,0,4,3],by decide +kernel,by decide +kernel⟩
def v56 : Equiv.Perm (Fin 5) := ⟨![2,1,3,0,4],![3,1,0,2,4],by decide +kernel,by decide +kernel⟩
def v57 : Equiv.Perm (Fin 5) := ⟨![2,1,3,4,0],![4,1,0,2,3],by decide +kernel,by decide +kernel⟩
def v58 : Equiv.Perm (Fin 5) := ⟨![2,1,4,0,3],![3,1,0,4,2],by decide +kernel,by decide +kernel⟩
def v59 : Equiv.Perm (Fin 5) := ⟨![2,1,4,3,0],![4,1,0,3,2],by decide +kernel,by decide +kernel⟩
def v60 : Equiv.Perm (Fin 5) := ⟨![2,3,0,1,4],![2,3,0,1,4],by decide +kernel,by decide +kernel⟩
def v61 : Equiv.Perm (Fin 5) := ⟨![2,3,0,4,1],![2,4,0,1,3],by decide +kernel,by decide +kernel⟩
def v62 : Equiv.Perm (Fin 5) := ⟨![2,3,1,0,4],![3,2,0,1,4],by decide +kernel,by decide +kernel⟩
def v63 : Equiv.Perm (Fin 5) := ⟨![2,3,1,4,0],![4,2,0,1,3],by decide +kernel,by decide +kernel⟩
def v64 : Equiv.Perm (Fin 5) := ⟨![2,3,4,0,1],![3,4,0,1,2],by decide +kernel,by decide +kernel⟩
def v65 : Equiv.Perm (Fin 5) := ⟨![2,3,4,1,0],![4,3,0,1,2],by decide +kernel,by decide +kernel⟩
def v66 : Equiv.Perm (Fin 5) := ⟨![2,4,0,1,3],![2,3,0,4,1],by decide +kernel,by decide +kernel⟩
def v67 : Equiv.Perm (Fin 5) := ⟨![2,4,0,3,1],![2,4,0,3,1],by decide +kernel,by decide +kernel⟩
def v68 : Equiv.Perm (Fin 5) := ⟨![2,4,1,0,3],![3,2,0,4,1],by decide +kernel,by decide +kernel⟩
def v69 : Equiv.Perm (Fin 5) := ⟨![2,4,1,3,0],![4,2,0,3,1],by decide +kernel,by decide +kernel⟩
def v70 : Equiv.Perm (Fin 5) := ⟨![2,4,3,0,1],![3,4,0,2,1],by decide +kernel,by decide +kernel⟩
def v71 : Equiv.Perm (Fin 5) := ⟨![2,4,3,1,0],![4,3,0,2,1],by decide +kernel,by decide +kernel⟩
def v72 : Equiv.Perm (Fin 5) := ⟨![3,0,1,2,4],![1,2,3,0,4],by decide +kernel,by decide +kernel⟩
def v73 : Equiv.Perm (Fin 5) := ⟨![3,0,1,4,2],![1,2,4,0,3],by decide +kernel,by decide +kernel⟩
def v74 : Equiv.Perm (Fin 5) := ⟨![3,0,2,1,4],![1,3,2,0,4],by decide +kernel,by decide +kernel⟩
def v75 : Equiv.Perm (Fin 5) := ⟨![3,0,2,4,1],![1,4,2,0,3],by decide +kernel,by decide +kernel⟩
def v76 : Equiv.Perm (Fin 5) := ⟨![3,0,4,1,2],![1,3,4,0,2],by decide +kernel,by decide +kernel⟩
def v77 : Equiv.Perm (Fin 5) := ⟨![3,0,4,2,1],![1,4,3,0,2],by decide +kernel,by decide +kernel⟩
def v78 : Equiv.Perm (Fin 5) := ⟨![3,1,0,2,4],![2,1,3,0,4],by decide +kernel,by decide +kernel⟩
def v79 : Equiv.Perm (Fin 5) := ⟨![3,1,0,4,2],![2,1,4,0,3],by decide +kernel,by decide +kernel⟩
def v80 : Equiv.Perm (Fin 5) := ⟨![3,1,2,0,4],![3,1,2,0,4],by decide +kernel,by decide +kernel⟩
def v81 : Equiv.Perm (Fin 5) := ⟨![3,1,2,4,0],![4,1,2,0,3],by decide +kernel,by decide +kernel⟩
def v82 : Equiv.Perm (Fin 5) := ⟨![3,1,4,0,2],![3,1,4,0,2],by decide +kernel,by decide +kernel⟩
def v83 : Equiv.Perm (Fin 5) := ⟨![3,1,4,2,0],![4,1,3,0,2],by decide +kernel,by decide +kernel⟩
def v84 : Equiv.Perm (Fin 5) := ⟨![3,2,0,1,4],![2,3,1,0,4],by decide +kernel,by decide +kernel⟩
def v85 : Equiv.Perm (Fin 5) := ⟨![3,2,0,4,1],![2,4,1,0,3],by decide +kernel,by decide +kernel⟩
def v86 : Equiv.Perm (Fin 5) := ⟨![3,2,1,0,4],![3,2,1,0,4],by decide +kernel,by decide +kernel⟩
def v87 : Equiv.Perm (Fin 5) := ⟨![3,2,1,4,0],![4,2,1,0,3],by decide +kernel,by decide +kernel⟩
def v88 : Equiv.Perm (Fin 5) := ⟨![3,2,4,0,1],![3,4,1,0,2],by decide +kernel,by decide +kernel⟩
def v89 : Equiv.Perm (Fin 5) := ⟨![3,2,4,1,0],![4,3,1,0,2],by decide +kernel,by decide +kernel⟩
def v90 : Equiv.Perm (Fin 5) := ⟨![3,4,0,1,2],![2,3,4,0,1],by decide +kernel,by decide +kernel⟩
def v91 : Equiv.Perm (Fin 5) := ⟨![3,4,0,2,1],![2,4,3,0,1],by decide +kernel,by decide +kernel⟩
def v92 : Equiv.Perm (Fin 5) := ⟨![3,4,1,0,2],![3,2,4,0,1],by decide +kernel,by decide +kernel⟩
def v93 : Equiv.Perm (Fin 5) := ⟨![3,4,1,2,0],![4,2,3,0,1],by decide +kernel,by decide +kernel⟩
def v94 : Equiv.Perm (Fin 5) := ⟨![3,4,2,0,1],![3,4,2,0,1],by decide +kernel,by decide +kernel⟩
def v95 : Equiv.Perm (Fin 5) := ⟨![3,4,2,1,0],![4,3,2,0,1],by decide +kernel,by decide +kernel⟩
def v96 : Equiv.Perm (Fin 5) := ⟨![4,0,1,2,3],![1,2,3,4,0],by decide +kernel,by decide +kernel⟩
def v97 : Equiv.Perm (Fin 5) := ⟨![4,0,1,3,2],![1,2,4,3,0],by decide +kernel,by decide +kernel⟩
def v98 : Equiv.Perm (Fin 5) := ⟨![4,0,2,1,3],![1,3,2,4,0],by decide +kernel,by decide +kernel⟩
def v99 : Equiv.Perm (Fin 5) := ⟨![4,0,2,3,1],![1,4,2,3,0],by decide +kernel,by decide +kernel⟩
def v100 : Equiv.Perm (Fin 5) := ⟨![4,0,3,1,2],![1,3,4,2,0],by decide +kernel,by decide +kernel⟩
def v101 : Equiv.Perm (Fin 5) := ⟨![4,0,3,2,1],![1,4,3,2,0],by decide +kernel,by decide +kernel⟩
def v102 : Equiv.Perm (Fin 5) := ⟨![4,1,0,2,3],![2,1,3,4,0],by decide +kernel,by decide +kernel⟩
def v103 : Equiv.Perm (Fin 5) := ⟨![4,1,0,3,2],![2,1,4,3,0],by decide +kernel,by decide +kernel⟩
def v104 : Equiv.Perm (Fin 5) := ⟨![4,1,2,0,3],![3,1,2,4,0],by decide +kernel,by decide +kernel⟩
def v105 : Equiv.Perm (Fin 5) := ⟨![4,1,2,3,0],![4,1,2,3,0],by decide +kernel,by decide +kernel⟩
def v106 : Equiv.Perm (Fin 5) := ⟨![4,1,3,0,2],![3,1,4,2,0],by decide +kernel,by decide +kernel⟩
def v107 : Equiv.Perm (Fin 5) := ⟨![4,1,3,2,0],![4,1,3,2,0],by decide +kernel,by decide +kernel⟩
def v108 : Equiv.Perm (Fin 5) := ⟨![4,2,0,1,3],![2,3,1,4,0],by decide +kernel,by decide +kernel⟩
def v109 : Equiv.Perm (Fin 5) := ⟨![4,2,0,3,1],![2,4,1,3,0],by decide +kernel,by decide +kernel⟩
def v110 : Equiv.Perm (Fin 5) := ⟨![4,2,1,0,3],![3,2,1,4,0],by decide +kernel,by decide +kernel⟩
def v111 : Equiv.Perm (Fin 5) := ⟨![4,2,1,3,0],![4,2,1,3,0],by decide +kernel,by decide +kernel⟩
def v112 : Equiv.Perm (Fin 5) := ⟨![4,2,3,0,1],![3,4,1,2,0],by decide +kernel,by decide +kernel⟩
def v113 : Equiv.Perm (Fin 5) := ⟨![4,2,3,1,0],![4,3,1,2,0],by decide +kernel,by decide +kernel⟩
def v114 : Equiv.Perm (Fin 5) := ⟨![4,3,0,1,2],![2,3,4,1,0],by decide +kernel,by decide +kernel⟩
def v115 : Equiv.Perm (Fin 5) := ⟨![4,3,0,2,1],![2,4,3,1,0],by decide +kernel,by decide +kernel⟩
def v116 : Equiv.Perm (Fin 5) := ⟨![4,3,1,0,2],![3,2,4,1,0],by decide +kernel,by decide +kernel⟩
def v117 : Equiv.Perm (Fin 5) := ⟨![4,3,1,2,0],![4,2,3,1,0],by decide +kernel,by decide +kernel⟩
def v118 : Equiv.Perm (Fin 5) := ⟨![4,3,2,0,1],![3,4,2,1,0],by decide +kernel,by decide +kernel⟩
def v119 : Equiv.Perm (Fin 5) := ⟨![4,3,2,1,0],![4,3,2,1,0],by decide +kernel,by decide +kernel⟩
def vertices : List (Equiv.Perm (Fin 5)) := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119]
theorem vertices_nodup : vertices.Nodup := by decide +kernel
theorem vertices_length : vertices.length=120 := by kernel_rfl

theorem vertices_complete (p : Equiv.Perm (Fin 5)) : p ∈ vertices := by
  classical
  have hc : vertices.toFinset.card=Fintype.card (Equiv.Perm (Fin 5)) := by
    rw [List.toFinset_card_of_nodup vertices_nodup,vertices_length,Fintype.card_perm,Fintype.card_fin]
    decide
  have he : vertices.toFinset=Finset.univ := Finset.eq_univ_of_card _ hc
  exact List.mem_toFinset.mp (he ▸ Finset.mem_univ p)

def elements : List Perm := vertices.map edgeHom

theorem elements_nodup : elements.Nodup := vertices_nodup.map edgeHom_injective

theorem elements_length : elements.length=120 := by
  rw [elements,List.length_map,vertices_length]

theorem elements_complete (p : Perm) : p ∈ elements ↔ p ∈ subgroup := by
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact ⟨q,rfl⟩
  · rintro ⟨q,rfl⟩
    exact List.mem_map.mpr ⟨q,vertices_complete q,rfl⟩

end D4.PaperSymmetry.C1
