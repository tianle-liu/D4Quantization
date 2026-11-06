import D4.PaperMonomials

/-! Coefficient counts refer to every canonical degree-five monomial, not
merely the number of entries printed in a proposed certificate. -/
namespace D4.PaperStatistics
open Certificate

def coefficient (p : Poly) (m : Monomial) : Int :=
  p.foldr (fun t s => if t.1=m then t.2+s else s) 0

@[simp] theorem coefficient_cons (t : Monomial × Int) (p : Poly) (m : Monomial) :
    coefficient (t::p) m = if t.1=m then t.2+coefficient p m else coefficient p m := rfl

theorem coefficient_zero_of_not_mem (p : Poly) (m : Monomial)
    (hm : m ∉ p.map Prod.fst) : coefficient p m=0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at hm
    simp only [coefficient_cons]
    rw [if_neg (Ne.symm hm.1)]
    exact ih hm.2

theorem coefficient_nonneg (p : Poly) (m : Monomial)
    (hp : ∀ t ∈ p, 0 ≤ t.2) : 0 ≤ coefficient p m := by
  induction p with
  | nil => exact le_rfl
  | cons t p ih =>
    have ht := hp t (by simp)
    have hi := ih (fun s hs => hp s (by simp [hs]))
    simp only [coefficient_cons]
    split_ifs <;> omega

theorem coefficient_pos_iff (p : Poly) (m : Monomial)
    (hp : ∀ t ∈ p, 0 < t.2) :
    0 < coefficient p m ↔ m ∈ p.map Prod.fst := by
  induction p with
  | nil => simp [coefficient]
  | cons t p ih =>
    have ht := hp t (by simp)
    have htail : ∀ s ∈ p, 0 < s.2 := fun s hs => hp s (by simp [hs])
    have hn := coefficient_nonneg p m (fun s hs => (htail s hs).le)
    have hi := ih htail
    by_cases he : t.1=m
    · rw [coefficient_cons,if_pos he]
      exact iff_of_true (by omega) (by simp [he])
    · rw [coefficient_cons,if_neg he]
      simpa only [List.map_cons,List.mem_cons,Ne.symm he,false_or] using hi

theorem coefficient_eq_of_mem (p : Poly) (m : Monomial) (c : Int)
    (hp : (p.map Prod.fst).Nodup) (hm : (m,c) ∈ p) : coefficient p m=c := by
  induction p with
  | nil => simp at hm
  | cons t p ih =>
    have hd := List.nodup_cons.mp hp
    rcases List.mem_cons.mp hm with he | hm
    · subst t
      simp only [coefficient_cons,if_pos rfl]
      rw [coefficient_zero_of_not_mem p m hd.1,add_zero]
      simp
    · have hn : t.1≠m := by
        intro he
        apply hd.1
        rw [he]
        exact List.mem_map.mpr ⟨(m,c),hm,rfl⟩
      simp only [coefficient_cons,if_neg hn]
      exact ih hd.2 hm

theorem support_counts (p : Poly) (npos : Nat)
    (hd : (p.map Prod.fst).Nodup) (hlen : p.length=npos)
    (hpos : ∀ t ∈ p, 0 < t.2)
    (hdegree : ∀ t ∈ p, t.1.length=5 ∧ t.1.Pairwise (· ≤ ·) ∧ ∀ i ∈ t.1, i<10) :
    (degreeFive.toFinset.filter (fun m => 0 < coefficient p m)).card=npos ∧
    (degreeFive.toFinset.filter (fun m => coefficient p m=0)).card=2002-npos := by
  classical
  have he : degreeFive.toFinset.filter (fun m => 0 < coefficient p m) =
      (p.map Prod.fst).toFinset := by
    ext m
    simp only [Finset.mem_filter,List.mem_toFinset,coefficient_pos_iff p m hpos]
    constructor
    · exact And.right
    · intro hm
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm
      exact ⟨(degreeFive_complete t.1).mpr (hdegree t ht),List.mem_map.mpr ⟨t,ht,rfl⟩⟩
  have hpcount : (degreeFive.toFinset.filter (fun m => 0 < coefficient p m)).card=npos := by
    rw [he,List.toFinset_card_of_nodup hd,List.length_map,hlen]
  refine ⟨hpcount,?_⟩
  have hs := Finset.filter_card_add_filter_neg_card_eq_card
    (s:=degreeFive.toFinset) (p:=fun m => 0 < coefficient p m)
  have hzero : degreeFive.toFinset.filter (fun m => ¬0 < coefficient p m) =
      degreeFive.toFinset.filter (fun m => coefficient p m=0) := by
    apply Finset.filter_congr
    intro m _
    have hn := coefficient_nonneg p m (fun t ht => (hpos t ht).le)
    omega
  rw [hpcount,hzero,degreeFive_card] at hs
  omega

theorem positive_minimum (p : Poly) (c : Int) (hc : 0 < c)
    (hd : (p.map Prod.fst).Nodup)
    (hmin : ∀ t ∈ p, c ≤ t.2) (hex : ∃ t ∈ p, t.2=c)
    (hdegree : ∀ t ∈ p, t.1.length=5 ∧ t.1.Pairwise (· ≤ ·) ∧ ∀ i ∈ t.1, i<10) :
    (∀ m ∈ degreeFive, 0 < coefficient p m → c ≤ coefficient p m) ∧
      ∃ m ∈ degreeFive, coefficient p m=c := by
  have hp : ∀ t ∈ p, 0 < t.2 := fun t ht => hc.trans_le (hmin t ht)
  constructor
  · intro m _ hm
    obtain ⟨t,ht,he⟩ := List.mem_map.mp ((coefficient_pos_iff p m hp).mp hm)
    subst m
    rw [coefficient_eq_of_mem p t.1 t.2 hd (by simpa using ht)]
    exact hmin t ht
  · obtain ⟨t,ht,he⟩ := hex
    exact ⟨t.1,(degreeFive_complete t.1).mpr (hdegree t ht),
      (coefficient_eq_of_mem p t.1 t.2 hd (by simpa using ht)).trans he⟩

/-- Linear-time sortedness checking suffices for distinct monomial keys. -/
theorem keys_nodup (p : Poly) (h : (p.map (fun t => key t.1)).Chain' (· < ·)) :
    (p.map Prod.fst).Nodup := by
  have hn : (p.map (fun t => key t.1)).Nodup :=
    (List.chain'_iff_pairwise.mp h).nodup
  have he : (p.map Prod.fst).map key = p.map (fun t => key t.1) := by simp
  rw [← he] at hn
  exact List.Nodup.of_map key hn

end D4.PaperStatistics
