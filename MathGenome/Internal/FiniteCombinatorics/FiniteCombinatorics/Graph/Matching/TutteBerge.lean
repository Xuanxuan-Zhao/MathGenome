import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.Tutte
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.TutteBerge
import Mathlib.Basic.Finite.Sum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Choose
import Mathlib.Tactic.ByContra

universe u v
noncomputable section
set_option linter.style.haveILetI false
namespace FiniteCombinatorics.Graph.Matching

abbrev deficit : Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.deficitType :=
  Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.deficitValue
abbrev deficiency : Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.deficiencyType :=
  Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.deficiencyValue
abbrev unmatchedCount : Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.unmatchedCountType :=
  Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.unmatchedCountValue
abbrev minimumUnmatched : Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.minimumUnmatchedType :=
  Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.minimumUnmatchedValue
abbrev maximumMatchingSize : Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.maximumMatchingSizeType :=
  Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.maximumMatchingSizeValue

variable {V : Type u} [Finite V] (G : SimpleGraph V)

lemma deficit_le_deficiency (S : Set V) : deficit G S ≤ deficiency G := by
  classical
  letI := Fintype.ofFinite (Set V)
  exact Finset.le_sup' (f := deficit G) (Finset.mem_univ S)

lemma deficiency_attained : ∃ S : Set V, deficit G S = deficiency G := by
  classical
  letI := Fintype.ofFinite (Set V)
  obtain ⟨S, _, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (deficit G)
  exact ⟨S, h.symm⟩

lemma deficiency_nonneg : 0 ≤ deficiency G := by
  have h := deficit_le_deficiency G ∅
  simpa [deficit, Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.deficitValue] using
    le_trans (show (0 : ℤ) ≤ deficit G ∅ by
      simp [deficit, Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.deficitValue]) h

lemma oddComponentCount_parity :
    oddComponentCount G % 2 = Nat.card V % 2 := by
  have h := SimpleGraph.odd_ncard_oddComponents G
  change Odd (oddComponentCount G) ↔ Odd (Nat.card V) at h
  simp only [Nat.odd_iff] at h
  omega

lemma deleted_card (S : Set V) :
    Nat.card ↥((Set.univ : Set V) \ S) + Nat.card S = Nat.card V := by
  simpa only [Nat.card_coe_set_eq, Set.ncard_univ] using
    Set.ncard_sdiff_add_ncard_of_subset (Set.subset_univ S)

lemma deficit_parity (S : Set V) : deficit G S % 2 = (Nat.card V : ℤ) % 2 := by
  have hp := oddComponentCount_parity (deletedGraph G S)
  have hc := deleted_card (V := V) S
  change (↑(oddComponentCount (deletedGraph G S)) - (Nat.card S : ℤ)) % 2 = _
  omega

lemma deficiency_parity : deficiency G % 2 = (Nat.card V : ℤ) % 2 := by
  obtain ⟨S, hS⟩ := deficiency_attained G
  rw [← hS]
  exact deficit_parity G S

lemma oddComponentCount_le_card : oddComponentCount G ≤ Nat.card V := by
  apply le_trans (Nat.card_le_card_of_injective
    (Subtype.val : {c : G.ConnectedComponent // Odd (Nat.card c.supp)} → _)
    Subtype.val_injective)
  exact Nat.card_le_card_of_surjective G.connectedComponentMk Quot.mk_surjective

lemma deficiency_le_card : deficiency G ≤ (Nat.card V : ℤ) := by
  obtain ⟨S, hS⟩ := deficiency_attained G
  have ho := oddComponentCount_le_card (deletedGraph G S)
  have hc := deleted_card (V := V) S
  rw [← hS]
  change (↑(oddComponentCount (deletedGraph G S)) - (Nat.card S : ℤ)) ≤ _
  omega

lemma minimumUnmatched_le (M : EdgeMatching G) : minimumUnmatched G ≤ unmatchedCount M.val := by
  classical
  letI := Fintype.ofFinite (EdgeMatching G)
  exact Finset.inf'_le (f := fun M : EdgeMatching G => unmatchedCount M.val) (Finset.mem_univ M)

lemma minimumUnmatched_attained :
    ∃ M : EdgeMatching G, unmatchedCount M.val = minimumUnmatched G := by
  classical
  letI := Fintype.ofFinite (EdgeMatching G)
  letI : Nonempty (EdgeMatching G) :=
    ⟨Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.emptyEdgeMatching G⟩
  obtain ⟨M, _, hM⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun M : EdgeMatching G => unmatchedCount M.val)
  exact ⟨M, hM.symm⟩

lemma le_maximumMatchingSize (M : EdgeMatching G) : Nat.card M.val ≤ maximumMatchingSize G := by
  classical
  letI := Fintype.ofFinite (EdgeMatching G)
  exact Finset.le_sup' (f := fun M : EdgeMatching G => Nat.card M.val) (Finset.mem_univ M)

lemma maximumMatchingSize_attained :
    ∃ M : EdgeMatching G, Nat.card M.val = maximumMatchingSize G := by
  classical
  letI := Fintype.ofFinite (EdgeMatching G)
  letI : Nonempty (EdgeMatching G) :=
    ⟨Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.emptyEdgeMatching G⟩
  obtain ⟨M, _, hM⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun M : EdgeMatching G => Nat.card M.val)
  exact ⟨M, hM.symm⟩

/-- Disjoint two-element edges account for exactly twice the matching size. -/
lemma saturated_card {M : Set (Sym2 V)} (hm : IsMatching G M) :
    Nat.card {v : V | Saturated M v} = 2 * Nat.card M := by
  classical
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite M
  have heq : (Finset.univ.biUnion (fun e : M => e.val.toFinset)) =
      {v : V | Saturated M v}.toFinset := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Sym2.mem_toFinset,
      Set.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨fun ⟨e, he⟩ => ⟨e.val, e.property, he⟩,
      fun ⟨e, he, hv⟩ => ⟨⟨e, he⟩, hv⟩⟩
  have hd : ((Finset.univ : Finset M) : Set M).PairwiseDisjoint (fun e : M => e.val.toFinset) := by
    intro e _ f _ hef
    apply Finset.disjoint_left.mpr
    intro v he hf
    exact hef (Subtype.ext (hm.2 e.val e.property f.val f.property v
      (Sym2.mem_toFinset.mp he) (Sym2.mem_toFinset.mp hf)))
  have hc (e : M) : e.val.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet (hm.1 e.property))
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', ← heq,
    Finset.card_biUnion hd]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm]

lemma matching_card_identity {M : Set (Sym2 V)} (hm : IsMatching G M) :
    2 * Nat.card M + unmatchedCount M = Nat.card V := by
  have h := Set.ncard_add_ncard_compl {v : V | Saturated M v}
  rw [← Nat.card_coe_set_eq, saturated_card G hm] at h
  exact h

lemma extrema_card_identity :
    2 * maximumMatchingSize G + minimumUnmatched G = Nat.card V := by
  obtain ⟨M, hM⟩ := minimumUnmatched_attained G
  obtain ⟨N, hN⟩ := maximumMatchingSize_attained G
  have h₁ := matching_card_identity G M.property
  have h₂ := matching_card_identity G N.property
  have h₃ := minimumUnmatched_le G N
  have h₄ := le_maximumMatchingSize G M
  omega

/-- An odd component has an unmatched vertex or sends a matching edge into S. -/
lemma odd_component_witness (H : G.Subgraph) (hm : H.IsMatching) (S : Set V)
    (c : (deletedGraph G S).ConnectedComponent) (hc : Odd (Nat.card c.supp)) :
    (∃ v : ↥((Set.univ : Set V) \ S), v ∈ c.supp ∧ v.val ∉ H.verts) ∨
    (∃ v : ↥((Set.univ : Set V) \ S), v ∈ c.supp ∧ ∃ w ∈ S, H.Adj v.val w) := by
  classical
  by_contra! hn
  let C : Set V := Subtype.val '' c.supp
  have hmatch : (H.induce C).IsMatching := by
    intro v hv
    obtain ⟨v', hv', rfl⟩ := hv
    have hvH : v'.val ∈ H.verts := by simpa using hn.1 v' hv'
    obtain ⟨w, hw, huniq⟩ := hm hvH
    have hws : w ∉ S := fun hs => hn.2 v' hv' w hs hw
    have hwC : w ∈ C := by
      refine ⟨⟨w, Set.mem_sdiff_of_mem (Set.mem_univ w) hws⟩, ?_, rfl⟩
      exact (c.mem_supp_congr_adj (show (deletedGraph G S).Adj v'
        ⟨w, Set.mem_sdiff_of_mem (Set.mem_univ w) hws⟩ from H.adj_sub hw)).mp hv' 
    exact ⟨w, ⟨⟨v', hv', rfl⟩, hwC, hw⟩, fun y hy => huniq y hy.2.2⟩
  have heven : Even (Nat.card C) := by
    letI := Fintype.ofFinite (H.induce C).verts
    change Even (Nat.card (H.induce C).verts)
    rw [Nat.card_eq_fintype_card]
    simpa only [Set.toFinset_card] using hmatch.even_card
  have hcard : Nat.card C = Nat.card c.supp := by
    exact Set.ncard_image_of_injective _ Subtype.val_injective
  rw [hcard] at heven
  exact (Nat.not_even_iff_odd.mpr hc) heven

lemma odd_components_le_unmatched_add (H : G.Subgraph) (hm : H.IsMatching) (S : Set V) :
    oddComponentCount (deletedGraph G S) ≤ Nat.card S + Nat.card ↥(H.vertsᶜ) := by
  classical
  let O := {c : (deletedGraph G S).ConnectedComponent // Odd (Nat.card c.supp)}
  have hex (c : O) : ∃ t : S ⊕ ↥(H.vertsᶜ),
      ∃ v : ↥((Set.univ : Set V) \ S), v ∈ c.val.supp ∧
        (match t with | .inl w => H.Adj v.val w.val | .inr w => v.val = w.val) := by
    rcases odd_component_witness G H hm S c.val c.property with h | h
    · obtain ⟨v, hv, hu⟩ := h
      exact ⟨.inr ⟨v.val, hu⟩, v, hv, rfl⟩
    · obtain ⟨v, hv, w, hw, hvw⟩ := h
      exact ⟨.inl ⟨w, hw⟩, v, hv, hvw⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro c d hcd
    obtain ⟨v, hv, hvf⟩ := hf c
    obtain ⟨w, hw, hwf⟩ := hf d
    have hvw : v = w := by
      apply Subtype.ext
      cases he : f c with
      | inl t =>
        have he' : f d = .inl t := hcd.symm.trans he
        rw [he] at hvf
        rw [he'] at hwf
        exact hm.eq_of_adj_right hvf hwf
      | inr t =>
        have he' : f d = .inr t := hcd.symm.trans he
        rw [he] at hvf
        rw [he'] at hwf
        exact hvf.trans hwf.symm
    exact Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex hv (hvw ▸ hw))
  change Nat.card O ≤ _
  simpa only [Nat.card_sum] using Nat.card_le_card_of_injective f hinj

lemma deficiency_le_unmatched {M : Set (Sym2 V)} (hm : IsMatching G M) :
    deficiency G ≤ (unmatchedCount M : ℤ) := by
  obtain ⟨S, hS⟩ := deficiency_attained G
  have h := odd_components_le_unmatched_add G (edgeSubgraph G M hm.1)
    ((edgeSubgraph_isMatching G M hm.1).mpr hm) S
  change oddComponentCount (deletedGraph G S) ≤ Nat.card S + unmatchedCount M at h
  rw [← hS]
  change (oddComponentCount (deletedGraph G S) : ℤ) - (Nat.card S : ℤ) ≤ _
  omega

lemma oddComponentCount_iso {W : Type v} [Finite W] {K : SimpleGraph W}
    (φ : G ≃g K) : oddComponentCount G = oddComponentCount K := by
  apply Nat.card_congr
  exact φ.connectedComponentEquiv.subtypeEquiv (fun c => by
    rw [← Nat.card_congr (c.isoEquivSupp φ)])

/-- Adjoin a clique whose vertices are adjacent to every old vertex. -/
def adjoinUniversal (D : Type v) : SimpleGraph (V ⊕ D) where
  Adj a b := match a, b with
    | .inl v, .inl w => G.Adj v w
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr d, .inr e => d ≠ e
  symm := ⟨by
    rintro (a | a) (b | b) h
    · exact h.symm
    · trivial
    · trivial
    · exact Ne.symm h⟩
  loopless := ⟨by
    rintro (a | a)
    · exact G.loopless.irrefl a
    · exact fun h => h rfl⟩

omit [Finite V] in
lemma adjoinUniversal_inr_adj {D : Type v} (d : D) (a : V ⊕ D)
    (h : Sum.inr d ≠ a) : (adjoinUniversal G D).Adj (.inr d) a := by
  cases a with
  | inl a => trivial
  | inr a => exact fun he => h (congrArg Sum.inr he)

/-- Once all new vertices are deleted, only the corresponding old induced graph remains. -/
def deletedAdjoinIso {D : Type v} [Finite D] (X : Set (V ⊕ D))
    (hD : ∀ d, Sum.inr d ∈ X) :
    deletedGraph G (Sum.inl ⁻¹' X) ≃g deletedGraph (adjoinUniversal G D) X where
  toEquiv := Equiv.ofBijective
    (fun a : ↥((Set.univ : Set V) \ (Sum.inl ⁻¹' X)) =>
      (⟨Sum.inl a.val, ⟨Set.mem_univ _, a.property.2⟩⟩ :
        ↥((Set.univ : Set (V ⊕ D)) \ X))) (by
      constructor
      · intro a b h
        exact Subtype.ext (Sum.inl_injective (congrArg Subtype.val h))
      · rintro ⟨a | d, ha⟩
        · exact ⟨⟨a, ⟨Set.mem_univ _, ha.2⟩⟩, rfl⟩
        · exact False.elim (ha.2 (hD d)))
  map_rel_iff' := by intro a b; rfl

lemma deletedAdjoin_connected {D : Type v} [Finite D] (X : Set (V ⊕ D))
    (d : D) (hd : Sum.inr d ∉ X) :
    (deletedGraph (adjoinUniversal G D) X).Connected := by
  let u : ↥((Set.univ : Set (V ⊕ D)) \ X) := ⟨.inr d, ⟨Set.mem_univ _, hd⟩⟩
  have hr (a : ↥((Set.univ : Set (V ⊕ D)) \ X)) :
      (deletedGraph (adjoinUniversal G D) X).Reachable u a := by
    by_cases h : u = a
    · subst a; exact .refl u
    · have ha : (deletedGraph (adjoinUniversal G D) X).Adj u a :=
        adjoinUniversal_inr_adj G d a.val (fun he => h (Subtype.ext he))
      exact ha.reachable
  exact { preconnected := fun a b => (hr a).symm.trans (hr b), nonempty := ⟨u⟩ }

lemma oddComponentCount_le_one (h : G.Connected) : oddComponentCount G ≤ 1 := by
  have hh : Nat.card G.ConnectedComponent = 1 :=
    (FiniteCombinatorics.Graph.connected_iff_one_component G).mp h
  calc
    oddComponentCount G ≤ Nat.card G.ConnectedComponent :=
      Nat.card_le_card_of_injective
        (Subtype.val : {c : G.ConnectedComponent // Odd (Nat.card c.supp)} → _)
        Subtype.val_injective
    _ = 1 := hh

/-- Tutte's inequalities for the universal extension. -/
lemma adjoinUniversal_tutte {D : Type v} [Finite D]
    (hd : deficiency G ≤ (Nat.card D : ℤ)) (hp : Even (Nat.card V + Nat.card D)) :
    ∀ X : Set (V ⊕ D),
      oddComponentCount (deletedGraph (adjoinUniversal G D) X) ≤ Nat.card X := by
  classical
  intro X
  by_cases hD : ∀ d : D, Sum.inr d ∈ X
  · rw [← oddComponentCount_iso _ (deletedAdjoinIso G X hD)]
    have hdef := (deficit_le_deficiency G (Sum.inl ⁻¹' X)).trans hd
    change (oddComponentCount (deletedGraph G (Sum.inl ⁻¹' X)) : ℤ) -
      (Nat.card (Sum.inl ⁻¹' X) : ℤ) ≤ _ at hdef
    let f : (Sum.inl ⁻¹' X) ⊕ D → X := fun t => match t with
      | .inl a => ⟨Sum.inl a.val, a.property⟩
      | .inr d => ⟨Sum.inr d, hD d⟩
    have hf : Function.Injective f := by
      rintro (a | d) (b | e) h
      · exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective (congrArg Subtype.val h)))
      · simp [f] at h
      · simp [f] at h
      · exact congrArg Sum.inr (Sum.inr_injective (congrArg Subtype.val h))
    have hc := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at hc
    omega
  · push Not at hD
    obtain ⟨d, hdX⟩ := hD
    have hconn := deletedAdjoin_connected G X d hdX
    have hone := oddComponentCount_le_one _ hconn
    by_cases he : X = ∅
    · subst X
      have hc := deleted_card (V := V ⊕ D) ∅
      rw [Nat.card_sum, show Nat.card (∅ : Set (V ⊕ D)) = 0 by simp, add_zero] at hc
      have hpar := oddComponentCount_parity (deletedGraph (adjoinUniversal G D) ∅)
      rw [Nat.even_iff] at hp
      simp only [Nat.card_coe_set_eq, Set.ncard_empty]
      omega
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr he
      have : Nonempty X := ⟨⟨x, hx⟩⟩
      have hpos : 0 < Nat.card X := Nat.card_pos
      omega

/-- Restrict a perfect matching of the extension back to the old vertices.
Every old vertex left unmatched had a distinct partner among the new vertices. -/
lemma matching_of_adjoinUniversal_perfect {D : Type v} [Finite D]
    (N : Set (Sym2 (V ⊕ D))) (hN : IsPerfectMatching (adjoinUniversal G D) N) :
    ∃ M : EdgeMatching G, unmatchedCount M.val ≤ Nat.card D := by
  classical
  let M : Set (Sym2 V) := Sym2.map Sum.inl ⁻¹' N
  have hsub : M ⊆ G.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ a b => exact hN.1.1 he
  have hmatch : IsMatching G M := by
    apply (matching_iff_neighbors G M).mpr
    refine ⟨hsub, fun a b c hab hac => ?_⟩
    exact Sum.inl_injective
      (((matching_iff_neighbors (adjoinUniversal G D) N).mp hN.1).2
        (.inl a) (.inl b) (.inl c) hab hac)
  have hex (v : {v : V // ¬ Saturated M v}) :
      ∃ d : D, s(Sum.inl v.val, Sum.inr d) ∈ N := by
    obtain ⟨w, hw⟩ := (saturated_iff_neighbor N (.inl v.val)).mp (hN.2 (.inl v.val))
    cases w with
    | inl w =>
      exfalso
      apply v.property
      exact ⟨s(v.val, w), hw, Sym2.mem_mk_left _ _⟩
    | inr d => exact ⟨d, hw⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Sum.inl_injective
    exact ((matching_iff_neighbors (adjoinUniversal G D) N).mp hN.1).2
      (.inr (f a)) (.inl a.val) (.inl b.val)
      (by simpa only [Sym2.eq_swap] using hf a)
      (by simpa only [hab, Sym2.eq_swap] using hf b)
  exact ⟨⟨M, hmatch⟩, Nat.card_le_card_of_injective f hinj⟩

/-- The universal extension produces a matching attaining the integer deficit. -/
lemma unmatched_attains_deficiency :
    ∃ M : EdgeMatching G, (unmatchedCount M.val : ℤ) = deficiency G := by
  let d : ℕ := (deficiency G).toNat
  have hd : (d : ℤ) = deficiency G := Int.toNat_of_nonneg (deficiency_nonneg G)
  have hp : Even (Nat.card V + d) := by
    have hpar := deficiency_parity G
    rw [Nat.even_iff]
    omega
  have ht := adjoinUniversal_tutte G (D := Fin d) (by rw [Nat.card_fin, hd])
    (by simpa only [Nat.card_fin] using hp)
  obtain ⟨N, hN⟩ := (tutte (adjoinUniversal G (Fin d))).mpr ht
  obtain ⟨M, hM⟩ := matching_of_adjoinUniversal_perfect G N hN
  have hlo := deficiency_le_unmatched G M.property
  rw [Nat.card_fin] at hM
  exact ⟨M, by omega⟩

/-- Tutte--Berge, with actual finite extrema, integer deficit, and integral half. -/
theorem tutteBerge : Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.tutteBergeType := by
  intro V _ G
  obtain ⟨M, hM⟩ := unmatched_attains_deficiency G
  obtain ⟨N, hN⟩ := minimumUnmatched_attained G
  have hlo := deficiency_le_unmatched G N.property
  have hle := minimumUnmatched_le G M
  have hmin : (minimumUnmatched G : ℤ) = deficiency G := by omega
  have hcard := extrema_card_identity G
  refine ⟨deficiency_nonneg G, hmin, ?_, ?_, deficiency_parity G⟩
  · change (maximumMatchingSize G : ℤ) = ((Nat.card V : ℤ) - deficiency G) / 2
    omega
  · change 2 * (maximumMatchingSize G : ℤ) + deficiency G = (Nat.card V : ℤ)
    omega

/-- All three optimization quantities vanish on the graph with no vertices. -/
theorem empty_tutteBerge :
    Specs.FiniteCombinatorics.Graph.Matching.TutteBerge.empty_tutteBergeType := by
  intro V _ _ G
  have hn : Nat.card V = 0 := Nat.card_of_isEmpty
  have h := tutteBerge G
  change 0 ≤ deficiency G ∧ (minimumUnmatched G : ℤ) = deficiency G ∧ _ at h
  change deficiency G = 0 ∧ minimumUnmatched G = 0 ∧ maximumMatchingSize G = 0
  have hc := extrema_card_identity G
  omega

end FiniteCombinatorics.Graph.Matching
