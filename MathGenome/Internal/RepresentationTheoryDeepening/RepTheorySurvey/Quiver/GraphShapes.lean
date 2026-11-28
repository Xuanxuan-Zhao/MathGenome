import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.Forms
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.GraphShapes

open scoped BigOperators Matrix

namespace RepTheorySurvey.Quiver.GraphShapes

open GraphShapesSpec (underlyingGraph IsPathGraph IsThreeArmedTree)
open SimpleGraph

universe u v

noncomputable section

section Obstructions

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)]

private def weightedSum (x : Q → ℝ) (i : Q) : ℝ :=
  ∑ j, (Forms.edgeMultiplicity i j : ℝ) * x j

/-- Nonpositive matrix rows on the support give a nonpositive Tits value. -/
private theorem false_of_nonpositive_rows
    (hacyclic : ¬ RM03.HasOrientedCycle Q) (hpos : Forms.PositiveDefinite Q)
    (x : Q → ℝ) (hx : x ≠ 0) (hnonneg : ∀ i, 0 ≤ x i)
    (hrow : ∀ i, 0 < x i → 2 * x i ≤ weightedSum x i) : False := by
  classical
  have hentry (i j : Q) :
      Forms.polarizationMatrix ℝ i j * x j =
        (if i = j then 2 * x i else 0) - (Forms.edgeMultiplicity i j : ℝ) * x j := by
    by_cases h : i = j
    · subst j
      simp [Forms.edgeMultiplicity_self hacyclic, Forms.polarizationMatrix_apply_self]
    · rw [Forms.polarizationMatrix_apply_of_ne h, ite_eq_right h, zero_sub, neg_mul]
  have hmatrix (i : Q) :
      (Forms.polarizationMatrix ℝ *ᵥ x) i = 2 * x i - weightedSum x i := by
    simp [Matrix.mulVec, dotProduct, hentry, Finset.sum_sub_distrib, weightedSum]
  have hquad : x ⬝ᵥ (Forms.polarizationMatrix ℝ *ᵥ x) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    rw [hmatrix]
    rcases (hnonneg i).eq_or_lt with h | h
    · simp [← h]
    · exact mul_nonpos_of_nonneg_of_nonpos (hnonneg i) (sub_nonpos.mpr (hrow i h))
  rw [← Forms.real_quadratic_matrix hacyclic x] at hquad
  have := hpos x hx
  linarith

omit [Fintype (RM03.Arrow Q)] in
private theorem weight_at_le_sum (x : Q → ℝ) (hx : ∀ i, 0 ≤ x i) (i j : Q) :
    (Forms.edgeMultiplicity i j : ℝ) * x j ≤ weightedSum x i := by
  classical
  exact Finset.single_le_sum (f := fun j => (Forms.edgeMultiplicity i j : ℝ) * x j)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hx j)) (Finset.mem_univ j)

omit [Fintype (RM03.Arrow Q)] in
private theorem neighbor_sum_le_weighted (x : Q → ℝ) (hx : ∀ i, 0 ≤ x i)
    (i : Q) (s : Finset Q) (hs : ∀ j ∈ s, (underlyingGraph (Q := Q)).Adj i j) :
    ∑ j ∈ s, x j ≤ weightedSum x i := by
  classical
  calc
    _ ≤ ∑ j ∈ s, (Forms.edgeMultiplicity i j : ℝ) * x j := by
      apply Finset.sum_le_sum
      intro j hj
      have h : (1 : ℝ) ≤ Forms.edgeMultiplicity i j := by
        exact_mod_cast (hs j hj).2
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h (hx j)
    _ ≤ weightedSum x i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => mul_nonneg (Nat.cast_nonneg _) (hx j))

omit [Fintype (RM03.Arrow Q)] in
private theorem two_neighbors_le_weighted (x : Q → ℝ) (hx : ∀ i, 0 ≤ x i)
    {i a b : Q} (hne : a ≠ b) (ha : (underlyingGraph (Q := Q)).Adj i a)
    (hb : (underlyingGraph (Q := Q)).Adj i b) :
    x a + x b ≤ weightedSum x i := by
  classical
  simpa [Finset.sum_insert, hne] using
    (neighbor_sum_le_weighted x hx i {a, b} (by simpa using ⟨ha, hb⟩))

theorem positiveDefiniteMultiplicity : GraphShapesSpec.PositiveDefiniteMultiplicity.{u, v} := by
  classical
  intro Q _ _ _ hacyclic hpos i j
  by_contra! h
  have hij : i ≠ j := by
    rintro rfl
    simp [Forms.edgeMultiplicity_self hacyclic] at h
  let x : Q → ℝ := fun k => if k = i ∨ k = j then 1 else 0
  have hxi : x i = 1 := by simp [x]
  have hxj : x j = 1 := by simp [x]
  have hnonneg (k : Q) : 0 ≤ x k := by dsimp [x]; split <;> norm_num
  have h2 : (2 : ℝ) ≤ Forms.edgeMultiplicity i j := by exact_mod_cast h
  apply false_of_nonpositive_rows hacyclic hpos x (by simpa [hxi] using congrFun · i) hnonneg
  intro k hk
  have hs : k = i ∨ k = j := by
    by_contra hn
    simp [x, hn] at hk
  rcases hs with rfl | rfl
  · simpa [hxi, hxj] using h2.trans (by simpa [hxj] using weight_at_le_sum x hnonneg k j)
  · have hw := weight_at_le_sum x hnonneg k i
    rw [Forms.edgeMultiplicity_comm k i, hxi, mul_one] at hw
    simpa [hxj] using h2.trans hw

private theorem underlying_acyclic
    (hacyclic : ¬ RM03.HasOrientedCycle Q) (hpos : Forms.PositiveDefinite Q) :
    (underlyingGraph (Q := Q)).IsAcyclic := by
  classical
  intro a p hp
  let x : Q → ℝ := fun i => if i ∈ p.support then 1 else 0
  have hx : x a = 1 := by simp [x]
  have hnonneg (i : Q) : 0 ≤ x i := by dsimp [x]; split <;> norm_num
  apply false_of_nonpositive_rows hacyclic hpos x (by simpa [hx] using congrFun · a) hnonneg
  intro i hi
  have hi' : i ∈ p.support := by by_contra h; simp [x, h] at hi
  let s := (p.toSubgraph.neighborSet i).toFinite.toFinset
  have hcard : s.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card]; exact hp.ncard_neighborSet_toSubgraph_eq_two hi'
  have hmem (j : Q) (hj : j ∈ s) : p.toSubgraph.Adj i j :=
    (p.toSubgraph.neighborSet i).toFinite.mem_toFinset.mp hj
  have hsum : (∑ j ∈ s, x j) = 2 := by
    calc
      _ = ∑ _j ∈ s, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have h : j ∈ p.support := p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert (hmem j hj).symm)
        simp [x, h]
      _ = 2 := by simp [hcard]
  have := neighbor_sum_le_weighted x hnonneg i s (fun j hj => p.toSubgraph.adj_sub (hmem j hj))
  simpa [hsum, x, hi'] using this

private theorem neighbor_ncard_le_three
    (hacyclic : ¬ RM03.HasOrientedCycle Q) (hpos : Forms.PositiveDefinite Q) (c : Q) :
    ((underlyingGraph (Q := Q)).neighborSet c).ncard ≤ 3 := by
  classical
  let G := underlyingGraph (Q := Q)
  by_contra! hc
  let x : Q → ℝ := fun i => if i = c then 2 else if G.Adj c i then 1 else 0
  have hxc : x c = 2 := by simp [x]
  have hxa {i : Q} (hi : G.Adj c i) : x i = 1 := by simp [x, hi, hi.ne.symm]
  have hnonneg (i : Q) : 0 ≤ x i := by dsimp [x]; split <;> (try split) <;> norm_num
  apply false_of_nonpositive_rows hacyclic hpos x (by simpa [hxc] using congrFun · c) hnonneg
  intro i hi
  by_cases he : i = c
  · subst i
    let s := (G.neighborSet c).toFinite.toFinset
    have hcard : 4 ≤ s.card := by rw [← Set.ncard_eq_toFinset_card]; exact hc
    have hadj (j : Q) (hj : j ∈ s) : G.Adj c j := (G.neighborSet c).toFinite.mem_toFinset.mp hj
    have hsum : (4 : ℝ) ≤ ∑ j ∈ s, x j := by
      simp only [Finset.sum_congr rfl (fun j hj => hxa (hadj j hj)), Finset.sum_const,
        nsmul_eq_mul, mul_one]
      exact_mod_cast hcard
    have := hsum.trans (neighbor_sum_le_weighted x hnonneg c s hadj)
    linarith
  · have ha : G.Adj c i := by
      by_contra hn
      simp [x, he, hn] at hi
    simpa [hxa ha, hxc] using
      (neighbor_sum_le_weighted x hnonneg i {c} (by simpa using ha.symm))

omit [Fintype (RM03.Arrow Q)] in
private theorem three_neighbors_weighted (x : Q → ℝ) (hx : ∀ i, 0 ≤ x i)
    {i a : Q} (ha : (underlyingGraph (Q := Q)).Adj i a) (hxa : x a = 2)
    (hd : 3 ≤ ((underlyingGraph (Q := Q)).neighborSet i).ncard)
    (hmin : ∀ j, (underlyingGraph (Q := Q)).Adj i j → 1 ≤ x j) :
    4 ≤ weightedSum x i := by
  classical
  let neighbors := (underlyingGraph (Q := Q)).neighborSet i
  let s := neighbors.toFinite.toFinset
  have hmem (j : Q) (hj : j ∈ s) : (underlyingGraph (Q := Q)).Adj i j :=
    neighbors.toFinite.mem_toFinset.mp hj
  have hs : a ∈ s := neighbors.toFinite.mem_toFinset.mpr ha
  have hc : 3 ≤ s.card := by
    rw [← Set.ncard_eq_toFinset_card]; exact hd
  have hce : 2 ≤ (s.erase a).card := by
    have := Finset.card_erase_add_one hs
    omega
  have hsum : (2 : ℝ) ≤ ∑ j ∈ s.erase a, x j := by
    calc
      _ ≤ ((s.erase a).card : ℝ) := by exact_mod_cast hce
      _ = ∑ _j ∈ s.erase a, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj => hmin j (hmem j (Finset.mem_of_mem_erase hj))
  have he := Finset.sum_erase_add s x hs
  have hbound := neighbor_sum_le_weighted x hx i s hmem
  linarith

private theorem eq_of_three_le_neighbor_ncard
    (hacyclic : ¬ RM03.HasOrientedCycle Q) (hpos : Forms.PositiveDefinite Q)
    {a b : Q} (hab : (underlyingGraph (Q := Q)).Reachable a b)
    (ha : 3 ≤ ((underlyingGraph (Q := Q)).neighborSet a).ncard)
    (hb : 3 ≤ ((underlyingGraph (Q := Q)).neighborSet b).ncard) : a = b := by
  classical
  let G := underlyingGraph (Q := Q)
  by_contra hne
  obtain ⟨q⟩ := hab
  let p : G.Walk a b := q.toPath.val
  have hp : p.IsPath := q.toPath.property
  have hn : ¬p.Nil := Walk.not_nil_of_ne hne
  -- Allow all neighbors of the path in the support. Each added vertex already
  -- has a path neighbor with value two.
  let x : Q → ℝ := fun i =>
    if i ∈ p.support then 2 else if ∃ j ∈ p.support, G.Adj j i then 1 else 0
  have hxs (i : Q) (hi : i ∈ p.support) : x i = 2 := by simp [x, hi]
  have hxa : x a = 2 := hxs a p.start_mem_support
  have hnonneg (i : Q) : 0 ≤ x i := by dsimp [x]; split <;> (try split) <;> norm_num
  have hneighbor {i j : Q} (hi : i ∈ p.support) (hadj : G.Adj i j) : 1 ≤ x j := by
    by_cases hj : j ∈ p.support
    · simp [x, hj]
    · simp [x, hj, show ∃ k ∈ p.support, G.Adj k j from ⟨i, hi, hadj⟩]
  apply false_of_nonpositive_rows hacyclic hpos x (by simpa [hxa] using congrFun · a) hnonneg
  intro i hi
  by_cases his : i ∈ p.support
  · rw [hxs i his]
    norm_num only [Nat.reduceMul, show (2 : ℝ) * 2 = 4 by norm_num]
    by_cases hia : i = a
    · subst i
      exact three_neighbors_weighted x hnonneg (p.adj_snd hn)
        (hxs _ (p.getVert_mem_support 1)) ha (fun _ => hneighbor p.start_mem_support)
    by_cases hib : i = b
    · subst i
      exact three_neighbors_weighted x hnonneg (p.adj_penultimate hn).symm
        (hxs _ (p.getVert_mem_support (p.length - 1))) hb (fun _ => hneighbor p.end_mem_support)
    obtain ⟨n, rfl, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp his
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hia p.getVert_zero
    have hnl' : n < p.length := by
      refine lt_of_le_of_ne hnl ?_
      intro h
      simp [h] at hib
    have h1 := (p.adj_getVert_succ (i := n - 1) (by omega)).symm
    rw [show n - 1 + 1 = n by omega] at h1
    have h2 := p.adj_getVert_succ hnl'
    have hdistinct : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
      intro h
      have he := hp.getVert_injOn (show n - 1 ≤ p.length by omega)
        (show n + 1 ≤ p.length by omega) h
      omega
    have hbound := two_neighbors_le_weighted x hnonneg hdistinct h1 h2
    rw [hxs _ (p.getVert_mem_support _), hxs _ (p.getVert_mem_support _)] at hbound
    norm_num at hbound ⊢
    exact hbound
  · obtain ⟨j, hjs, hj⟩ : ∃ j ∈ p.support, G.Adj j i := by
      by_contra h
      simp [x, his, h] at hi
    have hxi : x i = 1 := by simp [x, his, show ∃ j ∈ p.support, G.Adj j i from ⟨j, hjs, hj⟩]
    simpa [hxi, hxs j hjs] using
      (neighbor_sum_le_weighted x hnonneg i {j} (by simpa using hj.symm))

private theorem component_neighbor_ncard
    {V : Type*} {G : SimpleGraph V} (C : G.ConnectedComponent) (i : C) :
    (C.toSimpleGraph.neighborSet i).ncard = (G.neighborSet i.val).ncard := by
  let e : C.toSimpleGraph.neighborSet i ≃ G.neighborSet i.val :=
    { toFun j := ⟨j.val.val, j.property⟩
      invFun j := ⟨⟨j.val, C.mem_supp_of_adj_mem_supp i.property j.property⟩, j.property⟩
      left_inv j := rfl
      right_inv j := rfl }
  exact Set.ncard_congr' e

theorem positiveDefiniteComponentTree : GraphShapesSpec.PositiveDefiniteComponentTree.{u, v} := by
  intro Q _ _ _ hacyclic hpos C
  refine ⟨(underlying_acyclic hacyclic hpos).isTree_connectedComponent C, ?_, ?_⟩
  · intro x
    rw [component_neighbor_ncard]
    exact neighbor_ncard_le_three hacyclic hpos x.val
  · intro x y hx hy
    rw [component_neighbor_ncard] at hx hy
    apply Subtype.ext
    exact eq_of_three_le_neighbor_ncard hacyclic hpos
      (C.reachable_of_mem_supp x.property y.property) (le_of_eq hx.symm) (le_of_eq hy.symm)

end Obstructions

section TreeShapes

variable {V : Type u} [Finite V] {G : SimpleGraph V}

private theorem exists_longest_arm {c : V} (a : G.neighborSet c) :
    ∃ (t : V) (p : G.Walk c t), p.IsPath ∧ ¬p.Nil ∧ p.snd = a.val ∧
      ∀ {t' : V} (p' : G.Walk c t'), p'.IsPath → p'.snd = a.val → p'.length ≤ p.length := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let lengths := {n : ℕ | ∃ (t : V) (p : G.Walk c t), p.IsPath ∧ p.snd = a.val ∧ p.length = n}
  have hfinite : lengths.Finite :=
    (Set.finite_lt_nat (Fintype.card V)).subset fun _ ⟨_, _, hp, _, he⟩ => he ▸ hp.length_lt
  have hadj : G.Adj c a.val := a.property
  have hone : 1 ∈ lengths := ⟨a.val, hadj.toWalk, by simpa using hadj.ne, rfl, rfl⟩
  obtain ⟨_, ⟨t, p, hp, hfirst, rfl⟩, hmax⟩ := hfinite.exists_maximal ⟨1, hone⟩
  refine ⟨t, p, hp, ?_, hfirst, fun p' hp' hfirst' => ?_⟩
  · intro hn
    cases hn
    exact hadj.ne hfirst
  · exact le_of_not_gt fun hlt => hmax ⟨_, p', hp', hfirst', rfl⟩ hlt.le |>.not_gt hlt

/-- Any edge out of a noncentral vertex of a maximal arm is an edge of that arm. -/
private theorem adj_toSubgraph_of_maximal_arm
    (ht : G.IsTree) {c t : V} {p : G.Walk c t} (hp : p.IsPath) (hn : ¬p.Nil)
    (hdeg : ∀ v, v ≠ c → (G.neighborSet v).ncard ≤ 2)
    (hmax : ∀ {t' : V} (p' : G.Walk c t'), p'.IsPath → p'.snd = p.snd → p'.length ≤ p.length)
    {x y : V} (hx : x ∈ p.support) (hxc : x ≠ c) (hadj : G.Adj x y) :
    p.toSubgraph.Adj x y := by
  classical
  by_cases hxt : x = t
  · subst x
    have hy : y ∈ p.support := by
      by_contra h
      have hs : (p.concat hadj).snd = p.snd := by
        have hlen : 1 ≤ p.length := Walk.not_nil_iff_lt_length.mp hn
        simp only [Walk.snd, Walk.concat, Walk.getVert_append', ite_eq_left hlen]
      have hlen := hmax (p.concat hadj) (hp.concat h hadj) hs
      simp [Walk.length_concat] at hlen
    have he := ht.isAcyclic.eq_penultimate_of_adj_end hp hadj hy
    rw [he]
    exact (p.toSubgraph_adj_penultimate hn).symm
  · obtain ⟨i, rfl, hle⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    have h0 : i ≠ 0 := by
      rintro rfl
      exact hxc (p.getVert_zero)
    have hi : i < p.length := by
      refine lt_of_le_of_ne hle ?_
      rintro rfl
      exact hxt p.getVert_length
    have hd : (p.toSubgraph.neighborSet (p.getVert i)).ncard = 2 :=
      hp.ncard_neighborSet_toSubgraph_internal_eq_two h0 hi
    have he := Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset (p.getVert i))
      ((hdeg _ hxc).trans (le_of_eq hd.symm))
    change y ∈ p.toSubgraph.neighborSet (p.getVert i)
    rw [he]
    exact hadj

/-- Rooting a tree at its only possible branching vertex partitions the graph
into paths indexed by the neighbors of the root. -/
private theorem exists_rooted_arms (ht : G.IsTree) (c : V)
    (hdeg : ∀ v, v ≠ c → (G.neighborSet v).ncard ≤ 2) :
    ∃ (tip : G.neighborSet c → V) (arm : ∀ a, G.Walk c (tip a)),
      (∀ a, (arm a).IsPath ∧ 0 < (arm a).length ∧ (arm a).snd = a.val) ∧
      (∀ a b, a ≠ b → ∀ x, x ∈ (arm a).support → x ∈ (arm b).support → x = c) ∧
      (∀ x, x = c ∨ ∃ a, x ∈ (arm a).support) ∧
      (∀ x y, G.Adj x y ↔ ∃ a, (arm a).toSubgraph.Adj x y) := by
  classical
  choose tip arm hp hn hfirst hmax using fun a : G.neighborSet c => exists_longest_arm a
  have hstep (x y : V) (hx : x = c ∨ ∃ a, x ∈ (arm a).support) (hxy : G.Adj x y) :
      ∃ a, (arm a).toSubgraph.Adj x y := by
    by_cases hxc : x = c
    · subst x
      let a : G.neighborSet c := ⟨y, hxy⟩
      refine ⟨a, ?_⟩
      have hs : (arm a).snd = y := hfirst a
      simpa only [hs] using (arm a).toSubgraph_adj_snd (hn a)
    · obtain ⟨a, ha⟩ := hx.resolve_left hxc
      exact ⟨a, adj_toSubgraph_of_maximal_arm ht (hp a) (hn a) hdeg
        (fun p hp h => hmax a p hp (h.trans (hfirst a))) ha hxc hxy⟩
  have hwalk {x y : V} (w : G.Walk x y) :
      (x = c ∨ ∃ a, x ∈ (arm a).support) → (y = c ∨ ∃ a, y ∈ (arm a).support) := by
    induction w with
    | nil => exact id
    | @cons x z y h _ ih =>
      intro hx
      obtain ⟨a, ha⟩ := hstep x z hx h
      exact ih (Or.inr ⟨a, (arm a).mem_verts_toSubgraph.mp ((arm a).toSubgraph.edge_vert ha.symm)⟩)
  have hcover (x : V) : x = c ∨ ∃ a, x ∈ (arm a).support := by
    obtain ⟨w⟩ := ht.connected c x
    exact hwalk w (Or.inl rfl)
  refine ⟨tip, arm, fun a => ⟨hp a, Walk.not_nil_iff_lt_length.mp (hn a), hfirst a⟩, ?_,
    hcover, fun x y => ⟨hstep x y (hcover x), ?_⟩⟩
  · intro a b hab x ha hb
    by_contra hx
    have he : (arm a).takeUntil x ha = (arm b).takeUntil x hb :=
      congrArg Subtype.val ((ht.isAcyclic.subsingleton_path c x).elim
        ⟨_, (hp a).takeUntil ha⟩ ⟨_, (hp b).takeUntil hb⟩)
    apply hab
    apply Subtype.ext
    simpa only [Walk.snd_takeUntil hx, hfirst] using congrArg Walk.snd he
  · rintro ⟨a, ha⟩
    exact (arm a).toSubgraph.adj_sub ha

private theorem path_or_three_armed_of_tree (ht : G.IsTree)
    (hdeg : ∀ x, (G.neighborSet x).ncard ≤ 3)
    (hunique : ∀ x y, (G.neighborSet x).ncard = 3 → (G.neighborSet y).ncard = 3 → x = y) :
    IsPathGraph G ∨ IsThreeArmedTree G := by
  classical
  by_cases! hcenter : ∃ x, (G.neighborSet x).ncard = 3
  · obtain ⟨c, hc⟩ := hcenter
    apply Or.inr
    refine ⟨c, hc, exists_rooted_arms ht c ?_⟩
    intro x hx
    have hne : (G.neighborSet x).ncard ≠ 3 := fun he => hx (hunique x c he hc)
    have h := hdeg x
    omega
  · apply Or.inl
    by_cases hnt : Nontrivial V
    · let : Nontrivial V := hnt
      let : Fintype V := Fintype.ofFinite V
      obtain ⟨c, hc⟩ := ht.exists_vert_degree_one_of_nontrivial
      obtain ⟨z, hcz, hu⟩ := (degree_eq_one_iff_existsUnique_adj.mp hc)
      let a : G.neighborSet c := ⟨z, hcz⟩
      have hidx (b : G.neighborSet c) : b = a := Subtype.ext (hu _ b.property)
      obtain ⟨tip, arm, hp, _, hcover, hedge⟩ := exists_rooted_arms ht c (fun x _ => by
        have hd := hdeg x
        have hn := hcenter x
        omega)
      refine ⟨c, tip a, arm a, (hp a).1, ?_, ?_⟩
      · intro x
        rcases hcover x with rfl | ⟨b, hb⟩
        · exact (arm a).start_mem_support
        · rwa [hidx b] at hb
      · intro x y
        rw [hedge]
        exact ⟨fun ⟨b, hb⟩ => hidx b ▸ hb, fun ha => ⟨a, ha⟩⟩
    · let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnt
      obtain ⟨c⟩ := ht.connected.nonempty
      refine ⟨c, c, Walk.nil, Walk.IsPath.nil, fun x => ?_, fun x y => ?_⟩
      · simp [Subsingleton.elim x c]
      · exact ⟨fun h => (h.ne (Subsingleton.elim x y)).elim, fun h => h.adj_sub⟩

end TreeShapes

theorem positiveDefiniteComponentShapes : GraphShapesSpec.PositiveDefiniteComponentShapes.{u, v} := by
  intro Q _ _ _ hacyclic hpos C
  obtain ⟨ht, hd, hu⟩ := positiveDefiniteComponentTree hacyclic hpos C
  exact path_or_three_armed_of_tree ht hd hu

end
end RepTheorySurvey.Quiver.GraphShapes
