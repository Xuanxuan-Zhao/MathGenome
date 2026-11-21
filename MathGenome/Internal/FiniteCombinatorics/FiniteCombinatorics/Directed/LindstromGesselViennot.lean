import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Directed.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Directed.LindstromGesselViennot
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
universe u v r

namespace FiniteCombinatorics.Directed

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]
variable {G : Digraph V A}

namespace Walk

/-- Original arc sequences determine a walk with specified endpoints. -/
theorem arcs_injective {x y : V} : Function.Injective (arcs : Walk G x y → List A) := by
  intro p
  induction p with
  | nil x =>
    intro q h
    cases q with
    | nil => rfl
    | cons b q => cases h
  | @cons x y z a p ih =>
    intro q h
    cases q with
    | nil => cases h
    | @cons _ y' _ b q =>
      have hab : a.val = b.val := (List.cons.inj h).1
      have hy : y = y' := by rw [← a.property.2, ← b.property.2, hab]
      subst y'
      have ha : a = b := Subtype.ext hab
      subst b
      exact congrArg (Walk.cons a) (ih (List.cons.inj h).2)

/-- Every vertex-simple path has strictly fewer arcs than vertices of the graph. -/
theorem IsPath.length_lt_card {x y : V} {p : Walk G x y} (hp : p.IsPath) :
    p.length < Fintype.card V := by
  have h := List.Nodup.length_le_card hp
  change p.vertices.length ≤ Fintype.card V at h
  rw [length_vertices] at h
  exact Nat.lt_of_succ_le h

/-- The initial vertex is included, even for a length-zero walk. -/
theorem start_mem_vertices {x y : V} (p : Walk G x y) : x ∈ p.vertices := by
  obtain ⟨l, hl⟩ := vertices_eq_cons p
  simp [hl]

/-- The terminal vertex is included. -/
theorem end_mem_vertices {x y : V} (p : Walk G x y) : y ∈ p.vertices := by
  exact List.mem_of_mem_getLast? (by simp)

/-- The drop-last convention keeps exactly one copy of the gluing vertex. -/
theorem vertices_dropLast_append_end {x y : V} (p : Walk G x y) :
    p.vertices.dropLast ++ [y] = p.vertices := by
  exact List.dropLast_append_getLast? y (by simp)

/-- Prefix vertices remain vertices after concatenation. -/
theorem vertices_subset_append_left {x y z : V} (p : Walk G x y) (q : Walk G y z) :
    p.vertices ⊆ (p.append q).vertices := by
  intro t ht
  rw [← vertices_dropLast_append_end p, List.mem_append] at ht
  rw [vertices_append, List.mem_append]
  rcases ht with ht | ht
  · exact Or.inl ht
  · have hty : t = y := List.mem_singleton.mp ht
    subst t
    exact Or.inr (start_mem_vertices q)

/-- Suffix vertices remain vertices after concatenation. -/
theorem vertices_subset_append_right {x y z : V} (p : Walk G x y) (q : Walk G y z) :
    q.vertices ⊆ (p.append q).vertices := by
  intro t ht
  rw [vertices_append, List.mem_append]
  exact Or.inr ht

/-- A prefix of a vertex-simple path is vertex-simple. -/
theorem IsPath.of_append_left {x y z : V} {p : Walk G x y} {q : Walk G y z}
    (h : (p.append q).IsPath) : p.IsPath := by
  induction p with
  | nil => exact nil_isPath _ _
  | cons a p ih =>
    change (_ :: (p.append q).vertices).Nodup at h
    change (_ :: p.vertices).Nodup
    exact List.nodup_cons.mpr
      ⟨fun hx => (List.nodup_cons.mp h).1 (vertices_subset_append_left p q hx), ih h.of_cons⟩

/-- A suffix of a vertex-simple path is vertex-simple. -/
theorem IsPath.of_append_right {x y z : V} {p : Walk G x y} {q : Walk G y z}
    (h : (p.append q).IsPath) : q.IsPath := by
  change ((p.append q).vertices).Nodup at h
  rw [vertices_append] at h
  exact (List.nodup_append'.mp h).2.1

/-- Every occurrence of a vertex provides a decomposition into prefix and suffix. -/
theorem exists_split {x y : V} (p : Walk G x y) {z : V} (hz : z ∈ p.vertices) :
    ∃ q : Walk G x z, ∃ s : Walk G z y, p = q.append s := by
  induction p with
  | nil x =>
    have hz : z = x := List.mem_singleton.mp hz
    subst z
    exact ⟨nil x, nil x, rfl⟩
  | @cons x t y a p ih =>
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact ⟨nil x, cons a p, rfl⟩
    · obtain ⟨q, s, hs⟩ := ih hz
      exact ⟨cons a q, s, by rw [cons_append, ← hs]⟩

/-- Closing a path by one incoming arc gives a simple directed cycle. -/
theorem cons_isCycle_of_isPath {x y : V} (a : Arc G x y) (p : Walk G y x)
    (hp : p.IsPath) : (cons a p).IsCycle := by
  have hp' : (p.vertices.dropLast ++ [x]).Nodup := by
    rw [vertices_dropLast_append_end]
    exact hp
  have hx : x ∉ p.vertices.dropLast := by
    intro hx
    exact (List.disjoint_of_nodup_append hp') hx (List.mem_singleton_self x)
  have hd : p.vertices.dropLast.Nodup := (List.nodup_append'.mp hp').1
  change 0 < (cons a p).length ∧ ((cons a p).vertices).dropLast.Nodup
  constructor
  · simp
  · obtain ⟨l, hl⟩ := vertices_eq_cons p
    simpa only [vertices_cons, hl, List.dropLast_cons_cons, List.nodup_cons] using
      (show x ∉ p.vertices.dropLast ∧ p.vertices.dropLast.Nodup from ⟨hx, hd⟩)

/-- The accepted no-simple-cycle definition implies that every directed walk is a path. -/
theorem isPath_of_acyclic (hG : G.Acyclic) {x y : V} (p : Walk G x y) : p.IsPath := by
  induction p with
  | nil => exact nil_isPath _ _
  | @cons x t y a p ih =>
    change (x :: p.vertices).Nodup
    apply List.nodup_cons.mpr
    refine ⟨?_, ih⟩
    intro hx
    obtain ⟨q, s, hs⟩ := p.exists_split hx
    have hq : q.IsPath := IsPath.of_append_left (hs ▸ ih)
    exact hG x (cons a q) (cons_isCycle_of_isPath a q hq)

/-- The final vertex does not occur before the end of a vertex-simple path. -/
theorem IsPath.end_not_mem_dropLast {x y : V} {p : Walk G x y} (hp : p.IsPath) :
    y ∉ p.vertices.dropLast := by
  have hp' : (p.vertices.dropLast ++ [y]).Nodup := by
    rw [vertices_dropLast_append_end]
    exact hp
  intro hy
  exact (List.disjoint_of_nodup_append hp') hy (List.mem_singleton_self y)

/-- A splitting vertex occurs at precisely the length of the prefix. -/
theorem idxOf_vertices_append [DecidableEq V] {x y z : V}
    (p : Walk G x y) (q : Walk G y z) (hp : p.IsPath) :
    (p.append q).vertices.idxOf y = p.length := by
  rw [vertices_append, List.idxOf_append_of_notMem hp.end_not_mem_dropLast]
  obtain ⟨l, hl⟩ := vertices_eq_cons q
  simp only [hl, List.idxOf_cons_self, Nat.add_zero, List.length_dropLast, length_vertices,
    Nat.add_sub_cancel]

/-- Decomposition at a specified vertex is unique on a vertex-simple walk. -/
theorem append_eq_append_unique {x y z : V}
    (p p' : Walk G x y) (q q' : Walk G y z)
    (hp : p.IsPath) (hp' : p'.IsPath) (h : p.append q = p'.append q') :
    p = p' ∧ q = q' := by
  classical
  have hlen : p.length = p'.length := by
    rw [← idxOf_vertices_append p q hp, h, idxOf_vertices_append p' q' hp']
  have harcs := congrArg arcs h
  rw [arcs_append, arcs_append] at harcs
  have heq := List.append_inj harcs hlen
  exact ⟨arcs_injective heq.1, arcs_injective heq.2⟩

/-- A walk cut at a vertex retains the actual original-arc prefix and suffix. -/
structure Cut {x y : V} (p : Walk G x y) (z : V) where
  pre : Walk G x z
  post : Walk G z y
  reconstruct : pre.append post = p

/-- Choose a decomposition; uniqueness below removes all dependence on the choice. -/
noncomputable def cut {x y : V} (p : Walk G x y) (z : V) (hz : z ∈ p.vertices) : Cut p z :=
  Classical.choice (by
    obtain ⟨q, s, hs⟩ := exists_split p hz
    exact ⟨⟨q, s, hs.symm⟩⟩)

/-- Any cut of a vertex-simple walk has a vertex-simple prefix. -/
theorem Cut.pre_isPath {x y z : V} {p : Walk G x y} (c : Cut p z) (hp : p.IsPath) :
    c.pre.IsPath := IsPath.of_append_left (c.reconstruct.symm ▸ hp)

/-- Two decompositions at the same vertex have the same prefix and suffix. -/
theorem Cut.unique {x y z : V} {p : Walk G x y} (c d : Cut p z) (hp : p.IsPath) :
    c.pre = d.pre ∧ c.post = d.post := by
  apply append_eq_append_unique _ _ _ _ (c.pre_isPath hp) (d.pre_isPath hp)
  rw [c.reconstruct, d.reconstruct]

/-- Cutting a concatenation at its gluing vertex recovers the two factors. -/
theorem cut_append {x y z : V} (p : Walk G x y) (q : Walk G y z)
    (hpq : (p.append q).IsPath) (hy : y ∈ (p.append q).vertices) :
    (cut (p.append q) y hy).pre = p ∧ (cut (p.append q) y hy).post = q := by
  exact Cut.unique _ ⟨p, q, rfl⟩ hpq

/-- Switching two suffixes preserves the combined weight, even before invoking acyclicity. -/
theorem tail_switch_weight {R : Type r} [CommMonoid R] (w : A → R)
    {x₁ x₂ z y₁ y₂ : V} (p₁ : Walk G x₁ z) (p₂ : Walk G x₂ z)
    (q₁ : Walk G z y₁) (q₂ : Walk G z y₂) :
    (p₁.append q₂).weight w * (p₂.append q₁).weight w =
      (p₁.append q₁).weight w * (p₂.append q₂).weight w := by
  simp only [weight_append]
  ac_rfl

/-- Switching suffixes preserves the total multiplicity of every vertex. -/
theorem tail_switch_vertex_count [DecidableEq V]
    {x₁ x₂ z y₁ y₂ : V} (p₁ : Walk G x₁ z) (p₂ : Walk G x₂ z)
    (q₁ : Walk G z y₁) (q₂ : Walk G z y₂) (t : V) :
    ((p₁.append q₂).vertices.count t) + ((p₂.append q₁).vertices.count t) =
      ((p₁.append q₁).vertices.count t) + ((p₂.append q₂).vertices.count t) := by
  simp only [vertices_append, List.count_append]
  ac_rfl

/-- A cut prefix is the initial arc segment at the unique vertex occurrence. -/
theorem Cut.arcs_pre [DecidableEq V] {x y z : V} {p : Walk G x y}
    (c : Cut p z) (hp : p.IsPath) :
    c.pre.arcs = p.arcs.take (p.vertices.idxOf z) := by
  have hi : p.vertices.idxOf z = c.pre.length := by
    exact (congrArg (fun q => q.vertices.idxOf z) c.reconstruct).symm.trans
      (idxOf_vertices_append _ _ (c.pre_isPath hp))
  rw [hi]
  have ha := congrArg arcs c.reconstruct
  rw [arcs_append] at ha
  rw [← ha]
  exact List.take_left.symm

/-- The remaining arc segment is the cut suffix. -/
theorem Cut.arcs_post [DecidableEq V] {x y z : V} {p : Walk G x y}
    (c : Cut p z) (hp : p.IsPath) :
    c.post.arcs = p.arcs.drop (p.vertices.idxOf z) := by
  have hi : p.vertices.idxOf z = c.pre.length := by
    exact (congrArg (fun q => q.vertices.idxOf z) c.reconstruct).symm.trans
      (idxOf_vertices_append _ _ (c.pre_isPath hp))
  rw [hi]
  have ha := congrArg arcs c.reconstruct
  rw [arcs_append] at ha
  rw [← ha]
  exact List.drop_left.symm

/-- Equal arc and vertex lists identify both segments of a cut, even across endpoint casts. -/
theorem cut_arcs_of_lists [DecidableEq V] {x y y' z : V}
    (p : Walk G x z) (s : Walk G z y) (q : Walk G x y')
    (hp : p.IsPath) (hq : q.IsPath) (hz : z ∈ q.vertices)
    (hv : q.vertices = (p.append s).vertices) (ha : q.arcs = (p.append s).arcs) :
    (q.cut z hz).pre.arcs = p.arcs ∧ (q.cut z hz).post.arcs = s.arcs := by
  have hi : q.vertices.idxOf z = p.length := by
    rw [hv, idxOf_vertices_append _ _ hp]
  rw [Cut.arcs_pre _ hq, Cut.arcs_post _ hq, hi, ha, arcs_append]
  exact ⟨List.take_left, List.drop_left⟩

end Walk

namespace LGV

/-- This instance is proved from bounded lists of original arcs, not assumed. -/
instance finitePath (G : Digraph V A) (x y : V) : Finite (Spec.path G x y) := by
  let f : Spec.path G x y → {l : List A // l.length < Fintype.card V} :=
    fun p => ⟨p.val.arcs, Walk.IsPath.length_lt_card p.property⟩
  have : Finite {l : List A // l.length < Fintype.card V} := List.finite_length_lt A _
  apply Finite.of_injective f
  intro p q h
  exact Subtype.ext (Walk.arcs_injective (congrArg Subtype.val h))

noncomputable instance pathFintype (G : Digraph V A) (x y : V) : Fintype (Spec.path G x y) :=
  Fintype.ofFinite _

noncomputable instance familyFintype (G : Digraph V A) {n : ℕ}
    (a b : Fin n → V) (σ : Equiv.Perm (Fin n)) : Fintype (Family G a b σ) :=
  inferInstanceAs (Fintype (∀ i : Fin n, Spec.path G (a i) (b (σ i))))

/-- The sums in the independent specification really enumerate all paths. -/
theorem pathWeightSum_eq_sum {R : Type r} [CommRing R] (w : A → R) (x y : V) :
    pathWeightSum G w x y = ∑ p : Spec.path G x y, p.val.weight w := by
  exact finsum_eq_sum_of_fintype _

/-- No acyclicity is needed for the algebraic expansion into simple-path families. -/
theorem determinant_expansion (G : Digraph V A) {R : Type r} [CommRing R]
    (w : A → R) {n : ℕ} (a b : Fin n → V) :
    Matrix.det (pathMatrix G w a b) = allSignedSum G w a b := by
  classical
  unfold allSignedSum
  rw [← Matrix.det_transpose (pathMatrix G w a b), Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  simp only [Matrix.transpose_apply, pathMatrix, pathWeightSum, finsum_eq_sum_of_fintype]
  rw [Fintype.prod_sum]
  rfl

/-- Partition all families into their disjoint and intersecting parts. -/
theorem allSignedSum_eq_add (G : Digraph V A) {R : Type r} [CommRing R]
    (w : A → R) {n : ℕ} (a b : Fin n → V) :
    allSignedSum G w a b = signedSum G w a b + intersectingSignedSum G w a b := by
  classical
  unfold allSignedSum signedSum intersectingSignedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [finsum_eq_sum_of_fintype, ← mul_add]
  congr 1
  exact (Fintype.sum_subtype_add_sum_subtype (VertexDisjoint G) (familyWeight G w)).symm

/-- The remaining graph-theoretic obligation is precisely cancellation. -/
theorem lgv_of_cancellation (G : Digraph V A) {R : Type r} [CommRing R]
    (w : A → R) {n : ℕ} (a b : Fin n → V)
    (hcancel : intersectingSignedSum G w a b = 0) :
    Matrix.det (pathMatrix G w a b) = signedSum G w a b := by
  rw [determinant_expansion, allSignedSum_eq_add, hcancel, add_zero]

/-- Endpoint compatibility removes every nonidentity permutation term. -/
theorem signedSum_eq_unsignedSum (G : Digraph V A) {R : Type r} [CommRing R]
    (w : A → R) {n : ℕ} (a b : Fin n → V)
    (hmatch : ∀ (σ : Equiv.Perm (Fin n)) (P : Family G a b σ),
      VertexDisjoint G P → σ = 1) :
    signedSum G w a b = unsignedSum G w a b := by
  classical
  unfold signedSum unsignedSum
  rw [Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    have : IsEmpty {P : Family G a b σ // VertexDisjoint G P} :=
      ⟨fun P => hσ (hmatch σ P.val P.property)⟩
    simp only [finsum_eq_sum_of_fintype, Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
  · simp

/-- The unsigned conclusion follows once the same cancellation obligation is discharged. -/
theorem lgv_unsigned_of_cancellation (G : Digraph V A) {R : Type r} [CommRing R]
    (w : A → R) {n : ℕ} (a b : Fin n → V)
    (hcancel : intersectingSignedSum G w a b = 0)
    (hmatch : ∀ (σ : Equiv.Perm (Fin n)) (P : Family G a b σ),
      VertexDisjoint G P → σ = 1) :
    Matrix.det (pathMatrix G w a b) = unsignedSum G w a b :=
  (lgv_of_cancellation G w a b hcancel).trans (signedSum_eq_unsignedSum G w a b hmatch)

/-- Both sides include the unique empty family with product one. -/
theorem empty_case (G : Digraph V A) {R : Type r} [CommRing R]
    (w : A → R) (a b : Fin 0 → V) :
    Matrix.det (pathMatrix G w a b) = 1 ∧
      signedSum G w a b = 1 ∧ unsignedSum G w a b = 1 := by
  classical
  have hdisj (σ : Equiv.Perm (Fin 0)) (P : Family G a b σ) : VertexDisjoint G P := by
    intro i
    exact Fin.elim0 i
  have hweight (σ : Equiv.Perm (Fin 0)) (P : Family G a b σ) : familyWeight G w P = 1 := by
    simp [familyWeight]
  have hunique (σ : Equiv.Perm (Fin 0)) : Unique {P : Family G a b σ // VertexDisjoint G P} :=
    { default := ⟨fun i => Fin.elim0 i, hdisj σ _⟩
      uniq := fun P => Subtype.ext (funext fun i => Fin.elim0 i) }
  constructor
  · exact Matrix.det_isEmpty
  constructor
  · simp only [signedSum, hweight, finsum_eq_sum_of_fintype]
    simp
  · simp only [unsignedSum, hweight, finsum_eq_sum_of_fintype]
    simp

/-! ### Tail switches on complete configurations -/

/-- A complete family includes its endpoint permutation. -/
abbrev Configuration (G : Digraph V A) {n : ℕ} (a b : Fin n → V) :=
  Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
    {p : Walk G (a i) (b (σ i)) // Spec.isPath p}

section TailSwitch
variable {n : ℕ} {a b : Fin n → V}

/-- Original arc lists distinguish complete configurations once the permutation agrees. -/
theorem Configuration.ext_arcs (C D : Configuration G a b) (hσ : C.1 = D.1)
    (h : ∀ k, (C.2 k).val.arcs = (D.2 k).val.arcs) : C = D := by
  rcases C with ⟨σ, P⟩
  rcases D with ⟨τ, Q⟩
  dsimp at hσ h
  subst τ
  congr 1
  exact funext fun k => Subtype.ext (Walk.arcs_injective (h k))

/-- Transport only the endpoint indices of a path. -/
def castPath {x x' y y' : V} (hx : x = x') (hy : y = y')
    (p : {p : Walk G x y // Spec.isPath p}) : {p : Walk G x' y' // Spec.isPath p} :=
  hx ▸ hy ▸ p

@[simp] theorem arcs_castPath {x x' y y' : V} (hx : x = x') (hy : y = y')
    (p : {p : Walk G x y // Spec.isPath p}) : (castPath hx hy p).val.arcs = p.val.arcs := by
  subst x'; subst y'; rfl

@[simp] theorem vertices_castPath {x x' y y' : V} (hx : x = x') (hy : y = y')
    (p : {p : Walk G x y // Spec.isPath p}) : (castPath hx hy p).val.vertices = p.val.vertices := by
  subst x'; subst y'; rfl

/-- Exchange suffixes at a specified common vertex; acyclicity makes the new walks paths. -/
noncomputable def switch (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices) : Configuration G a b := by
  classical
  let ci := (C.2 i).val.cut z hi
  let cj := (C.2 j).val.cut z hj
  refine ⟨C.1 * Equiv.swap i j, fun k => ?_⟩
  exact if hki : k = i then
    castPath (congrArg a hki.symm) (by simp [hki])
      (⟨ci.pre.append cj.post, Walk.isPath_of_acyclic hG _⟩ :
        Spec.path G (a i) (b (C.1 j)))
  else if hkj : k = j then
    castPath (congrArg a hkj.symm) (by simp [hkj])
      (⟨cj.pre.append ci.post, Walk.isPath_of_acyclic hG _⟩ :
        Spec.path G (a j) (b (C.1 i)))
  else castPath rfl (by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]) (C.2 k)

@[simp] theorem switch_perm (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices) :
    (switch hG C z i j hi hj).1 = C.1 * Equiv.swap i j := rfl

/-- The switched arc lists explicitly retain original arc identities. -/
theorem switch_arcs (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices) (k : Fin n) :
    ((switch hG C z i j hi hj).2 k).val.arcs =
      if k = i then ((C.2 i).val.cut z hi).pre.arcs ++ ((C.2 j).val.cut z hj).post.arcs
      else if k = j then ((C.2 j).val.cut z hj).pre.arcs ++ ((C.2 i).val.cut z hi).post.arcs
      else (C.2 k).val.arcs := by
  classical
  by_cases hki : k = i
  · subst k
    simp only [switch, dite_true, ite_true]
    erw [arcs_castPath]
    exact Walk.arcs_append _ _
  · by_cases hkj : k = j
    · subst k
      simp only [switch, hki, dite_false, dite_true, ite_false, ite_true]
      erw [arcs_castPath]
      exact Walk.arcs_append _ _
    · simp only [switch, hki, hkj, dite_false, ite_false]
      erw [arcs_castPath]


/-- The vertex lists of a switch, with one copy of each joining vertex. -/
theorem switch_vertices (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices) (k : Fin n) :
    ((switch hG C z i j hi hj).2 k).val.vertices =
      if k = i then ((C.2 i).val.cut z hi).pre.vertices.dropLast ++
        ((C.2 j).val.cut z hj).post.vertices
      else if k = j then ((C.2 j).val.cut z hj).pre.vertices.dropLast ++
        ((C.2 i).val.cut z hi).post.vertices
      else (C.2 k).val.vertices := by
  classical
  by_cases hki : k = i
  · subst k
    simp only [switch, dite_true, ite_true]
    erw [vertices_castPath]
    exact Walk.vertices_append _ _
  · by_cases hkj : k = j
    · subst k
      simp only [switch, hki, dite_false, dite_true, ite_false, ite_true]
      erw [vertices_castPath]
      exact Walk.vertices_append _ _
    · simp only [switch, hki, hkj, dite_false, ite_false]
      erw [vertices_castPath]


/-- Replacing two factors by factors with the same product preserves the full product. -/
@[to_additive /-- Replacing two summands with the same sum preserves the full sum. -/]
theorem prod_congr_two {I M : Type*} [Fintype I] [CommMonoid M]
    (f g : I → M) (i j : I) (hij : i ≠ j)
    (hother : ∀ k, k ≠ i → k ≠ j → f k = g k)
    (hpair : f i * f j = g i * g j) : ∏ k, f k = ∏ k, g k := by
  classical
  rw [← Finset.prod_mul_prod_compl {i, j} f, ← Finset.prod_mul_prod_compl {i, j} g]
  rw [Finset.prod_pair hij, Finset.prod_pair hij, hpair]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact hother k hk.1 hk.2

/-- At the joining vertex, every individual path keeps its membership. -/
theorem switch_mem_join (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices) (k : Fin n) :
    z ∈ ((switch hG C z i j hi hj).2 k).val.vertices ↔ z ∈ (C.2 k).val.vertices := by
  classical
  rw [switch_vertices]
  by_cases hki : k = i
  · subst k
    simp only [ite_true]
    exact iff_of_true (List.mem_append_right _ (Walk.start_mem_vertices _)) hi
  · by_cases hkj : k = j
    · subst k
      simp only [hki, ite_false, ite_true]
      exact iff_of_true (List.mem_append_right _ (Walk.start_mem_vertices _)) hj
    · simp [hki, hkj]

/-- Total vertex multiplicity across the whole configuration. -/
noncomputable def vertexCount (C : Configuration G a b) (z : V) : ℕ := by
  classical
  exact ∑ k, (C.2 k).val.vertices.count z

/-- Tail switching preserves every total vertex multiplicity. -/
theorem switch_vertexCount (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hij : i ≠ j) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices) :
    vertexCount (switch hG C z i j hi hj) = vertexCount C := by
  classical
  funext t
  unfold vertexCount
  apply sum_congr_two _ _ i j hij
  · intro k hki hkj
    rw [switch_vertices]
    simp [hki, hkj]
  · simp only [switch_vertices, ite_true, hij.symm, ite_false, List.count_append]
    have hci := congrArg (fun p => p.vertices.count t) ((C.2 i).val.cut z hi).reconstruct
    have hcj := congrArg (fun p => p.vertices.count t) ((C.2 j).val.cut z hj).reconstruct
    rw [Walk.vertices_append, List.count_append] at hci hcj
    rw [← hci, ← hcj]
    ac_rfl

/-- Switching preserves the weight in any commutative ring. -/
theorem switch_weight (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hij : i ≠ j) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices) {R : Type r} [CommRing R] (w : A → R) :
    familyWeight G w (switch hG C z i j hi hj).2 = familyWeight G w C.2 := by
  classical
  unfold familyWeight
  change (∏ k, (((switch hG C z i j hi hj).2 k).val.arcs.map w).prod) =
    ∏ k, (((C.2 k).val.arcs).map w).prod
  apply prod_congr_two _ _ i j hij
  · intro k hki hkj
    rw [switch_arcs]
    simp [hki, hkj]
  · simp only [switch_arcs, ite_true, hij.symm, ite_false, List.map_append, List.prod_append]
    have hci := congrArg (fun p => (p.arcs.map w).prod) ((C.2 i).val.cut z hi).reconstruct
    have hcj := congrArg (fun p => (p.arcs.map w).prod) ((C.2 j).val.cut z hj).reconstruct
    rw [Walk.arcs_append, List.map_append, List.prod_append] at hci hcj
    rw [← hci, ← hcj]
    ac_rfl

/-- Cutting the first switched path recovers its old prefix and its partner's suffix. -/
theorem switch_cut_arcs_left (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices)
    (hi' : z ∈ ((switch hG C z i j hi hj).2 i).val.vertices) :
    (((switch hG C z i j hi hj).2 i).val.cut z hi').pre.arcs =
      ((C.2 i).val.cut z hi).pre.arcs ∧
    (((switch hG C z i j hi hj).2 i).val.cut z hi').post.arcs =
      ((C.2 j).val.cut z hj).post.arcs := by
  classical
  apply Walk.cut_arcs_of_lists _ _ _
    (((C.2 i).val.cut z hi).pre_isPath (C.2 i).property)
    ((switch hG C z i j hi hj).2 i).property hi'
  · simp only [switch_vertices, ite_true, Walk.vertices_append]
  · simp only [switch_arcs, ite_true, Walk.arcs_append]

/-- The other switched path recovers the complementary two segments. -/
theorem switch_cut_arcs_right (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hij : i ≠ j) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices)
    (hj' : z ∈ ((switch hG C z i j hi hj).2 j).val.vertices) :
    (((switch hG C z i j hi hj).2 j).val.cut z hj').pre.arcs =
      ((C.2 j).val.cut z hj).pre.arcs ∧
    (((switch hG C z i j hi hj).2 j).val.cut z hj').post.arcs =
      ((C.2 i).val.cut z hi).post.arcs := by
  classical
  apply Walk.cut_arcs_of_lists _ _ _
    (((C.2 j).val.cut z hj).pre_isPath (C.2 j).property)
    ((switch hG C z i j hi hj).2 j).property hj'
  · simp only [switch_vertices, hij.symm, ite_false, ite_true, Walk.vertices_append]
  · simp only [switch_arcs, hij.symm, ite_false, ite_true, Walk.arcs_append]

/-- At a fixed intersection and pair, switching twice restores every original arc. -/
theorem switch_switch (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hij : i ≠ j) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices)
    (hi' : z ∈ ((switch hG C z i j hi hj).2 i).val.vertices)
    (hj' : z ∈ ((switch hG C z i j hi hj).2 j).val.vertices) :
    switch hG (switch hG C z i j hi hj) z i j hi' hj' = C := by
  classical
  apply Configuration.ext_arcs
  · simp only [switch_perm, mul_assoc, Equiv.swap_mul_self, mul_one]
  · intro k
    rw [switch_arcs]
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
      rw [(switch_cut_arcs_left hG C z i j hi hj hi').1,
        (switch_cut_arcs_right hG C z i j hij hi hj hj').2]
      exact (Walk.arcs_append _ _).symm.trans
        (congrArg Walk.arcs ((C.2 i).val.cut z hi).reconstruct)
    · by_cases hkj : k = j
      · subst k
        simp only [hki, ite_false, ite_true]
        rw [(switch_cut_arcs_right hG C z i j hij hi hj hj').1,
          (switch_cut_arcs_left hG C z i j hi hj hi').2]
        exact (Walk.arcs_append _ _).symm.trans
          (congrArg Walk.arcs ((C.2 j).val.cut z hj).reconstruct)
      · simp only [hki, hkj, ite_false, switch_arcs]

/-- Distinct chosen indices ensure that the switch has no fixed point. -/
theorem switch_ne (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hij : i ≠ j) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices) : switch hG C z i j hi hj ≠ C := by
  intro h
  have hs : C.1 * Equiv.swap i j = C.1 * 1 := by
    simpa only [switch_perm, mul_one] using congrArg Sigma.fst h
  have ht := congrArg (fun σ : Equiv.Perm (Fin n) => σ i) (mul_left_cancel hs)
  exact hij (by simpa using ht.symm)

/-- A switch reverses the signed weight over every commutative ring. -/
theorem switch_signedWeight (hG : G.Acyclic) (C : Configuration G a b)
    (z : V) (i j : Fin n) (hij : i ≠ j) (hi : z ∈ (C.2 i).val.vertices)
    (hj : z ∈ (C.2 j).val.vertices) {R : Type r} [CommRing R] (w : A → R) :
    ((Equiv.Perm.sign (switch hG C z i j hi hj).1 : ℤ) : R) *
        familyWeight G w (switch hG C z i j hi hj).2 =
      - (((Equiv.Perm.sign C.1 : ℤ) : R) * familyWeight G w C.2) := by
  classical
  rw [switch_weight hG C z i j hij hi hj w, switch_perm,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  simp

end TailSwitch

/-! ### Intersections detected by total vertex multiplicities -/

section CanonicalSwitch
variable {n : ℕ} {a b : Fin n → V}

theorem two_le_vertexCount_of_pair (C : Configuration G a b) (z : V)
    (i j : Fin n) (hij : i ≠ j)
    (hi : z ∈ (C.2 i).val.vertices) (hj : z ∈ (C.2 j).val.vertices) :
    2 ≤ vertexCount C z := by
  classical
  have hci : (C.2 i).val.vertices.count z = 1 :=
    List.Nodup.count_of_mem (C.2 i).property hi
  have hcj : (C.2 j).val.vertices.count z = 1 :=
    List.Nodup.count_of_mem (C.2 j).property hj
  have h := Finset.sum_le_sum_of_subset (f := fun k => (C.2 k).val.vertices.count z)
    (s := {i, j}) (t := Finset.univ) (Finset.subset_univ _)
  simpa [Finset.sum_pair hij, hci, hcj, vertexCount] using h

theorem exists_pair_of_vertexCount (C : Configuration G a b) (z : V)
    (hz : 2 ≤ vertexCount C z) :
    ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ z ∈ (C.2 p.1).val.vertices ∧
      z ∈ (C.2 p.2).val.vertices := by
  classical
  by_contra hnone
  have hcount : vertexCount C z ≤ 1 := by
    unfold vertexCount
    apply Finset.sum_le_one_iff.mpr
    intro i j _ _ hi hj
    have hmi : z ∈ (C.2 i).val.vertices :=
      List.count_pos_iff.mp (Nat.pos_of_ne_zero hi)
    have hmj : z ∈ (C.2 j).val.vertices :=
      List.count_pos_iff.mp (Nat.pos_of_ne_zero hj)
    constructor
    · by_contra hij
      exact hnone ⟨(i,j), hij, hmi, hmj⟩
    · exact List.Nodup.count_of_mem (C.2 i).property hmi
  omega

theorem not_vertexDisjoint_iff_exists_vertexCount (C : Configuration G a b) :
    ¬ VertexDisjoint G C.2 ↔ ∃ z, 2 ≤ vertexCount C z := by
  classical
  constructor
  · contrapose!
    intro hcount i j hij
    apply List.disjoint_left.mpr
    intro z hi hj
    exact (Nat.not_le_of_lt (hcount z)) (two_le_vertexCount_of_pair C z i j hij hi hj)
  · rintro ⟨z, hz⟩ hdisj
    obtain ⟨⟨i,j⟩, hij, hi, hj⟩ := exists_pair_of_vertexCount C z hz
    exact (List.disjoint_left.mp (hdisj i j hij)) hi hj

/-! ### Canonical switches of intersecting families -/

/-- A vertex selector depending only on the total vertex multiplicity function. -/
noncomputable def selectIntersectionVertex (f : V → ℕ) (hf : ∃ z, 2 ≤ f z) : V :=
  Classical.choose hf

omit [Fintype V] in
theorem selectIntersectionVertex_spec (f : V → ℕ) (hf : ∃ z, 2 ≤ f z) :
    2 ≤ f (selectIntersectionVertex f hf) := Classical.choose_spec hf

omit [Fintype V] in
theorem selectIntersectionVertex_congr {f g : V → ℕ} (hf : ∃ z, 2 ≤ f z)
    (hg : ∃ z, 2 ≤ g z) (h : f = g) :
    selectIntersectionVertex f hf = selectIntersectionVertex g hg := by
  subst g
  rfl

/-- The index-pair selector depends only on which paths contain the joining vertex. -/
noncomputable def selectIntersectionPair (s : Fin n → Prop)
    (hs : ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ s p.1 ∧ s p.2) : Fin n × Fin n :=
  Classical.choose hs

theorem selectIntersectionPair_spec (s : Fin n → Prop)
    (hs : ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ s p.1 ∧ s p.2) :
    (selectIntersectionPair s hs).1 ≠ (selectIntersectionPair s hs).2 ∧
      s (selectIntersectionPair s hs).1 ∧ s (selectIntersectionPair s hs).2 :=
  Classical.choose_spec hs

theorem selectIntersectionPair_congr {s t : Fin n → Prop}
    (hs : ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ s p.1 ∧ s p.2)
    (ht : ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ t p.1 ∧ t p.2) (h : s = t) :
    selectIntersectionPair s hs = selectIntersectionPair t ht := by
  subst t
  rfl

/-- Choose solely from total multiplicities, which every tail switch preserves.
The following pair choice depends solely on membership at that selected vertex,
which the switch also preserves. Thus both choices are unchanged by switching. -/
noncomputable def collisionVertex (C : Configuration G a b)
    (hC : ¬VertexDisjoint G C.2) : V :=
  selectIntersectionVertex (vertexCount C)
    ((not_vertexDisjoint_iff_exists_vertexCount C).mp hC)

theorem collisionVertex_spec (C : Configuration G a b)
    (hC : ¬VertexDisjoint G C.2) : 2 ≤ vertexCount C (collisionVertex C hC) :=
  selectIntersectionVertex_spec _ _

theorem collisionVertex_eq_of_counts (C D : Configuration G a b)
    (hC : ¬VertexDisjoint G C.2) (hD : ¬VertexDisjoint G D.2)
    (h : vertexCount C = vertexCount D) : collisionVertex C hC = collisionVertex D hD :=
  selectIntersectionVertex_congr _ _ h

noncomputable def collisionPair (C : Configuration G a b)
    (hC : ¬VertexDisjoint G C.2) : Fin n × Fin n :=
  selectIntersectionPair (fun k => collisionVertex C hC ∈ (C.2 k).val.vertices)
    (exists_pair_of_vertexCount C _ (collisionVertex_spec C hC))

theorem collisionPair_spec (C : Configuration G a b)
    (hC : ¬VertexDisjoint G C.2) :
    (collisionPair C hC).1 ≠ (collisionPair C hC).2 ∧
      collisionVertex C hC ∈ (C.2 (collisionPair C hC).1).val.vertices ∧
      collisionVertex C hC ∈ (C.2 (collisionPair C hC).2).val.vertices :=
  selectIntersectionPair_spec _ _

/-- Complete configurations whose paths intersect. -/
abbrev BadConfiguration (G : Digraph V A) {n : ℕ} (a b : Fin n → V) :=
  {C : Configuration G a b // ¬ VertexDisjoint G C.2}

/-- The selected vertex and pair define a tail switch without any arbitrary family choices. -/
noncomputable def badSwitch (hG : G.Acyclic) (C : BadConfiguration G a b) :
    BadConfiguration G a b := by
  let z := collisionVertex C.val C.property
  let p := collisionPair C.val C.property
  have hp := collisionPair_spec C.val C.property
  refine ⟨switch hG C.val z p.1 p.2 hp.2.1 hp.2.2, ?_⟩
  intro hd
  exact hd p.1 p.2 hp.1
    ((switch_mem_join hG C.val z p.1 p.2 hp.2.1 hp.2.2 p.1).mpr hp.2.1)
    ((switch_mem_join hG C.val z p.1 p.2 hp.2.1 hp.2.2 p.2).mpr hp.2.2)

/-- The switch retains the entire multiplicity function used to choose the vertex. -/
theorem badSwitch_vertexCount (hG : G.Acyclic) (C : BadConfiguration G a b) :
    vertexCount (badSwitch hG C).val = vertexCount C.val :=
  switch_vertexCount hG _ _ _ _ (collisionPair_spec C.val C.property).1 _ _

theorem collisionVertex_badSwitch (hG : G.Acyclic) (C : BadConfiguration G a b) :
    collisionVertex (badSwitch hG C).val (badSwitch hG C).property =
      collisionVertex C.val C.property :=
  collisionVertex_eq_of_counts _ _ _ _ (badSwitch_vertexCount hG C)

/-- Membership of each individual path at the selected vertex is unchanged. -/
theorem collisionPair_badSwitch (hG : G.Acyclic) (C : BadConfiguration G a b) :
    collisionPair (badSwitch hG C).val (badSwitch hG C).property =
      collisionPair C.val C.property := by
  apply selectIntersectionPair_congr
  funext k
  apply propext
  rw [collisionVertex_badSwitch]
  exact switch_mem_join hG C.val _ _ _ _ _ k

/-- Applying the canonical switch twice restores the original configuration. -/
theorem badSwitch_involutive (hG : G.Acyclic) :
    Function.Involutive (badSwitch (a := a) (b := b) hG) := by
  intro C
  apply Subtype.ext
  change switch hG (badSwitch hG C).val
    (collisionVertex (badSwitch hG C).val (badSwitch hG C).property)
    (collisionPair (badSwitch hG C).val (badSwitch hG C).property).1
    (collisionPair (badSwitch hG C).val (badSwitch hG C).property).2 _ _ = C.val
  simp only [collisionVertex_badSwitch, collisionPair_badSwitch]
  exact switch_switch hG C.val _ _ _ (collisionPair_spec C.val C.property).1 _ _ _ _

/-- The transposed pair consists of distinct indices, so the switch has no fixed point. -/
theorem badSwitch_ne (hG : G.Acyclic) (C : BadConfiguration G a b) :
    badSwitch hG C ≠ C := by
  intro h
  exact switch_ne hG C.val _ _ _ (collisionPair_spec C.val C.property).1 _ _
    (congrArg Subtype.val h)

theorem badSwitch_weight (hG : G.Acyclic) (C : BadConfiguration G a b)
    {R : Type r} [CommRing R] (w : A → R) :
    familyWeight G w (badSwitch hG C).val.2 = familyWeight G w C.val.2 :=
  switch_weight hG C.val _ _ _ (collisionPair_spec C.val C.property).1 _ _ w

/-- Canonical switching preserves the magnitude and reverses the permutation sign. -/
theorem badSwitch_signedWeight (hG : G.Acyclic) (C : BadConfiguration G a b)
    {R : Type r} [CommRing R] (w : A → R) :
    ((Equiv.Perm.sign (badSwitch hG C).val.1 : ℤ) : R) *
        familyWeight G w (badSwitch hG C).val.2 =
      -(((Equiv.Perm.sign C.val.1 : ℤ) : R) * familyWeight G w C.val.2) :=
  switch_signedWeight hG C.val _ _ _ (collisionPair_spec C.val C.property).1 _ _ w

noncomputable instance configurationFintype (G : Digraph V A) {n : ℕ}
    (a b : Fin n → V) : Fintype (Configuration G a b) :=
  inferInstanceAs (Fintype (Σ σ, Family G a b σ))

noncomputable instance badConfigurationFintype (G : Digraph V A) {n : ℕ}
    (a b : Fin n → V) : Fintype (BadConfiguration G a b) := by
  classical
  exact inferInstanceAs (Fintype {C : Configuration G a b // ¬VertexDisjoint G C.2})

/-- Reshape the intersecting configurations as a permutation and an intersecting family. -/
def badConfigurationEquiv : BadConfiguration G a b ≃
    Σ σ : Equiv.Perm (Fin n), {P : Family G a b σ // ¬VertexDisjoint G P} where
  toFun C := ⟨C.val.1, ⟨C.val.2, C.property⟩⟩
  invFun C := ⟨⟨C.1, C.2.val⟩, C.2.property⟩

/-- The nested sum is the single sum over intersecting configurations. -/
theorem intersectingSignedSum_eq_sum {R : Type r} [CommRing R] (w : A → R) :
    intersectingSignedSum G w a b =
      ∑ C : BadConfiguration G a b,
        ((Equiv.Perm.sign C.val.1 : ℤ) : R) * familyWeight G w C.val.2 := by
  classical
  unfold intersectingSignedSum
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
  calc
    _ = ∑ C : (Σ σ : Equiv.Perm (Fin n),
        {P : Family G a b σ // ¬VertexDisjoint G P}),
        ((Equiv.Perm.sign C.1 : ℤ) : R) * familyWeight G w C.2.val :=
      (Fintype.sum_sigma _).symm
    _ = _ := (Fintype.sum_equiv badConfigurationEquiv _ _ (fun _ => rfl)).symm

/-- A fixed-point-free involution that negates each signed term cancels the sum. -/
theorem intersectingSignedSum_eq_zero_of_involution {R : Type r} [CommRing R]
    (w : A → R) (f : BadConfiguration G a b → BadConfiguration G a b)
    (hf : Function.Involutive f) (hne : ∀ C, f C ≠ C)
    (hneg : ∀ C, ((Equiv.Perm.sign (f C).val.1 : ℤ) : R) *
        familyWeight G w (f C).val.2 =
      -(((Equiv.Perm.sign C.val.1 : ℤ) : R) * familyWeight G w C.val.2)) :
    intersectingSignedSum G w a b = 0 := by
  classical
  rw [intersectingSignedSum_eq_sum]
  exact Finset.sum_ninvolution f (fun C => by rw [hneg]; exact add_neg_cancel _)
    (fun C _ => hne C) (fun _ => Finset.mem_univ _) hf

/-- Intersecting families cancel in pairs over an arbitrary commutative ring. -/
theorem intersectingSignedSum_eq_zero (hG : G.Acyclic)
    {R : Type r} [CommRing R] (w : A → R) :
    intersectingSignedSum G w a b = 0 :=
  intersectingSignedSum_eq_zero_of_involution w (badSwitch hG)
    (badSwitch_involutive hG) (badSwitch_ne hG) (fun C => badSwitch_signedWeight hG C w)

end CanonicalSwitch

/-- The signed Lindström–Gessel–Viennot identity for the original arc-weighted graph. -/
theorem lgv (G : Digraph V A) (hG : Spec.acyclic G)
    {R : Type r} [CommRing R] (w : A → R) {n : ℕ} (a b : Fin n → V)
    (_ha : Function.Injective a) (_hb : Function.Injective b) :
    Matrix.det (pathMatrix G w a b) = signedSum G w a b :=
  lgv_of_cancellation G w a b (intersectingSignedSum_eq_zero hG w)

/-- If disjoint families force the identity matching, the path determinant is unsigned. -/
theorem lgv_unsigned (G : Digraph V A) (hG : Spec.acyclic G)
    {R : Type r} [CommRing R] (w : A → R) {n : ℕ} (a b : Fin n → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hmatch : ∀ (σ : Equiv.Perm (Fin n)) (P : Family G a b σ),
      VertexDisjoint G P → σ = 1) :
    Matrix.det (pathMatrix G w a b) = unsignedSum G w a b :=
  (lgv G hG w a b ha hb).trans (signedSum_eq_unsignedSum G w a b hmatch)


end LGV
end FiniteCombinatorics.Directed
