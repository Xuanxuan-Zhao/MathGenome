import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DynkinExhaustion
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanMatrix
import Mathlib.Tactic.FieldSimp

/-! Exhaustion and uniqueness of the finite oriented Dynkin diagrams (LA-E05).
Source: res:E05, notes/005/lie-algebras-and-representations.tex:2170–2241.

Positive definiteness first excludes cycles, extra branches and multiple edges.
A connected diagram is then a chain or three single-edge arms. Exact Cartan
reindexings identify all allowed shapes, including both multiple-edge orientations.
Coordinate realization of the labels is allocated to LA-E06 and its children. -/
noncomputable section
open SimpleGraph
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

lemma IsAcyclic.adj_getVert_iff {p : G.Walk u v} (hG : G.IsAcyclic) (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro hadj
    have hij : i ≠ j := by intro h; subst j; exact G.irrefl hadj
    have forward {a b : ℕ} (ha : a ≤ p.length) (hb : b ≤ p.length)
        (hab : a < b) (hadj : G.Adj (p.getVert a) (p.getVert b)) : a + 1 = b := by
      have hsupp : p.getVert a ∈ (p.take b).support := by
        apply Walk.mem_support_iff_exists_getVert.mpr
        refine ⟨a, ?_, ?_⟩
        · simp [Walk.take_getVert, Nat.min_eq_right (Nat.le_of_lt hab)]
        · simp [Walk.take_length, min_eq_left hb]
          omega
      have heq := hG.eq_penultimate_of_adj_end (hp.take b) hadj.symm hsupp
      have heq' : p.getVert a = p.getVert (b - 1) := by
        simpa [Walk.penultimate, Walk.take_length, min_eq_left hb,
          Walk.take_getVert, min_eq_right (show b - 1 ≤ b by omega)] using heq
      have := hp.getVert_injOn ha (show b - 1 ≤ p.length by omega) heq'
      omega
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (forward hi hj h hadj)
    · exact Or.inr (forward hj hi h hadj.symm)
  · rintro (h | h)
    · subst j
      exact p.adj_getVert_succ (by omega)
    · subst i
      exact (p.adj_getVert_succ (by omega)).symm

lemma Walk.IsPath.mem_support_of_maximal_of_degree_le_two {p : G.Walk u v}
    (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsPath), p'.length ≤ p.length)
    (hdeg : ∀ (x a b c : V), G.Adj x a → G.Adj x b → G.Adj x c →
      a = b ∨ a = c ∨ b = c)
    {x y : V} (hx : x ∈ p.support) (hxy : G.Adj x y) : y ∈ p.support := by
  classical
  by_contra hy
  obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hi0 : i = 0
  · have hxu : x = u := by simpa [hi0] using hix.symm
    rw [hxu] at hxy
    have hnew : (Walk.cons hxy.symm p).IsPath := hp.cons hy
    have := hmax _ _ _ hnew
    simp at this
  by_cases hilast : i = p.length
  · have hxv : x = v := by simpa [hilast] using hix.symm
    rw [hxv] at hxy
    have hnew : (p.concat hxy).IsPath := hp.concat hy hxy
    have := hmax _ _ _ hnew
    simp at this
  have hadj₁ : G.Adj x (p.getVert (i - 1)) := by
    have := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa [Nat.sub_add_cancel (show 1 ≤ i by omega), hix] using this
  have hadj₂ : G.Adj x (p.getVert (i + 1)) := by
    simpa [hix] using p.adj_getVert_succ (i := i) (by omega)
  have hne₁ : y ≠ p.getVert (i - 1) := by
    intro h
    exact hy (h ▸ p.getVert_mem_support (i - 1))
  have hne₂ : y ≠ p.getVert (i + 1) := by
    intro h
    exact hy (h ▸ p.getVert_mem_support (i + 1))
  have hne₃ : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro h
    have := hp.getVert_injOn (show i - 1 ≤ p.length by omega)
      (show i + 1 ≤ p.length by omega) h
    omega
  exact (hdeg x y (p.getVert (i - 1)) (p.getVert (i + 1)) hxy hadj₁ hadj₂).elim
    hne₁ (fun h => h.elim hne₂ hne₃)

/-- A finite connected graph whose vertices have at most two neighbors has a
spanning simple path. -/
lemma Connected.exists_spanning_path_of_degree_le_two [Finite V] (hconn : G.Connected)
    (hdeg : ∀ (x a b c : V), G.Adj x a → G.Adj x b → G.Adj x c →
      a = b ∨ a = c ∨ b = c) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ∀ x, x ∈ p.support := by
  classical
  have : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨u, v, p, hp, ?_⟩
  have hclosed : ∀ {a b : V} (q : G.Walk a b), a ∈ p.support → b ∈ p.support := by
    intro a b q
    induction q with
    | nil => exact id
    | cons h q ih =>
      intro ha
      exact ih (hp.mem_support_of_maximal_of_degree_le_two hmax hdeg ha h)
  intro x
  obtain ⟨q⟩ := hconn u x
  exact hclosed q p.start_mem_support

/-- Every finite tree of maximum valence two is a chain, with an explicit
vertex equivalence retaining exactly the consecutive adjacencies. -/
lemma IsTree.exists_chain_equiv [Finite V] (ht : G.IsTree)
    (hdeg : ∀ (x a b c : V), G.Adj x a → G.Adj x b → G.Adj x c →
      a = b ∨ a = c ∨ b = c) :
    ∃ (n : ℕ) (e : Fin (n + 1) ≃ V), ∀ i j,
      G.Adj (e i) (e j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨u, v, p, hp, hspan⟩ := ht.connected.exists_spanning_path_of_degree_le_two hdeg
  let f : Fin (p.length + 1) → V := fun i => p.getVert i.val
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (show i.val ≤ p.length by omega)
        (show j.val ≤ p.length by omega) hij
    · intro x
      obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hspan x)
      exact ⟨⟨i, by omega⟩, hix⟩
  refine ⟨p.length, Equiv.ofBijective f hf, ?_⟩
  intro i j
  exact ht.isAcyclic.adj_getVert_iff hp (by omega) (by omega)

/-- A neighbor outside a simple path cannot also be adjacent to its other
endpoint in an acyclic graph. -/
lemma IsAcyclic.not_adj_end_of_adj_start_notMem {p : G.Walk u v}
    (hG : G.IsAcyclic) (hp : p.IsPath) (huv : u ≠ v)
    {w : V} (hu : G.Adj u w) (hw : w ∉ p.support) : ¬G.Adj v w := by
  intro hv
  apply hw
  apply hG.mem_support_of_ne_mem_support_of_adj_of_isPath hp hu.isPath_toWalk hv
  simp only [hu.support_toWalk, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨huv.symm, hv.ne⟩

/-- At least two of any three distinct neighbors of the initial endpoint of
a simple path lie outside the path. -/
lemma IsAcyclic.exists_two_external_neighbors {p : G.Walk u v}
    (hG : G.IsAcyclic) (hp : p.IsPath)
    (e : Fin 3 ↪ V) (he : ∀ i, G.Adj u (e i)) :
    ∃ a : Fin 2 ↪ V, (∀ i, G.Adj u (a i)) ∧ ∀ i, a i ∉ p.support := by
  classical
  have hout (i : Fin 3) (hi : e i ≠ p.snd) : e i ∉ p.support := by
    intro hs
    exact hi (hG.eq_snd_of_adj_start hp (he i) hs)
  have build (i j : Fin 3) (hij : i ≠ j) (hi : e i ≠ p.snd) (hj : e j ≠ p.snd) :
      ∃ a : Fin 2 ↪ V, (∀ k, G.Adj u (a k)) ∧ ∀ k, a k ∉ p.support := by
    let a : Fin 2 ↪ V := ⟨![e i, e j], by
      intro k l h
      fin_cases k <;> fin_cases l <;> simp_all [e.injective.ne hij]⟩
    refine ⟨a, ?_, ?_⟩
    · intro k
      fin_cases k <;> exact he _
    · intro k
      fin_cases k
      · exact hout i hi
      · exact hout j hj
  by_cases h0 : e 0 = p.snd
  · exact build 1 2 (by decide)
      (by rw [← h0]; exact e.injective.ne (by decide))
      (by rw [← h0]; exact e.injective.ne (by decide))
  by_cases h1 : e 1 = p.snd
  · exact build 0 2 (by decide) h0
      (by rw [← h1]; exact e.injective.ne (by decide))
  exact build 0 1 (by decide) h0 h1

/-- The vertex enumeration of a path together with any disjoint external
vertices is injective. -/
def Walk.IsPath.embeddingWithExternal {κ : Type*} {p : G.Walk u v}
    (hp : p.IsPath) (f : κ ↪ V) (hf : ∀ k, f k ∉ p.support) :
    Fin (p.length + 1) ⊕ κ ↪ V where
  toFun := Sum.elim (fun i => p.getVert i.val) f
  inj' := by
    intro i j h
    rcases i with i | i <;> rcases j with j | j
    · apply congrArg Sum.inl
      apply Fin.ext
      exact hp.getVert_injOn (show i.val ≤ p.length by omega)
        (show j.val ≤ p.length by omega) h
    · change p.getVert i.val = f j at h
      exact (hf j (h ▸ p.getVert_mem_support i.val)).elim
    · change f i = p.getVert j.val at h
      exact (hf i (h.symm ▸ p.getVert_mem_support j.val)).elim
    · exact congrArg Sum.inr (f.injective h)

/-- In a tree, any two distinct trivalent vertices exhibit a path with two
extra neighbors at each endpoint. The four retained neighbors are distinct
from each other and from the entire path. -/
lemma IsTree.exists_path_four_neighbors (ht : G.IsTree)
    {x y : V} (hxy : x ≠ y)
    (ex ey : Fin 3 ↪ V) (hx : ∀ i, G.Adj x (ex i)) (hy : ∀ i, G.Adj y (ey i)) :
    ∃ (n : ℕ) (e : Fin (n + 1) ⊕ Fin 4 ↪ V),
      e (.inl 0) = x ∧ e (.inl (Fin.last n)) = y ∧
      (∀ i j : Fin (n + 1), i.val + 1 = j.val → G.Adj (e (.inl i)) (e (.inl j))) ∧
      G.Adj (e (.inl 0)) (e (.inr 0)) ∧
      G.Adj (e (.inl 0)) (e (.inr 1)) ∧
      G.Adj (e (.inl (Fin.last n))) (e (.inr 2)) ∧
      G.Adj (e (.inl (Fin.last n))) (e (.inr 3)) := by
  classical
  obtain ⟨p, hp⟩ := (ht.connected x y).exists_isPath
  obtain ⟨a, ha, haout⟩ := ht.isAcyclic.exists_two_external_neighbors hp ex hx
  obtain ⟨b, hb, hbout'⟩ := ht.isAcyclic.exists_two_external_neighbors hp.reverse ey hy
  have hbout (i) : b i ∉ p.support := by simpa using hbout' i
  have hab (i j : Fin 2) : a i ≠ b j := by
    intro heq
    exact ht.isAcyclic.not_adj_end_of_adj_start_notMem hp hxy (ha i) (haout i) (heq ▸ hb j)
  let f : Fin 4 ↪ V := ⟨![a 0, a 1, b 0, b 1], by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [a.injective.ne (by decide : (0 : Fin 2) ≠ 1),
        b.injective.ne (by decide : (0 : Fin 2) ≠ 1), hab, Ne.symm]⟩
  have hf : ∀ i, f i ∉ p.support := by
    intro i
    fin_cases i
    · exact haout 0
    · exact haout 1
    · exact hbout 0
    · exact hbout 1
  let e := hp.embeddingWithExternal f hf
  refine ⟨p.length, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact p.getVert_zero
  · exact p.getVert_length
  · intro i j hij
    change G.Adj (p.getVert i.val) (p.getVert j.val)
    rw [← hij]
    exact p.adj_getVert_succ (by omega)
  · change G.Adj (p.getVert 0) (a 0)
    simpa using ha 0
  · change G.Adj (p.getVert 0) (a 1)
    simpa using ha 1
  · change G.Adj (p.getVert p.length) (b 0)
    simpa using hb 0
  · change G.Adj (p.getVert p.length) (b 1)
    simpa using hb 1

/-- A branch and any given edge in a tree can be joined by a path with two
external branch neighbors and the opposite endpoint of the edge external. -/
lemma IsTree.exists_path_branch_edge (ht : G.IsTree) (x y z : V)
    (ex : Fin 3 ↪ V) (hx : ∀ i, G.Adj x (ex i)) (hyz : G.Adj y z) :
    ∃ (n : ℕ) (e : Fin (n + 1) ⊕ Fin 3 ↪ V),
      e (.inl 0) = x ∧
      (∀ i j : Fin (n + 1), i.val + 1 = j.val → G.Adj (e (.inl i)) (e (.inl j))) ∧
      G.Adj (e (.inl 0)) (e (.inr 0)) ∧
      G.Adj (e (.inl 0)) (e (.inr 1)) ∧
      ((e (.inl (Fin.last n)) = y ∧ e (.inr 2) = z) ∨
        (e (.inl (Fin.last n)) = z ∧ e (.inr 2) = y)) := by
  classical
  have build {u v : V} (horder : (u = y ∧ v = z) ∨ (u = z ∧ v = y))
      (huv : G.Adj u v) (p : G.Walk x u) (hp : p.IsPath) (hv : v ∉ p.support) :
      ∃ (n : ℕ) (e : Fin (n + 1) ⊕ Fin 3 ↪ V),
        e (.inl 0) = x ∧
        (∀ i j : Fin (n + 1), i.val + 1 = j.val → G.Adj (e (.inl i)) (e (.inl j))) ∧
        G.Adj (e (.inl 0)) (e (.inr 0)) ∧
        G.Adj (e (.inl 0)) (e (.inr 1)) ∧
        ((e (.inl (Fin.last n)) = y ∧ e (.inr 2) = z) ∨
          (e (.inl (Fin.last n)) = z ∧ e (.inr 2) = y)) := by
    obtain ⟨a, ha, haout'⟩ := ht.isAcyclic.exists_two_external_neighbors (hp.concat hv huv) ex hx
    have haout (i) : a i ∉ p.support := by
      intro hi
      exact haout' i (p.support_subset_support_concat huv hi)
    have hav (i) : a i ≠ v := by
      intro heq
      exact haout' i (heq ▸ (p.concat huv).end_mem_support)
    let f : Fin 3 ↪ V := ⟨![a 0, a 1, v], by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [a.injective.ne (by decide : (0 : Fin 2) ≠ 1), Ne.symm]⟩
    have hf : ∀ i, f i ∉ p.support := by
      intro i
      fin_cases i
      · exact haout 0
      · exact haout 1
      · exact hv
    let e := hp.embeddingWithExternal f hf
    refine ⟨p.length, e, p.getVert_zero, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      change G.Adj (p.getVert i.val) (p.getVert j.val)
      rw [← hij]
      exact p.adj_getVert_succ (by omega)
    · change G.Adj (p.getVert 0) (a 0)
      simpa using ha 0
    · change G.Adj (p.getVert 0) (a 1)
      simpa using ha 1
    · change ((p.getVert p.length = y ∧ v = z) ∨ (p.getVert p.length = z ∧ v = y))
      simpa using horder
  obtain ⟨p, hp⟩ := (ht.connected x y).exists_isPath
  by_cases hz : z ∈ p.support
  · obtain ⟨q, hq⟩ := (ht.connected x z).exists_isPath
    exact build (Or.inr ⟨rfl, rfl⟩) hyz.symm q hq
      (ht.isAcyclic.ne_mem_support_of_support_of_adj_of_isPath hp hq hyz hz)
  · exact build (Or.inl ⟨rfl, rfl⟩) hyz p hp hz


lemma IsAcyclic.snd_eq_of_common_vertex {p : G.Walk u v} {w : V} {q : G.Walk u w}
    (hG : G.IsAcyclic) (hp : p.IsPath) (hq : q.IsPath)
    {z : V} (hzu : z ≠ u) (hzp : z ∈ p.support) (hzq : z ∈ q.support) : p.snd = q.snd := by
  classical
  have heq : p.takeUntil z hzp = q.takeUntil z hzq :=
    Subtype.mk.inj (hG.subsingleton_path u z |>.elim
      ⟨_, hp.takeUntil hzp⟩ ⟨_, hq.takeUntil hzq⟩)
  have := congrArg Walk.snd heq
  simpa only [Walk.snd_takeUntil hzu] using this

lemma Walk.Nil.snd_eq_start {a b : V} {q : G.Walk a b} (hn : q.Nil) : q.snd = a := by
  cases hn
  rfl

lemma exists_longest_path_with_snd [Finite V] {x z : V} (hxz : G.Adj x z) :
    ∃ (y : V) (p : G.Walk x y), p.IsPath ∧ p.snd = z ∧
      ∀ (y' : V) (q : G.Walk x y'), q.IsPath → q.snd = z → q.length ≤ p.length := by
  classical
  letI := Fintype.ofFinite V
  let s : Set ℕ := {n | ∃ (y : V) (p : G.Walk x y), p.IsPath ∧ p.snd = z ∧ p.length = n}
  have hs : s.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro n ⟨y, p, hp, _, rfl⟩
    exact Nat.le_of_lt hp.length_lt)
  have hs1 : 1 ∈ s := ⟨z, hxz.toWalk, hxz.isPath_toWalk, by rfl, by simp⟩
  obtain ⟨_, ⟨⟨y, p, hp, hpsnd, rfl⟩, hmax⟩⟩ := hs.exists_maximal ⟨1, hs1⟩
  refine ⟨y, p, hp, hpsnd, ?_⟩
  intro y' q hq hqsnd
  have := hmax ⟨y', q, hq, hqsnd, rfl⟩
  omega

/-- Except at the initial endpoint, a maximal path cannot be left through
a vertex of valence at most two. -/
lemma Walk.IsPath.mem_support_of_rooted_maximal {x y z : V} {p : G.Walk x y}
    (hp : p.IsPath) (hxz : G.Adj x z) (hpsnd : p.snd = z)
    (hmax : ∀ (y' : V) (q : G.Walk x y'), q.IsPath → q.snd = z → q.length ≤ p.length)
    (hdeg : ∀ (a b c d : V), a ≠ x → G.Adj a b → G.Adj a c → G.Adj a d →
      b = c ∨ b = d ∨ c = d)
    {a b : V} (ha : a ∈ p.support) (hax : a ≠ x) (hab : G.Adj a b) : b ∈ p.support := by
  by_contra hb
  obtain ⟨i, hia, hi⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  have hi0 : i ≠ 0 := by
    intro h
    exact hax (by simpa [h] using hia.symm)
  have hp1 : 1 ≤ p.length := by omega
  by_cases hilast : i = p.length
  · have hay : a = y := by simpa [hilast] using hia.symm
    rw [hay] at hab
    have hnew : (p.concat hab).IsPath := hp.concat hb hab
    have hsnd : (p.concat hab).snd = z := by
      simpa only [Walk.snd, Walk.concat_eq_append, Walk.getVert_append', if_pos hp1] using hpsnd
    have := hmax _ _ hnew hsnd
    simp at this
  have hadj₁ : G.Adj a (p.getVert (i - 1)) := by
    have := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    simpa [Nat.sub_add_cancel (show 1 ≤ i by omega), hia] using this
  have hadj₂ : G.Adj a (p.getVert (i + 1)) := by
    simpa [hia] using p.adj_getVert_succ (i := i) (by omega)
  have hne₁ : b ≠ p.getVert (i - 1) := by
    intro h
    exact hb (h ▸ p.getVert_mem_support (i - 1))
  have hne₂ : b ≠ p.getVert (i + 1) := by
    intro h
    exact hb (h ▸ p.getVert_mem_support (i + 1))
  have hne₃ : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro h
    have := hp.getVert_injOn (show i - 1 ≤ p.length by omega)
      (show i + 1 ≤ p.length by omega) h
    omega
  exact (hdeg a b (p.getVert (i - 1)) (p.getVert (i + 1)) hax hab hadj₁ hadj₂).elim
    hne₁ (fun h => h.elim hne₂ hne₃)


/-- A finite tree whose only vertex of valence three is `x` consists of
three nonempty chains attached at `x`. -/
lemma IsTree.exists_three_arms_equiv [Finite V] (ht : G.IsTree)
    (x : V) (ex : Fin 3 ↪ V) (hx : ∀ i, G.Adj x (ex i))
    (hroot : ∀ z, G.Adj x z → ∃ i, z = ex i)
    (hdeg : ∀ (a b c d : V), a ≠ x → G.Adj a b → G.Adj a c → G.Adj a d →
      b = c ∨ b = d ∨ c = d) :
    ∃ (l : Fin 3 → ℕ) (e : Unit ⊕ (Σ i : Fin 3, Fin (l i)) ≃ V),
      (∀ i, 1 ≤ l i) ∧ e (.inl ()) = x ∧
      (∀ i k, G.Adj x (e (.inr ⟨i, k⟩)) ↔ k.val = 0) ∧
      (∀ i j k m, G.Adj (e (.inr ⟨i, k⟩)) (e (.inr ⟨j, m⟩)) ↔
        i = j ∧ (k.val + 1 = m.val ∨ m.val + 1 = k.val)) := by
  classical
  choose y p hp hsnd hmax using fun i => exists_longest_path_with_snd (hx i)
  have hlen (i : Fin 3) : 1 ≤ (p i).length := by
    by_contra hn
    have hnil : (p i).Nil := Walk.length_eq_zero_iff.mp (by omega)
    have hs : (p i).snd = x := hnil.snd_eq_start
    exact (hx i).ne (by rw [← hsnd i, hs])
  have haway (i : Fin 3) (k : Fin (p i).length) : (p i).getVert (k.val + 1) ≠ x := by
    intro h
    have := ((hp i).getVert_eq_start_iff (show k.val + 1 ≤ (p i).length by omega)).mp h
    omega
  have hinter {i j : Fin 3} {z : V} (hz : z ≠ x)
      (hzi : z ∈ (p i).support) (hzj : z ∈ (p j).support) : i = j := by
    apply ex.injective
    rw [← hsnd i, ← hsnd j]
    exact ht.isAcyclic.snd_eq_of_common_vertex (hp i) (hp j) hz hzi hzj
  have hclosed {i : Fin 3} {a b : V} (ha : a ∈ (p i).support) (hax : a ≠ x)
      (hab : G.Adj a b) : b ∈ (p i).support :=
    (hp i).mem_support_of_rooted_maximal (hx i) (hsnd i) (hmax i) hdeg ha hax hab
  have hspan : ∀ z, ∃ i, z ∈ (p i).support := by
    have hstep {a b : V} (ha : ∃ i, a ∈ (p i).support) (hab : G.Adj a b) :
        ∃ i, b ∈ (p i).support := by
      rcases ha with ⟨i, hi⟩
      by_cases hax : a = x
      · rw [hax] at hab
        obtain ⟨j, hj⟩ := hroot b hab
        refine ⟨j, ?_⟩
        rw [hj, ← hsnd j]
        exact (p j).getVert_mem_support 1
      · exact ⟨i, hclosed hi hax hab⟩
    have hwalk {a b : V} (q : G.Walk a b) :
        (∃ i, a ∈ (p i).support) → ∃ i, b ∈ (p i).support := by
      induction q with
      | nil => exact id
      | cons h q ih => exact fun ha => ih (hstep ha h)
    intro z
    obtain ⟨q⟩ := ht.connected x z
    exact hwalk q ⟨0, (p 0).start_mem_support⟩
  let f : Unit ⊕ (Σ i : Fin 3, Fin (p i).length) → V :=
    Sum.elim (fun _ => x) (fun z => (p z.1).getVert (z.2.val + 1))
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      rcases a with a | ⟨i, k⟩ <;> rcases b with b | ⟨j, m⟩
      · exact congrArg Sum.inl (Subsingleton.elim a b)
      · exact (haway j m hab.symm).elim
      · exact (haway i k hab).elim
      · change (p i).getVert (k.val + 1) = (p j).getVert (m.val + 1) at hab
        have hij : i = j := hinter (haway i k) ((p i).getVert_mem_support _)
          (hab ▸ (p j).getVert_mem_support _)
        subst j
        have hkm : k = m := Fin.ext (by
          have := (hp i).getVert_injOn (show k.val + 1 ≤ (p i).length by omega)
            (show m.val + 1 ≤ (p i).length by omega) hab
          omega)
        subst m
        rfl
    · intro z
      by_cases hzx : z = x
      · exact ⟨.inl (), hzx.symm⟩
      obtain ⟨i, hi⟩ := hspan z
      obtain ⟨k, hkz, hk⟩ := Walk.mem_support_iff_exists_getVert.mp hi
      have hk0 : k ≠ 0 := by
        intro hk0
        exact hzx (by simpa [hk0] using hkz.symm)
      refine ⟨.inr ⟨i, ⟨k - 1, by omega⟩⟩, ?_⟩
      change (p i).getVert (k - 1 + 1) = z
      simpa [Nat.sub_add_cancel (show 1 ≤ k by omega)] using hkz
  refine ⟨fun i => (p i).length, Equiv.ofBijective f hf, hlen, rfl, ?_, ?_⟩
  · intro i k
    have hk : k.val < (p i).length := k.isLt
    change G.Adj x ((p i).getVert (k.val + 1)) ↔ k.val = 0
    constructor
    · intro hadj
      have heq := ht.isAcyclic.eq_snd_of_adj_start (hp i) hadj ((p i).getVert_mem_support _)
      have := (hp i).getVert_injOn (show k.val + 1 ≤ (p i).length by omega)
        (show 1 ≤ (p i).length from hlen i) heq
      omega
    · intro hk
      simpa only [hk, zero_add, Walk.snd, hsnd] using hx i
  · intro i j k m
    have hk : k.val < (p i).length := k.isLt
    have hm : m.val < (p j).length := m.isLt
    change G.Adj ((p i).getVert (k.val + 1)) ((p j).getVert (m.val + 1)) ↔ _
    constructor
    · intro hadj
      have hm : (p j).getVert (m.val + 1) ∈ (p i).support :=
        hclosed ((p i).getVert_mem_support _) (haway i k) hadj
      have hij := hinter (haway j m) hm ((p j).getVert_mem_support _)
      subst j
      refine ⟨rfl, ?_⟩
      have := (ht.isAcyclic.adj_getVert_iff (hp i)
        (show k.val + 1 ≤ (p i).length by omega)
        (show m.val + 1 ≤ (p i).length by omega)).mp hadj
      omega
    · rintro ⟨rfl, hnext⟩
      apply (ht.isAcyclic.adj_getVert_iff (hp i)
        (show k.val + 1 ≤ (p i).length by omega)
        (show m.val + 1 ≤ (p i).length by omega)).mpr
      omega


end SimpleGraph

lemma exists_fin_three_sorted_perm (l : Fin 3 → ℕ) :
    ∃ σ : Equiv.Perm (Fin 3), l (σ 0) ≤ l (σ 1) ∧ l (σ 1) ≤ l (σ 2) := by
  by_cases h01 : l 0 ≤ l 1
  · by_cases h12 : l 1 ≤ l 2
    · exact ⟨Equiv.refl _, h01, h12⟩
    · by_cases h02 : l 0 ≤ l 2
      · refine ⟨Equiv.ofBijective ![0, 2, 1] (by decide), ?_⟩
        simpa using And.intro h02 (show l 2 ≤ l 1 by omega)
      · refine ⟨Equiv.ofBijective ![2, 0, 1] (by decide), ?_⟩
        simpa using And.intro (show l 2 ≤ l 0 by omega) h01
  · by_cases h02 : l 0 ≤ l 2
    · refine ⟨Equiv.ofBijective ![1, 0, 2] (by decide), ?_⟩
      simpa using And.intro (show l 1 ≤ l 0 by omega) h02
    · by_cases h12 : l 1 ≤ l 2
      · refine ⟨Equiv.ofBijective ![1, 2, 0] (by decide), ?_⟩
        simpa using And.intro h12 (show l 2 ≤ l 0 by omega)
      · refine ⟨Equiv.ofBijective ![2, 1, 0] (by decide), ?_⟩
        simpa using And.intro (show l 2 ≤ l 1 by omega) (show l 1 ≤ l 0 by omega)


namespace LieAlgebrasAndRepresentations
open Set Module Matrix

/-- The two rank-two labels give the same oriented diagram after reindexing. -/
theorem dynkin_B2_C2 : DynkinExhaustionSpecs.bcTwoType := by
  refine ⟨Equiv.swap (0 : Fin 2) (1 : Fin 2), ?_, ?_⟩ <;>
    intro i j <;> fin_cases i <;> fin_cases j <;>
    simp only [FiniteDynkinType.diagram, FiniteDynkinType.cartan] <;> decide

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma normalizedSimpleGram_apply (b : ι → E) (i j : ι) :
    normalizedSimpleGram b i j =
      2 * (‖b i‖⁻¹ * ‖b j‖⁻¹ * inner ℝ (b i) (b j)) := by
  simp [normalizedSimpleGram, real_inner_smul_left, real_inner_smul_right, mul_assoc, mul_left_comm]

lemma normalizedSimpleGram_diag (b : Basis ι ℝ E) (i : ι) :
    normalizedSimpleGram b i i = 2 := by
  rw [normalizedSimpleGram_apply, real_inner_self_eq_norm_sq]
  have hn : ‖b i‖ ≠ 0 := norm_ne_zero_iff.mpr (b.ne_zero i)
  field_simp

lemma normalizedSimpleGram_posDef [Finite ι] (b : Basis ι ℝ E) :
    (normalizedSimpleGram b).PosDef := by
  have h : LinearIndependent ℝ (fun i => ‖b i‖⁻¹ • b i) := by
    convert b.linearIndependent.units_smul
      (fun i => Units.mk0 (‖b i‖⁻¹) (inv_ne_zero (norm_ne_zero_iff.mpr (b.ne_zero i)))) using 1
    rfl
  exact (Matrix.posDef_gram_of_linearIndependent h).smul (by norm_num)

lemma normalizedSimpleGram_offDiag {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) (b : Basis ι ℝ E) (hb : IsSimpleBasis R v b)
    {i j : ι} (hij : i ≠ j) :
    normalizedSimpleGram b i j = -Real.sqrt ((dynkinDiagram b).edges i j : ℝ) := by
  have hn (k : ι) : ‖b k‖ ≠ 0 := norm_ne_zero_iff.mpr (b.ne_zero k)
  have hnonpos : normalizedSimpleGram b i j ≤ 0 := by
    rw [normalizedSimpleGram_apply]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (hb.nonpos hR.toRootAxioms hv hij))
  have hsq : (normalizedSimpleGram b i j) ^ 2 = ((dynkinDiagram b).edges i j : ℝ) := by
    rw [normalizedSimpleGram_apply, dynkin_edges_cast hR hv hb hij]
    simp only [cartanMatrix, rootCartan, real_inner_comm (b j) (b i),
      real_inner_self_eq_norm_sq]
    field_simp
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonpos hnonpos, neg_neg]

theorem dynkin_normalizedGram : DynkinExhaustionSpecs.normalizedGramType := by
  intro E _ _ ι _ R hR v hv b hb
  exact ⟨normalizedSimpleGram_posDef b, normalizedSimpleGram_diag b,
    fun _ _ hij => normalizedSimpleGram_offDiag hR hv b hb hij⟩

/-- Numerical classification of positive branch-arm Schur complements. -/
theorem dynkin_arm_lengths : DynkinExhaustionSpecs.armLengthsType := by
  intro a b c ha hab hbc
  have bound (k d : ℕ) (hd : 0 < d) (hdk : d ≤ k + 1) :
      1 / ((k : ℝ) + 1) ≤ 1 / (d : ℝ) := by
    apply one_div_le_one_div_of_le (by exact_mod_cast hd)
    exact_mod_cast hdk
  constructor
  · intro h
    have ha1 : a = 1 := by
      by_contra hne
      have ha2 : 2 ≤ a := by omega
      have hb2 : 2 ≤ b := by omega
      have hc2 : 2 ≤ c := by omega
      have h1 := bound a 3 (by decide) (by omega)
      have h2 := bound b 3 (by decide) (by omega)
      have h3 := bound c 3 (by decide) (by omega)
      norm_num at h h1 h2 h3
      linarith
    refine ⟨ha1, ?_⟩
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    have hb2 : b = 2 := by
      by_contra hne
      have hb3 : 3 ≤ b := by omega
      have hc3 : 3 ≤ c := by omega
      have h2 := bound b 4 (by decide) (by omega)
      have h3 := bound c 4 (by decide) (by omega)
      subst a
      norm_num at h h2 h3
      linarith
    refine Or.inr ⟨hb2, ?_⟩
    have hc5 : c < 5 := by
      by_contra hn
      have h3 := bound c 6 (by decide) (by omega)
      subst a
      subst b
      norm_num at h h3
      linarith
    omega
  · rintro ⟨rfl, hb | ⟨rfl, hc | hc | hc⟩⟩
    · subst b
      have : 0 < 1 / ((c : ℝ) + 1) := by positivity
      norm_num
      linarith
    all_goals subst c; norm_num

/-- Numerical classification for the two sides of a double edge. -/
theorem dynkin_double_chain : DynkinExhaustionSpecs.doubleChainType := by
  intro p q hp hq
  constructor
  · intro h
    by_cases hp1 : p = 1
    · exact Or.inl hp1
    by_cases hq1 : q = 1
    · exact Or.inr (Or.inl hq1)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    have hp3 : p < 3 := by
      by_contra hn
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
      nlinarith [mul_nonneg (sub_nonneg.mpr hp3) (sub_nonneg.mpr hq2)]
    have hq3 : q < 3 := by
      by_contra hn
      have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast (show 3 ≤ q by omega)
      nlinarith [mul_nonneg (sub_nonneg.mpr hp2) (sub_nonneg.mpr hq3)]
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · rintro (rfl | rfl | ⟨rfl, rfl⟩) <;> push_cast <;> nlinarith

lemma normalizedSimpleGram_nonpos {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) (b : Basis ι ℝ E) (hb : IsSimpleBasis R v b)
    {i j : ι} (hij : i ≠ j) : normalizedSimpleGram b i j ≤ 0 := by
  rw [normalizedSimpleGram_offDiag hR hv b hb hij]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

lemma normalizedSimpleGram_edge_le {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) (b : Basis ι ℝ E) (hb : IsSimpleBasis R v b)
    {i j : ι} (he : (dynkinDiagram b).edges i j ≠ 0) :
    normalizedSimpleGram b i j ≤ -1 := by
  have hij := ((dynkin_edges_ne_zero hR hv hb i j).mp he).1
  rw [normalizedSimpleGram_offDiag hR hv b hb hij]
  have hm : (1 : ℝ) ≤ ((dynkinDiagram b).edges i j : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr he)
  have hs : 1 ≤ Real.sqrt ((dynkinDiagram b).edges i j : ℝ) := by
    simpa using Real.sqrt_le_sqrt hm
  linarith

/-- The five-vertex quadratic-form obstruction: a center and four distinct
neighbors already contradict positive definiteness. Extra edges only decrease
the quadratic value of `(2,1,1,1,1)`. -/
lemma no_four_neighbors_matrix (M : Matrix (Fin 5) (Fin 5) ℝ)
    (hM : M.PosDef) (hd : ∀ i, M i i = 2)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hc : ∀ j, j ≠ 0 → M 0 j ≤ -1) : False := by
  have hsymm (i j : Fin 5) : M j i = M i j := by
    simpa using hM.isHermitian.apply i j
  have hpos := hM.dotProduct_mulVec_pos (x := ![2,1,1,1,1]) (by
    intro he
    have := congrFun he 0
    norm_num at this)
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, hd] at hpos
  rw [hsymm 0 1, hsymm 0 2, hsymm 0 3, hsymm 0 4, hsymm 1 2, hsymm 1 3, hsymm 1 4, hsymm 2 3, hsymm 2 4, hsymm 3 4] at hpos
  have hc1 := hc 1 (by decide)
  have hc2 := hc 2 (by decide)
  have hc3 := hc 3 (by decide)
  have hc4 := hc 4 (by decide)
  have h12 := hoff 1 2 (by decide)
  have h13 := hoff 1 3 (by decide)
  have h14 := hoff 1 4 (by decide)
  have h23 := hoff 2 3 (by decide)
  have h24 := hoff 2 4 (by decide)
  have h34 := hoff 3 4 (by decide)
  linarith

lemma IsSimpleBasis.finite_index {R : Set E} {v : E} (hR : IsRootSystem R)
    {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b) : Finite ι := by
  have : Finite R := hR.finite.to_subtype
  exact Finite.of_injective (fun i => (⟨b i, hb.root_mem i⟩ : R))
    (fun i j h => b.injective (Subtype.mk.inj h))

theorem dynkin_no_four_neighbors : DynkinExhaustionSpecs.noFourNeighborsType := by
  intro E _ _ ι R hR v hv b hb e he
  have : Finite ι := hb.finite_index hR
  apply no_four_neighbors_matrix ((normalizedSimpleGram b).submatrix e e)
    ((normalizedSimpleGram_posDef b).submatrix e.injective)
  · exact fun i => normalizedSimpleGram_diag b (e i)
  · exact fun i j hij => normalizedSimpleGram_nonpos hR hv b hb (e.injective.ne hij)
  · exact fun j hj => normalizedSimpleGram_edge_le hR hv b hb (he j hj)

/-- A triple edge and any attached edge force a nonpositive quadratic value
on `(sqrt 3,2,1)`. -/
lemma no_attached_triple_matrix (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M.PosDef) (hd : ∀ i, M i i = 2)
    (h01 : M 0 1 = -Real.sqrt 3) (h12 : M 1 2 ≤ -1) (h02 : M 0 2 ≤ 0) : False := by
  have hsymm (i j : Fin 3) : M j i = M i j := by
    simpa using hM.isHermitian.apply i j
  have hpos := hM.dotProduct_mulVec_pos (x := ![Real.sqrt 3,2,1]) (by
    intro he
    have := congrFun he 1
    norm_num at this)
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, hd] at hpos
  rw [hsymm 0 1, hsymm 0 2, hsymm 1 2, h01] at hpos
  have hs3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg 3) h02]

theorem dynkin_no_attached_triple : DynkinExhaustionSpecs.tripleEdgeType := by
  intro E _ _ ι R hR v hv b hb e he
  have : Finite ι := hb.finite_index hR
  by_contra hne
  apply no_attached_triple_matrix ((normalizedSimpleGram b).submatrix e e)
    ((normalizedSimpleGram_posDef b).submatrix e.injective)
  · exact fun i => normalizedSimpleGram_diag b (e i)
  · change normalizedSimpleGram b (e 0) (e 1) = _
    rw [normalizedSimpleGram_offDiag hR hv b hb (e.injective.ne (by decide)), he]
    norm_num
  · exact normalizedSimpleGram_edge_le hR hv b hb hne
  · exact normalizedSimpleGram_nonpos hR hv b hb (e.injective.ne (by decide))

/-- Positivity on the all-ones vector gives a positive row sum. -/
lemma positive_row_sum {κ : Type*} [Fintype κ] [Nonempty κ]
    (M : Matrix κ κ ℝ) (hM : M.PosDef) : ∃ i, 0 < ∑ j, M i j := by
  have hpos := hM.dotProduct_mulVec_pos (x := fun _ => 1) (by
    intro he
    have := congrFun he (Classical.choice (inferInstance : Nonempty κ))
    norm_num at this)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, mul_one, one_mul] at hpos
  by_contra! hn
  have hle : ∑ i, ∑ j, M i j ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
  linarith

/-- Two incident edges would already make a positive row sum nonpositive. -/
lemma positive_row_has_at_most_one_neighbor {κ : Type*} [Fintype κ]
    (M : Matrix κ κ ℝ) (hd : ∀ i, M i i = 2)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) {i j k : κ}
    (hrow : 0 < ∑ l, M i l) (hij : i ≠ j) (hik : i ≠ k)
    (hj : M i j ≤ -1) (hk : M i k ≤ -1) : j = k := by
  classical
  by_contra hjk
  have hle : ∑ l, M i l ≤ ∑ l ∈ ({i,j,k} : Finset κ), M i l := by
    apply Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ _)
    intro l _ hl
    exact hoff i l (by aesop)
  simp [hij, hik, hjk, hd] at hle
  linarith

theorem dynkin_thin_vertex : DynkinExhaustionSpecs.thinVertexType := by
  intro E _ _ ι R hR v hv b hb s hs
  classical
  have : Finite ι := hb.finite_index hR
  have : Nonempty s := by
    obtain ⟨i, hi⟩ := hs
    exact ⟨⟨i, hi⟩⟩
  let M := (normalizedSimpleGram b).submatrix (fun i : s => (i : ι)) (fun i : s => (i : ι))
  have hM : M.PosDef := (normalizedSimpleGram_posDef b).submatrix Subtype.val_injective
  obtain ⟨i, hi⟩ := positive_row_sum M hM
  refine ⟨i, i.prop, ?_⟩
  intro j hj k hk hej hek
  have hij := ((dynkin_edges_ne_zero hR hv hb i j).mp hej).1
  have hik := ((dynkin_edges_ne_zero hR hv hb i k).mp hek).1
  have heq : (⟨j, hj⟩ : s) = ⟨k, hk⟩ :=
    positive_row_has_at_most_one_neighbor M (fun l => normalizedSimpleGram_diag b l)
      (fun l m hne => normalizedSimpleGram_nonpos hR hv b hb
        (fun he => hne (Subtype.ext he))) hi
      (fun he => hij (congrArg Subtype.val he))
      (fun he => hik (congrArg Subtype.val he))
      (normalizedSimpleGram_edge_le hR hv b hb hej)
      (normalizedSimpleGram_edge_le hR hv b hb hek)
  exact congrArg Subtype.val heq

/-- The hereditary leaf criterion excludes a cycle by rotating it to the
selected leaf. Its second and penultimate vertices are distinct neighbors. -/
lemma SimpleGraph.isAcyclic_of_finite_thin_vertex {κ : Type*} (G : SimpleGraph κ)
    (hthin : ∀ s : Finset κ, s.Nonempty → ∃ i ∈ s, ∀ j ∈ s, ∀ k ∈ s,
      G.Adj i j → G.Adj i k → j = k) : G.IsAcyclic := by
  classical
  intro u c hc
  obtain ⟨i, hi, hleaf⟩ := hthin c.support.toFinset
    (by simp)
  have hi' : i ∈ c.support := by simpa using hi
  let q := c.rotate i hi'
  have hq : q.IsCycle := hc.rotate hi'
  have hm (n : ℕ) : q.getVert n ∈ c.support.toFinset := by
    simpa using (c.mem_support_rotate_iff i hi').mp (q.getVert_mem_support n)
  exact hq.snd_ne_penultimate (hleaf q.snd (hm 1) q.penultimate
    (hm (q.length - 1)) (q.adj_snd hq.not_nil) (q.adj_penultimate hq.not_nil).symm)

lemma simpleRootGraph_adj_iff {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b) (i j : ι) :
    (simpleRootGraph b).Adj i j ↔ (dynkinDiagram b).edges i j ≠ 0 :=
  (dynkin_edges_ne_zero hR hv hb i j).symm

theorem dynkin_tree : DynkinExhaustionSpecs.treeType := by
  intro E _ _ ι R hR v hv b hb
  have ha : (simpleRootGraph b).IsAcyclic := by
    apply SimpleGraph.isAcyclic_of_finite_thin_vertex
    intro s hs
    obtain ⟨i, hi, ht⟩ := dynkin_thin_vertex R hR v hv b hb s hs
    exact ⟨i, hi, fun j hj k hk he hf => ht j hj k hk
      ((simpleRootGraph_adj_iff hR hv hb i j).mp he)
      ((simpleRootGraph_adj_iff hR hv hb i k).mp hf)⟩
  refine ⟨ha, ?_⟩
  intro hc
  have := hc.1
  refine ⟨?_, ha⟩
  refine ⟨?_⟩
  intro i j
  have hconn := hc.2 i j
  induction hconn with
  | rel x y h => exact ((simpleRootGraph_adj_iff hR hv hb x y).mpr h).reachable
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An exact Cartan-matrix identification transports both the weights and
the arrows to a standard diagram. -/
lemma dynkin_isomorphic_of_cartan {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (t : FiniteDynkinType) (e : ι ≃ Fin t.rank)
    (h : ∀ i j, cartanMatrix b i j = (t.cartan (e i) (e j) : ℝ)) :
    (dynkinDiagram b).Isomorphic t.diagram := by
  refine ⟨e, ?_, ?_⟩
  · intro i j
    simp only [dynkinDiagram, FiniteDynkinType.diagram]
    rw [h i j, h j i, ← Int.cast_mul]
    rw [Int.floor_intCast]
    by_cases hij : i = j
    · simp only [hij, ite_true]
    · simp only [hij, e.injective.ne hij, ite_false]
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [dynkinDiagram, FiniteDynkinType.diagram]
    · rw [dynkin_arrow_iff_cartan_lt hR hv hb hij, h i j, h j i]
      change _ ↔ e i ≠ e j ∧ _
      simp [e.injective.ne hij]

lemma dynkin_isomorphic_of_cartan_reindex {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (t : FiniteDynkinType) (e : Fin t.rank ≃ ι)
    (h : ∀ i j, cartanMatrix b (e i) (e j) = (t.cartan i j : ℝ)) :
    (dynkinDiagram b).Isomorphic t.diagram := by
  apply dynkin_isomorphic_of_cartan hR hv hb t e.symm
  intro i j
  simpa only [Equiv.apply_symm_apply] using h (e.symm i) (e.symm j)

lemma dynkin_triple_endpoint {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {i j k : ι} (he : (dynkinDiagram b).edges i j = 3)
    (hk : (dynkinDiagram b).edges j k ≠ 0) : k = i := by
  have hij : i ≠ j := ((dynkin_edges_ne_zero hR hv hb i j).mp (by omega)).1
  have hjk := ((dynkin_edges_ne_zero hR hv hb j k).mp hk).1
  by_contra hki
  let e : Fin 3 ↪ ι := ⟨![i,j,k], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all⟩
  exact hk (dynkin_no_attached_triple R hR v hv b hb e he)

/-- Connectedness propagates the isolated pair along every edge chain. -/
lemma dynkin_triple_vertices {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected) {i j : ι}
    (he : (dynkinDiagram b).edges i j = 3) : ∀ k, k = i ∨ k = j := by
  have hs := (dynkin_diagram_properties R hR v hv b hb).2.2.1
  have he' : (dynkinDiagram b).edges j i = 3 := by rw [hs, he]
  have closed {x y : ι} (hxy : (dynkinDiagram b).edges x y ≠ 0)
      (hx : x = i ∨ x = j) : y = i ∨ y = j := by
    rcases hx with rfl | rfl
    · exact Or.inr (dynkin_triple_endpoint hR hv hb he' hxy)
    · exact Or.inl (dynkin_triple_endpoint hR hv hb he hxy)
  intro k
  have ht : ∀ {x y}, DynkinConnected b x y →
      (x = i ∨ x = j ↔ y = i ∨ y = j) := by
    intro x y hxy
    induction hxy with
    | rel x y h => exact ⟨closed h, closed (by rwa [hs])⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (ht (hc.2 i k)).mp (Or.inl rfl)

theorem dynkin_triple_classification : DynkinExhaustionSpecs.tripleClassificationType := by
  intro E _ _ ι R hR v hv b hb hc ⟨i,j,he⟩
  classical
  have hij : i ≠ j := ((dynkin_edges_ne_zero hR hv hb i j).mp (by omega)).1
  have hp := cartan_pair_values hR hv hb hij
  have hprod := dynkin_edges_cast hR hv hb hij
  rw [he] at hprod
  norm_num only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
  have hpair : (cartanMatrix b i j = -3 ∧ cartanMatrix b j i = -1) ∨
      (cartanMatrix b j i = -3 ∧ cartanMatrix b i j = -1) := by
    rcases hp with h | h | h | h | h | h <;> rcases h with ⟨h₁,h₂⟩ <;>
      simp_all
  have identify (x y : ι) (hxy : x ≠ y) (hall : ∀ k, k = x ∨ k = y)
      (h₁ : cartanMatrix b x y = -3) (h₂ : cartanMatrix b y x = -1) :
      (dynkinDiagram b).Isomorphic FiniteDynkinType.G2.diagram := by
    let f : Fin 2 → ι := ![x,y]
    have hf : Function.Bijective f := by
      constructor
      · intro a c hac
        fin_cases a <;> fin_cases c <;> simp_all [f]
      · intro k
        rcases hall k with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    let e := Equiv.ofBijective f hf
    apply dynkin_isomorphic_of_cartan_reindex hR hv hb .G2 e
    change ∀ a c : Fin 2, cartanMatrix b (f a) (f c) = (CartanMatrix.G₂ a c : ℝ)
    intro a c
    fin_cases a <;> fin_cases c <;>
      norm_num [f, h₁, h₂, cartan_diagonal R hR v hv b hb,
        FiniteDynkinType.cartan, CartanMatrix.G₂]
  have hall := dynkin_triple_vertices hR hv hb hc he
  rcases hpair with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact identify i j hij hall h₁ h₂
  · exact identify j i hij.symm (fun k => (hall k).symm) h₁ h₂

/-- The total sum of a nonempty simple-chain Gram matrix is two. -/
lemma chainGram_sum (n : ℕ) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (CartanMatrix.A (n + 1) i j : ℝ)) = 2 := by
  induction n with
  | zero => norm_num [CartanMatrix.A, Fin.sum_univ_succ]
  | succ n ih =>
    have htop (i j : Fin (n + 1)) :
        CartanMatrix.A (n + 2) i.castSucc j.castSucc = CartanMatrix.A (n + 1) i j := by
      simp [CartanMatrix.A]
    have htail (i : Fin (n + 1)) :
        CartanMatrix.A (n + 2) i.castSucc (Fin.last (n + 1)) =
          if i = Fin.last n then -1 else 0 := by
      simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have htail' (i : Fin (n + 1)) :
        CartanMatrix.A (n + 2) (Fin.last (n + 1)) i.castSucc =
          if i = Fin.last n then -1 else 0 := by
      rw [← Matrix.IsSymm.apply (CartanMatrix.A_isSymm (n + 2))]
      exact htail i
    have hrow (i : Fin (n + 2)) :
        (∑ j : Fin (n + 2), (CartanMatrix.A (n + 2) i j : ℝ)) =
        (∑ j : Fin (n + 1), (CartanMatrix.A (n + 2) i j.castSucc : ℝ)) +
          (CartanMatrix.A (n + 2) i (Fin.last (n + 1)) : ℝ) :=
      Fin.sum_univ_castSucc _
    have hdiag : CartanMatrix.A (n + 2) (Fin.last (n + 1)) (Fin.last (n + 1)) = 2 := by
      simp [CartanMatrix.A]
    rw [Fin.sum_univ_castSucc]
    simp_rw [hrow, htop, htail, htail', hdiag]
    norm_num [Finset.sum_add_distrib, ih]

/-- Extra nonpositive off-diagonal entries can only decrease the value of
the quadratic form on a nonnegative vector. -/
lemma quadraticForm_le_of_entrywise {κ : Type*} [Fintype κ]
    {M N : Matrix κ κ ℝ} (hMN : ∀ i j, M i j ≤ N i j)
    {x : κ → ℝ} (hx : ∀ i, 0 ≤ x i) :
    x ⬝ᵥ (M *ᵥ x) ≤ x ⬝ᵥ (N *ᵥ x) := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hx i)
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hMN i j) (hx j))

/-- The quadratic form decomposes into its four blocks. -/
lemma quadraticForm_sum_blocks {κ η : Type*} [Fintype κ] [Fintype η]
    (M : Matrix (κ ⊕ η) (κ ⊕ η) ℝ) (u : κ → ℝ) (v : η → ℝ) :
    (Sum.elim u v) ⬝ᵥ (M *ᵥ Sum.elim u v) =
      (∑ i, ∑ j, u i * M (.inl i) (.inl j) * u j) +
      (∑ i, ∑ j, u i * M (.inl i) (.inr j) * v j) +
      (∑ i, ∑ j, v i * M (.inr i) (.inl j) * u j) +
      (∑ i, ∑ j, v i * M (.inr i) (.inr j) * v j) := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add, add_assoc, mul_assoc]
  abel

/-- A chain cannot support external edges whose squared weights total four.
The leaves need only be distinct from the chain and one another; extra edges
are allowed. This one bound covers two branches, a branch and a double edge,
and two double edges at any distance. -/
lemma path_attachments_matrix_bound {κ : Type*} [Fintype κ] (n : ℕ)
    (M : Matrix (Fin (n + 1) ⊕ κ) (Fin (n + 1) ⊕ κ) ℝ)
    (hM : M.PosDef) (hd : ∀ i, M i i = 2)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hpath : ∀ i j, M (.inl i) (.inl j) ≤ (CartanMatrix.A (n + 1) i j : ℝ))
    (a : κ → Fin (n + 1)) (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ha : ∀ j, M (.inl (a j)) (.inr j) ≤ -w j) :
    ∑ j, (w j) ^ 2 < 4 := by
  classical
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => CartanMatrix.A (n + 1) i j
  let B : Matrix (Fin (n + 1)) κ ℝ := fun i j => if i = a j then -w j else 0
  let D : Matrix κ κ ℝ := fun i j => if i = j then 2 else 0
  let N := Matrix.fromBlocks A B B.transpose D
  let x : Fin (n + 1) ⊕ κ → ℝ := Sum.elim (fun _ => 1) (fun j => w j / 2)
  have hsymm (i j) : M j i = M i j := by simpa using hM.isHermitian.apply i j
  have hMN : ∀ i j, M i j ≤ N i j := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact hpath i j
    · change M (.inl i) (.inr j) ≤ if i = a j then -w j else 0
      split_ifs with h
      · subst i; exact ha j
      · exact hoff _ _ (by simp)
    · change M (.inr i) (.inl j) ≤ if j = a i then -w i else 0
      rw [hsymm]
      split_ifs with h
      · subst j; exact ha i
      · exact hoff _ _ (by simp)
    · change M (.inr i) (.inr j) ≤ if i = j then 2 else 0
      split_ifs with h
      · subst j; exact (hd _).le
      · exact hoff _ _ (by simpa)
  have hN : x ⬝ᵥ (N *ᵥ x) = 2 - (∑ j, w j ^ 2) / 2 := by
    rw [quadraticForm_sum_blocks N (fun _ => 1) (fun j => w j / 2)]
    change (∑ i, ∑ j, 1 * A i j * 1) +
      (∑ i, ∑ j, 1 * B i j * (w j / 2)) +
      (∑ i, ∑ j, (w i / 2) * B j i * 1) +
      (∑ i, ∑ j, (w i / 2) * D i j * (w j / 2)) = _
    simp only [one_mul, mul_one]
    rw [Finset.sum_comm (f := fun i j => B i j * (w j / 2))]
    simp [A, B, D, chainGram_sum, pow_two]
    simp only [mul_div_assoc, div_mul_eq_mul_div, Finset.sum_neg_distrib]
    ring_nf
    rw [← Finset.sum_mul]
    ring
  have hx : x ≠ 0 := by
    intro h
    have := congrFun h (.inl 0)
    norm_num [x] at this
  have hpos := hM.dotProduct_mulVec_pos hx
  simp only [star_trivial] at hpos
  have hle := quadraticForm_le_of_entrywise hMN (x := x) (by
    intro i; rcases i with i | i
    · norm_num [x]
    · exact div_nonneg (hw i) (by norm_num))
  rw [hN] at hle
  linarith

/-- Apply the path obstruction to the actual edge multiplicities of a
simple-root diagram. Extra edges among any retained vertices are allowed. -/
theorem dynkin_path_attachment_bound : DynkinExhaustionSpecs.pathAttachmentBoundType := by
  intro E _ _ ι R hR v hv b hb n κ _ e hpath a
  classical
  have : Finite ι := hb.finite_index hR
  let M := (normalizedSimpleGram b).submatrix e e
  have hM : M.PosDef := (normalizedSimpleGram_posDef b).submatrix e.injective
  have hd : ∀ i, M i i = 2 := fun i => normalizedSimpleGram_diag b (e i)
  have hoff : ∀ i j, i ≠ j → M i j ≤ 0 := by
    intro i j hij
    exact normalizedSimpleGram_nonpos hR hv b hb (e.injective.ne hij)
  have hp : ∀ i j : Fin (n + 1),
      M (.inl i) (.inl j) ≤ (CartanMatrix.A (n + 1) i j : ℝ) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [CartanMatrix.A, Matrix.of_apply, ite_true, Int.cast_ofNat]
      exact (hd _).le
    · simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false]
      split_ifs with h
      · norm_num only [Int.cast_neg, Int.cast_one]
        apply normalizedSimpleGram_edge_le hR hv b hb
        rcases h with h | h
        · exact hpath i j h
        · have hs := (dynkin_diagram_properties R hR v hv b hb).2.2.1
          rw [hs]
          exact hpath j i h
      · norm_num only [Int.cast_zero]
        exact hoff _ _ (by simp [hij])
  let w : κ → ℝ := fun k =>
    Real.sqrt ((dynkinDiagram b).edges (e (.inl (a k))) (e (.inr k)) : ℝ)
  have ha : ∀ k, M (.inl (a k)) (.inr k) ≤ -w k := by
    intro k
    exact (normalizedSimpleGram_offDiag hR hv b hb (e.injective.ne (by simp))).le
  have h := path_attachments_matrix_bound n M hM hd hoff hp a w
    (fun k => Real.sqrt_nonneg _) ha
  simpa only [w, Real.sq_sqrt (Nat.cast_nonneg _)] using h

/-- An off-diagonal entry on a simple edge is minus one, and on a
missing edge it is zero. The assertion uses the actual root Cartan entries. -/
lemma cartan_entry_of_edge_le_one {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {i j : ι} (hij : i ≠ j) (he : (dynkinDiagram b).edges i j ≤ 1) :
    cartanMatrix b i j = if (dynkinDiagram b).edges i j = 0 then 0 else -1 := by
  have hp := cartan_pair_values hR hv hb hij
  have hm := dynkin_edges_cast hR hv hb hij
  have he' : ((dynkinDiagram b).edges i j : ℝ) ≤ 1 := by exact_mod_cast he
  norm_num only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
  rcases hp with h | h | h | h | h | h <;> rcases h with ⟨h₁,h₂⟩ <;>
    simp only [h₁,h₂] at hm ⊢ <;> norm_num at hm <;> simp_all

/-- A simply laced diagram enumerated by a chain is exactly A-type. -/
lemma dynkin_simply_laced_chain {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (n : ℕ) (e : Fin (n + 1) ≃ ι)
    (hc : ∀ i j, (dynkinDiagram b).edges (e i) (e j) ≠ 0 ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (hs : ∀ i j, (dynkinDiagram b).edges i j ≤ 1) :
    (dynkinDiagram b).Isomorphic (FiniteDynkinType.A (n + 1) (by omega)).diagram := by
  apply dynkin_isomorphic_of_cartan_reindex hR hv hb (.A (n + 1) (by omega)) e
  change ∀ i j : Fin (n + 1), cartanMatrix b (e i) (e j) = (CartanMatrix.A (n + 1) i j : ℝ)
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [CartanMatrix.A] using cartan_diagonal R hR v hv b hb (e i)
  · rw [cartan_entry_of_edge_le_one hR hv hb (e.injective.ne hij) (hs _ _)]
    simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false]
    have hh := hc i j
    by_cases he : (dynkinDiagram b).edges (e i) (e j) = 0 <;> simp_all

/-- A one-vertex diagram is A₁. -/
lemma dynkin_singleton_classification {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (e : Fin 1 ≃ ι) :
    (dynkinDiagram b).Isomorphic (FiniteDynkinType.A 1 (by decide)).diagram := by
  apply dynkin_isomorphic_of_cartan_reindex hR hv hb (.A 1 (by decide)) e
  intro i j
  fin_cases i
  fin_cases j
  change cartanMatrix b (e 0) (e 0) = 2
  exact cartan_diagonal R hR v hv b hb (e 0)

/-- In a connected two-vertex diagram the two vertices are joined. -/
lemma dynkin_pair_edge {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected) (e : Fin 2 ≃ ι) :
    (dynkinDiagram b).edges (e 0) (e 1) ≠ 0 := by
  intro hz
  have hall (x : ι) : x = e 0 ∨ x = e 1 := by
    have h := e.apply_symm_apply x
    generalize e.symm x = a at h
    fin_cases a
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hs := (dynkin_diagram_properties R hR v hv b hb).2.2.1
  have hzero (x y : ι) : (dynkinDiagram b).edges x y = 0 := by
    rcases hall x with rfl | rfl <;> rcases hall y with rfl | rfl
    · simp [dynkinDiagram]
    · exact hz
    · rw [hs]; exact hz
    · simp [dynkinDiagram]
  have heq {x y : ι} (h : DynkinConnected b x y) : x = y := by
    induction h with
    | rel x y h => exact (h (hzero x y)).elim
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (by decide : (0 : Fin 2) ≠ 1) (e.injective (heq (hc.2 (e 0) (e 1))))

/-- Exhaustion in rank two, including both orientations of every multiple edge. -/
lemma dynkin_pair_classification {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected) (e : Fin 2 ≃ ι) :
    ∃ t : FiniteDynkinType, (dynkinDiagram b).Isomorphic t.diagram := by
  have hne := dynkin_pair_edge hR hv hb hc e
  have hij : e 0 ≠ e 1 := e.injective.ne (by decide)
  have hp := cartan_pair_values hR hv hb hij
  have hprod := dynkin_edges_cast hR hv hb hij
  norm_num only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
  rcases hp with h | h | h | h | h | h
  · rw [h.1, h.2, mul_zero] at hprod
    exact (hne (Nat.cast_eq_zero.mp hprod)).elim
  · refine ⟨.A 2 (by decide), ?_⟩
    apply dynkin_isomorphic_of_cartan_reindex hR hv hb (.A 2 (by decide)) e
    intro a c
    change cartanMatrix b (e a) (e c) = (CartanMatrix.A 2 a c : ℝ)
    rw [CartanMatrix.A_two]
    fin_cases a <;> fin_cases c
    · change cartanMatrix b (e 0) (e 0) = 2
      exact cartan_diagonal R hR v hv b hb (e 0)
    · change cartanMatrix b (e 0) (e 1) = ((-1 : ℤ) : ℝ)
      norm_num
      exact h.1
    · change cartanMatrix b (e 1) (e 0) = ((-1 : ℤ) : ℝ)
      norm_num
      exact h.2
    · change cartanMatrix b (e 1) (e 1) = 2
      exact cartan_diagonal R hR v hv b hb (e 1)
  · refine ⟨.B 2 (by decide), ?_⟩
    apply dynkin_isomorphic_of_cartan_reindex hR hv hb (.B 2 (by decide)) e
    intro a c
    change cartanMatrix b (e a) (e c) = (CartanMatrix.C 2 a c : ℝ)
    rw [CartanMatrix.C_two]
    fin_cases a <;> fin_cases c
    · change cartanMatrix b (e 0) (e 0) = 2
      exact cartan_diagonal R hR v hv b hb (e 0)
    · change cartanMatrix b (e 0) (e 1) = ((-1 : ℤ) : ℝ)
      norm_num
      exact h.1
    · change cartanMatrix b (e 1) (e 0) = ((-2 : ℤ) : ℝ)
      norm_num
      exact h.2
    · change cartanMatrix b (e 1) (e 1) = 2
      exact cartan_diagonal R hR v hv b hb (e 1)
  · refine ⟨.C 2 (by decide), ?_⟩
    apply dynkin_isomorphic_of_cartan_reindex hR hv hb (.C 2 (by decide)) e
    intro a c
    change cartanMatrix b (e a) (e c) = (CartanMatrix.B 2 a c : ℝ)
    rw [CartanMatrix.B_two]
    fin_cases a <;> fin_cases c
    · change cartanMatrix b (e 0) (e 0) = 2
      exact cartan_diagonal R hR v hv b hb (e 0)
    · change cartanMatrix b (e 0) (e 1) = ((-2 : ℤ) : ℝ)
      norm_num
      exact h.1
    · change cartanMatrix b (e 1) (e 0) = ((-1 : ℤ) : ℝ)
      norm_num
      exact h.2
    · change cartanMatrix b (e 1) (e 1) = 2
      exact cartan_diagonal R hR v hv b hb (e 1)
  · refine ⟨.G2, ?_⟩
    apply dynkin_triple_classification R hR v hv b hb hc
    refine ⟨e 0, e 1, ?_⟩
    exact_mod_cast (show ((dynkinDiagram b).edges (e 0) (e 1) : ℝ) = 3 by
      rw [hprod, h.1, h.2]; norm_num)
  · refine ⟨.G2, ?_⟩
    apply dynkin_triple_classification R hR v hv b hb hc
    refine ⟨e 0, e 1, ?_⟩
    exact_mod_cast (show ((dynkinDiagram b).edges (e 0) (e 1) : ℝ) = 3 by
      rw [hprod, h.1, h.2]; norm_num)

/-- The complete oriented exhaustion assertion in ranks at most two. -/
lemma dynkin_rank_at_most_two {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected) (hn : Nat.card ι ≤ 2) :
    ∃ t : FiniteDynkinType, (dynkinDiagram b).Isomorphic t.diagram := by
  classical
  letI : Finite ι := hb.finite_index hR
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Nonempty ι := hc.1
  have hpos : 0 < Nat.card ι := Nat.card_pos
  have hcases : Nat.card ι = 1 ∨ Nat.card ι = 2 := by omega
  rcases hcases with h | h
  · let e : Fin 1 ≃ ι := (Fintype.equivFinOfCardEq (by
      simpa only [Nat.card_eq_fintype_card] using h)).symm
    exact ⟨.A 1 (by decide), dynkin_singleton_classification hR hv hb e⟩
  · let e : Fin 2 ≃ ι := (Fintype.equivFinOfCardEq (by
      simpa only [Nat.card_eq_fintype_card] using h)).symm
    exact dynkin_pair_classification hR hv hb hc e


/-- Two different edges on any embedded path cannot both be multiple. -/
lemma dynkin_chain_not_two_multiple {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {N : ℕ} (e : Fin (N + 1) ↪ ι)
    (hpath : ∀ i j : Fin (N + 1), i.val + 1 = j.val →
      (dynkinDiagram b).edges (e i) (e j) ≠ 0)
    (p q : Fin N) (hpq : p < q)
    (hp : 2 ≤ (dynkinDiagram b).edges (e p.castSucc) (e p.succ))
    (hq : 2 ≤ (dynkinDiagram b).edges (e q.castSucc) (e q.succ)) : False := by
  classical
  let n := q.val - p.val - 1
  have hlen : n + 1 = q.val - p.val := by dsimp [n]; omega
  let g : Fin (n + 1) ⊕ Fin 2 → Fin (N + 1) :=
    Sum.elim (fun i => ⟨p.val + 1 + i.val, by omega⟩) ![p.castSucc, q.succ]
  have hg : Function.Injective g := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · apply congrArg Sum.inl
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [g] at this
      omega
    · fin_cases y <;> have hh := congrArg Fin.val h <;> dsimp [g] at hh <;> omega
    · fin_cases x <;> have hh := congrArg Fin.val h <;> dsimp [g] at hh <;> omega
    · fin_cases x <;> fin_cases y
      · rfl
      · have hh := congrArg Fin.val h
        dsimp [g] at hh
        omega
      · have hh := congrArg Fin.val h
        dsimp [g] at hh
        omega
      · rfl
  let f : Fin (n + 1) ⊕ Fin 2 ↪ ι := ⟨fun x => e (g x), fun _ _ h => hg (e.injective h)⟩
  let a : Fin 2 → Fin (n + 1) := ![0, Fin.last n]
  have h := dynkin_path_attachment_bound R hR v hv b hb n f (by
    intro i j hij
    apply hpath
    dsimp [f, g]
    omega) a
  have hfirst : g (.inl (a 0)) = p.succ := by
    apply Fin.ext
    simp [g, a]
  have hlast : g (.inl (a 1)) = q.castSucc := by
    apply Fin.ext
    simp [g, a]
    omega
  have hs := (dynkin_diagram_properties R hR v hv b hb).2.2.1
  have hp' : (2 : ℝ) ≤ ((dynkinDiagram b).edges (f (.inl (a 0))) (f (.inr 0)) : ℝ) := by
    change (2 : ℝ) ≤ ((dynkinDiagram b).edges (e (g (.inl (a 0)) )) (e (g (.inr 0))) : ℝ)
    rw [hfirst]
    change (2 : ℝ) ≤ ((dynkinDiagram b).edges (e p.succ) (e p.castSucc) : ℝ)
    rw [hs]
    exact_mod_cast hp
  have hq' : (2 : ℝ) ≤ ((dynkinDiagram b).edges (f (.inl (a 1))) (f (.inr 1)) : ℝ) := by
    change (2 : ℝ) ≤ ((dynkinDiagram b).edges (e (g (.inl (a 1)) )) (e (g (.inr 1))) : ℝ)
    rw [hlast]
    change (2 : ℝ) ≤ ((dynkinDiagram b).edges (e q.castSucc) (e q.succ) : ℝ)
    exact_mod_cast hq
  rw [Fin.sum_univ_two] at h
  linarith

/-- An embedded path contains at most one edge of multiplicity at least two. -/
lemma dynkin_chain_unique_multiple {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {N : ℕ} (e : Fin (N + 1) ↪ ι)
    (hpath : ∀ i j : Fin (N + 1), i.val + 1 = j.val →
      (dynkinDiagram b).edges (e i) (e j) ≠ 0)
    (p q : Fin N)
    (hp : 2 ≤ (dynkinDiagram b).edges (e p.castSucc) (e p.succ))
    (hq : 2 ≤ (dynkinDiagram b).edges (e q.castSucc) (e q.succ)) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · exact (dynkin_chain_not_two_multiple hR hv hb e hpath p q h hp hq).elim
  · exact h
  · exact (dynkin_chain_not_two_multiple hR hv hb e hpath q p h hq hp).elim


lemma no_interior_double_matrix (M : Matrix (Fin 5) (Fin 5) ℝ)
    (hM : M.PosDef) (hd : ∀ i, M i i = 2)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (h01 : M 0 1 ≤ -1) (h12 : M 1 2 ≤ -Real.sqrt 2)
    (h23 : M 2 3 ≤ -1) (h34 : M 3 4 ≤ -1) : False := by
  let N : Matrix (Fin 5) (Fin 5) ℝ :=
    !![2,-1,0,0,0; -1,2,-Real.sqrt 2,0,0; 0,-Real.sqrt 2,2,-1,0;
       0,0,-1,2,-1; 0,0,0,-1,2]
  let x : Fin 5 → ℝ := ![Real.sqrt 2, 2 * Real.sqrt 2, 3, 2, 1]
  have hsymm (i j : Fin 5) : M j i = M i j := by simpa using hM.isHermitian.apply i j
  have h10 : M 1 0 ≤ -1 := by rw [hsymm]; exact h01
  have h21 : M 2 1 ≤ -Real.sqrt 2 := by rw [hsymm]; exact h12
  have h32 : M 3 2 ≤ -1 := by rw [hsymm]; exact h23
  have h43 : M 4 3 ≤ -1 := by rw [hsymm]; exact h34
  have hMN : ∀ i j, M i j ≤ N i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [N] <;>
      first | exact (hd _).le | assumption | exact hoff _ _ (by decide)
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hN : x ⬝ᵥ (N *ᵥ x) = 0 := by
    norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, x, N]
    nlinarith
  have hx : x ≠ 0 := by
    intro hz
    have := congrFun hz 4
    norm_num [x] at this
  have hpos := hM.dotProduct_mulVec_pos hx
  simp only [star_trivial] at hpos
  have hle := quadraticForm_le_of_entrywise hMN (x := x) (by
    intro i; fin_cases i <;> norm_num [x] <;> positivity)
  rw [hN] at hle
  linarith

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open Module
lemma dynkin_no_interior_double {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (e : Fin 5 ↪ ι)
    (hpath : ∀ i j : Fin 5, i.val + 1 = j.val →
      (dynkinDiagram b).edges (e i) (e j) ≠ 0)
    (hdouble : 2 ≤ (dynkinDiagram b).edges (e 1) (e 2)) : False := by
  have : Finite ι := hb.finite_index hR
  apply no_interior_double_matrix ((normalizedSimpleGram b).submatrix e e)
    ((normalizedSimpleGram_posDef b).submatrix e.injective)
  · exact fun i => normalizedSimpleGram_diag b (e i)
  · exact fun i j h => normalizedSimpleGram_nonpos hR hv b hb (e.injective.ne h)
  · exact normalizedSimpleGram_edge_le hR hv b hb (hpath 0 1 rfl)
  · change normalizedSimpleGram b (e 1) (e 2) ≤ -Real.sqrt 2
    rw [normalizedSimpleGram_offDiag hR hv b hb (e.injective.ne (by decide))]
    exact neg_le_neg (Real.sqrt_le_sqrt (by exact_mod_cast hdouble))
  · exact normalizedSimpleGram_edge_le hR hv b hb (hpath 2 3 rfl)
  · exact normalizedSimpleGram_edge_le hR hv b hb (hpath 3 4 rfl)

lemma dynkin_unique_branch_vertex {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected)
    {x y : ι} (ex ey : Fin 3 ↪ ι)
    (hx : ∀ i, (dynkinDiagram b).edges x (ex i) ≠ 0)
    (hy : ∀ i, (dynkinDiagram b).edges y (ey i) ≠ 0) : x = y := by
  by_contra hxy
  have ht := (dynkin_tree R hR v hv b hb).2 hc
  obtain ⟨n, e, _, _, hp, h0, h1, h2, h3⟩ :=
    ht.exists_path_four_neighbors hxy ex ey
      (fun i => (simpleRootGraph_adj_iff hR hv hb x (ex i)).mpr (hx i))
      (fun i => (simpleRootGraph_adj_iff hR hv hb y (ey i)).mpr (hy i))
  let a : Fin 4 → Fin (n + 1) := ![0, 0, Fin.last n, Fin.last n]
  have hsum := dynkin_path_attachment_bound R hR v hv b hb n e
    (fun i j hij => (simpleRootGraph_adj_iff hR hv hb _ _).mp (hp i j hij)) a
  have hn0 := Nat.one_le_iff_ne_zero.mpr ((simpleRootGraph_adj_iff hR hv hb _ _).mp h0)
  have hn1 := Nat.one_le_iff_ne_zero.mpr ((simpleRootGraph_adj_iff hR hv hb _ _).mp h1)
  have hn2 := Nat.one_le_iff_ne_zero.mpr ((simpleRootGraph_adj_iff hR hv hb _ _).mp h2)
  have hn3 := Nat.one_le_iff_ne_zero.mpr ((simpleRootGraph_adj_iff hR hv hb _ _).mp h3)
  norm_num [Fin.sum_univ_succ, a] at hsum
  norm_cast at hsum
  omega


/-- A connected diagram containing a branch has only single edges. -/
lemma dynkin_branch_edges_le_one {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected) (x : ι) (ex : Fin 3 ↪ ι)
    (hx : ∀ i, (dynkinDiagram b).edges x (ex i) ≠ 0) :
    ∀ y z, (dynkinDiagram b).edges y z ≤ 1 := by
  intro y z
  by_contra hn
  have he : 2 ≤ (dynkinDiagram b).edges y z := by omega
  have ht := (dynkin_tree R hR v hv b hb).2 hc
  obtain ⟨n, e, _, hp, h0, h1, horder⟩ :=
    ht.exists_path_branch_edge x y z ex
      (fun i => (simpleRootGraph_adj_iff hR hv hb x (ex i)).mpr (hx i))
      ((simpleRootGraph_adj_iff hR hv hb y z).mpr (by omega))
  let a : Fin 3 → Fin (n + 1) := ![0, 0, Fin.last n]
  have hsum := dynkin_path_attachment_bound R hR v hv b hb n e
    (fun i j hij => (simpleRootGraph_adj_iff hR hv hb _ _).mp (hp i j hij)) a
  have hn0 := Nat.one_le_iff_ne_zero.mpr ((simpleRootGraph_adj_iff hR hv hb _ _).mp h0)
  have hn1 := Nat.one_le_iff_ne_zero.mpr ((simpleRootGraph_adj_iff hR hv hb _ _).mp h1)
  have hn2 : 2 ≤ (dynkinDiagram b).edges (e (.inl (Fin.last n))) (e (.inr 2)) := by
    rcases horder with ⟨hy, hz⟩ | ⟨hz, hy⟩
    · rwa [hy, hz]
    · rw [hy, hz, (dynkin_diagram_properties R hR v hv b hb).2.2.1]
      exact he
  norm_num [Fin.sum_univ_succ, a] at hsum
  norm_cast at hsum
  omega


section DynkinUniqueness
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

lemma diagram_iso_rank {t s : FiniteDynkinType} (h : t.diagram.Isomorphic s.diagram) :
    t.rank = s.rank := by
  obtain ⟨f, _, _⟩ := h
  exact Fintype.card_fin t.rank ▸ Fintype.card_fin s.rank ▸ Fintype.card_congr f

lemma B_arrow {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (FiniteDynkinType.B n hn).diagram.arrow i j ↔
      i.val + 2 = n ∧ j.val + 1 = n := by
  simp only [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.C,
    Matrix.of_apply]
  split_ifs <;> norm_num <;> omega

lemma C_arrow {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (FiniteDynkinType.C n hn).diagram.arrow i j ↔
      i.val + 1 = n ∧ j.val + 2 = n := by
  simp only [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.B,
    Matrix.of_apply]
  split_ifs <;> norm_num <;> omega

lemma B_edges_nonzero {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (FiniteDynkinType.B n hn).diagram.edges i j ≠ 0 ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.C,
    Matrix.of_apply]
  split_ifs <;> norm_num <;> omega

lemma C_edges_nonzero {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (FiniteDynkinType.C n hn).diagram.edges i j ≠ 0 ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.B,
    Matrix.of_apply]
  split_ifs <;> norm_num <;> omega

lemma B_arrow_target_leaf {n : ℕ} (hn : 2 ≤ n) (i j k : Fin n)
    (ha : (FiniteDynkinType.B n hn).diagram.arrow i j)
    (he : (FiniteDynkinType.B n hn).diagram.edges j k ≠ 0) : k = i := by
  apply Fin.ext
  have hai := (B_arrow hn i j).mp ha
  have hei := (B_edges_nonzero hn j k).mp he
  omega

lemma not_B_C_iso {n : ℕ} (hn : 3 ≤ n) :
    ¬(FiniteDynkinType.B n (by omega)).diagram.Isomorphic
      (FiniteDynkinType.C n (by omega)).diagram := by
  rintro ⟨f, hedges, harrows⟩
  dsimp only [FiniteDynkinType.rank] at f hedges harrows ⊢
  let i : Fin n := ⟨n-1, by omega⟩
  let j : Fin n := ⟨n-2, by omega⟩
  let k : Fin n := ⟨n-3, by omega⟩
  have ha : (FiniteDynkinType.B n (by omega)).diagram.arrow
      (f.symm i) (f.symm j) := by
    apply (harrows _ _).mpr
    apply (C_arrow (by omega) _ _).mpr
    have hfi := congrArg Fin.val (f.apply_symm_apply i)
    have hfj := congrArg Fin.val (f.apply_symm_apply j)
    have hi : i.val + 1 = n := by dsimp [i]; omega
    have hj : j.val + 2 = n := by dsimp [j]; omega
    omega
  have he : (FiniteDynkinType.B n (by omega)).diagram.edges
      (f.symm j) (f.symm k) ≠ 0 := by
    rw [hedges]
    apply (C_edges_nonzero (by omega) _ _).mpr
    have hfj := congrArg Fin.val (f.apply_symm_apply j)
    have hfk := congrArg Fin.val (f.apply_symm_apply k)
    have hj : j.val + 2 = n := by dsimp [j]; omega
    have hk : k.val + 3 = n := by dsimp [k]; omega
    omega
  have h := B_arrow_target_leaf (by omega) (f.symm i) (f.symm j) (f.symm k) ha he
  have hik : k = i := f.symm.injective h
  have hv := congrArg Fin.val hik
  dsimp [i, k] at hv
  omega

def DynkinDiagram.ArrowIntoLeaf {ι : Type*} (d : DynkinDiagram ι) : Prop :=
  ∃ i j, d.arrow i j ∧ ∀ k, d.edges j k ≠ 0 → k = i

def DynkinDiagram.ArrowOutOfLeaf {ι : Type*} (d : DynkinDiagram ι) : Prop :=
  ∃ i j, d.arrow i j ∧ ∀ k, d.edges i k ≠ 0 → k = j

lemma DynkinDiagram.Isomorphic.symm {ι κ : Type*} {d : DynkinDiagram ι}
    {e : DynkinDiagram κ} (h : d.Isomorphic e) : e.Isomorphic d := by
  obtain ⟨f, he, ha⟩ := h
  refine ⟨f.symm, ?_, ?_⟩
  · intro i j
    simpa only [Equiv.apply_symm_apply] using (he (f.symm i) (f.symm j)).symm
  · intro i j
    simpa only [Equiv.apply_symm_apply] using (ha (f.symm i) (f.symm j)).symm

lemma DynkinDiagram.Isomorphic.arrowIntoLeaf {ι κ : Type*} {d : DynkinDiagram ι}
    {e : DynkinDiagram κ} (h : d.Isomorphic e) (hL : d.ArrowIntoLeaf) : e.ArrowIntoLeaf := by
  obtain ⟨f, he, ha⟩ := h
  obtain ⟨i, j, hij, hL⟩ := hL
  refine ⟨f i, f j, (ha i j).mp hij, ?_⟩
  intro k hk
  have hk' : d.edges j (f.symm k) ≠ 0 := by
    rw [he, Equiv.apply_symm_apply]
    exact hk
  have hp := congrArg f (hL (f.symm k) hk')
  simpa only [Equiv.apply_symm_apply] using hp

lemma DynkinDiagram.Isomorphic.arrowOutOfLeaf {ι κ : Type*} {d : DynkinDiagram ι}
    {e : DynkinDiagram κ} (h : d.Isomorphic e) (hL : d.ArrowOutOfLeaf) : e.ArrowOutOfLeaf := by
  obtain ⟨f, he, ha⟩ := h
  obtain ⟨i, j, hij, hL⟩ := hL
  refine ⟨f i, f j, (ha i j).mp hij, ?_⟩
  intro k hk
  have hk' : d.edges i (f.symm k) ≠ 0 := by
    rw [he, Equiv.apply_symm_apply]
    exact hk
  have hp := congrArg f (hL (f.symm k) hk')
  simpa only [Equiv.apply_symm_apply] using hp

lemma B_arrowIntoLeaf {n : ℕ} (hn : 2 ≤ n) :
    (FiniteDynkinType.B n hn).diagram.ArrowIntoLeaf := by
  let i : Fin n := ⟨n-2, by omega⟩
  let j : Fin n := ⟨n-1, by omega⟩
  have hij : (FiniteDynkinType.B n hn).diagram.arrow i j :=
    (B_arrow hn i j).mpr (by dsimp [i, j]; omega)
  exact ⟨i, j, hij, fun k hk => B_arrow_target_leaf hn i j k hij hk⟩

lemma C_arrowOutOfLeaf {n : ℕ} (hn : 2 ≤ n) :
    (FiniteDynkinType.C n hn).diagram.ArrowOutOfLeaf := by
  let i : Fin n := ⟨n-1, by omega⟩
  let j : Fin n := ⟨n-2, by omega⟩
  refine ⟨i, j, (C_arrow hn i j).mpr (by dsimp [i, j]; omega), ?_⟩
  intro k hk
  have hkbound : k.val < n := k.isLt
  have hei := (C_edges_nonzero hn i k).mp hk
  apply Fin.ext
  dsimp [i, j] at hei ⊢
  omega

lemma F4_not_arrowIntoLeaf : ¬ FiniteDynkinType.F4.diagram.ArrowIntoLeaf := by
  unfold DynkinDiagram.ArrowIntoLeaf FiniteDynkinType.diagram FiniteDynkinType.cartan
    FiniteDynkinType.rank
  decide

lemma F4_not_arrowOutOfLeaf : ¬ FiniteDynkinType.F4.diagram.ArrowOutOfLeaf := by
  unfold DynkinDiagram.ArrowOutOfLeaf FiniteDynkinType.diagram FiniteDynkinType.cartan
    FiniteDynkinType.rank
  decide

lemma not_B_F4_iso {n : ℕ} (hn : 2 ≤ n) :
    ¬ (FiniteDynkinType.B n hn).diagram.Isomorphic FiniteDynkinType.F4.diagram := by
  intro h
  exact F4_not_arrowIntoLeaf (h.arrowIntoLeaf (B_arrowIntoLeaf hn))

lemma not_C_F4_iso {n : ℕ} (hn : 2 ≤ n) :
    ¬ (FiniteDynkinType.C n hn).diagram.Isomorphic FiniteDynkinType.F4.diagram := by
  intro h
  exact F4_not_arrowOutOfLeaf (h.arrowOutOfLeaf (C_arrowOutOfLeaf hn))

lemma B_edges_le_two {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (FiniteDynkinType.B n hn).diagram.edges i j ≤ 2 := by
  simp only [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.C,
    Matrix.of_apply]
  split_ifs <;> norm_num <;> omega

lemma C_edges_le_two {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (FiniteDynkinType.C n hn).diagram.edges i j ≤ 2 := by
  simp only [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.B,
    Matrix.of_apply]
  split_ifs <;> norm_num <;> omega

lemma not_B_G2_iso {n : ℕ} (hn : 2 ≤ n) :
    ¬ (FiniteDynkinType.B n hn).diagram.Isomorphic FiniteDynkinType.G2.diagram := by
  rintro ⟨f, he, _⟩
  dsimp only [FiniteDynkinType.rank] at f he
  have hi := B_edges_le_two hn (f.symm 0) (f.symm 1)
  have hz := he (f.symm 0) (f.symm 1)
  have hG : FiniteDynkinType.G2.diagram.edges (f (f.symm 0)) (f (f.symm 1)) = 3 := by
    rw [f.apply_symm_apply, f.apply_symm_apply]
    decide
  omega

lemma not_C_G2_iso {n : ℕ} (hn : 2 ≤ n) :
    ¬ (FiniteDynkinType.C n hn).diagram.Isomorphic FiniteDynkinType.G2.diagram := by
  rintro ⟨f, he, _⟩
  dsimp only [FiniteDynkinType.rank] at f he
  have hi := C_edges_le_two hn (f.symm 0) (f.symm 1)
  have hz := he (f.symm 0) (f.symm 1)
  have hG : FiniteDynkinType.G2.diagram.edges (f (f.symm 0)) (f (f.symm 1)) = 3 := by
    rw [f.apply_symm_apply, f.apply_symm_apply]
    decide
  omega

lemma diagram_no_arrow_of_symm (t : FiniteDynkinType) (h : t.cartan.IsSymm) :
    ∀ i j, ¬ t.diagram.arrow i j := by
  intro i j ha
  have hs : t.cartan j i = t.cartan i j := h.apply i j
  exact (lt_irrefl (t.cartan i j)) (hs ▸ ha.2)

def FiniteDynkinType.IsMultiplyLaced : FiniteDynkinType → Prop
  | .B _ _ | .C _ _ | .F4 | .G2 => True
  | _ => False

lemma multiplyLaced_iff_arrow (t : FiniteDynkinType) :
    t.IsMultiplyLaced ↔ ∃ i j, t.diagram.arrow i j := by
  cases t with
  | A n hn =>
    simp only [FiniteDynkinType.IsMultiplyLaced, false_iff, not_exists]
    exact diagram_no_arrow_of_symm _ (CartanMatrix.A_isSymm n)
  | B n hn =>
    simp only [FiniteDynkinType.IsMultiplyLaced, true_iff]
    obtain ⟨i, j, ha, _⟩ := B_arrowIntoLeaf hn
    exact ⟨i, j, ha⟩
  | C n hn =>
    simp only [FiniteDynkinType.IsMultiplyLaced, true_iff]
    obtain ⟨i, j, ha, _⟩ := C_arrowOutOfLeaf hn
    exact ⟨i, j, ha⟩
  | D n hn =>
    simp only [FiniteDynkinType.IsMultiplyLaced, false_iff, not_exists]
    exact diagram_no_arrow_of_symm _ (CartanMatrix.D_isSymm n)
  | E6 =>
    simp only [FiniteDynkinType.IsMultiplyLaced, false_iff, not_exists]
    exact diagram_no_arrow_of_symm _ (CartanMatrix.E_isSymm 6)
  | E7 =>
    simp only [FiniteDynkinType.IsMultiplyLaced, false_iff, not_exists]
    exact diagram_no_arrow_of_symm _ (CartanMatrix.E_isSymm 7)
  | E8 =>
    simp only [FiniteDynkinType.IsMultiplyLaced, false_iff, not_exists]
    exact diagram_no_arrow_of_symm _ (CartanMatrix.E_isSymm 8)
  | F4 =>
    simp only [FiniteDynkinType.IsMultiplyLaced, true_iff]
    exact ⟨(2 : Fin 4), (1 : Fin 4), by norm_num [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.F₄, CartanMatrix.G₂]⟩
  | G2 =>
    simp only [FiniteDynkinType.IsMultiplyLaced, true_iff]
    exact ⟨(1 : Fin 2), (0 : Fin 2), by norm_num [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.F₄, CartanMatrix.G₂]⟩

lemma DynkinDiagram.Isomorphic.multiplyLaced {t s : FiniteDynkinType}
    (h : t.diagram.Isomorphic s.diagram) : t.IsMultiplyLaced ↔ s.IsMultiplyLaced := by
  suffices ∀ t s : FiniteDynkinType, t.diagram.Isomorphic s.diagram →
      t.IsMultiplyLaced → s.IsMultiplyLaced from
    ⟨this t s h, this s t h.symm⟩
  intro t s h ht
  obtain ⟨i, j, ha⟩ := (multiplyLaced_iff_arrow t).mp ht
  obtain ⟨f, _, hf⟩ := h
  exact (multiplyLaced_iff_arrow s).mpr ⟨f i, f j, (hf i j).mp ha⟩

lemma dynkin_multiplyLaced_uniqueness (t s : FiniteDynkinType)
    (ht : t.IsMultiplyLaced) (h : t.diagram.Isomorphic s.diagram) :
    t = s ∨
    (t = .B 2 (by decide) ∧ s = .C 2 (by decide)) ∨
    (t = .C 2 (by decide) ∧ s = .B 2 (by decide)) := by
  have hs := h.multiplyLaced.mp ht
  have hr := diagram_iso_rank h
  cases t <;> cases s <;>
    simp only [FiniteDynkinType.IsMultiplyLaced] at ht hs <;> try contradiction
  all_goals simp only [FiniteDynkinType.rank] at hr
  all_goals try (left; subst_vars; rfl)
  all_goals try (exact False.elim (not_B_F4_iso _ h))
  all_goals try (exact False.elim (not_C_F4_iso _ h))
  all_goals try (exact False.elim (not_B_F4_iso _ h.symm))
  all_goals try (exact False.elim (not_C_F4_iso _ h.symm))
  all_goals try (exact False.elim (not_B_G2_iso _ h))
  all_goals try (exact False.elim (not_C_G2_iso _ h))
  all_goals try (exact False.elim (not_B_G2_iso _ h.symm))
  all_goals try (exact False.elim (not_C_G2_iso _ h.symm))
  · rename_i n hn m hm
    subst m
    have hn2 : n = 2 := by
      by_contra hn2
      exact not_B_C_iso (by omega) h
    right; left; subst n; exact ⟨rfl, rfl⟩
  · rename_i n hn m hm
    subst m
    have hn2 : n = 2 := by
      by_contra hn2
      exact not_B_C_iso (by omega) h.symm
    right; right; subst n; exact ⟨rfl, rfl⟩

def DynkinDiagram.HasCherry {ι : Type*} (d : DynkinDiagram ι) : Prop :=
  ∃ i j k, i ≠ j ∧ d.edges i k ≠ 0 ∧ d.edges j k ≠ 0 ∧
    (∀ x, d.edges i x ≠ 0 → x = k) ∧ (∀ x, d.edges j x ≠ 0 → x = k)

lemma DynkinDiagram.Isomorphic.hasCherry {ι κ : Type*} {d : DynkinDiagram ι}
    {e : DynkinDiagram κ} (h : d.Isomorphic e) (hC : d.HasCherry) : e.HasCherry := by
  obtain ⟨f, he, _⟩ := h
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj⟩ := hC
  refine ⟨f i, f j, f k, f.injective.ne hij, ?_, ?_, ?_, ?_⟩
  · rwa [← he]
  · rwa [← he]
  · intro x hx
    have hx' : d.edges i (f.symm x) ≠ 0 := by
      rw [he, Equiv.apply_symm_apply]
      exact hx
    have hp := congrArg f (hi _ hx')
    simpa only [Equiv.apply_symm_apply] using hp
  · intro x hx
    have hx' : d.edges j (f.symm x) ≠ 0 := by
      rw [he, Equiv.apply_symm_apply]
      exact hx
    have hp := congrArg f (hj _ hx')
    simpa only [Equiv.apply_symm_apply] using hp

lemma D_edges_nonzero {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    (FiniteDynkinType.D n hn).diagram.edges i j ≠ 0 ↔
      (i.val + 1 = j.val ∧ j.val + 2 < n) ∨
      (j.val + 1 = i.val ∧ i.val + 2 < n) ∨
      (i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n)) ∨
      (j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n)) := by
  simp only [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.D,
    Matrix.of_apply]
  split_ifs <;> norm_num <;> omega

lemma D_hasCherry {n : ℕ} (hn : 4 ≤ n) :
    (FiniteDynkinType.D n hn).diagram.HasCherry := by
  let i : Fin n := ⟨n-2, by omega⟩
  let j : Fin n := ⟨n-1, by omega⟩
  let k : Fin n := ⟨n-3, by omega⟩
  refine ⟨i, j, k, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Fin.val h; dsimp [i, j] at this; omega
  · apply (D_edges_nonzero hn i k).mpr; dsimp [i, k]; omega
  · apply (D_edges_nonzero hn j k).mpr; dsimp [j, k]; omega
  · intro x hx
    have hxbound : x.val < n := x.isLt
    have hp := (D_edges_nonzero hn i x).mp hx
    apply Fin.ext
    dsimp [i, k] at hp ⊢
    omega
  · intro x hx
    have hxbound : x.val < n := x.isLt
    have hp := (D_edges_nonzero hn j x).mp hx
    apply Fin.ext
    dsimp [j, k] at hp ⊢
    omega

lemma E6_not_hasCherry : ¬ FiniteDynkinType.E6.diagram.HasCherry := by
  unfold DynkinDiagram.HasCherry FiniteDynkinType.diagram FiniteDynkinType.cartan
    FiniteDynkinType.rank
  decide

lemma E7_not_hasCherry : ¬ FiniteDynkinType.E7.diagram.HasCherry := by
  unfold DynkinDiagram.HasCherry FiniteDynkinType.diagram FiniteDynkinType.cartan
    FiniteDynkinType.rank
  decide

lemma E8_not_hasCherry : ¬ FiniteDynkinType.E8.diagram.HasCherry := by
  unfold DynkinDiagram.HasCherry FiniteDynkinType.diagram FiniteDynkinType.cartan
    FiniteDynkinType.rank
  decide

def DynkinDiagram.HasBranch {ι : Type*} (d : DynkinDiagram ι) : Prop :=
  ∃ c i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ d.edges c i ≠ 0 ∧
    d.edges c j ≠ 0 ∧ d.edges c k ≠ 0

lemma DynkinDiagram.Isomorphic.hasBranch {ι κ : Type*} {d : DynkinDiagram ι}
    {e : DynkinDiagram κ} (h : d.Isomorphic e) (hB : d.HasBranch) : e.HasBranch := by
  obtain ⟨f, he, _⟩ := h
  obtain ⟨c, i, j, k, hij, hik, hjk, hi, hj, hk⟩ := hB
  refine ⟨f c, f i, f j, f k, f.injective.ne hij, f.injective.ne hik,
    f.injective.ne hjk, ?_, ?_, ?_⟩ <;> rwa [← he]

lemma A_edges_nonzero {n : ℕ} (hn : 1 ≤ n) (i j : Fin n) :
    (FiniteDynkinType.A n hn).diagram.edges i j ≠ 0 ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [FiniteDynkinType.diagram, FiniteDynkinType.cartan, CartanMatrix.A,
    Matrix.of_apply]
  split_ifs <;> norm_num <;> omega

lemma A_not_hasBranch {n : ℕ} (hn : 1 ≤ n) :
    ¬ (FiniteDynkinType.A n hn).diagram.HasBranch := by
  rintro ⟨c, i, j, k, hij, hik, hjk, hi, hj, hk⟩
  have hi' := (A_edges_nonzero hn c i).mp hi
  have hj' := (A_edges_nonzero hn c j).mp hj
  have hk' := (A_edges_nonzero hn c k).mp hk
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  omega

lemma D_hasBranch {n : ℕ} (hn : 4 ≤ n) :
    (FiniteDynkinType.D n hn).diagram.HasBranch := by
  let c : Fin n := ⟨n-3, by omega⟩
  let i : Fin n := ⟨n-4, by omega⟩
  let j : Fin n := ⟨n-2, by omega⟩
  let k : Fin n := ⟨n-1, by omega⟩
  refine ⟨c, i, j, k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Fin.val h; dsimp [i, j] at this; omega
  · intro h; have := congrArg Fin.val h; dsimp [i, k] at this; omega
  · intro h; have := congrArg Fin.val h; dsimp [j, k] at this; omega
  · apply (D_edges_nonzero hn c i).mpr; dsimp [c, i]; omega
  · apply (D_edges_nonzero hn c j).mpr; dsimp [c, j]; omega
  · apply (D_edges_nonzero hn c k).mpr; dsimp [c, k]; omega

lemma E6_hasBranch : FiniteDynkinType.E6.diagram.HasBranch := by
  unfold DynkinDiagram.HasBranch FiniteDynkinType.diagram FiniteDynkinType.cartan
    FiniteDynkinType.rank
  decide

lemma E7_hasBranch : FiniteDynkinType.E7.diagram.HasBranch := by
  unfold DynkinDiagram.HasBranch FiniteDynkinType.diagram FiniteDynkinType.cartan
    FiniteDynkinType.rank
  decide

lemma E8_hasBranch : FiniteDynkinType.E8.diagram.HasBranch := by
  unfold DynkinDiagram.HasBranch FiniteDynkinType.diagram FiniteDynkinType.cartan
    FiniteDynkinType.rank
  decide

theorem dynkin_uniqueness : DynkinExhaustionSpecs.uniquenessType := by
  intro t s h
  by_cases ht : t.IsMultiplyLaced
  · exact dynkin_multiplyLaced_uniqueness t s ht h
  have hs : ¬ s.IsMultiplyLaced := fun hs => ht (h.multiplyLaced.mpr hs)
  have hr := diagram_iso_rank h
  cases t <;> cases s <;>
    simp only [FiniteDynkinType.IsMultiplyLaced] at ht hs <;> try contradiction
  all_goals simp only [FiniteDynkinType.rank] at hr
  all_goals try (left; subst_vars; rfl)
  all_goals try exact False.elim (A_not_hasBranch _ (h.hasBranch (D_hasBranch _)))
  all_goals try exact False.elim (A_not_hasBranch _ (h.symm.hasBranch (D_hasBranch _)))
  all_goals try exact False.elim (A_not_hasBranch _ (h.hasBranch E6_hasBranch))
  all_goals try exact False.elim (A_not_hasBranch _ (h.hasBranch E7_hasBranch))
  all_goals try exact False.elim (A_not_hasBranch _ (h.hasBranch E8_hasBranch))
  all_goals try exact False.elim (A_not_hasBranch _ (h.symm.hasBranch E6_hasBranch))
  all_goals try exact False.elim (A_not_hasBranch _ (h.symm.hasBranch E7_hasBranch))
  all_goals try exact False.elim (A_not_hasBranch _ (h.symm.hasBranch E8_hasBranch))
  all_goals try exact False.elim (E6_not_hasCherry (h.hasCherry (D_hasCherry _)))
  all_goals try exact False.elim (E7_not_hasCherry (h.hasCherry (D_hasCherry _)))
  all_goals try exact False.elim (E8_not_hasCherry (h.hasCherry (D_hasCherry _)))
  all_goals try exact False.elim (E6_not_hasCherry (h.symm.hasCherry (D_hasCherry _)))
  all_goals try exact False.elim (E7_not_hasCherry (h.symm.hasCherry (D_hasCherry _)))
  all_goals try exact False.elim (E8_not_hasCherry (h.symm.hasCherry (D_hasCherry _)))


end DynkinUniqueness

/-- The five-vertex obstruction forces every multiple edge to be an end
edge, except for the middle edge of a four-vertex chain. -/
lemma dynkin_chain_multiple_position_of_no_five
    {d : DynkinDiagram ι} (hs : ∀ i j, d.edges i j = d.edges j i)
    (hno5 : ∀ (f : Fin 5 ↪ ι),
      (∀ i j : Fin 5, i.val + 1 = j.val → d.edges (f i) (f j) ≠ 0) →
      2 ≤ d.edges (f 1) (f 2) → False)
    {N : ℕ} (e : Fin (N + 1) ↪ ι)
    (hpath : ∀ i j : Fin (N + 1), i.val + 1 = j.val → d.edges (e i) (e j) ≠ 0)
    (p : Fin N) (hp : 2 ≤ d.edges (e p.castSucc) (e p.succ)) :
    p.val = 0 ∨ p.val + 1 = N ∨ (N = 3 ∧ p.val = 1) := by
  by_cases hp0 : p.val = 0
  · exact Or.inl hp0
  by_cases hpN : p.val + 1 = N
  · exact Or.inr (Or.inl hpN)
  by_cases hN3 : N = 3
  · exact Or.inr (Or.inr ⟨hN3, by omega⟩)
  have hp1 : 1 ≤ p.val := by omega
  have hpN' : p.val + 2 ≤ N := by omega
  have hN4 : 4 ≤ N := by omega
  exfalso
  by_cases hpval : p.val = 1
  · let u : Fin 5 → Fin (N + 1) := fun i => ⟨p.val - 1 + i.val, by omega⟩
    have hu : Function.Injective u := by
      intro i j hij
      apply Fin.ext
      have := congrArg Fin.val hij
      dsimp [u] at this
      omega
    let f : Fin 5 ↪ ι := ⟨fun i => e (u i), fun _ _ h => hu (e.injective h)⟩
    have hu1 : u 1 = p.castSucc := by apply Fin.ext; dsimp [u]; omega
    have hu2 : u 2 = p.succ := by apply Fin.ext; dsimp [u]; omega
    apply hno5 f
    · intro i j hij
      change d.edges (e (u i)) (e (u j)) ≠ 0
      apply hpath
      dsimp [u]
      omega
    · change 2 ≤ d.edges (e (u 1)) (e (u 2))
      rw [hu1, hu2]
      exact hp
  · have hp2 : 2 ≤ p.val := by omega
    let u : Fin 5 → Fin (N + 1) := fun i => ⟨p.val + 2 - i.val, by omega⟩
    have hu : Function.Injective u := by
      intro i j hij
      apply Fin.ext
      have := congrArg Fin.val hij
      dsimp [u] at this
      omega
    let f : Fin 5 ↪ ι := ⟨fun i => e (u i), fun _ _ h => hu (e.injective h)⟩
    have hu1 : u 1 = p.succ := by apply Fin.ext; dsimp [u]
    have hu2 : u 2 = p.castSucc := by apply Fin.ext; dsimp [u]; omega
    apply hno5 f
    · intro i j hij
      change d.edges (e (u i)) (e (u j)) ≠ 0
      rw [hs]
      apply hpath
      dsimp [u]
      omega
    · change 2 ≤ d.edges (e (u 1)) (e (u 2))
      rw [hu1, hu2, hs]
      exact hp

/-- Every multiple edge of an embedded Dynkin chain is at an end, except
for the central edge of the four-vertex chain. -/
lemma dynkin_chain_multiple_position {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {N : ℕ} (e : Fin (N + 1) ↪ ι)
    (hpath : ∀ i j : Fin (N + 1), i.val + 1 = j.val →
      (dynkinDiagram b).edges (e i) (e j) ≠ 0)
    (p : Fin N)
    (hp : 2 ≤ (dynkinDiagram b).edges (e p.castSucc) (e p.succ)) :
    p.val = 0 ∨ p.val + 1 = N ∨ (N = 3 ∧ p.val = 1) := by
  exact dynkin_chain_multiple_position_of_no_five
    (dynkin_diagram_properties R hR v hv b hb).2.2.1
    (dynkin_no_interior_double hR hv hb) e hpath p hp


def chainCartan (n : ℕ) (p : Fin n) (a c : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if i = j then 2
    else if i = p.castSucc ∧ j = p.succ then a
    else if j = p.castSucc ∧ i = p.succ then c
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

lemma dynkin_chain_cartan {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {N : ℕ} (e : Fin (N + 1) ↪ ι)
    (hc : ∀ i j, (dynkinDiagram b).edges (e i) (e j) ≠ 0 ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (p : Fin N)
    (hu : ∀ q : Fin N, q ≠ p → (dynkinDiagram b).edges (e q.castSucc) (e q.succ) ≤ 1)
    (i j : Fin (N + 1)) :
    cartanMatrix b (e i) (e j) = chainCartan N p
      (cartanMatrix b (e p.castSucc) (e p.succ))
      (cartanMatrix b (e p.succ) (e p.castSucc)) i j := by
  by_cases hij : i = j
  · subst j
    simp only [chainCartan, ite_true]
    exact cartan_diagonal R hR v hv b hb _
  by_cases hforward : i = p.castSucc ∧ j = p.succ
  · rcases hforward with ⟨rfl,rfl⟩
    simp [chainCartan, Fin.ext_iff]
  by_cases hbackward : j = p.castSucc ∧ i = p.succ
  · rcases hbackward with ⟨rfl,rfl⟩
    simp [chainCartan, Fin.ext_iff]
  simp only [chainCartan, hij, hforward, hbackward, ite_false]
  have he : (dynkinDiagram b).edges (e i) (e j) ≤ 1 := by
    by_cases h : (dynkinDiagram b).edges (e i) (e j) = 0
    · omega
    rcases (hc i j).mp h with h | h
    · let q : Fin N := ⟨i.val, by omega⟩
      have hiq : i = q.castSucc := Fin.ext rfl
      have hjq : j = q.succ := by apply Fin.ext; dsimp [q]; omega
      have hqp : q ≠ p := by
        intro hqp
        exact hforward ⟨by simpa [hqp] using hiq, by simpa [hqp] using hjq⟩
      simpa [hiq,hjq] using hu q hqp
    · let q : Fin N := ⟨j.val, by omega⟩
      have hjq : j = q.castSucc := Fin.ext rfl
      have hiq : i = q.succ := by apply Fin.ext; dsimp [q]; omega
      have hqp : q ≠ p := by
        intro hqp
        exact hbackward ⟨by simpa [hqp] using hjq, by simpa [hqp] using hiq⟩
      rw [(dynkin_diagram_properties R hR v hv b hb).2.2.1]
      simpa [hiq,hjq] using hu q hqp
  rw [cartan_entry_of_edge_le_one hR hv hb (e.injective.ne hij) he]
  have hh := hc i j
  by_cases he0 : (dynkinDiagram b).edges (e i) (e j) = 0 <;> simp_all

lemma chainCartan_last_B {N : ℕ} (hN : 1 ≤ N) (p : Fin N) (hp : p.val + 1 = N) :
    chainCartan N p (-1) (-2) = fun i j => (CartanMatrix.C (N + 1) i j : ℝ) := by
  funext i j
  simp only [chainCartan, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ, Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_one]
  split_ifs <;> norm_num <;> omega

lemma chainCartan_last_C {N : ℕ} (hN : 1 ≤ N) (p : Fin N) (hp : p.val + 1 = N) :
    chainCartan N p (-2) (-1) = fun i j => (CartanMatrix.B (N + 1) i j : ℝ) := by
  funext i j
  simp only [chainCartan, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ, Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_one]
  split_ifs <;> norm_num <;> omega

lemma chainCartan_reverse {N : ℕ} (p : Fin N) (a c : ℝ) (i j : Fin (N + 1)) :
    chainCartan N p a c i.rev j.rev = chainCartan N p.rev c a i j := by
  have hr : i.rev.val + 1 = j.rev.val ∨ j.rev.val + 1 = i.rev.val ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
    have hi := Fin.add_rev_cast i
    have hj := Fin.add_rev_cast j
    omega
  simp only [chainCartan, Fin.rev_inj, Fin.rev_eq_iff, Fin.rev_castSucc, Fin.rev_succ, hr]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

lemma chainCartan_F4 : chainCartan 3 1 (-2) (-1) = fun i j => (CartanMatrix.F₄ i j : ℝ) := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [chainCartan, CartanMatrix.F₄]


/-- A terminal double edge identifies the full oriented B or C diagram. -/
lemma dynkin_of_chainCartan_at_last {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {N : ℕ} (e : Fin (N + 1) ≃ ι) (p : Fin N) (hp : p.val + 1 = N)
    (a c : ℝ) (hpair : (a = -1 ∧ c = -2) ∨ (a = -2 ∧ c = -1))
    (hm : ∀ i j, cartanMatrix b (e i) (e j) = chainCartan N p a c i j) :
    ∃ t : FiniteDynkinType, (dynkinDiagram b).Isomorphic t.diagram := by
  have hN : 1 ≤ N := by have := p.isLt; omega
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨.B (N + 1) (by omega), ?_⟩
    apply dynkin_isomorphic_of_cartan_reindex hR hv hb (.B (N + 1) (by omega)) e
    change ∀ i j : Fin (N + 1), cartanMatrix b (e i) (e j) = (CartanMatrix.C (N + 1) i j : ℝ)
    intro i j
    rw [hm]
    exact congrFun (congrFun (chainCartan_last_B hN p hp) i) j
  · refine ⟨.C (N + 1) (by omega), ?_⟩
    apply dynkin_isomorphic_of_cartan_reindex hR hv hb (.C (N + 1) (by omega)) e
    change ∀ i j : Fin (N + 1), cartanMatrix b (e i) (e j) = (CartanMatrix.B (N + 1) i j : ℝ)
    intro i j
    rw [hm]
    exact congrFun (congrFun (chainCartan_last_C hN p hp) i) j

/-- All oriented diagrams whose underlying graph is a chain are in the
finite list. No extra Cartan or classification certificate is assumed. -/
lemma dynkin_chain_classification {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected) {N : ℕ} (e : Fin (N + 1) ≃ ι)
    (hchain : ∀ i j, (dynkinDiagram b).edges (e i) (e j) ≠ 0 ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    ∃ t : FiniteDynkinType, (dynkinDiagram b).Isomorphic t.diagram := by
  classical
  have hpath : ∀ i j : Fin (N + 1), i.val + 1 = j.val →
      (dynkinDiagram b).edges (e i) (e j) ≠ 0 :=
    fun i j hij => (hchain i j).mpr (Or.inl hij)
  by_cases hmultiple : ∃ p : Fin N,
      2 ≤ (dynkinDiagram b).edges (e p.castSucc) (e p.succ)
  · obtain ⟨p, hp⟩ := hmultiple
    by_cases htriple : (dynkinDiagram b).edges (e p.castSucc) (e p.succ) = 3
    · exact ⟨.G2, dynkin_triple_classification R hR v hv b hb hc
        ⟨e p.castSucc, e p.succ, htriple⟩⟩
    have hu : ∀ q : Fin N, q ≠ p →
        (dynkinDiagram b).edges (e q.castSucc) (e q.succ) ≤ 1 := by
      intro q hqp
      by_contra hq
      apply hqp
      apply dynkin_chain_unique_multiple hR hv hb e.toEmbedding hpath q p ?_ hp
      change 2 ≤ (dynkinDiagram b).edges (e q.castSucc) (e q.succ)
      omega
    have hneq : e p.castSucc ≠ e p.succ := e.injective.ne (by
      intro h
      have := congrArg Fin.val h
      simp at this)
    have hvpair := cartan_pair_values hR hv hb hneq
    have hprod := dynkin_edges_cast hR hv hb hneq
    have hp' : (2 : ℝ) ≤ ((dynkinDiagram b).edges (e p.castSucc) (e p.succ) : ℝ) := by
      exact_mod_cast hp
    have htriple' : ((dynkinDiagram b).edges (e p.castSucc) (e p.succ) : ℝ) ≠ 3 := by
      exact_mod_cast htriple
    have hpair :
        (cartanMatrix b (e p.castSucc) (e p.succ) = -1 ∧
          cartanMatrix b (e p.succ) (e p.castSucc) = -2) ∨
        (cartanMatrix b (e p.castSucc) (e p.succ) = -2 ∧
          cartanMatrix b (e p.succ) (e p.castSucc) = -1) := by
      norm_num only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hvpair
      rcases hvpair with h | h | h | h | h | h <;>
        rcases h with ⟨h₁, h₂⟩ <;> simp_all
    have hm := dynkin_chain_cartan hR hv hb e.toEmbedding hchain p hu
    let a := cartanMatrix b (e p.castSucc) (e p.succ)
    let c := cartanMatrix b (e p.succ) (e p.castSucc)
    have hpair' : (a = -1 ∧ c = -2) ∨ (a = -2 ∧ c = -1) := hpair
    have hm' : ∀ i j, cartanMatrix b (e i) (e j) = chainCartan N p a c i j := hm
    have hreverse : ∀ i j, cartanMatrix b (e i.rev) (e j.rev) =
        chainCartan N p.rev c a i j := by
      intro i j
      rw [hm', chainCartan_reverse]
    have hpair_rev : (c = -1 ∧ a = -2) ∨ (c = -2 ∧ a = -1) := by
      rcases hpair' with ⟨ha, hc⟩ | ⟨ha, hc⟩
      · exact Or.inr ⟨hc, ha⟩
      · exact Or.inl ⟨hc, ha⟩
    rcases dynkin_chain_multiple_position hR hv hb e.toEmbedding hpath p hp with
      hp0 | hpN | ⟨hN, hp1⟩
    · exact dynkin_of_chainCartan_at_last hR hv hb (Fin.revPerm.trans e) p.rev
        (by simp only [Fin.val_rev]; omega) c a hpair_rev hreverse
    · exact dynkin_of_chainCartan_at_last hR hv hb e p hpN a c hpair' hm'
    · subst N
      have hpp : p = 1 := Fin.ext hp1
      subst p
      refine ⟨.F4, ?_⟩
      rcases hpair' with ⟨ha, hc⟩ | ⟨ha, hc⟩
      · apply dynkin_isomorphic_of_cartan_reindex hR hv hb .F4 (Fin.revPerm.trans e)
        change ∀ i j : Fin 4, cartanMatrix b (e i.rev) (e j.rev) = (CartanMatrix.F₄ i j : ℝ)
        intro i j
        rw [hreverse, ha, hc]
        have hr : (1 : Fin 3).rev = 1 := by decide
        rw [hr]
        exact congrFun (congrFun chainCartan_F4 i) j
      · apply dynkin_isomorphic_of_cartan_reindex hR hv hb .F4 e
        change ∀ i j : Fin 4, cartanMatrix b (e i) (e j) = (CartanMatrix.F₄ i j : ℝ)
        intro i j
        rw [hm', ha, hc]
        exact congrFun (congrFun chainCartan_F4 i) j
  · refine ⟨.A (N + 1) (by omega), dynkin_simply_laced_chain hR hv hb N e hchain ?_⟩
    intro x y
    by_contra hbad
    have hnonzero : (dynkinDiagram b).edges x y ≠ 0 := by omega
    let i := e.symm x
    let j := e.symm y
    have hxy : (dynkinDiagram b).edges (e i) (e j) = (dynkinDiagram b).edges x y := by
      simp [i, j]
    have hadj := (hchain i j).mp (by rwa [hxy])
    apply hmultiple
    rcases hadj with hadj | hadj
    · let p : Fin N := ⟨i.val, by have := j.isLt; omega⟩
      have hip : p.castSucc = i := Fin.ext rfl
      have hjp : p.succ = j := by apply Fin.ext; dsimp [p]; omega
      refine ⟨p, ?_⟩
      rw [hip, hjp, hxy]
      omega
    · let p : Fin N := ⟨j.val, by have := i.isLt; omega⟩
      have hip : p.succ = i := by apply Fin.ext; dsimp [p]; omega
      have hjp : p.castSucc = j := Fin.ext rfl
      refine ⟨p, ?_⟩
      rw [hip, hjp, (dynkin_diagram_properties R hR v hv b hb).2.2.1, hxy]
      omega

lemma dynkin_branch_neighbors {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (x : ι) (ex : Fin 3 ↪ ι)
    (hx : ∀ i, (dynkinDiagram b).edges x (ex i) ≠ 0)
    {y : ι} (hy : (dynkinDiagram b).edges x y ≠ 0) : ∃ i, ex i = y := by
  classical
  by_contra hn
  have hye (i : Fin 3) : y ≠ ex i := by intro h; exact hn ⟨i,h.symm⟩
  have hxe (i : Fin 3) : x ≠ ex i := ((dynkin_edges_ne_zero hR hv hb x (ex i)).mp (hx i)).1
  have hxy : x ≠ y := ((dynkin_edges_ne_zero hR hv hb x y).mp hy).1
  let f : Fin 5 ↪ ι := ⟨![x, ex 0, ex 1, ex 2, y], by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [ex.injective.ne (by decide : (0 : Fin 3) ≠ 1),
        ex.injective.ne (by decide : (0 : Fin 3) ≠ 2),
        ex.injective.ne (by decide : (1 : Fin 3) ≠ 2), Ne.symm]⟩
  apply dynkin_no_four_neighbors R hR v hv b hb f
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact hx 0
  · exact hx 1
  · exact hx 2
  · exact hy

lemma dynkin_degree_le_two_away_from_branch {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected) (x : ι) (ex : Fin 3 ↪ ι)
    (hx : ∀ i, (dynkinDiagram b).edges x (ex i) ≠ 0)
    (y : ι) (hyx : y ≠ x) (a c d : ι)
    (ha : (simpleRootGraph b).Adj y a) (hc' : (simpleRootGraph b).Adj y c)
    (hd : (simpleRootGraph b).Adj y d) : a = c ∨ a = d ∨ c = d := by
  by_contra hn
  have hac : a ≠ c := fun h => hn (Or.inl h)
  have had : a ≠ d := fun h => hn (Or.inr (Or.inl h))
  have hcd : c ≠ d := fun h => hn (Or.inr (Or.inr h))
  let ey : Fin 3 ↪ ι := ⟨![a,c,d], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]⟩
  apply hyx
  exact (dynkin_unique_branch_vertex hR hv hb hc ex ey hx (by
    intro i
    fin_cases i
    · exact (simpleRootGraph_adj_iff hR hv hb y a).mp ha
    · exact (simpleRootGraph_adj_iff hR hv hb y c).mp hc'
    · exact (simpleRootGraph_adj_iff hR hv hb y d).mp hd)).symm

lemma dynkin_chain_of_no_branch {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected)
    (hn : ¬∃ (x : ι) (ex : Fin 3 ↪ ι), ∀ i, (dynkinDiagram b).edges x (ex i) ≠ 0) :
    ∃ t : FiniteDynkinType, (dynkinDiagram b).Isomorphic t.diagram := by
  have : Finite ι := hb.finite_index hR
  have hdeg : ∀ (x a c d : ι), (simpleRootGraph b).Adj x a →
      (simpleRootGraph b).Adj x c → (simpleRootGraph b).Adj x d →
      a = c ∨ a = d ∨ c = d := by
    intro x a c d ha hc' hd
    by_contra hn'
    have hac : a ≠ c := fun h => hn' (Or.inl h)
    have had : a ≠ d := fun h => hn' (Or.inr (Or.inl h))
    have hcd : c ≠ d := fun h => hn' (Or.inr (Or.inr h))
    let ex : Fin 3 ↪ ι := ⟨![a,c,d], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]⟩
    apply hn
    refine ⟨x, ex, ?_⟩
    intro i
    fin_cases i
    · exact (simpleRootGraph_adj_iff hR hv hb x a).mp ha
    · exact (simpleRootGraph_adj_iff hR hv hb x c).mp hc'
    · exact (simpleRootGraph_adj_iff hR hv hb x d).mp hd
  obtain ⟨N, e, he⟩ := ((dynkin_tree R hR v hv b hb).2 hc).exists_chain_equiv hdeg
  exact dynkin_chain_classification hR hv hb hc e (by
    intro i j
    rw [← simpleRootGraph_adj_iff hR hv hb, he])

lemma dynkin_sorted_three_arms {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected) (x : ι) (ex : Fin 3 ↪ ι)
    (hx : ∀ i, (dynkinDiagram b).edges x (ex i) ≠ 0) :
    ∃ (l : Fin 3 → ℕ) (e : Unit ⊕ (Σ i : Fin 3, Fin (l i)) ≃ ι),
      (∀ i, 1 ≤ l i) ∧ l 0 ≤ l 1 ∧ l 1 ≤ l 2 ∧ e (.inl ()) = x ∧
      (∀ i k, (simpleRootGraph b).Adj x (e (.inr ⟨i, k⟩)) ↔ k.val = 0) ∧
      (∀ i j k m, (simpleRootGraph b).Adj (e (.inr ⟨i, k⟩)) (e (.inr ⟨j, m⟩)) ↔
        i = j ∧ (k.val + 1 = m.val ∨ m.val + 1 = k.val)) := by
  have : Finite ι := hb.finite_index hR
  obtain ⟨l, e, hl, he, hcenter, harm⟩ :=
    ((dynkin_tree R hR v hv b hb).2 hc).exists_three_arms_equiv x ex
      (fun i => (simpleRootGraph_adj_iff hR hv hb _ _).mpr (hx i))
      (by
        intro z hz
        obtain ⟨i, hi⟩ := dynkin_branch_neighbors hR hv hb x ex hx
          ((simpleRootGraph_adj_iff hR hv hb _ _).mp hz)
        exact ⟨i, hi.symm⟩)
      (by
        intro a c d f hax ha hc' hd
        exact dynkin_degree_le_two_away_from_branch hR hv hb hc x ex hx a hax c d f ha hc' hd)
  obtain ⟨σ, h01, h12⟩ := exists_fin_three_sorted_perm l
  let l' : Fin 3 → ℕ := fun i => l (σ i)
  let e' : Unit ⊕ (Σ i : Fin 3, Fin (l' i)) ≃ ι :=
    (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sigmaCongrLeft σ)).trans e
  refine ⟨l', e', fun i => hl (σ i), h01, h12, ?_, ?_, ?_⟩
  · exact he
  · intro i k
    exact hcenter (σ i) k
  · intro i j k m
    change (simpleRootGraph b).Adj (e (.inr ⟨σ i, k⟩)) (e (.inr ⟨σ j, m⟩)) ↔ _
    simpa only [σ.injective.eq_iff] using harm (σ i) (σ j) k m


section ArmInequality
set_option backward.isDefEq.respectTransparency.types false
open Matrix

def armChainMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if i = j then 2 else 0) - (if i.val + 1 = j.val then 1 else 0) -
    (if j.val + 1 = i.val then 1 else 0)

def chainRamp (n : ℕ) (i : Fin n) : ℝ := ((n : ℝ) - i.val) / ((n : ℝ) + 1)

lemma chainRamp_mulVec {n : ℕ} (i : Fin n) :
    (armChainMatrix n *ᵥ chainRamp n) i = if i.val = 0 then 1 else 0 := by
  have hd : ∑ j : Fin n, (if i = j then (2 : ℝ) else 0) * chainRamp n j =
      2 * chainRamp n i := by simp
  have hn : ∑ j : Fin n, (if i.val + 1 = j.val then (1 : ℝ) else 0) * chainRamp n j =
      if h : i.val + 1 < n then chainRamp n ⟨i.val+1, h⟩ else 0 := by
    split_ifs with h
    · have heq (j : Fin n) : i.val + 1 = j.val ↔ (⟨i.val+1, h⟩ : Fin n) = j := by
        exact ⟨fun hj => Fin.ext hj, fun hj => congrArg Fin.val hj⟩
      simp [heq, ite_mul]
    · have heq (j : Fin n) : ¬ i.val + 1 = j.val := by have := j.isLt; omega
      simp only [heq, ite_false, zero_mul, Finset.sum_const_zero]
  have hp : ∑ j : Fin n, (if j.val + 1 = i.val then (1 : ℝ) else 0) * chainRamp n j =
      if h : 0 < i.val then chainRamp n ⟨i.val-1, by omega⟩ else 0 := by
    split_ifs with h
    · have heq (j : Fin n) : j.val + 1 = i.val ↔ (⟨i.val-1, by omega⟩ : Fin n) = j := by
        constructor
        · intro hj
          apply Fin.ext
          change i.val - 1 = j.val
          omega
        · intro hj
          have hv := congrArg Fin.val hj
          change i.val - 1 = j.val at hv
          omega
      simp [heq, ite_mul]
    · have heq (j : Fin n) : ¬ j.val + 1 = i.val := by omega
      simp only [heq, ite_false, zero_mul, Finset.sum_const_zero]
  simp only [Matrix.mulVec, dotProduct, armChainMatrix, sub_mul, Finset.sum_sub_distrib]
  rw [hd, hn, hp]
  split_ifs with hnext hprev hzero <;> simp only [chainRamp, Fin.val_mk]
  all_goals have hin : i.val < n := i.isLt
  all_goals try have hi0 : i.val = 0 := by omega
  all_goals try have hinlast : i.val + 1 = n := by omega
  all_goals try simp only [Nat.cast_sub (show 1 ≤ i.val by omega), Nat.cast_add,
    Nat.cast_one]
  all_goals try have hi0r : (i.val : ℝ) = 0 := by exact_mod_cast hi0
  all_goals try have hlastR : (i.val : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hinlast
  all_goals try omega
  all_goals field_simp
  all_goals push_cast
  all_goals nlinarith

lemma chainRamp_first_sum (n : ℕ) :
    (∑ j : Fin n, (if j.val = 0 then (-1 : ℝ) else 0) * chainRamp n j) =
      -(n : ℝ) / ((n : ℝ) + 1) := by
  cases n with
  | zero => simp [chainRamp]
  | succ n =>
    simp [Fin.sum_univ_succ, chainRamp]
    ring

lemma blockDiagonal_chainRamp_mulVec {κ : Type*} [Fintype κ] [DecidableEq κ]
    (l : κ → ℕ) (a : κ) (i : Fin (l a)) :
    (Matrix.blockDiagonal' (fun a => armChainMatrix (l a)) *ᵥ
      (fun x : Σ a, Fin (l a) => chainRamp (l x.1) x.2)) ⟨a, i⟩ =
      if i.val = 0 then 1 else 0 := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
    exact chainRamp_mulVec i
  · intro b _ hab
    have hz (j : Fin (l b)) :
        Matrix.blockDiagonal' (fun a => armChainMatrix (l a)) ⟨a, i⟩ ⟨b, j⟩ = 0 :=
      Matrix.blockDiagonal'_apply_ne _ _ _ hab.symm
    simp only [hz, zero_mul, Finset.sum_const_zero]
  · simp

def armStarMatrix {κ : Type*} [DecidableEq κ] (l : κ → ℕ) :
    Matrix (Unit ⊕ (Σ a, Fin (l a))) (Unit ⊕ (Σ a, Fin (l a))) ℝ :=
  Matrix.fromBlocks (fun _ _ => 2)
    (fun _ x => if x.2.val = 0 then -1 else 0)
    (fun x _ => if x.2.val = 0 then -1 else 0)
    (Matrix.blockDiagonal' (fun a => armChainMatrix (l a)))

lemma armStarMatrix_mulVec {κ : Type*} [Fintype κ] [DecidableEq κ] (l : κ → ℕ) :
    armStarMatrix l *ᵥ
      (Sum.elim (fun _ => 1) (fun x : Σ a, Fin (l a) => chainRamp (l x.1) x.2)) =
    Sum.elim (fun _ => 2 - ∑ a, (l a : ℝ) / ((l a : ℝ) + 1)) (fun _ => 0) := by
  ext x
  rcases x with u | ⟨a, i⟩
  · simp only [armStarMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Sum.elim_inl, Sum.elim_inr,
      mul_one, Fintype.sum_unique, Fintype.sum_sigma]
    simp_rw [chainRamp_first_sum]
    simp [Finset.sum_neg_distrib, neg_div, sub_eq_add_neg]
  · simp only [armStarMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr,
      mul_one, Fintype.sum_unique]
    rw [show (∑ j, Matrix.blockDiagonal' (fun a => armChainMatrix (l a)) ⟨a, i⟩ j *
      chainRamp (l j.1) j.2) = if i.val = 0 then 1 else 0 from
      blockDiagonal_chainRamp_mulVec l a i]
    split_ifs <;> norm_num

lemma armStarMatrix_posDef_bound {κ : Type*} [Fintype κ] [DecidableEq κ] (l : κ → ℕ)
    (hM : (armStarMatrix l).PosDef) :
    0 < 2 - ∑ a, (l a : ℝ) / ((l a : ℝ) + 1) := by
  let x := Sum.elim (fun _ : Unit => (1 : ℝ))
    (fun y : Σ a, Fin (l a) => chainRamp (l y.1) y.2)
  have hx : x ≠ 0 := by
    intro hz
    have := congrFun hz (.inl ())
    norm_num [x] at this
  have hp := hM.dotProduct_mulVec_pos hx
  rw [show x = _ from rfl, armStarMatrix_mulVec] at hp
  simpa [dotProduct, Fintype.sum_sum_type, x] using hp

lemma armStarMatrix_three_arms {l : Fin 3 → ℕ} (hM : (armStarMatrix l).PosDef) :
    1 < ∑ a, 1 / ((l a : ℝ) + 1) := by
  have h := armStarMatrix_posDef_bound l hM
  have heq (a : Fin 3) : (l a : ℝ) / ((l a : ℝ) + 1) =
      1 - 1 / ((l a : ℝ) + 1) := by
    field_simp
    ring
  simp_rw [heq] at h
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  linarith

lemma armChainMatrix_eq_A (n : ℕ) (i j : Fin n) :
    armChainMatrix n i j = (CartanMatrix.A n i j : ℝ) := by
  simp only [armChainMatrix, CartanMatrix.A, Matrix.of_apply]
  split_ifs <;> norm_num <;> omega

lemma chainRamp_nonneg {n : ℕ} (i : Fin n) : 0 ≤ chainRamp n i := by
  unfold chainRamp
  have hi : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt i.isLt
  positivity

lemma embedded_star_matrix_bound (l : Fin 3 → ℕ)
    (M : Matrix (Unit ⊕ (Σ a, Fin (l a))) (Unit ⊕ (Σ a, Fin (l a))) ℝ)
    (hM : M.PosDef) (hd : ∀ i, M i i = 2)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hcenter : ∀ a (i : Fin (l a)), i.val = 0 → M (.inl ()) (.inr ⟨a, i⟩) ≤ -1)
    (hpath : ∀ a (i j : Fin (l a)), i.val + 1 = j.val →
      M (.inr ⟨a, i⟩) (.inr ⟨a, j⟩) ≤ -1) :
    1 < ∑ a, 1 / ((l a : ℝ) + 1) := by
  have hsymm (i j) : M j i = M i j := by simpa using hM.isHermitian.apply i j
  have hMN : ∀ i j, M i j ≤ armStarMatrix l i j := by
    intro i j
    rcases i with u | ⟨a, i⟩ <;> rcases j with v | ⟨b, j⟩
    · cases u; cases v
      change M (.inl ()) (.inl ()) ≤ 2
      exact (hd _).le
    · cases u
      change M (.inl ()) (.inr ⟨b, j⟩) ≤ if j.val = 0 then -1 else 0
      split_ifs with hj
      · exact hcenter b j hj
      · exact hoff _ _ (by simp)
    · cases v
      rw [hsymm]
      change M (.inl ()) (.inr ⟨a, i⟩) ≤ if i.val = 0 then -1 else 0
      split_ifs with hi
      · exact hcenter a i hi
      · exact hoff _ _ (by simp)
    · change M (.inr ⟨a, i⟩) (.inr ⟨b, j⟩) ≤
        Matrix.blockDiagonal' (fun a => armChainMatrix (l a)) ⟨a, i⟩ ⟨b, j⟩
      by_cases hab : a = b
      · subst b
        rw [Matrix.blockDiagonal'_apply_eq, armChainMatrix_eq_A]
        simp only [CartanMatrix.A, Matrix.of_apply]
        split_ifs with hij hnext <;> norm_num only [Int.cast_neg, Int.cast_one,
          Int.cast_zero, Int.cast_ofNat]
        · subst j; exact (hd _).le
        · rcases hnext with hnext | hprev
          · exact hpath a i j hnext
          · rw [hsymm]; exact hpath a j i hprev
        · exact hoff _ _ (by simpa only [ne_eq, Sum.inr.injEq,
            Sigma.mk.inj_iff, heq_eq_eq, true_and] using hij)
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab]
        exact hoff _ _ (by intro h; cases h; exact hab rfl)
  let x := Sum.elim (fun _ : Unit => (1 : ℝ))
    (fun y : Σ a, Fin (l a) => chainRamp (l y.1) y.2)
  have hxnonneg : ∀ i, 0 ≤ x i := by
    intro i; rcases i with u | ⟨a, i⟩
    · norm_num [x]
    · exact chainRamp_nonneg i
  have hx : x ≠ 0 := by
    intro hz
    have := congrFun hz (.inl ())
    norm_num [x] at this
  have hp := hM.dotProduct_mulVec_pos hx
  have hle : x ⬝ᵥ (M *ᵥ x) ≤ x ⬝ᵥ (armStarMatrix l *ᵥ x) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hxnonneg i)
    change (∑ j, M i j * x j) ≤ ∑ j, armStarMatrix l i j * x j
    exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (hMN i j) (hxnonneg j))
  have hq : 0 < x ⬝ᵥ (armStarMatrix l *ᵥ x) := lt_of_lt_of_le hp hle
  rw [show x = _ from rfl, armStarMatrix_mulVec] at hq
  have h : 0 < 2 - ∑ a, (l a : ℝ) / ((l a : ℝ) + 1) := by
    simpa [dotProduct, Fintype.sum_sum_type, x] using hq
  have heq (a : Fin 3) : (l a : ℝ) / ((l a : ℝ) + 1) =
      1 - 1 / ((l a : ℝ) + 1) := by
    field_simp
    ring
  simp_rw [heq] at h
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  linarith

lemma dynkin_three_arm_bound {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Module.Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {l : Fin 3 → ℕ} (e : Unit ⊕ (Σ a, Fin (l a)) ↪ ι)
    (hcenter : ∀ a (i : Fin (l a)), i.val = 0 →
      (dynkinDiagram b).edges (e (.inl ())) (e (.inr ⟨a, i⟩)) ≠ 0)
    (hpath : ∀ a (i j : Fin (l a)), i.val + 1 = j.val →
      (dynkinDiagram b).edges (e (.inr ⟨a, i⟩)) (e (.inr ⟨a, j⟩)) ≠ 0) :
    1 < ∑ a, 1 / ((l a : ℝ) + 1) := by
  have : Finite ι := hb.finite_index hR
  apply embedded_star_matrix_bound l ((normalizedSimpleGram b).submatrix e e)
    ((normalizedSimpleGram_posDef b).submatrix e.injective)
  · exact fun i => normalizedSimpleGram_diag b (e i)
  · exact fun i j hij => normalizedSimpleGram_nonpos hR hv b hb (e.injective.ne hij)
  · exact fun a i hi => normalizedSimpleGram_edge_le hR hv b hb (hcenter a i hi)
  · exact fun a i j hij => normalizedSimpleGram_edge_le hR hv b hb (hpath a i j hij)


end ArmInequality

abbrev DynkinArmVertex (l : Fin 3 → ℕ) := Unit ⊕ (Σ i : Fin 3, Fin (l i))

def threeArmAdj (l : Fin 3 → ℕ) : DynkinArmVertex l → DynkinArmVertex l → Prop
  | .inl _, .inl _ => False
  | .inl _, .inr ⟨_, k⟩ => k.val = 0
  | .inr ⟨_, k⟩, .inl _ => k.val = 0
  | .inr ⟨i, k⟩, .inr ⟨j, m⟩ => i = j ∧ (k.val + 1 = m.val ∨ m.val + 1 = k.val)

def threeArmCartan (l : Fin 3 → ℕ) : Matrix (DynkinArmVertex l) (DynkinArmVertex l) ℝ := by
  classical
  exact fun i j => if i = j then 2 else if threeArmAdj l i j then -1 else 0


lemma cartan_eq_threeArmCartan {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Module.Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {l : Fin 3 → ℕ} (e : DynkinArmVertex l ≃ ι)
    (ha : ∀ x y, (simpleRootGraph b).Adj (e x) (e y) ↔ threeArmAdj l x y)
    (hs : ∀ i j, (dynkinDiagram b).edges i j ≤ 1) :
    ∀ x y, cartanMatrix b (e x) (e y) = threeArmCartan l x y := by
  classical
  intro x y
  by_cases hxy : x = y
  · subst y
    simpa only [threeArmCartan, ite_true] using cartan_diagonal R hR v hv b hb (e x)
  · rw [cartan_entry_of_edge_le_one hR hv hb (e.injective.ne hxy) (hs _ _)]
    simp only [threeArmCartan, hxy, ite_false]
    have hadj : (dynkinDiagram b).edges (e x) (e y) ≠ 0 ↔ threeArmAdj l x y := by
      rw [← simpleRootGraph_adj_iff hR hv hb]
      exact ha x y
    by_cases he : (dynkinDiagram b).edges (e x) (e y) = 0
    · have hn : ¬ threeArmAdj l x y := fun h => (hadj.mpr h) he
      simp only [he, hn, ite_true, ite_false]
    · simp only [he, hadj.mp he, ite_false, ite_true]

lemma cartan_eq_threeArmCartan_of_arms {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Module.Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    {l : Fin 3 → ℕ} (e : DynkinArmVertex l ≃ ι)
    (hcenter : ∀ i k, (simpleRootGraph b).Adj (e (.inl ())) (e (.inr ⟨i, k⟩)) ↔ k.val = 0)
    (harm : ∀ i j k m, (simpleRootGraph b).Adj (e (.inr ⟨i, k⟩)) (e (.inr ⟨j, m⟩)) ↔
      i = j ∧ (k.val + 1 = m.val ∨ m.val + 1 = k.val))
    (hs : ∀ i j, (dynkinDiagram b).edges i j ≤ 1) :
    ∀ x y, cartanMatrix b (e x) (e y) = threeArmCartan l x y := by
  apply cartan_eq_threeArmCartan hR hv hb e _ hs
  intro x y
  rcases x with u | ⟨i,k⟩ <;> rcases y with v | ⟨j,m⟩
  · cases u; cases v
    simp [threeArmAdj]
  · cases u
    exact hcenter j m
  · cases v
    change (simpleRootGraph b).Adj (e (.inr ⟨i,k⟩)) (e (.inl ())) ↔ k.val = 0
    rw [(simpleRootGraph b).adj_comm]
    exact hcenter i k
  · exact harm i j k m


def armDIndex (c : ℕ) : DynkinArmVertex ![1,1,c] → Fin (c + 3)
  | .inl _ => ⟨c, by omega⟩
  | .inr ⟨i, k⟩ =>
    if i = 0 then ⟨c + 1, by omega⟩
    else if i = 1 then ⟨c + 2, by omega⟩
    else ⟨c - 1 - k.val, by omega⟩

lemma armDIndex_bijective (c : ℕ) : Function.Bijective (armDIndex c) := by
  constructor
  · intro x y h
    rcases x with x | ⟨i,k⟩ <;> rcases y with y | ⟨j,m⟩
    · cases x; cases y; rfl
    · fin_cases j <;> have hh := congrArg Fin.val h <;> simp [armDIndex] at hh <;> omega
    · fin_cases i <;> have hh := congrArg Fin.val h <;> simp [armDIndex] at hh <;> omega
    · fin_cases i <;> fin_cases j
      all_goals have hh := congrArg Fin.val h
      all_goals simp [armDIndex] at hh
      all_goals try omega
      all_goals congr 2
      all_goals apply Fin.ext
      all_goals simp at *
      all_goals omega
  · intro j
    by_cases hj0 : j.val = c
    · exact ⟨.inl (), Fin.ext hj0.symm⟩
    by_cases hj1 : j.val = c + 1
    · exact ⟨.inr ⟨0, ⟨0, by simp⟩⟩, by apply Fin.ext; simp [armDIndex, hj1]⟩
    by_cases hj2 : j.val = c + 2
    · exact ⟨.inr ⟨1, ⟨0, by simp⟩⟩, by apply Fin.ext; simp [armDIndex, hj2]⟩
    have hjc : j.val < c := by omega
    let k : Fin c := ⟨c - 1 - j.val, by omega⟩
    refine ⟨.inr ⟨2, k⟩, ?_⟩
    apply Fin.ext
    simp [armDIndex, k]
    omega

def armDEquiv (c : ℕ) : DynkinArmVertex ![1,1,c] ≃ Fin (c + 3) :=
  Equiv.ofBijective (armDIndex c) (armDIndex_bijective c)


abbrev dBranchAdj (n a b : ℕ) : Prop :=
  (a + 1 = b ∧ a + 2 < n) ∨
  (b + 1 = a ∧ b + 2 < n) ∨
  (a + 3 = n ∧ (b + 2 = n ∨ b + 1 = n)) ∨
  (b + 3 = n ∧ (a + 2 = n ∨ a + 1 = n))

lemma cartanD_apply_branch (n : ℕ) (hn : 3 ≤ n) (i j : Fin n) :
    (CartanMatrix.D n i j : ℝ) =
      if i = j then 2 else if dBranchAdj n i.val j.val then -1 else 0 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Int.cast_ite, Int.cast_ofNat,
    Int.cast_neg, Int.cast_one, Int.cast_zero, dBranchAdj]
  split_ifs <;> simp_all <;> omega

lemma threeArmAdj_D (c : ℕ) (hc : 1 ≤ c) (x y : DynkinArmVertex ![1,1,c]) :
    threeArmAdj ![1,1,c] x y ↔
      dBranchAdj (c + 3) (armDIndex c x).val (armDIndex c y).val := by
  rcases x with x | ⟨i,k⟩ <;> rcases y with y | ⟨j,m⟩
  · simp [threeArmAdj, armDIndex, dBranchAdj]
  · have hm := m.isLt
    fin_cases j <;> dsimp [threeArmAdj, armDIndex, dBranchAdj] at * <;> omega
  · have hk := k.isLt
    fin_cases i <;> dsimp [threeArmAdj, armDIndex, dBranchAdj] at * <;> omega
  · have hk := k.isLt
    have hm := m.isLt
    fin_cases i <;> fin_cases j <;>
      dsimp [threeArmAdj, armDIndex, dBranchAdj] at * <;> omega

lemma threeArmCartan_D (c : ℕ) (hc : 1 ≤ c) (x y : DynkinArmVertex ![1,1,c]) :
    threeArmCartan ![1,1,c] x y = (CartanMatrix.D (c + 3) (armDEquiv c x) (armDEquiv c y) : ℝ) := by
  change threeArmCartan ![1,1,c] x y = (CartanMatrix.D (c + 3) (armDIndex c x) (armDIndex c y) : ℝ)
  rw [cartanD_apply_branch (c + 3) (by omega)]
  have heq : (armDIndex c x = armDIndex c y) ↔ x = y := (armDIndex_bijective c).1.eq_iff
  simp only [threeArmCartan, heq, threeArmAdj_D c hc]

def armEIndex (c : ℕ) : DynkinArmVertex ![1,2,c] → Fin (c + 4)
  | .inl _ => ⟨3, by omega⟩
  | .inr ⟨i, k⟩ =>
    if hi : i = 0 then ⟨1, by omega⟩
    else if hj : i = 1 then ⟨2 - 2 * k.val, by omega⟩
    else ⟨4 + k.val, by have hk := k.isLt; fin_cases i <;> simp_all <;> omega⟩

lemma armEIndex_bijective (c : ℕ) : Function.Bijective (armEIndex c) := by
  constructor
  · intro x y h
    rcases x with x | ⟨i,k⟩ <;> rcases y with y | ⟨j,m⟩
    · cases x; cases y; rfl
    · have hm := m.isLt
      fin_cases j <;> have hh := congrArg Fin.val h <;> simp [armEIndex] at hh hm <;> omega
    · have hk := k.isLt
      fin_cases i <;> have hh := congrArg Fin.val h <;> simp [armEIndex] at hh hk <;> omega
    · have hk := k.isLt
      have hm := m.isLt
      fin_cases i <;> fin_cases j
      all_goals have hh := congrArg Fin.val h
      all_goals simp [armEIndex] at hh hk hm
      all_goals try omega
      all_goals congr 2
      all_goals apply Fin.ext
      all_goals omega
  · intro j
    by_cases hj0 : j.val = 0
    · refine ⟨.inr ⟨1, ⟨1, by simp⟩⟩, ?_⟩
      apply Fin.ext; simp [armEIndex, hj0]
    by_cases hj1 : j.val = 1
    · refine ⟨.inr ⟨0, ⟨0, by simp⟩⟩, ?_⟩
      apply Fin.ext; simp [armEIndex, hj1]
    by_cases hj2 : j.val = 2
    · refine ⟨.inr ⟨1, ⟨0, by simp⟩⟩, ?_⟩
      apply Fin.ext; simp [armEIndex, hj2]
    by_cases hj3 : j.val = 3
    · exact ⟨.inl (), Fin.ext hj3.symm⟩
    have hj4 : 4 ≤ j.val := by omega
    let k : Fin c := ⟨j.val - 4, by omega⟩
    refine ⟨.inr ⟨2, k⟩, ?_⟩
    apply Fin.ext
    simp [armEIndex, k]
    omega

def armEEquiv (c : ℕ) : DynkinArmVertex ![1,2,c] ≃ Fin (c + 4) :=
  Equiv.ofBijective (armEIndex c) (armEIndex_bijective c)

lemma armEIndex_adj (c : ℕ) (x y : DynkinArmVertex ![1,2,c]) :
    threeArmAdj ![1,2,c] x y ↔
      ((armEIndex c x).val = 0 ∧ (armEIndex c y).val = 2) ∨
      ((armEIndex c y).val = 0 ∧ (armEIndex c x).val = 2) ∨
      ((armEIndex c x).val = 1 ∧ (armEIndex c y).val = 3) ∨
      ((armEIndex c y).val = 1 ∧ (armEIndex c x).val = 3) ∨
      (2 ≤ (armEIndex c x).val ∧ (armEIndex c x).val + 1 = (armEIndex c y).val) ∨
      (2 ≤ (armEIndex c y).val ∧ (armEIndex c y).val + 1 = (armEIndex c x).val) := by
  rcases x with x | ⟨i,k⟩ <;> rcases y with y | ⟨j,m⟩
  · simp [threeArmAdj, armEIndex]
  · have hm := m.isLt
    fin_cases j <;> simp [threeArmAdj, armEIndex] at * <;> omega
  · have hk := k.isLt
    fin_cases i <;> simp [threeArmAdj, armEIndex] at * <;> omega
  · have hk := k.isLt
    have hm := m.isLt
    fin_cases i <;> fin_cases j <;> simp [threeArmAdj, armEIndex] at * <;> omega

lemma threeArmCartan_E (c : ℕ) (x y : DynkinArmVertex ![1,2,c]) :
    threeArmCartan ![1,2,c] x y =
      (CartanMatrix.E (c + 4) (armEEquiv c x) (armEEquiv c y) : ℝ) := by
  change threeArmCartan ![1,2,c] x y =
    (CartanMatrix.E (c + 4) (armEIndex c x) (armEIndex c y) : ℝ)
  have hxy : armEIndex c x = armEIndex c y ↔ x = y :=
    (armEIndex_bijective c).injective.eq_iff
  simp only [threeArmCartan, CartanMatrix.E, Matrix.of_apply, hxy,
    Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero]
  simp only [armEIndex_adj]


lemma threeArmCartan_classification (l : Fin 3 → ℕ)
    (hl : ∀ i, 1 ≤ l i) (h01 : l 0 ≤ l 1) (h12 : l 1 ≤ l 2)
    (hbound : 1 < ∑ a, 1 / ((l a : ℝ) + 1)) :
    ∃ (t : FiniteDynkinType) (f : DynkinArmVertex l ≃ Fin t.rank),
      ∀ i j, threeArmCartan l i j = (t.cartan (f i) (f j) : ℝ) := by
  have hnum := (dynkin_arm_lengths (l 0) (l 1) (l 2) (hl 0) h01 h12).mp
    (by simpa [Fin.sum_univ_succ, add_assoc] using hbound)
  rcases hnum with ⟨h0, h1 | ⟨h1, h2 | h2 | h2⟩⟩
  · have hcpos := hl 2
    generalize hcdef : l 2 = c at *
    have hlv : l = ![1,1,c] := by
      funext i
      fin_cases i <;> simp_all
    subst l
    refine ⟨.D (c + 3) (by omega), armDEquiv c, ?_⟩
    intro i j
    exact threeArmCartan_D c hcpos i j
  · have hlv : l = ![1,2,2] := by
      funext i
      fin_cases i <;> simp_all
    subst l
    exact ⟨.E6, armEEquiv 2, threeArmCartan_E 2⟩
  · have hlv : l = ![1,2,3] := by
      funext i
      fin_cases i <;> simp_all
    subst l
    exact ⟨.E7, armEEquiv 3, threeArmCartan_E 3⟩
  · have hlv : l = ![1,2,4] := by
      funext i
      fin_cases i <;> simp_all
    subst l
    exact ⟨.E8, armEEquiv 4, threeArmCartan_E 4⟩

lemma dynkin_branch_classification
    {R : Set E} {v : E} (hR : IsRootSystem R)
    (hv : RootRegular R v) {b : Basis ι ℝ E} (hb : IsSimpleBasis R v b)
    (hc : (dynkinDiagram b).IsConnected) (x : ι) (ex : Fin 3 ↪ ι)
    (hx : ∀ i, (dynkinDiagram b).edges x (ex i) ≠ 0) :
    ∃ t : FiniteDynkinType, (dynkinDiagram b).Isomorphic t.diagram := by
  obtain ⟨l, e, hl, h01, h12, hecenter, hcenter, harm⟩ :=
    dynkin_sorted_three_arms hR hv hb hc x ex hx
  have hbound : 1 < ∑ a, 1 / ((l a : ℝ) + 1) := by
    apply dynkin_three_arm_bound hR hv hb e.toEmbedding
    · intro a i hi
      apply (simpleRootGraph_adj_iff hR hv hb _ _).mp
      change (simpleRootGraph b).Adj (e (.inl ())) (e (.inr ⟨a, i⟩))
      rw [hecenter]
      exact (hcenter a i).mpr hi
    · intro a i j hij
      apply (simpleRootGraph_adj_iff hR hv hb _ _).mp
      exact (harm a a i j).mpr ⟨rfl, Or.inl hij⟩
  have hcartan := cartan_eq_threeArmCartan_of_arms hR hv hb e
    (by simpa only [hecenter] using hcenter) harm
    (dynkin_branch_edges_le_one hR hv hb hc x ex hx)
  obtain ⟨t, f, hf⟩ := threeArmCartan_classification l hl h01 h12 hbound
  refine ⟨t, dynkin_isomorphic_of_cartan hR hv hb t (e.symm.trans f) ?_⟩
  intro i j
  simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using
    (hcartan (e.symm i) (e.symm j)).trans (hf (e.symm i) (e.symm j))

/-- Every connected finite reduced crystallographic Dynkin diagram occurs
in the finite list, with all edge multiplicities and arrows retained. -/
theorem dynkin_exhaustion : DynkinExhaustionSpecs.exhaustionType := by
  intro E _ _ ι R hR v hv b hb hc
  classical
  by_cases hbranch : ∃ (x : ι) (ex : Fin 3 ↪ ι), ∀ i,
      (dynkinDiagram b).edges x (ex i) ≠ 0
  · obtain ⟨x, ex, hx⟩ := hbranch
    exact dynkin_branch_classification hR hv hb hc x ex hx
  · exact dynkin_chain_of_no_branch hR hv hb hc hbranch



end LieAlgebrasAndRepresentations
