import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.EdgeColoring.Konig
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.EdgeColoring.Foundations
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Choose

noncomputable section
universe u v
namespace FiniteCombinatorics.Graph.EdgeColoring
open Finset
open scoped Classical

/-- Counting preimages of a vertex subset in a regular labelled incidence map. -/
private lemma regular_preimage_card {E V : Type*} [Fintype E] [Fintype V]
    (f : E → V) (k : ℕ) (h : ∀ x, Fintype.card {e // f e = x} = k)
    (S : Finset V) : (univ.filter (fun e => f e ∈ S)).card = S.card * k := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter univ S f]
  apply sum_const_nat
  intro x _
  simpa only [Fintype.card_subtype] using h x

/-- Hall's counting argument for a regular bipartite multigraph. The selected
matching consists of original edge labels, one for each left vertex. -/
private lemma regular_matching {E V : Type*} [Fintype E] [Fintype V]
    (f g : E → V) (k : ℕ) (hk : 0 < k)
    (hf : ∀ x, Fintype.card {e // f e = x} = k)
    (hg : ∀ x, Fintype.card {e // g e = x} = k) :
    ∃ s : V → E, (∀ x, f (s x) = x) ∧ Function.Bijective (g ∘ s) := by
  classical
  let t : V → Finset V := fun x => univ.filter (fun y => ∃ e, f e = x ∧ g e = y)
  have hall : ∀ S : Finset V, S.card ≤ (S.biUnion t).card := by
    intro S
    have hsub : univ.filter (fun e => f e ∈ S) ⊆
        univ.filter (fun e => g e ∈ S.biUnion t) := by
      intro e he
      simp only [mem_filter, mem_univ, true_and] at he ⊢
      refine mem_biUnion.mpr ⟨f e, he, ?_⟩
      simpa only [t, mem_filter, mem_univ, true_and] using ⟨e, rfl, rfl⟩
    have hc := card_le_card hsub
    rw [regular_preimage_card f k hf, regular_preimage_card g k hg] at hc
    exact Nat.le_of_mul_le_mul_right hc hk
  obtain ⟨p, hp, hpt⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hs : ∀ x, ∃ e, f e = x ∧ g e = p x := by simpa [t] using hpt
  choose s hsf hsg using hs
  refine ⟨s, hsf, ?_⟩
  have heq : g ∘ s = p := funext hsg
  rw [heq]
  exact ⟨hp, Finite.surjective_of_injective hp⟩

/-- Removing one specified element of a fiber decreases its cardinality by one. -/
private lemma fiber_remove {E V : Type*} [Fintype E] (f : E → V)
    (q : E → Prop) (x : V) (a : E) (ha : f a = x)
    (hq : ∀ e, f e = x → (q e ↔ e ≠ a)) :
    Nat.card {e : {e // q e} // f e.val = x} =
      Nat.card {e // f e = x} - 1 := by
  classical
  let equiv : {e : {e // q e} // f e.val = x} ≃
      {e : {e // f e = x} // e ≠ ⟨a, ha⟩} :=
    { toFun := fun e => ⟨⟨e.val.val, e.property⟩, fun h =>
        (hq _ e.property).mp e.val.property (congrArg Subtype.val h)⟩
      invFun := fun e => ⟨⟨e.val.val, (hq _ e.val.property).mpr
        (fun h => e.property (Subtype.ext h))⟩, e.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr equiv, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- A regular bipartite multigraph is the union of `k` labelled matchings.
The endpoint types on both sides are copies of the same finite type. -/
private theorem regular_coloring (k : ℕ) :
    ∀ {E : Type v} {V : Type u} [Fintype E] [Fintype V] (f g : E → V),
    (∀ x, Fintype.card {e // f e = x} = k) →
    (∀ x, Fintype.card {e // g e = x} = k) →
    ∃ c : E → Fin k, ∀ e e', c e = c e' →
      (f e = f e' ∨ g e = g e') → e = e' := by
  classical
  induction k with
  | zero =>
    intro E V _ _ f g hf _
    have empty : IsEmpty E := ⟨fun e => by
      have hn : Nonempty {e' // f e' = f e} := ⟨⟨e, rfl⟩⟩
      have := Fintype.card_pos_iff.mpr hn
      rw [hf] at this
      omega⟩
    exact ⟨isEmptyElim, fun e => isEmptyElim e⟩
  | succ k ih =>
    intro E V _ _ f g hf hg
    obtain ⟨s, hsf, hsg⟩ := regular_matching f g (k+1) (by omega) hf hg
    let p : V ≃ V := Equiv.ofBijective (g ∘ s) hsg
    let q : E → Prop := fun e => e ≠ s (f e)
    have hqf (x : V) : Fintype.card {e : {e // q e} // f e.val = x} = k := by
      have h := fiber_remove f q x (s x) (hsf x) (by
        intro e he
        simp only [q, he])
      have hc : Fintype.card {e : {e // q e} // f e.val = x} =
          Fintype.card {e // f e = x} - 1 := by
        simpa only [Nat.card_eq_fintype_card] using h
      rw [hf] at hc
      exact hc
    have hqg (x : V) : Fintype.card {e : {e // q e} // g e.val = x} = k := by
      have hga : g (s (p.symm x)) = x := p.apply_symm_apply x
      have h := fiber_remove g q x (s (p.symm x)) hga (by
        intro e he
        change (e ≠ s (f e)) ↔ e ≠ s (p.symm x)
        have hi : e = s (f e) ↔ e = s (p.symm x) := by
          constructor
          · intro h
            have hp : p (f e) = x := by
              change g (s (f e)) = x
              rw [← h, he]
            rw [← p.symm_apply_apply (f e), hp] at h
            exact h
          · intro h
            rw [h, hsf]
        exact not_congr hi)
      have hc : Fintype.card {e : {e // q e} // g e.val = x} =
          Fintype.card {e // g e = x} - 1 := by
        simpa only [Nat.card_eq_fintype_card] using h
      rw [hg] at hc
      exact hc
    obtain ⟨c, hc⟩ := ih (fun e : {e // q e} => f e.val)
      (fun e : {e // q e} => g e.val) hqf hqg
    let C : E → Fin (k+1) := fun e => if h : q e then (c ⟨e, h⟩).succ else 0
    refine ⟨C, ?_⟩
    intro e e' hC hends
    by_cases he : q e <;> by_cases he' : q e'
    · have hcc : c ⟨e, he⟩ = c ⟨e', he'⟩ := by
        simpa only [C, dite_eq_left he, dite_eq_left he', Fin.succ_inj] using hC
      exact congrArg Subtype.val (hc _ _ hcc hends)
    · simp [C, he, he'] at hC
    · have hz : (c ⟨e', he'⟩).succ ≠ 0 := Fin.succ_ne_zero _
      exact (hz (by simpa [C, he, he'] using hC.symm)).elim
    · have hes : e = s (f e) := not_not.mp he
      have hes' : e' = s (f e') := not_not.mp he'
      rcases hends with h | h
      · rw [hes, hes', h]
      · have hp : p (f e) = p (f e') := by
          change g (s (f e)) = g (s (f e'))
          rwa [← hes, ← hes']
        rw [hes, hes', p.injective hp]

private lemma fiber_sum_card {E E' V : Type*} [Fintype E] [Fintype E']
    (f : E → V) (g : E' → V) (x : V) :
    Fintype.card {e : E ⊕ E' // Sum.elim f g e = x} =
      Fintype.card {e // f e = x} + Fintype.card {e // g e = x} := by
  classical
  exact (Fintype.card_congr Equiv.subtypeSum).trans Fintype.card_sum

/-- Reflect the graph, then fill equal deficiencies with labelled diagonal
edges. No relation between the sizes of its original parts is needed. -/
private theorem bounded_coloring {E : Type v} {V : Type u} [Fintype E] [Fintype V]
    (f g : E → V) (k : ℕ)
    (hdeg : ∀ x, Nat.card {e // f e = x} +
      Nat.card {e // g e = x} ≤ k) :
    ∃ c : E → Fin k, ∀ e e', c e = c e' →
      (f e = f e' ∨ g e = g e') → e = e' := by
  classical
  have hdeg' : ∀ x, Fintype.card {e // f e = x} + Fintype.card {e // g e = x} ≤ k := by
    simpa only [Nat.card_eq_fintype_card] using hdeg
  let d : V → ℕ := fun x => Fintype.card {e // f e = x} + Fintype.card {e // g e = x}
  let D := (x : V) × Fin (k - d x)
  let Eplus := (E ⊕ E) ⊕ D
  let F : Eplus → V := Sum.elim (Sum.elim f g) Sigma.fst
  let H : Eplus → V := Sum.elim (Sum.elim g f) Sigma.fst
  have hD (x : V) : Fintype.card {a : D // a.1 = x} = k - d x := by
    exact (Fintype.card_congr (Equiv.sigmaSubtype x)).trans (Fintype.card_fin _)
  have hF (x : V) : Fintype.card {e // F e = x} = k := by
    change Fintype.card {e // Sum.elim (Sum.elim f g) (fun a : D => a.1) e = x} = k
    rw [fiber_sum_card, fiber_sum_card, hD]
    exact Nat.add_sub_of_le (hdeg' x)
  have hH (x : V) : Fintype.card {e // H e = x} = k := by
    change Fintype.card {e // Sum.elim (Sum.elim g f) (fun a : D => a.1) e = x} = k
    rw [fiber_sum_card, fiber_sum_card, hD]
    simpa only [d, Nat.add_comm] using Nat.add_sub_of_le (hdeg' x)
  obtain ⟨c, hc⟩ := regular_coloring k F H hF hH
  refine ⟨fun e => c (Sum.inl (Sum.inl e)), ?_⟩
  intro e e' he hends
  exact Sum.inl_injective (Sum.inl_injective (hc _ _ he hends))

/-- Orient each original labelled edge from color zero to color one. -/
private lemma bipartite_endpoints {α : Type u} {β : Type v}
    (G : _root_.Graph α β) [G.Loopless]
    (hb : (Multigraph.underlying G).IsBipartite) :
    ∃ (b : Multigraph.Vertex G → Fin 2) (f g : Multigraph.Edge G → Multigraph.Vertex G),
      (∀ e, G.IsLink e.val (f e).val (g e).val) ∧
      (∀ e, b (f e) = 0) ∧ (∀ e, b (g e) = 1) := by
  classical
  obtain ⟨b, hb⟩ := hb
  have hex : ∀ e : Multigraph.Edge G, ∃ x y : Multigraph.Vertex G,
      G.IsLink e.val x.val y.val ∧ b x = 0 ∧ b y = 1 := by
    intro e
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.property
    let X : Multigraph.Vertex G := ⟨x, hxy.left_mem⟩
    let Y : Multigraph.Vertex G := ⟨y, hxy.right_mem⟩
    have hn : b X ≠ b Y := hb ((Multigraph.underlying_loopless_adjacency G X Y).mpr ⟨e.val, hxy⟩)
    by_cases hx : b X = 0
    · exact ⟨X, Y, hxy, hx, by omega⟩
    · exact ⟨Y, X, hxy.symm, by omega, by omega⟩
  choose f g hfg hf hg using hex
  exact ⟨b, f, g, hfg, hf, hg⟩

/-- The bipartite multigraph assertion of Kőnig's line-coloring theorem,
with degrees and colors both counted on the original edge labels. -/
theorem konig_line_coloring :
    Specs.FiniteCombinatorics.Graph.EdgeColoring.Konig.konig_line_coloringType := by
  intro α β G _ h hb
  classical
  apply le_antisymm
  · apply chromaticIndex_le
    let : Finite (Multigraph.Edge G) := Multigraph.finite_edges G h
    let : Finite (Multigraph.Vertex G) := Multigraph.finite_vertices G h
    let := Fintype.ofFinite (Multigraph.Edge G)
    let := Fintype.ofFinite (Multigraph.Vertex G)
    obtain ⟨b, f, g, hfg, hf, hg⟩ := bipartite_endpoints G hb
    have hdeg (x : Multigraph.Vertex G) :
        Nat.card {e // f e = x} + Nat.card {e // g e = x} ≤ maximumDegree G h := by
      let : Finite (G.incidenceSet x.val) := (Multigraph.finite_incidentEdges G h x.val).to_subtype
      let := Fintype.ofFinite (G.incidenceSet x.val)
      let j : {e // f e = x} ⊕ {e // g e = x} → G.incidenceSet x.val :=
        Sum.elim
          (fun e => ⟨e.val.val, by
            have hi := (hfg e.val).inc_left
            rw [e.property] at hi
            exact hi⟩)
          (fun e => ⟨e.val.val, by
            have hi := (hfg e.val).inc_right
            rw [e.property] at hi
            exact hi⟩)
      have hj : Function.Injective j := by
        intro e e' he
        have hv := congrArg Subtype.val he
        rcases e with e | e <;> rcases e' with e' | e'
        · exact congrArg Sum.inl (Subtype.ext (Subtype.ext hv))
        · have hc : (0 : Fin 2) = 1 := by
            calc
              0 = b (f e.val) := (hf e.val).symm
              _ = b x := congrArg b e.property
              _ = b (g e'.val) := (congrArg b e'.property).symm
              _ = 1 := hg e'.val
          exact (by decide : (0 : Fin 2) ≠ 1) hc |>.elim
        · have hc : (0 : Fin 2) = 1 := by
            calc
              0 = b (f e'.val) := (hf e'.val).symm
              _ = b x := congrArg b e'.property
              _ = b (g e.val) := (congrArg b e.property).symm
              _ = 1 := hg e.val
          exact (by decide : (0 : Fin 2) ≠ 1) hc |>.elim
        · exact congrArg Sum.inr (Subtype.ext (Subtype.ext hv))
      have hc : Nat.card {e // f e = x} + Nat.card {e // g e = x} ≤
          Nat.card (G.incidenceSet x.val) := by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_sum] using
          Fintype.card_le_of_injective j hj
      exact hc.trans ((Multigraph.degree_loopless G x.val).symm.le.trans
        (degree_le_maximumDegree G h x.val))
    obtain ⟨c, hc⟩ := bounded_coloring f g (maximumDegree G h) hdeg
    refine ⟨⟨c, ?_⟩⟩
    intro e e' hne hinc hcolor
    apply hne
    apply hc e e' hcolor
    obtain ⟨x, hx, hx'⟩ := hinc
    have he := hx.eq_or_eq_of_isLink (hfg e)
    have he' := hx'.eq_or_eq_of_isLink (hfg e')
    rcases he with he | he <;> rcases he' with he' | he'
    · exact Or.inl (Subtype.ext (he.symm.trans he'))
    · have heq : f e = g e' := Subtype.ext (he.symm.trans he')
      have hn : (0 : Fin 2) ≠ 1 := by decide
      exact (hn ((hf e).symm.trans ((congrArg b heq).trans (hg e')))).elim
    · have heq : f e' = g e := Subtype.ext (he'.symm.trans he)
      have hn : (0 : Fin 2) ≠ 1 := by decide
      exact (hn ((hf e').symm.trans ((congrArg b heq).trans (hg e)))).elim
    · exact Or.inr (Subtype.ext (he.symm.trans he'))
  · exact maximumDegree_le_chromaticIndex G h

end FiniteCombinatorics.Graph.EdgeColoring
