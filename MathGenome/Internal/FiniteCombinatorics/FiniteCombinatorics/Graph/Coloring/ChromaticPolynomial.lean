import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Counting.InclusionExclusion
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Lattice
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

open scoped BigOperators Classical
open Polynomial
universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Coloring

abbrev spanningComponentCount : Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningComponentCountType := @Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningComponentCount
abbrev chromaticPolynomial : Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.chromaticPolynomialType := @Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.chromaticPolynomial

theorem chromaticPolynomial_subset_formula : Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.subsetFormula := by
  intro V _ G
  rfl

/-- Functions constant across edges descend precisely to functions on components. -/
def componentFunctionEquiv {V : Type u} (H : SimpleGraph V) (α : Type*) :
    {f : V → α // ∀ a b, H.Adj a b → f a = f b} ≃ (H.ConnectedComponent → α) where
  toFun f := Quot.lift f.val (by
    intro a b h
    obtain ⟨p⟩ := h
    induction p with
    | nil => rfl
    | @cons a b c hab p ih => exact (f.property a b hab).trans ih)
  invFun g := ⟨fun a => g (H.connectedComponentMk a), fun _ _ h =>
    congrArg g (SimpleGraph.ConnectedComponent.sound h.reachable)⟩
  left_inv f := by rfl
  right_inv g := by
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ a => rfl

/-- An edge violation is independent of the choice/order of endpoints. -/
def edgeViolation {V : Type u} {α : Type*} (f : V → α) (e : Sym2 V) : Prop :=
  ∀ a b, e = s(a,b) → f a = f b

@[simp] theorem edgeViolation_mk {V : Type u} {α : Type*} (f : V → α) (a b : V) :
    edgeViolation f s(a,b) ↔ f a = f b := by
  constructor
  · exact fun h => h a b rfl
  · intro h x y he
    rcases Sym2.eq_iff.mp he with hxy | hxy
    · obtain ⟨rfl, rfl⟩ := hxy
      exact h
    · obtain ⟨rfl, rfl⟩ := hxy
      exact h.symm

private def violations {V : Type u} [Fintype V] (k : ℕ) (e : Sym2 V) :
    Finset (V → Fin k) := by
  classical
  exact Finset.univ.filter (fun f => edgeViolation f e)

private theorem mem_inf_violations {V : Type u} [Fintype V] (k : ℕ)
    (A : Finset (Sym2 V)) (f : V → Fin k) :
    f ∈ A.inf (violations k) ↔
      ∀ a b, (Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningGraph A).Adj a b → f a = f b := by
  classical
  simp only [Finset.mem_inf, violations, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h a b hab
    exact (edgeViolation_mk f a b).mp (h _ hab.1)
  · intro h e he
    induction e using Sym2.ind with
    | _ a b =>
      apply (edgeViolation_mk f a b).mpr
      by_cases hab : a = b
      · exact congrArg f hab
      · exact h a b ⟨he, hab⟩

private theorem card_inf_violations {V : Type u} [Fintype V] (k : ℕ)
    (A : Finset (Sym2 V)) :
    (A.inf (violations k)).card =
      k ^ spanningComponentCount A := by
  classical
  let H := Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningGraph A
  calc
    (A.inf (violations k)).card = Nat.card {f // f ∈ A.inf (violations k)} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (H.ConnectedComponent → Fin k) :=
      Nat.card_congr ((Equiv.subtypeEquivRight (mem_inf_violations k A)).trans
        (componentFunctionEquiv H (Fin k)))
    _ = k ^ spanningComponentCount A := by
      rw [Nat.card_fun, Nat.card_fin]
      rfl

@[simp] theorem mem_chromatic_edges {V : Type u} [Finite V] (G : SimpleGraph V)
    (e : Sym2 V) : e ∈ Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.edges G ↔ e ∈ G.edgeSet := by
  classical
  exact Set.Finite.mem_toFinset _

/-- Subsets of the original edge family give exactly the stated spanning edge set. -/
theorem spanningGraph_edgeSet {V : Type u} [Finite V] (G : SimpleGraph V)
    (A : Finset (Sym2 V))
    (hA : A ⊆ Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.edges G) :
    (Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningGraph A).edgeSet =
      (A : Set (Sym2 V)) := by
  rw [Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun h => h.1
  · intro heA
    exact ⟨heA, G.not_isDiag_of_mem_edgeSet ((mem_chromatic_edges G e).mp (hA heA))⟩

private def properColoringEquiv {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    {f : V → Fin k // f ∈ (Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.edges G).inf
      (fun e => (violations k e)ᶜ)} ≃ G.Coloring (Fin k) where
  toFun f := SimpleGraph.Coloring.mk f.val (by
    intro a b hab heq
    have hm := (Finset.mem_inf.mp f.property) s(a,b) ((mem_chromatic_edges G _).mpr hab)
    apply (Finset.mem_compl.mp hm)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (edgeViolation_mk f.val a b).mpr heq⟩)
  invFun c := ⟨c, by
    apply Finset.mem_inf.mpr
    intro e he
    apply Finset.mem_compl.mpr
    intro hbad
    induction e using Sym2.ind with
    | _ a b =>
      exact c.valid ((mem_chromatic_edges G _).mp he)
        ((edgeViolation_mk (fun v => c v) a b).mp (Finset.mem_filter.mp hbad).2)⟩
  left_inv f := by rfl
  right_inv c := by rfl

private theorem card_properColorings {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    ((Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.edges G).inf
      (fun e => (violations k e)ᶜ)).card = Nat.card (G.Coloring (Fin k)) := by
  classical
  rw [← Nat.card_congr (properColoringEquiv G k), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem chromaticPolynomial_counts :
    Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.countsColorings := by
  intro V _ G k
  classical
  let := Fintype.ofFinite V
  have h := Finset.inclusion_exclusion_card_inf_compl
    (Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.edges G) (violations k)
  rw [card_properColorings] at h
  rw [Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.chromaticPolynomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [h]
  apply Finset.sum_congr rfl
  intro A hA
  rw [card_inf_violations, Nat.cast_pow]

/-- Equality at the nonnegative integers already determines an integer polynomial. -/
theorem polynomial_eq_of_nat_evaluations (P Q : ℤ[X])
    (h : ∀ k : ℕ, P.eval (k : ℤ) = Q.eval (k : ℤ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ))).mono
  rintro x ⟨k, rfl⟩
  exact h k

theorem chromaticPolynomial_unique :
    Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.uniquePolynomial := by
  intro V _ G
  refine ⟨chromaticPolynomial G, chromaticPolynomial_counts G, ?_⟩
  intro P hP
  apply polynomial_eq_of_nat_evaluations
  intro k
  exact (hP k).trans (chromaticPolynomial_counts G k).symm

/-- In an edgeless graph, each vertex is its own component. -/
def edgelessComponentEquiv (V : Type u) :
    (⊥ : SimpleGraph V).ConnectedComponent ≃ V where
  toFun := Quot.lift id (fun _ _ h => SimpleGraph.reachable_bot.mp h)
  invFun := (⊥ : SimpleGraph V).connectedComponentMk
  left_inv c := by
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ a => rfl
  right_inv a := rfl

theorem spanningComponentCount_empty {V : Type u} :
    spanningComponentCount (∅ : Finset (Sym2 V)) = Nat.card V := by
  change Nat.card (Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningGraph
    (∅ : Finset (Sym2 V))).ConnectedComponent = Nat.card V
  rw [show Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningGraph
    (∅ : Finset (Sym2 V)) = (⊥ : SimpleGraph V) by
      simp [Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningGraph,
        SimpleGraph.fromEdgeSet_empty]]
  exact Nat.card_congr (edgelessComponentEquiv V)

@[simp] theorem chromatic_edges_bot {V : Type u} [Finite V] :
    Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.edges (⊥ : SimpleGraph V) = ∅ := by
  ext e
  simp

theorem chromaticPolynomial_edgeless :
    Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.edgelessPolynomial := by
  intro V _
  simp [Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.chromaticPolynomial,
    spanningComponentCount_empty]

theorem chromaticPolynomial_empty :
    Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.emptyPolynomial := by
  intro V _ _ G
  have hG : G = ⊥ := by ext a; exact isEmptyElim a
  rw [hG, chromaticPolynomial_edgeless, Nat.card_of_isEmpty, pow_zero]

theorem empty_coloring_count :
    Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.emptyColoringCount := by
  intro V _ _ G k
  have h := chromaticPolynomial_counts G k
  rw [chromaticPolynomial_empty G, Polynomial.eval_one] at h
  exact_mod_cast h.symm

end FiniteCombinatorics.Graph.Coloring
