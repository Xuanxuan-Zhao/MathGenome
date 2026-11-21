import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction
import Mathlib.Data.Fintype.Sum

universe u v
noncomputable section
namespace FiniteCombinatorics.Graph.Coloring

abbrev contractionSetoid := @Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.contractionSetoid
abbrev ContractedVertex := @Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.ContractedVertex
abbrev contractVertex := @Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.contractVertex
abbrev deleteEdge := @Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.deleteEdge
abbrev contractEdge := @Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.contractEdge

theorem contractVertex_eq_iff :
    Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.quotientIdentification := by
  intro V u v a b
  exact Quotient.eq

@[simp] theorem contractVertex_endpoints {V : Type u} (u v : V) :
    contractVertex u v u = contractVertex u v v :=
  (contractVertex_eq_iff u v u v).mpr (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)

theorem contractEdge_adj :
    Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.contractedAdjacency := by
  intro V G u v a b
  simp only [Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.contractEdge,
    SimpleGraph.map_adj', Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.deleteEdge,
    SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  aesop

@[simp] theorem deleteEdge_adj {V : Type u} (G : SimpleGraph V) (u v a b : V) :
    (deleteEdge G u v).Adj a b ↔ G.Adj a b ∧ s(a,b) ≠ s(u,v) := by
  simp [deleteEdge, Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.deleteEdge]

/-- Equality at the two endpoints makes a function constant on every quotient class. -/
theorem constant_on_contraction {V : Type u} {α : Type v} {u v : V}
    (f : V → α) (hf : f u = f v) {a b : V}
    (h : (contractionSetoid u v).r a b) : f a = f b := by
  rcases h with rfl | ⟨ha, hb⟩
  · rfl
  · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hf
    · exact hf.symm
    · rfl

/-- A coloring with equal endpoint colors descends without changing any color. -/
def descendContractionColoring {V : Type u} {α : Type v}
    (G : SimpleGraph V) (u v : V)
    (c : {c : (deleteEdge G u v).Coloring α // c u = c v}) :
    (contractEdge G u v).Coloring α :=
  SimpleGraph.Coloring.mk
    (Quotient.lift c.val (fun _ _ h => constant_on_contraction c.val c.property h)) (by
      intro a b hab
      obtain ⟨_, x, y, hxy, he, rfl, rfl⟩ := (contractEdge_adj G u v a b).mp hab
      exact c.val.valid ((deleteEdge_adj G u v x y).mpr ⟨hxy, he⟩))

/-- Pulling a coloring back to the old vertex type yields equal endpoint colors. -/
def liftContractionColoring {V : Type u} {α : Type v}
    (G : SimpleGraph V) (u v : V) :
    (contractEdge G u v).Coloring α →
      {c : (deleteEdge G u v).Coloring α // c u = c v} := fun c =>
  ⟨SimpleGraph.Coloring.mk (fun a => c (contractVertex u v a)) (by
    intro a b hab heq
    have h := (deleteEdge_adj G u v a b).mp hab
    by_cases hq : contractVertex u v a = contractVertex u v b
    · have hr := (contractVertex_eq_iff u v a b).mp hq
      rcases hr with rfl | ⟨ha, hb⟩
      · exact h.1.ne rfl
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact h.1.ne rfl
        · exact h.2 rfl
        · exact h.2 (Sym2.eq_swap)
        · exact h.1.ne rfl
    · exact c.valid ((contractEdge_adj G u v _ _).mpr ⟨hq, a, b, h.1, h.2, rfl, rfl⟩) heq),
   by change c (contractVertex u v u) = c (contractVertex u v v)
      rw [contractVertex_endpoints]⟩

/-- The color-preserving quotient correspondence, valid for every color type. -/
def contractionColoringEquiv {V : Type u} {α : Type v}
    (G : SimpleGraph V) (u v : V) :
    {c : (deleteEdge G u v).Coloring α // c u = c v} ≃
      (contractEdge G u v).Coloring α where
  toFun := descendContractionColoring G u v
  invFun := liftContractionColoring G u v
  left_inv c := by
    apply Subtype.ext
    apply DFunLike.ext
    intro a
    rfl
  right_inv c := by
    apply DFunLike.ext
    intro a
    induction a using Quotient.inductionOn with
    | h a => rfl

/-- The other colorings of the deleted graph are exactly the original colorings. -/
def differentEndpointColoringEquiv {V : Type u} {α : Type v}
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) :
    {c : (deleteEdge G u v).Coloring α // c u ≠ c v} ≃ G.Coloring α where
  toFun c := SimpleGraph.Coloring.mk c.val (by
    intro a b hab
    by_cases he : s(a,b) = s(u,v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact c.property
      · exact Ne.symm c.property
    · exact c.val.valid ((deleteEdge_adj G u v a b).mpr ⟨hab, he⟩))
  invFun c := ⟨SimpleGraph.Coloring.mk c (fun hab =>
    c.valid ((deleteEdge_adj G u v _ _).mp hab).1), c.valid huv⟩
  left_inv c := by
    apply Subtype.ext
    apply DFunLike.ext
    intro a
    rfl
  right_inv c := by
    apply DFunLike.ext
    intro a
    rfl

/-- Partition the colorings according to equality of the endpoint colors. -/
theorem deletion_colorings_count {V : Type u} [Finite V]
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) (k : ℕ) :
    Nat.card ((deleteEdge G u v).Coloring (Fin k)) =
      Nat.card (G.Coloring (Fin k)) + Nat.card ((contractEdge G u v).Coloring (Fin k)) := by
  classical
  let := Fintype.ofFinite V
  let e : (deleteEdge G u v).Coloring (Fin k) ≃
      G.Coloring (Fin k) ⊕ (contractEdge G u v).Coloring (Fin k) :=
    (Equiv.sumCompl (fun c : (deleteEdge G u v).Coloring (Fin k) => c u ≠ c v)).symm.trans
      (Equiv.sumCongr (differentEndpointColoringEquiv G u v huv)
        ((Equiv.subtypeEquivRight (fun _ => not_not)).trans (contractionColoringEquiv G u v)))
  let := Fintype.ofFinite (ContractedVertex u v)
  exact (Nat.card_congr e).trans Nat.card_sum

/-- Paper W60: deletion–contraction in the integer polynomial ring. -/
theorem chromaticPolynomial_deletion_contraction :
    Specs.FiniteCombinatorics.Graph.Coloring.DeletionContraction.deletionContraction := by
  intro V _ G u v huv
  apply polynomial_eq_of_nat_evaluations
  intro k
  rw [Polynomial.eval_sub, chromaticPolynomial_counts, chromaticPolynomial_counts,
    chromaticPolynomial_counts]
  apply eq_sub_iff_add_eq.mpr
  exact_mod_cast (deletion_colorings_count G u v huv k).symm

end FiniteCombinatorics.Graph.Coloring
