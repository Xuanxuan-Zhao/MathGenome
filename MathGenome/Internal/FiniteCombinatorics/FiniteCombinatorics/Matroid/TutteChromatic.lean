import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.TutteChromatic
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GraphicRank
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.TutteDefinition
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial
import Mathlib.Tactic.Ring

open Polynomial
open scoped BigOperators
universe u v
noncomputable section
namespace FiniteCombinatorics.Matroid.Graphic

/-- The spanning adjacency shadow uses exactly the same vertices and edges as
in the chromatic subset formula. -/
def simpleSpanningIso {V : Type u} [Finite V] (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (hA : (A : Set (Sym2 V)) ⊆ G.edgeSet) :
    spanningShadow (_root_.Graph.ofSimpleGraph G) (A : Set (Sym2 V)) ≃g
      Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningGraph A where
  toEquiv := Equiv.Set.univ V
  map_rel_iff' := by
    intro x y
    change (s(x.val, y.val) ∈ A ∧ x.val ≠ y.val) ↔
      (x ≠ y ∧ ∃ e, e ∈ (A : Set (Sym2 V)) ∧
        e = s(x.val, y.val) ∧ e ∈ G.edgeSet)
    constructor
    · rintro ⟨he, hne⟩
      exact ⟨fun h => hne (congrArg Subtype.val h), _, he, rfl, hA he⟩
    · rintro ⟨hne, e, he, rfl, _⟩
      exact ⟨he, fun h => hne (Subtype.ext h)⟩

lemma simple_component_count {V : Type u} [Finite V] (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (hA : (A : Set (Sym2 V)) ⊆ G.edgeSet) :
    spanningComponentCount (_root_.Graph.ofSimpleGraph G) (A : Set (Sym2 V)) =
      Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningComponentCount A :=
  Nat.card_congr (simpleSpanningIso G A hA).connectedComponentEquiv

lemma simple_subset_rank {V : Type u} [Finite V] (G : SimpleGraph V)
    (K : Type v) [Field K] (o : Orientation (_root_.Graph.ofSimpleGraph G))
    (A : Finset (Sym2 V)) (hA : (A : Set (Sym2 V)) ⊆ G.edgeSet) :
    rank (incidenceMatroid (_root_.Graph.ofSimpleGraph G) (simpleFinite G) K o)
      (A : Set (Sym2 V)) = (Nat.card V : ℤ) - (Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningComponentCount A : ℤ) := by
  have h := rank_eq_vertices_sub_components _ (simpleFinite G) K o _ hA
  rw [simple_component_count G A hA] at h
  simpa only [Expected.rank, rank, _root_.Graph.ofSimpleGraph,
    Set.ncard_univ] using h

lemma simple_total_rank {V : Type u} [Finite V] (G : SimpleGraph V)
    (K : Type v) [Field K] (o : Orientation (_root_.Graph.ofSimpleGraph G)) :
    rank (incidenceMatroid (_root_.Graph.ofSimpleGraph G) (simpleFinite G) K o) G.edgeSet =
      (Nat.card V : ℤ) - (Nat.card G.ConnectedComponent : ℤ) := by
  have h := total_rank _ (simpleFinite G) K o
  rw [Nat.card_congr (_root_.Graph.toSimpleGraphOfSimpleGraphIso G).connectedComponentEquiv] at h
  simpa only [Expected.rank, rank, _root_.Graph.ofSimpleGraph, Set.ncard_univ] using h

/-- The two rank deficits account for the sign and the component exponent. -/
private lemma specialization_term (r d n a c k : ℕ)
    (hs : r + d + n = 2 * d + a) (hc : c + d = k) :
    (-1 : ℤ[X]) ^ r * X ^ c * ((1 - X - 1) ^ d * (0 - 1) ^ n) =
      C ((-1 : ℤ) ^ a) * X ^ k := by
  have hx : (1 - X - 1 : ℤ[X]) = -X := by ring
  rw [hx, zero_sub, neg_pow (X : ℤ[X]) d]
  calc
    (-1 : ℤ[X]) ^ r * X ^ c *
        ((-1) ^ d * X ^ d * (-1) ^ n) =
        (-1) ^ (r + d + n) * X ^ (c + d) := by
          simp only [pow_add]
          ring
    _ = C ((-1 : ℤ) ^ a) * X ^ k := by
      rw [hs, hc]
      simp [pow_add, pow_mul]

/-- Matching one substituted Tutte term with one inclusion-exclusion term. -/
lemma simple_specialization_term {V : Type u} [Finite V] (G : SimpleGraph V)
    (K : Type v) [Field K] (o : Orientation (_root_.Graph.ofSimpleGraph G))
    (A : Finset (Sym2 V)) (hA : (A : Set (Sym2 V)) ⊆ G.edgeSet) :
    let M := incidenceMatroid (_root_.Graph.ofSimpleGraph G) (simpleFinite G) K o
    (-1 : ℤ[X]) ^ (M.eRk M.E).toNat * X ^ Nat.card G.ConnectedComponent *
      ((1 - X - 1) ^ rankDeficit M (A : Set (Sym2 V)) *
        (0 - 1) ^ rankNullity M (A : Set (Sym2 V))) =
      C ((-1 : ℤ) ^ A.card) *
        X ^ Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningComponentCount A := by
  dsimp only
  let M := incidenceMatroid (_root_.Graph.ofSimpleGraph G) (simpleFinite G) K o
  have hAM : (A : Set (Sym2 V)) ⊆ M.E := hA
  have hd := rankDeficitCast M (A : Set (Sym2 V)) hAM
  have hn := rankNullityCast M (A : Set (Sym2 V)) hAM
  have hr := simple_total_rank G K o
  have hq := simple_subset_rank G K o A hA
  change rank M M.E = _ at hr
  change rank M (A : Set (Sym2 V)) = _ at hq
  rw [Set.ncard_coe_finset] at hn
  dsimp only [M] at hd hn hr hq
  apply specialization_term
  · unfold rank at hd hn
    omega
  · unfold rank at hd hr hq
    omega

/-- W77: the integer polynomial substitution, in any incidence presentation. -/
theorem chromatic_specialization_incidence {V : Type u} [Finite V]
    (G : SimpleGraph V) (K : Type v) [Field K]
    (o : Orientation (_root_.Graph.ofSimpleGraph G)) :
    let M := incidenceMatroid (_root_.Graph.ofSimpleGraph G) (simpleFinite G) K o
    Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.chromaticPolynomial G =
      (-1 : ℤ[X]) ^ (M.eRk M.E).toNat * X ^ Nat.card G.ConnectedComponent *
        tutteSubstitute (tutte M) (1 - X) 0 := by
  classical
  let M := incidenceMatroid (_root_.Graph.ofSimpleGraph G) (simpleFinite G) K o
  change Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.chromaticPolynomial G =
    (-1 : ℤ[X]) ^ (M.eRk M.E).toNat * X ^ Nat.card G.ConnectedComponent *
      tutteSubstitute (tutte M) (1 - X) 0
  have he : M.ground_finite.toFinset =
      Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.edges G := by
    ext e
    simp only [Set.Finite.mem_toFinset,
      FiniteCombinatorics.Graph.Coloring.mem_chromatic_edges]
    rfl
  rw [tutteSubstituteSum, Finset.mul_sum, he,
    FiniteCombinatorics.Graph.Coloring.chromaticPolynomial_subset_formula G]
  apply Finset.sum_congr rfl
  intro A hA
  apply (simple_specialization_term G K o A ?_).symm
  intro e heA
  exact (FiniteCombinatorics.Graph.Coloring.mem_chromatic_edges G e).mp
    (Finset.mem_powerset.mp hA heA)

/-- The canonical cycle matroid has precisely the forest independent sets. -/
theorem cycleMatroid_indep {V : Type u} [Finite V] (G : SimpleGraph V)
    (A : Set (Sym2 V)) :
    (cycleMatroid G).Indep A ↔ Forest (_root_.Graph.ofSimpleGraph G) A :=
  incidenceMatroid_indep _ (simpleFinite G) ℚ (simpleOrientation G) A

/-- W77, with M(G) the canonical cycle matroid on the original edges. -/
theorem chromatic_specialization :
    Specs.FiniteCombinatorics.Matroid.TutteChromatic.chromaticSpecialization := by
  intro V _ G
  exact chromatic_specialization_incidence G ℚ (simpleOrientation G)

theorem cycleMatroid_ground :
    Specs.FiniteCombinatorics.Matroid.TutteChromatic.cycleMatroidGround := by
  intro V _ G
  rfl

/-- Choosing another field or orientation leaves the canonical matroid unchanged. -/
theorem cycleMatroid_eq_incidence :
    Specs.FiniteCombinatorics.Matroid.TutteChromatic.cycleMatroidInvariant := by
  intro V _ G K _ o
  exact incidenceMatroid_invariant _ (simpleFinite G) ℚ K (simpleOrientation G) o

theorem cycleMatroid_rank :
    Specs.FiniteCombinatorics.Matroid.TutteChromatic.cycleMatroidRank := by
  intro V _ G A hA
  exact simple_subset_rank G ℚ (simpleOrientation G) A hA

theorem chromatic_specialization_edgeless :
    Specs.FiniteCombinatorics.Matroid.TutteChromatic.edgelessSpecialization := by
  intro V _
  exact (chromatic_specialization (⊥ : SimpleGraph V)).symm.trans
    FiniteCombinatorics.Graph.Coloring.chromaticPolynomial_edgeless

theorem chromatic_specialization_empty :
    Specs.FiniteCombinatorics.Matroid.TutteChromatic.emptySpecialization := by
  intro V _ _ G
  exact (chromatic_specialization G).symm.trans
    (FiniteCombinatorics.Graph.Coloring.chromaticPolynomial_empty G)

end FiniteCombinatorics.Matroid.Graphic
