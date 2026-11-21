import Mathlib.Topology.Compactness.Paracompact

/-!
Independent interface for paper.tex, d10:15:locally-finite, its indexed-family
convention, and the terminology in d10:15:metric-sigma. Canonical definitions
live in the Specs namespace so downstream Specs can reuse these objects without
importing a candidate proof. Candidate-owned aliases expose the public interface. No separation or nonemptiness hypotheses are implicit.

A layer is a subset of the original index type, not a set of distinct values.
Thus repetitions of nonempty sets retain their multiplicity. Countable unions
are represented by a sequence of layers; empty layers and empty members are
allowed, so finite and empty unions are included.
-/

open Set
open scoped Topology
universe u v w

namespace Specs.D10Topology.Ch15.LocallyFiniteConventions

/-- The canonical indexed local-finiteness predicate from Chapter 2. -/
abbrev LocallyFiniteFamily {X : Type u} {I : Type v} [TopologicalSpace X]
    (A : I → Set X) : Prop := LocallyFinite A

/-- `V` refines the cover `U`: it still covers, and each member lies in some `U i`.
The original cover condition also follows from this predicate. -/
def CoverRefinement {X : Type u} {I : Type v} {J : Type w}
    (U : I → Set X) (V : J → Set X) : Prop :=
  (⋃ j, V j) = univ ∧ ∀ j, ∃ i, V j ⊆ U i

/-- Each point has a neighborhood meeting at most one indexed member. -/
def LocallyDiscrete {X : Type u} {I : Type v} [TopologicalSpace X]
    (A : I → Set X) : Prop :=
  ∀ x : X, ∃ N ∈ 𝓝 x, {i | (A i ∩ N).Nonempty}.Subsingleton

/-- A countable union of locally finite subfamilies of the original indices. -/
def SigmaLocallyFinite {X : Type u} {I : Type v} [TopologicalSpace X]
    (A : I → Set X) : Prop :=
  ∃ L : ℕ → Set I, (⋃ n, L n) = univ ∧
    ∀ n, LocallyFinite (fun i : L n => A i)

/-- A countable union of locally discrete subfamilies of the original indices. -/
def SigmaLocallyDiscrete {X : Type u} {I : Type v} [TopologicalSpace X]
    (A : I → Set X) : Prop :=
  ∃ L : ℕ → Set I, (⋃ n, L n) = univ ∧
    ∀ n, LocallyDiscrete (fun i : L n => A i)

/-- Paracompactness does not include Hausdorffness. -/
abbrev Paracompact (X : Type u) [TopologicalSpace X] : Prop := ParacompactSpace X


def familyPredicateType : Type (max u v + 1) :=
  {X : Type u} → {I : Type v} → [TopologicalSpace X] → (I → Set X) → Prop

def locallyFiniteValue : familyPredicateType.{u,v} := fun A => LocallyFinite A

def locallyDiscreteValue : familyPredicateType.{u,v} := fun A =>
  ∀ x, ∃ N ∈ 𝓝 x, {i | (A i ∩ N).Nonempty}.Subsingleton

def sigmaLocallyFiniteValue : familyPredicateType.{u,v} := fun {_} {I} _ A =>
  ∃ L : ℕ → Set I, (⋃ n, L n) = univ ∧
    ∀ n, LocallyFinite (fun i : L n => A i)

def sigmaLocallyDiscreteValue : familyPredicateType.{u,v} := fun {_} {I} _ A =>
  ∃ L : ℕ → Set I, (⋃ n, L n) = univ ∧
    ∀ n, locallyDiscreteValue (fun i : L n => A i)

def coverRefinementType : Type (max u v w + 1) :=
  {X : Type u} → {I : Type v} → {J : Type w} → (I → Set X) → (J → Set X) → Prop

def coverRefinementValue : coverRefinementType.{u,v,w} := fun U V =>
  (⋃ j, V j) = univ ∧ ∀ j, ∃ i, V j ⊆ U i

def paracompactType : Type (u + 1) := (X : Type u) → [TopologicalSpace X] → Prop

def paracompactValue : paracompactType := fun X => ParacompactSpace X

def locallyFinite_iff_neighborhood : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    LocallyFiniteFamily A ↔ ∀ x, ∃ N ∈ 𝓝 x, {i | (A i ∩ N).Nonempty}.Finite

def locallyFinite_iff_open_neighborhood : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    LocallyFiniteFamily A ↔ ∀ x, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ {i | (A i ∩ U).Nonempty}.Finite

def coverRefinement_iff : Prop :=
  ∀ {X : Type u} {I : Type v} {J : Type w} (U : I → Set X) (V : J → Set X),
    CoverRefinement U V ↔ (∀ x : X, ∃ j, x ∈ V j) ∧ ∀ j, ∃ i, V j ⊆ U i

def coverRefinement_original_covers : Prop :=
  ∀ {X : Type u} {I : Type v} {J : Type w} (U : I → Set X) (V : J → Set X),
    CoverRefinement U V → (⋃ i, U i) = univ

def locallyDiscrete_iff_open_neighborhood : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    LocallyDiscrete A ↔ ∀ x, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ {i | (A i ∩ U).Nonempty}.Subsingleton

def locallyDiscrete_locallyFinite : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    LocallyDiscrete A → LocallyFiniteFamily A

/-- Equivalent disjoint layers given by an assignment of a natural number to
 each original index; no indices, including repeated values, are lost. -/
def sigmaLocallyFinite_iff_layers : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    SigmaLocallyFinite A ↔ ∃ c : I → ℕ,
      ∀ n, LocallyFinite (fun i : {i // c i = n} => A i)

def sigmaLocallyDiscrete_iff_layers : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    SigmaLocallyDiscrete A ↔ ∃ c : I → ℕ,
      ∀ n, LocallyDiscrete (fun i : {i // c i = n} => A i)

def sigmaLocallyDiscrete_sigmaLocallyFinite : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    SigmaLocallyDiscrete A → SigmaLocallyFinite A

/-- The unrelated refinement indices may have the same universe as X.
The arbitrary-index consequence is specified separately below. -/
def paracompact_iff_open_cover_refinement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], Paracompact X ↔
    ∀ (I : Type u) (U : I → Set X), (∀ i, IsOpen (U i)) →
      (⋃ i, U i) = univ → ∃ (J : Type u) (V : J → Set X),
        (∀ j, IsOpen (V j)) ∧ LocallyFiniteFamily V ∧ CoverRefinement U V

/-- Every cover, with an arbitrary index universe, admits a refinement on the
same indices; empty refining members are permitted. -/
def paracompact_precise_refinement : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X], Paracompact X →
    ∀ U : I → Set X, (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
      ∃ V : I → Set X, (∀ i, IsOpen (V i)) ∧ LocallyFiniteFamily V ∧
        CoverRefinement U V ∧ ∀ i, V i ⊆ U i

/-- The necessary point-finiteness condition, with indexed multiplicity. -/
def locallyFinite_point_finite : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : I → Set X),
    LocallyFiniteFamily A → ∀ x, {i | x ∈ A i}.Finite

/-- Point finiteness is strictly weaker than local finiteness. -/
def pointFinite_not_locallyFinite : Prop :=
  ∃ (t : TopologicalSpace ℕ) (A : ℕ → Set ℕ),
    (∀ x, {i | x ∈ A i}.Finite) ∧ ¬ @LocallyFinite ℕ ℕ t A

/-- Repeating a nonempty set infinitely often cannot be locally finite. -/
def locallyFinite_const_iff : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : Set X), A.Nonempty →
    (LocallyFiniteFamily (fun _ : I => A) ↔ Finite I)

/-- Repeating a nonempty set twice already prevents local discreteness. -/
def locallyDiscrete_const_iff : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] (A : Set X), A.Nonempty →
    (LocallyDiscrete (fun _ : I => A) ↔ Subsingleton I)

def empty_members : Prop :=
  ∀ (X : Type u) (I : Type v) [TopologicalSpace X],
    LocallyFiniteFamily (fun _ : I => (∅ : Set X)) ∧
      LocallyDiscrete (fun _ : I => (∅ : Set X))

end Specs.D10Topology.Ch15.LocallyFiniteConventions
