import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Combinatorics.Matroid.Closure

/-! W75: projective points are indexed by the projectivization, explicitly bridged
below to the one-dimensional subspaces. Representatives are arbitrary nonzero
vectors in the corresponding subspaces. All matroids use the canonical indexed
vector construction and the shared integer rank. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set Submodule
universe u v

/-- A nonzero representative of each projective point. -/
def ProjectiveRepresentative (K : Type u) [Field K] (V : Type v)
    [AddCommGroup V] [Module K V] (v : Projectivization K V → V) : Prop :=
  ∀ p, ∃ h : v p ≠ 0, Projectivization.mk K (v p) h = p

def projectiveMatroid (K : Type u) [Field K] (V : Type v)
    [AddCommGroup V] [Module K V] [Finite V]
    (v : Projectivization K V → V) : _root_.Matroid (Projectivization K V) :=
  vectorMatroid K univ (Set.toFinite _) v

instance (K : Type u) [Field K] (V : Type v)
    [AddCommGroup V] [Module K V] [Finite V] (v : Projectivization K V → V) :
    (projectiveMatroid K V v).Finite := inferInstanceAs (vectorMatroid K _ _ _).Finite

/-- Points whose one-dimensional subspaces lie inside U. -/
def projectivePointsIn {K : Type u} [Field K] {V : Type v}
    [AddCommGroup V] [Module K V] (U : Submodule K V) : Set (Projectivization K V) :=
  {p | p.submodule ≤ U}

def ProjectiveRepresentativeType := ∀ (K : Type u) [Field K] (V : Type v)
  [AddCommGroup V] [Module K V], (Projectivization K V → V) → Prop

def projectiveMatroidType := ∀ (K : Type u) [Field K] (V : Type v)
  [AddCommGroup V] [Module K V] [Finite V],
  (Projectivization K V → V) → _root_.Matroid (Projectivization K V)

def projectivePointsInType := ∀ {K : Type u} [Field K] {V : Type v}
  [AddCommGroup V] [Module K V], Submodule K V → Set (Projectivization K V)

def projectiveSubspaceBridge : Prop := ∀ (K : Type u) [Field K] (V : Type v)
  [AddCommGroup V] [Module K V],
  (∃ e : Projectivization K V ≃ {U : Submodule K V // Module.finrank K U = 1},
    ∀ p, (e p).val = p.submodule) ∧
  ∀ (p : Projectivization K V) (x : V),
    (x ≠ 0 ∧ x ∈ p.submodule) ↔ ∃ h : x ≠ 0, Projectivization.mk K x h = p

/-- Reindexing an arbitrary subspace-indexed choice gives precisely the same
independence relation in the two canonical vector matroids. -/
def projectiveReindexBridge : Prop := ∀ (K : Type u) [Field K] (V : Type v)
  [AddCommGroup V] [Module K V] [Finite V]
  (v : {U : Submodule K V // Module.finrank K U = 1} → V),
  (∀ U, v U ≠ 0 ∧ v U ∈ U.val) →
  let e := Projectivization.equivSubmodule K V
  ProjectiveRepresentative K V (v ∘ e) ∧
  ∀ I : Set (Projectivization K V),
    (projectiveMatroid K V (v ∘ e)).Indep I ↔
    (vectorMatroid K (e '' univ) ((Set.toFinite _).image e) v).Indep (e '' I)

def projectiveRepValid : Prop := ∀ (K : Type u) [Field K] (V : Type v)
  [AddCommGroup V] [Module K V], ProjectiveRepresentative K V Projectivization.rep

def projectiveChoiceIndependent : Prop := ∀ (K : Type u) [Field K] (V : Type v)
  [AddCommGroup V] [Module K V] [Finite V] (v w : Projectivization K V → V),
  ProjectiveRepresentative K V v → ProjectiveRepresentative K V w →
  projectiveMatroid K V v = projectiveMatroid K V w

/-- Singletons and all distinct pairs are independent: no loops or parallel pairs. -/
def projectiveSimple : Prop := ∀ (K : Type u) [Field K] (V : Type v)
  [AddCommGroup V] [Module K V] [Finite V] (v : Projectivization K V → V),
  ProjectiveRepresentative K V v →
  (∀ p, (projectiveMatroid K V v).Indep {p}) ∧
  ∀ p q, p ≠ q → (projectiveMatroid K V v).Indep {p, q}

def projectiveGround : Prop := ∀ (K : Type u) [Field K] (V : Type v)
  [AddCommGroup V] [Module K V] [Finite V] (v : Projectivization K V → V),
  (projectiveMatroid K V v).E = univ

def projectiveRank : Prop := ∀ (K : Type u) [Field K] [Finite K] (r : ℕ),
  1 ≤ r → ∀ v : Projectivization K (Fin r → K) → (Fin r → K),
  ProjectiveRepresentative K (Fin r → K) v →
  rank (projectiveMatroid K (Fin r → K) v) univ = (r : ℤ)

def projectiveCardinality : Prop := ∀ (K : Type u) [Field K] [Finite K] (r : ℕ),
  1 ≤ r → ∀ v : Projectivization K (Fin r → K) → (Fin r → K),
  (projectiveMatroid K (Fin r → K) v).E.ncard =
    (Nat.card K ^ r - 1) / (Nat.card K - 1)

def projectiveDimensionOne : Prop := ∀ (K : Type u) [Field K] [Finite K],
  Nat.card (Projectivization K (Fin 1 → K)) = 1

def projectiveFieldSize : Prop := ∀ (K : Type u) [Field K] [Finite K], 2 ≤ Nat.card K

/-- The entire point set of a two-dimensional subspace is a closed rank-two
set in the canonical matroid and has q+1 points. -/
def projectiveLine : Prop := ∀ (K : Type u) [Field K] [Finite K] (r : ℕ),
  2 ≤ r → ∀ v : Projectivization K (Fin r → K) → (Fin r → K),
  ProjectiveRepresentative K (Fin r → K) v →
  ∀ U : Submodule K (Fin r → K), Module.finrank K U = 2 →
  (projectiveMatroid K (Fin r → K) v).IsFlat (projectivePointsIn U) ∧
  rank (projectiveMatroid K (Fin r → K) v) (projectivePointsIn U) = 2 ∧
  (projectivePointsIn U).ncard = Nat.card K + 1

end FiniteCombinatorics.Matroid.Expected
