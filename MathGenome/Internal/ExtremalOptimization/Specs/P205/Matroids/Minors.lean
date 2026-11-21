import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Models
import Mathlib.Combinatorics.Matroid.Minor.Contract

/-! Independent specifications for paper.tex, Lemma 9.7 (2274–2307).
Only the actual ground set is finite; the ambient type is arbitrary. The rank
is the shared natural rank, already identified upstream with the maximum size
of an independent subset. No independence assumption is imposed on `C`. -/
namespace Specs.P205.Matroids
open scoped Matroid
universe u

/-- Restriction has exactly the specified ground. -/
def RestrictionGround : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (U : Set α), U ⊆ M.E →
  (M ↾ U).E = U

/-- Restriction remains finite on a subset of the finite ground. -/
def RestrictionFinite : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (U : Set α), U ⊆ M.E →
  (M ↾ U).Finite

/-- Its independent sets are precisely the original independent subsets of `U`. -/
def RestrictionIndep : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (U : Set α), U ⊆ M.E →
  ∀ I : Set α, (M ↾ U).Indep I ↔ M.Indep I ∧ I ⊆ U

/-- Rank is preserved on every subset of `U`. -/
def RestrictionRank : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (U : Set α), U ⊆ M.E →
  ∀ S : Set α, S ⊆ U → rankValue (M ↾ U) S = rankValue M S

/-- The canonical contraction is a matroid on the complementary ground. -/
def ContractionGround : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (C : Set α), C ⊆ M.E →
  (M ／ C).E = M.E \ C

/-- Contraction remains finite, including empty and full contractions. -/
def ContractionFinite : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (C : Set α), C ⊆ M.E →
  (M ／ C).Finite

/-- Natural subtraction expresses the rank formula, with no assumption that `C` is independent. -/
def ContractionRank : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (C : Set α), C ⊆ M.E →
  ∀ S : Set α, S ⊆ M.E \ C →
  rankValue (M ／ C) S = rankValue M (S ∪ C) - rankValue M C

/-- The independence criterion holds for every choice of basis of `C`. -/
def ContractionIndep : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (C : Set α), C ⊆ M.E →
  ∀ I : Set α, M.IsBasis I C → ∀ J : Set α, J ⊆ M.E \ C →
  ((M ／ C).Indep J ↔ M.Indep (I ∪ J))

end Specs.P205.Matroids
