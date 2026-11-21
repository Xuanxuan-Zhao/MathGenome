import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Generic interfaces for paper.tex, Chapter 23, lines 6203--6215.
The canonical types are shared here so that downstream specifications can use
exactly the same domains without importing an implementation.
-/

open Set
open scoped ENNReal

universe u

namespace D11.Ch23

/-- A sigma-ring of subsets of an arbitrary type, including an empty type.
There is deliberately no axiom requiring the whole space to belong. -/
structure SigmaRing (X : Type u) where
  sets : Set (Set X)
  empty_mem : ∅ ∈ sets
  diff_mem : ∀ ⦃A B : Set X⦄, A ∈ sets → B ∈ sets → A \ B ∈ sets
  iUnion_mem : ∀ (A : ℕ → Set X), (∀ n, A n ∈ sets) → (⋃ n, A n) ∈ sets

instance {X : Type u} : SetLike (SigmaRing X) (Set X) where
  coe := SigmaRing.sets
  coe_injective R S h := by
    cases R
    cases S
    cases h
    rfl

/-- A nonnegative extended-valued measure whose domain is precisely the given
sigma-ring. Values on sets outside the ring are not part of this interface. -/
structure SigmaRingMeasure {X : Type u} (R : SigmaRing X) where
  toFun : {A : Set X // A ∈ R} → ℝ≥0∞
  empty' : toFun ⟨∅, R.empty_mem⟩ = 0
  iUnion' : ∀ (A : ℕ → Set X) (hA : ∀ n, A n ∈ R),
    Pairwise (fun i j => Disjoint (A i) (A j)) →
      toFun ⟨⋃ n, A n, R.iUnion_mem A hA⟩ = ∑' n, toFun ⟨A n, hA n⟩

instance {X : Type u} {R : SigmaRing X} :
    CoeFun (SigmaRingMeasure R) (fun _ => {A : Set X // A ∈ R} → ℝ≥0∞) :=
  ⟨SigmaRingMeasure.toFun⟩

end D11.Ch23

namespace Specs.D11.Ch23.SigmaRingInterfaces

open _root_.D11.Ch23

/-- Expected type and value of generation by intersection of all sigma-rings
containing the supplied family. The universal membership condition is precisely
membership in that intersection. -/
def generatedSigmaRingType : Type (u + 1) :=
  {X : Type u} → Set (Set X) → SigmaRing X

def generatedSigmaRingValue : generatedSigmaRingType.{u} :=
  fun {X} F =>
    { sets := {A | ∀ R : SigmaRing X, F ⊆ (R : Set (Set X)) → A ∈ R}
      empty_mem := fun R _ => R.empty_mem
      diff_mem := fun {_ _} hA hB R hF => R.diff_mem (hA R hF) (hB R hF)
      iUnion_mem := fun A hA R hF => R.iUnion_mem A (fun n => hA n R hF) }

/-- Exact, unrestricted characterization of the sigma-ring interface. -/
def sigmaRingCharacterization : Prop :=
  ∀ {X : Type u} (S : Set (Set X)),
    (∃ R : SigmaRing X, (R : Set (Set X)) = S) ↔
      ∅ ∈ S ∧
      (∀ ⦃A B : Set X⦄, A ∈ S → B ∈ S → A \ B ∈ S) ∧
      (∀ (A : ℕ → Set X), (∀ n, A n ∈ S) → (⋃ n, A n) ∈ S)

/-- Every and only function with zero empty mass and countable additivity on
disjoint sequences in R can be packaged as a sigma-ring measure. -/
def sigmaRingMeasureCharacterization : Prop :=
  ∀ {X : Type u} (R : SigmaRing X) (m : {A : Set X // A ∈ R} → ℝ≥0∞),
    (∃ μ : SigmaRingMeasure R, μ.toFun = m) ↔
      m ⟨∅, R.empty_mem⟩ = 0 ∧
      (∀ (A : ℕ → Set X) (hA : ∀ n, A n ∈ R),
        Pairwise (fun i j => Disjoint (A i) (A j)) →
          m ⟨⋃ n, A n, R.iUnion_mem A hA⟩ = ∑' n, m ⟨A n, hA n⟩)

def generatedSigmaRingContains : Prop :=
  ∀ {X : Type u} (F : Set (Set X)),
    F ⊆ (generatedSigmaRingValue F : Set (Set X))

def generatedSigmaRingLeast : Prop :=
  ∀ {X : Type u} (F : Set (Set X)) (R : SigmaRing X),
    F ⊆ (R : Set (Set X)) →
      (generatedSigmaRingValue F : Set (Set X)) ⊆ (R : Set (Set X))

def generatedSigmaRingIntersection : Prop :=
  ∀ {X : Type u} (F : Set (Set X)),
    (generatedSigmaRingValue F : Set (Set X)) =
      ⋂ (R : SigmaRing X) (_ : F ⊆ (R : Set (Set X))), (R : Set (Set X))

end Specs.D11.Ch23.SigmaRingInterfaces
