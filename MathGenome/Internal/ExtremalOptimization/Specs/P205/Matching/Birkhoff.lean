import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Basic.Real.Basic

/-! Independent statements for paper.tex, Theorem W42 (8.7).
No nonemptiness assumption is imposed on the index type or allowed relation. -/
namespace P205.Matching

/-- Positions outside `allowed` are prescribed to be zero. -/
def SupportedOn {n : Type*} (allowed : n → n → Prop) (M : Matrix n n ℝ) : Prop :=
  ∀ i j, ¬ allowed i j → M i j = 0

/-- The doubly stochastic matrices respecting all prescribed zero positions. -/
def restrictedDoublyStochastic {n : Type*} [Fintype n] [DecidableEq n]
    (allowed : n → n → Prop) : Set (Matrix n n ℝ) :=
  {M | M ∈ doublyStochastic ℝ n ∧ SupportedOn allowed M}

/-- Permutation matrices whose selected positions are all allowed. -/
def supportedPermutationMatrices {n : Type*} [Fintype n] [DecidableEq n]
    (allowed : n → n → Prop) : Set (Matrix n n ℝ) :=
  {M | ∃ σ : Equiv.Perm n, (∀ i, allowed i (σ i)) ∧ σ.permMatrix ℝ = M}

end P205.Matching

namespace Specs.P205.Matching.Birkhoff
open _root_.P205.Matching
open scoped BigOperators

/-- Finite coefficients, nonnegative and of total mass one, also in size zero. -/
def UnrestrictedDecomposition : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n] (M : Matrix n n ℝ),
    M ∈ doublyStochastic ℝ n →
    ∃ w : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ w σ) ∧
      (∑ σ, w σ) = 1 ∧ (∑ σ, w σ • σ.permMatrix ℝ) = M

def UnrestrictedHull : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n],
    (doublyStochastic ℝ n : Set (Matrix n n ℝ)) =
      convexHull ℝ {σ.permMatrix ℝ | σ : Equiv.Perm n}

def UnrestrictedExtremePoints : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n],
    Set.extremePoints ℝ (doublyStochastic ℝ n : Set (Matrix n n ℝ)) =
      {σ.permMatrix ℝ | σ : Equiv.Perm n}

/-- Every active term of any nonnegative permutation decomposition respects its zeros. -/
def ZeroSupportBridge : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (w : Equiv.Perm n → ℝ), (∀ σ, 0 ≤ w σ) →
    (∑ σ, w σ • σ.permMatrix ℝ) = M →
    ∀ σ, w σ ≠ 0 → ∀ i j, M i j = 0 → σ.permMatrix ℝ i j = 0

def RestrictedDecomposition : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n] (allowed : n → n → Prop)
    (M : Matrix n n ℝ), M ∈ restrictedDoublyStochastic allowed →
    ∃ w : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ w σ) ∧
      (∑ σ, w σ) = 1 ∧ (∑ σ, w σ • σ.permMatrix ℝ) = M ∧
      ∀ σ, w σ ≠ 0 → ∀ i, allowed i (σ i)

def RestrictedHull : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n] (allowed : n → n → Prop),
    restrictedDoublyStochastic allowed = convexHull ℝ (supportedPermutationMatrices allowed)

def RestrictedExtremePoints : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n] (allowed : n → n → Prop),
    Set.extremePoints ℝ (restrictedDoublyStochastic allowed) =
      supportedPermutationMatrices allowed

def InfeasibleAllowedRelation : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n] (allowed : n → n → Prop),
    (¬ ∃ σ : Equiv.Perm n, ∀ i, allowed i (σ i)) →
    restrictedDoublyStochastic allowed = ∅ ∧
      convexHull ℝ (supportedPermutationMatrices allowed) = ∅ ∧
      Set.extremePoints ℝ (restrictedDoublyStochastic allowed) = ∅

end Specs.P205.Matching.Birkhoff
