import MathGenome.Internal.Specs.D07.Ch02.CycleDecomposition
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Rat.Defs

/-!
Independent specification of `K07.02.transpositions_parity`, paper.tex:526–541.
Products use the accepted rightmost-first convention. `IsSwap` means a swap
of two distinct points, and products include the empty product. Integer units
are the canonical multiplicative group {1, -1}; no field of characteristic two
is used for the parity invariant. `Finite` and `Fintype` both allow the empty set.
-/

namespace Specs.D07.Ch02.TranspositionsParity

universe u v

def SignType : Type (u + 1) :=
  ∀ (X : Type u) [Fintype X], Equiv.Perm X →* ℤˣ

noncomputable def signValue : SignType.{u} := by
  classical
  exact fun _ _ => Equiv.Perm.sign

def TranspositionFactorization : Prop := by
  classical
  exact ∀ (X : Type u) [Finite X] (σ : Equiv.Perm X),
    ∃ L : List (Equiv.Perm X), L.prod = σ ∧ ∀ τ ∈ L, τ.IsSwap

def SignFactorization : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (L : List (Equiv.Perm X)),
    (∀ τ ∈ L, τ.IsSwap) → signValue X L.prod = (-1 : ℤˣ) ^ L.length

def ParityIndependent : Prop := by
  classical
  exact ∀ (X : Type u) [Finite X] (L M : List (Equiv.Perm X)),
    (∀ τ ∈ L, τ.IsSwap) → (∀ τ ∈ M, τ.IsSwap) →
    L.prod = M.prod → L.length % 2 = M.length % 2

def SignValues : Prop :=
  (∀ s : ℤˣ, s = 1 ∨ s = -1) ∧
  (1 : ℤˣ) ≠ -1 ∧
  ∀ (X : Type u) [Fintype X] (σ : Equiv.Perm X),
    signValue X σ = 1 ∨ signValue X σ = -1

def SignHomomorphism : Prop :=
  ∀ (X : Type u) [Fintype X],
    signValue X 1 = 1 ∧
    ∀ σ τ : Equiv.Perm X, signValue X (σ * τ) = signValue X σ * signValue X τ

def TranspositionSign : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (x y : X),
    x ≠ y → signValue X (Equiv.swap x y) = -1

/-- A self-swap is identity, so it is excluded from transposition counts. -/
def SelfSwapSign : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (x : X),
    signValue X (Equiv.swap x x) = 1

/-- The length is the number of distinct entries, including a one-cycle. -/
def CycleSign : Prop :=
  ∀ (X : Type u) [Fintype X] (l : List X) (h : l.Nodup),
    1 ≤ l.length →
    signValue X (PermutationConvention.cycleConstructorValue X l h) =
      (-1 : ℤˣ) ^ (l.length - 1)

def SignRelabeling : Prop :=
  ∀ (X : Type u) (Y : Type v) [Fintype X] [Fintype Y]
    (b : X ≃ Y) (σ : Equiv.Perm X),
    signValue Y ((b.symm.trans σ).trans b) = signValue X σ

def EmptySign : Prop :=
  ∀ (X : Type u) [Fintype X] [IsEmpty X] (σ : Equiv.Perm X),
    signValue X σ = 1

/-- The matrix sends e_j to e_(σ j), as in the source. -/
def DeterminantSign : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (σ : Equiv.Perm X),
    Matrix.det (fun i j : X => if i = σ j then (1 : ℚ) else 0) =
      ((signValue X σ : ℤ) : ℚ)

end Specs.D07.Ch02.TranspositionsParity
