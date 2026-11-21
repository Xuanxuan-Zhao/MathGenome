import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
Independent specification of the one-sided-inverse example in K07.08.units,
paper.tex:1220–1226. `FreeSpace K` is the free vector space on the natural
numbers, not the space of all sequences. Multiplication in `Module.End` is
composition: `(S * T) v = S (T v)`.
The final statement applies to every associative unital ring, including the
zero ring, without a commutativity assumption.
-/

universe u v

namespace Specs.D07.Ch08.UnitsOneSidedInverseCounterexample

abbrev FreeSpace (K : Type u) [Zero K] := ℕ →₀ K

/-- The standard basis of the free vector space, with `e_i = single i 1`. -/
noncomputable def standardBasis (K : Type u) [Field K] :
    Module.Basis ℕ K (FreeSpace K) := Finsupp.basisSingleOne

noncomputable def e (K : Type u) [Field K] (i : ℕ) : FreeSpace K := Finsupp.single i 1

/-- The forward shift sends `e_i` to `e_(i+1)`. -/
noncomputable def T (K : Type u) [Field K] : Module.End K (FreeSpace K) :=
  Finsupp.lmapDomain K K Nat.succ

/-- Restriction along successor deletes the zero coordinate. -/
noncomputable def S (K : Type u) [Field K] : Module.End K (FreeSpace K) :=
  Finsupp.lcomapDomain Nat.succ Nat.succ_injective

def StandardBasisVectors : Prop :=
  ∀ (K : Type u) [Field K] (i : ℕ), standardBasis K i = e K i

def ShiftOnBasis : Prop :=
  ∀ (K : Type u) [Field K] (i : ℕ), T K (e K i) = e K (i + 1)

def BackwardShiftZero : Prop :=
  ∀ (K : Type u) [Field K], S K (e K 0) = 0

def BackwardShiftOnSucc : Prop :=
  ∀ (K : Type u) [Field K] (i : ℕ), S K (e K (i + 1)) = e K i

def BackwardShiftMulShift : Prop :=
  ∀ (K : Type u) [Field K], S K * T K = 1

def BasisZeroNeZero : Prop :=
  ∀ (K : Type u) [Field K], e K 0 ≠ 0

def ShiftMulBackwardShiftAtZero : Prop :=
  ∀ (K : Type u) [Field K], (T K * S K) (e K 0) = 0

def ShiftMulBackwardShiftNeOne : Prop :=
  ∀ (K : Type u) [Field K], T K * S K ≠ 1

def ShiftNotIsUnit : Prop :=
  ∀ (K : Type u) [Field K], ¬ IsUnit (T K)

def BackwardShiftNotIsUnit : Prop :=
  ∀ (K : Type u) [Field K], ¬ IsUnit (S K)

def LeftRightInverseUnique : Prop :=
  ∀ (R : Type v) [Ring R] (a s t : R), s * a = 1 → a * t = 1 → s = t

end Specs.D07.Ch08.UnitsOneSidedInverseCounterexample
