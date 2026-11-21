import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
Independent specification of K07.20.separable_part (paper.tex:5833–5853).

The field `separableClosure K L` is internal to the specified extension L/K;
its underlying set is exactly the elements separable over K. The induced
algebra structures on intermediate fields provide compatible inclusions.
The algebraic extension may have infinite degree. Finite dimension is
required only for the last two finiteness assertions. No perfection of K
or separability of L/K is assumed. In positive characteristic the common
exponent is quantified before all elements of L.
-/

universe u v

namespace Specs.D07.Ch20.SeparablePart

/-- The separable elements themselves form the indicated intermediate field. -/
def SubfieldCarrier : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L],
    (separableClosure K L : Set L) = {x : L | IsSeparable K x}

/-- The lower step S/K is separable. -/
def SeparableLowerStep : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L], Algebra.IsSeparable K (separableClosure K L)

/-- The upper step L/S is purely inseparable, also in characteristic zero. -/
def PurelyInseparableUpperStep : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L], IsPurelyInseparable (separableClosure K L) L

/-- An intermediate field has the two properties exactly when it is S. -/
def UniqueSeparablePart : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (T : IntermediateField K L),
    (Algebra.IsSeparable K T ∧ IsPurelyInseparable T L) ↔ T = separableClosure K L

/-- Existence and uniqueness without any finite-degree assumption. -/
def ExistsUniqueSeparablePart : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L],
    ∃! S : IntermediateField K L, Algebra.IsSeparable K S ∧ IsPurelyInseparable S L

/-- In characteristic zero every algebraic element lies in S, so S=L. -/
def CharacteristicZeroPart : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [CharZero K], separableClosure K L = ⊤

/-- Finiteness here means finite vector-space dimension, not a finite set. -/
def FiniteSeparablePart : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], FiniteDimensional K (separableClosure K L)

/-- A single power works for every element of a finite extension. -/
def UniformExponent : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) [CharP K p], p.Prime →
    ∃ r : ℕ, ∀ x : L, x ^ (p ^ r) ∈ separableClosure K L

end Specs.D07.Ch20.SeparablePart
