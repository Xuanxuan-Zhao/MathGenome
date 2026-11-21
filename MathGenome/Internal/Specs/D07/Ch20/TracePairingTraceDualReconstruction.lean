import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.FieldTheory.Separable

/-!
Independent specification for the trace-dual reconstruction part of
K07.20.trace_pairing, paper.tex:5936–5963.

The trace is the trace of the multiplication operator, not an assumed sum of
embeddings. No characteristic restriction or nonvanishing of Tr(1) is imposed.
A finite index type describes an ordered basis by taking it to be Fin n.
Uniqueness below ranges over all indexed families, not just known bases.
-/

universe u v w
namespace Specs.D07.Ch20.TracePairingTraceDualReconstruction

open Module

/-- The indicated trace map is a linear equivalence with the full linear dual. -/
def TraceLinearEquivalence : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L],
    ∃ e : L ≃ₗ[K] Module.Dual K L,
      ∀ b x : L, e b x = Algebra.trace K L (b * x)

/-- Every linear functional is represented by one and only one field element. -/
def UniqueFunctionalRepresentation : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (f : L →ₗ[K] K),
    ∃! b : L, ∀ x : L, f x = Algebra.trace K L (b * x)

/-- Existence, basis status, uniqueness and reconstruction in one statement.
The uniqueness clause shows that any family satisfying the trace identities
is the underlying family of this basis, so basis status is a conclusion.
-/
def TraceDualBasisReconstruction : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (ι : Type w) [Fintype ι] [DecidableEq ι] (a : Basis ι K L),
    ∃ b : Basis ι K L,
      (∀ i j, Algebra.trace K L (a i * b j) = if i = j then 1 else 0) ∧
      (∀ c : ι → L,
        (∀ i j, Algebra.trace K L (a i * c j) = if i = j then 1 else 0) →
        c = (b : ι → L)) ∧
      (∀ x : L, x = ∑ i, Algebra.trace K L (x * b i) • a i)

end Specs.D07.Ch20.TracePairingTraceDualReconstruction
