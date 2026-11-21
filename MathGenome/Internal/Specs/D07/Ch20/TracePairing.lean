import MathGenome.Internal.Specs.D07.Ch20.TracePairingTraceDualReconstruction
import Mathlib.FieldTheory.Finite.GaloisField

/-!
Independent specification of K07.20.trace_pairing, paper.tex:5936–5950.
The trace is the multiplication-operator trace. All field extensions carry
their specified scalar embedding; finite dimension is imposed throughout
the general theorem. There is no restriction on the characteristic.

An arbitrary finite index type includes the ordered bases indexed by Fin n.
The finite-field example uses cardinalities, so applies to every compatible
copy of F_(q^p)/F_q. The GaloisField specialization also supplies explicit
examples for every prime p, without assuming nonzero trace as a hypothesis.
-/

universe u v w
namespace Specs.D07.Ch20.TracePairing

open Module
noncomputable section

def NondegenerateIffSeparable : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    (Algebra.traceForm K L).Nondegenerate ↔ Algebra.IsSeparable K L

def TraceNonzero : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Algebra.trace K L ≠ 0

def TraceSurjective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Surjective (Algebra.trace K L)

def TraceLinearEquivalence : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L],
    ∃ e : L ≃ₗ[K] Module.Dual K L,
      ∀ b x : L, e b x = Algebra.trace K L (b * x)

def UniqueFunctionalRepresentation : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (f : L →ₗ[K] K),
    ∃! b : L, ∀ x : L, f x = Algebra.trace K L (b * x)

/-- Existence as an actual basis, uniqueness among all indexed families,
and the coordinate reconstruction formula. -/
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

/-- The example F_(q^p)/F_q, for any finite fields with their given
embedding and the indicated cardinality. Degree and separability are
conclusions, not additional assumptions. -/
def FiniteFieldTraceOneZero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (K : Type u) (L : Type v) [Field K] [Field L]
    [Finite K] [Finite L] [Algebra K L] [CharP K p],
    Nat.card L = Nat.card K ^ p →
      Module.finrank K L = p ∧ Algebra.IsSeparable K L ∧
      Algebra.trace K L 1 = 0 ∧
      Function.Surjective (Algebra.trace K L) ∧ Algebra.trace K L ≠ 0

/-- Concrete examples exist: F_(p^p)/F_p for every prime p. -/
def PrimeFieldExample : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    Nat.card (GaloisField p p) = p ^ p ∧
    Module.finrank (ZMod p) (GaloisField p p) = p ∧
    Algebra.IsSeparable (ZMod p) (GaloisField p p) ∧
    Algebra.trace (ZMod p) (GaloisField p p) 1 = 0 ∧
    Function.Surjective (Algebra.trace (ZMod p) (GaloisField p p)) ∧
    Algebra.trace (ZMod p) (GaloisField p p) ≠ 0

end
end Specs.D07.Ch20.TracePairing
