import MathGenome.Internal.Specs.D07.Ch20.MultiplicationTraceNorm
import MathGenome.Internal.Specs.D07.Ch12.PowerBasis
import MathGenome.Internal.Specs.D07.Ch12.TowerLaw
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Independent specification of K07.20.characteristic_minpoly
(paper.tex:5886–5910). No separability or characteristic restriction is imposed
on the four general formulas. The example includes the failure of the
unweighted, distinct-embedding trace formula. -/

universe u v w
namespace Specs.D07.Ch20.CharacteristicMinpoly
noncomputable section
open Polynomial IntermediateField

def DegreeDivides : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : L),
    (minpoly K a).natDegree ∣ Module.finrank K L

def CharacteristicPolynomial : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : L),
    (Algebra.lmul K L a).charpoly =
      minpoly K a ^ (Module.finrank K L / (minpoly K a).natDegree)

def TraceFormula : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : L),
    Algebra.trace K L a =
      -((Module.finrank K L / (minpoly K a).natDegree : ℕ) : K) *
        (minpoly K a).coeff ((minpoly K a).natDegree - 1)

def NormFormula : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : L),
    Algebra.norm K a = (-1 : K) ^ Module.finrank K L *
      (minpoly K a).coeff 0 ^ (Module.finrank K L / (minpoly K a).natDegree)

/-- The hypotheses describe an arbitrary realization of K(u) with irreducible
X^p-t, rather than presupposing a special quotient implementation. Finiteness
is a conclusion here; it follows from these hypotheses. -/
def InseparableBinomial : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) (u : L),
    u ^ p = algebraMap K L t →
    Irreducible (X ^ p - C t : K[X]) → adjoin K {u} = ⊤ →
    FiniteDimensional K L ∧ Module.finrank K L = p ∧
      minpoly K u = X ^ p - C t ∧
      Algebra.trace K L = 0 ∧
      Algebra.norm K u = (-1 : K) ^ (p + 1) * t ∧
      Algebra.norm K u = t ∧ u ∉ Set.range (algebraMap K L)

/-- In any chosen algebraically closed overfield there is precisely one
embedding. Its value on u is outside the base field, so the singleton embedding
sum is not the multiplication trace (which belongs to K and is zero). -/
def SingleEmbedding : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) (u : L),
    u ^ p = algebraMap K L t →
    Irreducible (X ^ p - C t : K[X]) → adjoin K {u} = ⊤ →
    ∃ σ : L →ₐ[K] Ω, (∀ τ : L →ₐ[K] Ω, τ = σ) ∧
      σ u ∉ Set.range (algebraMap K Ω)

end
end Specs.D07.Ch20.CharacteristicMinpoly
