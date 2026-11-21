import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Linarith

/-! Independent statements for paper.tex:5990–6010.  The generator condition
means that every K-automorphism is an integer power of σ, including degree one.
The norm is the determinant of multiplication, `Algebra.norm`.

The concrete model of ℚ(i) is the quadratic algebra with basis (1,i) and
relation i² = -1. The embedding statement identifies it with the usual
rational complex numbers, rather than assuming such an identification. -/
universe u v
namespace Specs.D07.Ch20.Hilbert90Multiplicative

noncomputable section

def Hilbert90 : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (_ : ∀ τ, τ ∈ Subgroup.zpowers σ) (a : L),
    a ≠ 0 → (Algebra.norm K a = 1 ↔ ∃ b : L, b ≠ 0 ∧ a = b / σ b)

abbrev GaussianRational := QuadraticAlgebra ℚ (-1) 0

instance noRationalRoot : Fact (∀ r : ℚ, r ^ 2 ≠ -1 + 0 * r) := by
  refine ⟨fun r h => ?_⟩
  have := sq_nonneg r
  norm_num at h
  linarith

def ComplexRealization : Prop :=
  ∃ f : GaussianRational →ₐ[ℚ] ℂ, Function.Injective f ∧
    (∀ s t : ℚ, f (⟨s,t⟩ : GaussianRational) = (s : ℂ) + (t : ℂ) * Complex.I) ∧
    ∀ z, f (star z) = star (f z)

def RationalNorm : Prop :=
  ∀ a b : ℚ, Algebra.norm ℚ (⟨a,b⟩ : GaussianRational) = a^2 + b^2

def RationalNormOne : Prop :=
  ∀ a b : ℚ, Algebra.norm ℚ (⟨a,b⟩ : GaussianRational) = 1 ↔ a^2 + b^2 = 1

def RationalDenominator : Prop :=
  ∀ s t : ℚ, (s,t) ≠ (0,0) → s^2 + t^2 ≠ 0

def RationalQuotient : Prop :=
  ∀ s t : ℚ, (s,t) ≠ (0,0) →
    (⟨s,t⟩ : GaussianRational) / star (⟨s,t⟩ : GaussianRational) =
      (⟨(s^2-t^2)/(s^2+t^2), 2*s*t/(s^2+t^2)⟩ : GaussianRational)

/-- Both directions: the parameters produce rational points, and all points occur. -/
def RationalCircle : Prop :=
  ∀ a b : ℚ, a^2 + b^2 = 1 ↔
    ∃ s t : ℚ, (s,t) ≠ (0,0) ∧
      a = (s^2-t^2)/(s^2+t^2) ∧ b = 2*s*t/(s^2+t^2)

/-- In the rational complex copy, norm one is precisely a quotient by conjugation. -/
def RationalHilbert90 : Prop :=
  ∀ a b : ℚ, Algebra.norm ℚ (⟨a,b⟩ : GaussianRational) = 1 ↔
    ∃ s t : ℚ, (s,t) ≠ (0,0) ∧
      (⟨a,b⟩ : GaussianRational) =
        (⟨s,t⟩ : GaussianRational) / star (⟨s,t⟩ : GaussianRational)

end
end Specs.D07.Ch20.Hilbert90Multiplicative
