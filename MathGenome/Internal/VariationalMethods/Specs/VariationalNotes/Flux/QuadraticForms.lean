import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.SlabPoincare
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.LaxMilgram
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded

/-! The quadratic discussion in paper.tex §v09-03, with the scalar convention
from the preamble and §v03-07. The energy is real valued, even over ℂ.
The canonical Sobolev type and the gradient Hilbert structure are those of
SlabPoincare; no replacement Sobolev model is introduced. -/
noncomputable section
open scoped ComplexConjugate InnerProductSpace
open MeasureTheory TopologicalSpace
universe u v
namespace VariationalNotes.Flux.QuadraticSpecs

/-- The symmetric part over ℝ, and the Hermitian part over ℂ. -/
def hermitianPart {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (u v : H) : 𝕜 :=
  (a u v + conj (a v u)) / 2

/-- The gradient pairing on the original equivalence classes. -/
def gradientPairing {d m : ℕ} (Ω : Opens (Sobolev.Domain d))
    (u v : Sobolev.H1Zero Ω m) : ℝ :=
  ∫ x, Sobolev.frobenius (Sobolev.gradient Ω m Sobolev.Exponent.two u.val x)
    (Sobolev.gradient Ω m Sobolev.Exponent.two v.val x) ∂Sobolev.domainMeasure Ω

def GradientHilbert : Prop := Sobolev.SlabExpected.Hilbert

/-- Bounded open domains in every positive physical dimension, including the
empty domain. The datum is continuous for the original full Sobolev norm. -/
def GradientRiesz : Prop :=
  ∀ {n m : ℕ} (Ω : Opens (Sobolev.Domain (n+1))),
    Bornology.IsBounded (Ω : Set (Sobolev.Domain (n+1))) →
    ∀ ℓ : Sobolev.H1Zero Ω m →L[ℝ] ℝ,
      ∃! u : Sobolev.H1Zero Ω m, ∀ v, gradientPairing Ω u v = ℓ v

/-- Full-form solvability, the estimate, and the symmetric/Hermitian energy
characterization, for exactly the real or complex Hilbert hypotheses. -/
def FullForm : Prop := Existence.Specs.laxMilgram.{u,v}

/-- Directional differentiation is along the real parameter t, with the
scalar t embedded in the original field. No symmetry hypothesis is used. -/
def DirectionalDerivative : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (ℓ : H →L[𝕜] 𝕜) (u v : H),
    HasDerivAt (fun t : ℝ => Existence.Specs.laxMilgramEnergy a ℓ (u + (t : 𝕜) • v))
      (RCLike.re (hermitianPart a u v - ℓ v)) 0

/-- In particular, the real derivative involves the symmetric part. -/
def RealDerivative : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) (u v : H),
    HasDerivAt (fun t : ℝ => a (u + t • v) (u + t • v) / 2 - ℓ (u + t • v))
      ((a u v + a v u) / 2 - ℓ v) 0

/-- The two real tests v and iv recover the complex equation at v. -/
def ComplexTests : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [NormedSpace ℂ H]
    (a : H →L⋆[ℂ] H →L[ℂ] ℂ) (ℓ : H →L[ℂ] ℂ) (u v : H),
    (Complex.re (hermitianPart a u v - ℓ v) = 0 ∧
      Complex.re (hermitianPart a u (Complex.I • v) - ℓ (Complex.I • v)) = 0) ↔
      hermitianPart a u v = ℓ v

/-- For a coercive form, stationarity and minimization characterize its
Hermitian part, while FullForm independently solves the original form. -/
def PartEnergy : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (α : ℝ),
    0 < α → (∀ w : H, α * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) →
    ∀ ℓ : H →L[𝕜] 𝕜,
      (∀ u : H, (∀ v, Existence.Specs.laxMilgramEnergy a ℓ u ≤
          Existence.Specs.laxMilgramEnergy a ℓ v) ↔
        ∀ v, hermitianPart a u v = ℓ v) ∧
      (∃! u : H, ∀ v, Existence.Specs.laxMilgramEnergy a ℓ u ≤
          Existence.Specs.laxMilgramEnergy a ℓ v) ∧
      (∀ u : H, (∀ v, RCLike.re (hermitianPart a u v - ℓ v) = 0) ↔
        ∀ v, hermitianPart a u v = ℓ v)

end VariationalNotes.Flux.QuadraticSpecs
