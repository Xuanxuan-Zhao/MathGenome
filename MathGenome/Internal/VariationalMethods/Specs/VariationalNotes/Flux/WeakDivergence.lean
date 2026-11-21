import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.LpDuality

/-! The constraint in paper.tex, Theorem `thm:dirichlet-flux`.
Scalar Sobolev functions use the existing one-dimensional Euclidean target.
The row of their weak-gradient matrix is identified with the Euclidean domain.
The distributional divergence is the sum of the distributional coordinate
derivatives, so its negative has the positive gradient pairing. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ENNReal InnerProductSpace

namespace VariationalNotes.Flux.WeakDivergenceSpec
open VariationalNotes.Sobolev

abbrev X {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) := W1pZero Ω 1 p
abbrev Y {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) :=
  Lp (Domain d) p.ennreal (domainMeasure Ω)

def conjugate (p : Exponent) (hp : 1 < p.real) : Exponent :=
  ⟨p.real / (p.real - 1), (Real.HolderConjugate.conjExponent hp).symm.lt.le⟩

instance conjugateHolder (p : Exponent) (hp : 1 < p.real) :
    ENNReal.HolderConjugate p.ennreal (conjugate p hp).ennreal :=
  (Real.HolderConjugate.conjExponent hp).ennrealOfReal

abbrev Flux {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real) :=
  Y Ω (conjugate p hp)

def rowIndex (d : ℕ) : (Fin 1 × Fin d) ≃ Fin d where
  toFun := Prod.snd
  invFun j := (0, j)
  left_inv := by rintro ⟨i,j⟩; exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl

def rowIsometry (d : ℕ) : Gradient 1 d ≃ₗᵢ[ℝ] Domain d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (rowIndex d)

/-- The bounded weak gradient on the source's zero-boundary space. -/
def gradientMap {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) : X Ω p →L[ℝ] Y Ω p :=
  ((rowIsometry d).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    p.ennreal (domainMeasure Ω)).comp
      ((gradient Ω 1 p).comp (zeroSubmodule Ω 1 p).subtypeL)

/-- The ordinary Banach-space transpose A*: (Lp)' → X'. -/
def adjointMap {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) :
    (Y Ω p →L[ℝ] ℝ) →L[ℝ] (X Ω p →L[ℝ] ℝ) :=
  ContinuousLinearMap.precomp ℝ (gradientMap Ω p)

/-- The canonical integral representation of a flux as an Lp functional. -/
def fluxPairing {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real) :
    Flux Ω p hp →L[ℝ] (Y Ω p →L[ℝ] ℝ) :=
  (innerSL ℝ (E := Domain d)).lpPairing (domainMeasure Ω)
    (conjugate p hp).ennreal p.ennreal

def fluxAdjoint {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real) :
    Flux Ω p hp →L[ℝ] (X Ω p →L[ℝ] ℝ) :=
  (adjointMap Ω p).comp (fluxPairing Ω p hp)

/-- This relation identifies each real smooth test with its Sobolev class.
Existence and uniqueness, as well as density, are obligations below. -/
def IsTestClass {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (φ : P102.U4.TestSpace ℝ Ω) (v : X Ω p) : Prop :=
  coordinateLp Ω p (0 : Fin 1) (value Ω 1 p v.val) =
    P102.U4.testToDomainLp Ω p.ennreal φ

/-- The ordinary vector of the coordinate derivatives of a smooth real test. -/
def testGradient {d : ℕ} (Ω : Opens (Domain d)) (φ : P102.U4.TestSpace ℝ Ω)
    (x : Domain d) : Domain d :=
  WithLp.toLp 2 fun j => P102.U4.testPartialWord Ω [j] φ x

/-- Divergence as a genuine distribution, with the usual minus sign on tests. -/
def divergence {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (σ : Flux Ω p hp) : P102.U4.DistributionSpace ℝ Ω :=
  ∑ j : Fin d, P102.U4.distributionPartial {j}
    (P102.U4.regularDistribution Ω (coordinateLp Ω (conjugate p hp) j σ))

def AllVariations {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (σ : Flux Ω p hp) (ℓ : X Ω p →L[ℝ] ℝ) : Prop :=
  ∀ v : X Ω p, (∫ x, inner ℝ (σ x) (gradientMap Ω p v x) ∂domainMeasure Ω) = ℓ v

def TestVariations {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (σ : Flux Ω p hp) (ℓ : X Ω p →L[ℝ] ℝ) : Prop :=
  ∀ (φ : P102.U4.TestSpace ℝ Ω) (v : X Ω p), IsTestClass Ω p φ v →
    (∫ x, inner ℝ (σ x) (testGradient Ω φ x) ∂domainMeasure Ω) = ℓ v

def DistributionConstraint {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (hp : 1 < p.real) (σ : Flux Ω p hp) (ℓ : X Ω p →L[ℝ] ℝ) : Prop :=
  ∀ (φ : P102.U4.TestSpace ℝ Ω) (v : X Ω p), IsTestClass Ω p φ v →
    -(divergence Ω p hp σ φ) = ℓ v

namespace Expected
def GradientType := {d : ℕ} → (Ω : Opens (Domain d)) → (p : Exponent) → X Ω p →L[ℝ] Y Ω p
def GradientValue : GradientType := @gradientMap
def AdjointType := {d : ℕ} → (Ω : Opens (Domain d)) → (p : Exponent) →
  (Y Ω p →L[ℝ] ℝ) →L[ℝ] (X Ω p →L[ℝ] ℝ)
def AdjointValue : AdjointType := @adjointMap
def FluxAdjointType := {d : ℕ} → (Ω : Opens (Domain d)) → (p : Exponent) →
  (hp : 1 < p.real) → Flux Ω p hp →L[ℝ] (X Ω p →L[ℝ] ℝ)
def FluxAdjointValue : FluxAdjointType := @fluxAdjoint

def GradientFormula : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (v : X Ω p),
    ∀ᵐ x ∂domainMeasure Ω, ∀ j : Fin d,
      gradientMap Ω p v x j = gradient Ω 1 p v.val x (0,j)

def SmoothTests : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (φ : P102.U4.TestSpace ℝ Ω),
    (∃! v : X Ω p, IsTestClass Ω p φ v) ∧
    (∀ v : X Ω p, IsTestClass Ω p φ v →
      (gradientMap Ω p v : Domain d → Domain d) =ᵐ[domainMeasure Ω] testGradient Ω φ)

def TestDensity : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent),
    closure {v : X Ω p | ∃ φ : P102.U4.TestSpace ℝ Ω, IsTestClass Ω p φ v} = Set.univ

def AdjointFormula : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
      (σ : Flux Ω p hp) (v : X Ω p),
    Integrable (fun x => inner ℝ (σ x) (gradientMap Ω p v x)) (domainMeasure Ω) ∧
      fluxAdjoint Ω p hp σ v = ∫ x, inner ℝ (σ x) (gradientMap Ω p v x) ∂domainMeasure Ω

/-- On the paper's domains the integral pairing used in A* is precisely a
linear isometric duality identification, not an unspecified representation. -/
def DualityAdjoint : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p : Exponent) (hp : 1 < p.real),
    ∃ T : Flux Ω p hp ≃ₗᵢ[ℝ] (Y Ω p →L[ℝ] ℝ),
      (∀ σ v, T σ v = ∫ x, inner ℝ (σ x) (v x) ∂domainMeasure Ω) ∧
      ∀ σ, fluxAdjoint Ω p hp σ = adjointMap Ω p (T σ)

def DivergenceFormula : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
      (σ : Flux Ω p hp) (φ : P102.U4.TestSpace ℝ Ω),
    -(divergence Ω p hp σ φ) =
      ∫ x, inner ℝ (σ x) (testGradient Ω φ x) ∂domainMeasure Ω

def ConstraintEquivalences : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p : Exponent) (hp : 1 < p.real) (ℓ : X Ω p →L[ℝ] ℝ) (σ : Flux Ω p hp),
      (fluxAdjoint Ω p hp σ = ℓ ↔ AllVariations Ω p hp σ ℓ) ∧
      (AllVariations Ω p hp σ ℓ ↔ TestVariations Ω p hp σ ℓ) ∧
      (TestVariations Ω p hp σ ℓ ↔ DistributionConstraint Ω p hp σ ℓ)
end Expected
end VariationalNotes.Flux.WeakDivergenceSpec
