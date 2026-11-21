import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.IntegralRegularity
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.SlabPoincare
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.ReflexiveDirectMethod

/-! The primal part of `thm:dirichlet-flux`, paper.tex 4409–4439.
The scalar gradient is the single row of the shared Frobenius weak gradient,
reindexed isometrically as ℝᵈ. All integrals use restricted Lebesgue measure
on the actual open domain. Bounded openness, without any boundary regularity,
is the only geometric hypothesis; empty domains are allowed. -/
noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped Topology
namespace VariationalNotes.Flux.Primal
open Sobolev

/-- The canonical identification of a one-row matrix with a Euclidean vector. -/
def rowIsometry (d : ℕ) : Gradient 1 d ≃ₗᵢ[ℝ] Vector d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.uniqueProd (Fin d) (Fin 1))

/-- The distributional scalar gradient, as a genuine Euclidean-vector Lp class. -/
def gradientMap {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent) :
    W1pZero Ω 1 p →L[ℝ] Lp (Vector d) p.ennreal (domainMeasure Ω) :=
  (((rowIsometry d).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    p.ennreal (domainMeasure Ω)).comp (gradient Ω 1 p)).comp
    (zeroSubmodule Ω 1 p).subtypeL

/-- The real primal functional; integrability is a conclusion, not an assumption. -/
def objective {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (F : Domain d → Vector d → ℝ) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ)
    (u : W1pZero Ω 1 p) : ℝ :=
  (∫ x, F x (gradientMap Ω p u x) ∂domainMeasure Ω) - ℓ u

/-- Extend domain data by zero solely to use the ambient restricted-measure model. -/
def extendFromDomain {d : ℕ} (Ω : Opens (Domain d)) {E : Type*} [Zero E]
    (f : Ω → E) (x : Domain d) : E := by
  classical
  exact if hx : x ∈ Ω then f ⟨x, hx⟩ else 0

end Primal

namespace PrimalExpected
open Sobolev Primal

/-- Full primal attainment, including integrability, weak lower semicontinuity,
coercivity, a finite real greatest lower bound and the quantitative lower bound. -/
def AmbientAttainment : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent), 1 < p.real →
  ∀ (F : Domain d → Vector d → ℝ) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ),
    Sobolev.CaratheodorySpecs.Caratheodory (domainMeasure Ω) F →
  ∀ (a₀ a₁ : ℝ) (a : Domain d → ℝ), 0 < a₀ → 0 ≤ a₁ →
    Integrable a (domainMeasure Ω) →
    (∀ᵐ x ∂domainMeasure Ω, 0 ≤ a x) →
    (∀ᵐ x ∂domainMeasure Ω, ∀ z,
      a₀ * ‖z‖ ^ p.real - a x ≤ F x z ∧ F x z ≤ a x + a₁ * ‖z‖ ^ p.real) →
    (∀ᵐ x ∂domainMeasure Ω, ConvexOn ℝ univ (F x)) →
    let J := objective Ω p F ℓ
    (∀ u, Integrable (fun x => F x (gradientMap Ω p u x)) (domainMeasure Ω) ∧
      Sobolev.CaratheodorySpecs.lpIntegralEnergy (domainMeasure Ω) F (gradientMap Ω p u) -
        (ℓ u : EReal) = (J u : EReal)) ∧
    ConvexOn ℝ univ J ∧ Continuous J ∧
    ConvexAnalysis.Specs.IsLowerSemicontinuous
      (fun u : WeakSpace ℝ (W1pZero Ω 1 p) =>
        (J ((toWeakSpace ℝ (W1pZero Ω 1 p)).symm u) : WithTop ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u,
      a₀ * ‖gradientMap Ω p u‖ ^ p.real - C * ‖gradientMap Ω p u‖ -
        (∫ x, ‖a x‖ ∂domainMeasure Ω) ≤ J u) ∧
    (∀ b : ℝ, ∃ R : ℝ, ∀ u, R ≤ ‖u‖ → b ≤ J u) ∧
    Existence.Specs.CoerciveOn (fun u => (J u : WithTop ℝ)) univ ∧
    (∃ b : ℝ, ∀ u, b ≤ J u) ∧
    (∃ u : W1pZero Ω 1 p, IsGLB (range J) (J u))

/-- All primal conclusions for the original integrand on the actual domain. -/
def DomainConclusion {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (F : Ω → Vector d → ℝ) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ)
    (a₀ : ℝ) (a : Ω → ℝ) : Prop :=
    let J := objective Ω p (extendFromDomain Ω F) ℓ
    (∀ u, Integrable (fun x : Ω => F x (gradientMap Ω p u x.val))
        (volume.comap Subtype.val) ∧
      J u = (∫ x : Ω, F x (gradientMap Ω p u x.val) ∂(volume.comap Subtype.val)) - ℓ u) ∧
    ConvexOn ℝ univ J ∧ Continuous J ∧
    ConvexAnalysis.Specs.IsLowerSemicontinuous
      (fun u : WeakSpace ℝ (W1pZero Ω 1 p) =>
        (J ((toWeakSpace ℝ (W1pZero Ω 1 p)).symm u) : WithTop ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u,
      a₀ * ‖gradientMap Ω p u‖ ^ p.real - C * ‖gradientMap Ω p u‖ -
        (∫ x : Ω, ‖a x‖ ∂(volume.comap Subtype.val)) ≤ J u) ∧
    (∀ b : ℝ, ∃ R : ℝ, ∀ u, R ≤ ‖u‖ → b ≤ J u) ∧
    Existence.Specs.CoerciveOn (fun u => (J u : WithTop ℝ)) univ ∧
    (∃ b : ℝ, ∀ u, b ≤ J u) ∧
    (∃ u : W1pZero Ω 1 p, IsGLB (range J) (J u))


/-- Original domain formulation. `J` agrees with the integral on Ω itself;
no data outside Ω are required. Base sections are a.e. measurable with respect
 to induced Lebesgue measure, equivalently measurable for its completion; they
 need not be Borel measurable. No common representative is assumed. -/
def Attainment : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent), 1 < p.real →
  ∀ (F : Ω → Vector d → ℝ) (ℓ : W1pZero Ω 1 p →L[ℝ] ℝ),
    ((∀ z, AEMeasurable (fun x => F x z) (volume.comap Subtype.val)) ∧
      ∀ᵐ x ∂(volume.comap Subtype.val), Continuous (F x)) →
  ∀ (a₀ a₁ : ℝ) (a : Ω → ℝ), 0 < a₀ → 0 ≤ a₁ →
    Integrable a (volume.comap Subtype.val) →
    (∀ᵐ x ∂(volume.comap Subtype.val), 0 ≤ a x) →
    (∀ᵐ x ∂(volume.comap Subtype.val), ∀ z,
      a₀ * ‖z‖ ^ p.real - a x ≤ F x z ∧ F x z ≤ a x + a₁ * ‖z‖ ^ p.real) →
    (∀ᵐ x ∂(volume.comap Subtype.val), ConvexOn ℝ univ (F x)) →
    DomainConclusion Ω p F ℓ a₀ a

end PrimalExpected
end VariationalNotes.Flux
