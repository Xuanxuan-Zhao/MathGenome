import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory Set

namespace Specs.D13Unified.Ch20.PerronWeightedIntegrals
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Evolution in the Banach algebra of continuous endomorphisms. -/
def evolution (A : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E := NormedSpace.exp (t • A)

def kernel (A P : E →L[ℝ] E) (g : ℝ → E) (t s : ℝ) : E :=
  evolution A (t - s) (P (g s))

/-- Compact stable integral; for nonnegative t this equals the oriented integral. -/
def stableIntegral (A P : E →L[ℝ] E) (g : ℝ → E) (t : ℝ) : E :=
  ∫ s in Icc 0 t, kernel A P g t s

def unstableIntegral (A P : E →L[ℝ] E) (g : ℝ → E) (t : ℝ) : E :=
  ∫ s in Ici t, kernel A P g t s

def greenIntegral (A Ps Pu : E →L[ℝ] E) (g : ℝ → E) (t : ℝ) : E :=
  stableIntegral A Ps g t - unstableIntegral A Pu g t

def WeightedBound (β M : ℝ) (g : ℝ → E) : Prop :=
  ContinuousOn g (Ici 0) ∧ 0 ≤ M ∧ ∀ s, 0 ≤ s → Real.exp (β * s) * ‖g s‖ ≤ M

def StableDecay (A P : E →L[ℝ] E) (K α : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ‖(evolution A t).comp P‖ ≤ K * Real.exp (-α * t)

def UnstableDecay (A P : E →L[ℝ] E) (K α : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ‖(evolution A (-t)).comp P‖ ≤ K * Real.exp (-α * t)

def stableIntervalType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
  ∀ (A P : E →L[ℝ] E) (g : ℝ → E) (t : ℝ), 0 ≤ t →
    stableIntegral A P g t = ∫ s in 0..t, kernel A P g t s

def stableEstimateType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
  ∀ (A P : E →L[ℝ] E) (K α β M : ℝ), 1 ≤ K → 0 < β → β < α →
  StableDecay A P K α → ∀ g : ℝ → E, WeightedBound β M g → ∀ t, 0 ≤ t →
    IntegrableOn (kernel A P g t) (Icc 0 t) ∧
    Real.exp (β * t) * ‖stableIntegral A P g t‖ ≤ K * M / (α - β)

def unstableEstimateType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
  ∀ (A P : E →L[ℝ] E) (K α β M : ℝ), 1 ≤ K → 0 < β → β < α →
  UnstableDecay A P K α → ∀ g : ℝ → E, WeightedBound β M g → ∀ t, 0 ≤ t →
    IntegrableOn (kernel A P g t) (Ici t) ∧
    Real.exp (β * t) * ‖unstableIntegral A P g t‖ ≤ K * M / (α + β)

def continuityType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
  ∀ (A Ps Pu : E →L[ℝ] E) (K α β M : ℝ), 1 ≤ K → 0 < β → β < α →
  StableDecay A Ps K α → UnstableDecay A Pu K α → ∀ g : ℝ → E,
  WeightedBound β M g → ContinuousOn (stableIntegral A Ps g) (Ici 0) ∧
    ContinuousOn (unstableIntegral A Pu g) (Ici 0)

/-- Algebraic linearity on the vector space of paths with a finite weighted bound. -/
def linearityType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
  ∀ (A Ps Pu : E →L[ℝ] E) (K α β : ℝ), 1 ≤ K → 0 < β → β < α →
  StableDecay A Ps K α → UnstableDecay A Pu K α →
  ∀ (g h : ℝ → E) (M N : ℝ), WeightedBound β M g → WeightedBound β N h →
  ∀ (c d t : ℝ), 0 ≤ t →
    greenIntegral A Ps Pu (fun s => c • g s + d • h s) t =
      c • greenIntegral A Ps Pu g t + d • greenIntegral A Ps Pu h t

/-- The estimate for a difference forcing, needed by the nonlinear contraction. -/
def greenEstimateType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
  ∀ (A Ps Pu : E →L[ℝ] E) (K α β M : ℝ), 1 ≤ K → 0 < β → β < α →
  StableDecay A Ps K α → UnstableDecay A Pu K α → ∀ g : ℝ → E,
  WeightedBound β M g → ∀ t, 0 ≤ t →
    Real.exp (β * t) * ‖greenIntegral A Ps Pu g t‖ ≤
      K * M * ((α - β)⁻¹ + (α + β)⁻¹)
end Specs.D13Unified.Ch20.PerronWeightedIntegrals
