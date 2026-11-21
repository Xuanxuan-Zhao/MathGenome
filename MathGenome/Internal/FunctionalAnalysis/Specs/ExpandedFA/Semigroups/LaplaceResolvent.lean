import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent statements for the Laplace part of `fa2:p3:semigroup-basics`,
paper.tex 14449–14457. The field is the original real or complex scalar field.
In particular a real space uses real spectral parameters. Powers are indexed
by `n + 1`, so that every positive integer is covered, including the first power.
The integral is a vector Bochner integral; no operator-norm measurability is assumed.
-/

noncomputable section
open MeasureTheory Set

namespace ExpandedFA.Semigroups.LaplaceResolventSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- `exp (-ζ t)` over the original scalar field. -/
def kernel (ζ : 𝕜) (t : ℝ) : 𝕜 := NormedSpace.exp (-t • ζ)

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

def orbit (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (x : X) (t : ℝ) : X :=
  kernel ζ t • T.operators t.toNNReal x

/-- Normalized moment, with `n = m - 1` for the paper's positive power `m`. -/
def moment (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (n : ℕ) (x : X) : X :=
  ((n.factorial : ℝ)⁻¹) • ∫ t : ℝ in Ioi 0, t ^ n • orbit T ζ x t

def Integrability : Prop := ∀ (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜),
  C0SemigroupSpec.exponentialBoundValue T M ω → ω < RCLike.re ζ →
  ∀ (n : ℕ) (x : X), IntegrableOn (fun t : ℝ => t ^ n • orbit T ζ x t) (Ioi 0)

def MomentBound : Prop := ∀ (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜),
  C0SemigroupSpec.exponentialBoundValue T M ω → ω < RCLike.re ζ →
  ∀ (n : ℕ) (x : X), ‖moment T ζ n x‖ ≤ M / (RCLike.re ζ - ω) ^ (n + 1) * ‖x‖

/-- Existence of an actual bounded inverse on precisely the canonical derivative
domain. The structure fields supply both inverse identities, not an assumed
resolvent membership or a formal inverse expression. -/
def LaplaceInverse : Prop := ∀ (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜),
  C0SemigroupSpec.exponentialBoundValue T M ω → ω < RCLike.re ζ →
  ∃ R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ,
    ∀ x : X, R.inverse x = ∫ t : ℝ in Ioi 0, orbit T ζ x t

/-- The formula and the sharp common-M bound for every positive power, for any
bounded two-sided inverse. This also ensures independence of a chosen inverse. -/
def ResolventPowers : Prop := ∀ (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜),
  C0SemigroupSpec.exponentialBoundValue T M ω → ω < RCLike.re ζ →
  ∀ R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ,
    ∀ n : ℕ, (∀ x : X, (R.inverse ^ (n + 1)) x = moment T ζ n x) ∧
      ‖R.inverse ^ (n + 1)‖ ≤ M / (RCLike.re ζ - ω) ^ (n + 1)

/-- The same conclusions for the canonical resolvent from the shared operator
interface, including membership in its resolvent set. -/
def CanonicalResolvent : Prop := ∀ (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜),
  C0SemigroupSpec.exponentialBoundValue T M ω → ω < RCLike.re ζ →
  let A := C0SemigroupSpec.generatorValue T
  ζ ∈ Unbounded.OperatorDomainsSpec.resolventSetValue A ∧
    (∀ x : X, Unbounded.OperatorDomainsSpec.resolventValue ζ A x =
      ∫ t : ℝ in Ioi 0, orbit T ζ x t) ∧
    ∀ n : ℕ,
      (∀ x : X, (Unbounded.OperatorDomainsSpec.resolventValue ζ A ^ (n + 1)) x =
        moment T ζ n x) ∧
      ‖Unbounded.OperatorDomainsSpec.resolventValue ζ A ^ (n + 1)‖ ≤
        M / (RCLike.re ζ - ω) ^ (n + 1)

def IntegrabilityExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  Integrability (𝕜 := 𝕜) (X := X)

def MomentBoundExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  MomentBound (𝕜 := 𝕜) (X := X)

def LaplaceInverseExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  LaplaceInverse (𝕜 := 𝕜) (X := X)

def ResolventPowersExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ResolventPowers (𝕜 := 𝕜) (X := X)

def CanonicalResolventExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  CanonicalResolvent (𝕜 := 𝕜) (X := X)

end ExpandedFA.Semigroups.LaplaceResolventSpec
