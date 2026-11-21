import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.HilleYosida
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Lumer–Phillips, paper.tex 14784–14813. The domain is part of A.
No closedness is assumed. Hilbert inner products are linear in the second slot. -/
noncomputable section

namespace ExpandedFA.Semigroups.LumerPhillipsSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- λI − A on exactly D(A). -/
def shiftMap (A : Unbounded.Operator 𝕜 X X) (r : ℝ) : A.domain →ₗ[𝕜] X :=
  algebraMap ℝ 𝕜 r • A.domain.subtype - A.toFun

/-- Banach-space dissipativity, at every positive real parameter. -/
def Dissipative (A : Unbounded.Operator 𝕜 X X) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x : A.domain, r * ‖(x : X)‖ ≤ ‖shiftMap A r x‖

/-- The original full range condition; no inverse is assumed. -/
def FullRange (A : Unbounded.Operator 𝕜 X X) (r : ℝ) : Prop :=
  Function.Surjective (shiftMap A r)

variable [CompleteSpace X]

def Contractive (T : C0Semigroup 𝕜 X) : Prop := ∀ t, ‖T.operators t‖ ≤ 1

def Characterization : Prop := ∀ A : Unbounded.Operator 𝕜 X X,
  Dense (A.domain : Set X) →
  ((∃ T : C0Semigroup 𝕜 X, C0SemigroupSpec.generatorValue T = A ∧ Contractive T) ↔
    Dissipative A ∧ ∃ r : ℝ, 0 < r ∧ FullRange A r)

/-- Closedness and every positive range condition are consequences, even before
using domain density. We also expose the sharp resolvent bound. -/
def MaximalConsequences : Prop := ∀ A : Unbounded.Operator 𝕜 X X,
  Dissipative A → (∃ r : ℝ, 0 < r ∧ FullRange A r) →
    A.IsClosed ∧ ∀ r : ℝ, 0 < r →
      FullRange A r ∧
      algebraMap ℝ 𝕜 r ∈ Unbounded.OperatorDomainsSpec.resolventSetValue A ∧
      ‖Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ 𝕜 r) A‖ ≤ 1 / r

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

def HilbertCharacterization : Prop := ∀ A : Unbounded.Operator 𝕜 H H,
  Dissipative A ↔ ∀ x : A.domain, RCLike.re (inner 𝕜 (x : H) (A x)) ≤ 0

set_option linter.checkUnivs false

def CharacterizationExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  Characterization (𝕜 := 𝕜) (X := X)

def MaximalConsequencesExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  MaximalConsequences (𝕜 := 𝕜) (X := X)

def HilbertCharacterizationExpected : Prop := ∀ {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
  HilbertCharacterization (𝕜 := 𝕜) (H := H)

end ExpandedFA.Semigroups.LumerPhillipsSpec
