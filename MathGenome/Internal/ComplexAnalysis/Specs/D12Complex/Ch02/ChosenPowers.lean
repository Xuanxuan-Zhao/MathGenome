import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.PrincipalLogarithm

/-!
Independent specification for paper.tex:457–469, `d12:02-04-powers`.
Powers retain their chosen logarithm. The principal power uses the canonical
polar logarithm and factorial-series exponential from the upstream Specs.
Its holomorphy and derivative assertions are restricted to the principal slit
plane. The branch-change identities hold for arbitrary logarithm representatives
(indeed, for any functions related by the stated shift).
-/

noncomputable section

namespace D12Complex

/-- The power defined using a specified logarithm representative `L`. -/
def powerWithLog (L : ℂ → ℂ) (α z : ℂ) : ℂ := E (α * L z)

/-- Complex power for the principal logarithm, used on `PrincipalSlitPlane`. -/
def principalPower (α z : ℂ) : ℂ := powerWithLog PrincipalLog α z

end D12Complex

namespace Specs.D12Complex.Ch02.ChosenPowers

open _root_.D12Complex

def powerWithLog_type := (ℂ → ℂ) → ℂ → ℂ → ℂ
def powerWithLog_value : powerWithLog_type := fun L α z => E (α * L z)

def principalPower_type := ℂ → ℂ → ℂ
def principalPower_value : principalPower_type := fun α z => E (α * PrincipalLog z)

def holomorphicOn_principalPower_type : Prop :=
  ∀ α : ℂ, HolomorphicOn PrincipalSlitPlane (principalPower α)

def hasDerivAt_principalPower_type : Prop :=
  ∀ (α z : ℂ), z ∈ PrincipalSlitPlane →
    HasDerivAt (principalPower α) (α * principalPower (α - 1) z) z

def hasComplexDerivativeAt_principalPower_type : Prop :=
  ∀ (α z : ℂ), z ∈ PrincipalSlitPlane →
    HasComplexDerivativeAt (principalPower α) (α * principalPower (α - 1) z) z

def deriv_principalPower_type : Prop :=
  ∀ (α z : ℂ), z ∈ PrincipalSlitPlane →
    deriv (principalPower α) z = α * principalPower (α - 1) z

def principalPower_mul_type : Prop :=
  ∀ (α β z : ℂ), z ∈ PrincipalSlitPlane →
    principalPower α z * principalPower β z = principalPower (α + β) z

/-- Pointwise branch change; it applies at every point of any common domain. -/
def powerWithLog_change_type : Prop :=
  ∀ (L M : ℂ → ℂ) (α z : ℂ) (k : ℤ),
    M z = L z + (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ) →
    powerWithLog M α z =
      E ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ) * α) *
        powerWithLog L α z

/-- A single fixed integral shift of an entire chosen logarithm. -/
def powerWithLog_shift_type : Prop :=
  ∀ (L : ℂ → ℂ) (α z : ℂ) (k : ℤ),
    powerWithLog (fun w => L w + (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ))
      α z = E ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ) * α) *
        powerWithLog L α z

end Specs.D12Complex.Ch02.ChosenPowers
