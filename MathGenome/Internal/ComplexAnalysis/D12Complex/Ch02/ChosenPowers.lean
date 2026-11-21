import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.ChosenPowers
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.PrincipalLogarithm
import Mathlib.Tactic.Ring

/-!
Powers with a chosen logarithm (paper.tex:457–469).
The chain rule and the principal-logarithm inverse identity give the
derivative on the exact slit plane. Exponential addition gives exponent
addition and the change under an integral logarithm shift.
-/

noncomputable section

namespace D12Complex.ChosenPowers

abbrev powerWithLog : Specs.D12Complex.Ch02.ChosenPowers.powerWithLog_type :=
  _root_.D12Complex.powerWithLog

abbrev principalPower : Specs.D12Complex.Ch02.ChosenPowers.principalPower_type :=
  _root_.D12Complex.principalPower

private theorem principalPower_sub_one_mul (α z : ℂ) (hz : z ∈ PrincipalSlitPlane) :
    principalPower (α - 1) z * z = principalPower α z := by
  change E ((α - 1) * PrincipalLog z) * z = E (α * PrincipalLog z)
  calc
    _ = E ((α - 1) * PrincipalLog z) * E (PrincipalLog z) := by
      rw [PrincipalLogarithm.E_principalLog z hz]
    _ = E ((α - 1) * PrincipalLog z + PrincipalLog z) :=
      (Exponential.E_add _ _).symm
    _ = E (α * PrincipalLog z) := by congr 1; ring

theorem hasDerivAt_principalPower :
    Specs.D12Complex.Ch02.ChosenPowers.hasDerivAt_principalPower_type := by
  intro α z hz
  have he : HasDerivAt E (E (α * PrincipalLog z)) (α * PrincipalLog z) :=
    Exponential.hasDerivAt_E _
  have hl : HasDerivAt PrincipalLog (1 / z) z :=
    PrincipalLogarithm.hasDerivAt_principalLog z hz
  have h : HasDerivAt (fun w => E (α * PrincipalLog w))
      (E (α * PrincipalLog z) * (α * (1 / z))) z := by
    exact he.comp z (hl.const_mul α)
  have hvalue : E (α * PrincipalLog z) * (α * (1 / z)) =
      α * principalPower (α - 1) z := by
    change principalPower α z * (α * (1 / z)) = _
    rw [← principalPower_sub_one_mul α z hz]
    have hne := PrincipalLogarithm.principalSlitPlane_ne_zero z hz
    calc
      principalPower (α - 1) z * z * (α * (1 / z)) =
          α * principalPower (α - 1) z * (z * (1 / z)) := by ring
      _ = α * principalPower (α - 1) z := by rw [mul_one_div_cancel hne, mul_one]
  rw [hvalue] at h
  exact h

theorem hasComplexDerivativeAt_principalPower :
    Specs.D12Complex.Ch02.ChosenPowers.hasComplexDerivativeAt_principalPower_type := by
  intro α z hz
  exact (hasComplexDerivativeAt_iff _ _ _).mpr (hasDerivAt_principalPower α z hz)

theorem deriv_principalPower :
    Specs.D12Complex.Ch02.ChosenPowers.deriv_principalPower_type := by
  intro α z hz
  exact (hasDerivAt_principalPower α z hz).deriv

theorem holomorphicOn_principalPower :
    Specs.D12Complex.Ch02.ChosenPowers.holomorphicOn_principalPower_type := by
  intro α
  exact ⟨PrincipalLogarithm.isOpen_principalSlitPlane,
    fun z hz => (hasDerivAt_principalPower α z hz).differentiableAt⟩

theorem principalPower_mul :
    Specs.D12Complex.Ch02.ChosenPowers.principalPower_mul_type := by
  intro α β z _
  change E (α * PrincipalLog z) * E (β * PrincipalLog z) = E ((α + β) * PrincipalLog z)
  rw [← Exponential.E_add, add_mul]

theorem powerWithLog_change :
    Specs.D12Complex.Ch02.ChosenPowers.powerWithLog_change_type := by
  intro L M α z k hM
  change E (α * M z) = E (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * α) * E (α * L z)
  rw [hM, ← Exponential.E_add]
  congr 1
  ring

theorem powerWithLog_shift :
    Specs.D12Complex.Ch02.ChosenPowers.powerWithLog_shift_type := by
  intro L α z k
  exact powerWithLog_change L _ α z k rfl

end D12Complex.ChosenPowers
