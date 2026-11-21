import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicFoundation

/-! Odd reflection in paper.tex:2597–2603. The half-disk is open and
its diameter is open relative to the real axis. No data are imposed on the
outer semicircle, including its endpoints. -/
noncomputable section
open scoped ComplexConjugate
open Complex Metric Set

namespace Specs.D12Complex.Ch13.HarmonicReflection
open _root_.D12Complex

def oddReflection_type := (ℂ → ℝ) → ℂ → ℝ

def oddReflection_value : oddReflection_type := fun u z =>
  if 0 < z.im then u z else if z.im < 0 then -u (conj z) else 0

def harmonic_oddReflection_type : Prop :=
  ∀ (R : ℝ) (u : ℂ → ℝ), 0 < R →
    HarmonicOn {z : ℂ | ‖z‖ < R ∧ 0 < z.im} u →
    ContinuousOn u {z : ℂ | ‖z‖ < R ∧ 0 ≤ z.im} →
    (∀ z : ℂ, ‖z‖ < R → z.im = 0 → u z = 0) →
    HarmonicOn (ball 0 R) (oddReflection_value u)

/-- Arbitrary center and oriented diameter, with a nonzero complex direction.
The coordinates `(z-a)/c` identify the actual half-disk and its open diameter. -/
def harmonic_oddReflection_affine_type : Prop :=
  ∀ (a c : ℂ) (R : ℝ) (u : ℂ → ℝ), c ≠ 0 → 0 < R →
    HarmonicOn {z : ℂ | ‖(z-a)/c‖ < R ∧ 0 < ((z-a)/c).im} u →
    ContinuousOn u {z : ℂ | ‖(z-a)/c‖ < R ∧ 0 ≤ ((z-a)/c).im} →
    (∀ z : ℂ, ‖(z-a)/c‖ < R → ((z-a)/c).im = 0 → u z = 0) →
    HarmonicOn {z : ℂ | ‖(z-a)/c‖ < R}
      (fun z => if 0 < ((z-a)/c).im then u z
        else if ((z-a)/c).im < 0 then -u (a + c * conj ((z-a)/c)) else 0)

end Specs.D12Complex.Ch13.HarmonicReflection
