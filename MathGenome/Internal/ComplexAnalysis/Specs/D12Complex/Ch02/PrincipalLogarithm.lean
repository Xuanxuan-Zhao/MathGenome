import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
Independent specification for the slit-logarithm part of paper.tex:427–455.
The continuous-logarithm obstruction and chosen powers have separate goals.
The removed set is literally the image of the nonpositive real half-line;
the strip has strict boundaries. All functions are total representatives,
with the logarithm assertions restricted to the slit plane.
-/

noncomputable section

namespace D12Complex

/-- The complex plane with the nonpositive real ray removed, including zero. -/
def PrincipalSlitPlane : Set ℂ :=
  (Complex.ofReal '' Set.Iic (0 : ℝ))ᶜ

/-- The open strip of imaginary parts strictly between minus pi and pi. -/
def PrincipalStrip : Set ℂ := {w | |w.im| < Real.pi}

/-- The polar formula for the principal logarithm, used on `PrincipalSlitPlane`. -/
def PrincipalLog (z : ℂ) : ℂ :=
  (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I

end D12Complex

namespace Specs.D12Complex.Ch02.PrincipalLogarithm

open _root_.D12Complex

def PrincipalSlitPlane_type := Set ℂ
def PrincipalSlitPlane_value : PrincipalSlitPlane_type :=
  show Set ℂ from (Complex.ofReal '' Set.Iic (0 : ℝ))ᶜ

def PrincipalStrip_type := Set ℂ
def PrincipalStrip_value : PrincipalStrip_type := {w | |w.im| < Real.pi}

def PrincipalLog_type := ℂ → ℂ
def PrincipalLog_value : PrincipalLog_type :=
  fun z => (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I

def principalSlitPlane_eq_slitPlane_type : Prop :=
  PrincipalSlitPlane = Complex.slitPlane

def mem_principalSlitPlane_iff_type : Prop :=
  ∀ z : ℂ, z ∈ PrincipalSlitPlane ↔ 0 < z.re ∨ z.im ≠ 0

def principalSlitPlane_ne_zero_type : Prop :=
  ∀ z ∈ PrincipalSlitPlane, z ≠ 0

def isOpen_principalSlitPlane_type : Prop := IsOpen PrincipalSlitPlane

def mem_principalStrip_iff_type : Prop :=
  ∀ w : ℂ, w ∈ PrincipalStrip ↔ -Real.pi < w.im ∧ w.im < Real.pi

def isOpen_principalStrip_type : Prop := IsOpen PrincipalStrip

def principalArg_bounds_type : Prop :=
  ∀ z ∈ PrincipalSlitPlane, -Real.pi < Complex.arg z ∧ Complex.arg z < Real.pi

def principalLog_eq_log_type : Prop :=
  ∀ z ∈ PrincipalSlitPlane, PrincipalLog z = Complex.log z

def principalLog_parts_type : Prop :=
  ∀ z ∈ PrincipalSlitPlane,
    (PrincipalLog z).re = Real.log ‖z‖ ∧ (PrincipalLog z).im = Complex.arg z

def hasDerivAt_principalLog_type : Prop :=
  ∀ z ∈ PrincipalSlitPlane, HasDerivAt PrincipalLog (1 / z) z

def hasComplexDerivativeAt_principalLog_type : Prop :=
  ∀ z ∈ PrincipalSlitPlane, HasComplexDerivativeAt PrincipalLog (1 / z) z

def deriv_principalLog_type : Prop :=
  ∀ z ∈ PrincipalSlitPlane, deriv PrincipalLog z = 1 / z

def holomorphicOn_principalLog_type : Prop :=
  HolomorphicOn PrincipalSlitPlane PrincipalLog

def E_principalLog_type : Prop :=
  ∀ z ∈ PrincipalSlitPlane, E (PrincipalLog z) = z

def principalLog_one_type : Prop := PrincipalLog 1 = 0

def principalLog_mapsTo_type : Prop :=
  Set.MapsTo PrincipalLog PrincipalSlitPlane PrincipalStrip

def E_mapsTo_principalStrip_type : Prop :=
  Set.MapsTo E PrincipalStrip PrincipalSlitPlane

def principalLog_E_type : Prop :=
  ∀ w ∈ PrincipalStrip, PrincipalLog (E w) = w

/-- Both holomorphy statements, both range inclusions, and both inverse laws. -/
def principalLog_biholomorphicPair_type : Prop :=
  BiholomorphicPair PrincipalSlitPlane PrincipalStrip PrincipalLog E

def principalLog_bijOn_type : Prop :=
  Set.BijOn PrincipalLog PrincipalSlitPlane PrincipalStrip

def E_bijOn_principalStrip_type : Prop :=
  Set.BijOn E PrincipalStrip PrincipalSlitPlane

end Specs.D12Complex.Ch02.PrincipalLogarithm
