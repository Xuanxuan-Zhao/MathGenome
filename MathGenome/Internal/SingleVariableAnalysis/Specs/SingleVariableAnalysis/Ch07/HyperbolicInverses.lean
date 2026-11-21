import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.Hyperbolic
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogConstruction

/-!
Principal inverse part of K03.07.hyperbolic (paper.tex:1769–1792).
The formulas use the shared inverse of the factorial-series exponential.
Ambient functions are total, but assertions for arcosh and artanh are restricted
to their mathematical domains. The square-root reciprocals denote the displayed
negative half powers on the positive radicands of the interior domains.
The infinite right derivative is a limit of actual endpoint secant slopes.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.HyperbolicInverses

open Set Filter
open scoped Topology
open Hyperbolic LogConstruction

def realArsinhType : Type := ℝ → ℝ
def realArsinhValue : realArsinhType :=
  fun y => seriesLogValue (y + Real.sqrt (y ^ 2 + 1))
def realArcoshType : Type := ℝ → ℝ
def realArcoshValue : realArcoshType :=
  fun y => seriesLogValue (y + Real.sqrt (y ^ 2 - 1))
def realArtanhType : Type := ℝ → ℝ
def realArtanhValue : realArtanhType :=
  fun y => (1 / 2) * seriesLogValue ((1 + y) / (1 - y))

def sinhArsinh : Prop := ∀ y, realSinhValue (realArsinhValue y) = y
def arsinhSinh : Prop := ∀ x, realArsinhValue (realSinhValue x) = x
def coshArcosh : Prop := ∀ y, 1 ≤ y → realCoshValue (realArcoshValue y) = y
def arcoshCosh : Prop := ∀ x, 0 ≤ x → realArcoshValue (realCoshValue x) = x
def tanhArtanh : Prop := ∀ y, |y| < 1 → realTanhValue (realArtanhValue y) = y
def artanhTanh : Prop := ∀ x, realArtanhValue (realTanhValue x) = x

def arsinhRange : Prop := range realArsinhValue = univ
def arcoshRange : Prop := realArcoshValue '' Ici 1 = Ici 0
def artanhRange : Prop := realArtanhValue '' {y | |y| < 1} = univ

def arsinhDerivative : Prop :=
  ∀ y, HasDerivAt realArsinhValue (1 / Real.sqrt (1 + y ^ 2)) y
def arcoshDerivative : Prop :=
  ∀ y, 1 < y → HasDerivAt realArcoshValue (1 / Real.sqrt (y ^ 2 - 1)) y
def artanhDerivative : Prop :=
  ∀ y, |y| < 1 → HasDerivAt realArtanhValue (1 / (1 - y ^ 2)) y

def arsinhContinuity : Prop := Continuous realArsinhValue
def arcoshContinuity : Prop := ContinuousOn realArcoshValue (Ici 1)
def artanhContinuity : Prop := ContinuousOn realArtanhValue {y | |y| < 1}
def arcoshAtOne : Prop := realArcoshValue 1 = 0
def arcoshInfiniteRightDerivative : Prop :=
  Tendsto (fun y => (realArcoshValue y - realArcoshValue 1) / (y - 1))
    (𝓝[>] 1) atTop
def arcoshNoFiniteRightDerivative : Prop :=
  ∀ d : ℝ, ¬ HasDerivWithinAt realArcoshValue d (Ici 1) 1

end Specs.SingleVariableAnalysis.Ch07.HyperbolicInverses
