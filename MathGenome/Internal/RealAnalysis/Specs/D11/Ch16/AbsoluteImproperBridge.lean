import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.ProperIntegralEquality
import Mathlib.Order.Filter.CountablyGenerated

/-! Absolute improper integrals use the original closed-cell Darboux integral.
The measurable structure is completed Borel volume. An ambient function is
always extended by zero off its stated domain; no condition is imposed there.
`RCLike` includes both real and complex scalars. Its two real coordinates are
used only to reuse the established scalar Riemann convention. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
open Classical
namespace D11.Ch16.AbsoluteImproperBridge

abbrev lebesgueSpace := Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ)
abbrev lebesgueMeasure := Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ)

abbrev RealRiemann := Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue
abbrev realValue := @Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue

/-- For complex scalars this is exactly the established coordinate definition;
for real scalars the imaginary coordinate is the identically zero function. -/
def RiemannIntegrable {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (a b : ℝ) : Prop :=
  RealRiemann (fun x => RCLike.re (f x)) a b ∧
  RealRiemann (fun x => RCLike.im (f x)) a b

def riemannValue {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) {a b : ℝ}
    (h : RiemannIntegrable f a b) : 𝕜 :=
  (realValue (fun x => RCLike.re (f x)) h.1 : 𝕜) +
    (realValue (fun x => RCLike.im (f x)) h.2 : 𝕜) * RCLike.I

end D11.Ch16.AbsoluteImproperBridge

namespace Specs.D11.Ch16.AbsoluteImproperBridge
open _root_.D11.Ch16.AbsoluteImproperBridge

/-- The absolute value is genuinely Darboux integrable, before its value is used. -/
def norm_riemann : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (a b : ℝ),
    RiemannIntegrable f a b → RealRiemann (fun x => ‖f x‖) a b

end Specs.D11.Ch16.AbsoluteImproperBridge

namespace D11.Ch16.AbsoluteImproperBridge

/-- Values outside the proper ordered Riemann domain are immaterial to an
improper limit: every theorem below proves proper integrability eventually. -/
def properValue {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (a b : ℝ) : 𝕜 :=
  if h : RiemannIntegrable f a b then riemannValue f h else 0

def absoluteValue {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (a b : ℝ) : ℝ :=
  if h : RealRiemann (fun x => ‖f x‖) a b then realValue (fun x => ‖f x‖) h else 0

/-- Source integrability for the zero extension on the completed Lebesgue space. -/
abbrev InL1 {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) (S : Set ℝ) : Prop :=
  @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ℝ 𝕜 lebesgueSpace _ _ _
    lebesgueMeasure (S.indicator f)

/-- The complete conclusion for one independently filtered end. The absolute
limit is asserted even when it is infinity. Scalar values are used only under
`InL1`, which includes actual measurability and absolute integrability. -/
def Bridge {𝕜 ι : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) (S : Set ℝ) (u v : ι → ℝ) (l : Filter ι) : Prop :=
  @Measurable ℝ 𝕜 lebesgueSpace _ (S.indicator f) ∧
  Tendsto (fun i => ENNReal.ofReal (absoluteValue f (u i) (v i))) l
    (𝓝 (∫⁻ x in S, ENNReal.ofReal ‖f x‖ ∂lebesgueMeasure)) ∧
  ((∃ A : ℝ, Tendsto (fun i => absoluteValue f (u i) (v i)) l (𝓝 A)) ↔ InL1 f S) ∧
  (∀ h : InL1 f S,
    Tendsto (fun i => properValue f (u i) (v i)) l
      (𝓝 (@Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value ℝ 𝕜
        lebesgueSpace _ _ _ lebesgueMeasure (S.indicator f) h)))

end D11.Ch16.AbsoluteImproperBridge

namespace Specs.D11.Ch16.AbsoluteImproperBridge
open _root_.D11.Ch16.AbsoluteImproperBridge

/-- General compact truncations. Eventual hypotheses allow the actual endpoint
variable, without assuming proper integrability at a singular endpoint. -/
def exhaustion_bridge : Prop :=
  ∀ {𝕜 ι : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) (S : Set ℝ) (u v : ι → ℝ) (l : Filter ι)
    [l.NeBot] [l.IsCountablyGenerated],
    MeasurableSet[lebesgueSpace] S →
    (∀ᶠ i in l, RiemannIntegrable f (u i) (v i) ∧ Icc (u i) (v i) ⊆ S) →
    (∀ x ∈ S, ∀ᶠ i in l, x ∈ Icc (u i) (v i)) → Bridge f S u v l

/-- The stated half-line: `[a,R]` for every `R ≥ a`, with an unrestricted real
endpoint tending to positive infinity. -/
def right_infinite : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) (a : ℝ),
    (∀ R ≥ a, RiemannIntegrable f a R) →
    Bridge f (Ici a) (fun _ => a) id atTop

/-- The separate negative-infinity end, oriented from the moving endpoint to b. -/
def left_infinite : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) (b : ℝ),
    (∀ r ≤ b, RiemannIntegrable f r b) →
    Bridge f (Iic b) id (fun _ => b) atBot

/-- A finite singular lower endpoint, with no value or regularity required at a. -/
def left_singular : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) (a b : ℝ), a < b →
    (∀ r ∈ Ioc a b, RiemannIntegrable f r b) →
    Bridge f (Ioc a b) id (fun _ => b) (𝓝[>] a)

/-- A finite singular upper endpoint, with no value or regularity required at b. -/
def right_singular : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) (a b : ℝ), a < b →
    (∀ R ∈ Ico a b, RiemannIntegrable f a R) →
    Bridge f (Ico a b) (fun _ => a) id (𝓝[<] b)

end Specs.D11.Ch16.AbsoluteImproperBridge

namespace D11.Ch16.AbsoluteImproperBridge

/-- `none` denotes the infinite endpoint of the indicated side; `some a`
denotes a finite singular endpoint. Thus the four choices below cover the
whole line, both open half-lines, and a bounded open interval. -/
def leftDomain (a : Option ℝ) (c : ℝ) : Set ℝ :=
  match a with
  | none => Iic c
  | some a => Ioc a c

def rightDomain (b : Option ℝ) (c : ℝ) : Set ℝ :=
  match b with
  | none => Ici c
  | some b => Ico c b

def leftFilter (a : Option ℝ) : Filter ℝ :=
  match a with
  | none => atBot
  | some a => 𝓝[>] a

def rightFilter (b : Option ℝ) : Filter ℝ :=
  match b with
  | none => atTop
  | some b => 𝓝[<] b

def improperDomain (a b : Option ℝ) : Set ℝ :=
  {x | (match a with | none => True | some a => a < x) ∧
    (match b with | none => True | some b => x < b)}

end D11.Ch16.AbsoluteImproperBridge

namespace Specs.D11.Ch16.AbsoluteImproperBridge
open _root_.D11.Ch16.AbsoluteImproperBridge

/-- All improper endpoints are handled separately, including mixed finite and
infinite endpoints. In particular the equivalence requires BOTH absolute
one-sided limits, and the scalar value is the sum of the two independent
one-sided values. No principal-value condition appears. -/
def two_sided : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : ℝ → 𝕜) (a b : Option ℝ) (c : ℝ), c ∈ improperDomain a b →
    (∀ u v : ℝ, u ≤ v → Icc u v ⊆ improperDomain a b → RiemannIntegrable f u v) →
    let L := leftDomain a c
    let R := rightDomain b c
    let S := improperDomain a b
    Bridge f L id (fun _ => c) (leftFilter a) ∧
    Bridge f R (fun _ => c) id (rightFilter b) ∧
    @Measurable ℝ 𝕜 lebesgueSpace _ (S.indicator f) ∧
    (∫⁻ x in S, ENNReal.ofReal ‖f x‖ ∂lebesgueMeasure) =
      (∫⁻ x in L, ENNReal.ofReal ‖f x‖ ∂lebesgueMeasure) +
      (∫⁻ x in R, ENNReal.ofReal ‖f x‖ ∂lebesgueMeasure) ∧
    (InL1 f S ↔
      (∃ A : ℝ, Tendsto (fun r => absoluteValue f r c) (leftFilter a) (𝓝 A)) ∧
      (∃ B : ℝ, Tendsto (fun r => absoluteValue f c r) (rightFilter b) (𝓝 B))) ∧
    (∀ h : InL1 f S, ∃ V W : 𝕜,
      Tendsto (fun r => properValue f r c) (leftFilter a) (𝓝 V) ∧
      Tendsto (fun r => properValue f c r) (rightFilter b) (𝓝 W) ∧
      @Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value ℝ 𝕜 lebesgueSpace _ _ _
        lebesgueMeasure (S.indicator f) h = V + W)

/-- These input comparisons make explicit that the general coordinate
formulation has precisely the original real and complex Riemann hypotheses. -/
def real_input : Prop := ∀ (f : ℝ → ℝ) (a b : ℝ),
  RiemannIntegrable f a b ↔ RealRiemann f a b

def real_value : Prop := ∀ (f : ℝ → ℝ) (a b : ℝ) (h : RealRiemann f a b),
  properValue f a b = realValue f h

def complex_input : Prop := ∀ (f : ℝ → ℂ) (a b : ℝ),
  RiemannIntegrable f a b ↔
    Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegrableValue f a b

def complex_value : Prop := ∀ (f : ℝ → ℂ) (a b : ℝ)
    (h : Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegrableValue f a b),
  properValue f a b = Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue f h

end Specs.D11.Ch16.AbsoluteImproperBridge
