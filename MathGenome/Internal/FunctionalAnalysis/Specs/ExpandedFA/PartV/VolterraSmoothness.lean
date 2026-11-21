import Specs.ExpandedFA.PartV.VolterraResolventKernel
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Independent statements of paper.tex fa2:p5:volterra-regularity (21946–21969). All derivatives are real
parameter derivatives in the displayed Banach norms. Constant extensions are
only representatives for within derivatives; no derivative outside the interval
or the admissible triangle sections is assumed. -/
noncomputable section
open Set MeasureTheory
namespace ExpandedFA.PartV

/-- Constant extension of an interval function, used only to state derivatives
within the closed interval (ordinary derivatives in its interior). -/
def volterraIntervalExtension {E : Type*} [TopologicalSpace E] {a b : ℝ} (hab : a ≤ b)
    (f : C(VolterraInterval a b, E)) (t : ℝ) : E :=
  f (Set.projIcc a b hab t)

/-- Extend a section in the first variable by clamping it to its own admissible
interval `[s,b]`. This agrees with the original kernel on that section. -/
def volterraKernelSection {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {a b : ℝ}
    (k : C(volterraTriangle a b, E →L[𝕜] E))
    (s : VolterraInterval a b) (t : ℝ) : E →L[𝕜] E :=
  k ⟨(max (s : ℝ) (min b t), s), s.property.1,
    le_max_left _ _, max_le s.property.2 (min_le_left _ _)⟩

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance volterraDifferentiationSpecRealSpace : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance volterraDifferentiationSpecRealOperatorSpace : NormedSpace ℝ (E →L[𝕜] E) :=
  NormedSpace.restrictScalars ℝ 𝕜 (E →L[𝕜] E)

/-- The supplied continuous kernel `dk` is the actual operator norm derivative
in the first variable, within every admissible section, including endpoints. -/
def VolterraKernelHasDerivative {a b : ℝ}
    (k dk : C(volterraTriangle a b, E →L[𝕜] E)) : Prop :=
  ∀ (s : VolterraInterval a b) (t : ℝ) (ht : t ∈ Icc (s : ℝ) b),
    HasDerivWithinAt (volterraKernelSection k s)
      (dk ⟨(t, s), s.property.1, ht.1, ht.2⟩) (Icc (s : ℝ) b) t

/-- A continuous displayed derivative, with actual within derivatives at all
points of the interval. This is the closed interval meaning of `C¹`. -/
def VolterraHasIntervalDerivative {a b : ℝ} (hab : a ≤ b)
    (f f' : C(VolterraInterval a b, E)) : Prop :=
  ∀ t : VolterraInterval a b,
    HasDerivWithinAt (volterraIntervalExtension hab f) (f' t) (Icc a b) t

/-- The claimed derivative of `Vu`. -/
def volterraDerivativeValue {a b : ℝ} (hab : a ≤ b)
    (k dk : C(volterraTriangle a b, E →L[𝕜] E))
    (u : C(VolterraInterval a b, E)) (t : VolterraInterval a b) : E :=
  k ⟨((t : ℝ), t), t.property.1, le_rfl, t.property.2⟩ (u t) +
    volterraIntegralValue hab dk u t

/-- Restrict an ambient operator kernel to the actual closed triangle. -/
def ambientVolterraKernel {a b : ℝ} (K : ℝ × ℝ → E →L[𝕜] E)
    (hK : ContinuousOn K (volterraTriangle a b)) :
    C(volterraTriangle a b, E →L[𝕜] E) :=
  ⟨fun p => K p, hK.domRestrict⟩

/-- First-variable partial derivative in the real parameter, in operator norm. -/
def volterraPartialFirst (K : ℝ × ℝ → E →L[𝕜] E) (p : ℝ × ℝ) : E →L[𝕜] E :=
  fderiv ℝ K p (1, 0)

namespace VolterraSmoothnessSpec

/-- Displaying a continuous within derivative is exactly native `C¹` on the
closed interval. This makes the regularity hypothesis applicable to every
`C¹` datum, without an extension regularity assumption. -/
def C1Identification : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (a b : ℝ) (hab : a < b) (f : C(VolterraInterval a b, E)),
  ContDiffOn ℝ 1 (volterraIntervalExtension hab.le f) (Icc a b) ↔
    ∃ f' : C(VolterraInterval a b, E),
      VolterraHasIntervalDerivative (𝕜 := 𝕜) hab.le f f'

/-- Leibniz rule for every continuous `u`, with continuous derivative, `C¹`
regularity, within endpoint derivatives and ordinary interior derivatives. -/
def LeibnizRule : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k dk : C(volterraTriangle a b, E →L[𝕜] E)),
  VolterraKernelHasDerivative k dk → ∀ u : C(VolterraInterval a b, E),
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  Continuous (volterraDerivativeValue hab k dk u) ∧
  ContDiffOn ℝ 1 (volterraIntervalExtension hab (V u)) (Icc a b) ∧
  (∀ t : VolterraInterval a b,
    HasDerivWithinAt (volterraIntervalExtension hab (V u))
      (volterraDerivativeValue hab k dk u t) (Icc a b) t) ∧
  (∀ (t : ℝ) (ht : t ∈ Ioo a b),
    HasDerivAt (volterraIntervalExtension hab (V u))
      (volterraDerivativeValue hab k dk u ⟨t, ht.1.le, ht.2.le⟩) t)

/-- The unique continuous solution for every parameter and every `C¹` datum is
`C¹`; the same continuous expression gives its within and interior derivatives.
The hypotheses require no regularity outside the original closed domains. -/
def SolutionRegularity : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k dk : C(volterraTriangle a b, E →L[𝕜] E)),
  VolterraKernelHasDerivative k dk → ∀ (lam : 𝕜)
    (f f' : C(VolterraInterval a b, E)),
  VolterraHasIntervalDerivative (𝕜 := 𝕜) hab f f' →
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  ∃ u : C(VolterraInterval a b, E),
    u - lam • V u = f ∧
    (∀ v : C(VolterraInterval a b, E), v - lam • V v = f → v = u) ∧
    ContDiffOn ℝ 1 (volterraIntervalExtension hab u) (Icc a b) ∧
    ∃ u' : C(VolterraInterval a b, E),
      VolterraHasIntervalDerivative (𝕜 := 𝕜) hab u u' ∧
      (∀ t : VolterraInterval a b,
        u' t = f' t + lam • k ⟨((t : ℝ), t), t.property.1, le_rfl, t.property.2⟩ (u t) +
          lam • volterraIntegralValue hab dk u t) ∧
      (∀ (t : ℝ) (ht : t ∈ Ioo a b),
        HasDerivAt (volterraIntervalExtension hab u)
          (u' ⟨t, ht.1.le, ht.2.le⟩) t)

end VolterraSmoothnessSpec
end
section ScalarKernel
variable {𝕜 : Type*} [RCLike 𝕜]

namespace VolterraSmoothnessSpec

/-- Scalar multiplication, as the continuous linear operator used by the
accepted Volterra construction. Its action is precisely `k(t,s) * u(s)`. -/
def scalarVolterraKernel {a b : ℝ} (k : ℝ × ℝ → 𝕜)
    (hk : ContinuousOn k (volterraTriangle a b)) :
    C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜) :=
  ⟨fun p => ContinuousLinearMap.lsmul 𝕜 𝕜 (k p),
    (ContinuousLinearMap.lsmul 𝕜 𝕜).continuous.comp hk.domRestrict⟩

end VolterraSmoothnessSpec

/-- A plane representative of a triangle function. This continuous clamp fixes
every triangle point; it is used only to state native within smoothness. -/
def volterraTriangleClamp {a b : ℝ} (hab : a ≤ b) (p : ℝ × ℝ) : volterraTriangle a b :=
  volterraRetraction (Set.projIcc a b hab p.1) p.2

/-- Scalar value of the accepted reduced resolvent kernel, with its exact
series normalization `k + λk₂ + λ²k₃ + ...`. -/
def scalarReducedResolventExtension {a b : ℝ} (hab : a ≤ b)
    (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) (lam : 𝕜) (p : ℝ × ℝ) : 𝕜 :=
  volterraReducedResolventKernel k lam (volterraTriangleClamp hab p) 1

/-- Scalar value of the accepted full kernel `λk + λ²k₂ + ...`. -/
def scalarResolventExtension {a b : ℝ} (hab : a ≤ b)
    (k : C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜)) (lam : 𝕜) (p : ℝ × ℝ) : 𝕜 :=
  volterraResolventKernel k lam (volterraTriangleClamp hab p) 1

/-- The actual scalar first partial derivative. -/
def scalarVolterraPartialFirst (k : ℝ × ℝ → 𝕜) (p : ℝ × ℝ) : 𝕜 :=
  fderiv ℝ k p (1, 0)

namespace VolterraSmoothnessSpec

/-- The complete second-kind regularity assertion for every finite m, both
scalar fields, every parameter, and the singleton as well as positive intervals.
The hypothesis is native C^m on an open neighborhood of the actual triangle. -/
def ScalarSolutionRegularity : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
  (a b : ℝ) (hab : a ≤ b) (m : ℕ) (U : Set (ℝ × ℝ)) (_hU : IsOpen U)
  (hsub : volterraTriangle a b ⊆ U) (k : ℝ × ℝ → 𝕜) (hk : ContDiffOn ℝ m k U)
  (lam : 𝕜) (f : C(VolterraInterval a b, 𝕜)),
  ContDiffOn ℝ m (volterraIntervalExtension hab f) (Icc a b) →
  let V := VolterraOperatorSpec.OperatorValue 𝕜 𝕜 a b hab
    (scalarVolterraKernel k (hk.continuousOn.mono hsub))
  ∃ u : C(VolterraInterval a b, 𝕜),
    u - lam • V u = f ∧
    (∀ v : C(VolterraInterval a b, 𝕜), v - lam • V v = f → v = u) ∧
    ContDiffOn ℝ m (volterraIntervalExtension hab u) (Icc a b)

/-- Joint smoothness assertion for both
actual scalar resolvent series. Derivatives and smoothness are within the
closed triangle, including its edges and corners. -/
def ScalarResolventRegularity : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
  (a b : ℝ) (hab : a ≤ b) (m : ℕ) (U : Set (ℝ × ℝ)) (_hU : IsOpen U)
  (hsub : volterraTriangle a b ⊆ U) (k : ℝ × ℝ → 𝕜) (hk : ContDiffOn ℝ m k U)
  (lam : 𝕜),
  let kop := scalarVolterraKernel k (hk.continuousOn.mono hsub)
  ContDiffOn ℝ m (scalarReducedResolventExtension hab kop lam) (volterraTriangle a b) ∧
  ContDiffOn ℝ m (scalarResolventExtension hab kop lam) (volterraTriangle a b)

/-- The source C¹ formula, including within derivatives at both endpoints.
At a=b these are within derivatives on a singleton, and no uniqueness of a
derivative is claimed. The integral has the actual scalar partial derivative. -/
def ScalarC1Formula : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
  (a b : ℝ) (hab : a ≤ b) (U : Set (ℝ × ℝ)) (_hU : IsOpen U)
  (hsub : volterraTriangle a b ⊆ U) (k : ℝ × ℝ → 𝕜) (hk : ContDiffOn ℝ 1 k U)
  (lam : 𝕜) (f u : C(VolterraInterval a b, 𝕜)),
  ContDiffOn ℝ 1 (volterraIntervalExtension hab f) (Icc a b) →
  u - lam • VolterraOperatorSpec.OperatorValue 𝕜 𝕜 a b hab
    (scalarVolterraKernel k (hk.continuousOn.mono hsub)) u = f →
  ∀ t : VolterraInterval a b,
    HasDerivWithinAt (volterraIntervalExtension hab u)
      (derivWithin (volterraIntervalExtension hab f) (Icc a b) t +
        lam * k (t, t) * u t + lam * ∫ s in a..(t : ℝ),
          scalarVolterraPartialFirst k ((t : ℝ), s) *
            volterraIntervalExtension hab u s) (Icc a b) t

end VolterraSmoothnessSpec
end ScalarKernel

end ExpandedFA.PartV
