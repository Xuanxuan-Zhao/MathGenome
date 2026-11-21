import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.ScalarSphereBridge
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.TriplesCrossRatio

/-!
The essentiality bridge in paper.tex:4340–4345 (d12:23-06).
The extension agrees on the entire original punctured disk. The original
representative's value at the puncture is unrestricted. Sphere holomorphy
uses the canonical finite and reciprocal charts, including at poles.
-/
noncomputable section
open Set
namespace Specs.D12Complex.Ch23.ThreeOmissionsPunctureExtension
open _root_.D12Complex _root_.D12Complex.Mobius

/-- Extension for holomorphic sphere maps; this also allows sphere constants. -/
def three_omissions_puncture_extension_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → RiemannSphere) (p q r : RiemannSphere),
    0 < R → PlaneSphereHolomorphicOn (puncturedDisk a R) f →
    p ≠ q → p ≠ r → q ≠ r →
    (∀ z ∈ puncturedDisk a R, f z ≠ p) →
    (∀ z ∈ puncturedDisk a R, f z ≠ q) →
    (∀ z ∈ puncturedDisk a R, f z ≠ r) →
    ∃ F : ℂ → RiemannSphere, PlaneSphereHolomorphicOn (Metric.ball a R) F ∧
      EqOn F f (puncturedDisk a R)

/-- The assertion for actual scalar meromorphic functions, retaining pole values. -/
def meromorphic_three_omissions_puncture_extension_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → RiemannSphere) (p q r : RiemannSphere),
    0 < R → ScalarMeromorphicOn (puncturedDisk a R) f →
    p ≠ q → p ≠ r → q ≠ r →
    (∀ z ∈ puncturedDisk a R, f z ≠ p) →
    (∀ z ∈ puncturedDisk a R, f z ≠ q) →
    (∀ z ∈ puncturedDisk a R, f z ≠ r) →
    ∃ F : ℂ → RiemannSphere, PlaneSphereHolomorphicOn (Metric.ball a R) F ∧
      EqOn F f (puncturedDisk a R)

/-- Normalization and its inverse preserve extendibility, hence also its negation
(an essential puncture of a holomorphic sphere map). No omitted-value assumption
is needed for this coordinate-invariance statement. -/
def mobius_puncture_extension_iff_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → RiemannSphere) (M : Coefficients),
    Regular M →
    ((∃ F : ℂ → RiemannSphere, PlaneSphereHolomorphicOn (Metric.ball a R) F ∧
        EqOn F f (puncturedDisk a R)) ↔
      ∃ G : ℂ → RiemannSphere, PlaneSphereHolomorphicOn (Metric.ball a R) G ∧
        EqOn G (fun z => mobiusMap M (f z)) (puncturedDisk a R))

end Specs.D12Complex.Ch23.ThreeOmissionsPunctureExtension
