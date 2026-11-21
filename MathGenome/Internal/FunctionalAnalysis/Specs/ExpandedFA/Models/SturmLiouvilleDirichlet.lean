import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.OneDimensionalSobolev
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.ClosedNonnegativeForms
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! The Dirichlet part of paper.tex, `fa2:p3:sturm-liouville`.
The ambient L² space uses the accepted measure-preserving R¹ coordinates.
H¹, H² and H¹₀ are the actual upstream distributional graphs and closure.
Neither H² regularity nor the existence of a form operator is an input. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ExpandedFA.Models.SturmLiouvilleDirichlet
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.OneDimensional
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open ExpandedFA.Unbounded

/-- Exactly the coefficient and interval hypotheses in the source. Values of
p and q outside [a,b] are arbitrary and have no role. -/
structure Coefficients (a b : ℝ) where
  interval_nonempty : a < b
  p : ℝ → ℝ
  q : ℝ → ℝ
  p_C1 : ContDiffOn ℝ 1 p (Icc a b)
  q_continuous : ContinuousOn q (Icc a b)
  p₀ : ℝ
  p₀_pos : 0 < p₀
  p_lower : ∀ x ∈ Icc a b, p₀ ≤ p x

abbrev interval (a b : ℝ) : Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩
abbrev spatialInterval (a b : ℝ) := lineDomain (interval a b)
abbrev L2 (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) := DomainLp 𝕜 (spatialInterval a b) 2
abbrev H1 (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) := W1p 𝕜 (interval a b) 2
abbrev H2 (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) :=
  SpaceValue 𝕜 1 (spatialInterval a b) 2 2
abbrev H10 (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) :=
  ZeroSpaceValue 𝕜 1 (spatialInterval a b) 1 2 (by norm_num)

/-- The zeroth projection, as a linear map on the original graph. -/
def baseLM (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) : H1 𝕜 a b →ₗ[𝕜] L2 𝕜 a b where
  toFun := baseLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- H¹₀ as a submodule of L², not a replacement boundary predicate. -/
def dirichletFormDomain (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) : Submodule 𝕜 (L2 𝕜 a b) :=
  (H10 𝕜 a b).map (baseLM 𝕜 a b)

/-- The literal intersection H² ∩ H¹₀, viewed in L². -/
def StrongDomain {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (u : L2 𝕜 a b) : Prop :=
  (∃ w : H2 𝕜 a b, w.val (zeroIndex 1 2) = u) ∧
    u ∈ dirichletFormDomain 𝕜 a b

/-- Continuous coefficients on the compact interval give actual L∞ classes.
This lemma only constructs canonical coefficient data. -/
theorem continuous_coefficient_memLp {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b)) :
    MemLp (fun z : Domain 1 => (r (z 0) : 𝕜)) ∞
      (volume.restrict (spatialInterval a b : Set (Domain 1))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hr.norm
  have hm : AEStronglyMeasurable (fun z : Domain 1 => (r (z 0) : 𝕜))
      (volume.restrict (spatialInterval a b : Set (Domain 1))) := by
    apply ContinuousOn.aestronglyMeasurable _ (spatialInterval a b).isOpen.measurableSet
    apply (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.comp_continuousOn
    exact (hr.mono Ioo_subset_Icc_self).comp
      (continuous_apply (0 : Fin 1)).continuousOn (fun _ hz => hz)
  apply memLp_top_of_bound hm C
  filter_upwards [ae_restrict_mem (spatialInterval a b).isOpen.measurableSet] with z hz
  simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using hC (mem_image_of_mem (fun t => ‖r t‖)
    (Ioo_subset_Icc_self hz))

def coefficientLp {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b)) :
    DomainLp 𝕜 (spatialInterval a b) ∞ :=
  (continuous_coefficient_memLp r hr).toLp (fun z => (r (z 0) : 𝕜))

/-- Multiplication on the original L² classes, with no representative choices
in the output meaning. -/
def multiplier {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b)) : L2 𝕜 a b →L[𝕜] L2 𝕜 a b :=
  (ContinuousLinearMap.mul 𝕜 𝕜).holderL
    (volume.restrict (spatialInterval a b : Set (Domain 1))) ∞ 2 2 (coefficientLp r hr)

/-- The source form, conjugate-linear in the test and linear in the unknown.
Its integral formula is an independently checked target below. -/
def form {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (c : Coefficients a b)
    (v u : H1 𝕜 a b) : 𝕜 :=
  inner 𝕜 (derivativeLp v) (multiplier c.p c.p_C1.continuousOn (derivativeLp u)) +
    inner 𝕜 (baseLp v) (multiplier c.q c.q_continuous (baseLp u))

/-- Both domain and value of the form realization. No differential regularity
or solvability is assumed in this relation. -/
def FormRealization {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (c : Coefficients a b)
    (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)) : Prop :=
  ∀ u f, (u, f) ∈ A.graph ↔
    ∃ w : H10 𝕜 a b, baseLp w.val = u ∧
      ∀ v : H10 𝕜 a b, form c v.val w.val = inner 𝕜 (baseLp v.val) f

/-- Lu=−(pu′)′+qu, as an equality of scalar-linear distributions on (a,b).
Only the flux is differentiated; the coefficients need only their source
regularity. The main theorem separately establishes H² regularity. -/
def DifferentialAction {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (c : Coefficients a b)
    (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)) : Prop :=
  ∀ u : A.domain, ∃ w : H1 𝕜 a b, baseLp w = (u : L2 𝕜 a b) ∧
    lpDistribution (A u) =
      (lpDistribution (multiplier c.p c.p_C1.continuousOn (derivativeLp w))).comp
          (testPartialCLM [0]) +
        lpDistribution (multiplier c.q c.q_continuous (baseLp w))

/-- Compact resolvent includes an actual resolvent point and compactness at
every resolvent point, with the source convention (ζI−A)⁻¹. -/
def HasCompactResolvent {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)) : Prop :=
  (∃ ζ : 𝕜, Nonempty (ResolventInverse A ζ)) ∧
    ∀ (ζ : 𝕜) (R : ResolventInverse A ζ), IsCompactOperator R.inverse

namespace Spec

def FormIntegral : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b) (v u : H1 𝕜 a b),
  form c v u = ∫ z : Domain 1,
    (c.p (z 0) : 𝕜) * conj (derivativeLp v z) * derivativeLp u z +
      (c.q (z 0) : 𝕜) * conj (baseLp v z) * baseLp u z
    ∂(volume.restrict (spatialInterval a b : Set (Domain 1)))

def FormHermitian : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b) (v u : H1 𝕜 a b), conj (form c u v) = form c v u

/-- Quantitative coercivity after a finite scalar shift. This is a conclusion
from the given coefficients, not an input certificate. -/
def FormEstimates : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b), ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
    (∀ v u : H1 𝕜 a b, ‖form c v u‖ ≤ C * ‖v‖ * ‖u‖) ∧
    ∀ u : H1 𝕜 a b,
      c.p₀ * ‖derivativeLp u‖ ^ 2 + ‖baseLp u‖ ^ 2 ≤
        RCLike.re (form c u u) + (Q + 1) * ‖baseLp u‖ ^ 2

/-- Construction and uniqueness of the maximal weak form operator. -/
def WeakRealization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b),
  ∃! A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b), FormRealization c A

/-- Properties established before the H² domain and closed-form arguments. -/
def WeakProperties : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b) (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)),
  FormRealization c A → DifferentialAction c A ∧ A.IsFormalAdjoint A ∧
    ∃ γ : ℝ, ∀ u : A.domain,
      γ * ‖(u : L2 𝕜 a b)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (u : L2 𝕜 a b) (A u))

/-- The first, noncircular regularity step in the source proof. -/
def FluxRegularity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b) (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)),
  FormRealization c A → ∀ u : A.domain,
    ∃ (w : H1 𝕜 a b) (flux : H1 𝕜 a b),
      baseLp w = (u : L2 𝕜 a b) ∧
      baseLp flux = multiplier c.p c.p_C1.continuousOn (derivativeLp w) ∧
      derivativeLp flux = multiplier c.q c.q_continuous (baseLp w) - A u

/-- Complete assigned theorem, retaining exact domains and both scalar fields.
The periodic and spectral/heat clauses have separate allocated goals. -/
def Realization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b),
  ∃! A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b),
    FormRealization c A ∧
    (∀ u : L2 𝕜 a b, u ∈ A.domain ↔ StrongDomain u) ∧
    DifferentialAction c A ∧
    Dense (A.domain : Set (L2 𝕜 a b)) ∧
    A = HilbertAdjointSpec.adjointValue A ∧
    (∃ γ : ℝ, ∀ u : A.domain,
      γ * ‖(u : L2 𝕜 a b)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (u : L2 𝕜 a b) (A u))) ∧
    HasCompactResolvent A

end Spec
end ExpandedFA.Models.SturmLiouvilleDirichlet
