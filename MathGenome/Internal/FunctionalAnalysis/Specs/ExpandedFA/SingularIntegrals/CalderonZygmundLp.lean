import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The strong part of the standard convolution theorem, paper.tex:18241–18285.
The setting is exactly the accepted distribution-kernel setting, in every dimension
and over either scalar field. All compatibilities are ordinary a.e. equalities. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExpandedFA.SingularIntegrals.CZLp
open StandardConvolution

/-- The strictly interior finite exponents. -/
structure InteriorExponent where
  val : ℝ≥0∞
  one_lt : 1 < val
  lt_top : val < ∞

instance (p : InteriorExponent) : Fact (1 ≤ p.val) := ⟨p.one_lt.le⟩

abbrev LpSpace (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (p : ℝ≥0∞) :=
  Lp 𝕜 p (volume : Measure (Space d))

/-- Agreement with the original L² operator on the entire intersection. -/
def AgreesWithL2 {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) (p : InteriorExponent)
    (S : LpSpace 𝕜 d p.val →L[𝕜] LpSpace 𝕜 d p.val) : Prop :=
  ∀ (f : Space d → 𝕜) (hp : MemLp f p.val (volume : Measure (Space d)))
    (h2 : MemLp f 2 (volume : Measure (Space d))),
    (S (hp.toLp f) : Space d → 𝕜) =ᵐ[volume] (T.operator (h2.toLp f) : Space d → 𝕜)

/-- An intermediate completion statement on the full endpoint intersection.
The final theorem below strengthens agreement to every pairwise intersection. -/
def LowExtensions : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d)
    (p : InteriorExponent), p.val < 2 →
    ∃ S : LpSpace 𝕜 d p.val →L[𝕜] LpSpace 𝕜 d p.val,
      ∀ (f : Space d → 𝕜) (_h1 : MemLp f 1 (volume : Measure (Space d)))
        (h2 : MemLp f 2 (volume : Measure (Space d)))
        (hp : MemLp f p.val (volume : Measure (Space d))),
        (S (hp.toLp f) : Space d → 𝕜) =ᵐ[volume]
          (T.operator (h2.toLp f) : Space d → 𝕜)

/-- The complete lower-half strong theorem, including both whole-intersection
compatibilities. The upper half is retained separately in `CompatibleFamily`. -/
def LowStrongExtensions : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d)
    (p : InteriorExponent), p.val < 2 →
    ∃ S : LpSpace 𝕜 d p.val →L[𝕜] LpSpace 𝕜 d p.val,
      AgreesWithL2 T p S ∧
      ∀ (W : CZWeak.L1 𝕜 d →ₗ[𝕜] CZWeak.MeasurableClasses 𝕜 d),
        CZWeak.IsCompatibleExtension T W →
        ∀ (f : Space d → 𝕜) (h1 : MemLp f 1 (volume : Measure (Space d)))
          (hp : MemLp f p.val (volume : Measure (Space d))),
          (S (hp.toLp f) : Space d → 𝕜) =ᵐ[volume]
            (W (h1.toLp f) : Space d → 𝕜)

/-- The abstract duality step, with the genuine scalar-linear dual and
ordinary a.e. agreement on the entire Lp/L² intersection. Sigma-finiteness
suffices even if the upper exponent is infinity. -/
def AdjointDualityTransfer : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (𝕜 : Type) [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p], q ≠ ∞ →
    ∀ (B : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) (R : Lp 𝕜 q μ →L[𝕜] Lp 𝕜 q μ),
    (∀ (g : X → 𝕜) (hgq : MemLp g q μ) (hg2 : MemLp g 2 μ),
      (R (hgq.toLp g) : X → 𝕜) =ᵐ[μ] (B.adjoint (hg2.toLp g) : X → 𝕜)) →
    ∃ S : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ,
      (∀ f, ‖S f‖ ≤ ‖R‖ * ‖f‖) ∧
      ∀ (f : X → 𝕜) (hfp : MemLp f p μ) (hf2 : MemLp f 2 μ),
        (S (hfp.toLp f) : X → 𝕜) =ᵐ[μ] (B (hf2.toLp f) : X → 𝕜)

/-- The reflected-conjugate C¹ kernel has the same bound constant. -/
def ReflectedConjugateBounds : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (k : StandardKernel 𝕜 d),
    ∃ a : StandardKernel 𝕜 d,
      (∀ x, a.function x = star (k.function (-x))) ∧ a.constant = k.constant

/-- Translation invariance is inherited by the Hilbert adjoint. -/
def AdjointTranslationInvariant : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d),
    TranslationInvariant T.operator.adjoint

/-- The Hilbert adjoint is another operator in the same standard convolution
setting, with reflected conjugate kernel off the origin. In particular its
translation invariance and distribution-kernel identity must be proved. -/
def AdjointSetting : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d),
    ∃ A : StandardConvolutionOperator 𝕜 d,
      A.operator = T.operator.adjoint ∧
      ∀ x ≠ 0, A.kernel.function x = star (T.kernel.function (-x))

/-- A single family of bounded operators on all finite interior Lᵖ spaces.
Every pair of extensions agrees on its entire intersection, including L¹
with the previously established weak extension and L² with the given operator. -/
def CompatibleFamily : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d),
    ∃ S : ∀ p : InteriorExponent,
        LpSpace 𝕜 d p.val →L[𝕜] LpSpace 𝕜 d p.val,
      (∀ p, AgreesWithL2 T p (S p)) ∧
      (∀ (p q : InteriorExponent) (f : Space d → 𝕜)
        (hp : MemLp f p.val (volume : Measure (Space d)))
        (hq : MemLp f q.val (volume : Measure (Space d))),
        (S p (hp.toLp f) : Space d → 𝕜) =ᵐ[volume]
          (S q (hq.toLp f) : Space d → 𝕜)) ∧
      (∀ (W : CZWeak.L1 𝕜 d →ₗ[𝕜] CZWeak.MeasurableClasses 𝕜 d),
        CZWeak.IsCompatibleExtension T W →
        ∀ (p : InteriorExponent) (f : Space d → 𝕜)
          (h1 : MemLp f 1 (volume : Measure (Space d)))
          (hp : MemLp f p.val (volume : Measure (Space d))),
          (S p (hp.toLp f) : Space d → 𝕜) =ᵐ[volume]
            (W (h1.toLp f) : Space d → 𝕜))

end ExpandedFA.SingularIntegrals.CZLp
