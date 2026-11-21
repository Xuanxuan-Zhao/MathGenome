import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyBMODuality
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyCZEndpoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpIntegralPairing
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.HilbertTransform
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
The endpoint clause of `fa2:p4:john-nirenberg`, paper.tex:19665–19667 and
19702–19713. The moment and exponential assertions are allocated separately.
Scalars are real or complex; all Euclidean dimensions are retained. The
bilinear transpose is C T* C, not T*. Bounded data are paired only with
integrable Hardy images, never with an uncorrected singular kernel integral.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.PartIV.CzBmoEndpointSpec
open Hardy.HardyDualBMORepresentationSpec Hardy.BMOQuotientSpec
open SingularIntegrals.StandardConvolution

abbrev Linfty (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :=
  Lp 𝕜 ∞ (volume : Measure (Hardy.BMOQuotientSpec.Point d))

/-- Conjugation on the native L² classes, with its usual a.e. interpretation. -/
def transposeValue {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : SingularIntegrals.StandardConvolution.L2 𝕜 d →L[𝕜]
      SingularIntegrals.StandardConvolution.L2 𝕜 d)
    (f : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
    SingularIntegrals.StandardConvolution.L2 𝕜 d :=
  star (ContinuousLinearMap.adjoint T (star f))

/-- The L¹–L∞ product is an ordinary integrable product. -/
def functional {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : H1 d 𝕜 →L[𝕜] L1 d 𝕜) (h : Linfty d 𝕜) : H1 d 𝕜 →L[𝕜] 𝕜 :=
  (FunctionSpaces.ScalarLpIntegralPairingSpec.IntegralPairingValue volume 1 ∞ h).comp A

/-- The prescribed quotient structure is fixed by its norm and operations on
all BMO representatives, as in the accepted BMO interface. -/
def QuotientStructure {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    [NormedAddCommGroup (BMOValue d 𝕜)] [NormedSpace 𝕜 (BMOValue d 𝕜)] : Prop :=
  CompleteSpace (BMOValue d 𝕜) ∧
  (∀ g : BMOFunctionValue d 𝕜, ‖classOf g‖ = (BMOENormValue g.val).toReal) ∧
  (∀ f g : BMOFunctionValue d 𝕜,
    ∃ h : LocallyIntegrable (f.val + g.val) volume ∧ BMOENormValue (f.val + g.val) < ∞,
      classOf ⟨f.val + g.val, h⟩ = classOf f + classOf g) ∧
  (∀ (c : 𝕜) (f : BMOFunctionValue d 𝕜),
    ∃ h : LocallyIntegrable (c • f.val) volume ∧ BMOENormValue (c • f.val) < ∞,
      classOf ⟨c • f.val, h⟩ = c • classOf f)

/-- The analytic functional-to-quotient construction, with dimension-only
constant and scalar linearity of the actual endpoint map. This is a helper,
not a substitute for the unconditional standard-operator endpoint below. -/
def AbstractTransposition : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (𝕜 : Type) [RCLike 𝕜],
    ∃ G : NormedAddCommGroup (BMOValue d 𝕜), letI := G
    ∃ S : NormedSpace 𝕜 (BMOValue d 𝕜), letI := S
    QuotientStructure (d := d) (𝕜 := 𝕜) ∧
    ∀ A : H1 d 𝕜 →L[𝕜] L1 d 𝕜,
      ∃ E : Linfty d 𝕜 →L[𝕜] BMOValue d 𝕜,
        ‖E‖ ≤ C * ‖A‖ ∧
        ∀ h : Linfty d 𝕜, ∃ g : BMOFunctionValue d 𝕜,
          E h = classOf g ∧ Represents (functional A h) g.val ∧
          ∀ g' : BMOFunctionValue d 𝕜,
            Represents (functional A h) g'.val → classOf g' = E h

/-- Agreement of a Hardy endpoint with C T* C on the complete common domain. -/
def HardyTransposeAgreement {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : StandardConvolutionOperator 𝕜 d) (A : H1 d 𝕜 →L[𝕜] L1 d 𝕜) : Prop :=
  ∀ (f : H1 d 𝕜) (h2 : MemLp (Hardy.AtomicHardySpaceSpec.EmbeddingValue volume f
      : SingularIntegrals.StandardConvolution.Space d → 𝕜) 2),
    (A f : SingularIntegrals.StandardConvolution.Space d → 𝕜) =ᵐ[volume]
      transposeValue T.operator (h2.toLp _)

/-- Consistency on all bounded L² inputs, hence in particular on original
smooth compactly supported tests. No BMO hypothesis is imposed on T h. -/
def ConsistentWithL2 {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : StandardConvolutionOperator 𝕜 d) (E : Linfty d 𝕜 → BMOValue d 𝕜) : Prop :=
  ∀ (h : Linfty d 𝕜) (h2 : MemLp (h : SingularIntegrals.StandardConvolution.Space d → 𝕜) 2),
    ∃ g : BMOFunctionValue d 𝕜, E h = classOf g ∧
      ∃ c : 𝕜, ∀ᵐ x ∂volume, g.val x = T.operator (h2.toLp _) x + c

/-- Closure of the original standard convolution setting under the bilinear
transpose, preserving the quantitative kernel and L² bounds. -/
def StandardTranspose : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d),
    ∃ S : StandardConvolutionOperator 𝕜 d,
      (∀ f, S.operator f = transposeValue T.operator f) ∧
      S.kernel.constant = T.kernel.constant ∧ ‖S.operator‖ = ‖T.operator‖

/-- Full standard-CZ endpoint, with the original constant dependence and no
extra assumption supplying a Hardy bound for the transpose. -/
def Endpoint : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (𝕜 : Type) [RCLike 𝕜],
    ∃ G : NormedAddCommGroup (BMOValue d 𝕜), letI := G
    ∃ S : NormedSpace 𝕜 (BMOValue d 𝕜), letI := S
    QuotientStructure (d := d) (𝕜 := 𝕜) ∧
    ∀ T : StandardConvolutionOperator 𝕜 d,
      ∃ A : H1 d 𝕜 →L[𝕜] L1 d 𝕜,
      ∃ E : Linfty d 𝕜 →L[𝕜] BMOValue d 𝕜,
        HardyTransposeAgreement T A ∧
        ‖A‖ ≤ Hardy.HardyCZEndpointSpec.endpointConstant T ∧
        ‖E‖ ≤ C * Hardy.HardyCZEndpointSpec.endpointConstant T ∧
        (∀ h : Linfty d 𝕜, ∃ g : BMOFunctionValue d 𝕜,
          E h = classOf g ∧ Represents (functional A h) g.val) ∧
        ConsistentWithL2 T E

/-- The non-conjugated integral identity satisfied by C T* C. -/
def TransposePairing : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (T : SingularIntegrals.StandardConvolution.L2 𝕜 d →L[𝕜]
      SingularIntegrals.StandardConvolution.L2 𝕜 d)
    (f g : SingularIntegrals.StandardConvolution.L2 𝕜 d),
      (∫ x, T f x * g x) = ∫ x, f x * transposeValue T g x

open SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

/-- A line endpoint is a bounded map on the original line L∞ space. Its
values lie in BMO(ℝ¹)/𝕜 via the canonical line isometry. Both the transposed
functional and the agreement with the original line L² operator are explicit. -/
def LineHilbertEndpoint (𝕜 : Type) [RCLike 𝕜]
    (H : LineLp 𝕜 2 → LineLp 𝕜 2) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ G : NormedAddCommGroup (BMOValue 1 𝕜), letI := G
    ∃ S : NormedSpace 𝕜 (BMOValue 1 𝕜), letI := S
    QuotientStructure (d := 1) (𝕜 := 𝕜) ∧
    ∃ T : StandardConvolutionOperator 𝕜 1,
    ∃ A : H1 1 𝕜 →L[𝕜] L1 1 𝕜,
    ∃ E : Linfty 1 𝕜 →L[𝕜] BMOValue 1 𝕜,
    ∃ F : LineLp 𝕜 ∞ →L[𝕜] BMOValue 1 𝕜,
      (∀ f : LineLp 𝕜 2, fromEuclidean 2 (T.operator (toEuclidean 2 f)) = H f) ∧
      HardyTransposeAgreement T A ∧
      ‖A‖ ≤ Hardy.HardyCZEndpointSpec.endpointConstant T ∧
      ‖E‖ ≤ C ∧ ‖F‖ ≤ C ∧
      (∀ h, F h = E (toEuclidean ∞ h)) ∧
      (∀ h : LineLp 𝕜 ∞, ∃ g : BMOFunctionValue 1 𝕜,
        F h = classOf g ∧ Represents (functional A (toEuclidean ∞ h)) g.val) ∧
      ConsistentWithL2 T E ∧
      (∀ (h : LineLp 𝕜 ∞) (h2 : MemLp (h : ℝ → 𝕜) 2 volume),
        ∃ g : BMOFunctionValue 1 𝕜, F h = classOf g ∧
          ∃ c : 𝕜, ∀ᵐ x : ℝ ∂volume,
            g.val (lineIsometry x) = H (h2.toLp _) x + c)

/-- These shared realization types refer directly to the fixed multiplier
complexHilbert and to its real restriction, rather than to an unnamed operator
satisfying a separately chosen Fourier convention. -/
def HilbertRealization : Prop := StandardRealizations

/-- The actual multiplier-defined complex Hilbert transform and its real
restriction have consistent bounded scalar-linear line endpoints. -/
def HilbertEndpoint : Prop :=
  LineHilbertEndpoint ℂ complexHilbert ∧
  ∃ H : RealL2 →L[ℝ] RealL2, IsRealRestriction H ∧ LineHilbertEndpoint ℝ H

def HilbertAssembly : Prop := HilbertRealization → HilbertEndpoint

/-- The complete allocated obligation. -/
def FullEndpoint : Prop := Endpoint ∧ HilbertEndpoint

end ExpandedFA.PartIV.CzBmoEndpointSpec
