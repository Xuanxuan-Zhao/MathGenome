import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.RealComplexification
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.SeparableMASA
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.InnerProductSpace.Subspace

/-! Canonical real/imaginary coordinates of bounded operators on the existing
Hilbert complexification. These definitions do not change its instances or the
upstream bounded extension. The native Lp real forms below use the genuine
closed real fixed spaces of conjugation followed by measure-preserving pullback. -/
noncomputable section
open scoped InnerProductSpace Topology
namespace ExpandedFA.VonNeumann.RealAbelianComplexification
open TraceIdeals.RealComplexification
universe u
namespace Spec
open TraceIdeals.RealComplexification.Spec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Extract the real coordinate on the original real Hilbert space. -/
def operatorRealPart (R : Space H →L[ℂ] Space H) : H →L[ℝ] H :=
  realPart.comp ((R.restrictScalars ℝ).comp inclusion.toContinuousLinearMap)

/-- Extract the imaginary coordinate on the original real Hilbert space. -/
def operatorImagPart (R : Space H →L[ℂ] Space H) : H →L[ℝ] H :=
  imagPart.comp ((R.restrictScalars ℝ).comp inclusion.toContinuousLinearMap)

/-- Conjugation of operators, expressed using the canonical extension. The
implementation proves the pointwise formula J R J and all automorphism laws. -/
def gamma (R : Space H →L[ℂ] Space H) : Space H →L[ℂ] Space H :=
  operator (operatorRealPart R) - Complex.I • operator (operatorImagPart R)

/-- The concrete set A+iA; closure under algebra operations is a conclusion. -/
def complexifiedSet [CompleteSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)) :
    Set (Space H →L[ℂ] Space H) :=
  {R | ∃ S ∈ A, ∃ T ∈ A, R = operator S + Complex.I • operator T}

def OperatorRealPartType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (Space H →L[ℂ] Space H) → (H →L[ℝ] H)

def OperatorImagPartType := OperatorRealPartType.{u}

def GammaType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (Space H →L[ℂ] Space H) → (Space H →L[ℂ] Space H)

def ComplexifiedSetType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    StarSubalgebra ℝ (H →L[ℝ] H) → Set (Space H →L[ℂ] Space H)

def OperatorDecomposition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : Space H →L[ℂ] Space H),
    R = operator (operatorRealPart R) + Complex.I • operator (operatorImagPart R) ∧
    ∀ S T : H →L[ℝ] H,
      R = operator S + Complex.I • operator T ↔
        operatorRealPart R = S ∧ operatorImagPart R = T

def ConjugationLaws : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (∀ (R : Space H →L[ℂ] Space H) p,
      gamma R p = conjugation (R (conjugation p))) ∧
    (∀ R : Space H →L[ℂ] Space H, gamma (gamma R) = R) ∧
    (∀ R S : Space H →L[ℂ] Space H, gamma (R + S) = gamma R + gamma S) ∧
    (∀ (a : ℂ) (R : Space H →L[ℂ] Space H),
      gamma (a • R) = star a • gamma R) ∧
    (∀ R S : Space H →L[ℂ] Space H, gamma (R * S) = gamma R * gamma S) ∧
    gamma (1 : Space H →L[ℂ] Space H) = 1

def FixedOperators : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : Space H →L[ℂ] Space H),
    gamma R = R ↔ ∃! T : H →L[ℝ] H, R = operator T

def ConjugationStar : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H],
    letI : CompleteSpace (Space H) :=
      TraceIdeals.RealComplexification.Spec.completeSpace
    ∀ R : Space H →L[ℂ] Space H, gamma (star R) = star (gamma R)


local instance [CompleteSpace H] : CompleteSpace (Space H) :=
  TraceIdeals.RealComplexification.Spec.completeSpace

/-- A concrete complex star algebra; its carrier is proved to be A+iA. -/
def complexAlgebra [CompleteSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)) :
    StarSubalgebra ℂ (Space H →L[ℂ] Space H) :=
  StarAlgebra.adjoin ℂ (operator '' (A : Set (H →L[ℝ] H)))

def ComplexAlgebraType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    StarSubalgebra ℝ (H →L[ℝ] H) → StarSubalgebra ℂ (Space H →L[ℂ] Space H)

/-- Set complexification also applies to the actual commutants. -/
def complexSpanSet (s : Set (H →L[ℝ] H)) : Set (Space H →L[ℂ] Space H) :=
  {R | ∃ S ∈ s, ∃ T ∈ s, R = operator S + Complex.I • operator T}

def ComplexSpanSetType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    Set (H →L[ℝ] H) → Set (Space H →L[ℂ] Space H)

def AlgebraCarrier : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    (complexAlgebra A : Set (Space H →L[ℂ] Space H)) = complexifiedSet A

def AlgebraFixedPoints : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    (∀ R, R ∈ complexAlgebra A → gamma R ∈ complexAlgebra A) ∧
    (∀ R, R ∈ complexAlgebra A ∧ gamma R = R ↔ ∃ T ∈ A, R = operator T)

def Commutants : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Set (H →L[ℝ] H)),
    Set.centralizer (complexSpanSet s) = complexSpanSet (Set.centralizer s) ∧
    Set.centralizer (Set.centralizer (complexSpanSet s)) =
      complexSpanSet (Set.centralizer (Set.centralizer s))

def GeneratedDoubleCommutants : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H),
    complexSpanSet (Set.centralizer (Set.centralizer
      (StarAlgebra.adjoin ℝ {N} : Set (H →L[ℝ] H)))) =
    Set.centralizer (Set.centralizer
      (StarAlgebra.adjoin ℂ {operator N} : Set (Space H →L[ℂ] Space H)))

/-- Arbitrary filters and no norm-boundedness assumptions. -/
def StrongExtension : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ι : Type*) (l : Filter ι) (f : ι → H →L[ℝ] H) (T : H →L[ℝ] H),
    Filter.Tendsto f l (@nhds _ (OperatorTopology.Spec.StrongTopologyValue ℝ H H) T) ↔
    Filter.Tendsto (fun i => operator (f i)) l
      (@nhds _ (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H)) (operator T))

def WeakExtension : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : Type*) (l : Filter ι) (f : ι → H →L[ℝ] H) (T : H →L[ℝ] H),
    Filter.Tendsto f l (@nhds _ (OperatorTopology.Spec.WeakTopologyValue ℝ H H) T) ↔
    Filter.Tendsto (fun i => operator (f i)) l
      (@nhds _ (OperatorTopology.Spec.WeakTopologyValue ℂ (Space H) (Space H)) (operator T))

def ExtractionContinuous : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    @Continuous _ _
      (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H))
      (OperatorTopology.Spec.StrongTopologyValue ℝ H H) operatorRealPart ∧
    @Continuous _ _
      (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H))
      (OperatorTopology.Spec.StrongTopologyValue ℝ H H) operatorImagPart ∧
    @Continuous _ _
      (OperatorTopology.Spec.WeakTopologyValue ℂ (Space H) (Space H))
      (OperatorTopology.Spec.WeakTopologyValue ℝ H H) operatorRealPart ∧
    @Continuous _ _
      (OperatorTopology.Spec.WeakTopologyValue ℂ (Space H) (Space H))
      (OperatorTopology.Spec.WeakTopologyValue ℝ H H) operatorImagPart

def ClosedAlgebras : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    (@IsClosed _ (OperatorTopology.Spec.WeakTopologyValue ℝ H H) (A : Set _) ↔
      @IsClosed _ (OperatorTopology.Spec.WeakTopologyValue ℂ (Space H) (Space H))
        (complexAlgebra A : Set _)) ∧
    (@IsClosed _ (OperatorTopology.Spec.StrongTopologyValue ℝ H H) (A : Set _) ↔
      @IsClosed _ (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H))
        (complexAlgebra A : Set _))

def MASATransport : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    SeparableMASA.Spec.RealIsMASA A → SeparableMASA.Spec.IsMASA (complexAlgebra A)

def CyclicSeparatingTransport : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)) (e : H),
    (SeparableMASA.Spec.RealIsCyclic A e →
      SeparableMASA.Spec.IsCyclic (complexAlgebra A) (inclusion e)) ∧
    (SeparableMASA.Spec.RealIsSeparating A e →
      SeparableMASA.Spec.IsSeparating (complexAlgebra A) (inclusion e))

def Separability : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H], TopologicalSpace.SeparableSpace (Space H)

end Spec
end ExpandedFA.VonNeumann.RealAbelianComplexification

open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.VonNeumann.RealAbelianComplexification.Spec.NativeLp
universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

/-- A measurable measure-preserving involution, including null measures. -/
structure InvolutionData (μ : Measure X) where
  tau : X → X
  measurePreserving : MeasurePreserving tau μ μ
  involutive : Function.Involutive tau

/-- Conjugation followed by pullback on the native complex Lp quotient. -/
def conjugatePullback (D : InvolutionData μ) (f : Lp ℂ p μ) : Lp ℂ p μ :=
  star (Lp.compMeasurePreserving D.tau D.measurePreserving f)

theorem coeFn_conjugatePullback (D : InvolutionData μ) (f : Lp ℂ p μ) :
    conjugatePullback D f =ᵐ[μ] fun x ↦ star (f (D.tau x)) := by
  exact (Lp.coeFn_star _).trans ((Lp.coeFn_compMeasurePreserving _ _).fun_comp star)

theorem conjugatePullback_zero (D : InvolutionData μ) :
    conjugatePullback D (0 : Lp ℂ p μ) = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_conjugatePullback D (0 : Lp ℂ p μ),
    D.measurePreserving.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_zero (E := ℂ) (p := p) (μ := μ)),
    Lp.coeFn_zero (E := ℂ) (p := p) (μ := μ)] with x hC h0 h0'
  simp only [Function.comp_apply, Pi.zero_apply] at h0 h0'
  rw [hC, h0, star_zero, h0']

theorem conjugatePullback_add (D : InvolutionData μ) (f g : Lp ℂ p μ) :
    conjugatePullback D (f + g) = conjugatePullback D f + conjugatePullback D g := by
  apply Lp.ext
  filter_upwards [coeFn_conjugatePullback D (f+g),
    coeFn_conjugatePullback D f, coeFn_conjugatePullback D g,
    D.measurePreserving.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_add f g),
    Lp.coeFn_add (conjugatePullback D f) (conjugatePullback D g)] with x hfg hf hg hadd hadd'
  simp only [Function.comp_apply, Pi.add_apply] at hadd hadd'
  rw [hfg, hadd, star_add, ← hf, ← hg, hadd']

theorem conjugatePullback_smul (D : InvolutionData μ) (c : ℂ) (f : Lp ℂ p μ) :
    conjugatePullback D (c • f) = star c • conjugatePullback D f := by
  apply Lp.ext
  filter_upwards [coeFn_conjugatePullback D (c • f), coeFn_conjugatePullback D f,
    D.measurePreserving.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c f),
    Lp.coeFn_smul (star c) (conjugatePullback D f)] with x hcf hf hsmul hsmul'
  simp only [Function.comp_apply, Pi.smul_apply] at hsmul hsmul'
  rw [hcf, hsmul, star_smul, ← hf, hsmul']

theorem conjugatePullback_real_smul (D : InvolutionData μ) (c : ℝ) (f : Lp ℂ p μ) :
    conjugatePullback D (c • f) = c • conjugatePullback D f := by
  apply Lp.ext
  filter_upwards [coeFn_conjugatePullback D (c • f), coeFn_conjugatePullback D f,
    D.measurePreserving.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (conjugatePullback D f)] with x hcf hf hsmul hsmul'
  simp only [Function.comp_apply, Pi.smul_apply] at hsmul hsmul'
  rw [hcf, hsmul, star_smul, star_trivial, ← hf, hsmul']

theorem conjugatePullback_involutive (D : InvolutionData μ) :
    Function.Involutive (conjugatePullback D : Lp ℂ p μ → Lp ℂ p μ) := by
  intro f
  apply Lp.ext
  filter_upwards [coeFn_conjugatePullback D (conjugatePullback D f),
    D.measurePreserving.quasiMeasurePreserving.ae_eq_comp (coeFn_conjugatePullback D f)] with x hC hCC
  simp only [Function.comp_apply, D.involutive x] at hCC
  rw [hC, hCC, star_star]

theorem norm_conjugatePullback (D : InvolutionData μ) (f : Lp ℂ p μ) :
    ‖conjugatePullback D f‖ = ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_conjugatePullback D f)]
  change (eLpNorm (star ((f : X → ℂ) ∘ D.tau)) p μ).toReal = ‖f‖
  rw [eLpNorm_star, eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) D.measurePreserving]
  exact (Lp.norm_def f).symm

/-- The real-linear map is used only to construct the fixed real submodule. -/
def conjugatePullbackRealLinear (D : InvolutionData μ) : Lp ℂ p μ →ₗ[ℝ] Lp ℂ p μ where
  toFun := conjugatePullback D
  map_add' := conjugatePullback_add D
  map_smul' := conjugatePullback_real_smul D

theorem isometry_conjugatePullback [Fact (1 ≤ p)] (D : InvolutionData μ) :
    Isometry (conjugatePullback D : Lp ℂ p μ → Lp ℂ p μ) :=
  AddMonoidHomClass.isometry_of_norm (conjugatePullbackRealLinear D) (norm_conjugatePullback D)

/-- The inherited real form; its elements need not be real-valued functions. -/
def fixedSubmodule (D : InvolutionData μ) (p : ℝ≥0∞) : Submodule ℝ (Lp ℂ p μ) :=
  LinearMap.eqLocus (conjugatePullbackRealLinear D) LinearMap.id

abbrev Fixed (D : InvolutionData μ) (p : ℝ≥0∞) := ↥(fixedSubmodule D p)

@[simp] theorem mem_fixedSubmodule_iff (D : InvolutionData μ) (f : Lp ℂ p μ) :
    f ∈ fixedSubmodule D p ↔ conjugatePullback D f = f := Iff.rfl

theorem fixed_ae (D : InvolutionData μ) (f : Fixed D p) :
    (fun x ↦ f.val (D.tau x)) =ᵐ[μ] fun x ↦ star (f.val x) := by
  have heq := coeFn_conjugatePullback D f.val
  have hf : conjugatePullback D f.val = f.val := f.property
  rw [hf] at heq
  filter_upwards [heq] with x hx
  simpa only [star_star] using congrArg star hx.symm

theorem mem_fixedSubmodule_iff_ae (D : InvolutionData μ) (f : Lp ℂ p μ) :
    f ∈ fixedSubmodule D p ↔
      (fun x ↦ f (D.tau x)) =ᵐ[μ] fun x ↦ star (f x) := by
  constructor
  · intro hf
    exact fixed_ae D ⟨f, hf⟩
  · intro hf
    change conjugatePullback D f = f
    apply Lp.ext
    filter_upwards [coeFn_conjugatePullback D f, hf] with x hC hfix
    rw [hC, hfix, star_star]

theorem isClosed_fixedSubmodule [Fact (1 ≤ p)] (D : InvolutionData μ) :
    IsClosed (fixedSubmodule D p : Set (Lp ℂ p μ)) :=
  isClosed_eq (isometry_conjugatePullback D).continuous continuous_id

instance fixed_completeSpace [Fact (1 ≤ p)] (D : InvolutionData μ) :
    CompleteSpace (Fixed D p) := (isClosed_fixedSubmodule D).completeSpace_coe

/-- Full quotient-level conjugation and inherited complete real fixed-space laws. -/
def FoundationLaws : Prop :=
  ∀ (D : InvolutionData μ) (p : ℝ≥0∞),
    (∀ f : Lp ℂ p μ,
      conjugatePullback D f =ᵐ[μ] fun x ↦ star (f (D.tau x))) ∧
    (∀ f g : Lp ℂ p μ,
      conjugatePullback D (f + g) = conjugatePullback D f + conjugatePullback D g) ∧
    (∀ (c : ℂ) (f : Lp ℂ p μ),
      conjugatePullback D (c • f) = star c • conjugatePullback D f) ∧
    (∀ f : Lp ℂ p μ, ‖conjugatePullback D f‖ = ‖f‖) ∧
    Function.Involutive (conjugatePullback D : Lp ℂ p μ → Lp ℂ p μ) ∧
    (∀ f : Lp ℂ p μ, f ∈ fixedSubmodule D p ↔
      (fun x ↦ f (D.tau x)) =ᵐ[μ] fun x ↦ star (f x)) ∧
    (∀ [Fact (1 ≤ p)],
      (∀ f : Fixed D p, ‖f‖ = ‖f.val‖) ∧
      Isometry (conjugatePullback D : Lp ℂ p μ → Lp ℂ p μ) ∧
      IsClosed (fixedSubmodule D p : Set (Lp ℂ p μ)) ∧
      CompleteSpace (Fixed D p))

end ExpandedFA.VonNeumann.RealAbelianComplexification.Spec.NativeLp


namespace ExpandedFA.VonNeumann.RealAbelianComplexification.Spec
universe u
/-- All positive measures and all measurable measure-preserving involutions;
no finiteness, sigma-finiteness or nonzero-mass hypothesis is imposed. -/
def NativeLpFoundation : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X),
    NativeLp.FoundationLaws (μ := μ)
end ExpandedFA.VonNeumann.RealAbelianComplexification.Spec


namespace ExpandedFA.VonNeumann.RealAbelianComplexification.Spec.NativeLp
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
/-- The real Hilbert structure inherited from native complex L2. -/
instance fixed_innerProductSpace (D : InvolutionData μ) :
    InnerProductSpace ℝ (Fixed D 2) := (fixedSubmodule D 2).innerProductSpace

/-- Native Hölder duality restricted to the closed real fixed spaces. -/
def pairing (D : InvolutionData μ) : Fixed D ∞ →L[ℝ] Fixed D 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (Fixed D 1) ℂ ℝ Complex.reCLM).comp
    (((ContinuousLinearMap.mul ℝ ℂ).lpPairing μ ∞ 1).bilinearComp
      (fixedSubmodule D ∞).subtypeL (fixedSubmodule D 1).subtypeL)


end ExpandedFA.VonNeumann.RealAbelianComplexification.Spec.NativeLp
namespace ExpandedFA.VonNeumann.RealAbelianComplexification.Spec
open NativeLp
universe u

def NativeLpConjugationType :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞},
    InvolutionData μ → Lp ℂ p μ → Lp ℂ p μ

def NativeLpFixedSubmoduleType :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X},
    (D : InvolutionData μ) → (p : ℝ≥0∞) → Submodule ℝ (Lp ℂ p μ)

def NativeLpPairingType :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X},
    (D : InvolutionData μ) → Fixed D ∞ →L[ℝ] Fixed D 1 →L[ℝ] ℝ

/-- The native real Hilbert structure and ordinary multiplication integral pairing. -/
def NativeLpHilbertPairing : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) (D : InvolutionData μ),
    (∀ f g : Fixed D 2,
      Integrable (fun x => star (f.val x) * g.val x) μ ∧
      (∫ x, star (f.val x) * g.val x ∂μ).im = 0 ∧
      (inner ℝ f g : ℂ) = ∫ x, star (f.val x) * g.val x ∂μ) ∧
    (∀ (f : Fixed D ∞) (g : Fixed D 1),
      Integrable (fun x => f.val x * g.val x) μ ∧
      pairing D f g = (∫ x, f.val x * g.val x ∂μ).re ∧
      (∫ x, f.val x * g.val x ∂μ).im = 0)
end ExpandedFA.VonNeumann.RealAbelianComplexification.Spec

namespace ExpandedFA.VonNeumann.RealAbelianComplexification.Spec.NativeLp
universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X} {p q r : ℝ≥0∞}
/-- Native Hölder multiplication commutes with the conjugate pullback. -/
theorem conjugatePullback_holder [ENNReal.HolderTriple p q r]
    (D : InvolutionData μ) (f : Lp ℂ p μ) (g : Lp ℂ q μ) :
    conjugatePullback D ((ContinuousLinearMap.mul ℂ ℂ).holder r f g) =
      (ContinuousLinearMap.mul ℂ ℂ).holder r (conjugatePullback D f) (conjugatePullback D g) := by
  apply Lp.ext
  filter_upwards [coeFn_conjugatePullback D ((ContinuousLinearMap.mul ℂ ℂ).holder r f g),
    D.measurePreserving.quasiMeasurePreserving.ae ((ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := r) f g),
    (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := r) (conjugatePullback D f) (conjugatePullback D g),
    coeFn_conjugatePullback D f, coeFn_conjugatePullback D g] with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, ContinuousLinearMap.mul_apply', star_mul]
  exact mul_comm _ _

/-- Native star commutes with the conjugate pullback. -/
theorem conjugatePullback_star (D : InvolutionData μ) (f : Lp ℂ p μ) :
    conjugatePullback D (star f) = star (conjugatePullback D f) := by
  apply Lp.ext
  filter_upwards [coeFn_conjugatePullback D (star f),
    D.measurePreserving.quasiMeasurePreserving.ae (Lp.coeFn_star f),
    Lp.coeFn_star (conjugatePullback D f), coeFn_conjugatePullback D f] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.star_apply]

/-- A constant real scalar, as an actual native L∞ class. -/
def realConstant (a : ℝ) : Lp ℂ ∞ μ :=
  (memLp_top_const (a : ℂ)).toLp (fun _ : X ↦ (a : ℂ))

lemma coeFn_realConstant (a : ℝ) :
    realConstant (μ := μ) a =ᵐ[μ] fun _ ↦ (a : ℂ) :=
  MemLp.coeFn_toLp _

lemma conjugatePullback_realConstant (D : InvolutionData μ) (a : ℝ) :
    conjugatePullback D (realConstant a) = realConstant a := by
  apply Lp.ext
  filter_upwards [coeFn_conjugatePullback D (realConstant a),
    D.measurePreserving.quasiMeasurePreserving.ae (coeFn_realConstant (μ := μ) a),
    coeFn_realConstant (μ := μ) a] with x h1 h2 h3
  simp only [h1, h2, h3, Complex.star_def, Complex.conj_ofReal]

/-- Hölder multiplication restricted to its real fixed subspaces. -/
def fixedHolder [ENNReal.HolderTriple p q r] (D : InvolutionData μ)
    (f : Fixed D p) (g : Fixed D q) : Fixed D r :=
  ⟨(ContinuousLinearMap.mul ℂ ℂ).holder r f.val g.val, by
    change conjugatePullback D ((ContinuousLinearMap.mul ℂ ℂ).holder r f.val g.val) =
      (ContinuousLinearMap.mul ℂ ℂ).holder r f.val g.val
    have hf : conjugatePullback D f.val = f.val := f.property
    have hg : conjugatePullback D g.val = g.val := g.property
    rw [conjugatePullback_holder, hf, hg]⟩

/-- Pointwise multiplication of fixed essentially bounded classes. -/
def fixedProduct (D : InvolutionData μ) (f g : Fixed D ∞) : Fixed D ∞ :=
  fixedHolder D f g

/-- The native star, restricted to the actual fixed subspace. -/
def fixedStar (D : InvolutionData μ) (f : Fixed D p) : Fixed D p :=
  ⟨star f.val, by
    change conjugatePullback D (star f.val) = star f.val
    have hf : conjugatePullback D f.val = f.val := f.property
    rw [conjugatePullback_star, hf]⟩

/-- A real constant class in the real form of L∞. -/
def fixedConstant (D : InvolutionData μ) (a : ℝ) : Fixed D ∞ :=
  ⟨realConstant a, conjugatePullback_realConstant D a⟩

instance fixedMul (D : InvolutionData μ) : Mul (Fixed D ∞) := ⟨fixedProduct D⟩
instance fixedOne (D : InvolutionData μ) : One (Fixed D ∞) := ⟨fixedConstant D 1⟩
instance fixedStarInst (D : InvolutionData μ) : Star (Fixed D p) := ⟨fixedStar D⟩

lemma coeFn_fixedProduct (D : InvolutionData μ) (f g : Fixed D ∞) :
    (f * g).val =ᵐ[μ] fun x ↦ f.val x * g.val x :=
  (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder f.val g.val

lemma coeFn_fixedOne (D : InvolutionData μ) :
    (1 : Fixed D ∞).val =ᵐ[μ] fun _ ↦ (1 : ℂ) := by
  change realConstant (μ := μ) 1 =ᵐ[μ] fun _ ↦ (1 : ℂ)
  simpa only [Complex.ofReal_one] using coeFn_realConstant (μ := μ) 1

lemma coeFn_fixedStar (D : InvolutionData μ) (f : Fixed D p) :
    (star f).val =ᵐ[μ] fun x ↦ star (f.val x) := Lp.coeFn_star f.val

instance fixedCommRing (D : InvolutionData μ) : CommRing (Fixed D ∞) where
  __ := (inferInstance : AddCommGroup (Fixed D ∞))
  mul := (· * ·)
  one := 1
  mul_assoc f g h := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedProduct D (f*g) h, coeFn_fixedProduct D f g,
      coeFn_fixedProduct D f (g*h), coeFn_fixedProduct D g h] with x h1 h2 h3 h4
    simp only [h1, h2, h3, h4, mul_assoc]
  one_mul f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedProduct D 1 f, coeFn_fixedOne D] with x h1 h2
    simp only [h1, h2, one_mul]
  mul_one f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedProduct D f 1, coeFn_fixedOne D] with x h1 h2
    simp only [h1, h2, mul_one]
  left_distrib f g h := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedProduct D f (g+h), Lp.coeFn_add g.val h.val,
      coeFn_fixedProduct D f g, coeFn_fixedProduct D f h,
      Lp.coeFn_add (f*g).val (f*h).val] with x h1 h2 h3 h4 h5
    change (g+h).val x = g.val x + h.val x at h2
    change (f*g+f*h).val x = (f*g).val x + (f*h).val x at h5
    simp only [h1, h2, h3, h4, h5, mul_add]
  right_distrib f g h := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedProduct D (f+g) h, Lp.coeFn_add f.val g.val,
      coeFn_fixedProduct D f h, coeFn_fixedProduct D g h,
      Lp.coeFn_add (f*h).val (g*h).val] with x h1 h2 h3 h4 h5
    change (f+g).val x = f.val x + g.val x at h2
    change (f*h+g*h).val x = (f*h).val x + (g*h).val x at h5
    simp only [h1, h2, h3, h4, h5, add_mul]
  zero_mul f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedProduct D 0 f, Lp.coeFn_zero (E := ℂ) (p := ∞) (μ := μ)] with x h1 h2
    change (0 : Fixed D ∞).val x = (0 : ℂ) at h2
    simp only [h1, h2, zero_mul]
  mul_zero f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedProduct D f 0, Lp.coeFn_zero (E := ℂ) (p := ∞) (μ := μ)] with x h1 h2
    change (0 : Fixed D ∞).val x = (0 : ℂ) at h2
    simp only [h1, h2, mul_zero]
  mul_comm f g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedProduct D f g, coeFn_fixedProduct D g f] with x h1 h2
    simp only [h1, h2, mul_comm]


instance fixedInvolutiveStar (D : InvolutionData μ) : InvolutiveStar (Fixed D p) where
  star_involutive f := by
    apply Subtype.ext
    exact star_star f.val

instance fixedStarRing (D : InvolutionData μ) : StarRing (Fixed D ∞) where
  star_involutive := (fixedInvolutiveStar D).star_involutive
  star_mul f g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedStar D (f*g), coeFn_fixedProduct D f g,
      coeFn_fixedProduct D (star g) (star f), coeFn_fixedStar D f,
      coeFn_fixedStar D g] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, star_mul]
  star_add f g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedStar D (f+g), Lp.coeFn_add f.val g.val,
      Lp.coeFn_add (star f).val (star g).val,
      coeFn_fixedStar D f, coeFn_fixedStar D g] with x h1 h2 h3 h4 h5
    change (f+g).val x = f.val x + g.val x at h2
    change (star f+star g).val x = (star f).val x + (star g).val x at h3
    simp only [h1, h2, h3, h4, h5, star_add]

instance fixedAlgebra (D : InvolutionData μ) : Algebra ℝ (Fixed D ∞) :=
  Algebra.ofModule
    (fun a f g ↦ by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [coeFn_fixedProduct D (a • f) g, Lp.coeFn_smul a f.val,
        Lp.coeFn_smul a (f*g).val, coeFn_fixedProduct D f g] with x h1 h2 h3 h4
      change (a • f).val x = a • f.val x at h2
      change (a • (f*g)).val x = a • (f*g).val x at h3
      rw [h1, h2, h3, h4]
      exact smul_mul_assoc a (f.val x) (g.val x))
    (fun a f g ↦ by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [coeFn_fixedProduct D f (a • g), Lp.coeFn_smul a g.val,
        Lp.coeFn_smul a (f*g).val, coeFn_fixedProduct D f g] with x h1 h2 h3 h4
      change (a • g).val x = a • g.val x at h2
      change (a • (f*g)).val x = a • (f*g).val x at h3
      rw [h1, h2, h3, h4]
      exact mul_smul_comm a (f.val x) (g.val x))

instance fixedStarModule (D : InvolutionData μ) : StarModule ℝ (Fixed D p) where
  star_smul a f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedStar D (a • f), Lp.coeFn_smul a f.val,
      Lp.coeFn_smul (star a) (star f).val, coeFn_fixedStar D f] with x h1 h2 h3 h4
    change (a • f).val x = a • f.val x at h2
    change (star a • star f).val x = star a • (star f).val x at h3
    simp only [h1, h2, h3, h4, star_smul]

instance fixedNormedCommRing (D : InvolutionData μ) : NormedCommRing (Fixed D ∞) where
  __ := (inferInstance : NormedAddCommGroup (Fixed D ∞))
  __ := fixedCommRing D
  norm_mul_le f g := by
    change ‖(ContinuousLinearMap.mul ℂ ℂ).holder ∞ f.val g.val‖ ≤ ‖f.val‖ * ‖g.val‖
    simpa using (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le f.val g.val

instance fixedStarAddMonoid (D : InvolutionData μ) : StarAddMonoid (Fixed D p) where
  star_involutive := (fixedInvolutiveStar D).star_involutive
  star_add f g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_fixedStar D (f+g), Lp.coeFn_add f.val g.val,
      Lp.coeFn_add (star f).val (star g).val,
      coeFn_fixedStar D f, coeFn_fixedStar D g] with x h1 h2 h3 h4 h5
    change (f+g).val x = f.val x + g.val x at h2
    change (star f+star g).val x = (star f).val x + (star g).val x at h3
    simp only [h1, h2, h3, h4, h5, star_add]

instance fixedNormedStarGroup [Fact (1 ≤ p)] (D : InvolutionData μ) : NormedStarGroup (Fixed D p) where
  norm_star_le f := by
    change ‖star f.val‖ ≤ ‖f.val‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f.val)]
    change (eLpNorm (star (f.val : X → ℂ)) p μ).toReal ≤ _
    rw [eLpNorm_star]


/-- Existing native L∞ multiplier preserves the fixed native L² subspace. -/
theorem multiplier_preserves (D : InvolutionData μ) (f : Fixed D ∞)
    (u : Lp ℂ 2 μ) (hu : u ∈ fixedSubmodule D 2) :
    ScalarMultiplicationCommutant.Spec.multiplier μ f.val u ∈ fixedSubmodule D 2 := by
  change (ContinuousLinearMap.mul ℂ ℂ).holder 2 f.val u ∈ fixedSubmodule D 2
  exact (fixedHolder D f ⟨u, hu⟩).property

/-- Restriction of the shared native multiplier, as a real bounded operator. -/
def restrictedMultiplier (D : InvolutionData μ) (f : Fixed D ∞) :
    Fixed D 2 →L[ℝ] Fixed D 2 :=
  ((ScalarMultiplicationCommutant.Spec.multiplier μ f.val).restrictScalars ℝ).restrict
    (multiplier_preserves D f)

@[simp] theorem restrictedMultiplier_val (D : InvolutionData μ) (f : Fixed D ∞) (u : Fixed D 2) :
    (restrictedMultiplier D f u).val = ScalarMultiplicationCommutant.Spec.multiplier μ f.val u.val :=
  rfl

theorem coeFn_restrictedMultiplier (D : InvolutionData μ) (f : Fixed D ∞) (u : Fixed D 2) :
    (restrictedMultiplier D f u).val =ᵐ[μ] fun x ↦ f.val x * u.val x :=
  (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder f.val u.val

theorem restrictedMultiplier_one (D : InvolutionData μ) :
    restrictedMultiplier D 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [coeFn_restrictedMultiplier D 1 u, coeFn_fixedOne D] with x h1 h2
  change (restrictedMultiplier D 1 u).val x = u.val x
  simp only [h1, h2, one_mul]

theorem restrictedMultiplier_product (D : InvolutionData μ) (f g : Fixed D ∞) :
    restrictedMultiplier D (f*g) = restrictedMultiplier D f * restrictedMultiplier D g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [coeFn_restrictedMultiplier D (f*g) u, coeFn_fixedProduct D f g,
    coeFn_restrictedMultiplier D f (restrictedMultiplier D g u),
    coeFn_restrictedMultiplier D g u] with x h1 h2 h3 h4
  change (restrictedMultiplier D (f*g) u).val x =
    (restrictedMultiplier D f (restrictedMultiplier D g u)).val x
  simp only [h1, h2, h3, h4, mul_assoc]

theorem restrictedMultiplier_add (D : InvolutionData μ) (f g : Fixed D ∞) :
    restrictedMultiplier D (f+g) = restrictedMultiplier D f + restrictedMultiplier D g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [coeFn_restrictedMultiplier D (f+g) u, Lp.coeFn_add f.val g.val,
    coeFn_restrictedMultiplier D f u, coeFn_restrictedMultiplier D g u,
    Lp.coeFn_add (restrictedMultiplier D f u).val (restrictedMultiplier D g u).val]
    with x h1 h2 h3 h4 h5
  change (f+g).val x = f.val x + g.val x at h2
  change (restrictedMultiplier D (f+g) u).val x =
    (restrictedMultiplier D f u + restrictedMultiplier D g u).val x
  change (restrictedMultiplier D f u + restrictedMultiplier D g u).val x =
    (restrictedMultiplier D f u).val x + (restrictedMultiplier D g u).val x at h5
  simp only [h1, h2, h3, h4, h5, add_mul]

theorem restrictedMultiplier_real_smul (D : InvolutionData μ) (a : ℝ) (f : Fixed D ∞) :
    restrictedMultiplier D (a • f) = a • restrictedMultiplier D f := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [coeFn_restrictedMultiplier D (a • f) u, Lp.coeFn_smul a f.val,
    coeFn_restrictedMultiplier D f u, Lp.coeFn_smul a (restrictedMultiplier D f u).val]
    with x h1 h2 h3 h4
  change (a • f).val x = a • f.val x at h2
  change (a • restrictedMultiplier D f u).val x = a • (restrictedMultiplier D f u).val x at h4
  change (restrictedMultiplier D (a • f) u).val x = (a • restrictedMultiplier D f u).val x
  rw [h1, h2, h4, h3]
  exact smul_mul_assoc a (f.val x) (u.val x)


@[simp] theorem fixed_algebraMap (D : InvolutionData μ) (a : ℝ) :
    algebraMap ℝ (Fixed D ∞) a = fixedConstant D a := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul a (1 : Fixed D ∞).val,
    coeFn_fixedOne D, coeFn_realConstant (μ := μ) a] with x h1 h2 h3
  change (a • (1 : Fixed D ∞)).val x = (fixedConstant D a).val x
  change (a • (1 : Fixed D ∞)).val x = a • (1 : Fixed D ∞).val x at h1
  change (fixedConstant D a).val x = (a : ℂ) at h3
  simp only [h1, h2, h3, Complex.real_smul, mul_one]

/-- The canonical restricted action is an ordinary real algebra representation. -/
def multiplierAlgebraHom (D : InvolutionData μ) :
    Fixed D ∞ →ₐ[ℝ] (Fixed D 2 →L[ℝ] Fixed D 2) where
  toFun := restrictedMultiplier D
  map_one' := restrictedMultiplier_one D
  map_mul' := restrictedMultiplier_product D
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coeFn_restrictedMultiplier D 0 u,
      Lp.coeFn_zero (E := ℂ) (p := ∞) (μ := μ),
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x h1 h2 h3
    change (0 : Fixed D ∞).val x = (0 : ℂ) at h2
    change (0 : Fixed D 2).val x = (0 : ℂ) at h3
    change (restrictedMultiplier D 0 u).val x = (0 : Fixed D 2).val x
    simp only [h1, h2, h3, zero_mul]
  map_add' := restrictedMultiplier_add D
  commutes' a := by
    change restrictedMultiplier D (a • (1 : Fixed D ∞)) = a • (1 : Fixed D 2 →L[ℝ] Fixed D 2)
    rw [restrictedMultiplier_real_smul, restrictedMultiplier_one]

/-- Every product, star and scalar is the restriction of the native complex operation. -/
def AlgebraLaws : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) (D : InvolutionData μ),
    (∀ f g : Fixed D ∞,
      (f*g).val = (ContinuousLinearMap.mul ℂ ℂ).holder ∞ f.val g.val) ∧
    (∀ f : Fixed D ∞, (star f).val = star f.val) ∧
    (1 : Fixed D ∞).val = realConstant 1 ∧
    (∀ a : ℝ, algebraMap ℝ (Fixed D ∞) a = fixedConstant D a) ∧
    (∀ f g : Fixed D ∞, ‖f*g‖ ≤ ‖f‖ * ‖g‖) ∧
    (∀ f : Fixed D ∞, ‖star f‖ = ‖f‖)

/-- The real action uses the shared actual native L∞ multiplication operator. -/
def MultiplierLaws : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) (D : InvolutionData μ),
    (∀ (f : Fixed D ∞) (u : Lp ℂ 2 μ), u ∈ fixedSubmodule D 2 →
      ScalarMultiplicationCommutant.Spec.multiplier μ f.val u ∈ fixedSubmodule D 2) ∧
    (∀ (f : Fixed D ∞) (u : Fixed D 2),
      (restrictedMultiplier D f u).val = ScalarMultiplicationCommutant.Spec.multiplier μ f.val u.val) ∧
    restrictedMultiplier D 1 = 1 ∧
    (∀ f g : Fixed D ∞, restrictedMultiplier D (f*g) = restrictedMultiplier D f * restrictedMultiplier D g) ∧
    (∀ f g : Fixed D ∞, restrictedMultiplier D (f+g) = restrictedMultiplier D f + restrictedMultiplier D g) ∧
    (∀ (a : ℝ) (f : Fixed D ∞), restrictedMultiplier D (a • f) = a • restrictedMultiplier D f)


end ExpandedFA.VonNeumann.RealAbelianComplexification.Spec.NativeLp

namespace ExpandedFA.VonNeumann.RealAbelianComplexification.Spec
open NativeLp
universe u v

def NativeLpProductType :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X},
    (D : InvolutionData μ) → Fixed D ∞ → Fixed D ∞ → Fixed D ∞

def NativeLpStarType :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞},
    (D : InvolutionData μ) → Fixed D p → Fixed D p

def NativeLpMultiplierType :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X},
    (D : InvolutionData μ) → Fixed D ∞ → Fixed D 2 →L[ℝ] Fixed D 2

def NativeLpMultiplierRepresentationType :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X},
    (D : InvolutionData μ) → Fixed D ∞ →ₐ[ℝ] (Fixed D 2 →L[ℝ] Fixed D 2)

def NativeLpAlgebraMultiplier : Prop := AlgebraLaws.{u} ∧ MultiplierLaws.{u}

/-- The entire assigned result, retaining the original spaces, operators,
scalar-matching topologies and native involution-fixed real forms. -/
def CompleteResult : Prop :=
  OperatorDecomposition.{u} ∧ ConjugationLaws.{u} ∧ FixedOperators.{u} ∧
  ConjugationStar.{u} ∧ AlgebraCarrier.{u} ∧ AlgebraFixedPoints.{u} ∧
  Commutants.{u} ∧ GeneratedDoubleCommutants.{u} ∧
  StrongExtension.{u, v} ∧ WeakExtension.{u, v} ∧ ExtractionContinuous.{u} ∧
  ClosedAlgebras.{u} ∧ MASATransport.{u} ∧ CyclicSeparatingTransport.{u} ∧ Separability.{u} ∧
  NativeLpFoundation.{u} ∧ NativeLpHilbertPairing.{u} ∧ NativeLpAlgebraMultiplier.{u}
end ExpandedFA.VonNeumann.RealAbelianComplexification.Spec
