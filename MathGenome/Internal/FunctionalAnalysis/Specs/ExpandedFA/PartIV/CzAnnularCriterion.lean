import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.SmoothKernelMultiplierEquivalence
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.PointSupportedDistributions
import Mathlib.Analysis.Fourier.LpSpace

/-! Independent statements for `paper.tex`, fa2:p4:cz-annular-criterion,
20689–20756, with the standard-distribution convention at fa2:p4:cz-multiplier.
The dimension includes zero. Both real and complex scalar fields are covered; the real case is
identified with the canonical complexification of its scalar-linear LF dual. Annuli use the Euclidean norm and ordinary Lebesgue integrals.
A value assigned to the kernel at the origin has no role in off-zero agreement.
The operator assertion uses the same globally represented multiplier as K. -/

open MeasureTheory Set TopologicalSpace
open scoped SchwartzMap ContDiff FourierTransform

noncomputable section
namespace ExpandedFA.PartIV.CzAnnularCriterion
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples
open ExpandedFA.SingularIntegrals

/-- The hypotheses on the function, before any extension has been constructed. -/
def SmoothKernelBounds {d : ℕ} (k : Euclidean d → ℂ) : Prop :=
  ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)) ∧
    ∀ (n : ℕ) (w : Fin n → Fin d), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Euclidean d, x ≠ 0 →
        ‖iteratedFDeriv ℝ n k x (fun j => basisVector (w j))‖ ≤
          C * (‖x‖ ^ (d + n))⁻¹

/-- Uniform cancellation on every finite sharp annulus. Ordinary integrability
is included explicitly, so the totalized integral cannot hide a divergence. -/
def AnnularCancellation {d : ℕ} (k : Euclidean d → ℂ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ r R : ℝ, 0 < r → r < R →
    IntegrableOn k {x | r < ‖x‖ ∧ ‖x‖ < R} ∧
      ‖∫ x in {x | r < ‖x‖ ∧ ‖x‖ < R}, k x‖ ≤ A

/-- The standard CZ notion is the accepted global smooth bounded multiplier
condition, together with every physical kernel bound and off-zero agreement. -/
def StandardExtension {d : ℕ} (k : Euclidean d → ℂ) (K : KernelDistribution d) : Prop :=
  KernelBounds K k ∧ HasSmoothMultiplier K

abbrev L2 (d : ℕ) := Lp ℂ 2 (volume : Measure (Euclidean d))

/-- An actual bounded L² operator whose Fourier action is multiplication by
one globally represented multiplier of this very distribution. -/
def HasL2Realization {d : ℕ} (K : KernelDistribution d) : Prop :=
  ∃ (U : Tempered ℂ d) (m : Euclidean d → ℂ) (T : L2 d →L[ℂ] L2 d) (M : ℝ),
    ExtendsKernel U K ∧ BoundedFunction m ∧ FourierRepresentedBy U m ∧
    0 ≤ M ∧ (∀ ξ, ‖m ξ‖ ≤ M) ∧ ‖T‖ ≤ M ∧
      ∀ f : L2 d, (fun ξ => (𝓕 (T f) : L2 d) ξ) =ᵐ[volume]
        (fun ξ => m ξ * (𝓕 f : L2 d) ξ)

end ExpandedFA.PartIV.CzAnnularCriterion

namespace Specs.ExpandedFA.PartIV.CzAnnularCriterion
open _root_.ExpandedFA.PartIV.CzAnnularCriterion
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Fourier
open _root_.ExpandedFA.SingularIntegrals

/-- The entire affirmative zero-dimensional case: every annulus is empty,
and the zero distribution is an admissible extension of any off-zero kernel. -/
def zeroDimensionType : Prop := ∀ k : Euclidean 0 → ℂ,
  AnnularCancellation k ∧ ∃ K : KernelDistribution 0, StandardExtension k K

/-- Necessity already follows from bump cancellation and the physical kernel
bounds; it does not need the symbol derivative conclusions. -/
def necessityType : Prop := ∀ (d : ℕ) (K : KernelDistribution d) (k : Euclidean d → ℂ),
  KernelBounds K k → (∃ N : ℕ, BumpCancellation K N) → AnnularCancellation k

/-- Both directions of the original criterion, without an extension assumption
in the function's hypotheses. -/
def annularCriterionType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ),
  SmoothKernelBounds k →
    ((∃ K : KernelDistribution d, StandardExtension k K) ↔ AnnularCancellation k)

/-- The bump and L² assertions are conclusions, not extra assumptions on K. -/
def standardConsequencesType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ)
    (K : KernelDistribution d), StandardExtension k K →
  (∃ N : ℕ, d < N ∧ BumpCancellation K N) ∧ HasL2Realization K

/-- Eliminates every positive-order point-supported derivative in the difference.
The empty coordinate word is the already defined Dirac evaluation. -/
def uniquenessType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ)
    (K L : KernelDistribution d), StandardExtension k K → StandardExtension k L →
  ∃ c : ℂ, K - L = c • coordinateJet ℂ ⊤ (0 : Domain d) (Fin.elim0 : Fin 0 → Fin d)

/-- Every scalar Dirac ambiguity is permitted by the same standard conditions. -/
def diracStabilityType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ)
    (K : KernelDistribution d), StandardExtension k K → ∀ c : ℂ,
  StandardExtension k (K + c • coordinateJet ℂ ⊤ (0 : Domain d)
    (Fin.elim0 : Fin 0 → Fin d))

/-- The general local statement used for uniqueness. No kernel estimates are
needed: singleton support plus bounded bump dilations forces order zero. -/
def pointSupportBumpsType : Prop := ∀ (d N : ℕ) (u : KernelDistribution d),
  distributionSupport u ⊆ {0} → BumpCancellation u N →
  ∃ c : ℂ, u = c • coordinateJet ℂ ⊤ (0 : Domain d) (Fin.elim0 : Fin 0 → Fin d)

end Specs.ExpandedFA.PartIV.CzAnnularCriterion

namespace ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples

abbrev KernelDistribution (d : ℕ) := ScalarDistribution ℝ (⊤ : Opens (Domain d))

def ofRealTest {d : ℕ} : Tests ℝ (⊤ : Opens (Domain d)) →L[ℝ] Tests ℂ (⊤ : Opens (Domain d)) :=
  TestFunction.postcompCLM Complex.ofRealCLM

def realTest {d : ℕ} : Tests ℂ (⊤ : Opens (Domain d)) →L[ℝ] Tests ℝ (⊤ : Opens (Domain d)) :=
  TestFunction.postcompCLM Complex.reCLM

def imagTest {d : ℕ} : Tests ℂ (⊤ : Opens (Domain d)) →L[ℝ] Tests ℝ (⊤ : Opens (Domain d)) :=
  TestFunction.postcompCLM Complex.imCLM

@[simp] theorem ofRealTest_apply {d : ℕ} (φ : Tests ℝ (⊤ : Opens (Domain d))) (x : Domain d) :
    ofRealTest φ x = (φ x : ℂ) := rfl
@[simp] theorem realTest_apply {d : ℕ} (φ : Tests ℂ (⊤ : Opens (Domain d))) (x : Domain d) :
    realTest φ x = (φ x).re := rfl
@[simp] theorem imagTest_apply {d : ℕ} (φ : Tests ℂ (⊤ : Opens (Domain d))) (x : Domain d) :
    imagTest φ x = (φ x).im := rfl

/-- The complex-linear extension of a real scalar distribution, formed on the
real and imaginary parts of the original compact tests. -/
def complexify {d : ℕ} (u : KernelDistribution d) :
    ExpandedFA.SingularIntegrals.KernelDistribution d where
  toFun φ := (u (realTest φ) : ℂ) + Complex.I * (u (imagTest φ) : ℂ)
  map_add' φ ψ := by simp only [map_add, Complex.ofReal_add]; ring
  map_smul' c φ := by
    have hr : realTest (c • φ) = c.re • realTest φ - c.im • imagTest φ := by
      ext x
      simp [Complex.mul_re]
    have hi : imagTest (c • φ) = c.re • imagTest φ + c.im • realTest φ := by
      ext x
      simp [Complex.mul_im]
    rw [hr, hi]
    simp only [map_sub, map_add, map_smul, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_add, Complex.ofReal_mul, RingHom.id_apply]
    apply Complex.ext <;> simp
  cont := by
    exact ((Complex.ofRealCLM.continuous.comp (u.continuous.comp realTest.continuous))).add
      (continuous_const.mul (Complex.ofRealCLM.continuous.comp
        (u.continuous.comp imagTest.continuous)))

/-- The real part of a complex distribution evaluated on real tests. -/
def restrict {d : ℕ} (K : ExpandedFA.SingularIntegrals.KernelDistribution d) :
    KernelDistribution d :=
  Complex.reCLM.comp ((K.restrictScalars ℝ).comp ofRealTest)

def dilateTest {d : ℕ} (r : ℝ) (hr : r ≠ 0)
    (φ : Tests ℝ (⊤ : Opens (Domain d))) : Tests ℝ (⊤ : Opens (Domain d)) :=
  ⟨fun x => φ (r⁻¹ • x), φ.contDiff.comp (contDiff_id.const_smul r⁻¹),
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)),
    subset_univ _⟩

def NormalizedBump {d : ℕ} (N : ℕ) (φ : Tests ℝ (⊤ : Opens (Domain d))) : Prop :=
  tsupport (testSchwartz ℝ φ) ⊆ Metric.closedBall 0 1 ∧
    ∀ n ≤ N, ∀ x : Euclidean d, ‖iteratedFDeriv ℝ n (testSchwartz ℝ φ) x‖ ≤ 1

def BumpCancellation {d : ℕ} (u : KernelDistribution d) (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ φ, NormalizedBump N φ → ∀ r : ℝ, ∀ hr : 0 < r,
    ‖u (dilateTest r hr.ne' φ)‖ ≤ C

def AgreesOffZero {d : ℕ} (u : KernelDistribution d) (k : Euclidean d → ℝ) : Prop :=
  ∀ φ : Tests ℝ (⊤ : Opens (Domain d)), 0 ∉ tsupport (testSchwartz ℝ φ) →
    Integrable (fun x => k x * testSchwartz ℝ φ x) ∧
      u φ = ∫ x, k x * testSchwartz ℝ φ x
end ExpandedFA.PartIV.CzAnnularCriterion.RealScalar

namespace ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open ExpandedFA.Distributions ExpandedFA.Fourier ExpandedFA.Fourier.Examples

/-- The physical smoothness and size hypotheses for a real-valued kernel. -/
def SmoothKernelBounds {d : ℕ} (k : Euclidean d → ℝ) : Prop :=
  ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)) ∧
    ∀ (n : ℕ) (w : Fin n → Fin d), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Euclidean d, x ≠ 0 →
        ‖iteratedFDeriv ℝ n k x (fun j => basisVector (w j))‖ ≤
          C * (‖x‖ ^ (d + n))⁻¹

/-- Ordinary integrals on finite annuli, with their integrability explicit. -/
def AnnularCancellation {d : ℕ} (k : Euclidean d → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ r R : ℝ, 0 < r → r < R →
    IntegrableOn k {x | r < ‖x‖ ∧ ‖x‖ < R} ∧
      ‖∫ x in {x | r < ‖x‖ ∧ ‖x‖ < R}, k x‖ ≤ A

def KernelBounds {d : ℕ} (u : KernelDistribution d) (k : Euclidean d → ℝ) : Prop :=
  AgreesOffZero u k ∧ SmoothKernelBounds k

/-- A real CZ distribution has the standard bounded smooth multiplier after
canonical complexification. This retains the actual real LF distribution. -/
def StandardExtension {d : ℕ} (k : Euclidean d → ℝ) (u : KernelDistribution d) : Prop :=
  ExpandedFA.PartIV.CzAnnularCriterion.StandardExtension (fun x => (k x : ℂ)) (complexify u)

end ExpandedFA.PartIV.CzAnnularCriterion.RealScalar

namespace Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open _root_.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Fourier

def annularCriterionType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℝ),
  SmoothKernelBounds k →
    ((∃ u : KernelDistribution d, StandardExtension k u) ↔ AnnularCancellation k)

def uniquenessType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℝ)
    (u v : KernelDistribution d), StandardExtension k u → StandardExtension k v →
  ∃ c : ℝ, u - v = c • coordinateJet ℝ ⊤ (0 : Domain d) (Fin.elim0 : Fin 0 → Fin d)

def diracStabilityType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℝ)
    (u : KernelDistribution d), StandardExtension k u → ∀ c : ℝ,
  StandardExtension k (u + c • coordinateJet ℝ ⊤ (0 : Domain d)
    (Fin.elim0 : Fin 0 → Fin d))

def necessityType : Prop := ∀ (d : ℕ) (u : KernelDistribution d) (k : Euclidean d → ℝ),
  KernelBounds u k → (∃ N : ℕ, BumpCancellation u N) → AnnularCancellation k

def zeroDimensionType : Prop := ∀ k : Euclidean 0 → ℝ,
  AnnularCancellation k ∧ ∃ u : KernelDistribution 0, StandardExtension k u

end Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar

namespace ExpandedFA.PartIV.CzAnnularCriterion
open ExpandedFA.Fourier

abbrev RealL2 (d : ℕ) := Lp ℝ 2 (volume : Measure (Euclidean d))

def includeRealL2 (d : ℕ) : RealL2 d →L[ℝ] L2 d :=
  Complex.ofRealCLM.compLpL 2 volume

def projectRealL2 (d : ℕ) : L2 d →L[ℝ] RealL2 d :=
  Complex.reCLM.compLpL 2 volume

namespace RealScalar
open ExpandedFA.Distributions ExpandedFA.SingularIntegrals ExpandedFA.Fourier.Examples

/-- An actual real tempered extension on real Schwartz tests. -/
def HasTemperedExtension {d : ℕ} (u : KernelDistribution d) : Prop :=
  ∃ V : Tempered ℝ d, ∀ φ : Tests ℝ (⊤ : Opens (Domain d)), V (testSchwartz ℝ φ) = u φ

/-- A bounded real L² operator, obtained by restricting a complex multiplier
operator of this same distribution. The inclusion identity holds for every
real L² function; the globally represented multiplier is Hermitian. -/
def HasL2Realization {d : ℕ} (u : KernelDistribution d) : Prop :=
  ∃ (U : Tempered ℂ d) (m : Euclidean d → ℂ) (T : L2 d →L[ℂ] L2 d)
    (S : RealL2 d →L[ℝ] RealL2 d) (M : ℝ),
    ExtendsKernel U (complexify u) ∧ BoundedFunction m ∧ FourierRepresentedBy U m ∧
    (∀ ξ, starRingEnd ℂ (m (-ξ)) = m ξ) ∧
    0 ≤ M ∧ (∀ ξ, ‖m ξ‖ ≤ M) ∧ ‖T‖ ≤ M ∧ ‖S‖ ≤ M ∧
      (∀ f : L2 d, (fun ξ => (𝓕 (T f) : L2 d) ξ) =ᵐ[volume]
        (fun ξ => m ξ * (𝓕 f : L2 d) ξ)) ∧
      ∀ f : RealL2 d, includeRealL2 d (S f) = T (includeRealL2 d f)

end RealScalar
end ExpandedFA.PartIV.CzAnnularCriterion

namespace Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open _root_.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open _root_.ExpandedFA.Fourier

def standardConsequencesType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℝ)
    (u : KernelDistribution d), StandardExtension k u →
  KernelBounds u k ∧ HasTemperedExtension u ∧
    (∃ N : ℕ, d < N ∧ BumpCancellation u N) ∧ HasL2Realization u

end Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar

namespace Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open _root_.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Fourier

def pointSupportBumpsType : Prop := ∀ (d N : ℕ) (u : KernelDistribution d),
  distributionSupport u ⊆ {0} → BumpCancellation u N →
  ∃ c : ℝ, u = c • coordinateJet ℝ ⊤ (0 : Domain d) (Fin.elim0 : Fin 0 → Fin d)

/-- The real standard-distribution definition has precisely the physical
bump characterization used in the source. -/
def standardIffBumpsType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℝ)
    (u : KernelDistribution d), KernelBounds u k →
  (StandardExtension k u ↔ ∃ N : ℕ, d < N ∧ BumpCancellation u N)

end Specs.ExpandedFA.PartIV.CzAnnularCriterion.RealScalar
