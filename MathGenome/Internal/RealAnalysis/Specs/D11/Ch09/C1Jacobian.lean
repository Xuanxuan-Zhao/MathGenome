import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian

/-! Independent statements for paper.tex:3082–3174. The functions are ambient
extensions of maps on the open sets; their values outside those sets are
unrestricted. Measurability on a region always uses the trace of the full
Carathéodory Lebesgue sigma-algebra. Scalar identities require integrability. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch09.C1Jacobian
open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures

/-- The absolute determinant with the Euclidean derivative and normalization. -/
def jacobian {n : ℕ} (G : Point n → Point n) (x : Point n) : ℝ :=
  |(fderiv ℝ G x).det|

/-- Exactly an injective C¹ map on an open set with nonsingular derivative. -/
structure C1Hypotheses {n : ℕ} (U : Set (Point n)) (G : Point n → Point n) : Prop where
  isOpen : IsOpen U
  contDiff : ContDiffOn ℝ 1 G U
  injOn : InjOn G U
  det_ne_zero : ∀ x ∈ U, (fderiv ℝ G x).det ≠ 0

def open_image_inverse : Prop := ∀ (n : ℕ) [NeZero n]
    (U : Set (Point n)) (G : Point n → Point n), C1Hypotheses U G →
  IsOpen (G '' U) ∧ ∃ e : OpenPartialHomeomorph (Point n) (Point n),
    e.source = U ∧ (e : Point n → Point n) = G ∧
    e.target = G '' U ∧ ContDiffOn ℝ 1 e.symm e.target

def measurable_image : Prop := ∀ (n : ℕ) [NeZero n]
    (U : Set (Point n)) (G : Point n → Point n), C1Hypotheses U G →
  ∀ E ⊆ U, MeasurableSet[lebesgueSpace_value n] E →
    MeasurableSet[lebesgueSpace_value n] (G '' E)

def set_jacobian : Prop := ∀ (n : ℕ) [NeZero n]
    (U : Set (Point n)) (G : Point n → Point n), C1Hypotheses U G →
  ∀ E ⊆ U, MeasurableSet[lebesgueSpace_value n] E →
    lebesgue_value n (G '' E) =
      ∫⁻ x in E, ENNReal.ofReal (jacobian G x) ∂lebesgue_value n

/-- Arbitrary measurable targets include both nonnegative and scalar functions. -/
def completed_composition : Prop := ∀ (n : ℕ) [NeZero n]
    (U : Set (Point n)) (G : Point n → Point n), C1Hypotheses U G →
  ∀ (Y : Type) [MeasurableSpace Y] (h : Point n → Y),
    @Measurable (G '' U) Y
      (MeasurableSpace.comap Subtype.val (lebesgueSpace_value n)) _ ((G '' U).domRestrict h) →
    @Measurable U Y
      (MeasurableSpace.comap Subtype.val (lebesgueSpace_value n)) _ (U.domRestrict (h ∘ G))

def nonnegative_jacobian : Prop := ∀ (n : ℕ) [NeZero n]
    (U : Set (Point n)) (G : Point n → Point n), C1Hypotheses U G →
  letI : MeasurableSpace (Point n) := lebesgueSpace_value n
  ∀ (h : Point n → ℝ≥0∞), Measurable ((G '' U).domRestrict h) →
    Measurable (U.domRestrict (fun x => ENNReal.ofReal (jacobian G x) * h (G x))) ∧
    (∫⁻ y in G '' U, h y ∂lebesgue_value n) =
      ∫⁻ x in U, ENNReal.ofReal (jacobian G x) * h (G x) ∂lebesgue_value n

def scalar_integrable_iff : Prop := ∀ (n : ℕ) [NeZero n]
    (U : Set (Point n)) (G : Point n → Point n), C1Hypotheses U G →
  ∀ (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI : MeasurableSpace (Point n) := lebesgueSpace_value n
  ∀ (h : Point n → 𝕜), Measurable ((G '' U).domRestrict h) →
    Measurable (U.domRestrict (fun x => jacobian G x • h (G x))) ∧
    (IntegrableOn h (G '' U) (lebesgue_value n) ↔
      IntegrableOn (fun x => jacobian G x • h (G x)) U (lebesgue_value n))

def scalar_jacobian : Prop := ∀ (n : ℕ) [NeZero n]
    (U : Set (Point n)) (G : Point n → Point n), C1Hypotheses U G →
  ∀ (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI : MeasurableSpace (Point n) := lebesgueSpace_value n
  ∀ (h : Point n → 𝕜), Measurable ((G '' U).domRestrict h) →
    IntegrableOn h (G '' U) (lebesgue_value n) →
    IntegrableOn (fun x => jacobian G x • h (G x)) U (lebesgue_value n) ∧
    (∫ y in G '' U, h y ∂lebesgue_value n) =
      ∫ x in U, jacobian G x • h (G x) ∂lebesgue_value n

end Specs.D11.Ch09.C1Jacobian
