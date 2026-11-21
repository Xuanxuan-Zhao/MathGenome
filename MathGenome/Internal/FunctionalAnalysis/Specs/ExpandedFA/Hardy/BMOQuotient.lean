import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Independent specification of paper.tex:18406–18430. Scalars include both ℝ and ℂ.
Balls are Euclidean balls, not the balls for the coordinate supremum norm.
All equivalences are almost everywhere: changing a function on a null set does
not change the BMO class. The logarithm is assigned the harmless value 0 at the
origin by `Real.log 0`; its required local integrability includes the origin.

The extended seminorm retains infinite oscillation before membership is proved.
The final construction proposition requests actual Banach space structures on
the explicit quotient, the stated norm formula, the induced vector operations,
and a bounded linear map from L∞ with the expected representatives. These
structures and results are obligations, not supplied certificates.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.Hardy.BMOQuotientSpec

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def MeanType := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜],
  (Point d → 𝕜) → Point d → ℝ → 𝕜

def MeanValue : MeanType := fun f x r =>
  (volume.real (Metric.ball x r))⁻¹ • ∫ y in Metric.ball x r, f y

def MeanOscillationType := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜],
  (Point d → 𝕜) → Point d → ℝ → ℝ≥0∞

def MeanOscillationValue : MeanOscillationType := fun f x r =>
  (volume (Metric.ball x r))⁻¹ *
    ∫⁻ y in Metric.ball x r, ‖f y - MeanValue f x r‖ₑ

def BMOENormType := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜], (Point d → 𝕜) → ℝ≥0∞

def BMOENormValue : BMOENormType := fun f =>
  ⨆ x, ⨆ r : ℝ, ⨆ (_ : 0 < r), MeanOscillationValue f x r

def BMOFunctionType := ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜], Type

def BMOFunctionValue : BMOFunctionType := fun d 𝕜 _ =>
  {f : Point d → 𝕜 // LocallyIntegrable f volume ∧ BMOENormValue f < ∞}

def ModConstantsType := ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜],
  BMOFunctionValue d 𝕜 → BMOFunctionValue d 𝕜 → Prop

def ModConstantsValue : ModConstantsType := fun f g =>
  ∃ c, ∀ᵐ x ∂volume, f.val x = g.val x + c

/-- The quotient relation identifies constants and null-set changes. -/
def modConstantsSetoid (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    Setoid (BMOFunctionValue d 𝕜) where
  r := ModConstantsValue
  iseqv := {
    refl := fun f => ⟨0, Filter.Eventually.of_forall (fun _ => by simp)⟩
    symm := by
      rintro f g ⟨c, hc⟩
      refine ⟨-c, hc.mono ?_⟩
      intro x hx
      rw [hx]
      simp
    trans := by
      rintro f g h ⟨c, hc⟩ ⟨e, he⟩
      refine ⟨e + c, ?_⟩
      filter_upwards [hc, he] with x hx hxx
      rw [hx, hxx, add_assoc] }

def BMOType := ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜], Type

def BMOValue : BMOType := fun d 𝕜 _ => Quotient (modConstantsSetoid d 𝕜)

abbrev classOf {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : BMOFunctionValue d 𝕜) :
    BMOValue d 𝕜 := Quotient.mk _ f

/-- Equality on the explicit quotient, including null-set changes. -/
def QuotientEquality : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f g : BMOFunctionValue d 𝕜),
    classOf f = classOf g ↔ ModConstantsValue f g

def LogLocalIntegrability : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜], 0 < d →
    LocallyIntegrable (fun x : Point d => (Real.log ‖x‖ : 𝕜)) volume

def LogEssentialUnboundedness : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜], 0 < d →
    ¬ MemLp (fun x : Point d => (Real.log ‖x‖ : 𝕜)) ∞ volume

/-- This verifies the extended-integral convention against the displayed formula. -/
def OscillationFormula : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜),
    LocallyIntegrable f volume → ∀ x r, 0 < r →
      MeanOscillationValue f x r = ENNReal.ofReal
        ((volume.real (Metric.ball x r))⁻¹ *
          ∫ y in Metric.ball x r, ‖f y - MeanValue f x r‖)

def AeInvariance : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f g : Point d → 𝕜),
    f =ᵐ[volume] g → BMOENormValue f = BMOENormValue g

def ConstantInvariance : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜),
    LocallyIntegrable f volume → ∀ c : 𝕜,
      BMOENormValue (fun x => f x + c) = BMOENormValue f

def Definiteness : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜),
    LocallyIntegrable f volume →
      (BMOENormValue f = 0 ↔ ∃ c : 𝕜, f =ᵐ[volume] fun _ => c)

/-- The bounded-function estimate includes local integrability and uses the
usual essential-supremum norm. It is valid for a.e. representatives as well. -/
def BoundedInclusion : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜),
    MemLp f ∞ volume → LocallyIntegrable f volume ∧
      BMOENormValue f ≤ 2 * eLpNorm f ∞ volume

/-- Actual normed vector space structure on the prescribed quotient, not
merely the existence of an unrelated complete space. Vector operations are
specified on every representative. The map from L∞ need not be injective:
its kernel consists of the constants. -/
def BanachQuotient : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜],
    ∃ G : NormedAddCommGroup (BMOValue d 𝕜),
      letI := G
      ∃ S : NormedSpace 𝕜 (BMOValue d 𝕜),
        letI := S
        CompleteSpace (BMOValue d 𝕜) ∧
        (∀ f : BMOFunctionValue d 𝕜, ‖classOf f‖ = (BMOENormValue f.val).toReal) ∧
        (∀ f g : BMOFunctionValue d 𝕜,
          ∃ h : LocallyIntegrable (f.val + g.val) volume ∧
              BMOENormValue (f.val + g.val) < ∞,
            classOf ⟨f.val + g.val, h⟩ = classOf f + classOf g) ∧
        (∀ (c : 𝕜) (f : BMOFunctionValue d 𝕜),
          ∃ h : LocallyIntegrable (c • f.val) volume ∧
              BMOENormValue (c • f.val) < ∞,
            classOf ⟨c • f.val, h⟩ = c • classOf f) ∧
        ∃ T : Lp 𝕜 ∞ (volume : Measure (Point d)) →L[𝕜] BMOValue d 𝕜,
          ‖T‖ ≤ 2 ∧
          ∀ f : Lp 𝕜 ∞ (volume : Measure (Point d)),
            ∃ h : LocallyIntegrable (f : Point d → 𝕜) volume ∧
                BMOENormValue (f : Point d → 𝕜) < ∞,
              T f = classOf ⟨f, h⟩

/-- Positive dimension is necessary for the unbounded example. The formula
uses the ordinary Euclidean norm, with its value at zero explicitly retained. -/
def LogExample : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜],
    let f : Point d → 𝕜 := fun x => (Real.log ‖x‖ : 𝕜)
    LocallyIntegrable f volume ∧ BMOENormValue f < ∞ ∧
      ¬ MemLp f ∞ volume

end ExpandedFA.Hardy.BMOQuotientSpec
