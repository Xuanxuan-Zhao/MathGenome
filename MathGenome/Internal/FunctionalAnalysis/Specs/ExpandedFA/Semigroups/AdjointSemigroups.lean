import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjoint
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Operator.Mul

/-! Independent statements for the adjoint clauses of `fa2:p3:adjoint-semigroup`
and the translation counterexample at `fa2:p3:growth-spectral-gap`.
The adjoint is the scalar-linear transpose. Reflexivity means surjectivity of
canonical evaluation into the continuous bidual, not algebraic reflexivity.
-/
noncomputable section
open Filter Topology
open scoped NNReal

namespace ExpandedFA.Semigroups.AdjointSemigroupsSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Transpose of a bounded map, with its usual dual operator norm. -/
def transpose (U : X →L[𝕜] X) : (X →L[𝕜] 𝕜) →L[𝕜] (X →L[𝕜] 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 X X 𝕜).flip U

def adjointOperators (T : C0Semigroup 𝕜 X) (t : ℝ≥0) := transpose (T.operators t)

/-- The exact canonical notion of Banach reflexivity. -/
def Reflexive : Prop := Function.Surjective
  (ContinuousLinearMap.apply 𝕜 𝕜 : X →L[𝕜] (X →L[𝕜] 𝕜) →L[𝕜] 𝕜)

def SemigroupLaws : Prop := ∀ T : C0Semigroup 𝕜 X,
  adjointOperators T 0 = ContinuousLinearMap.id 𝕜 (X →L[𝕜] 𝕜) ∧
  ∀ t s, adjointOperators T (t + s) =
    (adjointOperators T t).comp (adjointOperators T s)

/-- Both each time map and each orbit are continuous for the weak-star topology. -/
def WeakStarContinuity : Prop := ∀ T : C0Semigroup 𝕜 X,
  (∀ t : ℝ≥0, Continuous (fun q : WeakDual 𝕜 X =>
    StrongDual.toWeakDual (q.toStrongDual.comp (T.operators t)))) ∧
  ∀ q : X →L[𝕜] 𝕜, Continuous (fun t : ℝ≥0 =>
    StrongDual.toWeakDual (adjointOperators T t q))

def ReflexiveStrongContinuity : Prop := Reflexive (𝕜 := 𝕜) (X := X) →
  ∀ (T : C0Semigroup 𝕜 X) (q : X →L[𝕜] 𝕜),
    Tendsto (fun h : ℝ => adjointOperators T h.toNNReal q) (𝓝[>] 0) (𝓝 q)

/-- The full conclusion includes equality of partial linear maps, hence equality
of their exact domains. No density of the adjoint domain is assumed. -/
def ReflexiveGenerator : Prop := Reflexive (𝕜 := 𝕜) (X := X) →
  ∀ T : C0Semigroup 𝕜 X, ∃ S : C0Semigroup 𝕜 (X →L[𝕜] 𝕜),
    S.operators = adjointOperators T ∧
    C0SemigroupSpec.generatorValue S =
      Unbounded.BanachAdjointSpec.adjointValue (C0SemigroupSpec.generatorValue T)

section Translations
open MeasureTheory
open scoped ENNReal

/-- Lebesgue translations with convention τ_h f(x) = f(x-h). -/
def lpTranslate (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℝ) :
    Lp 𝕜 p (volume : Measure ℝ) →L[𝕜] Lp 𝕜 p (volume : Measure ℝ) :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 (fun x : ℝ => x - h)
    (measurePreserving_sub_right volume h)).toContinuousLinearMap

/-- The scalar-linear integral realization of an L∞ function in (L¹)'. -/
def linftyToDual : Lp 𝕜 ∞ (volume : Measure ℝ) →L[𝕜]
    (Lp 𝕜 1 (volume : Measure ℝ) →L[𝕜] 𝕜) :=
  (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing volume ∞ 1

def halfLineFunction (x : ℝ) : 𝕜 := (Set.Ici (0 : ℝ)).indicator (fun _ => (1 : 𝕜)) x

theorem halfLine_memLp : MemLp (halfLineFunction (𝕜 := 𝕜)) ∞ (volume : Measure ℝ) := by
  apply memLp_top_of_bound
    ((stronglyMeasurable_const.indicator measurableSet_Ici).aestronglyMeasurable) 1
  filter_upwards [] with x
  by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx]

def halfLine : Lp 𝕜 ∞ (volume : Measure ℝ) :=
  halfLine_memLp.toLp (halfLineFunction (𝕜 := 𝕜))

def TranslationPrimal : Prop := ∃ T : C0Semigroup 𝕜 (Lp 𝕜 1 (volume : Measure ℝ)),
  T.operators = fun t : ℝ≥0 => lpTranslate (𝕜 := 𝕜) 1 (t : ℝ)

/-- The sign reverses under the scalar-linear integral pairing. -/
def TranslationAdjoint : Prop := ∀ (h : ℝ) (g : Lp 𝕜 ∞ (volume : Measure ℝ)),
  (linftyToDual g).comp (lpTranslate 1 h) = linftyToDual (lpTranslate ∞ (-h) g)

/-- The same step-function distance holds both in L∞ and in the actual normed dual. -/
def TranslationStepDistance : Prop := ∀ h : ℝ, h ≠ 0 →
  ‖lpTranslate ∞ h (halfLine (𝕜 := 𝕜)) - halfLine‖ = 1 ∧
  ‖linftyToDual (lpTranslate ∞ h (halfLine (𝕜 := 𝕜))) - linftyToDual halfLine‖ = 1

def TranslationNotStrong : Prop :=
  ¬ Tendsto (fun h : ℝ =>
      (linftyToDual (halfLine (𝕜 := 𝕜))).comp (lpTranslate 1 h))
    (𝓝[>] 0) (𝓝 (linftyToDual (halfLine (𝕜 := 𝕜))))

/-- A concrete C₀ semigroup whose actual dual orbit fails norm continuity,
with the integral model of its adjoint action specified for every L∞ vector. -/
def TranslationCounterexample : Prop :=
  ∃ T : C0Semigroup 𝕜 (Lp 𝕜 1 (volume : Measure ℝ)),
    T.operators = (fun t : ℝ≥0 => lpTranslate (𝕜 := 𝕜) 1 (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (g : Lp 𝕜 ∞ (volume : Measure ℝ)),
      adjointOperators T t (linftyToDual g) = linftyToDual (lpTranslate ∞ (-(t : ℝ)) g)) ∧
    ¬ Tendsto (fun h : ℝ => adjointOperators T h.toNNReal
        (linftyToDual (halfLine (𝕜 := 𝕜))))
      (𝓝[>] 0) (𝓝 (linftyToDual (halfLine (𝕜 := 𝕜))))

end Translations
end ExpandedFA.Semigroups.AdjointSemigroupsSpec

namespace ExpandedFA.Semigroups.AdjointSemigroupsSpec.Expected

def SemigroupLaws : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  AdjointSemigroupsSpec.SemigroupLaws (𝕜 := 𝕜) (X := X)

def WeakStarContinuity : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  AdjointSemigroupsSpec.WeakStarContinuity (𝕜 := 𝕜) (X := X)

def ReflexiveStrongContinuity : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  AdjointSemigroupsSpec.ReflexiveStrongContinuity (𝕜 := 𝕜) (X := X)

def ReflexiveGenerator : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  AdjointSemigroupsSpec.ReflexiveGenerator (𝕜 := 𝕜) (X := X)

def TranslationPrimal : Prop := ∀ {𝕜 : Type*} [RCLike 𝕜],
  AdjointSemigroupsSpec.TranslationPrimal (𝕜 := 𝕜)

def TranslationAdjoint : Prop := ∀ {𝕜 : Type*} [RCLike 𝕜],
  AdjointSemigroupsSpec.TranslationAdjoint (𝕜 := 𝕜)

def TranslationStepDistance : Prop := ∀ {𝕜 : Type*} [RCLike 𝕜],
  AdjointSemigroupsSpec.TranslationStepDistance (𝕜 := 𝕜)

def TranslationNotStrong : Prop := ∀ {𝕜 : Type*} [RCLike 𝕜],
  AdjointSemigroupsSpec.TranslationNotStrong (𝕜 := 𝕜)

def TranslationCounterexample : Prop := ∀ {𝕜 : Type*} [RCLike 𝕜],
  AdjointSemigroupsSpec.TranslationCounterexample (𝕜 := 𝕜)

end ExpandedFA.Semigroups.AdjointSemigroupsSpec.Expected
