import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionFiniteOrder
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-! Independent objects for the calculus part of `fa2:p4:distribution-calculus`.
Coefficients are smooth only on the open domain. Derivatives use coordinate
words, so all mixed partials, including order zero, are represented. -/
open Set TopologicalSpace
open scoped Distributions ContDiff

namespace ExpandedFA.Distributions

/-- A representative of a smooth scalar function on Ω; values off Ω are immaterial. -/
abbrev SmoothCoefficient (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :=
  {a : Domain d → 𝕜 // ContDiffOn ℝ ∞ a Ω}

/-- Ordered coordinate partial derivatives, with the empty word giving the function. -/
noncomputable def partialFunction {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    List (Fin d) → (Domain d → 𝕜) → (Domain d → 𝕜)
  | [], f => f
  | i :: w, f => fun x => fderiv ℝ (partialFunction w f) x (coordinateVector i)

/-- Coordinate differentiation on the LF test space. -/
noncomputable def testPartialCLM {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} : List (Fin d) → Tests 𝕜 Ω →L[𝕜] Tests 𝕜 Ω
  | [] => ContinuousLinearMap.id 𝕜 _
  | i :: w => (TestFunction.lineDerivCLM 𝕜 (coordinateVector i)).comp (testPartialCLM w)

/-- The coordinate word for the ordinary multi-index α, in coordinate order. -/
def multiIndexWord {d : ℕ} (α : Fin d → ℕ) : List (Fin d) :=
  (List.ofFn (fun i : Fin d => i)).flatMap (fun i => List.replicate (α i) i)

/-- Coordinate differentiation preserves local smoothness. -/
noncomputable def coefficientPartial {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (i : Fin d) (a : SmoothCoefficient 𝕜 Ω) :
    SmoothCoefficient 𝕜 Ω :=
  ⟨fun x => fderiv ℝ a.val x (coordinateVector i),
    (a.property.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const⟩

/-- A locally finite scalar Radon measure, presented by its finite restrictions
to compact subsets of Ω. Each chart is an actual countably additive scalar
measure of finite variation, and compatibility is equality of measures, not an
assumed continuity property of test integrals. This presentation allows infinite
total mass on Ω. Finite Borel measures on Euclidean space are Radon. -/
structure LocalScalarRadonMeasure (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) where
  onCompact : ∀ (K : Compacts (Domain d)), (K : Set (Domain d)) ⊆ Ω →
    MeasureTheory.VectorMeasure (Domain d) 𝕜
  finiteVariation : ∀ K hK, MeasureTheory.IsFiniteMeasure (onCompact K hK).variation
  restrict_eq : ∀ K hK L hL, K ≤ L →
    (onCompact L hL).restrict K = onCompact K hK

/-- Integration against a local scalar measure uses the compact support of the
test. Independence of a larger compact is proved in the implementation. The
pairing is multiplication in 𝕜, with no complex conjugation. -/
noncomputable def localScalarMeasureIntegral {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (μ : LocalScalarRadonMeasure 𝕜 Ω) (φ : Tests 𝕜 Ω) : 𝕜 :=
  MeasureTheory.VectorMeasure.integral
    (μ.onCompact ⟨tsupport φ, φ.hasCompactSupport⟩ φ.tsupport_subset) φ
    (ContinuousLinearMap.mul ℝ 𝕜)

end ExpandedFA.Distributions

namespace Specs.ExpandedFA.Distributions.DistributionCalculus
open _root_.ExpandedFA.Distributions MeasureTheory

/-- Integration is scalar-linear and continuous for every locally integrable scalar
function, with respect to any positive Borel measure. In particular μ = volume
recovers the locally Lebesgue-integrable functions of the paper. -/
def integrationType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (μ : Measure (Domain d)) (f : Domain d → 𝕜),
  LocallyIntegrableOn f Ω μ → ∃ u : ScalarDistribution 𝕜 Ω,
    ∀ φ : Tests 𝕜 Ω, u φ = ∫ x, f x * φ x ∂μ

/-- Every locally finite scalar Radon measure, of either scalar field and with
no global finite-mass assumption, defines its integration distribution. -/
def scalarMeasureType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (μ : LocalScalarRadonMeasure 𝕜 Ω),
  ∃ u : ScalarDistribution 𝕜 Ω, ∀ φ, u φ = localScalarMeasureIntegral μ φ

def testPartialFormulaType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (w : List (Fin d)) (φ : Tests 𝕜 Ω),
  ⇑(testPartialCLM w φ) = partialFunction w φ

/-- Differentiation with its exact transpose sign and the original scalar-linear dual. -/
def derivativeType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (_w : List (Fin d)),
  ScalarDistribution 𝕜 Ω → ScalarDistribution 𝕜 Ω

noncomputable def derivativeValue : derivativeType :=
  fun 𝕜 _ _ _ w u => ((-1 : 𝕜) ^ w.length) • u.comp (testPartialCLM w)

def multiIndexDerivativeType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (_α : Fin d → ℕ),
  ScalarDistribution 𝕜 Ω → ScalarDistribution 𝕜 Ω

noncomputable def multiIndexDerivativeValue : multiIndexDerivativeType :=
  fun 𝕜 _ d Ω α u => derivativeValue 𝕜 d Ω (multiIndexWord α) u

/-- The exact multi-index sign, including the zero multi-index and dimension zero. -/
def multiIndexFormulaType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (α : Fin d → ℕ) (u : ScalarDistribution 𝕜 Ω) (φ : Tests 𝕜 Ω),
  multiIndexDerivativeValue 𝕜 d Ω α u φ =
    (-1 : 𝕜) ^ (∑ i, α i) * u (testPartialCLM (multiIndexWord α) φ)

/-- Multiplication acts on tests by the actual local smooth function. Its
continuity is part of the conclusion, not a hypothesis on the coefficient. -/
def testMultiplicationType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (a : SmoothCoefficient 𝕜 Ω),
  ∃ M : Tests 𝕜 Ω →L[𝕜] Tests 𝕜 Ω,
    ∀ φ x, M φ x = a.val x * φ x

/-- The actual distribution product has the prescribed scalar-linear pairing. -/
def multiplicationType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (a : SmoothCoefficient 𝕜 Ω) (u : ScalarDistribution 𝕜 Ω),
  ∃ v : ScalarDistribution 𝕜 Ω, ∀ φ : Tests 𝕜 Ω,
    ∃ ψ : Tests 𝕜 Ω, (∀ x, ψ x = a.val x * φ x) ∧ v φ = u ψ

/-- The first-order Leibniz rule. Higher-order rules follow by iteration; the
word-indexed derivative includes every coordinate multi-index. -/
def leibnizType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (a : SmoothCoefficient 𝕜 Ω)
    (u : ScalarDistribution 𝕜 Ω) (i : Fin d),
  ∃ (da : SmoothCoefficient 𝕜 Ω)
    (M : Tests 𝕜 Ω →L[𝕜] Tests 𝕜 Ω)
    (Md : Tests 𝕜 Ω →L[𝕜] Tests 𝕜 Ω),
    (∀ x ∈ Ω, da.val x = fderiv ℝ a.val x (coordinateVector i)) ∧
    (∀ φ x, M φ x = a.val x * φ x) ∧
    (∀ φ x, Md φ x = da.val x * φ x) ∧
    -(u.comp M).comp (testPartialCLM [i]) =
      (u.comp Md) + (-u.comp (testPartialCLM [i])).comp M

/-- The completely expanded word Leibniz formula, written recursively to avoid
binomial multiplicities: each coordinate derivative is assigned either to the
coefficient or to the distribution. There are 2^length(w) summands. -/
noncomputable def leibnizExpansion {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)}
    (M : SmoothCoefficient 𝕜 Ω → Tests 𝕜 Ω →L[𝕜] Tests 𝕜 Ω) :
    List (Fin d) → SmoothCoefficient 𝕜 Ω → ScalarDistribution 𝕜 Ω → ScalarDistribution 𝕜 Ω
  | [], a, u => u.comp (M a)
  | i :: w, a, u => leibnizExpansion M w (coefficientPartial i a) u +
      leibnizExpansion M w a (-u.comp (testPartialCLM [i]))

/-- The full finite-order Leibniz rule, with no equicontinuity or order bound assumed. -/
def fullLeibnizType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)),
  ∃ M : SmoothCoefficient 𝕜 Ω → Tests 𝕜 Ω →L[𝕜] Tests 𝕜 Ω,
    (∀ a φ x, M a φ x = a.val x * φ x) ∧
    ∀ (w : List (Fin d)) (a : SmoothCoefficient 𝕜 Ω) (u : ScalarDistribution 𝕜 Ω),
      derivativeValue 𝕜 d Ω w (u.comp (M a)) = leibnizExpansion M w a u

end Specs.ExpandedFA.Distributions.DistributionCalculus
