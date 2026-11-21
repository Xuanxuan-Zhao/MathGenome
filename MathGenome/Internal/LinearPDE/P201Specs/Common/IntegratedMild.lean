import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.InhomogeneousEvolution

/-! Independent statement of the integrated part of paper.tex, C07.
The generator is the full right norm-derivative generator of the given C₀
semigroup. No boundedness of the generator, extra forcing regularity, or
separability of the Banach space is assumed. Real-time functions are used
only on the closed nonnegative slab; uniqueness means equality on that slab.
The integrable representative convention is unchanged by endpoint values. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace P201.Common.IntegratedMild
open ExpandedFA ExpandedFA.Semigroups

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X

abbrev Generator (S : C0Semigroup 𝕜 X) := C0SemigroupSpec.generatorValue S

/-- The actual time primitive, not an assumed domain-valued integral. -/
def primitive (u : ℝ → X) (t : ℝ) : X := ∫ s in (0 : ℝ)..t, u s

/-- J(h)x = ∫₀ʰ S(r)x dr in the ambient Banach space. -/
def orbitIntegral (S : C0Semigroup 𝕜 X) (h : ℝ≥0) (x : X) : X :=
  ∫ r in (0 : ℝ)..(h : ℝ), S.operators r.toNNReal x

/-- The common variation-of-constants formula, with the original L¹ forcing. -/
abbrev mildSolution (S : C0Semigroup 𝕜 X) (x₀ : X) (f : ℝ → X) : ℝ → X :=
  InhomogeneousEvolutionSpec.solution S x₀ f

/-- Formula definition of a mild solution on the given time slab. -/
def IsMildSolution (S : C0Semigroup 𝕜 X) (T : ℝ≥0)
    (x₀ : X) (f u : ℝ → X) : Prop :=
  ContinuousOn u (Icc 0 (T : ℝ)) ∧
    EqOn u (mildSolution S x₀ f) (Icc 0 (T : ℝ))

/-- Integrated definition. A genuine membership witness is required before
applying the unbounded generator to each primitive. -/
def IsIntegratedSolution (S : C0Semigroup 𝕜 X) (T : ℝ≥0)
    (x₀ : X) (f u : ℝ → X) : Prop :=
  ContinuousOn u (Icc 0 (T : ℝ)) ∧
    ∀ t ∈ Icc 0 (T : ℝ), ∃ h : primitive (𝕜 := 𝕜) u t ∈ (Generator S).domain,
      u t = x₀ + Generator S ⟨primitive (𝕜 := 𝕜) u t, h⟩ + primitive (𝕜 := 𝕜) f t

namespace Expected

/-- Completeness in the sum norm ‖x‖ + ‖Ax‖. -/
def GraphComplete : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (S : C0Semigroup 𝕜 X),
    CompleteSpace (Unbounded.GraphDomain (Generator S))

/-- The orbit primitive is a bounded linear map into the exact graph-norm
space, is strongly graph-continuous in time, and has uniform compact-time
operator bounds. Its second coordinate is precisely S(h)x − x. -/
def OrbitIntegralRegularity : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (S : C0Semigroup 𝕜 X),
    ∃ J : ℝ≥0 → X →L[𝕜] Unbounded.GraphDomain (Generator S),
      (∀ h x,
        (Unbounded.GraphDomain.toDomain _ (J h x) : X) = orbitIntegral S h x ∧
        Generator S (Unbounded.GraphDomain.toDomain _ (J h x)) = S.operators h x - x) ∧
      (∀ x, Continuous (fun h => J h x)) ∧
      ∀ T : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ≥0, h ≤ T → ‖J h‖ ≤ C

/-- Full integrated mild theorem. Interval integrability of every convolution
is stated explicitly so that the formula has its Bochner meaning. The final
equivalence includes existence and uniqueness among every continuous
integrated solution, with equality only on the prescribed time interval. -/
def IntegratedWellPosedness : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (S : C0Semigroup 𝕜 X) (T : ℝ≥0), 0 < (T : ℝ) →
    ∀ (x₀ : X) (f : ℝ → X), IntegrableOn f (Icc 0 (T : ℝ)) →
      (∀ t ∈ Icc 0 (T : ℝ),
        IntervalIntegrable (fun s => S.operators (t - s).toNNReal (f s)) volume 0 t) ∧
      mildSolution S x₀ f 0 = x₀ ∧
      IsIntegratedSolution S T x₀ f (mildSolution S x₀ f) ∧
      ∀ u : ℝ → X,
        IsIntegratedSolution S T x₀ f u ↔ IsMildSolution S T x₀ f u

end Expected
end P201.Common.IntegratedMild
