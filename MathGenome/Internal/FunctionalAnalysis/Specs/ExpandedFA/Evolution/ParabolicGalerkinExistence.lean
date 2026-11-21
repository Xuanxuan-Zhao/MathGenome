import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HilbertTripleTrace
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Independent interface for the existence stage at paper.tex:15157–15194.
The forms are algebraic bilinear forms, bounded only outside a single null
set, simultaneously in both arguments. No separability assumption occurs.
The canonical operator is set to zero at times where the displayed bound
fails. This changes neither the equation nor any Bochner class.

The time interval may have length zero: the prescribed initial value fixes
the singleton H-valued curve, although its L² class alone has no trace.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.Evolution.ParabolicGalerkinSpec

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev BilinearForms (V : Type u) [AddCommGroup V] [Module ℝ V] :=
  ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ

/-- The original uniform form bound at a single time. -/
def BoundedAt (a : BilinearForms V) (M t : ℝ) : Prop :=
  ∀ x y : V, ‖a t x y‖ ≤ M * ‖x‖ * ‖y‖

/-- A total representative of the source's a.e. defined operator A(t).
In particular, no boundedness at exceptional times is assumed. -/
def formOperator (a : BilinearForms V) (M t : ℝ) : V →L[ℝ] StrongDual ℝ V :=
  open Classical in
  if h : BoundedAt a M t then (a t).mkContinuous₂ M h else 0

/-- All source assumptions, with the *same* exceptional set for all x,y.
Measurability is relative to the Lebesgue time measure, modulo null sets,
as in the source Bochner convention. M and C need not be positive. -/
structure FormHypotheses (j : HilbertTriple V H) (T : ℝ)
    (a : BilinearForms V) (M α C : ℝ) : Prop where
  alpha_pos : 0 < α
  scalar_measurable : ∀ x y : V,
    AEMeasurable (fun t => a t x y) (HilbertTripleSpec.timeMeasureValue T)
  bounds : ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
    BoundedAt a M t ∧ ∀ x : V,
      α * ‖x‖ ^ 2 - C * ‖j.embedding x‖ ^ 2 ≤ a t x x
  strong_measurable : ∀ x : V,
    AEStronglyMeasurable (fun t => formOperator a M t x)
      (HilbertTripleSpec.timeMeasureValue T)

/-- No operator-norm measurability is required for this action. -/
def OperatorAction : Prop := ∀ (T : ℝ) (a : BilinearForms V) (M : ℝ),
  (∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T, BoundedAt a M t) →
  (∀ x, AEStronglyMeasurable (fun t => formOperator a M t x)
    (HilbertTripleSpec.timeMeasureValue T)) →
  ∃ L : HilbertTripleSpec.timeLpValue V 2 T →L[ℝ]
      HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T,
    ‖L‖ ≤ max M 0 ∧ ∀ z,
      (L z : ℝ → StrongDual ℝ V) =ᵐ[HilbertTripleSpec.timeMeasureValue T]
        fun t => formOperator a M t (z t)

/-- The actual finite-dimensional subspaces, ordered by inclusion. -/
abbrev FiniteSubspace (V : Type u) [AddCommGroup V] [Module ℝ V] :=
  {E : Submodule ℝ V // FiniteDimensional ℝ E}

instance (E : FiniteSubspace V) : FiniteDimensional ℝ E.val := E.property

/-- The Galerkin subspace with its H norm. -/
def imageSubspace (j : HilbertTriple V H) (E : FiniteSubspace V) : Submodule ℝ H :=
  E.val.map j.embedding.toLinearMap

instance (j : HilbertTriple V H) (E : FiniteSubspace V) :
    FiniteDimensional ℝ (imageSubspace j E) := by
  let : FiniteDimensional ℝ E.val := E.property
  exact Module.Finite.map E.val j.embedding.toLinearMap

/-- H-orthogonal projection, including the zero subspace. -/
def initialProjection (j : HilbertTriple V H) (E : FiniteSubspace V) : H →L[ℝ] H :=
  (imageSubspace j E).starProjection

def ProjectionConvergence : Prop := ∀ j : HilbertTriple V H,
  (atTop : Filter (FiniteSubspace V)).NeBot ∧
    ∀ h : H, Tendsto (fun E => initialProjection j E h) atTop (𝓝 h)

/-- Pointwise estimate used after testing the Galerkin equation by its
solution. No derivative bound on the Galerkin net is postulated. -/
def EnergyInequality : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
    (a : BilinearForms V) (M α C : ℝ), FormHypotheses j T a M α C →
  ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
    ∀ (x : V) (g : StrongDual ℝ V),
      g x - a t x x + (α / 2) * ‖x‖ ^ 2 ≤
        C * ‖j.embedding x‖ ^ 2 + (2 * α)⁻¹ * ‖g‖ ^ 2

/-- The form term is a genuine bounded functional of the unknown, even
without Bochner measurability of the transpose trajectory A(t)'v. -/
def FormTestFunctional : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
    (a : BilinearForms V) (M α C : ℝ), FormHypotheses j T a M α C →
  ∀ w : HilbertTripleSpec.timeLpValue V 2 T,
    ∃ ℓ : StrongDual ℝ (HilbertTripleSpec.timeLpValue V 2 T),
      ∀ z : HilbertTripleSpec.timeLpValue V 2 T,
        ℓ z = ∫ t, a t (z t) (w t) ∂HilbertTripleSpec.timeMeasureValue T

/-- The finite-dimensional mass form is invertible for the H norm, even
though the subspace carries its original V norm. No uniform bound on its
inverse, independent of the subspace, is asserted. -/
def FiniteMassSolvability : Prop := ∀ (j : HilbertTriple V H) (E : FiniteSubspace V),
  ∃ B : StrongDual ℝ E.val ≃L[ℝ] E.val, ∀ (f : StrongDual ℝ E.val) (x : E.val),
    inner ℝ (j.embedding (B f)) (j.embedding x) = f x

/-- Weak extraction from an eventually bounded L² net, retaining its norm
bound and refining the original filter. This includes inclusion-directed
Galerkin nets on nonseparable spaces. -/
def WeakLpExtraction : Prop := ∀ (T : ℝ) (I : Type v) (l : Filter I) [l.NeBot]
    (z : I → HilbertTripleSpec.timeLpValue V 2 T) (R : ℝ),
  (∀ᶠ i in l, ‖z i‖ ≤ R) →
  ∃ x : HilbertTripleSpec.timeLpValue V 2 T, ‖x‖ ≤ R ∧
    ∃ F : Filter I, F.NeBot ∧ F ≤ l ∧
      ∀ ℓ : StrongDual ℝ (HilbertTripleSpec.timeLpValue V 2 T),
        Tendsto (fun i => ℓ (z i)) F (𝓝 (ℓ x))

def extendSubspaceCurve (E : FiniteSubspace V) {T : ℝ}
    (c : HilbertTripleTraceSpec.TraceCurve E.val T) (t : ℝ) : V :=
  if ht : t ∈ Set.Icc 0 T then (c ⟨t, ht⟩ : V) else 0

def embeddedCurve (j : HilbertTriple V H) (E : FiniteSubspace V) {T : ℝ}
    (c : HilbertTripleTraceSpec.TraceCurve E.val T) :
    HilbertTripleTraceSpec.TraceCurve H T :=
  ⟨fun t => j.embedding (c t), j.embedding.continuous.comp
    (continuous_subtype_val.comp c.continuous)⟩

/-- A Galerkin solution is an absolutely continuous finite-dimensional curve.
The integral equation specifies its derivative without demanding C¹ time
regularity for merely measurable coefficients. Its initial value is the
H-orthogonal projection, expressed by orthogonality to the whole subspace.
-/
structure GalerkinSolution (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T)
    (u₀ : H) (E : FiniteSubspace V) where
  curve : HilbertTripleTraceSpec.TraceCurve E.val T
  value : HilbertTripleSpec.timeLpValue V 2 T
  velocity : HilbertTripleSpec.timeLpValue E.val 2 T
  represents : (value : ℝ → V) =ᵐ[HilbertTripleSpec.timeMeasureValue T]
    extendSubspaceCurve E curve
  integral_equation : ∀ s t : Set.Icc 0 T,
    curve t - curve s = ∫ r in s.val..t.val, velocity r
  equation : ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T, ∀ x : E.val,
    inner ℝ (j.embedding (velocity t)) (j.embedding x) + a t (value t) x = f t x
  initial : ∀ x : E.val,
    inner ℝ (j.embedding (curve ⟨0, by simp [hT]⟩) - u₀) (j.embedding x) = 0

/-- A solution with its original V-valued Bochner class, V'-valued derivative
and genuine H-valued closed-interval representative. -/
structure WeakSolution (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (M : ℝ)
    (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H) where
  value : HilbertTripleSpec.timeLpValue V 2 T
  derivative : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T
  curve : HilbertTripleTraceSpec.TraceCurve H T
  represents : HilbertTripleTraceSpec.Represents j T value curve
  has_derivative : HilbertTripleSpec.tripleDerivativeValue j T value derivative
  equation : ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
    derivative t = f t - formOperator a M t (value t)
  initial : curve ⟨0, by simp [hT]⟩ = u₀

/-- Zero time retains the prescribed initial datum, rather than claiming a
trace determined by the null L² class. -/
def ZeroTimeSolution : Prop := ∀ (j : HilbertTriple V H) (a : BilinearForms V) (M : ℝ)
    (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 0) (u₀ : H),
  ∃ z : WeakSolution j 0 le_rfl a M f u₀,
    z.value = 0 ∧ z.derivative = 0 ∧ ‖z.curve‖ ≤ ‖u₀‖

/-- Full assigned conclusion. The constant is chosen before the form, the forcing and
initial data, depending only on j,T,M,α,C. `F ≤ atTop` is a generalized subnet of the inclusion-directed
Galerkin net, preserving every eventual finite-dimensional test. Weak
convergence is tested by every continuous real linear functional on L²(V).
No countable exhaustion of V is substituted for this net.
-/
def GalerkinExistence : Prop :=
  ∀ (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (M α C : ℝ),
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (a : BilinearForms V), FormHypotheses j T a M α C →
      ∀ (f : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H),
      ∃ G : (E : FiniteSubspace V) → GalerkinSolution j T hT a f u₀ E,
      ∃ z : WeakSolution j T hT a M f u₀,
        (∀ E, ‖embeddedCurve j E (G E).curve‖ + ‖(G E).value‖ ≤
          K * (‖u₀‖ + ‖f‖)) ∧
        (‖z.curve‖ + ‖z.value‖ + ‖z.derivative‖ ≤ K * (‖u₀‖ + ‖f‖)) ∧
        ∃ F : Filter (FiniteSubspace V), F.NeBot ∧ F ≤ atTop ∧
          ∀ ℓ : StrongDual ℝ (HilbertTripleSpec.timeLpValue V 2 T),
            Tendsto (fun E => ℓ (G E).value) F (𝓝 (ℓ z.value))

def OperatorActionExpected : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V],
    OperatorAction (V := V)

def GalerkinExistenceExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    GalerkinExistence (V := V) (H := H)

def ProjectionConvergenceExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    ProjectionConvergence (V := V) (H := H)

def EnergyInequalityExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    EnergyInequality (V := V) (H := H)

def FormTestFunctionalExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    FormTestFunctional (V := V) (H := H)

def ZeroTimeSolutionExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    ZeroTimeSolution (V := V) (H := H)

def FiniteMassSolvabilityExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    FiniteMassSolvability (V := V) (H := H)

def WeakLpExtractionExpected : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V],
    WeakLpExtraction.{u,v} (V := V)

/-- Scalar integrated energy estimate used for the Galerkin and limit
curves. The energy is continuous, while its dissipative term is merely
integrable. No pointwise differentiability of either is assumed. -/
def IntegratedEnergyBoundExpected : Prop :=
  ∀ (T α β D : ℝ) (h k : ℝ → ℝ), 0 ≤ T → 0 < α → 0 ≤ β → 0 ≤ D →
    ContinuousOn h (Set.Icc 0 T) →
    (∀ t ∈ Set.Icc 0 T, 0 ≤ h t) →
    IntervalIntegrable k volume 0 T →
    (∀ t ∈ Set.Icc 0 T, 0 ≤ k t) →
    (∀ t ∈ Set.Icc 0 T,
      h t + α * (∫ r in 0..t, k r) ≤ D + β * (∫ r in 0..t, h r)) →
    (∀ t ∈ Set.Icc 0 T, h t ≤ D * Real.exp (β * T)) ∧
      α * (∫ r in 0..T, k r) ≤ D * (1 + β * T * Real.exp (β * T))

end ExpandedFA.Evolution.ParabolicGalerkinSpec
