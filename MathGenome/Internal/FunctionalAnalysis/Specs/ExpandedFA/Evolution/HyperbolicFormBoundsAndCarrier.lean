import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HilbertTriple
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
Independent statements for the first paragraph of the proof of
`fa2:p3:hyperbolic-triple` (paper.tex:15253–15280).

The forms are bounded real bilinear maps on the original Hilbert space.
Scalar C¹ regularity is `ContDiffOn` on the closed time interval, not
operator-norm C¹ regularity. The time derivative at an endpoint is the
one-sided derivative `derivWithin`. On a singleton interval this canonical
derivative is zero; empty intervals are retained. No separability assumption
is made on either ambient Hilbert space. The Gårding assumption is unnecessary
for these preparatory results and is therefore not imposed.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
universe u v
namespace ExpandedFA.Evolution.HyperbolicFormSpec

abbrev Form (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  V →L[ℝ] V →L[ℝ] ℝ

section Forms
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Riesz representation on V with its original Hilbert norm. -/
def representingOperator (a : Form V) : V →L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp a

def ScalarC1 (T : ℝ) (a : ℝ → Form V) : Prop :=
  ∀ u v, ContDiffOn ℝ 1 (fun t => a t u v) (Set.Icc 0 T)

def RepresentationExpected : Prop := ∀ a : Form V,
  (∀ u v, inner ℝ (representingOperator a u) v = a u v) ∧
  (‖representingOperator a‖ = ‖a‖) ∧
  ((∀ u v, a u v = a v u) → IsSelfAdjoint (representingOperator a))

def UniformBoundsExpected : Prop := ∀ (T : ℝ) (a : ℝ → Form V), ScalarC1 T a →
  ∃ M : ℝ, 0 ≤ M ∧
    (∀ t ∈ Set.Icc 0 T, ∀ u v,
      |a t u v| + |derivWithin (fun r => a r u v) (Set.Icc 0 T) t| ≤ M * ‖u‖ * ‖v‖) ∧
    (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T,
      ‖representingOperator (a t) - representingOperator (a s)‖ ≤ M * |t - s|)

end Forms
section Carrier
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- H₀ carries the original H norm and is the closure of J V₀. -/
def pivotSpace (j : HilbertTriple V H) (S : Submodule ℝ V) : Submodule ℝ H :=
  (S.map j.embedding.toLinearMap).topologicalClosure

/-- Data of the reducing carrier. All properties are conclusions of the existence theorem. -/
structure ReducingCarrier (j : HilbertTriple V H) (T : ℝ) (a : ℝ → Form V)
    (u₀ : V) (v₀ : H) (f : HilbertTripleSpec.timeLpValue H 2 T) where
  space : Submodule ℝ V
  closed : IsClosed (space : Set V)
  separable : TopologicalSpace.IsSeparable (space : Set V)
  initial : u₀ ∈ space
  velocity : v₀ ∈ pivotSpace j space
  forcing : ∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T, f t ∈ pivotSpace j space
  massInvariant : ∀ u ∈ space,
    (ContinuousLinearMap.adjoint j.embedding) (j.embedding u) ∈ space
  formInvariant : ∀ t ∈ Set.Icc 0 T, ∀ u ∈ space, representingOperator (a t) u ∈ space
  formComplementInvariant : ∀ t ∈ Set.Icc 0 T, ∀ w ∈ spaceᗮ,
    representingOperator (a t) w ∈ spaceᗮ

def CarrierExistenceExpected : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
  (a : ℝ → Form V), ScalarC1 T a →
  (∀ t ∈ Set.Icc 0 T, ∀ u v, a t u v = a t v u) →
  ∀ (u₀ : V) (v₀ : H) (f : HilbertTripleSpec.timeLpValue H 2 T),
    Nonempty (ReducingCarrier j T a u₀ v₀ f)

def CarrierGeometryExpected : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
  (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : HilbertTripleSpec.timeLpValue H 2 T)
  (c : ReducingCarrier j T a u₀ v₀ f),
  TopologicalSpace.IsSeparable (pivotSpace j c.space : Set H) ∧
  (∀ w ∈ c.spaceᗮ, j.embedding w ∈ (pivotSpace j c.space)ᗮ) ∧
  (∀ w ∈ c.spaceᗮ,
    (ContinuousLinearMap.adjoint j.embedding) (j.embedding w) ∈ c.spaceᗮ) ∧
  (∀ t ∈ Set.Icc 0 T, ∀ u ∈ c.space, ∀ w ∈ c.spaceᗮ, a t u w = 0) ∧
  (letI : CompleteSpace c.space := c.closed.completeSpace_coe
   letI : CompleteSpace (pivotSpace j c.space) :=
     (c.space.map j.embedding.toLinearMap).isClosed_topologicalClosure.completeSpace_coe
   ∃ j₀ : HilbertTriple c.space (pivotSpace j c.space),
     (∀ u : c.space, (j₀.embedding u : H) = j.embedding u) ∧
     (∀ (h : pivotSpace j c.space) (u : c.space),
       HilbertTripleSpec.pivotValue j₀ h u = HilbertTripleSpec.pivotValue j (h : H) (u : V)))

/-- Distributional scalar testing of u''+Au=f, with velocity v.
The canonical triple pairing is the H product after J. -/
def WaveTestEquation (j : HilbertTriple V H) (T : ℝ) (a : ℝ → Form V)
    (u : ℝ → V) (v f : ℝ → H) : Prop :=
  ∀ w : V, HilbertTripleSpec.derivativeValue T
    (fun t => inner ℝ (v t) (j.embedding w))
    (fun t => inner ℝ (f t) (j.embedding w) - a t (u t) w)

def CarrierEquationLiftExpected : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
  (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : HilbertTripleSpec.timeLpValue H 2 T)
  (c : ReducingCarrier j T a u₀ v₀ f)
  (u : ℝ → c.space) (v : ℝ → pivotSpace j c.space),
  (∀ w : c.space, HilbertTripleSpec.derivativeValue T
    (fun t => inner ℝ (v t : H) (j.embedding w))
    (fun t => inner ℝ (f t) (j.embedding w) - a t (u t) w)) →
  WaveTestEquation j T a (fun t => u t) (fun t => v t) f

/-- A reduced V₀′ acceleration solving the reduced vector equation lifts to
an actual V′-valued distributional acceleration solving the full equation.
Restriction of the pivot is the pivot of the subtriple constructed above. -/
def CarrierVectorLiftExpected : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
  (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : HilbertTripleSpec.timeLpValue H 2 T)
  (c : ReducingCarrier j T a u₀ v₀ f)
  (u : ℝ → c.space) (v : ℝ → pivotSpace j c.space)
  (g : ℝ → StrongDual ℝ c.space),
  HilbertTripleSpec.derivativeValue T
    (fun t => (HilbertTripleSpec.pivotValue j (v t)).comp c.space.subtypeL) g →
  (∀ᵐ t ∂HilbertTripleSpec.timeMeasureValue T,
    g t = (HilbertTripleSpec.pivotValue j (f t) - a t (u t)).comp c.space.subtypeL) →
  HilbertTripleSpec.derivativeValue T
    (fun t => HilbertTripleSpec.pivotValue j (v t))
    (fun t => HilbertTripleSpec.pivotValue j (f t) - a t (u t)) ∧
  (MemLp g 2 (HilbertTripleSpec.timeMeasureValue T) →
    MemLp (fun t => HilbertTripleSpec.pivotValue j (f t) - a t (u t))
      2 (HilbertTripleSpec.timeMeasureValue T))

end Carrier
/- Closed theorem types, including all ambient Hilbert-space hypotheses. -/
def RepresentationLawExpected : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V],
    RepresentationExpected (V := V)

def UniformBoundsLawExpected : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V],
    UniformBoundsExpected (V := V)

def CarrierExistenceLawExpected : Prop :=
  ∀ {V : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    CarrierExistenceExpected (V := V) (H := H)

def CarrierGeometryLawExpected : Prop :=
  ∀ {V : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    CarrierGeometryExpected (V := V) (H := H)

def CarrierEquationLiftLawExpected : Prop :=
  ∀ {V : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    CarrierEquationLiftExpected (V := V) (H := H)

def CarrierVectorLiftLawExpected : Prop :=
  ∀ {V : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    CarrierVectorLiftExpected (V := V) (H := H)

end ExpandedFA.Evolution.HyperbolicFormSpec
