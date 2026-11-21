import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HyperbolicFormBoundsAndCarrier
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Weak-energy existence stage of `fa2:p3:hyperbolic-triple`, in the adopted
paper's paragraph “Galerkin existence in the weak energy class”.

The spaces and their separate original norms are those of HilbertTriple.
The scalar-C¹ hypothesis is exactly the upstream closed-interval hypothesis.
Weak continuity is expressed by continuity of every continuous linear
functional. All time derivatives are the upstream vector distributional
derivatives. In particular no strong endpoint identity or existence
certificate is part of the form hypotheses.

The time horizon may be zero: prescribed initial data fix the singleton
state. The strong-trace conclusion uses the relative neighborhood filter on
the closed interval, which also handles this case.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
universe u v

namespace ExpandedFA.Evolution.HyperbolicWeakEnergySpec
open HilbertTripleSpec HyperbolicFormSpec

section Spaces
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Exactly the symmetric, scalar-C¹, uniform Gårding assumptions. -/
structure FormHypotheses (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (α C : ℝ) : Prop where
  scalarC1 : ScalarC1 T a
  symmetric : ∀ t ∈ Set.Icc 0 T, ∀ x y, a t x y = a t y x
  alpha_pos : 0 < α
  shift_nonneg : 0 ≤ C
  garding : ∀ t ∈ Set.Icc 0 T, ∀ x,
    α * ‖x‖ ^ 2 - C * ‖j.embedding x‖ ^ 2 ≤ a t x x

/-- The canonical shifted form a(t)+κ(J·,J·)H. -/
def shiftedForm (j : HilbertTriple V H) (a : ℝ → Form V) (κ t : ℝ) : Form V :=
  a t + κ • intoDualValue j

def shiftedEnergy (j : HilbertTriple V H) (a : ℝ → Form V)
    (κ t : ℝ) (x : V) (y : H) : ℝ :=
  ‖y‖ ^ 2 + shiftedForm j a κ t x x

/-- Continuity for the weak topology, stated without changing the underlying
type, norm, or Hilbert structure. -/
def WeaklyContinuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℝ → E) (S : Set ℝ) : Prop :=
  ∀ L : StrongDual ℝ E, ContinuousOn (fun t => L (z t)) S

/-- The state is represented at every time; the open-interval regularity
uses genuine strongly measurable Bochner functions. The extra L² memberships
spell out W¹,²(V′), and the H-valued membership spells out W¹,∞(H). -/
structure WeakEnergySolution (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T) where
  displacement : ℝ → V
  velocity : ℝ → H
  acceleration : ℝ → StrongDual ℝ V
  displacement_mem : MemLp displacement ∞ (timeMeasureValue T)
  pivot_displacement_mem : MemLp (fun t => j.embedding (displacement t)) ∞
    (timeMeasureValue T)
  velocity_mem : MemLp velocity ∞ (timeMeasureValue T)
  dual_velocity_mem : MemLp (fun t => pivotValue j (velocity t)) 2 (timeMeasureValue T)
  acceleration_mem : MemLp acceleration 2 (timeMeasureValue T)
  displacement_derivative : derivativeValue T (fun t => j.embedding (displacement t)) velocity
  velocity_derivative : derivativeValue T (fun t => pivotValue j (velocity t)) acceleration
  equation : ∀ᵐ t ∂timeMeasureValue T,
    acceleration t + a t (displacement t) = pivotValue j (f t)
  displacement_weak : WeaklyContinuousOn displacement (Set.Icc 0 T)
  velocity_weak : WeaklyContinuousOn velocity (Set.Icc 0 T)
  initial_displacement : displacement 0 = u₀
  initial_velocity : velocity 0 = v₀

/-- Uniform constants precede the data: they depend on the embedding, forms,
their bounds, and T only. The shift κ=C is a permitted choice in the source.
The last two conclusions concern only the starting time, not continuity at
every time (which belongs to the later uniqueness/restarting obligation). -/
def WeakExistence : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧
    ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T),
      ∃ z : WeakEnergySolution j T a u₀ v₀ f,
        (∀ t ∈ Set.Icc 0 T,
          shiftedEnergy j a C t (z.displacement t) (z.velocity t) ≤
            Real.exp (c * t) *
              (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) ∧
        (∀ t ∈ Set.Icc 0 T,
          ‖z.displacement t‖ ^ 2 + ‖z.velocity t‖ ^ 2 ≤
            K * (‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2)) ∧
        Tendsto z.displacement (𝓝[Set.Icc 0 T] 0) (𝓝 u₀) ∧
        Tendsto z.velocity (𝓝[Set.Icc 0 T] 0) (𝓝 v₀)

/-- Elementary energy geometry needed before taking any Galerkin limit. -/
def ShiftedBounds : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
  (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc 0 T, ∀ x y,
      ‖y‖ ^ 2 + α * ‖x‖ ^ 2 ≤ shiftedEnergy j a C t x y ∧
      shiftedEnergy j a C t x y ≤ ‖y‖ ^ 2 + B * ‖x‖ ^ 2

/-- The algebraic estimate used when testing a finite Galerkin system with
its velocity. The constant is independent of the trial subspace and data. -/
def EnergyRhsBound : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
  (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∃ c : ℝ, 0 ≤ c ∧ ∀ t ∈ Set.Icc 0 T, ∀ (x : V) (y h : H),
    2 * inner ℝ h y + derivWithin (fun r => a r x x) (Set.Icc 0 T) t +
      2 * C * inner ℝ (j.embedding x) y ≤
        c * shiftedEnergy j a C t x y + ‖h‖ ^ 2

/-- The strong initial trace follows from the weak representatives, a uniform
V bound, and an energy upper bound whose limit is the initial energy. This
is a criterion for use after the compactness construction, not an assumed
ingredient of WeakExistence. -/
def InitialTraceCriterion : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∀ (x : ℝ → V) (y : ℝ → H),
    WeaklyContinuousOn x (Set.Icc 0 T) → WeaklyContinuousOn y (Set.Icc 0 T) →
    ∀ (R : ℝ), 0 ≤ R → (∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ R) →
    ∀ g : ℝ → ℝ,
      Tendsto g (𝓝[Set.Icc 0 T] 0) (𝓝 (shiftedEnergy j a C 0 (x 0) (y 0))) →
      (∀ t ∈ Set.Icc 0 T, shiftedEnergy j a C t (x t) (y t) ≤ g t) →
      Tendsto x (𝓝[Set.Icc 0 T] 0) (𝓝 (x 0)) ∧
      Tendsto y (𝓝[Set.Icc 0 T] 0) (𝓝 (y 0))

/-- A bounded V-valued state which is continuous after injection into H is
weakly continuous in V. No separability assumption is needed. -/
def WeakContinuityFromPivot : Prop := ∀ (j : HilbertTriple V H)
  (S : Set ℝ) (x : ℝ → V) (R : ℝ),
  0 ≤ R → (∀ t ∈ S, ‖x t‖ ≤ R) →
  ContinuousOn (fun t => j.embedding (x t)) S → WeaklyContinuousOn x S

/-- The fixed-data singleton case requires no differential equation on an
empty open interval. Its state and its relative strong traces are fixed. -/
def ZeroTimeSolution : Prop := ∀ (j : HilbertTriple V H) (a : ℝ → Form V)
  (u₀ : V) (v₀ : H) (f : timeLpValue H 2 0),
  ∃ z : WeakEnergySolution j 0 a u₀ v₀ f,
    (∀ t ∈ Set.Icc (0 : ℝ) 0, z.displacement t = u₀ ∧ z.velocity t = v₀) ∧
    Tendsto z.displacement (𝓝[Set.Icc 0 0] 0) (𝓝 u₀) ∧
    Tendsto z.velocity (𝓝[Set.Icc 0 0] 0) (𝓝 v₀)

/-- The two vector distributional graphs and genuine Bochner bounds give
weak representatives at every time, with the same bounds. Their primitive
increment identities include the two endpoints. This conclusion has no
separability or compact-embedding premise. -/
def WeakRepresentatives : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∀ (u : ℝ → V) (v : ℝ → H) (g : ℝ → StrongDual ℝ V) (R S : ℝ),
    0 ≤ R → 0 ≤ S →
    MemLp u ∞ (timeMeasureValue T) → MemLp v ∞ (timeMeasureValue T) →
    MemLp g 2 (timeMeasureValue T) →
    (∀ᵐ t ∂timeMeasureValue T, ‖u t‖ ≤ R) →
    (∀ᵐ t ∂timeMeasureValue T, ‖v t‖ ≤ S) →
    derivativeValue T (fun t => j.embedding (u t)) v →
    derivativeValue T (fun t => pivotValue j (v t)) g →
    ∃ (x : ℝ → V) (y : ℝ → H),
      x =ᵐ[timeMeasureValue T] u ∧ y =ᵐ[timeMeasureValue T] v ∧
      (∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ R ∧ ‖y t‖ ≤ S) ∧
      WeaklyContinuousOn x (Set.Icc 0 T) ∧
      WeaklyContinuousOn y (Set.Icc 0 T) ∧
      ContinuousOn (fun t => j.embedding (x t)) (Set.Icc 0 T) ∧
      ContinuousOn (fun t => pivotValue j (y t)) (Set.Icc 0 T) ∧
      (∀ s t : Set.Icc 0 T,
        j.embedding (x t) - j.embedding (x s) = ∫ r in s.val..t.val, v r) ∧
      (∀ s t : Set.Icc 0 T,
        pivotValue j (y t) - pivotValue j (y s) = ∫ r in s.val..t.val, g r)

/-- Extend the a.e. energy upper estimate to every time of the weak
representatives, including endpoints. The bound is continuous, not assumed
to be an energy identity. -/
def EnergyBoundEverywhere : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∀ (x : ℝ → V) (y : ℝ → H),
    WeaklyContinuousOn x (Set.Icc 0 T) → WeaklyContinuousOn y (Set.Icc 0 T) →
    ∀ R : ℝ, 0 ≤ R → (∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ R) →
    ∀ G : ℝ → ℝ, ContinuousOn G (Set.Icc 0 T) →
      (∀ᵐ t ∂timeMeasureValue T, shiftedEnergy j a C t (x t) (y t) ≤ G t) →
      ∀ t ∈ Set.Icc 0 T, shiftedEnergy j a C t (x t) (y t) ≤ G t

/-- The energy bound implies a uniform bound in the two original norms.
The coefficient is chosen before the initial data and forcing. -/
def StateBoundOfGronwall : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∀ c : ℝ, 0 ≤ c →
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (x : ℝ → V) (y : ℝ → H),
    (∀ t ∈ Set.Icc 0 T, shiftedEnergy j a C t (x t) (y t) ≤
      Real.exp (c * t) * (shiftedEnergy j a C 0 u₀ v₀ + ∫ r in 0..t, ‖f r‖ ^ 2)) →
    ∀ t ∈ Set.Icc 0 T, ‖x t‖ ^ 2 + ‖y t‖ ^ 2 ≤
      K * (‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2)

/-- Exact mass systems on each finite trial space. This is a construction
with prescribed trial data, and does not assume a uniform energy bound. -/
def FiniteGalerkinSystems : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (a : ℝ → Form V), ScalarC1 T a →
  ∀ (E : Submodule ℝ V) [FiniteDimensional ℝ E]
    (f : timeLpValue H 2 T) (u₀ v₀ : E),
    ∃ u v q : ℝ → E,
      Continuous u ∧ Continuous v ∧ u 0 = u₀ ∧ v 0 = v₀ ∧
      MemLp q 2 (timeMeasureValue T) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, u t - u s = ∫ r in s..t, v r) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, v t - v s = ∫ r in s..t, q r) ∧
      (∀ t, ∀ w : E, inner ℝ (j.embedding (q t)) (j.embedding w) + a t (u t) w =
        inner ℝ (f t) (j.embedding w))

end Spaces

def WeakExistenceExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    WeakExistence (V := V) (H := H)

def ShiftedBoundsExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    ShiftedBounds (V := V) (H := H)

def EnergyRhsBoundExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    EnergyRhsBound (V := V) (H := H)

def InitialTraceCriterionExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    InitialTraceCriterion (V := V) (H := H)

def WeakContinuityFromPivotExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    WeakContinuityFromPivot (V := V) (H := H)

def ZeroTimeSolutionExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    ZeroTimeSolution (V := V) (H := H)

def WeakRepresentativesExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    WeakRepresentatives (V := V) (H := H)

def EnergyBoundEverywhereExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    EnergyBoundEverywhere (V := V) (H := H)

def StateBoundOfGronwallExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    StateBoundOfGronwall (V := V) (H := H)

def FiniteGalerkinSystemsExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    FiniteGalerkinSystems (V := V) (H := H)

end ExpandedFA.Evolution.HyperbolicWeakEnergySpec
