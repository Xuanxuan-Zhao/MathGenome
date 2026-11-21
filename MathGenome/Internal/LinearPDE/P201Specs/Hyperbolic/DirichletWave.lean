import MathGenome.Internal.LinearPDE.P201Specs.Heat.FormDomain
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.DirichletResolvent
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.AbstractWaveEnergy
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HilbertTriple
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent statements for paper.tex §W05, finite-energy Dirichlet wave
and its proof, with the scope and form conventions from the introductory sections.
Forms use the manuscript's linear-first convention. No solution, square-root
identification, or spectral representation is included in the input data.
Time forcing is Bochner L¹, represented by an arbitrary integrable function.
-/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ComplexConjugate NNReal ENNReal Matrix.Norms.Elementwise
universe u v
namespace P201.Wave
open ExpandedFA ExpandedFA.Unbounded
open ClosedNonnegativeForms Models.AbstractWaveEnergy

/-- Original bounded Hermitian coercive form and dense continuous injection.
The norms on V and H remain their original Hilbert norms. -/
structure FormData (𝕜 : Type*) (V : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  j : V →L[𝕜] H
  injective : Function.Injective j
  dense : DenseRange j
  a : V →L[𝕜] V →L⋆[𝕜] 𝕜
  hermitian : ∀ x y, conj (a x y) = a y x
  coercive : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re (a x x)

namespace FormData
variable {𝕜 : Type*} [RCLike 𝕜] {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (d : FormData 𝕜 V H)

def rangeEquiv : V ≃ₗ[𝕜] d.j.range :=
  LinearEquiv.ofInjective d.j.toLinearMap d.injective

/-- The same canonical associated operator as E10, with exactly the image JV. -/
def denseForm : P201.Elliptic.DenseForm 𝕜 H where
  domain := d.j.range
  dense := d.dense
  form :=
    { toFun := fun x =>
        { toFun := fun y => d.a (d.rangeEquiv.symm x) (d.rangeEquiv.symm y)
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }

theorem denseForm_hermitian : d.denseForm.IsHermitian := by
  intro x y
  exact d.hermitian _ _

theorem denseForm_nonnegative : d.denseForm.IsNonnegative := by
  intro x
  obtain ⟨c, hc, hb⟩ := d.coercive
  exact le_trans (mul_nonneg hc.le (sq_nonneg _)) (hb _)

def energyForm := d.denseForm.toNonnegative d.denseForm_hermitian d.denseForm_nonnegative

def operator : Operator 𝕜 H H := d.denseForm.associatedOperator

/-- Scalar-linear dual convention: conjugate the manuscript's weak equation.
This is the ordinary continuous dual, not an assumed antidual identification. -/
def pivot (h : H) : V →L[𝕜] 𝕜 := (innerSL 𝕜 h).comp d.j

def dualForm (x : V) : V →L[𝕜] 𝕜 where
  toFun := fun w => d.a w x
  map_add' := by intros; simp
  map_smul' := by intros; simp
  cont := by fun_prop

def acceleration (f : ℝ → H) (u : ℝ → V) (t : ℝ) : V →L[𝕜] 𝕜 :=
  d.pivot (f t) - d.dualForm (u t)

def energy (x : V) (y : H) : ℝ :=
  (‖y‖ ^ 2 + RCLike.re (d.a x x)) / 2

variable [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

/-- C(V) ∩ C¹(H), with endpoints interpreted by within derivatives;
scalar testing is exactly the time-distribution equation. -/
structure IsSolution (T : ℝ) (g : V) (h : H) (f : ℝ → H)
    (u : ℝ → V) (vel : ℝ → H) : Prop where
  continuous_position : ContinuousOn u (Icc 0 T)
  continuous_velocity : ContinuousOn vel (Icc 0 T)
  derivative : ∀ t ∈ Icc 0 T,
    HasDerivWithinAt (fun s => d.j (u s)) (vel t) (Icc 0 T) t
  initial_position : u 0 = g
  initial_velocity : vel 0 = h
  equation : ∀ w : V, Evolution.HilbertTripleSpec.derivativeValue T
    (fun t => inner 𝕜 (d.j w) (vel t))
    (fun t => inner 𝕜 (d.j w) (f t) - d.a (u t) w)

/-- Homogeneous evolution in the original V topology, with the actual
sesquilinear weak equation and energy. This is a preparatory stage of W05. -/
def HomogeneousClaims (F : WaveFamily (𝕜 := 𝕜) (H := H)) : Prop :=
  ∀ (g : V) (h : H), ∃ (u : ℝ → V) (vel : ℝ → H),
    Continuous u ∧ Continuous vel ∧
    (∀ t, HasDerivAt (fun s => d.j (u s)) (vel t) t) ∧
    (∀ (w : V) t, HasDerivAt (fun s => inner 𝕜 (d.j w) (vel s))
      (-d.a (u t) w) t) ∧
    u 0 = g ∧ vel 0 = h ∧
    (∀ t, d.energy (u t) (vel t) = d.energy g h) ∧
    ∀ t, d.j (u t) = F.cosine t (d.j g) + F.quotient t h

/-- Full L¹ forced conclusion, including uniqueness among all weak energy
solutions and every pair of times in the closed slab. -/
def ForcedClaims (F : WaveFamily (𝕜 := 𝕜) (H := H)) : Prop :=
  ∀ T : ℝ, 0 < T → ∀ (g : V) (h : H) (f : ℝ → H),
    IntegrableOn f (Ioo 0 T) →
    ∃ (u : ℝ → V) (vel : ℝ → H),
      d.IsSolution T g h f u vel ∧
      (∀ (z : ℝ → V) (w : ℝ → H), d.IsSolution T g h f z w →
        EqOn z u (Icc 0 T) ∧ EqOn w vel (Icc 0 T)) ∧
      IntegrableOn (d.acceleration f u) (Ioo 0 T) ∧
      Evolution.HilbertTripleSpec.derivativeValue T
        (fun t => d.pivot (vel t)) (d.acceleration f u) ∧
      (∀ r ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        d.energy (u t) (vel t) - d.energy (u r) (vel r) =
          ∫ s in r..t, RCLike.re (inner 𝕜 (vel s) (f s))) ∧
      (∀ t ∈ Icc 0 T,
        IntervalIntegrable (fun s => F.quotient (t - s) (f s)) volume 0 t ∧
        d.j (u t) = F.cosine t (d.j g) + F.quotient t h +
          ∫ s in (0 : ℝ)..t, F.quotient (t - s) (f s))

/-- Exact form domain and energy of the very square root used in the formula. -/
def RootClaims (F : WaveFamily (𝕜 := 𝕜) (H := H)) : Prop :=
  OperatorDomainsSpec.productValue F.S F.S = d.operator ∧
  F.S.domain = d.j.range ∧
  ∀ (x : V) (hx : d.j x ∈ F.S.domain),
    RCLike.re (d.a x x) = ‖F.S ⟨d.j x, hx⟩‖ ^ 2

end FormData

namespace DirichletWaveExpected

/-- The V′ acceleration is an actual vector-valued time-distribution derivative
for every weak energy solution with integrable H-valued forcing. -/
def AccelerationTheorem : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    (d : FormData 𝕜 V H) (T : ℝ) (g : V) (h : H) (f : ℝ → H)
    (u : ℝ → V) (vel : ℝ → H),
    IntegrableOn f (Ioo 0 T) → d.IsSolution T g h f u vel →
    IntegrableOn (d.acceleration f u) (Ioo 0 T) ∧
      Evolution.HilbertTripleSpec.derivativeValue T
        (fun t => d.pivot (vel t)) (d.acceleration f u)

def RealResult {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (d : FormData ℝ V H) : Prop :=
  ∃ C : RealNonnegativeSpectralCalculus.Calculus (H := H),
    C.integral RealNonnegativeSpectralCalculus.coordinate = d.operator ∧
    d.RootClaims (realFamily C) ∧ d.ForcedClaims (realFamily C)

def ComplexResult {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : FormData ℂ V H) : Prop :=
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H)
    (C : MeasurableSpectralCalculus.BoundedRealization E),
    MeasurableSpectralCalculus.measurableIntegral C
      (complexSymbol RealSymbols.coordinate) = d.operator ∧
    d.RootClaims (complexFamily C) ∧ d.ForcedClaims (complexFamily C)

def RealTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (d : FormData ℝ V H), RealResult d

def ComplexTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : FormData ℂ V H), ComplexResult d

/-- Completed homogeneous stage, retaining the exact canonical operator. -/
def RealHomogeneousTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (d : FormData ℝ V H),
    ∃ C : RealNonnegativeSpectralCalculus.Calculus (H := H),
      C.integral RealNonnegativeSpectralCalculus.coordinate = d.operator ∧
      d.RootClaims (realFamily C) ∧ d.HomogeneousClaims (realFamily C)

def ComplexHomogeneousTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : FormData ℂ V H),
    letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
    ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H)
      (C : MeasurableSpectralCalculus.BoundedRealization E),
      MeasurableSpectralCalculus.measurableIntegral C (complexSymbol RealSymbols.coordinate) =
        d.operator ∧ d.RootClaims (complexFamily C) ∧ d.HomogeneousClaims (complexFamily C)

/-- Original real spatial scope, with an arbitrary bounded symmetric coercive
form on the actual full-H¹ closure. The injection is fixed, not supplied. -/
def RealDirichletTheorem : Prop :=
  ∀ (m : ℕ) (Ω : P201Specs.Domain (m + 1)), P201Specs.IsBoundedLipschitzOpen Ω →
    (Ω : Set (P201Specs.Space (m + 1))).Nonempty →
    ∀ a : P201Specs.H10 ℝ Ω →L[ℝ] P201Specs.H10 ℝ Ω →L[ℝ] ℝ,
      (∀ x y, a x y = a y x) →
      (∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ a x x) →
      ∃ d : FormData ℝ (P201Specs.H10 ℝ Ω) (P201Specs.Lp ℝ Ω 2),
        d.j = P201Specs.hZeroUnderlying Ω ∧ (∀ x y, d.a x y = a x y) ∧ RealResult d

/-- The same original scope over C, retaining every Hermitian coercive form. -/
def ComplexDirichletTheorem : Prop :=
  ∀ (m : ℕ) (Ω : P201Specs.Domain (m + 1)), P201Specs.IsBoundedLipschitzOpen Ω →
    (Ω : Set (P201Specs.Space (m + 1))).Nonempty →
    ∀ a : P201Specs.H10 ℂ Ω →L[ℂ] P201Specs.H10 ℂ Ω →L⋆[ℂ] ℂ,
      (∀ x y, conj (a x y) = a y x) →
      (∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ (a x x).re) →
      ∃ d : FormData ℂ (P201Specs.H10 ℂ Ω) (P201Specs.Lp ℂ Ω 2),
        d.j = P201Specs.hZeroUnderlying Ω ∧ d.a = a ∧ ComplexResult d

/-- E10 specialization fixes the energy form and exact canonical graph.
Homogeneous trace is asserted in the physical C02 trace space, including n=1. -/
def EllipticTheorem : Prop :=
  ∀ (m : ℕ) (Ω : P201Specs.Domain (m + 1))
    (hΩ : P201Specs.IsBoundedLipschitzOpen Ω),
    (Ω : Set (P201Specs.Space (m + 1))).Nonempty →
    ∀ A : P201Specs.Dirichlet.MatrixField (m + 1),
      MemLp A ∞ (P201Specs.domainMeasure Ω) →
      ∀ lam : ℝ, 0 < lam → P201Specs.Dirichlet.Elliptic Ω A lam →
        P201Specs.Dirichlet.Symmetric Ω A →
        ∃ d : FormData ℝ (P201Specs.H10 ℝ Ω) (P201Specs.Lp ℝ Ω 2),
          d.j = P201Specs.hZeroUnderlying Ω ∧
          (∀ x y, d.a x y = P201Specs.ellipticEnergyForm Ω A x.val y.val) ∧
          (∀ x h, (x, h) ∈ d.operator.graph ↔
            ∃ v : P201Specs.H10 ℝ Ω, P201Specs.hZeroUnderlying Ω v = x ∧
              P201Specs.Dirichlet.Solves Ω A (P201Specs.pivot Ω h) v.val) ∧
          RealResult d ∧
          ∃ trace : P201Specs.H ℝ Ω 1 →L[ℝ] P201Specs.Hhalf Ω hΩ,
            P201Specs.Trace.AgreesWithSmooth trace ∧
            trace.ker = P201Specs.hZeroSubmodule ℝ Ω ∧
            ∀ x : P201Specs.H10 ℝ Ω, trace x.val = 0

end DirichletWaveExpected
end P201.Wave
