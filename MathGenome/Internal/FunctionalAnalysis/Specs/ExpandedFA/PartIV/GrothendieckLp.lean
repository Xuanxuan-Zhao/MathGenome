import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.GrothendieckBound
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.MeasureTheory.Measure.Prod

/-! Independent statements for the finite-dimensionality conclusion of
`fa2:p4:grothendieck-lp`, paper.tex:19534–19589. Counterexamples at the end
of that proof remain part of the assigned scope. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace ExpandedFA.PartIV.GrothendieckLp

/-- Changing exponent preserves the underlying almost-everywhere class. -/
def toL2 {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (E : Submodule 𝕜 (Lp 𝕜 p μ))
    (h₂ : ∀ f : E, MemLp (f : Lp 𝕜 p μ) 2 μ) : E →ₗ[𝕜] Lp 𝕜 2 μ where
  toFun f := ⟨f.val.val, h₂ f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Lebesgue measure on the finite interval [0,1]. -/
abbrev intervalMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- A scalar polynomial evaluated on the real interval (also for complex coefficients). -/
def polynomialFunction (𝕜 : Type*) [RCLike 𝕜] :
    Polynomial 𝕜 →ₐ[𝕜] C(ℝ, 𝕜) :=
  Polynomial.aeval ⟨RCLike.ofReal, RCLike.continuous_ofReal⟩

lemma polynomial_memLp (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (q : Polynomial 𝕜) :
    MemLp (polynomialFunction 𝕜 q : ℝ → 𝕜) p intervalMeasure := by
  have hc := (polynomialFunction 𝕜 q).continuous
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

/-- The actual polynomial subspace of Lp([0,1]), using a.e. equivalence classes. -/
def polynomialToLp (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) :
    Polynomial 𝕜 →ₗ[𝕜] Lp 𝕜 p intervalMeasure :=
  LinearMap.codRestrict (Lp.LpSubmodule 𝕜 𝕜 p intervalMeasure)
    ((ContinuousMap.toAEEqFunLinearMap intervalMeasure).comp
      (polynomialFunction 𝕜).toLinearMap)
    (fun q => by
      change eLpNorm _ p intervalMeasure < ∞
      have he : ⇑(((ContinuousMap.toAEEqFunLinearMap intervalMeasure).comp
          (polynomialFunction 𝕜).toLinearMap) q) =ᵐ[intervalMeasure]
          polynomialFunction 𝕜 q := AEEqFun.coeFn_mk _ _
      rw [eLpNorm_congr_ae he]
      exact (polynomial_memLp 𝕜 p q).eLpNorm_lt_top)

instance intervalMeasure_probability : IsProbabilityMeasure intervalMeasure where
  measure_univ := by simp [intervalMeasure, Real.volume_Icc]

/-- Countably many disjoint copies of the unit interval with length measure.
The n-th interval is {n} × [0,1]; the ambient measure vanishes off their union. -/
abbrev stripMeasure : Measure (ℕ × ℝ) := Measure.count.prod intervalMeasure

def unitBlock (n : ℕ) : Set (ℕ × ℝ) := {n} ×ˢ Set.Icc 0 1

/-- The usual ℓp model, realized by functions constant on each unit interval.
Here Lp over counting measure is exactly the a.e.-class presentation of ℓp. -/
def sequenceToIntervals (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) :
    Lp 𝕜 p (Measure.count : Measure ℕ) →ₗ[𝕜] Lp 𝕜 p stripMeasure :=
  Lp.compMeasurePreservingₗ 𝕜 Prod.fst measurePreserving_fst

namespace Spec
/-- The quantitative bound holds for every finite orthonormal family in a
subspace on which the stated uniform L∞/L² estimate holds. -/
def OrthonormalFamilyBound : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (W : Submodule 𝕜 (Lp 𝕜 2 μ))
    (A : ℝ), 0 ≤ A →
    (∀ f : W, MemLp (f : Lp 𝕜 2 μ) ∞ μ ∧
      (eLpNorm (f : Lp 𝕜 2 μ) ∞ μ).toReal ≤ A * ‖f‖) →
    ∀ (n : ℕ) (v : Fin n → W), Orthonormal 𝕜 v →
      (n : ℝ) ≤ A ^ 2 * μ.real Set.univ

/-- No completeness or closedness is needed once the uniform comparison is known. -/
def FiniteDimensionOfL2Bound : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (W : Submodule 𝕜 (Lp 𝕜 2 μ))
    (A : ℝ), 0 ≤ A →
    (∀ f : W, MemLp (f : Lp 𝕜 2 μ) ∞ μ ∧
      (eLpNorm (f : Lp 𝕜 2 μ) ∞ μ).toReal ≤ A * ‖f‖) →
    FiniteDimensional 𝕜 W

/-- Original theorem, with the positive-exponent Lp metric supplied upstream.
In particular there is no assumption that the measure is nonzero or p ≥ 1. -/
def FiniteDimension : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) (hp : 0 < p), p < ∞ →
    letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp μ
    ∀ E : Submodule 𝕜 (Lp 𝕜 p μ), IsClosed (E : Set (Lp 𝕜 p μ)) →
      (∀ f : E, MemLp (f : Lp 𝕜 p μ) ∞ μ) → FiniteDimensional 𝕜 E
/-- The numerical estimate applied to families in the original E, with an
explicit change-of-exponent map on the same almost-everywhere classes. -/
def QuantitativeConclusion : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) (hp : 0 < p), p < ∞ →
    letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp μ
    ∀ E : Submodule 𝕜 (Lp 𝕜 p μ), IsClosed (E : Set (Lp 𝕜 p μ)) →
      (∀ f : E, MemLp (f : Lp 𝕜 p μ) ∞ μ) →
      ∃ A : ℝ, 0 < A ∧ ∃ h₂ : ∀ f : E, MemLp (f : Lp 𝕜 p μ) 2 μ,
        (∀ f : E, (eLpNorm (f : Lp 𝕜 p μ) ∞ μ).toReal ≤
          A * (eLpNorm (f : Lp 𝕜 p μ) 2 μ).toReal) ∧
        ∀ (n : ℕ) (v : Fin n → E),
          Orthonormal 𝕜 (fun i => toL2 μ p E h₂ (v i)) →
          (n : ℝ) ≤ A ^ 2 * μ.real Set.univ

/-- Dropping closedness fails on the concrete polynomial subspace of every
positive finite Lp([0,1]). -/
def PolynomialCounterexample : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (hp : 0 < p), p < ∞ →
    letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp intervalMeasure
    let E := (polynomialToLp 𝕜 p).range
    (∀ f : E, MemLp (f : Lp 𝕜 p intervalMeasure) ∞ intervalMeasure) ∧
    ¬ FiniteDimensional 𝕜 E ∧ ¬ IsClosed (E : Set (Lp 𝕜 p intervalMeasure))

/-- Counting-measure Lp is exactly the classical sequence ℓp: finite p-th
power sum, the usual quasi-norm, and unique pointwise representatives. -/
def SequenceIdentification : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (hp : 0 < p), p < ∞ →
    ∀ a : ℕ → 𝕜,
      (MemLp a p (Measure.count : Measure ℕ) ↔
        (∑' n, ‖a n‖ₑ ^ p.toReal) < ∞) ∧
      eLpNorm a p (Measure.count : Measure ℕ) =
        (∑' n, ‖a n‖ₑ ^ p.toReal) ^ (1 / p.toReal) ∧
      (MemLp a p (Measure.count : Measure ℕ) →
        ∃! f : Lp 𝕜 p (Measure.count : Measure ℕ), ⇑f = a)

/-- Without finite total measure, the closed, infinite-dimensional ℓp model
consists entirely of essentially bounded functions. The blocks are genuinely
disjoint unit intervals, each of measure one. -/
def InfiniteMeasureCounterexample : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (hp : 0 < p), p < ∞ →
    letI := GrothendieckBound.lpNormedGroup (V := 𝕜) p hp stripMeasure
    let E := (sequenceToIntervals 𝕜 p).range
    stripMeasure Set.univ = ∞ ∧
    (∀ n, stripMeasure (unitBlock n) = 1) ∧
    Pairwise (fun n m => Disjoint (unitBlock n) (unitBlock m)) ∧
    (∀ g : Lp 𝕜 p (Measure.count : Measure ℕ),
      ⇑(sequenceToIntervals 𝕜 p g) =ᵐ[stripMeasure] (fun x => g x.1)) ∧
    (∀ g : Lp 𝕜 p (Measure.count : Measure ℕ),
      eLpNorm (sequenceToIntervals 𝕜 p g) p stripMeasure =
        eLpNorm g p (Measure.count : Measure ℕ)) ∧
    Function.Injective (sequenceToIntervals 𝕜 p) ∧
    IsClosed (E : Set (Lp 𝕜 p stripMeasure)) ∧
    (∀ f : E, MemLp (f : Lp 𝕜 p stripMeasure) ∞ stripMeasure) ∧
    ¬ FiniteDimensional 𝕜 E

end Spec
end ExpandedFA.PartIV.GrothendieckLp
