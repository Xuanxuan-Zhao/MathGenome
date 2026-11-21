import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.SimpleIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch04.SimpleApproximation
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity

/-! The nonnegative simple integral on an arbitrary positive measure space.
This is the finite level sum, not a scalar integral totalized on nonintegrable
functions. Finite real values are embedded into `ℝ≥0∞` before multiplying
by possibly infinite measures. -/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u v w
noncomputable section
namespace D11.Ch05.SimpleIntegral

def simpleIntegral {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (s : SimpleFunc X ℝ≥0) : ℝ≥0∞ :=
  (s.map (fun a : ℝ≥0 => (a : ℝ≥0∞))).lintegral μ

theorem level_formula : Specs.D11.Ch05.SimpleIntegral.level_formula := by
  intro X _ μ s
  exact SimpleFunc.map_lintegral _ s

theorem additivity {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (s t : SimpleFunc X ℝ≥0) :
    simpleIntegral μ (s + t) = simpleIntegral μ s + simpleIntegral μ t := by
  change ((s + t).map (fun a : ℝ≥0 => (a : ℝ≥0∞))).lintegral μ = _
  rw [SimpleFunc.map_add ENNReal.coe_add, SimpleFunc.add_lintegral]
  rfl

theorem homogeneity {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (s : SimpleFunc X ℝ≥0) (a : ℝ≥0) :
    simpleIntegral μ (SimpleFunc.const X a * s) = (a : ℝ≥0∞) * simpleIntegral μ s := by
  change ((SimpleFunc.const X a * s).map (fun a : ℝ≥0 => (a : ℝ≥0∞))).lintegral μ = _
  rw [SimpleFunc.map_mul ENNReal.coe_mul, SimpleFunc.map_const,
    SimpleFunc.const_mul_lintegral]
  rfl

theorem monotonicity : Specs.D11.Ch05.SimpleIntegral.monotonicity := by
  intro X _ μ s t h
  apply SimpleFunc.lintegral_mono_fun
  intro x
  exact ENNReal.coe_le_coe.mpr (h x)

theorem zero_integral {X : Type u} [MeasurableSpace X] (μ : Measure X) :
    simpleIntegral μ (0 : SimpleFunc X ℝ≥0) = 0 := by
  change (SimpleFunc.const X (0 : ℝ≥0∞)).lintegral μ = 0
  simp

theorem indicator_integral {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (a : ℝ≥0) (E : Set X) (hE : MeasurableSet E) :
    simpleIntegral μ ((SimpleFunc.const X a).restrict E) = (a : ℝ≥0∞) * μ E := by
  change (((SimpleFunc.const X a).restrict E).map (fun a : ℝ≥0 => (a : ℝ≥0∞))).lintegral μ = _
  have h : ((SimpleFunc.const X a).restrict E).map (fun a : ℝ≥0 => (a : ℝ≥0∞)) =
      (SimpleFunc.const X (a : ℝ≥0∞)).restrict E := by
    ext x
    simp only [SimpleFunc.map_apply, SimpleFunc.restrict_apply _ hE]
    by_cases hx : x ∈ E <;> simp [hx]
  rw [h, SimpleFunc.restrict_const_lintegral _ hE]

/-- Evaluation of finite sums of bundled simple functions. -/
lemma sum_apply {X : Type u} {ι : Type v} [MeasurableSpace X]
    (I : Finset ι) (s : ι → SimpleFunc X ℝ≥0) (x : X) :
    (∑ i ∈ I, s i) x = ∑ i ∈ I, s i x := by
  let ev : SimpleFunc X ℝ≥0 →+ ℝ≥0 :=
    { toFun := fun s => s x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum ev _ _

/-- Additivity gives the weighted indicator formula even for overlapping
sets; in particular it applies to all disjoint representations in the paper. -/
lemma weighted_indicator_formula {X : Type u} {ι : Type v} [MeasurableSpace X]
    (μ : Measure X) (I : Finset ι) (a : ι → ℝ≥0) (E : ι → Set X)
    (hE : ∀ i ∈ I, MeasurableSet (E i)) :
    simpleIntegral μ (∑ i ∈ I, (SimpleFunc.const X (a i)).restrict (E i)) =
      ∑ i ∈ I, (a i : ℝ≥0∞) * μ (E i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using zero_integral μ
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    rw [show simpleIntegral μ
      ((SimpleFunc.const X (a i)).restrict (E i) +
        ∑ j ∈ I, (SimpleFunc.const X (a j)).restrict (E j)) = _ from
      additivity μ _ _]
    rw [indicator_integral μ (a i) (E i) (hE i (Finset.mem_insert_self _ _))]
    rw [ih (fun j hj => hE j (Finset.mem_insert_of_mem hj))]

theorem representation_formula : Specs.D11.Ch05.SimpleIntegral.representation_formula := by
  classical
  intro X ι _ μ s I a E ha hE _ hrep
  let t : SimpleFunc X ℝ≥0 :=
    ∑ i ∈ I, (SimpleFunc.const X (Real.toNNReal (a i))).restrict (E i)
  have hst : s = t := by
    apply SimpleFunc.ext
    intro x
    apply NNReal.coe_injective
    rw [hrep x]
    change _ = ((∑ i ∈ I, (SimpleFunc.const X (Real.toNNReal (a i))).restrict (E i)) x : ℝ)
    rw [sum_apply, NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [SimpleFunc.restrict_apply _ (hE i hi)]
    by_cases hx : x ∈ E i <;> simp [hx, Real.toNNReal_of_nonneg (ha i hi)]
  change simpleIntegral μ s = _
  rw [hst, weighted_indicator_formula μ I _ E hE]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem representation_independent : Specs.D11.Ch05.SimpleIntegral.representation_independent := by
  classical
  intro X ι κ _ μ I J a b E F hE hF _ _ hrep
  let s : SimpleFunc X ℝ≥0 := ∑ i ∈ I, (SimpleFunc.const X (a i)).restrict (E i)
  let t : SimpleFunc X ℝ≥0 := ∑ j ∈ J, (SimpleFunc.const X (b j)).restrict (F j)
  have hst : s = t := by
    apply SimpleFunc.ext
    intro x
    change (∑ i ∈ I, (SimpleFunc.const X (a i)).restrict (E i)) x =
      (∑ j ∈ J, (SimpleFunc.const X (b j)).restrict (F j)) x
    rw [sum_apply, sum_apply]
    calc
      _ = ∑ i ∈ I, (E i).indicator (fun _ => a i) x := by
        apply Finset.sum_congr rfl
        intro i hi
        exact SimpleFunc.restrict_apply _ (hE i hi) x
      _ = ∑ j ∈ J, (F j).indicator (fun _ => b j) x := hrep x
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (SimpleFunc.restrict_apply (SimpleFunc.const X (b j)) (hF j hj) x).symm
  calc
    _ = simpleIntegral μ s := (weighted_indicator_formula μ I a E hE).symm
    _ = simpleIntegral μ t := congrArg (simpleIntegral μ) hst
    _ = _ := weighted_indicator_formula μ J b F hF

end D11.Ch05.SimpleIntegral
