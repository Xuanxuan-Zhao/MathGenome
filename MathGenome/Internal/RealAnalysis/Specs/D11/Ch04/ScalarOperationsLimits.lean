import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.MeasurableMapTests
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.CompositionCoordinates
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Order.LiminfLimsup

/-! Independent statements for paper.tex:1236–1290. All target measurable
structures are Borel; the source sigma-algebra is arbitrary. The native
`EReal` has two infinities and `ENNReal` is [0,∞]. Nonnegative products use
native multiplication with 0 * ∞ = 0. No extended subtraction is used.
`finiteLimitSet` records actual convergence to a finite real value. -/

open Set Filter MeasurableSpace
open scoped Topology MeasureTheory ENNReal NNReal
universe u

namespace Specs.D11.Ch04.ScalarOperationsLimits

/-- Points at which the extended-real sequence converges to a finite value. -/
def finiteLimitSet {X : Type u} (f : ℕ → X → EReal) : Set X :=
  {x | ∃ l : ℝ, Tendsto (fun n => f n x) atTop (𝓝 (l : EReal))}

/-- The finite pointwise limit, assigned zero at all other points. -/
noncomputable def finiteLimit {X : Type u} (f : ℕ → X → EReal) (x : X) : ℝ := by
  classical
  exact if x ∈ finiteLimitSet f then (limsup (fun n => f n x) atTop).toReal else 0

def finiteLimitSet_type := ∀ {X : Type u}, (ℕ → X → EReal) → Set X

def finiteLimitSet_value : finiteLimitSet_type.{u} :=
  fun {_} f => {x | ∃ l : ℝ, Tendsto (fun n => f n x) atTop (𝓝 (l : EReal))}

def finiteLimit_type := ∀ {X : Type u}, (ℕ → X → EReal) → X → ℝ

noncomputable def finiteLimit_value : finiteLimit_type.{u} := by
  classical
  exact fun {_} f x => if x ∈ finiteLimitSet f then (limsup (fun n => f n x) atTop).toReal else 0

def real_linear_combination : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → ℝ) (a b : ℝ),
    @Measurable X ℝ m (borel ℝ) f → @Measurable X ℝ m (borel ℝ) g →
    @Measurable X ℝ m (borel ℝ) (fun x => a * f x + b * g x)

def real_product : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f → @Measurable X ℝ m (borel ℝ) g →
    @Measurable X ℝ m (borel ℝ) (fun x => f x * g x)

def real_nonzero_domain : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (g : X → ℝ),
    @Measurable X ℝ m (borel ℝ) g → MeasurableSet[m] {x | g x ≠ 0}

def real_quotient_on : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → ℝ),
    @Measurable X ℝ m (borel ℝ) f → @Measurable X ℝ m (borel ℝ) g →
    @Measurable {x : X // g x ≠ 0} ℝ
      (m.comap Subtype.val) (borel ℝ) (fun x => f x.val / g x.val)

def complex_linear_combination : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → ℂ) (a b : ℂ),
    @Measurable X ℂ m (borel ℂ) f → @Measurable X ℂ m (borel ℂ) g →
    @Measurable X ℂ m (borel ℂ) (fun x => a * f x + b * g x)

def complex_product : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → ℂ),
    @Measurable X ℂ m (borel ℂ) f → @Measurable X ℂ m (borel ℂ) g →
    @Measurable X ℂ m (borel ℂ) (fun x => f x * g x)

def complex_nonzero_domain : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (g : X → ℂ),
    @Measurable X ℂ m (borel ℂ) g → MeasurableSet[m] {x | g x ≠ 0}

def complex_quotient_on : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → ℂ),
    @Measurable X ℂ m (borel ℂ) f → @Measurable X ℂ m (borel ℂ) g →
    @Measurable {x : X // g x ≠ 0} ℂ
      (m.comap Subtype.val) (borel ℂ) (fun x => f x.val / g x.val)

def ereal_lt_set : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → EReal),
    @Measurable X EReal m (borel EReal) f →
    @Measurable X EReal m (borel EReal) g →
    MeasurableSet[m] {x | f x < g x}

def ereal_le_set : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → EReal),
    @Measurable X EReal m (borel EReal) f →
    @Measurable X EReal m (borel EReal) g →
    MeasurableSet[m] {x | f x ≤ g x}

def ereal_eq_set : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → EReal),
    @Measurable X EReal m (borel EReal) f →
    @Measurable X EReal m (borel EReal) g →
    MeasurableSet[m] {x | f x = g x}

def ereal_max : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → EReal),
    @Measurable X EReal m (borel EReal) f →
    @Measurable X EReal m (borel EReal) g →
    @Measurable X EReal m (borel EReal) (fun x => max (f x) (g x))

def ereal_min : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → EReal),
    @Measurable X EReal m (borel EReal) f →
    @Measurable X EReal m (borel EReal) g →
    @Measurable X EReal m (borel EReal) (fun x => min (f x) (g x))

def nonnegative_add : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → ℝ≥0∞),
    @Measurable X ℝ≥0∞ m (borel ℝ≥0∞) f →
    @Measurable X ℝ≥0∞ m (borel ℝ≥0∞) g →
    @Measurable X ℝ≥0∞ m (borel ℝ≥0∞) (fun x => f x + g x)

def nonnegative_mul : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → ℝ≥0∞),
    @Measurable X ℝ≥0∞ m (borel ℝ≥0∞) f →
    @Measurable X ℝ≥0∞ m (borel ℝ≥0∞) g →
    @Measurable X ℝ≥0∞ m (borel ℝ≥0∞) (fun x => f x * g x)

def nonnegative_const_mul : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (a : ℝ≥0) (f : X → ℝ≥0∞),
    @Measurable X ℝ≥0∞ m (borel ℝ≥0∞) f →
    @Measurable X ℝ≥0∞ m (borel ℝ≥0∞) (fun x => (a : ℝ≥0∞) * f x)

def ereal_nonnegative_add : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → EReal),
    @Measurable X EReal m (borel EReal) f →
    @Measurable X EReal m (borel EReal) g →
    (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
    @Measurable X EReal m (borel EReal) (fun x => f x + g x) ∧
      ∀ x, 0 ≤ f x + g x

def ereal_nonnegative_mul : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f g : X → EReal),
    @Measurable X EReal m (borel EReal) f →
    @Measurable X EReal m (borel EReal) g →
    (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
    @Measurable X EReal m (borel EReal) (fun x => f x * g x) ∧
      ∀ x, 0 ≤ f x * g x

def ereal_nonnegative_const_mul : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (a : ℝ) (f : X → EReal),
    0 ≤ a → @Measurable X EReal m (borel EReal) f → (∀ x, 0 ≤ f x) →
    @Measurable X EReal m (borel EReal) (fun x => (a : EReal) * f x) ∧
      ∀ x, 0 ≤ (a : EReal) * f x

def zero_times_infinity : Prop :=
  (0 : ℝ≥0∞) * ⊤ = 0 ∧ (⊤ : ℝ≥0∞) * 0 = 0 ∧
    (0 : EReal) * ⊤ = 0 ∧ (⊤ : EReal) * 0 = 0

def countable_sup : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : ℕ → X → EReal),
    (∀ n, @Measurable X EReal m (borel EReal) (f n)) →
    @Measurable X EReal m (borel EReal) (fun x => ⨆ n, f n x)

def countable_inf : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : ℕ → X → EReal),
    (∀ n, @Measurable X EReal m (borel EReal) (f n)) →
    @Measurable X EReal m (borel EReal) (fun x => ⨅ n, f n x)

def countable_limsup : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : ℕ → X → EReal),
    (∀ n, @Measurable X EReal m (borel EReal) (f n)) →
    @Measurable X EReal m (borel EReal) (fun x => limsup (fun n => f n x) atTop)

def countable_liminf : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : ℕ → X → EReal),
    (∀ n, @Measurable X EReal m (borel EReal) (f n)) →
    @Measurable X EReal m (borel EReal) (fun x => liminf (fun n => f n x) atTop)

def strict_comparison_formula : Prop :=
  ∀ {X : Type u} (f g : X → EReal),
    {x | f x < g x} = ⋃ q : ℚ, {x | f x < ((q : ℝ) : EReal)} ∩
      {x | ((q : ℝ) : EReal) < g x}

def sup_upper_level : Prop :=
  ∀ {X : Type u} (f : ℕ → X → EReal) (a : EReal),
    {x | a < ⨆ n, f n x} = ⋃ n, {x | a < f n x}

def inf_lower_level : Prop :=
  ∀ {X : Type u} (f : ℕ → X → EReal) (a : EReal),
    {x | (⨅ n, f n x) < a} = ⋃ n, {x | f n x < a}

def limsup_tail_formula : Prop :=
  ∀ {X : Type u} (f : ℕ → X → EReal) (x : X),
    limsup (fun n => f n x) atTop = ⨅ N : ℕ, ⨆ n ≥ N, f n x

def liminf_tail_formula : Prop :=
  ∀ {X : Type u} (f : ℕ → X → EReal) (x : X),
    liminf (fun n => f n x) atTop = ⨆ N : ℕ, ⨅ n ≥ N, f n x

def finite_limit_set_formula : Prop :=
  ∀ {X : Type u} (f : ℕ → X → EReal),
    finiteLimitSet f = {x | limsup (fun n => f n x) atTop = liminf (fun n => f n x) atTop} ∩
      {x | ⊥ < limsup (fun n => f n x) atTop ∧ limsup (fun n => f n x) atTop < ⊤}

def finite_limit_set_measurable : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : ℕ → X → EReal),
    (∀ n, @Measurable X EReal m (borel EReal) (f n)) →
    MeasurableSet[m] (finiteLimitSet f)

def finite_limit_measurable : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : ℕ → X → EReal),
    (∀ n, @Measurable X EReal m (borel EReal) (f n)) →
    @Measurable X ℝ m (borel ℝ) (finiteLimit f)

def finite_limit_ereal_measurable : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : ℕ → X → EReal),
    (∀ n, @Measurable X EReal m (borel EReal) (f n)) →
    @Measurable X EReal m (borel EReal) (fun x => (finiteLimit f x : EReal))

def finite_limit_eq : Prop :=
  ∀ {X : Type u} (f : ℕ → X → EReal) (x : X) (l : ℝ),
    Tendsto (fun n => f n x) atTop (𝓝 (l : EReal)) → finiteLimit f x = l

def finite_limit_tendsto : Prop :=
  ∀ {X : Type u} (f : ℕ → X → EReal) (x : X), x ∈ finiteLimitSet f →
    Tendsto (fun n => f n x) atTop (𝓝 ((finiteLimit f x : ℝ) : EReal))

def finite_limit_zero_off : Prop :=
  ∀ {X : Type u} (f : ℕ → X → EReal) (x : X), x ∉ finiteLimitSet f → finiteLimit f x = 0

def real_pointwise_limit : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : ℕ → X → ℝ) (g : X → ℝ),
    (∀ n, @Measurable X ℝ m (borel ℝ) (f n)) →
    (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
    @Measurable X ℝ m (borel ℝ) g

def complex_pointwise_limit : Prop :=
  ∀ {X : Type u} (m : MeasurableSpace X) (f : ℕ → X → ℂ) (g : X → ℂ),
    (∀ n, @Measurable X ℂ m (borel ℂ) (f n)) →
    (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
    @Measurable X ℂ m (borel ℂ) g

end Specs.D11.Ch04.ScalarOperationsLimits
