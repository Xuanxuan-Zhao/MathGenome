import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
Real PVMs and their bounded calculus, paper.tex 67–73 and 12374–12400.
The base has no topology and the real Hilbert space need not be separable or
nonzero. The normalization includes the constraint imposed by an empty base.
Only strong countable additivity is an axiom. The bounded realization below
contains no unbounded-operator data or assertions.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace ExpandedFA.SpectralMeasure
universe u v

/-- A normalized real PVM. No condition is imposed on nonmeasurable sets. -/
structure RealProjectionValuedMeasure (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  toFun : Set S → H →L[ℝ] H
  univ : toFun univ = 1
  selfAdjoint : ∀ B, MeasurableSet B → ∀ x y,
    ⟪toFun B x, y⟫_ℝ = ⟪x, toFun B y⟫_ℝ
  inter : ∀ B C, MeasurableSet B → MeasurableSet C →
    toFun B * toFun C = toFun (B ∩ C)
  countablyAdditive : ∀ (B : ℕ → Set S), (∀ n, MeasurableSet (B n)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) → ∀ x,
    HasSum (fun n => toFun (B n) x) (toFun (⋃ n, B n) x)

instance {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    CoeFun (RealProjectionValuedMeasure S H) (fun _ => Set S → H →L[ℝ] H) :=
  ⟨RealProjectionValuedMeasure.toFun⟩

/-- Everywhere bounded, measurable real functions, before any a.e. quotient. -/
structure RealBoundedFunction (S : Type u) [MeasurableSpace S] where
  toFun : S → ℝ
  measurable : Measurable toFun
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ s, |toFun s| ≤ C

namespace RealBoundedFunction
variable {S : Type u} [MeasurableSpace S]
instance : CoeFun (RealBoundedFunction S) (fun _ => S → ℝ) := ⟨toFun⟩

def const (c : ℝ) : RealBoundedFunction S :=
  ⟨fun _ => c, measurable_const, |c|, abs_nonneg c, fun _ => le_rfl⟩

def add (f g : RealBoundedFunction S) : RealBoundedFunction S := by
  refine ⟨fun s => f s + g s, f.measurable.add g.measurable, ?_⟩
  obtain ⟨C, hC, hf⟩ := f.bounded
  obtain ⟨D, hD, hg⟩ := g.bounded
  exact ⟨C + D, add_nonneg hC hD, fun s => (abs_add_le _ _).trans (add_le_add (hf s) (hg s))⟩

def smul (c : ℝ) (f : RealBoundedFunction S) : RealBoundedFunction S := by
  refine ⟨fun s => c * f s, measurable_const.mul f.measurable, ?_⟩
  obtain ⟨C, hC, hf⟩ := f.bounded
  refine ⟨|c| * C, mul_nonneg (abs_nonneg _) hC, fun s => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hf s) (abs_nonneg _)

def mul (f g : RealBoundedFunction S) : RealBoundedFunction S := by
  refine ⟨fun s => f s * g s, f.measurable.mul g.measurable, ?_⟩
  obtain ⟨C, hC, hf⟩ := f.bounded
  obtain ⟨D, hD, hg⟩ := g.bounded
  refine ⟨C * D, mul_nonneg hC hD, fun s => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf s) (hg s) (abs_nonneg _) hC

def ofSimple (f : SimpleFunc S ℝ) : RealBoundedFunction S := by
  classical
  refine ⟨f, f.measurable, ?_⟩
  refine ⟨∑ c ∈ f.range, |c|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), fun s => ?_⟩
  exact Finset.single_le_sum (fun c _ => abs_nonneg c) (f.mem_range_self s)

def indicator (B : Set S) (hB : MeasurableSet B) : RealBoundedFunction S :=
  ⟨B.indicator (fun _ => 1), measurable_const.indicator hB, 1, zero_le_one,
    fun s => by by_cases hs : s ∈ B <;> simp [hs]⟩
end RealBoundedFunction

/-- The complete finite range is used, including the zero fibre. -/
def realSimpleSpectralIntegral {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (E : RealProjectionValuedMeasure S H) (f : SimpleFunc S ℝ) : H →L[ℝ] H :=
  ∑ c ∈ f.range, c • E (f ⁻¹' {c})

/-- The bounded spectral theorem interface, independent of its construction.
All integrals against coefficient measures are the native signed/vector integral,
with separate integrability against the actual variation measure. -/
structure RealBoundedRealization {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (E : RealProjectionValuedMeasure S H) where
  coefficient : H → H → SignedMeasure S
  coefficient_apply : ∀ x y B, MeasurableSet B →
    coefficient x y B = ⟪x, E B y⟫_ℝ
  variation_bound : ∀ x y,
    (coefficient x y).variation univ ≤ ENNReal.ofReal (‖x‖ * ‖y‖)
  scalar : H → Measure S
  scalar_finite : ∀ x, IsFiniteMeasure (scalar x)
  scalar_apply : ∀ x B, MeasurableSet B →
    scalar x B = ENNReal.ofReal (‖E B x‖ ^ 2)
  scalar_mass : ∀ x, scalar x univ = ENNReal.ofReal (‖x‖ ^ 2)
  coefficient_diagonal : ∀ x, letI := scalar_finite x
    coefficient x x = (scalar x).toSignedMeasure
  integral : RealBoundedFunction S → H →L[ℝ] H
  integral_const : ∀ c, integral (.const c) = c • (1 : H →L[ℝ] H)
  integral_add : ∀ f g, integral (.add f g) = integral f + integral g
  integral_smul : ∀ c f, integral (.smul c f) = c • integral f
  integral_mul : ∀ f g, integral (.mul f g) = integral f * integral g
  integral_star : ∀ f, star (integral f) = integral f
  integral_bound : ∀ f C, 0 ≤ C → (∀ s, |f s| ≤ C) → ‖integral f‖ ≤ C
  integral_simple : ∀ f : SimpleFunc S ℝ,
    integral (.ofSimple f) = realSimpleSpectralIntegral E f
  integral_indicator : ∀ B (hB : MeasurableSet B), integral (.indicator B hB) = E B
  simple_approximation : ∀ f : RealBoundedFunction S, ∃ a : ℕ → SimpleFunc S ℝ,
    TendstoUniformly (fun n => (a n : S → ℝ)) f atTop
  integral_uniform_limit : ∀ (f : RealBoundedFunction S) (a : ℕ → SimpleFunc S ℝ),
    TendstoUniformly (fun n => (a n : S → ℝ)) f atTop →
    Tendsto (fun n => realSimpleSpectralIntegral E (a n)) atTop (𝓝 (integral f))
  coefficient_integrable : ∀ (f : RealBoundedFunction S) (x y : H), Integrable (f : S → ℝ) (coefficient x y).variation
  coefficient_integral : ∀ f x y, ⟪x, integral f y⟫_ℝ =
    (coefficient x y).integral (f : S → ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
  norm_square : ∀ f x, ‖integral f x‖ ^ 2 = ∫ s, |f s| ^ 2 ∂(scalar x)

namespace RealDefinitions.Spec
variable {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Type and independently fixed value of the exported simple spectral integral. -/
def SimpleIntegralType :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    RealProjectionValuedMeasure S H → SimpleFunc S ℝ → H →L[ℝ] H

def SimpleIntegralValue : SimpleIntegralType.{u, v} :=
  fun _ _ _ _ _ _ E f => ∑ c ∈ f.range, c • E (f ⁻¹' {c})

def ProjectionPropertiesFor : Prop := ∀ E : RealProjectionValuedMeasure S H,
  E ∅ = 0 ∧
  (∀ B, MeasurableSet B → E B * E B = E B ∧ star (E B) = E B) ∧
  (∀ B, MeasurableSet B → ‖E B‖ ≤ 1) ∧
  (∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
    ∀ x y, ⟪E B x, E C y⟫_ℝ = 0)

/-- This equivalence is under projection and intersection axioms alone, not
under the axiom of unconditional additivity which it is intended to justify. -/
def CountableAdditivityEquivalence : Prop :=
  ∀ (P : Set S → H →L[ℝ] H),
    (∀ B, MeasurableSet B → ∀ x y, ⟪P B x, y⟫_ℝ = ⟪x, P B y⟫_ℝ) →
    (∀ B C, MeasurableSet B → MeasurableSet C → P B * P C = P (B ∩ C)) →
    P ∅ = 0 → ∀ (B : ℕ → Set S), (∀ n, MeasurableSet (B n)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) → ∀ x,
    HasSum (fun n => P (B n) x) (P (⋃ n, B n) x) ↔
      Tendsto (fun N => ∑ n ∈ Finset.range N, P (B n) x) atTop
        (𝓝 (P (⋃ n, B n) x))

/-- Full equivalence of the two additivity axioms. In particular, zero at the
empty set is a consequence of ordered additivity, not an extra assumption. -/
def OrderedAdditivityEquivalenceFor : Prop :=
  ∀ (P : Set S → H →L[ℝ] H),
    (∀ B, MeasurableSet B → ∀ x y, ⟪P B x, y⟫_ℝ = ⟪x, P B y⟫_ℝ) →
    (∀ B C, MeasurableSet B → MeasurableSet C → P B * P C = P (B ∩ C)) →
    ((∀ (B : ℕ → Set S), (∀ n, MeasurableSet (B n)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → ∀ x,
      HasSum (fun n => P (B n) x) (P (⋃ n, B n) x)) ↔
    (∀ (B : ℕ → Set S), (∀ n, MeasurableSet (B n)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → ∀ x,
      Tendsto (fun N => ∑ n ∈ Finset.range N, P (B n) x) atTop
        (𝓝 (P (⋃ n, B n) x))))

def BoundedRealizationExistsFor : Prop :=
  ∀ E : RealProjectionValuedMeasure S H, Nonempty (RealBoundedRealization E)


/-- Universally quantified independent target, including empty and zero cases. -/
def ProjectionProperties : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    ProjectionPropertiesFor (S := S) (H := H)

def OrderedAdditivityEquivalence : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    OrderedAdditivityEquivalenceFor (S := S) (H := H)

def BoundedRealizationExists : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    BoundedRealizationExistsFor (S := S) (H := H)

end RealDefinitions.Spec
end ExpandedFA.SpectralMeasure
