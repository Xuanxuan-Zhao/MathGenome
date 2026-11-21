import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BaRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.InvariantAbelianMean
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Tactic.Linarith

/-! The real dual of all bounded functions is the space of signed charges
of bounded variation (`paper.tex:5384–5412`). We first integrate finite-range
functions, extend by uniform density, and identify the operator norm using
signed disjoint-family tests. Positivity is proved by positive simple
approximation. The invariant-probability clause reuses invariant Hahn–Banach
through the accepted abelian-mean theorem. -/

noncomputable section
universe u
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical

namespace ExpandedFA.P1.BaRepresentation
variable {S : Type u}
local instance : MeasurableSpace S := ⊤

@[simp] lemma simpleToBounded_apply (f : SimpleReal S) (x : S) :
    simpleToBounded f x = f x := rfl

/-- Additivity over a finite disjoint union follows from binary additivity. -/
lemma charge_biUnion {μ : Set S → ℝ} (hμ : IsFinitelyAdditive μ)
    {ι : Type*} (t : Finset ι) (A : ι → Set S)
    (hA : (↑t : Set ι).Pairwise (fun i j => Disjoint (A i) (A j))) :
    μ (⋃ i ∈ t, A i) = ∑ i ∈ t, μ (A i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hμ.1
  | @insert i t hi ih =>
    rw [Finset.coe_insert, Set.pairwise_insert] at hA
    have hd : Disjoint (A i) (⋃ j ∈ t, A j) := by
      apply Set.disjoint_left.2
      intro x hx hy
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hy
      exact Set.disjoint_left.1 (hA.2 j hj (by intro he; subst j; exact hi hj)).1 hx hxj
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi, hμ.2 _ _ hd, ih hA.1]

lemma charge_sum_fibers {μ : Set S → ℝ} (hμ : IsFinitelyAdditive μ)
    {β : Type*} (f : S → β) (t : Finset β) :
    μ (f ⁻¹' (t : Set β)) = ∑ b ∈ t, μ (f ⁻¹' {b}) := by
  classical
  have h := charge_biUnion hμ t (fun b => f ⁻¹' {b})
    (by intro i _ j _ hij; exact Set.disjoint_left.2 (by intro x hxi hxj; exact hij (hxi.symm.trans hxj)))
  have he : f ⁻¹' (t : Set β) = ⋃ b ∈ t, f ⁻¹' {b} := by
    ext x
    simp
  rwa [← he] at h

/-- Change of variables for a finite simple integral. Only finite additivity is used. -/
lemma map_simpleIntegral {μ : Set S → ℝ} (hμ : IsFinitelyAdditive μ)
    {β : Type*} (f : @SimpleFunc S ⊤ β) (g : β → ℝ) :
    simpleIntegral μ (f.map g) = ∑ b ∈ f.range, g b * μ (f ⁻¹' {b}) := by
  classical
  unfold simpleIntegral
  rw [SimpleFunc.range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases SimpleFunc.mem_range.1 hb with ⟨a, rfl⟩
  rw [SimpleFunc.map_preimage_singleton, charge_sum_fibers hμ, Finset.mul_sum]
  apply Finset.sum_congr
  · rfl
  · intro c hc
    have h := (Finset.mem_filter.1 hc).2
    rw [h]

/-- Integration on finite simple functions is real linear. -/
def simpleIntegralLinear {μ : Set S → ℝ} (hμ : IsFinitelyAdditive μ) :
    SimpleReal S →ₗ[ℝ] ℝ where
  toFun := simpleIntegral μ
  map_add' f g := by
    calc
      simpleIntegral μ (f + g) =
          ∑ x ∈ (SimpleFunc.pair f g).range,
            (x.1 * μ (SimpleFunc.pair f g ⁻¹' {x}) +
             x.2 * μ (SimpleFunc.pair f g ⁻¹' {x})) := by
        rw [SimpleFunc.add_eq_map₂, map_simpleIntegral hμ]
        exact Finset.sum_congr rfl fun a _ => add_mul _ _ _
      _ = simpleIntegral μ ((SimpleFunc.pair f g).map Prod.fst) +
          simpleIntegral μ ((SimpleFunc.pair f g).map Prod.snd) := by
        rw [Finset.sum_add_distrib, map_simpleIntegral hμ, map_simpleIntegral hμ]
      _ = _ := rfl
  map_smul' c f := by
    rw [SimpleFunc.smul_eq_map, map_simpleIntegral hμ]
    change (∑ r ∈ f.range, (c * r) * μ (f ⁻¹' {r})) =
      c * ∑ r ∈ f.range, r * μ (f ⁻¹' {r})
    simp_rw [Finset.mul_sum, mul_assoc]

/-- The inclusion of finite simple functions into all bounded functions. -/
def simpleInclusion : SimpleReal S →ₗ[ℝ] BoundedReal S where
  toFun := simpleToBounded
  map_add' _ _ := by
    let : TopologicalSpace S := ⊥
    ext x
    rfl
  map_smul' _ _ := by
    let : TopologicalSpace S := ⊥
    ext x
    rfl

lemma zero_mem_variationSums (μ : Set S → ℝ) : 0 ∈ variationSums μ :=
  ⟨∅, by simp, by simp⟩

lemma variation_nonneg {μ : Set S → ℝ} (hμ : HasBoundedVariation μ) :
    0 ≤ variation μ := le_csSup hμ (zero_mem_variationSums μ)

/-- The variation controls every finite simple integral in the uniform norm. -/
lemma simpleIntegral_bound {μ : Set S → ℝ} (hμ : HasBoundedVariation μ)
    (f : SimpleReal S) :
    ‖simpleIntegral μ f‖ ≤ variation μ * ‖simpleToBounded f‖ := by
  classical
  let : TopologicalSpace S := ⊥
  let P : Finset (Set S) := f.range.image (fun r => f ⁻¹' {r})
  have hp : (↑P : Set (Set S)).Pairwise Disjoint := by
    intro A hA B hB hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hB
    apply Set.disjoint_left.2
    intro x ha hb
    exact hne (by rw [ha.symm.trans hb])
  have hs : (∑ r ∈ f.range, |μ (f ⁻¹' {r})|) ≤ variation μ := by
    have hi : ∀ a ∈ f.range, ∀ b ∈ f.range,
        f ⁻¹' {a} = f ⁻¹' {b} → a = b := by
      intro a ha b _ hab
      obtain ⟨x, hx⟩ := SimpleFunc.mem_range.1 ha
      have : x ∈ f ⁻¹' {b} := hab ▸ hx
      exact hx.symm.trans this
    have he : (∑ A ∈ P, |μ A|) = ∑ r ∈ f.range, |μ (f ⁻¹' {r})| :=
      Finset.sum_image (by intro a ha b hb hab; exact hi a ha b hb hab)
    rw [← he]
    exact le_csSup hμ ⟨P, hp, rfl⟩
  calc
    ‖simpleIntegral μ f‖ ≤ ∑ r ∈ f.range, ‖r * μ (f ⁻¹' {r})‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ f.range, ‖simpleToBounded f‖ * |μ (f ⁻¹' {r})| := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.1 hr
      rw [norm_mul, Real.norm_eq_abs (μ _)]
      exact mul_le_mul_of_nonneg_right
        ((simpleToBounded f).norm_coe_le_norm x) (abs_nonneg _)
    _ ≤ variation μ * ‖simpleToBounded f‖ := by
      rw [← Finset.mul_sum, mul_comm (variation μ)]
      exact mul_le_mul_of_nonneg_left hs (norm_nonneg _)

/-- Quantize the bounded real range by a finite cover of its containing interval. -/
theorem simple_dense (f : BoundedReal S) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : SimpleReal S, ‖simpleToBounded s - f‖ < ε := by
  classical
  let : TopologicalSpace S := ⊥
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1
    (isCompact_Icc : IsCompact (Set.Icc (-‖f‖) ‖f‖)).totallyBounded (ε / 2) (by positivity)
  have hx (x : S) : ∃ y ∈ t, dist (f x) y < ε / 2 := by
    have hmem : f x ∈ Set.Icc (-‖f‖) ‖f‖ :=
      ⟨f.neg_norm_le_apply x, f.apply_le_norm x⟩
    rcases Set.mem_iUnion₂.1 (hcover hmem) with ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩
  choose g hgt hg using hx
  let s : SimpleReal S := ⟨g, fun _ => trivial, ht.subset (Set.range_subset_iff.2 hgt)⟩
  refine ⟨s, lt_of_le_of_lt ?_ (by linarith : ε / 2 < ε)⟩
  apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ ε / 2)).2
  intro x
  change ‖g x - f x‖ ≤ ε / 2
  rw [← dist_eq_norm, dist_comm]
  exact (hg x).le

lemma simpleInclusion_dense : DenseRange (simpleInclusion (S := S)) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨s, hs⟩ := simple_dense f ε hε
  refine ⟨s, ?_⟩
  change dist f (simpleToBounded s) < ε
  rw [dist_eq_norm, norm_sub_rev]
  exact hs

/-- A finite simple function is its finite sum of level-set indicators. -/
lemma simple_indicator_expansion (s : SimpleReal S) :
    simpleToBounded s = ∑ r ∈ s.range, r • AbelianMean.indicator (s ⁻¹' {r}) := by
  classical
  let : TopologicalSpace S := ⊥
  ext x
  change s x = (∑ r ∈ s.range, r • AbelianMean.indicator (s ⁻¹' {r})) x
  simp only [BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.smul_apply,
    AbelianMean.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, smul_eq_mul]
  rw [Finset.sum_eq_single (s x)]
  · simp
  · intro b hb hne
    simp [Ne.symm hne]
  · intro h
    exact (h (s.mem_range_self x)).elim

lemma functional_simpleIntegral (L : BoundedReal S →L[ℝ] ℝ) (s : SimpleReal S) :
    L (simpleToBounded s) = simpleIntegral (fun A => L (AbelianMean.indicator A)) s := by
  rw [simple_indicator_expansion, map_sum]
  simp only [map_smul, smul_eq_mul, simpleIntegral]

/-- Continuous functionals are determined by their values on all indicators. -/
lemma functional_ext {L M : BoundedReal S →L[ℝ] ℝ}
    (h : ∀ A : Set S, L (AbelianMean.indicator A) = M (AbelianMean.indicator A)) : L = M := by
  apply DFunLike.coe_injective
  apply simpleInclusion_dense.equalizer L.continuous M.continuous
  funext s
  change L (simpleToBounded s) = M (simpleToBounded s)
  simp only [functional_simpleIntegral, h]

/-- Integration extends uniquely from the dense simple functions. -/
def integralFunctional {μ : Set S → ℝ} (ha : IsFinitelyAdditive μ)
    (_hb : HasBoundedVariation μ) : BoundedReal S →L[ℝ] ℝ :=
  (simpleIntegralLinear ha).extendOfNorm simpleInclusion

lemma integralFunctional_simple {μ : Set S → ℝ} (ha : IsFinitelyAdditive μ)
    (hb : HasBoundedVariation μ) (s : SimpleReal S) :
    integralFunctional ha hb (simpleToBounded s) = simpleIntegral μ s :=
  LinearMap.extendOfNorm_eq simpleInclusion_dense
    ⟨variation μ, simpleIntegral_bound hb⟩ s

lemma integralFunctional_norm_le {μ : Set S → ℝ} (ha : IsFinitelyAdditive μ)
    (hb : HasBoundedVariation μ) : ‖integralFunctional ha hb‖ ≤ variation μ :=
  LinearMap.opNorm_extendOfNorm_le simpleInclusion_dense (variation_nonneg hb)
    (simpleIntegral_bound hb)

lemma simpleIntegral_eq_sum {μ : Set S → ℝ} (ha : IsFinitelyAdditive μ)
    (f : SimpleReal S) (t : Finset ℝ) (ht : f.range ⊆ t) :
    simpleIntegral μ f = ∑ r ∈ t, r * μ (f ⁻¹' {r}) := by
  classical
  apply Finset.sum_subset ht
  intro r _ hr
  rw [(f.preimage_eq_empty_iff r).2 hr, ha.1, mul_zero]

/-- The simple indicator uses no measurability restriction on its subset. -/
def simpleIndicator (A : Set S) : SimpleReal S :=
  (SimpleFunc.const S (1 : ℝ)).restrict A

lemma simpleIndicator_apply (A : Set S) (x : S) :
    simpleIndicator A x = if x ∈ A then (1 : ℝ) else 0 := by
  classical
  exact SimpleFunc.restrict_apply _ (by trivial) x

lemma simpleToBounded_indicator (A : Set S) :
    simpleToBounded (simpleIndicator A) = AbelianMean.indicator A := by
  let : TopologicalSpace S := ⊥
  ext x
  exact simpleIndicator_apply A x

lemma simpleIntegral_indicator {μ : Set S → ℝ} (ha : IsFinitelyAdditive μ)
    (A : Set S) : simpleIntegral μ (simpleIndicator A) = μ A := by
  classical
  have hr : (simpleIndicator A).range ⊆ {0, 1} := by
    intro r hr
    obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.1 hr
    simp only [simpleIndicator_apply]
    split_ifs <;> simp
  have hf : simpleIndicator A ⁻¹' {(1 : ℝ)} = A := by
    ext x
    simp [simpleIndicator_apply]
  rw [simpleIntegral_eq_sum ha _ _ hr]
  simp [hf]

lemma integralFunctional_indicator {μ : Set S → ℝ} (ha : IsFinitelyAdditive μ)
    (hb : HasBoundedVariation μ) (A : Set S) :
    integralFunctional ha hb (AbelianMean.indicator A) = μ A := by
  rw [← simpleToBounded_indicator, integralFunctional_simple, simpleIntegral_indicator ha]

/-- Disjointness bounds a signed indicator sum by the largest coefficient. -/
lemma norm_sum_indicator_le_one (P : Finset (Set S))
    (hp : (↑P : Set (Set S)).Pairwise Disjoint)
    (c : Set S → ℝ) (hc : ∀ A ∈ P, ‖c A‖ ≤ 1) :
    ‖∑ A ∈ P, c A • AbelianMean.indicator A‖ ≤ 1 := by
  classical
  let : TopologicalSpace S := ⊥
  apply (BoundedContinuousFunction.norm_le zero_le_one).2
  intro x
  simp only [BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.smul_apply,
    AbelianMean.indicator_apply, smul_eq_mul]
  by_cases hx : ∃ A ∈ P, x ∈ A
  · obtain ⟨A, hA, hxA⟩ := hx
    rw [Finset.sum_eq_single A]
    · simpa [hxA] using hc A hA
    · intro B hB hBA
      have hxB : x ∉ B := fun hxB => Set.disjoint_left.1 (hp hA hB hBA.symm) hxA hxB
      simp [hxB]
    · exact fun h => (h hA).elim
  · have hzero : ∀ A ∈ P, x ∉ A := by simpa using hx
    have hz : (∑ A ∈ P, c A * if x ∈ A then 1 else 0) = 0 :=
      Finset.sum_eq_zero (fun A hA => by rw [ite_eq_right (hzero A hA), mul_zero])
    rw [hz, norm_zero]
    exact zero_le_one

/-- The signed partition tests prove the full variation bound for any functional. -/
lemma functional_variation_bound (L : BoundedReal S →L[ℝ] ℝ)
    (P : Finset (Set S)) (hp : (↑P : Set (Set S)).Pairwise Disjoint) :
    (∑ A ∈ P, |L (AbelianMean.indicator A)|) ≤ ‖L‖ := by
  classical
  let c : Set S → ℝ := fun A => if 0 ≤ L (AbelianMean.indicator A) then 1 else -1
  let f : BoundedReal S := ∑ A ∈ P, c A • AbelianMean.indicator A
  have hc : ∀ A ∈ P, ‖c A‖ ≤ 1 := by
    intro A _
    dsimp [c]
    split_ifs <;> norm_num
  have hnorm : ‖f‖ ≤ 1 := norm_sum_indicator_le_one P hp c hc
  have hval : L f = ∑ A ∈ P, |L (AbelianMean.indicator A)| := by
    dsimp [f]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [map_smul]
    dsimp [c]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  rw [← hval]
  calc
    L f ≤ ‖L f‖ := Real.le_norm_self _
    _ ≤ ‖L‖ * ‖f‖ := L.le_opNorm f
    _ ≤ ‖L‖ := by simpa using mul_le_mul_of_nonneg_left hnorm (norm_nonneg L)

lemma functional_hasBoundedVariation (L : BoundedReal S →L[ℝ] ℝ) :
    HasBoundedVariation (fun A => L (AbelianMean.indicator A)) := by
  refine ⟨‖L‖, ?_⟩
  rintro r ⟨P, hp, rfl⟩
  exact functional_variation_bound L P hp

lemma functional_finitelyAdditive (L : BoundedReal S →L[ℝ] ℝ) :
    IsFinitelyAdditive (fun A => L (AbelianMean.indicator A)) := by
  refine ⟨?_, ?_⟩
  · change L (AbelianMean.indicator ∅) = 0
    rw [AbelianMean.indicator_empty, map_zero]
  · intro A B hd
    change L (AbelianMean.indicator (A ∪ B)) = L (AbelianMean.indicator A) + L (AbelianMean.indicator B)
    rw [AbelianMean.indicator_union hd, map_add]

lemma functional_variation_eq_norm (L : BoundedReal S →L[ℝ] ℝ) :
    variation (fun A => L (AbelianMean.indicator A)) = ‖L‖ := by
  let μ := fun A => L (AbelianMean.indicator A)
  have ha : IsFinitelyAdditive μ := functional_finitelyAdditive L
  have hb : HasBoundedVariation μ := functional_hasBoundedVariation L
  apply le_antisymm
  · apply csSup_le ⟨0, zero_mem_variationSums μ⟩
    rintro r ⟨P, hp, rfl⟩
    exact functional_variation_bound L P hp
  · have he : integralFunctional ha hb = L := functional_ext
      (by intro A; exact integralFunctional_indicator ha hb A)
    calc
      ‖L‖ = ‖integralFunctional ha hb‖ := congrArg norm he.symm
      _ ≤ variation μ := integralFunctional_norm_le ha hb

lemma simpleIntegral_nonneg {μ : Set S → ℝ} (hμ : ∀ A, 0 ≤ μ A)
    (s : SimpleReal S) (hs : ∀ x, 0 ≤ s x) : 0 ≤ simpleIntegral μ s := by
  apply Finset.sum_nonneg
  intro r hr
  obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.1 hr
  exact mul_nonneg (hs x) (hμ _)

/-- Nonnegative functions have nonnegative finite-range uniform approximants. -/
lemma nonneg_simple_dense (f : BoundedReal S) (hf : ∀ x, 0 ≤ f x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : SimpleReal S, (∀ x, 0 ≤ s x) ∧ ‖simpleToBounded s - f‖ < ε := by
  let : TopologicalSpace S := ⊥
  obtain ⟨s, hs⟩ := simple_dense f ε hε
  let p : SimpleReal S := s.map (fun r => max r 0)
  refine ⟨p, fun x => le_max_right _ _, lt_of_le_of_lt ?_ hs⟩
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
  intro x
  change |max (s x) 0 - f x| ≤ ‖simpleToBounded s - f‖
  calc
    |max (s x) 0 - f x| = |max (s x) 0 - max (f x) 0| := by rw [max_eq_left (hf x)]
    _ ≤ |s x - f x| := abs_max_sub_max_le_abs _ _ _
    _ ≤ ‖simpleToBounded s - f‖ := (simpleToBounded s - f).norm_coe_le_norm x

/-- The precise norm-preserving forward construction. -/
theorem forward : Specs.ExpandedFA.P1.BaRepresentation.forwardType.{u} := by
  intro S L
  exact ⟨functional_finitelyAdditive L, functional_hasBoundedVariation L,
    functional_variation_eq_norm L⟩

/-- Bounded charges integrate uniquely to continuous functionals on all bounded functions. -/
theorem representation : Specs.ExpandedFA.P1.BaRepresentation.representationType.{u} := by
  intro S μ ha hb
  let L := integralFunctional ha hb
  have hA : ∀ A, L (AbelianMean.indicator A) = μ A := integralFunctional_indicator ha hb
  have hnorm : ‖L‖ = variation μ := by
    have he : (fun A => L (AbelianMean.indicator A)) = μ := funext hA
    rw [← he]
    exact (functional_variation_eq_norm L).symm
  refine ⟨L, ⟨hA, integralFunctional_simple ha hb, hnorm⟩, ?_⟩
  intro M hM
  exact functional_ext (fun A => (hM.1 A).trans (hA A).symm)

/-- Positivity is preserved in both directions of the correspondence. -/
theorem positivity : Specs.ExpandedFA.P1.BaRepresentation.positivityType.{u} := by
  intro S L
  constructor
  · intro h A
    exact h _ (AbelianMean.indicator_nonneg A)
  · intro hμ f hf
    let K : Set (BoundedReal S) := {g | 0 ≤ L g}
    have hc : IsClosed K := isClosed_le continuous_const L.continuous
    have hcl : f ∈ closure K := by
      apply Metric.mem_closure_iff.2
      intro ε hε
      obtain ⟨s, hs, hdist⟩ := nonneg_simple_dense f hf ε hε
      refine ⟨simpleToBounded s, ?_, ?_⟩
      · change 0 ≤ L (simpleToBounded s)
        rw [functional_simpleIntegral]
        exact simpleIntegral_nonneg hμ s hs
      · rw [dist_eq_norm, norm_sub_rev]
        exact hdist
    exact hc.closure_subset hcl

/-- Uniform density, with no cardinality or nonemptiness assumption on the index set. -/
theorem density : Specs.ExpandedFA.P1.BaRepresentation.densityType.{u} := by
  intro S f ε hε
  exact simple_dense f ε hε

/-- All uniform simple approximations give the same integral. -/
theorem uniform_integration : Specs.ExpandedFA.P1.BaRepresentation.uniformIntegrationType.{u} := by
  intro S μ ha hb
  refine ⟨integralFunctional ha hb, integralFunctional_indicator ha hb, ?_⟩
  intro s f hs
  have h := (integralFunctional ha hb).continuous.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, integralFunctional_simple] using h

/-- A real linear bijection onto exactly the bounded-variation signed charges. -/
theorem linear_identification : Specs.ExpandedFA.P1.BaRepresentation.linearIdentificationType.{u} := by
  intro S
  let T : (BoundedReal S →L[ℝ] ℝ) →ₗ[ℝ] (Set S → ℝ) :=
    { toFun := fun L A => L (AbelianMean.indicator A)
      map_add' := by intro L M; rfl
      map_smul' := by intro c L; rfl }
  refine ⟨T, ?_, fun _ _ => rfl, ?_⟩
  · intro L M h
    exact functional_ext (fun A => congrFun h A)
  · intro μ
    constructor
    · rintro ⟨L, rfl⟩
      exact ⟨functional_finitelyAdditive L, functional_hasBoundedVariation L⟩
    · rintro ⟨ha, hb⟩
      exact ⟨integralFunctional ha hb, funext (integralFunctional_indicator ha hb)⟩

/-- The invariant extension dependency supplies the full-power-set probability. -/
theorem invariant_probability : Specs.ExpandedFA.P1.BaRepresentation.invariantProbabilityType.{u} := by
  intro G _
  obtain ⟨L, μ, _, hμ, _⟩ := ExpandedFA.P1.invariant_abelian_mean G
  exact ⟨μ, hμ⟩

end ExpandedFA.P1.BaRepresentation
