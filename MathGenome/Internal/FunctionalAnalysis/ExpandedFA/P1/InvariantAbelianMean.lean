import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.InvariantHahnBanach
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.InvariantAbelianMean

/-! The abelian-group invariant-mean clause of `paper.tex:5384–5412`.
We extend evaluation on constants under the uniform norm using invariant
Hahn–Banach. Normalization and the norm bound imply positivity. Evaluating
arbitrary indicators then gives the invariant finitely additive probability. -/

noncomputable section

universe u

namespace ExpandedFA.P1
namespace AbelianMean

open scoped Classical

variable {G : Type u}

@[simp] lemma constant_apply (c : ℝ) (x : G) : constant G c x = c := rfl

@[simp] lemma translate_apply [Group G] (a : G) (f : BoundedRealFunction G) (x : G) :
    translate a f x = f (a * x) := rfl

@[simp] lemma indicator_apply (A : Set G) (x : G) :
    indicator A x = if x ∈ A then (1 : ℝ) else 0 := rfl

/-- The discrete representation includes every uniformly bounded function. -/
lemma exists_bounded_real_function (f : G → ℝ) (C : ℝ) (hf : ∀ x, ‖f x‖ ≤ C) :
    ∃ b : BoundedRealFunction G, ∀ x, b x = f x := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  exact ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f C hf, fun _ => rfl⟩

/-- Constants as a linear map into the bounded real functions. -/
def constantLinear (G : Type u) : ℝ →ₗ[ℝ] BoundedRealFunction G where
  toFun := constant G
  map_add' c d := by
    let : TopologicalSpace G := ⊥
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' c d := by
    let : TopologicalSpace G := ⊥
    apply BoundedContinuousFunction.ext
    intro x
    rfl

lemma translate_constant [Group G] (a : G) (c : ℝ) :
    translate a (constant G c) = constant G c := by
  let : TopologicalSpace G := ⊥
  apply BoundedContinuousFunction.ext
  intro x
  rfl

lemma norm_constant [Nonempty G] (c : ℝ) : ‖constant G c‖ = ‖c‖ := by
  let : TopologicalSpace G := ⊥
  exact BoundedContinuousFunction.norm_const_eq c

/-- The translation operators form a commuting semigroup for an abelian group. -/
def translationSemigroup (G : Type u) [CommGroup G] :
    Subsemigroup (Module.End ℝ (BoundedRealFunction G)) where
  carrier := Set.range (translate (G := G))
  mul_mem' := by
    let : TopologicalSpace G := ⊥
    rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨b * a, ?_⟩
    apply LinearMap.ext
    intro f
    apply BoundedContinuousFunction.ext
    intro x
    change f ((b * a) * x) = f (b * (a * x))
    rw [mul_assoc]

lemma translations_commute [CommGroup G]
    (A : Module.End ℝ (BoundedRealFunction G)) (hA : A ∈ translationSemigroup G)
    (B : Module.End ℝ (BoundedRealFunction G)) (hB : B ∈ translationSemigroup G) : Commute A B := by
  let : TopologicalSpace G := ⊥
  rcases hA with ⟨a, rfl⟩
  rcases hB with ⟨b, rfl⟩
  change translate a * translate b = translate b * translate a
  apply LinearMap.ext
  intro f
  apply BoundedContinuousFunction.ext
  intro x
  simp only [Module.End.mul_apply, translate_apply]
  rw [mul_left_comm a b]

lemma norm_translate_le [Group G] (a : G) (f : BoundedRealFunction G) :
    ‖translate a f‖ ≤ ‖f‖ := by
  let : TopologicalSpace G := ⊥
  exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
    fun x => f.norm_coe_le_norm (a * x)

lemma norm_sublinear : IsSublinear (fun f : BoundedRealFunction G => ‖f‖) := by
  refine ⟨norm_add_le, ?_⟩
  intro t ht f
  change ‖t • f‖ = t * ‖f‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

/-- Evaluation at the identity, restricted to the subspace of constants. -/
def constantEvaluation (G : Type u) [Group G] :
    (constantLinear G).range →ₗ[ℝ] ℝ where
  toFun f := (f : BoundedRealFunction G) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Invariant Hahn–Banach extends the normalized functional on constants. -/
lemma exists_dominated_invariant [CommGroup G] :
    ∃ F : BoundedRealFunction G →ₗ[ℝ] ℝ,
      (∀ c : ℝ, F (constant G c) = c) ∧
      (∀ f, F f ≤ ‖f‖) ∧ (∀ a f, F (translate a f) = F f) := by
  have hY : ∀ A ∈ translationSemigroup G, ∀ y ∈ (constantLinear G).range,
      A y ∈ (constantLinear G).range := by
    rintro A ⟨a, rfl⟩ y ⟨c, rfl⟩
    exact ⟨c, (translate_constant a c).symm⟩
  have hfinv : ∀ (A : Module.End ℝ (BoundedRealFunction G))
      (hA : A ∈ translationSemigroup G) (y : (constantLinear G).range),
      constantEvaluation G ⟨A y, hY A hA y y.property⟩ = constantEvaluation G y := by
    rintro A ⟨a, rfl⟩ ⟨y, c, rfl⟩
    rfl
  obtain ⟨F, hext, hbound, hinv⟩ := invariant_hahn_banach
    (fun f : BoundedRealFunction G => ‖f‖) norm_sublinear
    (translationSemigroup G) translations_commute
    (by rintro A ⟨a, rfl⟩ f; exact norm_translate_le a f)
    (constantLinear G).range hY (constantEvaluation G)
    (by
      let : TopologicalSpace G := ⊥
      exact fun f => BoundedContinuousFunction.apply_le_norm (f : BoundedRealFunction G) 1) hfinv
  refine ⟨F, ?_, hbound, fun a f => hinv _ ⟨a, rfl⟩ f⟩
  intro c
  exact hext ⟨constant G c, ⟨c, rfl⟩⟩

/-- The domination bound also controls the absolute value. -/
lemma norm_bound_of_dominated (F : BoundedRealFunction G →ₗ[ℝ] ℝ)
    (hF : ∀ f, F f ≤ ‖f‖) (f : BoundedRealFunction G) : ‖F f‖ ≤ ‖f‖ := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h := hF (-f)
    simp only [map_neg, norm_neg] at h
    linarith
  · exact hF f

/-- A normalized functional dominated by the uniform norm is positive. -/
lemma nonneg_of_dominated [Group G] (F : BoundedRealFunction G →ₗ[ℝ] ℝ)
    (hconst : ∀ c, F (constant G c) = c) (hF : ∀ f, F f ≤ ‖f‖)
    (f : BoundedRealFunction G) (hf : ∀ x, 0 ≤ f x) : 0 ≤ F f := by
  let : TopologicalSpace G := ⊥
  have hn : ‖constant G ‖f‖ - f‖ ≤ ‖f‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
    intro x
    change ‖‖f‖ - f x‖ ≤ ‖f‖
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · linarith [hf x]
    · exact sub_nonneg.mpr (BoundedContinuousFunction.apply_le_norm f x)
  have h := (hF (constant G ‖f‖ - f)).trans hn
  rw [map_sub, hconst] at h
  linarith

lemma exists_invariant_mean (G : Type u) [CommGroup G] :
    ∃ L : BoundedRealFunction G →L[ℝ] ℝ, IsInvariantMean L := by
  obtain ⟨F, hconst, hbound, hinv⟩ := exists_dominated_invariant (G := G)
  have hb (f) : ‖F f‖ ≤ 1 * ‖f‖ := by
    simpa using norm_bound_of_dominated F hbound f
  let L := F.mkContinuous 1 hb
  have hnorm : ‖L‖ = 1 := by
    apply le_antisymm
    · exact F.mkContinuous_norm_le zero_le_one hb
    · have h := L.le_opNorm (constant G 1)
      change ‖F (constant G 1)‖ ≤ ‖L‖ * ‖constant G 1‖ at h
      simpa only [hconst, norm_constant, norm_one, mul_one] using h
  exact ⟨L, hnorm, hconst, nonneg_of_dominated F hconst hbound, hinv⟩

lemma indicator_empty : indicator (∅ : Set G) = 0 := by
  let : TopologicalSpace G := ⊥
  apply BoundedContinuousFunction.ext
  intro x
  simp

lemma indicator_univ : indicator (Set.univ : Set G) = constant G 1 := by
  let : TopologicalSpace G := ⊥
  apply BoundedContinuousFunction.ext
  intro x
  simp

lemma indicator_nonneg (A : Set G) (x : G) : 0 ≤ indicator A x := by
  classical
  simp only [indicator_apply]
  split_ifs <;> norm_num

lemma indicator_union {A B : Set G} (h : Disjoint A B) :
    indicator (A ∪ B) = indicator A + indicator B := by
  let : TopologicalSpace G := ⊥
  classical
  apply BoundedContinuousFunction.ext
  intro x
  simp only [indicator_apply, BoundedContinuousFunction.add_apply, Set.mem_union]
  have hx : ¬(x ∈ A ∧ x ∈ B) := fun hx => Set.disjoint_left.mp h hx.1 hx.2
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp_all

/-- Precomposition by `a⁻¹` carries the indicator of `A` to that of `a A`. -/
lemma indicator_translate [Group G] (a : G) (A : Set G) :
    indicator ((fun x => a * x) '' A) = translate a⁻¹ (indicator A) := by
  let : TopologicalSpace G := ⊥
  classical
  apply BoundedContinuousFunction.ext
  intro x
  simp only [indicator_apply, translate_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨a⁻¹ * x, hx, mul_inv_cancel_left a x⟩

/-- A mean gives a probability on every subset, by evaluation on indicators. -/
lemma probability_of_mean [CommGroup G] (L : BoundedRealFunction G →L[ℝ] ℝ)
    (hL : IsInvariantMean L) :
    IsInvariantProbability (fun A : Set G => L (indicator A)) := by
  rcases hL with ⟨hnorm, hconst, hpos, hinv⟩
  refine ⟨fun A => hpos _ (indicator_nonneg A), ?_, ?_, ?_, ?_⟩
  · change L (indicator ∅) = 0
    rw [indicator_empty, map_zero]
  · change L (indicator Set.univ) = 1
    rw [indicator_univ, hconst]
  · intro A B h
    change L (indicator (A ∪ B)) = L (indicator A) + L (indicator B)
    rw [indicator_union h, map_add]
  · intro a A
    change L (indicator ((fun x => a * x) '' A)) = L (indicator A)
    rw [indicator_translate, hinv]

end AbelianMean

/-- Every abelian group has a positive norm-one invariant mean on all bounded
real functions and the induced invariant finitely additive probability on
its full power set. No topology on the group or countable additivity is used. -/
theorem invariant_abelian_mean (G : Type u) [CommGroup G] :
    ∃ (L : AbelianMean.BoundedRealFunction G →L[ℝ] ℝ) (μ : Set G → ℝ),
      AbelianMean.IsInvariantMean L ∧ AbelianMean.IsInvariantProbability μ ∧
      ∀ A : Set G, μ A = L (AbelianMean.indicator A) := by
  obtain ⟨L, hL⟩ := AbelianMean.exists_invariant_mean G
  exact ⟨L, fun A => L (AbelianMean.indicator A), hL,
    AbelianMean.probability_of_mean L hL, fun _ => rfl⟩

end ExpandedFA.P1
