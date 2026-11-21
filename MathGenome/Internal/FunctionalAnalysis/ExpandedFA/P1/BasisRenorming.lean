import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BasisRenorming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15PartialSums
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15SubsetProjections
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! Monotone and multiplier renorming in `fa2:p1:basis-renorming`.
The accepted coordinate-continuity and partial-sum theorems establish these
properties for the original raw basis; no boundedness of coordinates or
projections is added to its hypotheses. -/

open Filter Topology
noncomputable section
universe u v
namespace ExpandedFA.P1.BasisRenorming

open C15Basis.Spec BasisNormCompleteness.Spec

/-- The supremum of the norms of the original partial sums is complete,
equivalent to the given norm, and makes all partial sums contractive. -/
theorem raw_monotone_renorming : Spec.RawMonotoneRenorming.{u, v} := by
  intro 𝕜 E _ _ _ _ e h
  obtain ⟨T, hT, _, _⟩ := C15PartialSums.raw_partial_sum_bounds h
  obtain ⟨C, hC, hb⟩ := C15CoordinateContinuity.raw_basis_norm_equivalent h
  refine ⟨BasisNormCompleteness.raw_basis_complete h,
    ⟨C + 1, by linarith, fun x => ?_⟩, hT.contractive⟩
  exact (hb x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))

/-- Genuine finite bases, including the empty basis of the zero space. -/
theorem finite_monotone_renorming : Spec.FiniteMonotoneRenorming.{u, v} := by
  intro 𝕜 E _ _ _ _ d e h
  obtain ⟨T, hT, _, _, _, _⟩ := C15PartialSums.finite_partial_sum_bounds h
  obtain ⟨C, hC, hb⟩ := C15CoordinateContinuity.finite_basis_norm_equivalent h
  refine ⟨BasisNormCompleteness.finite_basis_complete h,
    ⟨C + 1, by linarith, fun x => ?_⟩, hT.contractive⟩
  exact (hb x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))

theorem empty_monotone_norm : Spec.EmptyMonotoneNorm.{u, v} := by
  intro 𝕜 E _ _ _ h x
  exact BasisNormCompleteness.empty_basis_norm h x

/-- The terms of an ordered convergent basis expansion tend to zero.
This needs neither unconditionality nor completeness. -/
theorem basis_terms_tendsto_zero {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e) (x : E) :
    Tendsto (fun n => rawCoordinates h x n • e n) atTop (𝓝 0) := by
  have hp := C15Basis.rawPartialSum_tendsto h x
  have ht := (hp.comp (tendsto_add_atTop_nat 1)).sub hp
  simpa only [Function.comp_apply, BasisNormCompleteness.BasisNormProof.raw_increment,
    sub_self] using ht

/-- In a normalized basis, every vector's scalar coordinates tend to zero. -/
theorem normalized_coordinates_norm_tendsto_zero {𝕜 : Type u} {E : Type v}
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e)
    (he : ∀ n, ‖e n‖ = 1) (x : E) :
    Tendsto (fun n => ‖rawCoordinates h x n‖) atTop (𝓝 0) := by
  simpa only [norm_smul, he, mul_one, norm_zero] using
    (basis_terms_tendsto_zero h x).norm

/-- This proves the obstruction independently of the remaining construction
of the coordinate product. The final algebra theorem applies it to the constructed
product by its coordinate formula; it rules out a two-sided identity in particular. -/
theorem normalized_coordinate_product_no_identity :
    Spec.NormalizedCoordinateProductNoIdentity.{u, v} := by
  intro 𝕜 E _ _ _ e h he m hm
  rintro ⟨u, hu⟩
  have hc (n : ℕ) : rawCoordinates h u n = 1 := by
    have hn := hm u (e n) n
    rw [hu] at hn
    simpa only [C15CoordinateContinuity.rawCoordinates_basis, Pi.single_eq_same,
      mul_one] using hn.symm
  have hz := normalized_coordinates_norm_tendsto_zero h he u
  simp only [hc, norm_one] at hz
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  exact one_ne_zero hbad

namespace MultiplierProof

/-- Bounded real weights cost at most twice the bound on all subset sums. -/
lemma real_weight_bound {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : Finset ι) (z : ι → V) (c : ι → ℝ) {r : ℝ}
    (hc : ∀ i ∈ F, |c i| ≤ 1)
    (hz : ∀ A ⊆ F, ‖∑ i ∈ A, z i‖ ≤ r) :
    ‖∑ i ∈ F, c i • z i‖ ≤ 2 * r := by
  classical
  obtain ⟨g, hg, he⟩ := exists_dual_vector'' ℝ (∑ i ∈ F, c i • z i)
  change g (∑ i ∈ F, c i • z i) = ‖∑ i ∈ F, c i • z i‖ at he
  let A := F.filter (fun i => 0 ≤ g (z i))
  let B := F.filter (fun i => ¬ 0 ≤ g (z i))
  have habs : (∑ i ∈ F, |g (z i)|) =
      g (∑ i ∈ A, z i) - g (∑ i ∈ B, z i) := by
    simp only [map_sum, Finset.sum_filter, A, B, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : 0 ≤ g (z i)
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (lt_of_not_ge h)]
  have hg_bound (v : V) : |g v| ≤ ‖v‖ := by
    exact (g.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _) hg)
  calc
    ‖∑ i ∈ F, c i • z i‖ = ∑ i ∈ F, c i * g (z i) := by
      rw [← he, map_sum]; simp
    _ ≤ ∑ i ∈ F, |g (z i)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact (le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hc i hi))
    _ = g (∑ i ∈ A, z i) - g (∑ i ∈ B, z i) := habs
    _ ≤ 2 * r := by
      have hA := (hg_bound (∑ i ∈ A, z i)).trans (hz A (Finset.filter_subset _ _))
      have hB := (hg_bound (∑ i ∈ B, z i)).trans (hz B (Finset.filter_subset _ _))
      have := (abs_le.mp hA).2
      have := (abs_le.mp hB).1
      linarith

/-- The same estimate for either manuscript scalar field. -/
lemma scalar_weight_bound {ι 𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (F : Finset ι) (z : ι → V) (c : ι → 𝕜) {r : ℝ} (_hr : 0 ≤ r)
    (hc : ∀ i ∈ F, ‖c i‖ ≤ 1)
    (hz : ∀ A ⊆ F, ‖∑ i ∈ A, z i‖ ≤ r) :
    ‖∑ i ∈ F, c i • z i‖ ≤ 4 * r := by
  let := NormedSpace.restrictScalars ℝ 𝕜 V
  have hreal := real_weight_bound F z (fun i => RCLike.re (c i))
    (fun i hi => (RCLike.abs_re_le_norm _).trans (hc i hi)) hz
  have himag := real_weight_bound F z (fun i => RCLike.im (c i))
    (fun i hi => (RCLike.abs_im_le_norm _).trans (hc i hi)) hz
  have heq : (∑ i ∈ F, c i • z i) =
      (∑ i ∈ F, RCLike.re (c i) • z i) +
        (RCLike.I : 𝕜) • (∑ i ∈ F, RCLike.im (c i) • z i) := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜),
      RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul, ← add_smul,
      mul_comm RCLike.I, RCLike.re_add_im]
  rw [heq]
  have hb : ‖(RCLike.I : 𝕜) • (∑ i ∈ F, RCLike.im (c i) • z i)‖ ≤ 2 * r := by
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by simpa only [RCLike.norm_I] using (show (if (RCLike.I : 𝕜) = 0 then 0 else 1 : ℝ) ≤ 1 by split_ifs <;> norm_num))).trans himag
  exact (norm_add_le _ _).trans (by linarith)


/-- Bounded scalar multiplication preserves unconditional summability. -/
lemma summable_unit_weights {ι 𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    {z : ι → V} (hz : Summable z) (c : ι → 𝕜) (hc : ∀ i, ‖c i‖ ≤ 1) :
    Summable (fun i => c i • z i) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨S, hS⟩ := summable_iff_vanishing_norm.mp hz (ε / 8) (by positivity)
  refine ⟨S, fun F hF => ?_⟩
  have hb := scalar_weight_bound F z c (show 0 ≤ ε / 8 by positivity)
    (fun i _ => hc i) (fun A hA =>
      (hS A (Finset.disjoint_of_subset_left hA hF)).le)
  exact hb.trans_lt (by linarith)

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]
variable (b : UnconditionalSchauderBasis ι 𝕜 E)

lemma summable_weights (c : ι → 𝕜) {R : ℝ} (hR : 0 ≤ R)
    (hc : ∀ i, ‖c i‖ ≤ R) (x : E) :
    Summable (fun i => (c i * b.coord i x) • b i) := by
  by_cases h : R = 0
  · have hz : ∀ i, c i = 0 := fun i => norm_eq_zero.mp (le_antisymm (h ▸ hc i) (norm_nonneg _))
    simp [hz]
  have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm h)
  have hu : ∀ i, ‖c i / (R : 𝕜)‖ ≤ 1 := by
    intro i
    rw [norm_div, RCLike.norm_ofReal, abs_of_pos hp, div_le_one hp]
    exact hc i
  have hs := (summable_unit_weights (b.expansion x).summable _ hu).const_smul (R : 𝕜)
  convert hs using 1
  ext i
  simp only [smul_smul]
  congr 1
  field_simp [RCLike.ofReal_ne_zero.mpr h]

/-- The canonical multiplier, with boundedness used only in its theorems. -/
def value (c : ι → 𝕜) (x : E) : E := ∑' i, (c i * b.coord i x) • b i

lemma value_hasSum (c : ι → 𝕜) {R : ℝ} (hR : 0 ≤ R)
    (hc : ∀ i, ‖c i‖ ≤ R) (x : E) :
    HasSum (fun i => (c i * b.coord i x) • b i) (value b c x) :=
  (summable_weights b c hR hc x).hasSum

lemma value_unit_bound {C : ℝ} (hC : ∀ A : Finset ι, ‖b.proj A‖ ≤ C)
    (c : ι → 𝕜) (hc : ∀ i, ‖c i‖ ≤ 1) (x : E) :
    ‖value b c x‖ ≤ 4 * C * ‖x‖ := by
  have hCp : 0 ≤ C := by simpa using hC ∅
  apply le_of_tendsto ((value_hasSum b c zero_le_one hc x).norm)
  apply Filter.Eventually.of_forall
  intro F
  have hb := scalar_weight_bound F (fun i => b.coord i x • b i) c
    (mul_nonneg hCp (norm_nonneg x)) (fun i _ => hc i) (by
      intro A hA
      rw [← GeneralSchauderBasis.proj_apply]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hC A) (norm_nonneg x)))
  simpa only [smul_smul, mul_assoc] using hb

lemma coord_value (c : ι → 𝕜) {R : ℝ} (hR : 0 ≤ R)
    (hc : ∀ i, ‖c i‖ ≤ R) (x : E) (i : ι) :
    b.coord i (value b c x) = c i * b.coord i x := by
  classical
  have hs := (b.coord i).hasSum (value_hasSum b c hR hc x)
  have ht := hasSum_single (f := fun j => b.coord i ((c j * b.coord j x) • b j))
    i (by intro j hji; simp [b.ortho, Ne.symm hji])
  exact hs.unique (by simpa [b.ortho, Pi.single_apply] using ht)

omit [CompleteSpace E] in
lemma ext_coordinates {x y : E} (h : ∀ i, b.coord i x = b.coord i y) : x = y :=
  C15SubsetProjections.SubsetProjectionProof.ext_coordinates b h


abbrev uNorm (x : E) : ℝ :=
  Spec.multiplierSupNorm b.basis (fun x i => b.coord i x) x

instance unitWeights_nonempty : Nonempty (Spec.UnitWeights ι 𝕜) :=
  ⟨⟨fun _ => 1, fun _ => by simp⟩⟩

lemma unit_bdd (x : E) :
    BddAbove (Set.range (fun c : Spec.UnitWeights ι 𝕜 => ‖value b c.val x‖)) := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  exact ⟨4 * C * ‖x‖, by rintro _ ⟨c, rfl⟩; exact value_unit_bound b hC _ c.property x⟩

lemma le_uNorm (c : ι → 𝕜) (hc : ∀ i, ‖c i‖ ≤ 1) (x : E) :
    ‖value b c x‖ ≤ uNorm b x :=
  le_ciSup (unit_bdd b x) (⟨c, hc⟩ : Spec.UnitWeights ι 𝕜)

omit [CompleteSpace E] in
lemma uNorm_le {x : E} {r : ℝ}
    (h : ∀ c : Spec.UnitWeights ι 𝕜, ‖value b c.val x‖ ≤ r) : uNorm b x ≤ r :=
  ciSup_le h

omit [CompleteSpace E] in
lemma value_one (x : E) : value b (fun _ => 1) x = x := by
  simpa only [value, one_mul] using (b.expansion x).tsum_eq

lemma norm_le_uNorm (x : E) : ‖x‖ ≤ uNorm b x := by
  simpa only [value_one] using le_uNorm b (fun _ => 1) (by simp) x

lemma uNorm_nonneg (x : E) : 0 ≤ uNorm b x :=
  (norm_nonneg x).trans (norm_le_uNorm b x)

lemma value_add (c : ι → 𝕜) (hc : ∀ i, ‖c i‖ ≤ 1) (x y : E) :
    value b c (x + y) = value b c x + value b c y := by
  apply ext_coordinates b
  intro i
  simp only [coord_value b c zero_le_one hc, map_add, mul_add]

lemma value_smul (c : ι → 𝕜) (hc : ∀ i, ‖c i‖ ≤ 1) (t : 𝕜) (x : E) :
    value b c (t • x) = t • value b c x := by
  apply ext_coordinates b
  intro i
  simp only [coord_value b c zero_le_one hc, map_smul, smul_eq_mul]
  ring

lemma uNorm_zero : uNorm b 0 = 0 := by
  apply le_antisymm _ (uNorm_nonneg b 0)
  apply uNorm_le b
  intro c
  simp [value]

lemma uNorm_add_le (x y : E) : uNorm b (x + y) ≤ uNorm b x + uNorm b y := by
  apply uNorm_le b
  intro c
  rw [value_add b _ c.property]
  exact (norm_add_le _ _).trans (add_le_add (le_uNorm b _ c.property _) (le_uNorm b _ c.property _))

lemma uNorm_smul_le (t : 𝕜) (x : E) : uNorm b (t • x) ≤ ‖t‖ * uNorm b x := by
  apply uNorm_le b
  intro c
  rw [value_smul b _ c.property, norm_smul]
  exact mul_le_mul_of_nonneg_left (le_uNorm b _ c.property _) (norm_nonneg _)

lemma uNorm_smul (t : 𝕜) (x : E) : uNorm b (t • x) = ‖t‖ * uNorm b x := by
  apply le_antisymm (uNorm_smul_le b t x)
  by_cases ht : t = 0
  · simp [ht, uNorm_nonneg]
  have hh := uNorm_smul_le b t⁻¹ (t • x)
  rw [inv_smul_smul₀ ht, norm_inv] at hh
  exact (le_inv_mul_iff₀ (norm_pos_iff.mpr ht)).mp hh

lemma uNorm_upper : ∃ K : ℝ, 0 < K ∧ ∀ x, uNorm b x ≤ K * ‖x‖ := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hp : 0 ≤ C := by simpa using hC ∅
  refine ⟨4 * C + 1, by positivity, fun x => ?_⟩
  apply uNorm_le b
  intro c
  exact (value_unit_bound b hC _ c.property x).trans
    (by nlinarith [norm_nonneg x])

lemma uNorm_complete (s : ℕ → E)
    (hs : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ k ≥ J,
      uNorm b (s j - s k) < ε) :
    ∃ x : E, ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, uNorm b (s j - x) < ε := by
  have hsc : CauchySeq s := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨J, hJ⟩ := hs ε hε
    exact ⟨J, fun j hj k hk => by
      rw [dist_eq_norm]; exact (norm_le_uNorm b _).trans_lt (hJ j hj k hk)⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hsc
  obtain ⟨K, hK, hKu⟩ := uNorm_upper b
  refine ⟨x, fun ε hε => ?_⟩
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hx) (ε / K) (by positivity)
  refine ⟨J, fun j hj => (hKu _).trans_lt ?_⟩
  have hh := hJ j hj
  rw [dist_eq_norm] at hh
  exact (mul_lt_mul_of_pos_left hh hK).trans_eq (mul_div_cancel₀ ε (ne_of_gt hK))

lemma unit_comp (c d : ι → 𝕜) (hc : ∀ i, ‖c i‖ ≤ 1) (hd : ∀ i, ‖d i‖ ≤ 1)
    (x : E) : value b d (value b c x) = value b (fun i => d i * c i) x := by
  have hdc : ∀ i, ‖d i * c i‖ ≤ 1 := fun i => by
    rw [norm_mul]; exact (mul_le_mul_of_nonneg_right (hd i) (norm_nonneg _)).trans (by simpa using hc i)
  apply ext_coordinates b
  intro i
  simp only [coord_value b _ zero_le_one hc, coord_value b _ zero_le_one hd,
    coord_value b _ zero_le_one hdc, mul_assoc]

lemma unit_contractive (c : ι → 𝕜) (hc : ∀ i, ‖c i‖ ≤ 1) (x : E) :
    uNorm b (value b c x) ≤ uNorm b x := by
  apply uNorm_le b
  intro d
  rw [unit_comp b c d.val hc d.property]
  apply le_uNorm b
  intro i
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (d.property i) (norm_nonneg _)).trans (by simpa using hc i)

lemma bounded_contractive (c : ι → 𝕜) {R : ℝ} (hR : 0 ≤ R)
    (hc : ∀ i, ‖c i‖ ≤ R) (x : E) :
    uNorm b (value b c x) ≤ R * uNorm b x := by
  by_cases hr : R = 0
  · have hz : ∀ i, c i = 0 := fun i => norm_eq_zero.mp (le_antisymm (hr ▸ hc i) (norm_nonneg _))
    simp [value, hz, hr, uNorm_zero]
  have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hr)
  have hu : ∀ i, ‖c i / (R : 𝕜)‖ ≤ 1 := by
    intro i
    rw [norm_div, RCLike.norm_ofReal, abs_of_pos hp, div_le_one hp]
    exact hc i
  have heq : value b c x = (R : 𝕜) • value b (fun i => c i / (R : 𝕜)) x := by
    apply ext_coordinates b
    intro i
    rw [coord_value b c hR hc, map_smul, coord_value b _ zero_le_one hu]
    simp only [smul_eq_mul]
    field_simp [RCLike.ofReal_ne_zero.mpr hr]
  rw [heq, uNorm_smul, RCLike.norm_ofReal, abs_of_pos hp]
  exact mul_le_mul_of_nonneg_left (unit_contractive b _ hu x) hR

/-- All parts of the displayed complete equivalent multiplier norm. -/
theorem native_multiplier_renorming :
    Spec.MultiplierRenorming b.basis (fun x i => b.coord i x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨M, hM⟩ := unit_bdd b x
    exact ⟨M, fun c => hM (Set.mem_range_self c)⟩
  · exact ⟨uNorm_nonneg b, fun x => ⟨fun h => norm_eq_zero.mp
      (le_antisymm (h ▸ norm_le_uNorm b x) (norm_nonneg x)),
      fun h => h ▸ uNorm_zero b⟩,
      uNorm_add_le b, uNorm_smul b, norm_le_uNorm b, uNorm_upper b, uNorm_complete b⟩
  · intro c R hR hc x
    exact ⟨value_hasSum b c hR hc x, coord_value b c hR hc x,
      bounded_contractive b c hR hc x⟩


/-- Solidity of the multiplier norm; division is zero at zero coordinates. -/
lemma uNorm_solid (x y : E) (h : ∀ i, ‖b.coord i x‖ ≤ ‖b.coord i y‖) :
    uNorm b x ≤ uNorm b y := by
  let c : ι → 𝕜 := fun i => b.coord i x / b.coord i y
  have hc : ∀ i, ‖c i‖ ≤ 1 := by
    intro i
    dsimp [c]
    by_cases hi : b.coord i y = 0
    · simp [hi]
    · rw [norm_div, div_le_one (norm_pos_iff.mpr hi)]
      exact h i
  have heq : value b c y = x := by
    apply ext_coordinates b
    intro i
    rw [coord_value b c zero_le_one hc]
    dsimp [c]
    by_cases hi : b.coord i y = 0
    · have hx : b.coord i x = 0 := norm_eq_zero.mp (by simpa [hi] using h i)
      simp [hi, hx]
    · exact div_mul_cancel₀ _ hi
  rw [← heq]
  exact unit_contractive b c hc y

lemma coord_norm_le (he : ∀ i, ‖b i‖ = 1) (x : E) (i : ι) :
    ‖b.coord i x‖ ≤ uNorm b x := by
  classical
  let c : ι → 𝕜 := Pi.single i 1
  have hc : ∀ j, ‖c j‖ ≤ 1 := by intro j; by_cases h : j = i <;> simp [c, h]
  have heq : value b c x = b.coord i x • b i := by
    apply ext_coordinates b
    intro j
    rw [coord_value b c zero_le_one hc]
    simp only [map_smul, smul_eq_mul, b.ortho]
    by_cases hj : j = i <;> simp [c, hj]
  have hb := le_uNorm b c hc x
  rwa [heq, norm_smul, he, mul_one] at hb

/-- Multiplication is the coordinate multiplier whose coefficients are those
of the other factor, bounded by its multiplier norm under normalization. -/
def product (x y : E) : E := value b (fun i => b.coord i y) x

lemma coord_product (he : ∀ i, ‖b i‖ = 1) (x y : E) (i : ι) :
    b.coord i (product b x y) = b.coord i x * b.coord i y := by
  rw [product, coord_value b _ (uNorm_nonneg b y) (fun i => coord_norm_le b he y i)]
  exact mul_comm _ _

theorem native_coordinate_algebra (he : ∀ i, ‖b i‖ = 1) :
    Spec.CoordinateAlgebra b.basis (fun x i => b.coord i x) (product b) := by
  refine ⟨coord_product b he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    apply ext_coordinates b
    intro i
    simp only [coord_product b he, mul_assoc]
  · intro x y
    apply ext_coordinates b
    intro i
    simp only [coord_product b he, mul_comm]
  · intro x y z
    apply ext_coordinates b
    intro i
    simp only [coord_product b he, map_add, mul_add]
  · intro x y z
    apply ext_coordinates b
    intro i
    simp only [coord_product b he, map_add, add_mul]
  · intro t x y
    apply ext_coordinates b
    intro i
    simp only [coord_product b he, map_smul, smul_eq_mul, mul_assoc]
  · intro t x y
    apply ext_coordinates b
    intro i
    simp only [coord_product b he, map_smul, smul_eq_mul]
    ring
  · intro x y
    exact (bounded_contractive b _ (uNorm_nonneg b y) (fun i => coord_norm_le b he y i) x).trans_eq
      (mul_comm _ _)

end MultiplierProof

namespace RealLatticeProof
open MultiplierProof
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (b : UnconditionalSchauderBasis ι ℝ E)

def absolute (x : E) : E :=
  value b (fun i => if 0 ≤ b.coord i x then 1 else -1) x

lemma coord_absolute (x : E) (i : ι) : b.coord i (absolute b x) = |b.coord i x| := by
  have hc : ∀ j, ‖(if 0 ≤ b.coord j x then 1 else -1 : ℝ)‖ ≤ 1 := by
    intro j; split_ifs <;> norm_num
  rw [absolute, coord_value b _ zero_le_one hc]
  split_ifs with hi
  · rw [one_mul, abs_of_nonneg hi]
  · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hi)]

def supremum (x y : E) : E := (1 / 2 : ℝ) • (x + y + absolute b (x - y))
def infimum (x y : E) : E := (1 / 2 : ℝ) • (x + y - absolute b (x - y))

lemma coord_supremum (x y : E) (i : ι) :
    b.coord i (supremum b x y) = max (b.coord i x) (b.coord i y) := by
  simp only [supremum, map_smul, map_add, coord_absolute, map_sub, smul_eq_mul]
  by_cases h : b.coord i x ≤ b.coord i y
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [max_eq_left (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]; ring

lemma coord_infimum (x y : E) (i : ι) :
    b.coord i (infimum b x y) = min (b.coord i x) (b.coord i y) := by
  simp only [infimum, map_smul, map_sub, map_add, coord_absolute, smul_eq_mul]
  by_cases h : b.coord i x ≤ b.coord i y
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]; ring

/-- Coordinate order and coordinate maxima/minima, on the original E. -/
@[instance_reducible] def lattice : Lattice E where
  le x y := ∀ i, b.coord i x ≤ b.coord i y
  le_refl x i := le_refl _
  le_trans x y z hxy hyz i := (hxy i).trans (hyz i)
  le_antisymm x y hxy hyx := ext_coordinates b (fun i => le_antisymm (hxy i) (hyx i))
  sup := supremum b
  le_sup_left x y i := by rw [coord_supremum]; exact le_max_left _ _
  le_sup_right x y i := by rw [coord_supremum]; exact le_max_right _ _
  sup_le x y z hx hy i := by rw [coord_supremum]; exact max_le (hx i) (hy i)
  inf := infimum b
  inf_le_left x y i := by rw [coord_infimum]; exact min_le_left _ _
  inf_le_right x y i := by rw [coord_infimum]; exact min_le_right _ _
  le_inf x y z hy hz i := by rw [coord_infimum]; exact le_min (hy i) (hz i)

theorem native_real_coordinate_lattice :
    Spec.RealCoordinateLattice b.basis (fun x i => b.coord i x) := by
  refine ⟨lattice b, fun x y => Iff.rfl, ?_, ?_, ?_⟩
  · intro x y z h i
    simpa only [map_add] using add_le_add (h i) (le_refl (b.coord i z))
  · intro t ht x y h i
    simpa only [map_smul, smul_eq_mul] using mul_le_mul_of_nonneg_left (h i) ht
  · intro x y h
    apply uNorm_solid b x y
    simpa only [Real.norm_eq_abs] using h

end RealLatticeProof

/-- The original raw Schauder hypothesis supplies continuous coordinates;
unconditionality changes only the summation filter, preserving all coordinates. -/
theorem raw_native_unconditional_basis {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e)
    (hu : C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 E e) :
    ∃ b : UnconditionalSchauderBasis ℕ 𝕜 E,
      b.basis = e ∧ ∀ i x, b.coord i x = rawCoordinates h x i := by
  obtain ⟨b, hb, hc, _⟩ := C15CoordinateContinuity.raw_native_basis h
  let bu : UnconditionalSchauderBasis ℕ 𝕜 E :=
    { basis := b.basis
      coord := b.coord
      ortho := b.ortho
      expansion := by
        intro x
        have hx := (C15Unconditional.isUnconditionalSchauderBasis_iff 𝕜 E e).mp hu |>.2
          x (rawCoordinates h x)
          ((C01Banach.hasSequentialSum_iff E _ x).mpr (C15Basis.rawCoordinates_tendsto h x))
        simpa only [hb, hc] using
          (C15Unconditional.hasUnconditionalSum_iff_hasSum _ _).mp hx }
  exact ⟨bu, hb, hc⟩

theorem raw_multiplier_renorming : Spec.RawMultiplierRenorming.{u, v} := by
  intro 𝕜 E _ _ _ _ e h hu
  obtain ⟨b, hb, hc⟩ := raw_native_unconditional_basis h hu
  simpa only [hb, hc] using MultiplierProof.native_multiplier_renorming b

theorem finite_multiplier_renorming : Spec.FiniteMultiplierRenorming.{u, v} := by
  intro 𝕜 E _ _ _ _ d e h
  obtain ⟨b, hb, hc, _⟩ := C15CoordinateContinuity.finite_native_basis h
  simpa only [hb, hc] using MultiplierProof.native_multiplier_renorming b

theorem raw_real_coordinate_lattice : Spec.RawRealCoordinateLattice.{v} := by
  intro E _ _ _ e h hu
  obtain ⟨b, hb, hc⟩ := raw_native_unconditional_basis h hu
  simpa only [hb, hc] using RealLatticeProof.native_real_coordinate_lattice b

theorem finite_real_coordinate_lattice : Spec.FiniteRealCoordinateLattice.{v} := by
  intro E _ _ _ d e h
  obtain ⟨b, hb, hc, _⟩ := C15CoordinateContinuity.finite_native_basis h
  simpa only [hb, hc] using RealLatticeProof.native_real_coordinate_lattice b

theorem raw_normalized_coordinate_algebra : Spec.RawNormalizedCoordinateAlgebra.{u, v} := by
  intro 𝕜 E _ _ _ _ e h hu he
  obtain ⟨b, hb, hc⟩ := raw_native_unconditional_basis h hu
  have hn : ∀ i, ‖b i‖ = 1 := by simpa only [hb] using he
  have hm : Spec.CoordinateAlgebra e (rawCoordinates h) (MultiplierProof.product b) := by
    simpa only [hb, hc] using MultiplierProof.native_coordinate_algebra b hn
  exact ⟨MultiplierProof.product b, hm, normalized_coordinate_product_no_identity h he _ hm.1⟩

theorem finite_normalized_coordinate_algebra : Spec.FiniteNormalizedCoordinateAlgebra.{u, v} := by
  intro 𝕜 E _ _ _ _ d e h he
  obtain ⟨b, hb, hc, _⟩ := C15CoordinateContinuity.finite_native_basis h
  have hn : ∀ i, ‖b i‖ = 1 := by simpa only [hb] using he
  exact ⟨MultiplierProof.product b, by
    simpa only [hb, hc] using MultiplierProof.native_coordinate_algebra b hn⟩

end ExpandedFA.P1.BasisRenorming
