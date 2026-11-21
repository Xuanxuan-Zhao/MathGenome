import MathGenome.Internal.FourierSobolev.Specs.P102.U4.GraphArea
import MathGenome.Internal.FourierSobolev.P102.U4.GraphAreaPieces
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology
namespace P102.U4.GraphArea
open GraphPieces

theorem graph_injective {m : ℕ} (γ : Space m → ℝ) : Function.Injective (graph γ) := by
  intro x y h
  exact congrArg (fun z : Ambient m => z.ofLp.1) h

theorem graph_lipschitzOn {m : ℕ} {γ : Space m → ℝ} {U : Set (Space m)}
    {L : ℝ≥0} (hL : LipschitzOnWith L γ U) :
    LipschitzOnWith ((2 : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal * max 1 L) (graph γ) U :=
  (WithLp.prod_lipschitzWith_toLp 2 (Space m) ℝ).comp_lipschitzOnWith
    (LipschitzWith.id.lipschitzOnWith.prodMk hL)

theorem graph_image_null {m : ℕ} {γ : Space m → ℝ} {U S : Set (Space m)}
    {L : ℝ≥0} (hL : LipschitzOnWith L γ U) (hSU : S ⊆ U)
    (hS : volume S = 0) : (μHE[m] : Measure (Ambient m)) (graph γ '' S) = 0 := by
  apply le_antisymm _ zero_le
  have h := normalized_lipschitz_image_le ((graph_lipschitzOn hL).mono hSU) m
  simpa only [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hS, mul_zero] using h

/-- Summing the upstream estimates loses only a base-null set, whose graph is null.
All sums and integrals are extended nonnegative ones; no finite-area hypothesis. -/
theorem area_bounds {m : ℕ} (hm : 0 < m) (U : Opens (Space m))
    (γ : Space m → ℝ) (L : ℝ≥0) (hL : LipschitzOnWith L γ U)
    (a : Space m → Space m) (ha : GradientRepresentative U γ a)
    (B : Set (Space m)) (hB : MeasurableSet B) (hBU : B ⊆ U)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ENNReal.ofReal ((1 - ε) ^ (m + 1)) *
        (∫⁻ x in B, ENNReal.ofReal (jacobian (a x))) ≤
      (μHE[m] : Measure (Ambient m)) (graph γ '' B) ∧
    (μHE[m] : Measure (Ambient m)) (graph γ '' B) ≤
      ENNReal.ofReal ((1 + ε) ^ (m + 1)) *
        (∫⁻ x in B, ENNReal.ofReal (jacobian (a x))) := by
  obtain ⟨E, q, hE, hp⟩ := graph_area_pieces m hm U γ L hL a ha ε hε hε2
  let S : ℕ → Set (Space m) := fun n => B ∩ E n
  have hSm (n : ℕ) : MeasurableSet (S n) := hB.inter (hE.1 n)
  have hSE (n : ℕ) : S n ⊆ E n := inter_subset_right
  have hSU : (⋃ n, S n) ⊆ U := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact hBU hn.1
  have hSB : (⋃ n, S n) ⊆ B := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact hn.1
  have hN : volume (B \ ⋃ n, S n) = 0 := by
    apply measure_mono_null _ hE.2.2.2.1
    intro x hx
    refine ⟨hBU hx.1, ?_⟩
    intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact hx.2 (mem_iUnion.mpr ⟨n, hx.1, hn⟩)
  have hcov : (⋃ n, S n) =ᵐ[volume] B := by
    apply ae_eq_set.mpr
    exact ⟨by simp [sdiff_eq_empty.mpr hSB], hN⟩
  have hdisj : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    exact (hE.2.2.1 hij).mono (hSE i) (hSE j)
  have himg (n : ℕ) : MeasurableSet (graph γ '' S n) := (hp n (S n) (hSm n) (hSE n)).1
  have himgdisj : Pairwise (fun i j => Disjoint (graph γ '' S i) (graph γ '' S j)) := by
    intro i j hij
    exact (disjoint_image_iff (graph_injective γ)).mpr (hdisj hij)
  have hgraphcov : (⋃ n, graph γ '' S n) =ᵐ[μHE[m]] (graph γ '' B) := by
    rw [← image_iUnion]
    apply ae_eq_set.mpr
    constructor
    · simp [sdiff_eq_empty.mpr (image_mono hSB)]
    · rw [← image_sdiff (graph_injective γ)]
      exact graph_image_null hL (sdiff_subset.trans hBU) hN
  have harea : (μHE[m] : Measure (Ambient m)) (graph γ '' B) =
      ∑' n, (μHE[m] : Measure (Ambient m)) (graph γ '' S n) := by
    rw [← measure_congr hgraphcov, measure_iUnion himgdisj himg]
  have hint : (∫⁻ x in B, ENNReal.ofReal (jacobian (a x))) =
      ∑' n, ∫⁻ x in S n, ENNReal.ofReal (jacobian (a x)) := by
    rw [← setLIntegral_congr hcov, lintegral_iUnion hSm hdisj]
  rw [harea, hint, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ⟨ENNReal.tsum_le_tsum fun n => (hp n (S n) (hSm n) (hSE n)).2.1,
    ENNReal.tsum_le_tsum fun n => (hp n (S n) (hSm n) (hSE n)).2.2⟩

theorem borel_area : Expected.BorelArea := by
  intro m hm U γ L hL a ha B hB hBU
  let I := ∫⁻ x in B, ENNReal.ofReal (jacobian (a x))
  have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε hpos hlt
    exact ⟨hpos, hlt⟩
  have hlo : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ (m + 1)) * I)
      (𝓝[>] 0) (𝓝 I) := by
    have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ (m + 1)))
        (𝓝[>] 0) (𝓝 1) := by
      have h : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ (m + 1))) :=
        ENNReal.continuous_ofReal.comp (by fun_prop)
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const ht (Or.inl one_ne_zero)
  have hup : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ (m + 1)) * I)
      (𝓝[>] 0) (𝓝 I) := by
    have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ (m + 1)))
        (𝓝[>] 0) (𝓝 1) := by
      have h : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ (m + 1))) :=
        ENNReal.continuous_ofReal.comp (by fun_prop)
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const ht (Or.inl one_ne_zero)
  apply le_antisymm
  · exact ge_of_tendsto hup (hε.mono fun ε h => (area_bounds hm U γ L hL a ha B hB hBU ε h.1 h.2).2)
  · exact le_of_tendsto hlo (hε.mono fun ε h => (area_bounds hm U γ L hL a ha B hB hBU ε h.1 h.2).1)

theorem zero_dimension : Expected.ZeroDimension := by
  refine ⟨volume_euclideanSpace_eq_dirac _, ?_, ?_⟩
  · intro a
    have : a = 0 := Subsingleton.elim _ _
    simp [this, jacobian]
  · intro γ B
    by_cases hB : B = ∅
    · exact Or.inl hB
    · have hB' : B = {0} := by
        obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hB
        ext y
        simp only [mem_singleton_iff]
        constructor
        · intro _; exact Subsingleton.elim _ _
        · intro _; simpa only [Subsingleton.elim y x] using hx
      refine Or.inr ⟨hB', ?_⟩
      rw [hB', image_singleton, normalized_zero_eq_count]
      simp

/-- Borel area in every dimension, including an empty or singleton zero-dimensional base. -/
theorem area {m : ℕ} (U : Opens (Space m)) (γ : Space m → ℝ) (L : ℝ≥0)
    (hL : LipschitzOnWith L γ U) (a : Space m → Space m)
    (ha : GradientRepresentative U γ a) (B : Set (Space m))
    (hB : MeasurableSet B) (hBU : B ⊆ U) :
    (μHE[m] : Measure (Ambient m)) (graph γ '' B) =
      ∫⁻ x in B, ENNReal.ofReal (jacobian (a x)) := by
  cases m with
  | zero =>
    rcases zero_dimension.2.2 γ B with h | ⟨h, hmass⟩
    · simp [h]
    · rw [hmass, h, zero_dimension.1]
      simp [zero_dimension.2.1]
  | succ n => exact borel_area (n + 1) (Nat.succ_pos _) U γ L hL a ha B hB hBU

/-- Extension from Borel sets to the Lebesgue completion, without any
finite-measure restriction on the set or its graph. -/
theorem completed_area : Expected.CompletedArea := by
  intro m U γ L hL a ha B hB hBU
  obtain ⟨C, hCB, hC, hCa⟩ := hB.exists_measurable_subset_ae_eq
  have hCU : C ⊆ U := hCB.trans hBU
  have himg : graph γ '' C =ᵐ[μHE[m]] graph γ '' B := by
    apply ae_eq_set.mpr
    constructor
    · simp [sdiff_eq_empty.mpr (image_mono hCB)]
    · rw [← image_sdiff (graph_injective γ)]
      exact graph_image_null hL (sdiff_subset.trans hBU) (ae_eq_set.mp hCa).2
  refine ⟨(image_measurability m U γ hL.continuousOn C hC hCU).nullMeasurableSet.congr himg, ?_⟩
  rw [← measure_congr himg, area U γ L hL a ha C hC hCU]
  exact setLIntegral_congr hCa

/-- A Borel extension of the parametrization, used only to express pushforward
identities. On the domain it is exactly the original parametrization. -/
def borelParam {m : ℕ} (U : Opens (Space m)) (γ : Space m → ℝ) : Space m → Ambient m :=
  by
    classical
    exact graph ((U : Set (Space m)).piecewise γ (fun _ => 0))

theorem borelParam_eq {m : ℕ} (U : Opens (Space m)) (γ : Space m → ℝ)
    {x : Space m} (hx : x ∈ U) : borelParam U γ x = graph γ x := by
  classical
  simp [borelParam, graph, hx]

theorem borelParam_embedding {m : ℕ} (U : Opens (Space m)) (γ : Space m → ℝ)
    (hγ : ContinuousOn γ U) : MeasurableEmbedding (borelParam U γ) := by
  classical
  have hg : Measurable ((U : Set (Space m)).piecewise γ (fun _ => (0 : ℝ))) :=
    hγ.measurable_piecewise continuousOn_const U.isOpen.measurableSet
  have h : Measurable (borelParam U γ) :=
    (WithLp.homeomorphProd 2 (Space m) ℝ).symm.continuous.measurable.comp
      (measurable_id.prodMk hg)
  exact h.measurableEmbedding (graph_injective _)

theorem measurable_density {m : ℕ} {a : Space m → Space m} (ha : Measurable a) :
    Measurable (density a) := (measurable_jacobian.comp ha).ennreal_ofReal

theorem density_pos {m : ℕ} (a : Space m → Space m) (x : Space m) : 0 < density a x :=
  ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one (one_le_jacobian _))

/-- The weighted base measure pushes forward to the graph's Hausdorff measure. -/
theorem map_weighted_volume {m : ℕ} (U : Opens (Space m))
    (γ : Space m → ℝ) (L : ℝ≥0) (hL : LipschitzOnWith L γ U)
    (a : Space m → Space m) (ha : GradientRepresentative U γ a) :
    Measure.map (borelParam U γ)
      ((volume.restrict (U : Set (Space m))).withDensity (density a)) =
        surfaceMeasure U γ := by
  have hf := borelParam_embedding U γ hL.continuousOn
  ext S hS
  rw [Measure.map_apply hf.measurable hS, withDensity_apply _ (hf.measurable hS),
    surfaceMeasure, Measure.restrict_apply hS]
  rw [Measure.restrict_restrict (hf.measurable hS)]
  have hB : MeasurableSet ((borelParam U γ) ⁻¹' S ∩ (U : Set (Space m))) :=
    (hf.measurable hS).inter U.isOpen.measurableSet
  unfold density
  rw [← area U γ L hL a ha _ hB inter_subset_right]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨hxS, hxU⟩, rfl⟩
    exact ⟨by simpa only [mem_preimage, borelParam_eq U γ hxU] using hxS, ⟨x, hxU, rfl⟩⟩
  · rintro ⟨hzS, x, hxU, rfl⟩
    exact ⟨x, ⟨by simpa only [mem_preimage, borelParam_eq U γ hxU] using hzS, hxU⟩, rfl⟩

/-- Positivity of J makes weighted and unweighted base measures have the same
null sets. This is essential for functions measurable in the completions. -/
theorem volume_absolutelyContinuous_weighted {m : ℕ} (U : Opens (Space m))
    (a : Space m → Space m) (ha : Measurable a) :
    volume.restrict (U : Set (Space m)) ≪
      (volume.restrict (U : Set (Space m))).withDensity (density a) := by
  apply withDensity_absolutelyContinuous' (measurable_density ha).aemeasurable
  exact Eventually.of_forall fun x => (density_pos a x).ne'

theorem nonnegative_integral : Expected.NonnegativeIntegral := by
  intro m U γ L hL a ha w hw
  have hw := hw.aemeasurable
  have hf := borelParam_embedding U γ hL.continuousOn
  have hmap := map_weighted_volume U γ L hL a ha
  have hw' : AEMeasurable (w ∘ borelParam U γ)
      ((volume.restrict (U : Set (Space m))).withDensity (density a)) := by
    apply hf.aemeasurable_map_iff.mp
    rwa [hmap]
  have hweq : (w ∘ borelParam U γ) =ᵐ[volume.restrict (U : Set (Space m))]
      (fun x => w (graph γ x)) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    simp only [Function.comp_apply, borelParam_eq U γ hx]
  refine ⟨((hw'.mono_ac (volume_absolutelyContinuous_weighted U a ha.1)).congr hweq).nullMeasurable, ?_⟩
  rw [← hmap, hf.lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_density ha.1)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply lintegral_congr_ae
  filter_upwards [hweq] with x hx
  exact (congrArg (fun z => density a x * z) hx).trans (mul_comm _ _)

theorem integral : Expected.Integral := by
  intro E _ _ _ m U γ L hL a ha w
  have hf := borelParam_embedding U γ hL.continuousOn
  have hmap := map_weighted_volume U γ L hL a ha
  have hweq : (fun x => (density a x).toReal • (w ∘ borelParam U γ) x)
      =ᵐ[volume.restrict (U : Set (Space m))]
      (fun x => jacobian (a x) • w (graph γ x)) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    simp only [Function.comp_apply, borelParam_eq U γ hx, density,
      ENNReal.toReal_ofReal (le_trans zero_le_one (one_le_jacobian _))]
  constructor
  · rw [← hmap, hf.integrable_map_iff,
      integrable_withDensity_iff_integrable_smul' (measurable_density ha.1)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    exact integrable_congr hweq
  · rw [← hmap, hf.integral_map,
      integral_withDensity_eq_integral_toReal_smul (measurable_density ha.1)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    exact integral_congr_ae hweq

theorem jacobian_pos {m : ℕ} (a : Space m) : 0 < jacobian a :=
  lt_of_lt_of_le zero_lt_one (one_le_jacobian a)

theorem jacobian_smul_unitNormal {m : ℕ} (a : Space m) :
    jacobian a • unitNormal a = conormal a := by
  rw [unitNormal, smul_smul, mul_inv_cancel₀ (jacobian_pos a).ne', one_smul]

theorem conormal_norm {m : ℕ} (a : Space m) : ‖conormal a‖ = jacobian a := by
  simp [conormal, jacobian, WithLp.prod_norm_eq_of_L2, add_comm]

theorem unitNormal_norm {m : ℕ} (a : Space m) : ‖unitNormal a‖ = 1 := by
  rw [unitNormal, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (jacobian_pos a)),
    conormal_norm, inv_mul_cancel₀ (jacobian_pos a).ne']

theorem unitNormal_zero (a : Space 0) : unitNormal a = WithLp.toLp 2 (0, (-1 : ℝ)) := by
  have ha : a = 0 := Subsingleton.elim _ _
  simp [unitNormal, zero_dimension.2.1, conormal, ha]

theorem measurable_normalField {m : ℕ} {a : Space m → Space m} (ha : Measurable a) :
    Measurable (normalField a) := by
  have hu : Measurable (unitNormal (m := m)) := by
    apply Continuous.measurable
    unfold unitNormal conormal
    exact (((show Continuous (jacobian (m := m)) by unfold jacobian; fun_prop).inv₀
      (fun b => (jacobian_pos b).ne')).smul
      ((WithLp.homeomorphProd 2 (Space m) ℝ).symm.continuous.comp
        (continuous_id.prodMk continuous_const)))
  exact hu.comp (ha.comp ((WithLp.homeomorphProd 2 (Space m) ℝ).continuous.fst.measurable))

/-- Jacobian cancellation in the full integration theorem proves flux and its
integrability equivalence. The identity even holds under the Bochner convention
for a nonintegrable field; the stated equivalence specifies genuine fluxes. -/
theorem flux : Expected.Flux := by
  intro m U γ L hL a ha F
  have hi := integral ℝ m U γ L hL a ha (fun z => inner ℝ (F z) (normalField a z))
  have hc : (fun x => jacobian (a x) • inner ℝ (F (graph γ x)) (normalField a (graph γ x))) =
      (fun x => inner ℝ (F (graph γ x)) (conormal (a x))) := by
    funext x
    change jacobian (a x) * inner ℝ (F (graph γ x)) (unitNormal (a x)) = _
    rw [← inner_smul_right, jacobian_smul_unitNormal]
  rwa [hc] at hi

def horizontal {m : ℕ} : Ambient m →L[ℝ] Space m :=
  (ContinuousLinearMap.fst ℝ (Space m) ℝ).comp
    (WithLp.linearEquiv 2 ℝ (Space m × ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

def vertical {m : ℕ} : Ambient m →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (Space m) ℝ).comp
    (WithLp.linearEquiv 2 ℝ (Space m × ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

def defining {m : ℕ} (γ : Space m → ℝ) (z : Ambient m) : ℝ := γ z.ofLp.1 - z.ofLp.2

theorem hasFDerivAt_graph {m : ℕ} {γ : Space m → ℝ} {x a : Space m}
    (h : HasFDerivAt γ (innerSL ℝ a) x) :
    HasFDerivAt (graph γ) (affineGraph a).toContinuousLinearMap x := by
  let q := (WithLp.linearEquiv 2 ℝ (Space m × ℝ)).symm.toContinuousLinearEquiv
  have hg := q.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk h)
  change HasFDerivAt (graph γ) _ x at hg
  apply hg.congr_fderiv
  ext v
  rfl

theorem conormal_inner {m : ℕ} (a : Space m) (v : Ambient m) :
    inner ℝ (conormal a) v = inner ℝ a v.ofLp.1 - v.ofLp.2 := by
  simp [conormal, WithLp.prod_inner_apply, sub_eq_add_neg]

theorem hasFDerivAt_defining {m : ℕ} {γ : Space m → ℝ} {x a : Space m}
    (h : HasFDerivAt γ (innerSL ℝ a) x) :
    HasFDerivAt (defining γ) (innerSL ℝ (conormal a)) (graph γ x) := by
  have hf := (h.comp (graph γ x) (horizontal (m := m)).hasFDerivAt).sub
    (vertical (m := m)).hasFDerivAt
  change HasFDerivAt (defining γ) _ (graph γ x) at hf
  apply hf.congr_fderiv
  ext v
  change inner ℝ a v.ofLp.1 - v.ofLp.2 = inner ℝ (conormal a) v
  exact (conormal_inner a v).symm

theorem affineGraph_range_eq {m : ℕ} (a : Space m) :
    ((affineGraph a).range : Set (Ambient m)) = {v | inner ℝ (conormal a) v = 0} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change inner ℝ (conormal a) (affineGraph a w) = 0
    rw [conormal_inner]
    exact sub_self _
  · intro hv
    refine ⟨v.ofLp.1, ?_⟩
    apply (WithLp.equiv 2 (Space m × ℝ)).injective
    change (v.ofLp.1, inner ℝ a v.ofLp.1) = v.ofLp
    apply Prod.ext
    · rfl
    · exact sub_eq_zero.mp (conormal_inner a v ▸ hv)

theorem tangent : Expected.Tangent := by
  intro m U γ x a hx h
  apply Set.Subset.antisymm
  · intro v hv
    rw [affineGraph_range_eq]
    have hzero : HasFDerivWithinAt (defining γ) (0 : Ambient m →L[ℝ] ℝ)
        (graph γ '' (U : Set (Space m))) (graph γ x) := by
      apply (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (graph γ x)).hasFDerivWithinAt.congr'
      · rintro _ ⟨y, hy, rfl⟩
        simp [defining, graph]
      · exact mem_image_of_mem _ hx
    have he := (hasFDerivAt_defining h).hasFDerivWithinAt.unique_on hzero hv
    exact he
  · rintro v ⟨w, rfl⟩
    exact (hasFDerivAt_graph h).hasFDerivWithinAt.mapsTo_tangent_cone
      (by rw [tangentConeAt_of_mem_nhds (U.isOpen.mem_nhds hx)]; trivial)

theorem eventually_pos_of_hasDerivAt_pos {f : ℝ → ℝ} {c : ℝ}
    (hf : HasDerivAt f c 0) (h0 : f 0 = 0) (hc : 0 < c) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < f r := by
  have hs := hf.tendsto_slope_zero_right.eventually (eventually_gt_nhds hc)
  filter_upwards [hs, self_mem_nhdsWithin] with r hr hrpos
  have hh : 0 < r⁻¹ * f r := by simpa [h0] using hr
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hrpos)).mp hh

theorem outward : Expected.Outward := by
  intro m U γ x a hx h
  let p := graph γ x
  let n := unitNormal a
  have hJ : inner ℝ (conormal a) n = jacobian a := by
    change inner ℝ (conormal a) ((jacobian a)⁻¹ • conormal a) = _
    rw [inner_smul_right, real_inner_self_eq_norm_sq, conormal_norm, pow_two,
      ← mul_assoc, inv_mul_cancel₀ (jacobian_pos a).ne', one_mul]
  have hline : HasDerivAt (fun r : ℝ => p + r • n) n 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const n).const_add p
  have hd : HasDerivAt (fun r : ℝ => defining γ (p + r • n)) (jacobian a) 0 := by
    have hdf : HasFDerivAt (defining γ) (innerSL ℝ (conormal a)) (p + (0 : ℝ) • n) := by
      simpa only [zero_smul, add_zero] using hasFDerivAt_defining h
    have hd := hdf.comp_hasDerivAt 0 hline
    change HasDerivAt (fun r : ℝ => defining γ (p + r • n)) (inner ℝ (conormal a) n) 0 at hd
    rwa [hJ] at hd
  have h0 : defining γ (p + (0 : ℝ) • n) = 0 := by simp [p, defining, graph]
  have hp := eventually_pos_of_hasDerivAt_pos hd h0 (jacobian_pos a)
  have hdneg : HasDerivAt (fun r : ℝ => -(defining γ (p + (-r) • n)))
      (jacobian a) 0 := by
    have hn0 : HasDerivAt (fun r : ℝ => -(defining γ (p + r • n)))
        (-jacobian a) (-(0 : ℝ)) := by
      convert hd.neg using 1
      simp only [neg_zero]
    convert hn0.comp 0 (hasDerivAt_neg (0 : ℝ)) using 1 <;> simp only [Function.comp_def, mul_neg, mul_one, neg_neg]
  have hn := eventually_pos_of_hasDerivAt_pos hdneg (by simpa using h0) (jacobian_pos a)
  have hbcont : Continuous (fun r : ℝ => horizontal (m := m) (p - r • n)) := by fun_prop
  have hb : ∀ᶠ r : ℝ in 𝓝[>] 0, (p - r • n).ofLp.1 ∈ U := by
    have ht : Tendsto (fun r : ℝ => horizontal (m := m) (p - r • n))
        (𝓝 (0 : ℝ)) (𝓝 x) := by simpa [p, horizontal, graph] using hbcont.tendsto 0
    exact (ht.eventually (U.isOpen.mem_nhds hx)).filter_mono nhdsWithin_le_nhds
  refine ⟨unitNormal_norm a, ?_, ?_⟩
  · intro v hv
    rw [tangent m U γ x a hx h, affineGraph_range_eq] at hv
    change inner ℝ ((jacobian a)⁻¹ • conormal a) v = 0
    have hv' : inner ℝ (conormal a) v = 0 := hv
    simp only [inner_smul_left, RCLike.conj_to_real, hv', mul_zero]
  · filter_upwards [hp, hn, hb] with r hrpos hrneg hrbase
    have hrneg' : defining γ (p - r • n) < 0 := by
      simpa only [neg_pos, neg_smul, ← sub_eq_add_neg] using hrneg
    constructor
    · intro hmem
      change _ ∧ γ (p + r • n).ofLp.1 < (p + r • n).ofLp.2 at hmem
      change 0 < γ (p + r • n).ofLp.1 - (p + r • n).ofLp.2 at hrpos
      linarith [hmem.2]
    · exact ⟨hrbase, sub_neg.mp hrneg'⟩

theorem ae_normal : Expected.AENormal := by
  intro m U γ L hL a ha
  rw [← map_weighted_volume U γ L hL a ha]
  apply (borelParam_embedding U γ hL.continuousOn).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _)
  filter_upwards [ha.2, ae_restrict_mem U.isOpen.measurableSet] with x hd hx
  rw [borelParam_eq U γ hx]
  exact outward m U γ x (a x) hx hd

theorem tangent_orthogonal {m : ℕ} (U : Opens (Space m)) (γ : Space m → ℝ)
    (x a : Space m) (hx : x ∈ U) (h : HasFDerivAt γ (innerSL ℝ a) x) :
    tangentConeAt ℝ (graph γ '' (U : Set (Space m))) (graph γ x) =
      ((ℝ ∙ unitNormal a)ᗮ : Set (Ambient m)) := by
  rw [tangent m U γ x a hx h, affineGraph_range_eq]
  ext v
  change inner ℝ (conormal a) v = 0 ↔ v ∈ (ℝ ∙ unitNormal a)ᗮ
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  change inner ℝ (conormal a) v = 0 ↔ inner ℝ ((jacobian a)⁻¹ • conormal a) v = 0
  rw [inner_smul_left]
  simp [(jacobian_pos a).ne']

/-- The two normal rays distinguish the two possible signs of a unit normal. -/
theorem outward_unique {m : ℕ} {Ω S : Set (Ambient m)} {p n n' : Ambient m}
    (hcone : tangentConeAt ℝ S p = ((ℝ ∙ n)ᗮ : Set (Ambient m)))
    (hn : OutwardUnitNormal Ω S p n) (hn' : OutwardUnitNormal Ω S p n') : n = n' := by
  have hperp : n' ∈ (ℝ ∙ n)ᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro v hv
    exact hn'.2.1 v (hcone.symm ▸ hv)
  rw [Submodule.orthogonal_orthogonal] at hperp
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hperp
  have habs : |c| = 1 := by
    simpa only [← hc, norm_smul, Real.norm_eq_abs, hn.1, mul_one] using hn'.1
  have hc2 : c ^ 2 = 1 := by nlinarith [sq_abs c]
  rcases (sq_eq_one_iff).mp hc2 with hc1 | hcneg
  · simpa only [hc1, one_smul] using hc
  · have hnn : n' = -n := by simpa only [hcneg, neg_one_smul] using hc.symm
    obtain ⟨r, hr, hr'⟩ := (hn.2.2.and hn'.2.2).exists
    have hnot : p - r • n ∉ Ω := by
      simpa only [hnn, smul_neg, ← sub_eq_add_neg] using hr'.1
    exact False.elim (hnot hr.2)

theorem affine_hasFDerivAt {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (p : Ambient m) :
    HasFDerivAt e e.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap p :=
  e.toAffineIsometry.toContinuousAffineMap.hasFDerivAt

theorem tangentCone_affine_image {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (S : Set (Ambient m)) (p : Ambient m) :
    tangentConeAt ℝ (e '' S) (e p) = e.linearIsometryEquiv '' tangentConeAt ℝ S p := by
  apply Set.Subset.antisymm
  · intro v hv
    refine ⟨e.linearIsometryEquiv.symm v, ?_, by simp⟩
    have h := (affine_hasFDerivAt e.symm (e p)).hasFDerivWithinAt.mapsTo_tangent_cone hv
    have hlin : e.symm.linearIsometryEquiv = e.linearIsometryEquiv.symm := by ext z; rfl
    rw [hlin] at h
    simp only [image_image, e.symm_apply_apply, image_id'] at h
    convert h using 1
    rfl
  · rintro _ ⟨v, hv, rfl⟩
    exact (affine_hasFDerivAt e p).hasFDerivWithinAt.mapsTo_tangent_cone hv

theorem affine_normal_ray {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (p n : Ambient m) (r : ℝ) :
    e (p + r • n) = e p + r • e.linearIsometryEquiv n := by
  rw [add_comm p, ← vadd_eq_add, e.map_vadd]
  simp only [map_smul, vadd_eq_add, add_comm]

theorem outward_affine_image {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    {Ω S : Set (Ambient m)} {p n : Ambient m} (hn : OutwardUnitNormal Ω S p n) :
    OutwardUnitNormal (e '' Ω) (e '' S) (e p) (e.linearIsometryEquiv n) := by
  refine ⟨by simpa using hn.1, ?_, ?_⟩
  · intro v hv
    rw [tangentCone_affine_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simpa using hn.2.1 w hw
  · filter_upwards [hn.2.2] with r hr
    constructor
    · rintro ⟨z, hz, heq⟩
      have heq' : e z = e (p + r • n) := heq.trans (affine_normal_ray e p n r).symm
      exact hr.1 (e.injective heq' ▸ hz)
    · refine ⟨p - r • n, hr.2, ?_⟩
      simpa only [neg_smul, ← sub_eq_add_neg] using affine_normal_ray e p n (-r)

theorem outward_congr {m : ℕ} {Ω Ω' S S' : Set (Ambient m)} {p n : Ambient m}
    (hΩ : Ω =ᶠ[𝓝 p] Ω') (hS : S =ᶠ[𝓝 p] S')
    (hn : OutwardUnitNormal Ω S p n) : OutwardUnitNormal Ω' S' p n := by
  have ht : tangentConeAt ℝ S p = tangentConeAt ℝ S' p :=
    tangentConeAt_congr (nhdsWithin_eq_iff_eventuallyEqSet.mpr hS)
  refine ⟨hn.1, ?_, ?_⟩
  · intro v hv
    exact hn.2.1 v (ht.symm ▸ hv)
  · have hplus : Tendsto (fun r : ℝ => p + r • n) (𝓝[>] 0) (𝓝 p) := by
      have hc : Continuous (fun r : ℝ => p + r • n) := by fun_prop
      simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hminus : Tendsto (fun r : ℝ => p - r • n) (𝓝[>] 0) (𝓝 p) := by
      have hc : Continuous (fun r : ℝ => p - r • n) := by fun_prop
      simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    filter_upwards [hn.2.2, hplus.eventually hΩ, hminus.eventually hΩ] with r hr hp hm
    exact ⟨by simpa only [← hp] using hr.1, by simpa only [← hm] using hr.2⟩

theorem isometry_image_orthogonal_singleton {m : ℕ} (q : Ambient m ≃ₗᵢ[ℝ] Ambient m)
    (n : Ambient m) :
    q '' ((ℝ ∙ n)ᗮ : Set (Ambient m)) = ((ℝ ∙ q n)ᗮ : Set (Ambient m)) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change q w ∈ (ℝ ∙ q n)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have hw' : inner ℝ n w = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
    simpa using hw'
  · intro hv
    refine ⟨q.symm v, ?_, by simp⟩
    change q.symm v ∈ (ℝ ∙ n)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have hv' : inner ℝ (q n) v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv
    have hinner := q.inner_map_map n (q.symm v)
    simpa using hinner.symm.trans (by simpa using hv')

theorem chart_agreement : Expected.ChartAgreement := by
  intro m U V γ δ x y a b e f hx hy hγ hδ hp hS hΩ
  have ht1 : tangentConeAt ℝ (e '' (graph γ '' (U : Set (Space m)))) (e (graph γ x)) =
      e.linearIsometryEquiv '' ((affineGraph a).range : Set (Ambient m)) := by
    rw [tangentCone_affine_image, tangent m U γ x a hx hγ]
  have ht2 : tangentConeAt ℝ (f '' (graph δ '' (V : Set (Space m)))) (e (graph γ x)) =
      f.linearIsometryEquiv '' ((affineGraph b).range : Set (Ambient m)) := by
    rw [hp, tangentCone_affine_image, tangent m V δ y b hy hδ]
  have ht := tangentConeAt_congr (𝕜 := ℝ) (nhdsWithin_eq_iff_eventuallyEqSet.mpr hS)
  refine ⟨ht1.symm.trans (ht.trans ht2), ?_⟩
  have hn1 := outward_affine_image e (outward m U γ x a hx hγ)
  have hn2 := outward_affine_image f (outward m V δ y b hy hδ)
  rw [← hp] at hn2
  have hn2' := outward_congr hΩ.symm hS.symm hn2
  apply outward_unique _ hn1 hn2'
  rw [tangentCone_affine_image, tangent_orthogonal U γ x a hx hγ,
    isometry_image_orthogonal_singleton]

theorem gradient_existence : Expected.GradientExistence := by
  intro m U γ L hL
  cases m with
  | zero =>
    refine ⟨fun _ => 0, measurable_const, ?_⟩
    have hγ : γ = fun _ => γ 0 := by
      funext x
      exact congrArg γ (Subsingleton.elim x 0)
    apply Eventually.of_forall
    intro x
    rw [hγ]
    simpa only [map_zero] using hasFDerivAt_const (𝕜 := ℝ) (γ 0) x
  | succ n => exact GraphPieces.gradient_existence (n + 1) (Nat.succ_pos _) U γ L hL

theorem aemeasurable_pullback : Expected.AEPullbackMeasurability := by
  intro E _ m U γ L hL a ha w
  have hf := borelParam_embedding U γ hL.continuousOn
  have hmap := map_weighted_volume U γ L hL a ha
  have hweq : (w ∘ borelParam U γ) =ᵐ[volume.restrict (U : Set (Space m))]
      (fun x => w (graph γ x)) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    simp only [Function.comp_apply, borelParam_eq U γ hx]
  constructor
  · intro hw
    rw [← hmap] at hw
    exact ((hf.aemeasurable_map_iff.mp hw).mono_ac
      (volume_absolutelyContinuous_weighted U a ha.1)).congr hweq
  · intro hw
    rw [← hmap]
    exact hf.aemeasurable_map_iff.mpr
      ((hw.congr hweq.symm).mono_ac (withDensity_absolutelyContinuous _ _))

theorem pullback_measurability : Expected.PullbackMeasurability := by
  intro E _ _ m U γ L hL a ha w
  constructor
  · intro hw
    exact ((aemeasurable_pullback E m U γ L hL a ha w).mp hw.aemeasurable).nullMeasurable
  · intro hw
    exact ((aemeasurable_pullback E m U γ L hL a ha w).mpr hw.aemeasurable).nullMeasurable

end P102.U4.GraphArea
