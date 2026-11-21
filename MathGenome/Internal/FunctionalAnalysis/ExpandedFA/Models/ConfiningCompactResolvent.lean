import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.ConfiningCompactResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.ConfiningSchrodingerRealization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.RellichEmbeddings
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.CompactNormalClassification

set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 50000

noncomputable section
open MeasureTheory Set TopologicalSpace Filter
open scoped InnerProductSpace ComplexConjugate Topology ENNReal lp
attribute [local instance 2000] NormedAddCommGroup.toSeminormedAddCommGroup

namespace ExpandedFA.Models.ConfiningCompactResolvent
open WeightedConfiningEnergySpace ConfiningSchrodingerRealization
open ExpandedFA.Sobolev ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜]

lemma IsConfining.positiveAtInfinity {p : Potential} (hp : IsConfining p) :
    PositiveAtInfinity p := by
  obtain ⟨R, _, hR⟩ := hp 1
  exact ⟨1, zero_lt_one, R, hR⟩

/-- Forget the weight and change the finite derivative norm from ℓ² to ℓ¹. -/
def toSobolev (p : Potential) : Space 𝕜 p →L[𝕜]
    Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 1 ⊤ 1 2 :=
  (sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm.toContinuousLinearMap.comp
    ((WithLp.fstL 2 𝕜 (H1 𝕜) (L2 𝕜)).comp (weightedGraph 𝕜 p).subtypeL)

@[simp] lemma toSobolev_value (p : Potential) (u : Space 𝕜 p) :
    (toSobolev p u).val (zeroIndex 1 1) = value u := rfl

lemma volume_to_line : MeasurePreserving (id : Line → Line) volume lineMeasure :=
  ⟨measurable_id, by simp [lineMeasure]⟩
lemma line_to_volume : MeasurePreserving (id : Line → Line) lineMeasure volume :=
  ⟨measurable_id, by simp [lineMeasure]⟩

def lineL2Isometry : L2 𝕜 →ₗᵢ[𝕜] Lp 𝕜 2 (volume : Measure Line) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 id volume_to_line

lemma lineL2Isometry_coe (f : L2 𝕜) : lineL2Isometry f =ᵐ[volume] f :=
  Lp.coeFn_compMeasurePreserving f volume_to_line

def lineL2Equiv : L2 𝕜 ≃ₗᵢ[𝕜] Lp 𝕜 2 (volume : Measure Line) :=
  LinearIsometryEquiv.ofSurjective lineL2Isometry (by
    intro f
    let g : L2 𝕜 := Lp.compMeasurePreserving id line_to_volume f
    refine ⟨g, Lp.ext ?_⟩
    have hg : g =ᵐ[volume] f := by
      have h := Lp.coeFn_compMeasurePreserving f line_to_volume
      simpa only [lineMeasure, Opens.coe_top, Measure.restrict_univ, Function.comp_def, id_eq] using h
    exact (lineL2Isometry_coe g).trans hg)

lemma lineL2Equiv_coe (f : L2 𝕜) : lineL2Equiv f =ᵐ[volume] f :=
  lineL2Isometry_coe f

lemma wholeUnderlying_toSobolev (p : Potential) (u : Space 𝕜 p) :
    Rellich.wholeUnderlying (toSobolev p u) = lineL2Equiv (value u) := by
  apply Lp.ext
  exact (Rellich.wholeUnderlying_coe _).trans (lineL2Equiv_coe _).symm

/-- The weighted component controls the L² tail whenever p ≥ c⁻² there. -/
lemma tail_norm_le (p : Potential) (u : Space 𝕜 p) {c R : ℝ} (hc : 0 < c)
    (hR : ∀ x : ℝ, R ≤ |x| → c⁻¹ ^ 2 ≤ p.toContinuousMap x) :
    ‖KolmogorovRieszSpec.LpRestrictValue 2 volume
      (Metric.closedBall (0 : Line) R)ᶜ (lineL2Equiv (value u))‖ ≤ c * ‖weighted u‖ := by
  let s := (Metric.closedBall (0 : Line) R)ᶜ
  let v := KolmogorovRieszSpec.LpRestrictValue 2 volume s (lineL2Equiv (value u))
  let w := KolmogorovRieszSpec.LpRestrictValue 2 volume s (lineL2Equiv (weighted u))
  have hbound : ‖v‖ ≤ c * ‖w‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    have hweight := weighted_ae p u
    simp only [lineMeasure, Opens.coe_top, Measure.restrict_univ] at hweight
    have hv := (Lp.memLp (lineL2Equiv (value u))).restrict s |>.coeFn_toLp
    have hw := (Lp.memLp (lineL2Equiv (weighted u))).restrict s |>.coeFn_toLp
    filter_upwards [hv, hw, ae_restrict_of_ae (lineL2Equiv_coe (value u)),
      ae_restrict_of_ae (lineL2Equiv_coe (weighted u)), ae_restrict_of_ae hweight,
      ae_restrict_mem measurableSet_closedBall.compl] with x hv hw hx hy hz hs
    change ‖v x‖ ≤ c * ‖w x‖
    dsimp only [v, w, KolmogorovRieszSpec.LpRestrictValue]
    rw [hv, hw, hx, hy, hz]
    have hnorm : ‖x‖ = |x 0| := by
      have heq : x = fun _ => x 0 := by funext i; fin_cases i; rfl
      conv_lhs => rw [heq]
      simp
    have hxR : R ≤ |x 0| := by
      have hnot : ¬ ‖x‖ ≤ R := by simpa [s, Metric.mem_closedBall, dist_zero_right] using hs
      rw [hnorm] at hnot
      exact (lt_of_not_ge hnot).le
    have hp := hR (x 0) hxR
    have hsqrt : c⁻¹ ≤ Real.sqrt (p.toContinuousMap (x 0)) := by
      exact (Real.le_sqrt (by positivity) (p.nonneg _)).mpr hp
    have hcs : 1 ≤ c * Real.sqrt (p.toContinuousMap (x 0)) := by
      calc
        1 = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hc.le
    rw [norm_mul, weight, RCLike.norm_ofReal,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [norm_nonneg (value u x), mul_le_mul_of_nonneg_right hcs (norm_nonneg (value u x))]
  calc
    _ = ‖v‖ := rfl
    _ ≤ c * ‖w‖ := hbound
    _ ≤ c * ‖lineL2Equiv (weighted u)‖ := mul_le_mul_of_nonneg_left
      (ExpandedFA.Sobolev.norm_lpRestrict_le (p := 2) (μ := volume) s _) hc.le
    _ = c * ‖weighted u‖ := by rw [LinearIsometryEquiv.norm_map]

lemma weighted_norm_le {p : Potential} (u : Space 𝕜 p) : ‖weighted u‖ ≤ ‖u‖ := by
  have h := weighted_norm_formula 𝕜 p u
  nlinarith [sq_nonneg ‖derivative u‖, sq_nonneg ‖value u‖,
    norm_nonneg u, norm_nonneg (weighted u)]

lemma uniform_tails (p : Potential) (hp : IsConfining p)
    (B : Set (Space 𝕜 p)) (hB : Bornology.IsBounded B) :
    KolmogorovRieszSpec.UniformLpTails 2 ((fun u => lineL2Equiv (value u)) '' B) := by
  obtain ⟨C, hC, hb⟩ := hB.exists_pos_norm_le
  intro ε hε
  let c := ε / (2 * C)
  have hc : 0 < c := div_pos hε (by positivity)
  obtain ⟨R, hR, hpot⟩ := hp (c⁻¹ ^ 2)
  refine ⟨R, hR, ?_⟩
  rintro f ⟨u, hu, rfl⟩
  calc
    _ ≤ c * ‖weighted u‖ := tail_norm_le p u hc hpot
    _ ≤ c * C := mul_le_mul_of_nonneg_left ((weighted_norm_le u).trans (hb u hu)) hc.le
    _ < ε := by dsimp [c]; field_simp; nlinarith

lemma toSobolev_norm_le (p : Potential) (u : Space 𝕜 p) :
    ‖toSobolev p u‖ ≤ 2 * ‖u‖ := by
  change ‖(toSobolev p u).val‖ ≤ _
  rw [PiLp.norm_eq_of_L1, sum_indices]
  change ‖value u‖ + ‖derivative u‖ ≤ 2 * ‖u‖
  have hv := value_norm_le u
  have hn := weighted_norm_formula 𝕜 p u
  have hd : ‖derivative u‖ ≤ ‖u‖ := by
    nlinarith [sq_nonneg ‖value u‖, sq_nonneg ‖weighted u‖,
      norm_nonneg u, norm_nonneg (derivative u)]
  linarith

/-- Rellich's local compactness plus the confining tail bound gives global
precompactness. The equivalent Kolmogorov–Riesz criterion packages this gluing. -/
theorem compact_inclusion :
    Specs.ExpandedFA.Models.ConfiningCompactResolvent.CompactInclusion := by
  intro 𝕜 _ p hp
  letI : NormedSpace 𝕜 (Space 𝕜 p) := (spaceInnerProductSpace 𝕜 p).toNormedSpace
  let L := toSobolev (𝕜 := 𝕜) p
  let J := (lineL2Equiv (𝕜 := 𝕜)).toContinuousLinearEquiv.toContinuousLinearMap.comp (valueL p)
  have hJ : IsCompactOperator J := by
    apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image J).mpr
    let B : Set (Space 𝕜 p) := {u | ‖u‖ < 1}
    have hB : Bornology.IsBounded B :=
      isBounded_iff_forall_norm_le.mpr ⟨1, fun u hu => le_of_lt hu⟩
    have hBn : B ∈ 𝓝 (0 : Space 𝕜 p) :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp [B])
    refine ⟨B, hBn, ?_⟩
    have heq : J '' B = Rellich.wholeUnderlyingCLM '' (L '' B) := by
      rw [Set.image_image]
      congr 1
      funext u
      exact (wholeUnderlying_toSobolev p u).symm
    rw [heq]
    let U := Rellich.wholeUnderlyingCLM (𝕜 := 𝕜) (d := 1) (p := 2)
    have hSB : Bornology.IsBounded (L '' B) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨2, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      have hu' : ‖u‖ < 1 := hu
      exact (toSobolev_norm_le p u).trans (by linarith)
    have hUB : Bornology.IsBounded (U '' (L '' B)) :=
      U.lipschitzWith.isBounded_image hSB
    apply (kolmogorovRiesz (𝕜 := 𝕜) 1 2 (by norm_num)
      (U '' (L '' B)) hUB).mpr
    refine ⟨?_, Rellich.bounded_uniformTranslationContinuous _ hSB⟩
    rw [← heq]
    exact uniform_tails p hp B hB
  have h := hJ.continuous_comp (lineL2Equiv (𝕜 := 𝕜)).symm.continuous
  have heq : (lineL2Equiv (𝕜 := 𝕜)).symm ∘ J = value (𝕜 := 𝕜) (p := p) := by
    funext u
    exact (lineL2Equiv (𝕜 := 𝕜)).symm_apply_apply (value u)
  rwa [heq] at h

/-- The solution map is bounded into V, so composition with the compact
inclusion is compact in L². -/
theorem compact_solution_operator :
    Specs.ExpandedFA.Models.ConfiningCompactResolvent.CompactSolutionOperator := by
  intro 𝕜 _ p hp T hT
  obtain ⟨S, hS⟩ := exists_solution_map (𝕜 := 𝕜) p hp.positiveAtInfinity
  have heq : T = (valueL p).comp S := by
    apply ContinuousLinearMap.ext
    intro f
    obtain ⟨u, hu, he⟩ := hT f
    have huniq := (weighted_variational_solvability 𝕜 p hp.positiveAtInfinity f).unique he (hS f)
    change T f = value (S f)
    rw [← huniq]
    exact hu.symm
  rw [heq]
  exact (compact_inclusion 𝕜 p hp).comp_clm S


/-- Countably many disjoint unit intervals give an infinite orthonormal family
in the actual L² space, over both scalar fields. -/
lemma l2_not_finiteDimensional : ¬ FiniteDimensional 𝕜 (L2 𝕜) := by
  classical
  let s : ℕ → Set Line := fun n =>
    (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Ioc (n : ℝ) (n + 1)
  have hs (n : ℕ) : MeasurableSet (s n) :=
    measurableSet_Ioc.preimage (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable
  have hvol (n : ℕ) : (volume : Measure Line) (s n) = 1 := by
    calc
      _ = volume (Ioc (n : ℝ) (n + 1)) :=
        (volume_preserving_funUnique (Fin 1) ℝ).measure_preimage_equiv _
      _ = 1 := by simp
  have hline (n : ℕ) : lineMeasure (s n) = 1 := by
    simpa only [lineMeasure, Opens.coe_top, Measure.restrict_univ] using hvol n
  let v : ℕ → L2 𝕜 := fun n => indicatorConstLp 2 (hs n) (by rw [hline n]; simp) (1 : 𝕜)
  have hv : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪indicatorConstLp 2 (hs i) _ (1 : 𝕜),
      indicatorConstLp 2 (hs j) _ (1 : 𝕜)⟫_𝕜 = _
    rw [MeasureTheory.L2.inner_indicatorConstLp_one_indicatorConstLp_one
      (hs i) (hs j) (by change lineMeasure (s i) ≠ ∞; rw [hline i]; simp)
      (by change lineMeasure (s j) ≠ ∞; rw [hline j]; simp)]
    split_ifs with hij
    · subst j
      simp [Measure.real, hvol]
    · have he : s i ∩ s j = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hi, hj⟩
        change (i : ℝ) < _ ∧ _ ≤ (i : ℝ) + 1 at hi
        change (j : ℝ) < _ ∧ _ ≤ (j : ℝ) + 1 at hj
        rcases lt_or_gt_of_ne hij with hh | hh
        · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hh
          linarith
        · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hh
          linarith
      simp [he]
  intro h
  letI := h
  exact Module.Finite.not_linearIndependent_of_infinite v hv.linearIndependent

section Spectral
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {ι : Type}

lemma hilbertBasis_summable_sq (b : HilbertBasis ι 𝕜 H) (f : H) :
    Summable (fun i => ‖⟪b i, f⟫_𝕜‖ ^ 2) := by
  have h := (lp.memℓp (b.repr f)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply] using h

/-- Parseval identifies exactly the range of a diagonal bounded map.
No regularity is imposed on u beyond the weighted square-sum condition. -/
lemma diagonal_range (T : H →L[𝕜] H) (b : HilbertBasis ι 𝕜 H)
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (hT : ∀ i, T (b i) = (a i : 𝕜) • b i) (hs : T.IsSymmetric) (u : H) :
    u ∈ T.range ↔ Summable (fun i => (a i)⁻¹ ^ 2 * ‖⟪b i, u⟫_𝕜‖ ^ 2) := by
  have hcoeff (f : H) (i : ι) : ⟪b i, T f⟫_𝕜 = (a i : 𝕜) * ⟪b i, f⟫_𝕜 := by
    calc
      _ = ⟪T (b i), f⟫_𝕜 := (hs (b i) f).symm
      _ = _ := by rw [hT, inner_smul_left, RCLike.conj_ofReal]
  have hn (i : ι) : (a i : 𝕜) ≠ 0 := by exact_mod_cast ha i
  have hnrm (i : ι) (z : 𝕜) : ‖(a i : 𝕜)⁻¹ * z‖ ^ 2 =
      (a i)⁻¹ ^ 2 * ‖z‖ ^ 2 := by
    simp only [norm_mul, norm_inv, RCLike.norm_ofReal, mul_pow, inv_pow, sq_abs]
  constructor
  · rintro ⟨f, rfl⟩
    convert hilbertBasis_summable_sq b f using 1
    funext i
    rw [← hnrm]
    change ‖(a i : 𝕜)⁻¹ * ⟪b i, T f⟫_𝕜‖ ^ 2 = _
    rw [hcoeff f i, ← mul_assoc, inv_mul_cancel₀ (hn i), one_mul]
  · intro hu
    let c : ι → 𝕜 := fun i => (a i : 𝕜)⁻¹ * ⟪b i, u⟫_𝕜
    have hc : Memℓp c 2 := by
      apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, c, hnrm] using hu
    let f : H := b.repr.symm ⟨c, hc⟩
    refine ⟨f, ?_⟩
    apply b.repr.injective
    apply lp.ext
    funext i
    rw [b.repr_apply_apply, b.repr_apply_apply]
    change ⟪b i, T f⟫_𝕜 = ⟪b i, u⟫_𝕜
    rw [hcoeff]
    have hf : ⟪b i, f⟫_𝕜 = c i := by
      rw [← b.repr_apply_apply]
      exact congrArg (fun v : ℓ²(ι, 𝕜) => v i) (b.repr.apply_symm_apply ⟨c, hc⟩)
    rw [hf]
    dsimp [c]
    rw [← mul_assoc, mul_inv_cancel₀ (hn i), one_mul]

/-- Any enumeration of the eigenvectors has reciprocals tending to infinity:
finite multiplicities and finiteness away from zero suffice. -/
lemma reciprocals_tendsto (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hfinite : ∀ ε : ℝ, 0 < ε → {n | ε ≤ |a n|}.Finite) :
    Tendsto (fun n => (a n)⁻¹) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  let C := max M 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hfin := hfinite C⁻¹ (inv_pos.mpr hC)
  filter_upwards [atTop_le_cofinite hfin.eventually_cofinite_notMem] with n hn
  have he : a n < C⁻¹ := by
    simpa only [Set.mem_setOf_eq, abs_of_pos (ha n), not_le] using hn
  exact (le_max_left M 1).trans ((lt_inv_comm₀ hC (ha n)).mpr he).le

end Spectral

/-- The abstract positive compact inverse theorem, retaining the exact domain. -/
lemma positive_compact_inverse_spectrum
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (hInfinite : ¬ FiniteDimensional 𝕜 H) (T : H →L[𝕜] H)
    (hc : IsCompactOperator T) (hs : IsSelfAdjoint T)
    (hp : ∀ x, 0 ≤ RCLike.re ⟪x, T x⟫_𝕜) (hi : Function.Injective T)
    (A : H →ₗ.[𝕜] H) (hA : ∀ u f, (u, f) ∈ A.graph ↔ T f = u) :
    ∃ (b : HilbertBasis ℕ 𝕜 H) (ev : ℕ → ℝ),
      (∀ n, 0 < ev n) ∧ Tendsto ev atTop atTop ∧
      (∀ n, (b n, (ev n : 𝕜) • b n) ∈ A.graph) ∧
      (∀ u : H, u ∈ A.domain ↔
        Summable (fun n => ev n ^ 2 * ‖⟪b n, u⟫_𝕜‖ ^ 2)) := by
  classical
  obtain ⟨I, hI, e, a, he, hea, hspan, _, _, _, hfinite⟩ :=
    ExpandedFA.CompactSpectral.CompactNormalClassification.selfAdjoint_expansion
      𝕜 H T hs (hc.isCompact_closure_image_closedBall 1)
  letI : Countable I := hI
  have hker : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hi
  rw [hker, Submodule.bot_orthogonal_eq_top] at hspan
  let bI : HilbertBasis I 𝕜 H := HilbertBasis.mk he hspan.ge
  have hIinf : Infinite I := by
    apply not_finite_iff_infinite.mp
    intro hfin
    letI : Finite I := hfin
    letI : Fintype I := Fintype.ofFinite I
    exact hInfinite bI.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  letI : Infinite I := hIinf
  let q : ℕ ≃ I := Nonempty.some nonempty_equiv_of_countable
  have herange : Set.range (e ∘ q) = Set.range e := q.surjective.range_comp e
  have heN := he.comp q q.injective
  let b : HilbertBasis ℕ 𝕜 H := HilbertBasis.mk heN (by rw [herange]; exact hspan.ge)
  have hb (n : ℕ) : b n = e (q n) := by simp [b]
  have ha (i : I) : 0 < a i := by
    have h := hp (e i)
    rw [(hea i).2, inner_smul_right, inner_self_eq_norm_sq_to_K, he.1 i] at h
    have hnn : 0 ≤ a i := by simpa using h
    exact lt_of_le_of_ne hnn (Ne.symm (hea i).1)
  have hTe (n : ℕ) : T (b n) = (a (q n) : 𝕜) • b n := by rw [hb, (hea _).2]
  have hfiniteN (ε : ℝ) (hε : 0 < ε) : {n | ε ≤ |a (q n)|}.Finite :=
    Set.Finite.preimage (f := q) q.injective.injOn (hfinite ε hε)
  refine ⟨b, (fun n => (a (q n))⁻¹), (fun n => inv_pos.mpr (ha _)),
    reciprocals_tendsto _ (fun n => ha _) hfiniteN, ?_, ?_⟩
  · intro n
    apply (hA _ _).mpr
    rw [map_smul, hTe, smul_smul, RCLike.ofReal_inv, inv_mul_cancel₀]
    · exact one_smul 𝕜 _
    · exact_mod_cast (ha (q n)).ne'
  · intro u
    have hdom : u ∈ A.domain ↔ u ∈ T.range := by
      constructor
      · intro hu
        exact ⟨A ⟨u, hu⟩, (hA _ _).mp ((A.mem_graph_iff).mpr ⟨⟨u, hu⟩, rfl, rfl⟩)⟩
      · rintro ⟨f, hf⟩
        exact LinearPMap.mem_domain_of_mem_graph ((hA u f).mpr hf)
    exact hdom.trans (diagonal_range T b (fun n => a (q n))
      (fun n => (ha _).ne') hTe hs.isSymmetric u)

/-- Apply compact spectral theory to the original variational operator. -/
theorem discrete_spectrum :
    Specs.ExpandedFA.Models.ConfiningCompactResolvent.DiscreteSpectrum := by
  intro 𝕜 _ p hp T hT A hA
  obtain ⟨S, hS⟩ := exists_solution_map (𝕜 := 𝕜) p hp.positiveAtInfinity
  have heq : T = (valueL p).comp S := by
    apply ContinuousLinearMap.ext
    intro f
    obtain ⟨u, hu, he⟩ := hT f
    have huniq := (weighted_variational_solvability 𝕜 p hp.positiveAtInfinity f).unique he (hS f)
    change T f = value (S f)
    rw [← huniq]
    exact hu.symm
  obtain ⟨hs, hpos, hinj, _⟩ := solution_operator_properties p S hS
  rw [← heq] at hs hpos hinj
  exact positive_compact_inverse_spectrum l2_not_finiteDimensional T
    (compact_solution_operator 𝕜 p hp T hT) hs hpos hinj A hA

end ExpandedFA.Models.ConfiningCompactResolvent
