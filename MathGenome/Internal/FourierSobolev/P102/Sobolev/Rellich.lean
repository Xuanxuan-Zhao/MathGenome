import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.Rellich
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzExtension
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SupportedCompactness
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalEmbeddings
import MathGenome.Internal.FourierSobolev.P102.Sobolev.CriticalMorreyEmbeddings
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.RellichEmbeddings

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace P102.Sobolev.Rellich
open P102.U4

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma bounded_domain {m : ℕ} (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (Ω : Opens (Space (m+1)))
    (hΩ : Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m))) :
    Bornology.IsBounded (Ω : Set (Space (m+1))) := by
  have hb := e.lipschitzWith.isBounded_image hΩ.2.1
  have he : e '' (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) =
      (Ω : Set (Space (m+1))) := e.toEquiv.image_preimage _
  rwa [he] at hb

/-- Extend into a fixed bounded support set, apply whole-space compactness,
then restrict the resulting compact closure. -/
theorem same_exponent (m : ℕ) (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (Ω : Opens (Space (m+1)))
    (hΩ : Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    CompactLpInclusion 𝕜 Ω p p := by
  obtain ⟨D, K, C, B, _, hE⟩ := Extension.lipschitz_extension m e Ω hΩ
  obtain ⟨E, _, hres, hsupp, _, _⟩ := hE 𝕜 p
  let R := ExpandedFA.Sobolev.lpRestrict (E := 𝕜) p volume (Ω : Set (Space (m+1)))
  have hR : Continuous R := ExpandedFA.Sobolev.lpRestrict_lipschitz _ |>.continuous
  refine ⟨sobolevUnderlyingCLM Ω 1 p, sobolevUnderlying_injective Ω 1 p,
    fun _ => Filter.EventuallyEq.rfl, fun A hA => ?_⟩
  have hc := supported_compactness (by omega : 0 < m+1) p hp (E '' A)
    (E.lipschitzWith.isBounded_image hA) K K.isCompact.isBounded (by
      rintro v ⟨u, hu, rfl⟩
      filter_upwards [wholeLp_ae (sobolevUnderlying (E u)), hsupp u] with x hx hs
      intro h
      rw [hx]
      exact hs h)
  have heq : R '' ((fun v => wholeLp (sobolevUnderlying v)) '' (E '' A)) =
      (sobolevUnderlyingCLM (𝕜 := 𝕜) Ω 1 p) '' A := by
    rw [image_image, image_image]
    congr 1
    funext u
    apply Lp.ext
    have ha : (wholeLp (sobolevUnderlying (E u)) : Space (m+1) → 𝕜) =ᵐ[
        volume.restrict (Ω : Set (Space (m+1)))] sobolevUnderlying (E u) :=
      ae_restrict_of_ae (wholeLp_ae (sobolevUnderlying (E u)))
    exact (ExpandedFA.Sobolev.lpRestrict_representative _ _).trans (ha.trans (hres u))
  have hi : (sobolevUnderlyingCLM (𝕜 := 𝕜) Ω 1 p) '' A ⊆
      R '' closure ((fun v => wholeLp (sobolevUnderlying v)) '' (E '' A)) := by
    rw [← heq]
    exact image_mono subset_closure
  exact (hc.image hR).of_isClosed_subset isClosed_closure
    (closure_minimal hi (hc.image hR).isClosed)

/-- Once an inclusion exists, the operator norm supplies a uniform Lr bound. -/
lemma inclusion_bound {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (H : HasSobolevInclusion 𝕜 Ω p r) :
    ∃ C : ℝ≥0, ∀ u : Sobolev 𝕜 Ω 1 p,
      MemLp (sobolevUnderlying u) r (volume.restrict (Ω : Set (Space d))) ∧
      eLpNorm (sobolevUnderlying u) r (volume.restrict (Ω : Set (Space d))) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  obtain ⟨I, _, hI⟩ := H
  refine ⟨‖I‖₊, fun u => ⟨(Lp.memLp (I u)).ae_eq (hI u), ?_⟩⟩
  rw [← eLpNorm_congr_ae (hI u), ← Lp.enorm_def, ← ofReal_norm]
  calc
    _ ≤ ENNReal.ofReal (‖I‖ * ‖u‖) := ENNReal.ofReal_le_ofReal (I.le_opNorm u)
    _ = _ := by
      rw [ENNReal.ofReal_mul (norm_nonneg I), ← coe_nnnorm I, ENNReal.ofReal_coe_nnreal]

lemma lower_inclusion [IsFiniteMeasure (volume.restrict (Ω : Set (Space d)))]
    {q r : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))] [Fact (1 ≤ (r : ℝ≥0∞))]
    (hqr : q ≤ r) (hq : 0 < q) (H : HasSobolevInclusion 𝕜 Ω p r) :
    HasSobolevInclusion 𝕜 Ω p q := by
  let μ := volume.restrict (Ω : Set (Space d))
  let F := μ univ ^ (1/(q : ℝ) - 1/(r : ℝ))
  have hF : F ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg
    (sub_nonneg.mpr (one_div_le_one_div_of_le (by exact_mod_cast hq) (by exact_mod_cast hqr)))
    (measure_ne_top μ univ)
  obtain ⟨C, hC⟩ := inclusion_bound H
  apply IntegerEmbeddings.inclusion_of_bound (C * F.toNNReal)
  intro u
  have hle : (q : ℝ≥0∞) ≤ r := by exact_mod_cast hqr
  refine ⟨(hC u).1.mono_exponent hle, ?_⟩
  calc
    _ ≤ eLpNorm (sobolevUnderlying u) r μ * F := by
      simpa only [ENNReal.coe_toReal] using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hle (hC u).1.aestronglyMeasurable
    _ ≤ ((C : ℝ≥0∞) * ENNReal.ofReal ‖u‖) * F := by gcongr; exact (hC u).2
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hF]; ac_rfl

/-- Convergence in measure from base compactness, followed by the higher
integrability convergence criterion. No domain smoothness is used here. -/
theorem compact_upgrade [IsFiniteMeasure (volume.restrict (Ω : Set (Space d)))]
    (Hbase : CompactLpInclusion 𝕜 Ω p p)
    {q r : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))] [Fact (1 ≤ (r : ℝ≥0∞))]
    (hq : 0 < q) (hqr : q < r) (H : HasSobolevInclusion 𝕜 Ω p r) :
    CompactLpInclusion 𝕜 Ω p q := by
  obtain ⟨J, hJinj, hJ⟩ := lower_inclusion hqr.le hq H
  obtain ⟨C, hC⟩ := inclusion_bound H
  obtain ⟨P, _, hP, hcompact⟩ := Hbase
  refine ⟨J, hJinj, hJ, fun A hA =>
    ExpandedFA.Sobolev.Rellich.compact_closure_of_subsequences ?_⟩
  intro f hf
  choose u hu heq using hf
  have heq' (n : ℕ) : f n = J (u n) := (heq n).symm
  obtain ⟨M, hM, hMb⟩ := hA.exists_pos_norm_le
  obtain ⟨g, _, σ, hσ, ht⟩ := (hcompact A hA).tendsto_subseq
    (fun n => subset_closure (mem_image_of_mem P (hu n)))
  have hmeasure : TendstoInMeasure (volume.restrict (Ω : Set (Space d)))
      (fun n => f (σ n)) atTop g := by
    apply (tendstoInMeasure_of_tendsto_Lp ht).congr_left
    intro n
    exact (hP (u (σ n))).trans ((hJ (u (σ n))).symm) |>.trans
      (by rw [heq' (σ n)])
  have hbound (n : ℕ) : eLpNorm (f (σ n)) r
      (volume.restrict (Ω : Set (Space d))) ≤ (C : ℝ≥0∞) * ENNReal.ofReal M := by
    rw [heq' (σ n), eLpNorm_congr_ae (hJ _)]
    apply (hC _).2.trans
    gcongr
    exact hMb _ (hu _)
  obtain ⟨z, hz⟩ := ExpandedFA.Sobolev.Rellich.lp_convergent_of_higher_bound hq hqr
    (fun n => f (σ n)) g (by finiteness) hbound hmeasure
  exact ⟨z, σ, hσ, hz⟩

/-- A uniform supremum estimate on representatives yields every finite Lr
inclusion, including the one-dimensional W¹¹ endpoint. -/
lemma inclusion_of_sup_bound [IsFiniteMeasure (volume.restrict (Ω : Set (Space d)))]
    (C : ℝ) (hC : 0 ≤ C)
    (H : ∀ u : Sobolev 𝕜 Ω 1 p, ∃ f : Space d → 𝕜,
      IntegerEmbeddings.RepresentsOn u f ∧
      ∀ x ∈ closure (Ω : Set (Space d)), ‖f x‖ ≤ C * ‖u‖)
    (r : ℝ≥0) [Fact (1 ≤ (r : ℝ≥0∞))] : HasSobolevInclusion 𝕜 Ω p r := by
  let μ := volume.restrict (Ω : Set (Space d))
  let F := μ univ ^ (r : ℝ)⁻¹
  have hF : F ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ univ)
  apply IntegerEmbeddings.inclusion_of_bound (F.toNNReal * C.toNNReal)
  intro u
  obtain ⟨f, hf, hb⟩ := H u
  have ha : ∀ᵐ x ∂μ, ‖sobolevUnderlying u x‖ ≤ C * ‖u‖ := by
    filter_upwards [self_mem_ae_restrict Ω.isOpen.measurableSet, hf] with x hx he
    rw [he]
    exact hb x (subset_closure hx)
  refine ⟨MemLp.of_bound (Lp.aestronglyMeasurable _) _ ha, ?_⟩
  calc
    _ ≤ F * ENNReal.ofReal (C * ‖u‖) := by
      simpa only [F, ENNReal.coe_toReal] using eLpNorm_le_of_ae_bound (p := (r : ℝ≥0∞)) (μ := μ) (Lp.aestronglyMeasurable _) ha
    _ = _ := by
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hF, ← ENNReal.ofReal_coe_nnreal,
        Real.coe_toNNReal _ hC, ENNReal.ofReal_mul hC, mul_assoc]

/-- Finite q compactness in all three ranges. -/
theorem lebesgue : Expected.Lebesgue := by
  intro m e Ω hΩ p q hp hq hrange
  letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  letI : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  intro 𝕜 _
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Space (m+1)))) :=
    isFiniteMeasure_restrict.mpr (bounded_domain e Ω hΩ).measure_lt_top.ne
  have hbase := same_exponent m e Ω hΩ 𝕜 p ENNReal.coe_ne_top
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  by_cases hpd : p < (m+1 : ℕ)
  · let r := criticalExponent (m+1) p
    have hd : 2 ≤ m+1 := by
      have h : 1 < m+1 := by exact_mod_cast hp.trans_lt hpd
      omega
    letI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast one_le_criticalExponent hp hpd⟩
    obtain ⟨C, hC⟩ := subcritical_lipschitz m hd e Ω hΩ p hp hpd
    exact compact_upgrade hbase hq0 (hrange hpd) (hC 𝕜).2
  · let r : ℝ≥0 := q + 1
    have hr : 1 ≤ r := by simp [r]
    have hqr : q < r := by dsimp [r]; simp
    letI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
    apply compact_upgrade hbase hq0 hqr
    by_cases hdp : (m+1 : ℕ) < p
    · obtain ⟨C, hC, hrep⟩ := IntegerEmbeddings.finite m e Ω hΩ 𝕜 p
        (by exact_mod_cast hdp) ENNReal.coe_ne_top
      apply inclusion_of_sup_bound C hC _ r
      intro u
      obtain ⟨f, _, hf, hnorm, _⟩ := hrep u
      obtain ⟨A, B, hA, hB, hAB, hsup, _⟩ := hnorm
      exact ⟨f, hf, fun x hx => (hsup x hx).trans (by linarith)⟩
    · have heq : p = (m+1 : ℕ) := le_antisymm (le_of_not_gt hdp) (le_of_not_gt hpd)
      by_cases hd : 2 ≤ m+1
      · subst p
        obtain ⟨C, hC⟩ := IntegerEmbeddings.critical m hd e Ω hΩ r hr
        exact (hC 𝕜).2
      · have hm : m = 0 := by omega
        subst m
        norm_num at heq
        subst p
        obtain ⟨C, hC, hrep⟩ := IntegerEmbeddings.dimensionOne e Ω hΩ 𝕜
        apply inclusion_of_sup_bound C hC _ r
        intro u
        obtain ⟨f, _, hf, hsup, _⟩ := hrep u
        exact ⟨f, hf, hsup⟩

lemma holderWith_of_norm {X : Type*} [PseudoMetricSpace X]
    (f : X → 𝕜) (B α : ℝ≥0)
    (h : ∀ x y, ‖f x - f y‖ ≤ B * dist x y ^ (α : ℝ)) : HolderWith B α f := by
  intro x y
  calc
    edist (f x) (f y) = ENNReal.ofReal ‖f x - f y‖ := by rw [edist_dist, dist_eq_norm]
    _ ≤ ENNReal.ofReal (B * dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal (h x y)
    _ = _ := by
      rw [ENNReal.ofReal_mul B.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg, edist_dist]

def interpolationConstant (a B α β : ℝ) : ℝ :=
  (2 * a) ^ (1 - β / α) * B ^ (β / α)

/-- Interpolate the zero-exponent bound supplied by the supremum norm with
an alpha-Hölder bound, using the library's Hölder interpolation theorem. -/
lemma interpolation_bound {X : Type*} [PseudoMetricSpace X]
    (f : X →ᵇ 𝕜) {α β B : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβα : β < α)
    (hB : 0 ≤ B) (hb : ∀ x y, ‖f x - f y‖ ≤ B * dist x y ^ α) :
    ∀ x y, ‖f x - f y‖ ≤ interpolationConstant ‖f‖ B α β * dist x y ^ β := by
  let t₁ : ℝ≥0 := NNReal.mk (1 - β / α) (sub_nonneg.mpr ((div_lt_one hα).mpr hβα).le)
  let t₂ : ℝ≥0 := NNReal.mk (β / α) (div_nonneg hβ hα.le)
  have ht : t₁ + t₂ = 1 := by
    apply NNReal.eq
    change (1 - β/α) + β/α = 1
    ring
  let a : ℝ≥0 := NNReal.mk α hα.le
  let b : ℝ≥0 := NNReal.mk β hβ
  have he : (0 : ℝ≥0) * t₁ + a * t₂ = b := by
    apply NNReal.eq
    change 0 * (1 - β/α) + α * (β/α) = β
    simp [mul_div_cancel₀ _ hα.ne']
  have hz : HolderWith (2 * ‖f‖₊) 0 f := by
    apply holderWith_of_norm
    intro x y
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm, NNReal.coe_zero,
      Real.rpow_zero, mul_one]
    exact (norm_sub_le (f x) (f y)).trans (by linarith [f.norm_coe_le_norm x, f.norm_coe_le_norm y])
  have ha : HolderWith (NNReal.mk B hB) a f := holderWith_of_norm f _ _ hb
  have hi := hz.interpolate ha ht
  rw [he] at hi
  intro x y
  simpa [interpolationConstant, NNReal.coe_mul, NNReal.coe_rpow,
    t₁, t₂, b, NNReal.coe_mk, dist_eq_norm] using hi.dist_le x y

/-- Arzelà–Ascoli for a uniformly bounded alpha-Hölder sequence, followed by
interpolation in every strict lower exponent. The compact set may be empty. -/
theorem compact_holder_sequence {X : Type*} [MetricSpace X] [CompactSpace X]
    (v : ℕ → X →ᵇ 𝕜) {α β M : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβα : β < α)
    (hM : 0 ≤ M) (hsup : ∀ n x, ‖v n x‖ ≤ M)
    (hhold : ∀ n x y, ‖v n x - v n y‖ ≤ M * dist x y ^ α) :
    ∃ (σ : ℕ → ℕ) (f : X →ᵇ 𝕜), StrictMono σ ∧
      Tendsto (v ∘ σ) atTop (𝓝 f) ∧
      (∀ x, ‖f x‖ ≤ M) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x y, ‖f x - f y‖ ≤ B * dist x y ^ β) ∧
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x y,
        ‖(v (σ n) x - f x) - (v (σ n) y - f y)‖ ≤ ε * dist x y ^ β := by
  have heq : Equicontinuous ((↑) : range v → X → 𝕜) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => M * r ^ α)
    · simpa using
        tendsto_const_nhds.mul ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).rpow_const_nhds_zero hα)
    · rintro x y ⟨g, n, rfl⟩
      simpa only [dist_eq_norm] using hhold n x y
  have hc : IsCompact (closure (range v)) := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : 𝕜) M) (isCompact_closedBall _ _) (range v)
    (by rintro g x ⟨n, rfl⟩; simpa only [Metric.mem_closedBall, dist_zero_right] using hsup n x) heq
  obtain ⟨f, _, σ, hσ, ht⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have hpoint (x : X) : Tendsto (fun n => v (σ n) x) atTop (𝓝 (f x)) :=
    (continuous_eval_const x).tendsto f |>.comp ht
  have hfsup (x : X) : ‖f x‖ ≤ M := le_of_tendsto (hpoint x).norm (Eventually.of_forall fun n => hsup _ x)
  have hfhold (x y : X) : ‖f x - f y‖ ≤ M * dist x y ^ α :=
    le_of_tendsto ((hpoint x).sub (hpoint y)).norm (Eventually.of_forall fun n => hhold _ x y)
  refine ⟨σ, f, hσ, ht, hfsup, ?_, ?_⟩
  · refine ⟨interpolationConstant ‖f‖ M α β, by unfold interpolationConstant; positivity,
      interpolation_bound f hα hβ hβα hM hfhold⟩
  · have hnorm : Tendsto (fun n => ‖v (σ n) - f‖) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self, norm_zero] using (ht.sub_const f).norm
    have hlim : Tendsto (fun n => interpolationConstant ‖v (σ n) - f‖ (2*M) α β)
        atTop (𝓝 0) := by
      unfold interpolationConstant
      have ha0 : Tendsto (fun n => 2 * ‖v (σ n) - f‖) atTop (𝓝 0) := by
        simpa using hnorm.const_mul 2
      have ha := ha0.rpow_const_nhds_zero
        (show 0 < 1 - β/α from sub_pos.mpr ((div_lt_one hα).mpr hβα))
      simpa only [zero_mul] using ha.mul_const ((2*M) ^ (β/α))
    intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
    intro x y
    have hb (x y : X) : ‖(v (σ n) - f) x - (v (σ n) - f) y‖ ≤ (2*M) * dist x y ^ α := by
      have he : (v (σ n) - f) x - (v (σ n) - f) y =
          (v (σ n) x - v (σ n) y) - (f x - f y) := by simp only [BoundedContinuousFunction.sub_apply]; abel
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith [hhold (σ n) x y, hfhold x y])
    exact (interpolation_bound (v (σ n) - f) hα hβ hβα (by positivity) hb x y).trans
      (mul_le_mul_of_nonneg_right hn.le (Real.rpow_nonneg dist_nonneg _))

/-- The unique representatives supplied by Morrey's theorem have a common
Hölder bound on every Sobolev-bounded sequence. -/
theorem holder : Expected.Holder := by
  classical
  intro m e Ω hΩ p hp hdp β hβ hβα
  letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  intro 𝕜 _ u hu v hv
  let S := closure (Ω : Set (Space (m+1)))
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (bounded_domain e Ω hΩ).isCompact_closure
  let α : ℝ := 1 - ((m+1 : ℕ) : ℝ) / p
  have hα : 0 < α := lt_of_le_of_lt hβ hβα
  obtain ⟨C, hC, hrep⟩ := IntegerEmbeddings.finite m e Ω hΩ 𝕜 p
    (by exact_mod_cast hdp) ENNReal.coe_ne_top
  obtain ⟨R, hR, hRu⟩ := hu.exists_pos_norm_le
  let M : ℝ := C * R
  have hM : 0 ≤ M := mul_nonneg hC hR.le
  have hb (n : ℕ) : (∀ x ∈ S, ‖v n x‖ ≤ M) ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖v n x - v n y‖ ≤ M * ‖x-y‖ ^ α := by
    obtain ⟨f, hf, huf, hnorm, huniq⟩ := hrep (u n)
    have heq := huniq (v n) (hv n).1 (hv n).2
    obtain ⟨A, B, hA, hB, hAB, hsup, hhold⟩ := hnorm
    have hCR : C * ‖u n‖ ≤ M := mul_le_mul_of_nonneg_left (hRu _ (mem_range_self n)) hC
    have hAM : A ≤ M := (by linarith : A ≤ C * ‖u n‖).trans hCR
    have hBM : B ≤ M := (by linarith : B ≤ C * ‖u n‖).trans hCR
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · rw [heq hx]
      exact (hsup x hx).trans hAM
    · rw [heq hx, heq hy]
      have hh := hhold x hx y hy
      simp only [ENNReal.coe_toReal] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hBM (Real.rpow_nonneg (norm_nonneg _) _))
  let V : ℕ → S →ᵇ 𝕜 := fun n =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => v n x, continuousOn_iff_continuous_domRestrict.mp (hv n).1⟩
  have hV (n : ℕ) (x : S) : V n x = v n x := rfl
  obtain ⟨σ, g, hσ, ht, hgsup, hgBound, hconv⟩ :=
    compact_holder_sequence V hα hβ hβα hM
      (fun n x => (hb n).1 x x.property)
      (fun n x y => by
        simpa only [hV, Subtype.dist_eq, dist_eq_norm] using (hb n).2 x x.property y y.property)
  obtain ⟨B, hB, hgβ⟩ := hgBound
  let f : Space (m+1) → 𝕜 := fun x => if hx : x ∈ S then g ⟨x, hx⟩ else 0
  have hf (x : S) : f x = g x := by simp only [f, dite_eq_left x.property]
  refine ⟨σ, f, hσ, ?_, ?_, ?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact g.continuous.congr (fun x => (hf x).symm)
  · refine ⟨M + B, M, B, hM, hB, le_rfl, fun x hx => ?_, fun x hx y hy => ?_⟩
    · exact (hf ⟨x,hx⟩).symm ▸ hgsup ⟨x,hx⟩
    · simpa only [hf ⟨x,hx⟩, hf ⟨y,hy⟩, Subtype.dist_eq, dist_eq_norm] using hgβ ⟨x,hx⟩ ⟨y,hy⟩
  · refine ⟨?_, Or.inr ?_⟩
    · apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      have hevent := (Metric.tendsto_nhds.mp ht) ε hε
      filter_upwards [hevent] with n hn
      intro x hx
      rw [hf ⟨x,hx⟩]
      change dist (g ⟨x,hx⟩) (V (σ n) ⟨x,hx⟩) < ε
      exact (BoundedContinuousFunction.dist_coe_le_dist (f := g) (g := V (σ n))
        (⟨x,hx⟩ : S)).trans_lt (by simpa only [dist_comm, Function.comp_apply] using hn)
    · intro ε hε
      filter_upwards [hconv ε hε] with n hn
      intro x hx y hy
      simpa only [hf ⟨x,hx⟩, hf ⟨y,hy⟩, hV, Function.comp_apply, Subtype.dist_eq, dist_eq_norm] using hn ⟨x,hx⟩ ⟨y,hy⟩

end P102.Sobolev.Rellich
