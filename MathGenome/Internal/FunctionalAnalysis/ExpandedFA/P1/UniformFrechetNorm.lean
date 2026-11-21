import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UniformFrechetNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SmoothnessDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.GateauxNormDerivative
import Mathlib.Topology.Order.LeftRightNhds

namespace ExpandedFA.P1.UniformFrechetNorm

open Filter Set Metric
open scoped Topology
universe u v
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

local notation "ρ" => SmoothnessDefinitions.Spec.ModulusValue 𝕜 E

/-- A useful epsilon form of the right-sided modulus limit. -/
lemma small_modulus (hs : SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ρ t < ε * t := by
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, ρ t / t < ε :=
    (tendsto_order.1 hs).2 ε hε
  obtain ⟨δ, hδ, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  exact ⟨δ, hδ, fun t ht htδ => (div_lt_iff₀ ht).1 (hd ⟨ht, htδ⟩)⟩

/-- Every unit-ball pair is bounded by the original modulus. -/
lemma pair_le_modulus (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (t : ℝ) :
    (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1 ≤ ρ t := by
  have hb : BddAbove {r : ℝ | ∃ a b : E, ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧
      r = (‖a + (t : 𝕜) • b‖ + ‖a - (t : 𝕜) • b‖) / 2 - 1} := by
    refine ⟨|t|, ?_⟩
    rintro r ⟨a, b, ha, hb, rfl⟩
    have hp := norm_add_le a ((t : 𝕜) • b)
    have hm := norm_sub_le a ((t : 𝕜) • b)
    simp only [norm_smul, RCLike.norm_ofReal] at hp hm
    have htb : |t| * ‖b‖ ≤ |t| := by nlinarith [abs_nonneg t]
    linarith
  exact (le_csSup hb ⟨x, y, hx, hy, rfl⟩).trans (le_max_right _ _)

/-- The convex support remainder is between zero and twice the modulus. -/
lemma support_remainder (x h : E) (hx : ‖x‖ = 1)
    (f : E →L[𝕜] 𝕜) (hf : ‖f‖ = 1) (hfx : f x = 1) :
    0 ≤ ‖x + h‖ - 1 - RCLike.re (f h) ∧
      ‖x + h‖ - 1 - RCLike.re (f h) ≤ 2 * ρ ‖h‖ := by
  have hlo := GateauxNormDerivative.re_apply_le_norm f hf.le (x + h)
  have hneg := GateauxNormDerivative.re_apply_le_norm f hf.le (x - h)
  simp only [map_add, map_sub, hfx, RCLike.one_re] at hlo hneg
  refine ⟨by linarith, ?_⟩
  by_cases hh : h = 0
  · simp only [hh, add_zero, map_zero, hx, sub_self]
    exact mul_nonneg (by norm_num) (le_max_left _ _)
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    have hy : ‖(‖h‖⁻¹ : 𝕜) • h‖ ≤ 1 := by
      simp [norm_smul, hn]
    have he : (‖h‖ : 𝕜) • ((‖h‖⁻¹ : 𝕜) • h) = h := by
      have hk : (‖h‖ : 𝕜) ≠ 0 := by exact_mod_cast hn
      simp [smul_smul, hk]
    have hp := pair_le_modulus (𝕜 := 𝕜) x _ hx.le hy ‖h‖
    rw [he] at hp
    linarith

/-- Support remainders have a common radius over all unit vectors and supports. -/
lemma uniform_support_remainder
    (hs : SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧
      ∀ (x h : E) (f : E →L[𝕜] 𝕜), ‖x‖ = 1 → ‖f‖ = 1 → f x = 1 →
        ‖h‖ < δ → |‖x + h‖ - 1 - RCLike.re (f h)| ≤ ε * ‖h‖ := by
  obtain ⟨δ, hδ, hd⟩ := small_modulus hs (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro x h f hx hf hfx hh
  obtain ⟨hlo, hhi⟩ := support_remainder x h hx f hf hfx
  rw [abs_of_nonneg hlo]
  by_cases hz : h = 0
  · simp [hz, hx]
  · have hm := hd ‖h‖ (norm_pos_iff.mpr hz) hh
    linarith

/-- Choosing Hahn–Banach supports supplies the real derivatives uniformly. -/
lemma smooth_implies_uniform_frechet
    (hs : SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E) :
    Spec.UniformlyFrechetDifferentiableNorm 𝕜 E := by
  classical
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hex (x : Spec.UnitSphere E) : ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = 1 := by
    have hx0 : (x : E) ≠ 0 := by intro he; simpa [he] using x.property
    obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional_nonzero 𝕜 E x hx0
    exact ⟨f, hf, by simpa [x.property] using hfx⟩
  choose f hf using hex
  refine ⟨fun x => RCLike.reCLM.comp ((f x).restrictScalars ℝ), ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := uniform_support_remainder hs hε
  exact ⟨δ, hδ, fun x h hh => hd x h (f x) x.property (hf x).1 (hf x).2 hh⟩


/-- The linear terms cancel in the symmetric increment, recovering the modulus. -/
lemma uniform_frechet_implies_smooth
    (hd : Spec.UniformlyFrechetDifferentiableNorm 𝕜 E) :
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E := by
  cases subsingleton_or_nontrivial E with
  | inl hz =>
    letI := hz
    exact SmoothnessDefinitions.uniformlySmooth_zero_space 𝕜 E
  | inr hn =>
    letI := hn
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    obtain ⟨D, hD⟩ := hd
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ha.trans_le (div_nonneg (le_max_left _ _) (le_of_lt ht))
    · intro ε hε
      obtain ⟨δ, hδ, hd⟩ := hD (ε / 2) (half_pos hε)
      apply mem_nhdsGT_iff_exists_Ioo_subset.2
      refine ⟨δ, hδ, ?_⟩
      intro t ht
      have hp : ρ t ≤ (ε / 2) * t := by
        rw [SmoothnessDefinitions.modulus_sphere_formula 𝕜 E t]
        obtain ⟨z, hz⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
        apply csSup_le
        · exact ⟨_, z, z, hz, hz, rfl⟩
        · rintro r ⟨x, y, hx, hy, rfl⟩
          have hty : ‖(t : 𝕜) • y‖ = t := by
            simp [norm_smul, hy, abs_of_pos ht.1]
          have h1 := (abs_le.1 (hd ⟨x, hx⟩ ((t : 𝕜) • y) (by simpa only [hty] using ht.2))).2
          have h2 := (abs_le.1 (hd ⟨x, hx⟩ (-((t : 𝕜) • y))
            (by simpa only [norm_neg, hty] using ht.2))).2
          simp only [map_neg, norm_neg, hty, ← sub_eq_add_neg] at h1 h2
          linarith
      exact ((div_le_iff₀ ht.1).2 hp).trans_lt (by linarith)

theorem uniformlySmooth_iff_uniformlyFrechet : Spec.Characterization.{u,v} := by
  intro 𝕜 E _ _ _
  exact ⟨smooth_implies_uniform_frechet, uniform_frechet_implies_smooth⟩

/-- Compare any two supports using symmetric increments at a fixed positive scale. -/
lemma support_real_difference (x y h : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hh : ‖h‖ ≤ 1) (f g : E →L[𝕜] 𝕜)
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (hfx : f x = 1) (hgy : g y = 1)
    {t : ℝ} (ht : 0 < t) :
    |RCLike.re ((f - g) h)| ≤ (2 * ρ t + ‖x - y‖) / t := by
  have upper (a : E) (ha : ‖a‖ = 1) (k : E →L[𝕜] 𝕜)
      (hk : ‖k‖ = 1) (hka : k a = 1) :
      ‖a + (t : 𝕜) • h‖ ≤ 1 + t * RCLike.re (k h) + 2 * ρ t := by
    have hp := pair_le_modulus (𝕜 := 𝕜) a h ha.le hh t
    have hm := GateauxNormDerivative.support_lower a (-h) k hk.le
      (by simpa [ha] using hka) t
    simp only [map_neg, smul_neg, ← sub_eq_add_neg, ha] at hm
    linarith
  have compare (a b : E) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
      (k l : E →L[𝕜] 𝕜) (hk : ‖k‖ = 1) (hl : ‖l‖ = 1)
      (hka : k a = 1) (hlb : l b = 1) :
      t * (RCLike.re (l h) - RCLike.re (k h)) ≤ 2 * ρ t + ‖a - b‖ := by
    have hlo := GateauxNormDerivative.support_lower b h l hl.le
      (by simpa [hb] using hlb) t
    have hup := upper a ha k hk hka
    have hnorm : ‖b + (t : 𝕜) • h‖ ≤ ‖a + (t : 𝕜) • h‖ + ‖a - b‖ := by
      have he := norm_sub_le_norm_sub_add_norm_sub b a (-((t : 𝕜) • h))
      simpa [sub_neg_eq_add, norm_sub_rev, add_comm] using he
    linarith
  have h1 := compare x y hx hy f g hf hg hfx hgy
  have h2 := compare y x hy hx g f hg hf hgy hfx
  rw [norm_sub_rev y x] at h2
  simp only [sub_apply, map_sub]
  apply abs_le.2
  constructor
  · have hdiv : RCLike.re (g h) - RCLike.re (f h) ≤ (2 * ρ t + ‖x - y‖) / t :=
      (le_div_iff₀ ht).2 (by nlinarith [h1])
    linarith
  · apply (le_div_iff₀ ht).2
    nlinarith [h2]

/-- A scalar-linear functional is controlled by real parts on the unit ball.
The estimate also works over ℝ, where the imaginary part vanishes. -/
lemma norm_le_twice_real_bound (f : E →L[𝕜] 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h : E, ‖h‖ ≤ 1 → |RCLike.re (f h)| ≤ C) : ‖f‖ ≤ 2 * C := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro h hh
  have hr := hb h hh.le
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by rw [RCLike.norm_I]; split_ifs <;> norm_num
  have hi := hb ((RCLike.I : 𝕜) • h) (by simpa [norm_smul, hh] using hI)
  simp only [map_smul, smul_eq_mul, RCLike.I_mul_re, abs_neg] at hi
  have hz : ‖f h‖ ≤ |RCLike.re (f h)| + |RCLike.im (f h)| := by
    calc
      ‖f h‖ = ‖(RCLike.re (f h) : 𝕜) + (RCLike.im (f h) : 𝕜) * RCLike.I‖ := by
        rw [RCLike.re_add_im]
      _ ≤ ‖(RCLike.re (f h) : 𝕜)‖ + ‖(RCLike.im (f h) : 𝕜) * RCLike.I‖ := norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_mul, RCLike.norm_ofReal]
        nlinarith [abs_nonneg (RCLike.im (f h))]
  linarith

/-- A norm estimate for any two supports, before choosing the norming map. -/
lemma support_norm_difference (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (f g : E →L[𝕜] 𝕜) (hf : ‖f‖ = 1) (hg : ‖g‖ = 1)
    (hfx : f x = 1) (hgy : g y = 1) {t : ℝ} (ht : 0 < t) :
    ‖f - g‖ ≤ 2 * ((2 * ρ t + ‖x - y‖) / t) := by
  apply norm_le_twice_real_bound (f - g)
  · exact div_nonneg (by nlinarith [show 0 ≤ ρ t from le_max_left _ _, norm_nonneg (x - y)]) ht.le
  · intro h hh
    exact support_real_difference x y h hx hy hh f g hf hg hfx hgy ht


/-- In a uniformly smooth space any two norming functionals at a unit point agree. -/
lemma support_unique (hs : SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E)
    (x : E) (hx : ‖x‖ = 1) (f g : E →L[𝕜] 𝕜)
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (hfx : f x = 1) (hgx : g x = 1) : f = g := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := small_modulus hs (show 0 < ε / 8 by linarith)
  have ht : 0 < δ / 2 := half_pos hδ
  have hm := hd (δ / 2) ht (by linarith)
  have hb := support_norm_difference x x hx hx f g hf hg hfx hgx ht
  simp only [sub_self, norm_zero, add_zero] at hb
  have hq : (2 * ρ (δ / 2)) / (δ / 2) < ε / 4 :=
    (div_lt_iff₀ ht).2 (by nlinarith [hm])
  linarith

theorem unique_norming_functional : Spec.UniqueNormingFunctional.{u,v} := by
  intro 𝕜 E _ _ _ hs x hx
  have hx0 : x ≠ 0 := by intro he; simpa [he] using hx
  obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional_nonzero 𝕜 E x hx0
  have hfx1 : f x = 1 := by simpa [hx] using hfx
  exact ⟨f, ⟨hf, hfx1⟩, fun g hg => support_unique hs x hx g f hg.1 hf hg.2 hfx1⟩

/-- The support comparison is uniform in both points of the sphere. -/
theorem uniformly_continuous_norming_map : Spec.UniformlyContinuousNormingMap.{u,v} := by
  classical
  intro 𝕜 E _ _ _ hs
  have hex (x : Spec.UnitSphere E) : ∃! f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = 1 :=
    unique_norming_functional 𝕜 E hs x x.property
  choose f hf hu using hex
  refine ⟨f, fun x => ⟨(hf x).1, (hf x).2, fun g hg hgx => hu x g ⟨hg, hgx⟩⟩, ?_⟩
  apply Metric.uniformContinuous_iff.2
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := small_modulus hs (show 0 < ε / 16 by linarith)
  let t := δ / 2
  have ht : 0 < t := half_pos hδ
  have hm := hd t ht (by dsimp [t]; linarith)
  refine ⟨ε * t / 8, by positivity, ?_⟩
  intro x y hxy
  rw [Subtype.dist_eq, dist_eq_norm] at hxy
  rw [dist_eq_norm]
  have hb := support_norm_difference (x : E) y x.property y.property (f x) (f y)
    (hf x).1 (hf y).1 (hf x).2 (hf y).2 ht
  have hq : (2 * SmoothnessDefinitions.Spec.ModulusValue 𝕜 E t + ‖(x : E) - (y : E)‖) / t < ε / 2 :=
    (div_lt_iff₀ ht).2 (by nlinarith [hm, hxy])
  linarith

/-- The uniform remainder gives the native real Fréchet derivative Re f. -/
theorem norm_derivative_formula : Spec.NormDerivativeFormula.{u,v} := by
  intro 𝕜 E _ _ _ hs x f hx hf hfx
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := uniform_support_remainder hs hε
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hh' : ‖h‖ < δ := by simpa using hh
  simpa [hx] using hd x h f hx hf hfx hh'

end ExpandedFA.P1.UniformFrechetNorm
