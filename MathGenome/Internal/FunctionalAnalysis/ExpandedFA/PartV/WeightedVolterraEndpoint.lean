import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeightedVolterraEndpoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.WeightedVolterraDerivatives
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace ExpandedFA.PartV.WeightedVolterraEndpoint
open ExpandedFA.PartV.WeightedVolterraDerivatives

lemma solution_zero {𝕜 : Type} [RCLike 𝕜] {α T : ℝ} (hT : 0 ≤ T)
    {k : ℝ × ℝ → 𝕜} {f u : ℝ → 𝕜} {ζ : 𝕜}
    (hu : WeightedVolterraDerivatives.Spec.IsSolution α T k f ζ u) : u 0 = f 0 := by
  simpa using hu.2 0 ⟨le_rfl, hT⟩

theorem zero_time : Spec.ZeroTime := by
  intro 𝕜 _ α k f ζ u hu
  have h0 := solution_zero (le_refl 0) hu
  refine ⟨h0, (fun _ => f 0), contDiff_const, ?_⟩
  intro t ht
  have : t = 0 := le_antisymm ht.2 ht.1
  subst t
  exact h0.symm

/-- C¹ control on the rescaled integrals gives a Lipschitz estimate reaching
zero, unlike the singular powers multiplying those integrals. -/
lemma norm_sub_zero_le {𝕜 : Type} [RCLike 𝕜] {T B : ℝ} (hT : 0 < T)
    {H : ℝ → 𝕜} (hH : ContDiffOn ℝ 1 H (Icc 0 T))
    (hB : ∀ t ∈ Icc (0 : ℝ) T, ‖iteratedDerivWithin 1 H (Icc 0 T) t‖ ≤ B)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖H t - H 0‖ ≤ B * t := by
  simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using
    (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_derivWithin_le
      (hH.differentiableOn one_ne_zero) (by simpa using hB) ⟨le_rfl, hT.le⟩ ht

lemma rescaledIterate_zero {𝕜 : Type} [RCLike 𝕜] {α : ℝ}
    (hα : 0 < α) (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) :
    rescaledIterate α k f 1 0 = (1/α) • (k (0,0) * f 0) := by
  simp only [rescaledIterate, Nat.cast_zero, zero_mul, zero_add]
  rw [integral_smul_const]
  congr 1
  rw [WeakVolterraResolvent.integral_betaWeight hα (by norm_num),
    Real.Gamma_one, Real.Gamma_add_one hα.ne']
  field_simp [(Real.Gamma_pos_of_pos hα).ne']

lemma rescaledIterate_zero_of_datum_zero {𝕜 : Type} [RCLike 𝕜]
    (α : ℝ) (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (hf : f 0 = 0) :
    ∀ n, rescaledIterate α k f n 0 = 0 := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih => simp [rescaledIterate, ih]

/-- Absorb the time powers of any tail of a Gamma-majorized series. -/
lemma gamma_tail_majorant {𝕜 : Type} [RCLike 𝕜]
    {F : ℕ → ℝ → 𝕜} {α c D β T : ℝ} (hα : 0 < α)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (q d : ℕ)
    (hF : ∀ n t, t ∈ Ioc (0 : ℝ) T →
      ‖F n t‖ ≤ D * ((n+q : ℕ) : ℝ)^d * c^(n+q) /
        Real.Gamma (((n+q : ℕ) : ℝ)*α+1) *
        t^(((n+q : ℕ) : ℝ)*α-β)) :
    ∃ b : ℕ → ℝ, Summable b ∧ (∀ n, 0 ≤ b n) ∧
      ∀ n t, t ∈ Ioc (0 : ℝ) T → ‖F n t‖ ≤ b n * t^((q : ℝ)*α-β) := by
  let R : ℝ := max 1 T
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let b : ℕ → ℝ := fun n =>
    (D / R^((q : ℝ)*α)) * (((n+q : ℕ) : ℝ)^d * (c*R^α)^(n+q) /
      Real.Gamma (((n+q : ℕ) : ℝ)*α+1))
  refine ⟨b, ((summable_nat_add_iff q).mpr
    (polynomial_gamma_summability hα (by positivity) d)).mul_left _,
    fun n => by dsimp [b]; positivity [Real.Gamma_pos_of_pos (by positivity :
      0 < ((n+q : ℕ) : ℝ)*α+1)], ?_⟩
  intro n t ht
  have hp : t^((n : ℝ)*α) ≤ R^((n : ℝ)*α) :=
    Real.rpow_le_rpow ht.1.le (ht.2.trans (le_max_right _ _)) (by positivity)
  calc
    ‖F n t‖ ≤ D * ((n+q : ℕ) : ℝ)^d * c^(n+q) /
        Real.Gamma (((n+q : ℕ) : ℝ)*α+1) * t^(((n+q : ℕ) : ℝ)*α-β) := hF n t ht
    _ = D * ((n+q : ℕ) : ℝ)^d * c^(n+q) /
        Real.Gamma (((n+q : ℕ) : ℝ)*α+1) *
          (t^((n : ℝ)*α)*t^((q : ℝ)*α-β)) := by
      rw [show ((n+q : ℕ) : ℝ)*α-β = (n : ℝ)*α+((q : ℝ)*α-β) by
        push_cast; ring, Real.rpow_add ht.1]
    _ ≤ D * ((n+q : ℕ) : ℝ)^d * c^(n+q) /
        Real.Gamma (((n+q : ℕ) : ℝ)*α+1) *
          (R^((n : ℝ)*α)*t^((q : ℝ)*α-β)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg ht.1.le _))
        (by positivity [Real.Gamma_pos_of_pos (by positivity :
          0 < ((n+q : ℕ) : ℝ)*α+1)])
    _ = b n * t^((q : ℝ)*α-β) := by
      dsimp [b]
      rw [mul_pow, ← Real.rpow_mul_natCast hR.le,
        show α*((n+q : ℕ) : ℝ) = (n : ℝ)*α+(q : ℝ)*α by push_cast; ring,
        Real.rpow_add hR]
      field_simp


/-- All solutions have the actual rescaled Neumann expansion. -/
lemma solution_rescaled_hasSum {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) {k : ℝ × ℝ → 𝕜} {f u : ℝ → 𝕜} {ζ : 𝕜}
    (hk : ContinuousOn k (WeakVolterraBounds.Spec.triangle T))
    (hf : ContinuousOn f (Icc 0 T))
    (hu : WeightedVolterraDerivatives.Spec.IsSolution α T k f ζ u) :
    ∀ t ∈ Ioc (0 : ℝ) T, HasSum (fun n : ℕ => ζ^(n+1) *
      (t^(((n+1 : ℕ) : ℝ)*α) • rescaledIterate α k f (n+1) t)) (u t - f t) := by
  let K : C(WeakVolterraBounds.Spec.triangle T, 𝕜) :=
    ⟨fun z => k z, continuousOn_iff_continuous_domRestrict.mp hk⟩
  let F : C(Icc (0 : ℝ) T, 𝕜) :=
    ⟨fun t => f t, continuousOn_iff_continuous_domRestrict.mp hf⟩
  let U : C(Icc (0 : ℝ) T, 𝕜) :=
    ⟨fun t => u t, continuousOn_iff_continuous_domRestrict.mp hu.1⟩
  obtain ⟨V, hV, _⟩ := WeakVolterraBounds.continuous_construction
    α T hα hT K ‖K‖ (norm_nonneg _) (fun z => K.norm_coe_le_norm z)
  have hV' : WeakVolterraResolvent.Spec.ContinuousRealizes hT α K V :=
    fun f t => (hV f t).2
  have hU : U = F + ζ • V U := continuous_equation_of_solution
    hT hu K (fun _ => rfl) F U (fun _ => rfl) (fun _ => rfl) V hV'
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) T := Ioc_subset_Icc_self ht
  convert correction_hasSum hα hT K V hV' ζ F U hU ⟨t, ht'⟩ using 1
  ext n
  rw [← continuous_iterate_rescaled hT k f K (fun _ => rfl) F (fun _ => rfl)
    V hV' (n+1) t ht]
  simp only [FractionalIntegrals.Spec.continuousExtension, projIcc_of_mem hT ht']

lemma norm_rescaled_term_le {𝕜 : Type} [RCLike 𝕜]
    {α D c t : ℝ} {H : ℕ → ℝ → 𝕜} (ζ : 𝕜) (n : ℕ) (ht : 0 ≤ t)
    (hb : ‖H n t‖ ≤ D*c^n / Real.Gamma ((n : ℝ)*α+1)) :
    ‖ζ^n * (t^((n : ℝ)*α) • H n t)‖ ≤
      D*(‖ζ‖*c)^n / Real.Gamma ((n : ℝ)*α+1) * t^((n : ℝ)*α) := by
  rw [norm_mul, norm_pow, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht _)]
  calc
    _ ≤ ‖ζ‖^n * (t^((n : ℝ)*α) * (D*c^n / Real.Gamma ((n : ℝ)*α+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb
        (Real.rpow_nonneg ht _)) (by positivity)
    _ = _ := by rw [mul_pow]; ring

lemma expansion_of_rescaled_bounds {𝕜 : Type} [RCLike 𝕜]
    {α T D c : ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
    {k : ℝ × ℝ → 𝕜} {f u : ℝ → 𝕜} {ζ : 𝕜}
    (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hH : ∀ n, ContDiffOn ℝ 1 (rescaledIterate α k f n) (Icc 0 T))
    (hHb : ∀ j ≤ 1, ∀ n, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin j (rescaledIterate α k f n) (Icc 0 T) t‖ ≤
        D*c^n / Real.Gamma ((n : ℝ)*α+1))
    (hs : ∀ t ∈ Ioc (0 : ℝ) T, HasSum (fun n : ℕ => ζ^(n+1) *
      (t^(((n+1 : ℕ) : ℝ)*α) • rescaledIterate α k f (n+1) t)) (u t - f t)) :
    Spec.Expansion α T k f ζ u := by
  let A : ℕ → ℝ → 𝕜 := fun n t => ζ^(n+1) *
    (t^(((n+1 : ℕ) : ℝ)*α) • rescaledIterate α k f (n+1) t)
  obtain ⟨b, hb, hb0, hAb⟩ := gamma_tail_majorant (β := 0) hα
    (mul_nonneg (norm_nonneg ζ) hc) hD 2 0 (F := fun n => A (n+1)) (by
      intro n t ht
      simpa only [A, pow_zero, mul_one, sub_zero, Nat.add_assoc] using
        norm_rescaled_term_le ζ (n+1+1) ht.1.le
          (by simpa using hHb 0 (by omega) (n+1+1) t (Ioc_subset_Icc_self ht)))
  have htail : ∀ t ∈ Ioc (0 : ℝ) T,
      ‖u t-f t-A 0 t‖ ≤ (∑' n, b n) * t^(2*α) := by
    intro t ht
    have hh : HasSum (fun n => A (n+1) t) (u t-f t-A 0 t) := by
      simpa only [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).mpr (hs t ht)
    rw [← hh.tsum_eq]
    simpa only [Nat.cast_ofNat, sub_zero] using
      (weighted_tsum_bound (α := 2*α) (β := 0) hb hb0
        (by simpa only [Nat.cast_ofNat, sub_zero] using hAb)).2.1 t ht
  let B : ℝ := D*c / Real.Gamma (α+1)
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg hD hc)
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hfirst : ∀ t ∈ Ioc (0 : ℝ) T,
      ‖A 0 t - t^α • Spec.coefficient α k f ζ‖ ≤
        (‖ζ‖*B*(max 1 T)^(1-α))*t^(2*α) := by
    intro t ht
    have hdiff := norm_sub_zero_le hT (hH 1)
      (by simpa [B] using hHb 1 (by omega) 1) t (Ioc_subset_Icc_self ht)
    have he : Spec.coefficient α k f ζ = ζ * rescaledIterate α k f 1 0 := by
      rw [rescaledIterate_zero hα]
      simp only [Spec.coefficient, mul_smul_comm, mul_assoc]
    have he' : A 0 t - t^α • Spec.coefficient α k f ζ =
        t^α • (ζ * (rescaledIterate α k f 1 t - rescaledIterate α k f 1 0)) := by
      simp only [A, zero_add, pow_one, Nat.cast_one, one_mul, he, mul_sub,
        smul_sub, mul_smul_comm]
    rw [he', norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _), norm_mul]
    calc
      _ ≤ t^α * (‖ζ‖ * (B*t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiff (norm_nonneg _))
          (Real.rpow_nonneg ht.1.le _)
      _ = ‖ζ‖*B*(t^(1-α)*t^(2*α)) := by
        rw [← Real.rpow_add ht.1,
          show 1-α+2*α = α+1 by ring, Real.rpow_add ht.1, Real.rpow_one]
        ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow ht.1.le (ht.2.trans (le_max_right (1 : ℝ) T))
              (show 0 ≤ 1-α by linarith))
            (Real.rpow_nonneg ht.1.le (2*α))) (mul_nonneg (norm_nonneg ζ) hB0)
  refine ⟨(∑' n, b n) + ‖ζ‖*B*(max 1 T)^(1-α),
    add_nonneg (tsum_nonneg hb0) (by positivity), ?_⟩
  intro t ht
  calc
    _ = ‖(u t-f t-A 0 t)+(A 0 t-t^α • Spec.coefficient α k f ζ)‖ := by
      congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add (htail t ht) (hfirst t ht)
    _ = _ := by ring

theorem endpoint_expansion : Spec.EndpointExpansion := by
  intro 𝕜 _ α T m hα hα1 hT hm k f ζ u hk hf hu
  by_cases hT0 : T = 0
  · subst T
    exact ⟨0, le_rfl, by simp⟩
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  have hk1 : WeightedVolterraDerivatives.Spec.SmoothKernel 1 T k := by
    obtain ⟨U, ho, ht, hk⟩ := hk
    exact ⟨U, ho, ht, hk.of_le (by exact_mod_cast hm)⟩
  have hf1 : ContDiffOn ℝ 1 f (Icc 0 T) := hf.of_le (by exact_mod_cast hm)
  obtain ⟨D,c,hD,hc,hH,hHb⟩ := rescaledIterate_smooth_gamma_bounds hα hTpos k f hk1 hf1
  exact expansion_of_rescaled_bounds hα hα1 hTpos hD hc hH hHb
    (solution_rescaled_hasSum hα hT (smoothKernel_continuousOn hk) hf.continuousOn hu)

/-- A power bound with positive exponent forces a right-hand limit of zero. -/
lemma tendsto_zero_of_power_bound {𝕜 : Type} [RCLike 𝕜]
    {g : ℝ → 𝕜} {T p C : ℝ} (hp : 0 < p)
    (hg : ∀ t ∈ Ioc (0 : ℝ) T, ‖g t‖ ≤ C*t^p) :
    Tendsto g (𝓝[Ioc 0 T] 0) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t => C*t^p) (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hg t ht)
  simpa using (tendsto_const_nhds.mul
    ((tendsto_id.mono_left nhdsWithin_le_nhds).rpow_const_nhds_zero hp) :
    Tendsto (fun t : ℝ => C*t^p) (𝓝[Ioc 0 T] 0) (𝓝 (C*0)))

lemma expansion_normalized_limit {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) {k : ℝ × ℝ → 𝕜} {f u : ℝ → 𝕜} {ζ : 𝕜}
    (he : Spec.Expansion α T k f ζ u) :
    Tendsto (fun t => t^(-α) • (u t-f t)) (𝓝[Ioc 0 T] 0)
      (𝓝 (Spec.coefficient α k f ζ)) := by
  obtain ⟨C, _, hC⟩ := he
  have hz : Tendsto (fun t => t^(-α) • (u t-f t-t^α • Spec.coefficient α k f ζ))
      (𝓝[Ioc 0 T] 0) (𝓝 0) := by
    apply tendsto_zero_of_power_bound hα
    intro t ht
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    calc
      _ ≤ t^(-α)*(C*t^(2*α)) :=
        mul_le_mul_of_nonneg_left (hC t ht) (Real.rpow_nonneg ht.1.le _)
      _ = C*t^α := by rw [mul_left_comm, ← Real.rpow_add ht.1]; ring_nf
  have heq : ∀ᶠ t in 𝓝[Ioc (0 : ℝ) T] 0,
      t^(-α) • (u t-f t-t^α • Spec.coefficient α k f ζ) =
        t^(-α) • (u t-f t) - Spec.coefficient α k f ζ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [smul_sub, smul_smul, ← Real.rpow_add ht.1]
    simp
  exact tendsto_sub_nhds_zero_iff.mp (hz.congr' heq)

/-- A differentiable correction vanishing at zero, scaled by a smaller
power, has zero limit. This contradicts a nonzero leading coefficient. -/
lemma normalized_limit_of_differentiable {𝕜 : Type} [RCLike 𝕜]
    {α T : ℝ} (hα1 : α < 1) {g : ℝ → 𝕜} (hg0 : g 0 = 0)
    (hg : DifferentiableWithinAt ℝ g (Icc 0 T) 0) :
    Tendsto (fun t => t^(-α) • g t) (𝓝[Ioc 0 T] 0) (𝓝 0) := by
  obtain ⟨C,hC⟩ := hg.isBigO_sub.bound
  have hC' := hC.filter_mono (nhdsWithin_mono 0 Ioc_subset_Icc_self)
  apply squeeze_zero_norm' (a := fun t => C*t^(1-α)) ?_ ?_
  · filter_upwards [hC', self_mem_nhdsWithin] with t ht htI
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg htI.1.le _)]
    have hb : ‖g t‖ ≤ C*t := by
      simpa only [hg0, sub_zero, Real.norm_eq_abs, abs_of_nonneg htI.1.le] using ht
    calc
      _ ≤ t^(-α)*(C*t) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg htI.1.le _)
      _ = C*t^(1-α) := by
        rw [show 1-α = -α+1 by ring, Real.rpow_add htI.1, Real.rpow_one]; ring
  · simpa using (tendsto_const_nhds.mul
      ((tendsto_id.mono_left nhdsWithin_le_nhds).rpow_const_nhds_zero
        (show 0 < 1-α by linarith)) :
      Tendsto (fun t : ℝ => C*t^(1-α)) (𝓝[Ioc 0 T] 0) (𝓝 (C*0)))

theorem endpoint_obstruction : Spec.EndpointObstruction := by
  intro 𝕜 _ α T m hα hα1 hT hm k f ζ u hk hf hu hcoeff hdu
  have hdf : DifferentiableWithinAt ℝ f (Icc 0 T) 0 :=
    (hf.differentiableOn (by exact_mod_cast (show m ≠ 0 by omega))) 0 ⟨le_rfl,hT.le⟩
  have h0 : u 0-f 0 = 0 := sub_eq_zero.mpr (solution_zero hT.le hu)
  have hlim := normalized_limit_of_differentiable hα1 h0 (hdu.sub hdf)
  have hlim' := expansion_normalized_limit hα
    (endpoint_expansion α T m hα hα1 hT.le hm k f ζ u hk hf hu)
  have : NeBot (𝓝[Ioc (0 : ℝ) T] 0) := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hT]
    infer_instance
  exact hcoeff (tendsto_nhds_unique hlim' hlim)

/-- Vanishing of the smooth factor cancels the loss of one time power in
its product with t^p. -/
lemma compatible_term_derivative_bound {𝕜 : Type} [RCLike 𝕜]
    {T p B : ℝ} (hT : 0 < T) (hp : 0 ≤ p) {H : ℝ → 𝕜}
    (hH : ContDiffOn ℝ 1 H (Icc 0 T)) (h0 : H 0 = 0)
    (hB : ∀ t ∈ Icc (0 : ℝ) T, ‖derivWithin H (Icc 0 T) t‖ ≤ B)
    (w : 𝕜) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) :
    ‖derivWithin (fun s => w*(s^p • H s)) (Ioc 0 T) t‖ ≤
      ‖w‖*(p+1)*B*t^p := by
  have hdH := ((hH.differentiableOn one_ne_zero) t (Ioc_subset_Icc_self ht)).hasDerivWithinAt
  have hd := ((Real.hasDerivAt_rpow_const (p := p) (Or.inl ht.1.ne')).hasDerivWithinAt.smul
    (hdH.mono Ioc_subset_Icc_self)).const_mul w
  change HasDerivWithinAt (fun s => w*(s^p • H s))
    (w*(t^p • derivWithin H (Icc 0 T) t + (p*t^(p-1)) • H t)) (Ioc 0 T) t at hd
  rw [hd.derivWithin (uniqueDiffOn_Ioc _ _ t ht), norm_mul]
  have hval : ‖H t‖ ≤ B*t := by
    simpa only [h0, sub_zero] using norm_sub_zero_le hT hH (by simpa using hB)
      t (Ioc_subset_Icc_self ht)
  have hBp : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl,hT.le⟩)
  calc
    _ ≤ ‖w‖ * (‖t^p • derivWithin H (Icc 0 T) t‖ +
        ‖(p*t^(p-1)) • H t‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg w)
    _ = ‖w‖ * (t^p * ‖derivWithin H (Icc 0 T) t‖ +
        (p*t^(p-1)) * ‖H t‖) := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _),
        Real.norm_of_nonneg (mul_nonneg hp (Real.rpow_nonneg ht.1.le _))]
    _ ≤ ‖w‖ * (t^p * B + (p*t^(p-1))*(B*t)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (hB t (Ioc_subset_Icc_self ht))
          (Real.rpow_nonneg ht.1.le _))
          (mul_le_mul_of_nonneg_left hval (mul_nonneg hp (Real.rpow_nonneg ht.1.le _))))
        (norm_nonneg w)
    _ = _ := by
      have he : t^(p-1)*t = t^p := by
        calc
          _ = t^(p-1)*t^(1 : ℝ) := by rw [Real.rpow_one]
          _ = t^(p-1+1) := (Real.rpow_add ht.1 _ _).symm
          _ = _ := by congr 1; ring
      calc
        _ = ‖w‖ * (t^p * B + p*B*(t^(p-1)*t)) := by ring
        _ = _ := by rw [he]; ring

lemma compatible_rescaled_bounds {𝕜 : Type} [RCLike 𝕜]
    {α T D c : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hT : 0 < T)
    {k : ℝ × ℝ → 𝕜} {f : ℝ → 𝕜} (ζ : 𝕜)
    (hD : 0 ≤ D) (hc : 0 ≤ c) (hf0 : f 0 = 0)
    (hH : ∀ n, ContDiffOn ℝ 1 (rescaledIterate α k f n) (Icc 0 T))
    (hHb : ∀ j ≤ 1, ∀ n, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin j (rescaledIterate α k f n) (Icc 0 T) t‖ ≤
        D*c^n / Real.Gamma ((n : ℝ)*α+1)) :
    ∃ b d : ℕ → ℝ, Summable b ∧ Summable d ∧
      (∀ n, 0 ≤ b n) ∧ (∀ n, 0 ≤ d n) ∧
      (∀ n t, t ∈ Ioc (0 : ℝ) T →
        ‖ζ^(n+1) * (t^(((n+1 : ℕ) : ℝ)*α) • rescaledIterate α k f (n+1) t)‖ ≤
          b n*t^(α+1)) ∧
      (∀ n t, t ∈ Ioc (0 : ℝ) T →
        ‖derivWithin (fun s => ζ^(n+1) *
          (s^(((n+1 : ℕ) : ℝ)*α) • rescaledIterate α k f (n+1) s)) (Ioc 0 T) t‖ ≤
          d n*t^α) := by
  let A : ℕ → ℝ → 𝕜 := fun n t => ζ^(n+1) *
    (t^(((n+1 : ℕ) : ℝ)*α) • rescaledIterate α k f (n+1) t)
  have hval : ∀ n t, t ∈ Ioc (0 : ℝ) T →
      ‖A n t‖ ≤ D * ((n+1 : ℕ) : ℝ)^0 * (‖ζ‖*c)^(n+1) /
        Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) * t^(((n+1 : ℕ) : ℝ)*α-(-1)) := by
    intro n t ht
    have hz := rescaledIterate_zero_of_datum_zero α k f hf0 (n+1)
    have hv : ‖rescaledIterate α k f (n+1) t‖ ≤
        (D*c^(n+1)/Real.Gamma (((n+1 : ℕ) : ℝ)*α+1))*t := by
      simpa only [hz, sub_zero] using norm_sub_zero_le hT (hH (n+1))
        (hHb 1 (by omega) (n+1)) t (Ioc_subset_Icc_self ht)
    dsimp [A]
    rw [norm_mul, norm_pow, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    calc
      _ ≤ ‖ζ‖^(n+1) * (t^(((n+1 : ℕ) : ℝ)*α) *
          ((D*c^(n+1)/Real.Gamma (((n+1 : ℕ) : ℝ)*α+1))*t)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv
          (Real.rpow_nonneg ht.1.le _)) (by positivity)
      _ = _ := by
        rw [pow_zero, mul_one, sub_neg_eq_add, Real.rpow_add ht.1, Real.rpow_one, mul_pow]
        ring
  have hder : ∀ n t, t ∈ Ioc (0 : ℝ) T →
      ‖derivWithin (A n) (Ioc 0 T) t‖ ≤
        (2*D)*((n+1 : ℕ) : ℝ)^1*(‖ζ‖*c)^(n+1) /
          Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) * t^(((n+1 : ℕ) : ℝ)*α-0) := by
    intro n t ht
    have hb0 : 0 ≤ D*c^(n+1)/Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) := by
      positivity [Real.Gamma_pos_of_pos (by positivity : 0 < ((n+1 : ℕ) : ℝ)*α+1)]
    have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    have hnα : ((n+1 : ℕ) : ℝ)*α+1 ≤ 2*((n+1 : ℕ) : ℝ) := by nlinarith
    calc
      _ ≤ ‖ζ^(n+1)‖ * (((n+1 : ℕ) : ℝ)*α+1) *
          (D*c^(n+1)/Real.Gamma (((n+1 : ℕ) : ℝ)*α+1)) * t^(((n+1 : ℕ) : ℝ)*α) :=
        compatible_term_derivative_bound hT (by positivity) (hH (n+1))
          (rescaledIterate_zero_of_datum_zero α k f hf0 (n+1))
          (by simpa using hHb 1 (by omega) (n+1)) _ _ ht
      _ ≤ ‖ζ^(n+1)‖ * (2*((n+1 : ℕ) : ℝ)) *
          (D*c^(n+1)/Real.Gamma (((n+1 : ℕ) : ℝ)*α+1)) * t^(((n+1 : ℕ) : ℝ)*α) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnα (norm_nonneg _)) hb0)
          (Real.rpow_nonneg ht.1.le _)
      _ = _ := by rw [norm_pow, pow_one, sub_zero, mul_pow]; ring
  obtain ⟨b,hb,hb0,hbnd⟩ := gamma_tail_majorant hα
    (mul_nonneg (norm_nonneg ζ) hc) hD 1 0 hval
  obtain ⟨d,hd,hd0,hdnd⟩ := gamma_tail_majorant hα
    (mul_nonneg (norm_nonneg ζ) hc) (mul_nonneg (by norm_num) hD) 1 1 hder
  exact ⟨b,d,hb,hd,hb0,hd0,
    by simpa only [Nat.cast_one, one_mul, sub_neg_eq_add, A] using hbnd,
    by simpa only [Nat.cast_one, one_mul, sub_zero, A] using hdnd⟩

lemma positive_interval_mem_nhdsWithin {T t : ℝ} (ht : 0 < t) :
    Ioc (0 : ℝ) T ∈ 𝓝[Icc 0 T] t := by
  apply mem_of_superset
    (inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)) self_mem_nhdsWithin)
  intro s hs
  exact ⟨hs.1, hs.2.2⟩

/-- Glue the positive-time derivative to its zero endpoint limit. -/
lemma contDiffOn_closed_of_deriv_zero_limit {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} (hT : 0 < T) {g : ℝ → 𝕜}
    (hgc : ContinuousOn g (Icc 0 T)) (hg : ContDiffOn ℝ 1 g (Ioc 0 T))
    (hlim : Tendsto (derivWithin g (Ioc 0 T)) (𝓝[Ioc 0 T] 0) (𝓝 0)) :
    ContDiffOn ℝ 1 g (Icc 0 T) ∧ HasDerivWithinAt g 0 (Icc 0 T) 0 ∧
      Tendsto (derivWithin g (Icc 0 T)) (𝓝[Ioc 0 T] 0) (𝓝 0) := by
  have hlimAt : Tendsto (deriv g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hT] at hlim
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    exact (((hg.differentiableOn one_ne_zero) t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt.hasDerivAt
      (Ioc_mem_nhds ht.1 ht.2)).deriv.symm
  have hd0 : HasDerivWithinAt g 0 (Icc 0 T) 0 := by
    apply (hasDerivWithinAt_Ici_of_tendsto_deriv
      ((hg.differentiableOn one_ne_zero).mono Ioo_subset_Ioc_self)
      ((hgc 0 ⟨le_rfl,hT.le⟩).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT hT) hlimAt).mono Icc_subset_Ici_self
  have hd (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) :
      HasDerivWithinAt g (derivWithin g (Ioc 0 T) t) (Icc 0 T) t :=
    (((hg.differentiableOn one_ne_zero) t ht).hasDerivWithinAt).mono_of_mem_nhdsWithin
      (positive_interval_mem_nhdsWithin ht.1)
  have heq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) :
      derivWithin g (Icc 0 T) t = derivWithin g (Ioc 0 T) t :=
    (hd t ht).derivWithin (uniqueDiffOn_Icc hT t (Ioc_subset_Icc_self ht))
  have hlim' : Tendsto (derivWithin g (Icc 0 T)) (𝓝[Ioc 0 T] 0) (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heq t ht).symm
  have hd00 : derivWithin g (Icc 0 T) 0 = 0 :=
    hd0.derivWithin (uniqueDiffOn_Icc hT 0 ⟨le_rfl,hT.le⟩)
  refine ⟨(contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hT)).mpr ⟨?_, ?_⟩, hd0, hlim'⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with he | hp
    · subst t
      exact hd0.differentiableWithinAt
    · exact (hd t ⟨hp,ht.2⟩).differentiableWithinAt
  · have hcp : ContinuousOn (derivWithin g (Icc 0 T)) (Ioc 0 T) :=
      (hg.continuousOn_derivWithin (uniqueDiffOn_Ioc _ _) le_rfl).congr heq
    intro t ht
    rcases eq_or_lt_of_le ht.1 with he | hp
    · subst t
      have hset : insert (0 : ℝ) (Ioc 0 T) = Icc 0 T := by
        ext t
        simp only [mem_insert_iff, mem_Ioc, mem_Icc]
        constructor
        · rintro (rfl | h)
          · exact ⟨le_rfl,hT.le⟩
          · exact ⟨h.1.le,h.2⟩
        · intro h
          rcases eq_or_lt_of_le h.1 with he | hp
          · exact Or.inl he.symm
          · exact Or.inr ⟨hp,h.2⟩
      have hc0 : ContinuousWithinAt (derivWithin g (Icc 0 T)) (insert 0 (Ioc 0 T)) 0 :=
        continuousWithinAt_insert_self.mpr (by simpa only [ContinuousWithinAt, hd00] using hlim')
      simpa only [hset] using hc0
    · exact (hcp t ⟨hp,ht.2⟩).mono_of_mem_nhdsWithin (positive_interval_mem_nhdsWithin hp)

lemma compatibility_of_series {𝕜 : Type} [RCLike 𝕜]
    {α T : ℝ} (hα : 0 < α) (hT : 0 < T) {f u : ℝ → 𝕜}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T)) (hu : ContinuousOn u (Icc 0 T))
    {A : ℕ → ℝ → 𝕜} {b d : ℕ → ℝ}
    (hA : ∀ n, ContDiffOn ℝ 1 (A n) (Ioc 0 T))
    (hb : Summable b) (hd : Summable d) (hb0 : ∀ n, 0 ≤ b n) (hd0 : ∀ n, 0 ≤ d n)
    (hB : ∀ n t, t ∈ Ioc (0 : ℝ) T → ‖A n t‖ ≤ b n*t^(α+1))
    (hD : ∀ n t, t ∈ Ioc (0 : ℝ) T → ‖derivWithin (A n) (Ioc 0 T) t‖ ≤ d n*t^α)
    (hs : ∀ t ∈ Ioc (0 : ℝ) T, HasSum (fun n => A n t) (u t-f t)) :
    Spec.Compatibility α T f u := by
  let B : ℕ → ℕ → ℝ := fun j n => if j = 0 then b n else d n
  have hBs (j : ℕ) (_hj : j ≤ 1) : Summable (B j) := by
    by_cases hj : j = 0 <;> simp only [B,hj,ite_true,ite_false] <;> assumption
  have hB0 (j : ℕ) (_hj : j ≤ 1) (n : ℕ) : 0 ≤ B j n := by
    by_cases hj : j = 0 <;> simp only [B,hj,ite_true,ite_false] <;> first | exact hb0 n | exact hd0 n
  have hBB : ∀ j ≤ 1, ∀ n t, t ∈ Ioc (0 : ℝ) T →
      ‖iteratedDerivWithin j (A n) (Ioc 0 T) t‖ ≤ B j n*t^(α+1-(j : ℝ)) := by
    intro j hj n t ht
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · simpa only [B,ite_true,Nat.cast_zero,sub_zero,iteratedDerivWithin_zero] using hB n t ht
    · simpa only [B,one_ne_zero,ite_false,Nat.cast_one,add_sub_cancel_right,
        iteratedDerivWithin_one] using hD n t ht
  have hr := derivative_conclusion_of_series hf hA hBs hB0 hBB hs
  obtain ⟨C,_,hC⟩ := hr.2 1 le_rfl le_rfl
  have hCb : ∀ t ∈ Ioc (0 : ℝ) T,
      ‖derivWithin (fun t => u t-f t) (Ioc 0 T) t‖ ≤ C*t^α := by
    simpa only [iteratedDerivWithin_one,Nat.cast_one,add_sub_cancel_right] using hC
  have hg := hr.1.sub (hf.mono Ioc_subset_Icc_self)
  have hlim := tendsto_zero_of_power_bound hα hCb
  obtain ⟨hgclosed,hg0,hlim'⟩ := contDiffOn_closed_of_deriv_zero_limit hT
    (hu.sub hf.continuousOn) hg hlim
  have heq : EqOn (fun t => f t+(u t-f t)) u (Icc 0 T) := by intro t _; abel
  refine ⟨(hf.add hgclosed).congr (fun t ht => (heq ht).symm), ?_, ?_, hlim'⟩
  · have hd := (((hf.differentiableOn one_ne_zero) 0 ⟨le_rfl,hT.le⟩).hasDerivWithinAt).add hg0
    simpa only [add_zero] using hd.congr
      (fun t ht => (heq ht).symm) (by simp only [Pi.add_apply,Pi.sub_apply]; abel)
  · refine ⟨∑' n, b n, tsum_nonneg hb0, ?_⟩
    intro t ht
    rw [← (hs t ht).tsum_eq]
    simpa only [sub_zero] using (weighted_tsum_bound (α := α+1) (β := 0) hb hb0
      (by simpa only [sub_zero] using hB)).2.1 t ht

/-- The degenerate interval has no positive-time instances. Every singleton
is smooth within that interval, and every specified derivative is valid there. -/
lemma compatibility_zero_time {𝕜 : Type} [RCLike 𝕜]
    (α : ℝ) (f u : ℝ → 𝕜) : Spec.Compatibility α 0 f u := by
  refine ⟨?_, ?_, ⟨0, le_rfl, by simp⟩, by simp⟩
  · intro t ht
    have : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simpa only [Icc_self] using
      (contDiffWithinAt_singleton : ContDiffWithinAt ℝ 1 u {(0 : ℝ)} 0)
  · exact HasFDerivWithinAt.of_subsingleton (by simp : (Icc (0 : ℝ) 0).Subsingleton)

theorem endpoint_compatibility : Spec.EndpointCompatibility := by
  intro 𝕜 _ α T m hα hα1 hT hm k f ζ u hk hf hu hf0
  by_cases hT0 : T = 0
  · subst T
    exact compatibility_zero_time α f u
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  have hk1 : WeightedVolterraDerivatives.Spec.SmoothKernel 1 T k := by
    obtain ⟨U,ho,ht,hk⟩ := hk
    exact ⟨U,ho,ht,hk.of_le (by exact_mod_cast hm)⟩
  have hf1 : ContDiffOn ℝ 1 f (Icc 0 T) := hf.of_le (by exact_mod_cast hm)
  obtain ⟨D,c,hD,hc,hH,hHb⟩ := rescaledIterate_smooth_gamma_bounds hα hTpos k f hk1 hf1
  obtain ⟨b,d,hb,hd,hb0,hd0,hB,hD'⟩ :=
    compatible_rescaled_bounds hα hα1.le hTpos ζ hD hc hf0 hH hHb
  have hA (n : ℕ) : ContDiffOn ℝ 1
      (fun t => ζ^(n+1) * (t^(((n+1 : ℕ) : ℝ)*α) • rescaledIterate α k f (n+1) t))
      (Ioc 0 T) :=
    contDiffOn_const.mul (contDiffOn_rpow_smul_pos ((hH (n+1)).mono Ioc_subset_Icc_self))
  exact compatibility_of_series hα hTpos hf1 hu.1 hA hb hd hb0 hd0 hB hD'
    (solution_rescaled_hasSum hα hT (smoothKernel_continuousOn hk) hf.continuousOn hu)

lemma differentiableWithinAt_of_extension {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ → 𝕜} (hext : Spec.HasC1ExtensionAtZero T u) :
    DifferentiableWithinAt ℝ u (Icc 0 T) 0 := by
  obtain ⟨U,ho,h0,v,hv,heq⟩ := hext
  have hd : DifferentiableAt ℝ v 0 :=
    ((hv.differentiableOn one_ne_zero) 0 h0).differentiableAt (ho.mem_nhds h0)
  apply (hd.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq ?_
    (heq ⟨⟨le_rfl,hT⟩,h0⟩).symm).differentiableWithinAt
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ho.mem_nhds h0), self_mem_nhdsWithin] with t htU ht
  exact (heq ⟨ht,htU⟩).symm

theorem endpoint_no_c1_extension : Spec.EndpointNoC1Extension := by
  intro 𝕜 _ α T m hα hα1 hT hm k f ζ u hk hf hu hcoeff hext
  exact endpoint_obstruction α T m hα hα1 hT hm k f ζ u hk hf hu hcoeff
    (differentiableWithinAt_of_extension hT.le hext)

end ExpandedFA.PartV.WeightedVolterraEndpoint
