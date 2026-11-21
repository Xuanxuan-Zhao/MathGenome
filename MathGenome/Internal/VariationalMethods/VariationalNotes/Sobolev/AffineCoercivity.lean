import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.AffineCoercivity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.SlabPoincare
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology
namespace VariationalNotes.Sobolev

/-- Splitting at a large scalar absorbs every lower power into a positive
multiple of a higher power, with a finite constant on the remaining interval. -/
theorem lower_power_absorption {p q ε : ℝ} (hq : 0 ≤ q) (hqp : q < p)
    (hε : 0 < ε) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ t : ℝ, 0 ≤ t → t ^ q ≤ ε * t ^ p + B := by
  obtain ⟨T, hT⟩ := (tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (sub_pos.mpr hqp))) (1 / ε)
  let R := max 1 T
  refine ⟨R ^ q, Real.rpow_nonneg (by dsimp [R]; positivity) _, ?_⟩
  intro t ht
  by_cases h : t ≤ R
  · exact (Real.rpow_le_rpow ht h hq).trans (le_add_of_nonneg_left (by positivity))
  · have htR : R ≤ t := le_of_not_ge h
    have ht1 : 1 ≤ t := (le_max_left 1 T).trans htR
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hpow : 1 / ε ≤ t ^ (p-q) := hT t ((le_max_right 1 T).trans htR)
    have hmul : t ^ q * t ^ (p-q) = t ^ p := by
      rw [← Real.rpow_add htpos]; congr 1; ring
    have hcoeff : 1 ≤ ε * t ^ (p-q) := by simpa only [mul_comm] using (div_le_iff₀ hε).mp hpow
    have hh := mul_le_mul_of_nonneg_left hcoeff (Real.rpow_nonneg ht q)
    rw [mul_one] at hh
    have heq : t ^ q * (ε * t ^ (p-q)) = ε * t ^ p := by rw [← hmul]; ring
    rw [heq] at hh
    exact hh.trans (le_add_of_nonneg_right (Real.rpow_nonneg (by dsimp [R]; positivity) _))

/-- Monotonicity of the signed extended integral. -/
theorem extendedIntegral_mono_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (h : f ≤ᵐ[μ] g) : extendedIntegral μ f ≤ extendedIntegral μ g := by
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (h.mono fun _ hx => ENNReal.ofReal_le_ofReal hx))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (h.mono fun _ hx => ENNReal.ofReal_le_ofReal (neg_le_neg hx)))

/-- An integrable lower comparison can be integrated even when the energy
has nonintegrable positive part. -/
theorem integral_le_extendedIntegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : Integrable f μ) (h : f ≤ᵐ[μ] g) :
    ((∫ x, f x ∂μ : ℝ) : EReal) ≤ extendedIntegral μ g := by
  rw [← extendedIntegral_eq_integral hf]
  exact extendedIntegral_mono_ae h

variable {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)

/-- A bounded domain in positive dimension fits in a coordinate strip.
The extra unit on each side also covers the empty domain. -/
theorem bounded_domain_strip [NeZero d]
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) :
    ∃ a b : ℝ, a < b ∧ InCoordinateStrip Ω ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ a b := by
  obtain ⟨R, hR, hbound⟩ := hΩ.exists_pos_norm_le
  refine ⟨-R-1, R+1, by linarith, ?_⟩
  intro x hx
  have hc := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) x ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have habs : |x ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩| ≤ R :=
    hc.trans (hbound x hx)
  exact ⟨by have := (abs_le.mp habs).1; linarith,
    by have := (abs_le.mp habs).2; linarith⟩

/-- Nonhomogeneous boundary data contributes only a fixed additive constant. -/
theorem affine_norm_control [NeZero d]
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (u₀ : W1p Ω m p) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ u ∈ affineClass Ω m p u₀,
      ‖u‖ ≤ A + B * ‖gradient Ω m p u‖ := by
  obtain ⟨a, b, hab, hstrip⟩ := bounded_domain_strip Ω hΩ
  let L := b-a+1
  have hL : 0 ≤ L := by dsimp [L]; linarith
  refine ⟨‖u₀‖ + L * ‖gradient Ω m p u₀‖, L, by positivity, hL, ?_⟩
  intro u hu
  let v : W1pZero Ω m p := ⟨u-u₀, hu⟩
  have hv := (slab_norm_equivalence Ω p _ a b hab hstrip v).2
  have hgrad : ‖gradient Ω m p (u-u₀)‖ ≤
      ‖gradient Ω m p u‖ + ‖gradient Ω m p u₀‖ := by
    rw [map_sub]; exact norm_sub_le _ _
  have hnorm : ‖u‖ ≤ ‖u₀‖ + ‖u-u₀‖ := by
    calc
      ‖u‖ = ‖u₀ + (u-u₀)‖ := by congr 1; abel
      _ ≤ ‖u₀‖ + ‖u-u₀‖ := norm_add_le _ _
  calc
    ‖u‖ ≤ ‖u₀‖ + ‖u-u₀‖ := hnorm
    _ ≤ ‖u₀‖ + L * ‖gradient Ω m p (u-u₀)‖ := add_le_add le_rfl hv
    _ ≤ ‖u₀‖ + L * (‖gradient Ω m p u‖ + ‖gradient Ω m p u₀‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hgrad hL)
    _ = _ := by ring

/-- Lp powers are integrable and integrate to the corresponding norm power. -/
theorem lp_power_integrable {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure X) (f : Lp E p.ennreal μ) :
    Integrable (fun x => ‖f x‖ ^ p.real) μ := by
  have hp : p.ennreal ≠ 0 := (ENNReal.ofReal_pos.mpr p.pos).ne'
  simpa only [Exponent.toReal] using
    memLp_one_iff_integrable.mp ((Lp.memLp f).norm_rpow hp ENNReal.ofReal_ne_top)

theorem integral_lp_power {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure X) (f : Lp E p.ennreal μ) :
    ∫ x, ‖f x‖ ^ p.real ∂μ = ‖f‖ ^ p.real := by
  have hp : p.ennreal ≠ 0 := (ENNReal.ofReal_pos.mpr p.pos).ne'
  have heq : ‖f‖ = (∫ x, ‖f x‖ ^ p.real ∂μ) ^ p.real⁻¹ := by
    simpa only [Lp.norm_def, toReal_eLpNorm, Exponent.toReal] using
      lpNorm_eq_integral_norm_rpow_toReal hp ENNReal.ofReal_ne_top (Lp.aestronglyMeasurable f)
  rw [heq, ← Real.rpow_mul (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)),
    inv_mul_cancel₀ p.pos.ne', Real.rpow_one]

/-- A linear norm bound implies a polynomial bound with a uniform constant. -/
theorem affine_power_control {A B t v : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : 0 ≤ t) (hv : 0 ≤ v) (h : v ≤ A+B*t) :
    v ^ p.real ≤ (A+B) ^ p.real * (1+t ^ p.real) := by
  have hp := p.pos.le
  by_cases ht1 : t ≤ 1
  · have hlin : v ≤ A+B := h.trans (by nlinarith)
    have hpow := Real.rpow_le_rpow hv hlin hp
    have hK : 0 ≤ (A+B) ^ p.real := Real.rpow_nonneg (by positivity) _
    nlinarith [Real.rpow_nonneg ht p.real]
  · have ht1' : 1 ≤ t := le_of_not_ge ht1
    have hlin : v ≤ (A+B)*t := h.trans (by nlinarith)
    have hpow := Real.rpow_le_rpow hv hlin hp
    rw [Real.mul_rpow (by positivity) ht] at hpow
    have hK : 0 ≤ (A+B) ^ p.real := Real.rpow_nonneg (by positivity) _
    nlinarith

/-- The quantitative coercivity estimate, before any convexity assumption. -/
theorem affine_coercive_estimate : AffineCoercivityExpected.Estimate := by
  intro d m _ _ Ω p q u₀ F α C a H
  obtain ⟨A, B, hA, hB, hnorm⟩ := affine_norm_control Ω p H.bounded u₀
  let K := (A+B) ^ p.real
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  let ε := α / (2 * ((C+1)*(K+1)))
  have hC := H.C_nonneg
  have hden : 0 < 2 * ((C+1)*(K+1)) := by positivity
  have hε : 0 < ε := div_pos H.alpha_pos hden
  obtain ⟨D, hD, hpower⟩ := lower_power_absorption q.pos.le H.exponent_lt hε
  have hεeq : 2 * ((C+1)*(K+1)) * ε = α := by
    dsimp [ε]; exact mul_div_cancel₀ _ hden.ne'
  have habsorb : C * ε * K ≤ α / 2 := by
    have hCK : C*K ≤ (C+1)*(K+1) := by nlinarith [H.C_nonneg]
    have := mul_le_mul_of_nonneg_right hCK hε.le
    nlinarith
  let : IsFiniteMeasure (domainMeasure Ω) :=
    (isFiniteMeasure_restrict).mpr H.bounded.measure_lt_top.ne
  let V := (domainMeasure Ω Set.univ).toReal
  refine ⟨C*ε*K + C*D*V + ∫ x, a x ∂domainMeasure Ω, ?_⟩
  intro u hu
  have hv := lp_power_integrable p (domainMeasure Ω) (value Ω m p u)
  have hG := lp_power_integrable p (domainMeasure Ω) (gradient Ω m p u)
  let g : Domain d → ℝ := fun x =>
    α * ‖gradient Ω m p u x‖ ^ p.real -
      C*ε * ‖value Ω m p u x‖ ^ p.real - (C*D + a x)
  have hg : Integrable g (domainMeasure Ω) :=
    (hG.const_mul α).sub
      (hv.const_mul (C*ε)) |>.sub
        ((integrable_const (C*D)).add H.a_integrable)
  have hgf : g ≤ᵐ[domainMeasure Ω]
      fun x => F x (value Ω m p u x) (gradient Ω m p u x) := by
    filter_upwards [H.lower_bound] with x hx
    have hpw := mul_le_mul_of_nonneg_left
      (hpower ‖value Ω m p u x‖ (norm_nonneg _)) H.C_nonneg
    have hf := hx (value Ω m p u x) (gradient Ω m p u x)
    dsimp [g]; nlinarith
  have hi : ((∫ x, g x ∂domainMeasure Ω : ℝ) : EReal) ≤ energy Ω m p F u :=
    integral_le_extendedIntegral hg hgf
  have hig : ∫ x, g x ∂domainMeasure Ω =
      α * ‖gradient Ω m p u‖ ^ p.real - C*ε * ‖value Ω m p u‖ ^ p.real -
        (C*D*V + ∫ x, a x ∂domainMeasure Ω) := by
    have hsplit := integral_sub ((hG.const_mul α).sub (hv.const_mul (C*ε)))
      ((integrable_const (C*D)).add H.a_integrable)
    have hinner := integral_sub (hG.const_mul α) (hv.const_mul (C*ε))
    have hadd := integral_add (integrable_const (C*D)) H.a_integrable
    simp only [Pi.sub_apply, Pi.add_apply] at hsplit hinner hadd
    dsimp only [g]
    rw [hsplit, hinner, hadd, integral_const_mul, integral_const_mul,
      integral_lp_power, integral_lp_power, integral_const]
    simp only [smul_eq_mul, V, Measure.real]; ring
  rw [hig] at hi
  apply le_trans _ hi
  apply EReal.coe_le_coe_iff.mpr
  have hval : ‖value Ω m p u‖ ≤ ‖u‖ := WithLp.norm_fst_le (ValueLp Ω m p) u.val
  have hpw := affine_power_control p hA hB (norm_nonneg (gradient Ω m p u))
    (norm_nonneg (value Ω m p u)) (hval.trans (hnorm u hu))
  have hmul := mul_le_mul_of_nonneg_left hpw (mul_nonneg H.C_nonneg hε.le)
  have hgp := Real.rpow_nonneg (norm_nonneg (gradient Ω m p u)) p.real
  have ha := mul_le_mul_of_nonneg_right habsorb hgp
  dsimp only [K] at habsorb
  dsimp only [K]
  nlinarith

/-- The full Sobolev norm is bounded on every finite energy sublevel. -/
theorem affine_energy_sublevels_bounded : AffineCoercivityExpected.Sublevels := by
  intro d m _ _ Ω p q u₀ F α C a H M
  obtain ⟨C₂, hcoerc⟩ := affine_coercive_estimate Ω p q u₀ F α C a H
  obtain ⟨A, B, hA, hB, hnorm⟩ := affine_norm_control Ω p H.bounded u₀
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨A+B*(1+(M+C₂)/(α/2)), ?_⟩
  intro u hu
  have he := (hcoerc u hu.1).trans hu.2
  have he' : α / 2 * ‖gradient Ω m p u‖ ^ p.real - C₂ ≤ M :=
    EReal.coe_le_coe_iff.mp he
  have hpw : ‖gradient Ω m p u‖ ^ p.real ≤ (M+C₂)/(α/2) :=
    (le_div_iff₀ (by linarith [H.alpha_pos])).mpr (by linarith)
  have ht : ‖gradient Ω m p u‖ ≤ 1+‖gradient Ω m p u‖ ^ p.real := by
    by_cases h : ‖gradient Ω m p u‖ ≤ 1
    · linarith [Real.rpow_nonneg (norm_nonneg (gradient Ω m p u)) p.real]
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) p.one_le
      rw [Real.rpow_one] at hh
      linarith
  have hb : ‖gradient Ω m p u‖ ≤ 1+(M+C₂)/(α/2) := by linarith
  exact (hnorm u hu.1).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hB))

/-- A finite competitor and coercivity keep the extended infimum strictly
between the two infinities. -/
theorem affine_energy_infimum_finite {d m : ℕ} [NeZero d] [NeZero m]
    (Ω : Opens (Domain d)) (p q : Exponent) (u₀ : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ) (α C : ℝ) (a : Domain d → ℝ)
    (H : CoercivityHypotheses Ω p q F α C a)
    (hc : ∃ v ∈ affineClass Ω m p u₀, ∃ e : ℝ, energy Ω m p F v = (e : EReal)) :
    ∃ I : ℝ, sInf (energy Ω m p F '' affineClass Ω m p u₀) = (I : EReal) := by
  obtain ⟨C₂, hcoerc⟩ := affine_coercive_estimate Ω p q u₀ F α C a H
  obtain ⟨v, hv, e, he⟩ := hc
  let L := sInf (energy Ω m p F '' affineClass Ω m p u₀)
  have hlo : ((-C₂ : ℝ) : EReal) ≤ L := by
    apply le_sInf
    rintro z ⟨u, hu, rfl⟩
    apply le_trans _ (hcoerc u hu)
    apply EReal.coe_le_coe_iff.mpr
    have hn := Real.rpow_nonneg (norm_nonneg (gradient Ω m p u)) p.real
    nlinarith [H.alpha_pos]
  have hhi : L ≤ (e : EReal) := by
    rw [← he]; exact sInf_le (Set.mem_image_of_mem _ hv)
  have htop : L ≠ ⊤ := ne_top_of_le_ne_top (by simp) hhi
  have hbot : L ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hlo
  exact ⟨L.toReal, (EReal.coe_toReal htop hbot).symm⟩

/-- Choose energies within 1/(n+1) of the real infimum. Coercivity puts
all chosen functions in one bounded sublevel of the full Sobolev space. -/
theorem affine_bounded_minimizing_sequence : AffineCoercivityExpected.MinimizingSequence := by
  classical
  intro d m _ _ Ω p q u₀ F α C a H hc
  obtain ⟨I, hI⟩ := affine_energy_infimum_finite Ω p q u₀ F α C a H hc
  have happ (n : ℕ) : ∃ u ∈ affineClass Ω m p u₀,
      energy Ω m p F u < ((I+1/((n:ℝ)+1) : ℝ) : EReal) := by
    have hlt : sInf (energy Ω m p F '' affineClass Ω m p u₀) <
        ((I+1/((n:ℝ)+1) : ℝ) : EReal) := by
      rw [hI]
      apply EReal.coe_lt_coe_iff.mpr
      have : 0 < 1/((n:ℝ)+1) := by positivity
      linarith
    obtain ⟨z, ⟨u, hu, rfl⟩, hz⟩ := sInf_lt_iff.mp hlt
    exact ⟨u, hu, hz⟩
  choose u hu hup using happ
  have hlo (n : ℕ) : (I : EReal) ≤ energy Ω m p F (u n) := by
    rw [← hI]; exact sInf_le (Set.mem_image_of_mem _ (hu n))
  have hupper (n : ℕ) : energy Ω m p F (u n) ≤ ((I+1 : ℝ) : EReal) := by
    apply (hup n).le.trans
    apply EReal.coe_le_coe_iff.mpr
    have hdiv : 1/((n:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  have hfinite (n : ℕ) : ∃ e : ℝ, energy Ω m p F (u n) = (e : EReal) := by
    have ht := ne_top_of_le_ne_top (EReal.coe_ne_top (I+1)) (hupper n)
    have hb := ne_bot_of_le_ne_bot (EReal.coe_ne_bot I) (hlo n)
    exact ⟨(energy Ω m p F (u n)).toReal, (EReal.coe_toReal ht hb).symm⟩
  have hbounded : Bornology.IsBounded (Set.range u) :=
    (affine_energy_sublevels_bounded Ω p q u₀ F α C a H (I+1)).subset (by
      rintro v ⟨n, rfl⟩; exact ⟨hu n, hupper n⟩)
  refine ⟨I, hI, u, hu, hfinite, hbounded, ?_⟩
  have ht : Tendsto (fun n : ℕ => I+1/((n:ℝ)+1)) atTop (𝓝 I) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := I)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (EReal.tendsto_coe.mpr ht) hlo (fun n => (hup n).le)

end VariationalNotes.Sobolev
