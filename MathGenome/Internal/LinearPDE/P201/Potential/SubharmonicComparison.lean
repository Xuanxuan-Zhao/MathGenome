import MathGenome.Internal.LinearPDE.P201Specs.Potential.SubharmonicComparison
import MathGenome.Internal.LinearPDE.P201.Potential.SubharmonicMaximum
import MathGenome.Internal.LinearPDE.P201.Potential.BallPoisson

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace P201.SubharmonicComparison
open P201Specs
open P201.SubharmonicMaximum

abbrev HasHarmonicComparison : P201Specs.SubharmonicComparison.ComparisonType :=
  @P201Specs.SubharmonicComparison.HasHarmonicComparison

theorem strong_maximum : P201Specs.SubharmonicComparison.StrongMaximumStatement := by
  intro n hn Ω u hu a ha m ham hm
  exact SubharmonicMaximum.strong_maximum hn Ω u hu.1.1 hu.1.2.1
    (SubharmonicMaximum.sphere_implies_ball hn Ω u hu.1.1 hu.1.2.1 hu.2)
    a ha m ham hm

theorem boundary_maximum : P201Specs.SubharmonicComparison.BoundaryMaximumStatement := by
  intro n hn Ω u M hb hu hboundary
  exact SubharmonicMaximum.boundary_maximum hn Ω u M hb hu.1.1 hu.1.2.1
    (SubharmonicMaximum.sphere_implies_ball hn Ω u hu.1.1 hu.1.2.1 hu.2) hboundary

/-- The signed extended integral is linear under subtraction of a bounded real
integrand, even if its value is negatively infinite. -/
theorem extendedIntegral_sub_real {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (u : Space n → EReal) (h : Space n → ℝ) (hu : AEMeasurable u μ)
    (hh : Integrable h μ) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hub : ∀ᵐ x ∂μ, u x ≤ (C : EReal)) (hhb : ∀ᵐ x ∂μ, |h x| ≤ B) :
    extendedIntegral μ (fun x => u x - (h x : EReal)) =
      extendedIntegral μ u - ((∫ x, h x ∂μ : ℝ) : EReal) := by
  let v := fun x => u x - (h x : EReal)
  have hv : AEMeasurable v μ := hu.sub hh.aemeasurable.coe_real_ereal
  have hvb : ∀ᵐ x ∂μ, v x ≤ ((C + B : ℝ) : EReal) := by
    filter_upwards [hub, hhb] with x hx hhx
    apply (EReal.sub_le_sub hx (EReal.coe_le_coe_iff.mpr (neg_le_of_abs_le hhx))).trans
    simp only [← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith
  have hi : Integrable (fun x => B + h x) μ := (integrable_const B).add hh
  have hin : ∀ᵐ x ∂μ, 0 ≤ B + h x := hhb.mono fun x hx => by
    have := neg_le_of_abs_le hx
    linarith
  have hp : (∫⁻ x, ((C + B : ℝ) - v x).toENNReal ∂μ) =
      (∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ) +
        ENNReal.ofReal (∫ x, (B + h x) ∂μ) := by
    calc
      _ = ∫⁻ x, ((C : EReal) - u x).toENNReal + ENNReal.ofReal (B + h x) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hub, hin] with x hx hhx
        have he : ((C + B : ℝ) : EReal) - v x =
            ((C : EReal) - u x) + ((B + h x : ℝ) : EReal) := by
          dsimp only [v]
          induction u x with
          | bot => simp
          | top => simp
          | coe t => simp only [← EReal.coe_sub, ← EReal.coe_add]; congr 1; ring
        rw [he, EReal.toENNReal_add ((EReal.sub_nonneg (.inl (EReal.coe_ne_top C))
            (.inl (EReal.coe_ne_bot C))).mpr hx) (EReal.coe_nonneg.mpr hhx),
          EReal.real_coe_toENNReal]
      _ = _ := by
        have hDmeas : AEMeasurable (fun x => ((C : EReal) - u x).toENNReal) μ :=
          (aemeasurable_const.sub hu).ereal_toENNReal
        rw [lintegral_add_left' hDmeas,
          ← ofReal_integral_eq_lintegral_ofReal hi hin]
  change SubharmonicMaximum.extendedIntegral μ v =
    SubharmonicMaximum.extendedIntegral μ u - ((∫ x, h x ∂μ : ℝ) : EReal)
  rw [SubharmonicMaximum.extendedIntegral_deficit μ v hv (C + B) (add_nonneg hC hB) hvb,
    hp, SubharmonicMaximum.extendedIntegral_deficit μ u hu C hC hub]
  have hie : (∫ x, (B + h x) ∂μ) = B * μ.real univ + ∫ x, h x ∂μ := by
    rw [integral_add (integrable_const B) hh, integral_const, smul_eq_mul, mul_comm B]
  have hin' : 0 ≤ ∫ x, (B + h x) ∂μ := integral_nonneg_of_ae hin
  rw [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, max_eq_left hin', hie]
  generalize (∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ) = D
  by_cases hD : D = ⊤
  · simp only [hD, EReal.coe_ennreal_top, EReal.top_add_coe, EReal.sub_top,
      EReal.bot_sub]
  · rw [← EReal.coe_ennreal_toReal hD, ← EReal.coe_add, ← EReal.coe_sub,
      ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    ring


/-- The corresponding identity for normalized averages. -/
theorem extendedAverage_sub_real {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (u : Space n → EReal) (h : Space n → ℝ) (hu : AEMeasurable u μ)
    (hh : Integrable h μ) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hub : ∀ᵐ x ∂μ, u x ≤ (C : EReal)) (hhb : ∀ᵐ x ∂μ, |h x| ≤ B) :
    extendedAverage μ (fun x => u x - (h x : EReal)) =
      extendedAverage μ u - (((μ.real univ)⁻¹ * ∫ x, h x ∂μ : ℝ) : EReal) := by
  change (((μ.real univ)⁻¹ : ℝ) : EReal) * extendedIntegral μ (fun x => u x - (h x : EReal)) =
    (((μ.real univ)⁻¹ : ℝ) : EReal) * extendedIntegral μ u - _
  rw [extendedIntegral_sub_real μ u h hu hh C B hC hB hub hhb,
    EReal.mul_sub_of_nonneg_of_ne_top
      (a := (((μ.real univ)⁻¹ : ℝ) : EReal))
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr (measureReal_nonneg)))
      (EReal.coe_ne_top _), ← EReal.coe_mul]

/-- A measurable representative of an upper semicontinuous function on an open
set. This is used only under measures supported inside that set. -/
theorem measurable_zero_extension {n : ℕ} (Ω : Domain n)
    [DecidablePred (fun x => x ∈ Ω)] (u : Space n → EReal)
    (hu : UpperSemicontinuousOn u (Ω : Set _)) :
    Measurable (fun x => if x ∈ Ω then u x else 0) := by
  classical
  apply measurable_of_restrict_of_restrict_compl Ω.isOpen.measurableSet
  · convert (upperSemicontinuousOn_iff_restrict.mpr hu).measurable using 1
    ext x
    exact ite_eq_left x.property
  · have he : ((Ω : Set _)ᶜ).domRestrict (fun x => if x ∈ Ω then u x else 0) =
        fun _ => (0 : EReal) := by
      funext x
      exact ite_eq_right x.property
    rw [he]
    exact measurable_const

/-- Subtracting a harmonic function preserves the extended ball submean
inequalities. In particular no finiteness of the negative part is needed. -/
theorem ball_submean_sub_harmonic {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (u : Space n → EReal) (h : Space n → ℝ)
    (hu : UpperSemicontinuousOn u (Ω : Set _))
    (htop : ∀ x ∈ Ω, u x ≠ ⊤)
    (hmean : HasBallSubmean Ω u) (hh : P201Specs.MeanValues.IsHarmonic Ω h) :
    HasBallSubmean Ω (fun x => u x - (h x : EReal)) := by
  classical
  intro a r hr hball
  let μ : Measure (Space n) := volume.restrict (ball a r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let U : Space n → EReal := fun x => if x ∈ Ω then u x else 0
  have hU : Measurable U := measurable_zero_extension Ω u hu
  have hUeq : u =ᵐ[μ] U := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (ite_eq_left (hball (ball_subset_closedBall hx))).symm
  have hdiff : (fun x => u x - (h x : EReal)) =ᵐ[μ] (fun x => U x - (h x : EReal)) :=
    hUeq.mono fun _ hx => congrArg (fun z => z - _) hx
  obtain ⟨C₀, hC₀⟩ := SubharmonicMaximum.compact_upper_bound Ω u hu
    htop
    (closedBall a r) (isCompact_closedBall a r) hball
  let C := max C₀ 0
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn
    (hh.1.continuousOn.mono hball)
  let B := max B₀ 0
  have hub : ∀ᵐ x ∂μ, U x ≤ (C : EReal) := by
    filter_upwards [hUeq, ae_restrict_mem measurableSet_ball] with x hx hxball
    rw [← hx]
    exact (hC₀ x (ball_subset_closedBall hxball)).trans
      (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hhb : ∀ᵐ x ∂μ, |h x| ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (show |h x| ≤ B₀ by simpa [Real.norm_eq_abs] using
      (hB₀ x (ball_subset_closedBall hx))).trans (le_max_left _ _)
  have hi : Integrable h μ :=
    ((hh.1.continuousOn.mono hball).integrableOn_compact
      (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have he := extendedAverage_sub_real μ U h hU.aemeasurable hi C B
    (le_max_right _ _) (le_max_right _ _) hub hhb
  change u a - (h a : EReal) ≤ extendedAverage μ (fun x => u x - (h x : EReal))
  rw [SubharmonicMaximum.extendedAverage_congr_ae μ _ _ hdiff, he,
    ← SubharmonicMaximum.extendedAverage_congr_ae μ u U hUeq]
  have hav : (μ.real univ)⁻¹ * ∫ x, h x ∂μ = h a := by
    simpa only [P201Specs.ballAverage, smul_eq_mul, μ,
      measureReal_restrict_apply_univ] using
        (P201.MeanValues.mean_values hn Ω h hh a r hr hball).2.symm
  rw [hav]
  exact EReal.sub_le_sub (hmean a r hr hball) le_rfl


/-- Upper semicontinuity survives subtraction of a finite continuous function. -/
theorem upperSemicontinuousOn_sub_real {n : ℕ} (S : Set (Space n))
    (u : Space n → EReal) (h : Space n → ℝ)
    (hu : UpperSemicontinuousOn u S) (hh : ContinuousOn h S) :
    UpperSemicontinuousOn (fun x => u x - (h x : EReal)) S := by
  have hc : ContinuousOn (fun x => ((-h x : ℝ) : EReal)) S :=
    continuous_coe_real_ereal.comp_continuousOn hh.neg
  simpa only [sub_eq_add_neg, EReal.coe_neg] using
    hu.add' hc.upperSemicontinuousOn (fun x _ =>
      EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)))

/-- Boundary comparison from ball submean, using the maximum principle on u-h. -/
theorem ball_implies_comparison :
    P201Specs.SubharmonicComparison.BallImpliesComparisonStatement := by
  intro n hn Ω u hu htop hmean a r hr hball h hh hcont hboundary
  let D : Domain n := ⟨ball a r, isOpen_ball⟩
  let v : Space n → EReal := fun x => u x - (h x : EReal)
  have hDΩ : (D : Set (Space n)) ⊆ (Ω : Set (Space n)) := by
    exact ball_subset_closedBall.trans hball
  have hv : UpperSemicontinuousOn v (D : Set _) :=
    upperSemicontinuousOn_sub_real D u h (hu.mono hDΩ) hh.1.continuousOn
  have hvtop : ∀ x ∈ D, v x ≠ ⊤ := by
    intro x hx
    exact EReal.add_ne_top (htop x (hDΩ hx)) (by simp)
  have hDm : HasBallSubmean D u := fun b s hs hbs => hmean b s hs (hbs.trans hDΩ)
  have hvm : HasBallSubmean D v :=
    ball_submean_sub_harmonic (by omega) D u h (hu.mono hDΩ)
      (fun x hx => htop x (hDΩ hx)) hDm hh
  have hvboundary : ∀ ζ ∈ frontier (D : Set _),
      limsup v (𝓝[D] ζ) ≤ (0 : EReal) := by
    intro ζ hζ
    have hζs : ζ ∈ sphere a r := by simpa [D, frontier_ball a hr.ne'] using hζ
    have hζc : ζ ∈ closure (ball a r) := by
      rw [closure_ball a hr.ne']
      exact sphere_subset_closedBall hζs
    have : NeBot (𝓝[ball a r] ζ) := mem_closure_iff_nhdsWithin_neBot.mp hζc
    have hlim : Tendsto (fun x => ((-h x : ℝ) : EReal))
        (𝓝[ball a r] ζ) (𝓝 ((-h ζ : ℝ) : EReal)) :=
      continuous_coe_real_ereal.continuousAt.tendsto.comp
        ((hcont ζ (sphere_subset_closedBall hζs)).mono ball_subset_closedBall).neg
    have he := hlim.limsup_eq
    have hb := EReal.limsup_add_le
      (u := u) (v := fun x => ((-h x : ℝ) : EReal)) (f := 𝓝[ball a r] ζ)
      (.inr (by rw [he]; exact EReal.coe_ne_top _))
      (.inr (by rw [he]; exact EReal.coe_ne_bot _))
    rw [he] at hb
    change limsup (fun x => u x + ((-h x : ℝ) : EReal)) (𝓝[ball a r] ζ) ≤
      limsup u (𝓝[ball a r] ζ) + ((-h ζ : ℝ) : EReal) at hb
    change limsup (fun x => u x - (h x : EReal)) (𝓝[ball a r] ζ) ≤ _
    apply (show limsup (fun x => u x - (h x : EReal)) (𝓝[ball a r] ζ) ≤
        limsup u (𝓝[ball a r] ζ) + ((-h ζ : ℝ) : EReal) by
      simpa only [Pi.add_apply, EReal.coe_neg, sub_eq_add_neg] using hb).trans
    have heq : (h ζ : EReal) + ((-h ζ : ℝ) : EReal) = 0 := by
      rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
    exact (add_le_add (hboundary ζ hζs) le_rfl).trans_eq heq
  have hvle := SubharmonicMaximum.boundary_maximum hn D v 0
    (isBounded_ball) hv hvtop hvm hvboundary
  intro x hx
  exact EReal.sub_nonpos.mp (hvle x hx)


/-- Bounded-above upper semicontinuous extended functions on a metric space
are decreasing pointwise limits of finite continuous majorants. The floor -j
also covers the identically negatively infinite function. -/
theorem exists_continuous_majorants {X : Type*} [MetricSpace X] [Nonempty X]
    (u : X → EReal) (hu : UpperSemicontinuous u) (C : ℝ) (hC : 0 ≤ C)
    (hub : ∀ x, u x ≤ (C : EReal)) :
    ∃ g : ℕ → C(X, ℝ),
      (∀ j x, u x ≤ (g j x : EReal)) ∧
      (∀ j x, g j x ≤ C) ∧
      (∀ x, Antitone (fun j => g j x)) ∧
      ∀ x, Tendsto (fun j => (g j x : EReal)) atTop (𝓝 (u x)) := by
  let f : ℕ → X → ℝ := fun j x => (max (u x) ((-(j : ℝ) : ℝ) : EReal)).toReal
  have hf (j : ℕ) (x : X) : (f j x : EReal) = max (u x) ((-(j : ℝ) : ℝ) : EReal) := by
    apply EReal.coe_toReal
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top C)
        (max_le (hub x) (EReal.coe_le_coe_iff.mpr ((neg_nonpos.mpr (Nat.cast_nonneg j)).trans hC)))
    · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
  have hfle (j : ℕ) (x : X) : f j x ≤ C := by
    apply EReal.coe_le_coe_iff.mp
    rw [hf]
    exact max_le (hub x) (EReal.coe_le_coe_iff.mpr ((neg_nonpos.mpr (Nat.cast_nonneg j)).trans hC))
  have hfb (j : ℕ) (x : X) : BddAbove (range (fun y => f j y - (j : ℝ) * dist x y)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) dist_nonneg)).trans (hfle j y)
  let G : ℕ → X → ℝ := fun j x => ⨆ y, f j y - (j : ℝ) * dist x y
  have hself (j : ℕ) (x : X) : f j x ≤ G j x := by
    simpa [G] using le_ciSup (hfb j x) x
  have hGc (j : ℕ) : Continuous (G j) := by
    apply (LipschitzWith.of_le_add_mul' (j : ℝ) ?_).continuous
    intro x z
    apply ciSup_le
    intro y
    have hzy := le_ciSup (hfb j z) y
    have htri := dist_triangle z x y
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    change f j y - (j : ℝ) * dist z y ≤ G j z at hzy
    rw [dist_comm z x] at htri
    nlinarith
  let g : ℕ → C(X, ℝ) := fun j => ⟨G j, hGc j⟩
  have hmajor (j : ℕ) (x : X) : u x ≤ (g j x : EReal) := by
    apply (le_max_left (u x) ((-(j : ℝ) : ℝ) : EReal)).trans
    rw [← hf]
    exact EReal.coe_le_coe_iff.mpr (hself j x)
  refine ⟨g, hmajor, ?_, ?_, ?_⟩
  · intro j x
    apply ciSup_le
    intro y
    exact (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) dist_nonneg)).trans (hfle j y)
  · intro x i j hij
    apply ciSup_mono (hfb i x)
    intro y
    have hfj : f j y ≤ f i y := by
      apply EReal.coe_le_coe_iff.mp
      rw [hf, hf]
      exact max_le_max_left _ (EReal.coe_le_coe_iff.mpr (neg_le_neg (by exact_mod_cast hij)))
    have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hd : 0 ≤ dist x y := dist_nonneg
    nlinarith
  · intro x
    apply tendsto_order.2
    constructor
    · intro b hb
      exact Eventually.of_forall (fun j => hb.trans_le (hmajor j x))
    · intro b hb
      obtain ⟨c, hc, hcb⟩ := EReal.exists_between_coe_real hb
      have hn := hu x (c : EReal) hc
      obtain ⟨δ, hδ, hδu⟩ := Metric.eventually_nhds_iff.mp hn
      have hn₁ : ∀ᶠ j : ℕ in atTop, -c ≤ (j : ℝ) :=
        (eventually_ge_atTop (-c)).natCast_atTop
      have hn₂ : ∀ᶠ j : ℕ in atTop, (C - c) / δ ≤ (j : ℝ) :=
        (eventually_ge_atTop ((C - c) / δ)).natCast_atTop
      filter_upwards [hn₁, hn₂] with j hj₁ hj₂
      apply lt_of_le_of_lt (b := (c : EReal)) _ hcb
      apply EReal.coe_le_coe_iff.mpr
      apply ciSup_le
      intro y
      by_cases hxy : dist y x < δ
      · have hfy : f j y ≤ c := by
          apply EReal.coe_le_coe_iff.mp
          rw [hf]
          exact max_le (hδu hxy).le (EReal.coe_le_coe_iff.mpr (by linarith))
        exact (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) dist_nonneg)).trans hfy
      · have hy : δ ≤ dist x y := by simpa [dist_comm] using le_of_not_gt hxy
        have hjδ : C - c ≤ (j : ℝ) * δ := (div_le_iff₀ hδ).mp hj₂
        have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hy hj
        have hfy := hfle j y
        linarith


/-- Monotone convergence for bounded-above signed extended averages, in the
form needed for passing submean inequalities to decreasing majorants. -/
theorem le_extendedAverage_of_antitone_majorants {n : ℕ}
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (hμ : 0 < μ.real univ)
    (u : Space n → EReal) (hu : AEMeasurable u μ)
    (f : ℕ → Space n → ℝ) (hf : ∀ j, AEMeasurable (f j) μ)
    (C m : ℝ) (hC : 0 ≤ C) (hm : m ≤ C)
    (hub : ∀ᵐ x ∂μ, u x ≤ (C : EReal))
    (hfb : ∀ j, ∀ᵐ x ∂μ, f j x ≤ C)
    (hanti : ∀ᵐ x ∂μ, Antitone (fun j => f j x))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => (f j x : EReal)) atTop (𝓝 (u x)))
    (hmean : ∀ j, (m : EReal) ≤ extendedAverage μ (fun x => (f j x : EReal))) :
    (m : EReal) ≤ extendedAverage μ u := by
  apply (le_extendedAverage_iff_deficit μ hμ u hu C m hC hm hub).mpr
  let d : ℕ → Space n → ℝ≥0∞ := fun j x => ((C : EReal) - (f j x : EReal)).toENNReal
  have hd (j : ℕ) : AEMeasurable (d j) μ :=
    (aemeasurable_const.sub (hf j).coe_real_ereal).ereal_toENNReal
  have hdmono : ∀ᵐ x ∂μ, Monotone (fun j => d j x) := by
    filter_upwards [hanti] with x hx
    intro i j hij
    exact EReal.toENNReal_le_toENNReal
      (EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr (hx hij)))
  have hdlim : ∀ᵐ x ∂μ, Tendsto (fun j => d j x) atTop
      (𝓝 (((C : EReal) - u x).toENNReal)) := by
    filter_upwards [hlim] with x hx
    have hc : ContinuousAt (fun z : EReal => ((C : EReal) - z).toENNReal) (u x) := by
      have ha := EReal.continuousAt_add
        (p := ((C : EReal), -u x))
        (.inl (EReal.coe_ne_top C)) (.inl (EReal.coe_ne_bot C))
      have hp : ContinuousAt (fun z : EReal => ((C : EReal), -z)) (u x) :=
        continuousAt_const.prodMk continuousAt_id.neg
      simpa only [sub_eq_add_neg, Function.comp_def] using
        EReal.continuous_toENNReal.continuousAt.comp
          (f := fun z : EReal => (C : EReal) + -z) (x := u x)
          (ha.comp (f := fun z : EReal => ((C : EReal), -z)) (x := u x) hp)
    exact hc.tendsto.comp hx
  have hl := lintegral_tendsto_of_tendsto_of_monotone hd hdmono hdlim
  apply le_of_tendsto' hl
  intro j
  exact (le_extendedAverage_iff_deficit μ hμ (fun x => (f j x : EReal))
    (hf j).coe_real_ereal C m hC hm
      ((hfb j).mono fun x hx => EReal.coe_le_coe_iff.mpr hx)).mp (hmean j)


/-- Continuous-data Poisson solutions majorize u. Decreasing continuous
boundary majorants and the extended monotone convergence lemma then recover
the original spherical submean inequality. -/
theorem comparison_implies_sphere :
    P201Specs.SubharmonicComparison.ComparisonImpliesSphereStatement := by
  classical
  intro n hn Ω u hu htop hcomp a r hr hball
  have haΩ := hball (mem_closedBall_self hr.le)
  by_cases habot : u a = ⊥
  · simp [habot]
  let m : ℝ := (u a).toReal
  have ham : u a = (m : EReal) := (EReal.coe_toReal (htop a haΩ) habot).symm
  obtain ⟨C₀, hC₀⟩ := compact_upper_bound Ω u hu htop (closedBall a r)
    (isCompact_closedBall a r) hball
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (x : Space n) (hx : x ∈ closedBall a r) : u x ≤ (C : EReal) :=
    (hC₀ x hx).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hm : m ≤ C := EReal.coe_le_coe_iff.mp (ham ▸ hbound a (mem_closedBall_self hr.le))
  have : NeZero n := ⟨by omega⟩
  have : Nonempty (sphere a r) := (NormedSpace.sphere_nonempty.mpr hr.le).coe_sort
  have hus : UpperSemicontinuous (fun ζ : sphere a r => u ζ) :=
    upperSemicontinuousOn_iff_restrict.mpr
      (hu.mono (sphere_subset_closedBall.trans hball))
  obtain ⟨g, hgmajor, hgbound, hganti, hglim⟩ := exists_continuous_majorants
    (fun ζ : sphere a r => u ζ) hus C hC
    (fun ζ => hbound ζ (sphere_subset_closedBall ζ.property))
  let μ := sphereSurface a r
  have hμ : 0 < μ.real univ := by
    rw [P201.sphereSurfaceMass a r hr.le]
    exact mul_pos (P201.MeanValues.omega_pos (by omega)) (pow_pos hr _)
  let U : Space n → EReal := fun x => if x ∈ Ω then u x else 0
  have hU : Measurable U := measurable_zero_extension Ω u hu
  have hUeq : u =ᵐ[μ] U := by
    filter_upwards [SubharmonicMaximum.sphereSurface_ae_mem a r hr.le] with x hx
    exact (ite_eq_left (hball (sphere_subset_closedBall hx))).symm
  let f : ℕ → Space n → ℝ := fun j => BallPoisson.boundaryValue a r (g j)
  have hfi (j : ℕ) : Integrable (f j) μ :=
    BallPoisson.sphereSurface_integrable_of_continuousOn hr
      (BallPoisson.boundaryValue_continuousOn a r (g j))
  change u a ≤ extendedAverage μ u
  rw [ham, extendedAverage_congr_ae μ u U hUeq]
  apply le_extendedAverage_of_antitone_majorants μ hμ U hU.aemeasurable f
    (fun j => (hfi j).aemeasurable) C m hC hm
  · filter_upwards [hUeq, SubharmonicMaximum.sphereSurface_ae_mem a r hr.le] with x hx hxs
    rw [← hx]
    exact hbound x (sphere_subset_closedBall hxs)
  · intro j
    filter_upwards [SubharmonicMaximum.sphereSurface_ae_mem a r hr.le] with x hx
    simpa only [f, BallPoisson.boundaryValue_coe a r (g j) ⟨x, hx⟩] using hgbound j ⟨x, hx⟩
  · filter_upwards [SubharmonicMaximum.sphereSurface_ae_mem a r hr.le] with x hx
    simpa only [f, BallPoisson.boundaryValue_coe a r _ ⟨x, hx⟩] using hganti ⟨x, hx⟩
  · filter_upwards [hUeq, SubharmonicMaximum.sphereSurface_ae_mem a r hr.le] with x hx hxs
    rw [← hx]
    simpa only [f, BallPoisson.boundaryValue_coe a r _ ⟨x, hxs⟩] using hglim ⟨x, hxs⟩
  · intro j
    let H := BallPoisson.poissonExtension a r (g j)
    have hH := BallPoisson.continuous_extension hn a r hr (g j)
    have hboundary : ∀ ζ ∈ sphere a r,
        limsup u (𝓝[ball a r] ζ) ≤ (H ζ : EReal) := by
      intro ζ hζ
      have husζ : UpperSemicontinuousWithinAt u (ball a r) ζ :=
        (hu ζ (hball (sphere_subset_closedBall hζ))).mono
          (ball_subset_closedBall.trans hball)
      have hle : limsup u (𝓝[ball a r] ζ) ≤ u ζ := husζ.limsup_le
      have htrace : H ζ = g j ⟨ζ, hζ⟩ := hH.2 ⟨ζ, hζ⟩
      rw [htrace]
      exact hle.trans (hgmajor j ⟨ζ, hζ⟩)
    have hcenter := hcomp a r hr hball H
      (BallPoisson.poissonExtension_harmonic hn a hr (g j)) hH.1 hboundary
      a (mem_ball_self hr)
    change u a ≤ ((BallPoisson.poissonExtension a r (g j) a : ℝ) : EReal) at hcenter
    rw [BallPoisson.poissonExtension_interior a r (g j) (mem_ball_self hr),
      BallPoisson.poissonIntegral_center hn a hr (g j)] at hcenter
    change (m : EReal) ≤ P201Specs.SubharmonicMaximum.extendedAverage μ
      (fun x => (f j x : EReal))
    rw [real_average_bridge μ (f j) (hfi j), ← ham]
    exact hcenter

/-- The complete three-way equivalence under precisely the source's
admissibility hypotheses. -/
theorem equivalence : P201Specs.SubharmonicComparison.EquivalenceStatement := by
  intro n hn Ω u hu
  have hsb := sphere_implies_ball hn Ω u hu.1 hu.2.1
  have hbc := ball_implies_comparison hn Ω u hu.1 hu.2.1
  have hcs := comparison_implies_sphere hn Ω u hu.1 hu.2.1
  exact ⟨⟨hsb, fun h => hcs (hbc h)⟩, ⟨fun h => hbc (hsb h), hcs⟩⟩

/-- The C² characterization for all three equivalent formulations. -/
theorem smooth_criterion : P201Specs.SubharmonicComparison.SmoothCriterionStatement := by
  intro n hn Ω u hu
  have hadm := real_admissible Ω u hu.continuousOn
  have heq := equivalence hn Ω (fun x => (u x : EReal)) hadm
  have hΔ := smooth_sphere_criterion hn Ω u hu
  have hbridge := (continuous_submean_bridge hn Ω u hu.continuousOn).1
  have hsp := hbridge.trans hΔ
  exact ⟨hsp, smooth_extended_ball_criterion hn Ω u hu,
    heq.2.symm.trans hsp, smooth_subharmonic_criterion hn Ω u hu⟩

end P201.SubharmonicComparison
