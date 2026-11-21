import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.UpcrossingInequality
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.FixedInputConditionalUI
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.Vitali
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.SubmartingaleAEConvergence
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.LevyDownward

open MeasureTheory Filter
open scoped MeasureTheory Topology ENNReal NNReal

universe u
namespace P207

/-- Reversing the order of pairs and negating the path exchanges the two levels. -/
theorem upcrossingPairs_reverse {x : ℕ → ℝ} {a b : ℝ} {N k : ℕ}
    (h : UpcrossingPairs x a b N k) :
    UpcrossingPairs (fun i => -x (N - i)) (-b) (-a) N k := by
  obtain ⟨s, t, hp, ho⟩ := h
  refine ⟨fun j => N - t j.rev, fun j => N - s j.rev, ?_, ?_⟩
  · intro j
    obtain ⟨hst, htN, hsa, hbt⟩ := hp j.rev
    refine ⟨?_, Nat.sub_le _ _, ?_, ?_⟩
    · change N - t j.rev < N - s j.rev
      omega
    · have heq : N - (N - t j.rev) = t j.rev := by omega
      simpa only [heq] using neg_le_neg hbt
    · have heq : N - (N - s j.rev) = s j.rev := by omega
      simpa only [heq] using neg_le_neg hsa
  · intro i j hij
    have hji : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
    have hsep := ho _ _ hji
    have hi := hp i.rev
    have hj := hp j.rev
    change N - s i.rev < N - t j.rev
    omega

/-- The endpoint-inclusive greedy count is invariant under reversal and negation. -/
theorem greedyUpcrossings_reverse (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) (hab : a < b) :
    greedyUpcrossings (fun i => -x (N - i)) (-b) (-a) N =
      greedyUpcrossings x a b N := by
  apply Nat.le_antisymm
  · have h := upcrossingPairs_reverse
      (greedy_upcrossingPairs (x := fun i => -x (N - i)) (n := N) (neg_lt_neg hab))
    obtain ⟨s, t, hp, ho⟩ := h
    apply upcrossingPairs_le_greedy hab
    refine ⟨s, t, ?_, ho⟩
    intro j
    obtain ⟨hst, ht, hs, hb⟩ := hp j
    have hsN : N - (N - s j) = s j := by omega
    have htN : N - (N - t j) = t j := by omega
    simpa only [hsN, htN, neg_neg] using And.intro hst (And.intro ht (And.intro hs hb))
  · exact upcrossingPairs_le_greedy (neg_lt_neg hab)
      (upcrossingPairs_reverse (greedy_upcrossingPairs hab))

/-- Freeze the finite reversed filtration after its horizon. -/
def reverseFiltration {Ω : Type u} [m : MeasurableSpace Ω]
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hle : ∀ n, G n ≤ m)
    (N : ℕ) : Filtration ℕ m where
  seq k := G (N - k)
  mono' _ _ hij := hG (Nat.sub_le_sub_left hij N)
  le' _ := hle _

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- A uniform finite-horizon bound, obtained from a genuine increasing filtration. -/
theorem reverse_condExp_upcrossing_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hle : ∀ n, G n ≤ m)
    (Y : Ω → ℝ) (_hY : Integrable Y μ) (a b : ℝ) (hab : a < b) (N : ℕ) :
    (b - a) * (∫ ω, (greedyUpcrossings (fun n => μ[Y | G n] ω) a b N : ℝ) ∂μ) ≤
      (∫ ω, ‖Y ω‖ ∂μ) + |b| := by
  let F := reverseFiltration G hG hle N
  let Z : ℕ → Ω → ℝ := fun k ω => -μ[Y | G (N - k)] ω
  have hZ : MeasureTheory.Martingale Z F μ := (martingale_condExp Y F μ).neg
  have hsource : IsSubmartingale Z F μ :=
    (submartingale_iff_library μ F Z).mpr hZ.submartingale
  have hbnd := (upcrossing_inequality μ F Z hsource (-b) (-a) (neg_lt_neg hab) N).1
  have hc (ω : Ω) : greedyUpcrossings (fun k => Z k ω) (-b) (-a) N =
      greedyUpcrossings (fun n => μ[Y | G n] ω) a b N :=
    greedyUpcrossings_reverse (fun n => μ[Y | G n] ω) a b N hab
  have hpos : 0 ≤ ∫ ω, (Z 0 ω - -b)⁺ ∂μ :=
    integral_nonneg fun _ => posPart_nonneg _
  have hterm : (∫ ω, (Z N ω - -b)⁺ ∂μ) ≤ (∫ ω, ‖Y ω‖ ∂μ) + |b| := by
    have heq : (fun ω => (Z N ω - -b)⁺) =
        fun ω => (-μ[Y | G 0] ω + b)⁺ := by
      funext ω
      simp [Z, sub_neg_eq_add]
    rw [heq]
    calc
      _ ≤ ∫ ω, ‖μ[Y | G 0] ω‖ + |b| ∂μ := by
        apply integral_mono (integrable_condExp.neg.add (integrable_const b)).pos_part
          (integrable_condExp.norm.add (integrable_const |b|))
        intro ω
        change (-μ[Y | G 0] ω + b)⁺ ≤ ‖μ[Y | G 0] ω‖ + |b|
        apply max_le _ (add_nonneg (norm_nonneg _) (abs_nonneg _))
        simpa only [Real.norm_eq_abs] using
          add_le_add (neg_le_abs (μ[Y | G 0] ω)) (le_abs_self b)
      _ = (∫ ω, ‖μ[Y | G 0] ω‖ ∂μ) + |b| := by
        rw [integral_add integrable_condExp.norm (integrable_const _)]; simp
      _ ≤ _ := add_le_add (integral_norm_condExp_le (μ := μ) (m := G 0) Y) le_rfl
  simp only [hc] at hbnd
  have heq : -a - -b = b - a := by ring
  rw [heq] at hbnd
  linarith

/-- Uniform bounds for expected finite counts imply finite total crossings a.e. -/
theorem upcrossings_ae_finite_of_integral_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (a b C : ℝ) (hab : a < b)
    (hbound : ∀ N, (∫ ω, (greedyUpcrossings (fun n => X n ω) a b N : ℝ) ∂μ) ≤ C) :
    ∀ᵐ ω ∂μ, upcrossings a b X ω < ∞ := by
  have ha : StronglyAdapted (Filtration.const ℕ m le_rfl) X :=
    fun n => (hX n).stronglyMeasurable
  apply ae_lt_top (ha.measurable_upcrossings hab)
  have hi : (∫⁻ ω, upcrossings a b X ω ∂μ) ≤ ENNReal.ofReal C := by
    unfold upcrossings
    rw [lintegral_iSup']
    · refine iSup_le fun N => ?_
      cases N with
      | zero => simp [upcrossingsBefore_zero]
      | succ N =>
        rw [show (fun ω => (upcrossingsBefore a b X (N + 1) ω : ℝ≥0∞)) =
            fun ω => ((upcrossingsBefore a b X (N + 1) ω : ℝ≥0) : ℝ≥0∞) from rfl,
          lintegral_coe_eq_integral _ (ha.integrable_upcrossingsBefore hab)]
        apply ENNReal.ofReal_le_ofReal
        simp only [NNReal.coe_natCast]
        have hh := hbound N
        simp_rw [greedyUpcrossings_eq_process_upcrossingsBefore Ω X a b N] at hh
        exact hh
    · exact fun N => measurable_from_top.comp_aemeasurable
        (ha.measurable_upcrossingsBefore hab).aemeasurable
    · filter_upwards with ω N M hNM
      change (upcrossingsBefore a b X N ω : ℝ≥0∞) ≤
        (upcrossingsBefore a b X M ω : ℝ≥0∞)
      exact_mod_cast upcrossingsBefore_mono (f := X) hab hNM ω
  exact (hi.trans_lt ENNReal.ofReal_lt_top).ne

/-- The conditional-expectation sequence converges a.e. to some finite real value. -/
theorem reverse_condExp_exists_ae_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hle : ∀ n, G n ≤ m)
    (Y : Ω → ℝ) (hY : Integrable Y μ) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n => μ[Y | G n] ω) atTop (𝓝 c) := by
  let X : ℕ → Ω → ℝ := fun n => μ[Y | G n]
  have hm (n : ℕ) : Measurable (X n) :=
    stronglyMeasurable_condExp.measurable.mono (hle n) le_rfl
  have hu : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings a b X ω < ∞ := by
    simp only [ae_all_iff, eventually_imp_distrib_left]
    intro a b hab
    have hab' : (a : ℝ) < b := Rat.cast_lt.mpr hab
    apply upcrossings_ae_finite_of_integral_bound μ X hm a b
      (((∫ ω, ‖Y ω‖ ∂μ) + |(b : ℝ)|) / ((b : ℝ) - a)) hab'
    intro N
    apply (le_div_iff₀ (sub_pos.mpr hab')).mpr
    simpa only [mul_comm] using reverse_condExp_upcrossing_bound μ G hG hle Y hY a b hab' N
  obtain ⟨R, hR⟩ : ∃ R : ℝ≥0, eLpNorm Y 1 μ = R :=
    ⟨(eLpNorm Y 1 μ).toNNReal, (ENNReal.coe_toNNReal (memLp_one_iff_integrable.mpr hY).ne).symm⟩
  have hbdd : ∀ n, eLpNorm (X n) 1 μ ≤ R := by
    intro n
    rw [← hR]
    exact eLpNorm_condExp_le_eLpNorm Y le_rfl
  filter_upwards [hu, ae_bdd_liminf_atTop_of_eLpNorm_bdd one_ne_zero hbdd] with ω hω hlim
  exact tendsto_of_upcrossings_lt_top hlim hω

omit m in
/-- The real limsup is measurable for every earlier sigma-algebra, hence for
their literal intersection. The real-valued limsup also defines a value on
the exceptional paths, without completing any sigma-algebra. -/
theorem measurable_reverse_limsup
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable[G n] (X n)) :
    Measurable[⨅ n, G n] (fun ω => limsup (fun n => X n ω) atTop) := by
  apply Measurable.of_comap_le
  apply le_iInf
  intro k
  apply Measurable.comap_le
  have hm : Measurable[G k] (fun ω => limsup (fun n => X (n + k) ω) atTop) :=
    Measurable.limsup (fun n => (hX (n + k)).mono (hG (Nat.le_add_left k n)) le_rfl)
  have heq : (fun ω => limsup (fun n => X (n + k) ω) atTop) =
      fun ω => limsup (fun n => X n ω) atTop := by
    funext ω
    change limsup ((fun n => X n ω) ∘ (fun n => n + k)) atTop = _
    rw [limsup_comp, map_add_atTop_eq_nat]
  rwa [heq] at hm

/-- Lévy's downward theorem on the original probability space. -/
theorem levy_downward : LevyDownwardSpec.levy_downward.{u} := by
  intro Ω m μ _ G hG hle Y hY
  let X : ℕ → Ω → ℝ := fun n => μ[Y | G n]
  let Z : Ω → ℝ := fun ω => limsup (fun n => X n ω) atTop
  have hXint (n : ℕ) : Integrable (X n) μ := integrable_condExp
  have hZmeas : Measurable[⨅ n, G n] Z :=
    measurable_reverse_limsup G hG X (fun _ => stronglyMeasurable_condExp.measurable)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [reverse_condExp_exists_ae_tendsto μ G hG hle Y hY] with ω hω
    obtain ⟨c, hc⟩ := hω
    have heq : Z ω = c := hc.limsup_eq
    rwa [heq]
  have hui := Martingale.sourceUniformIntegrable_condExp μ Y hY G hle
  obtain ⟨hZint, _, hL1⟩ := Martingale.vitali_forward μ X Z hXint
    (tendstoInMeasure_of_tendsto_ae (fun n => (hXint n).aestronglyMeasurable) hlim) hui
  have heLp (n : ℕ) : eLpNorm (X n - Z) 1 μ =
      ENNReal.ofReal (∫ ω, ‖X n ω - Z ω‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hXint n).sub hZint).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hXint n).sub hZint)]
    rfl
  have hLp : Tendsto (fun n => eLpNorm (X n - Z) 1 μ) atTop (𝓝 0) := by
    simpa only [heLp, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hL1
  have hinter : (⨅ n, G n) ≤ m := (iInf_le G 0).trans (hle 0)
  have htest (s : Set Ω) (hs : MeasurableSet[⨅ n, G n] s) :
      ∫ ω in s, Z ω ∂μ = ∫ ω in s, Y ω ∂μ := by
    have ht := tendsto_setIntegral_of_L1' Z (Eventually.of_forall hXint) hLp s
    have heq (n : ℕ) : ∫ ω in s, X n ω ∂μ = ∫ ω in s, Y ω ∂μ :=
      setIntegral_condExp (hle n) hY ((iInf_le G n) s hs)
    have ht' : Tendsto (fun n => ∫ ω in s, X n ω ∂μ) atTop (𝓝 (∫ ω in s, Y ω ∂μ)) := by
      simpa only [heq] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ ω in s, Y ω ∂μ) atTop
          (𝓝 (∫ ω in s, Y ω ∂μ)))
    exact tendsto_nhds_unique ht ht'
  have hident : Z =ᵐ[μ] μ[Y | ⨅ n, G n] :=
    ae_eq_condExp_of_forall_setIntegral_eq hinter hY
      (fun s _ _ => hZint.integrableOn) (fun s hs _ => htest s hs)
      hZmeas.stronglyMeasurable.aestronglyMeasurable
  refine ⟨stronglyMeasurable_condExp.measurable, ?_, ?_⟩
  · filter_upwards [hlim, hident] with ω hω hid
    rwa [hid] at hω
  · have heq (n : ℕ) : (∫ ω, ‖X n ω - Z ω‖ ∂μ) =
        ∫ ω, ‖μ[Y | G n] ω - μ[Y | ⨅ n, G n] ω‖ ∂μ :=
      integral_congr_ae (hident.mono fun ω hω => by
        change ‖X n ω - Z ω‖ = ‖μ[Y | G n] ω - μ[Y | ⨅ n, G n] ω‖
        rw [hω])
    simpa only [heq] using hL1

end P207
