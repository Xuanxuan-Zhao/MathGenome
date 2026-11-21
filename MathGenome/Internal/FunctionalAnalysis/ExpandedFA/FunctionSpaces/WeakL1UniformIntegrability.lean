import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.WeakL1UniformIntegrability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

open MeasureTheory Filter
open scoped ENNReal Topology

universe u v
noncomputable section

namespace ExpandedFA.FunctionSpaces

open WeakL1UniformIntegrabilitySpec

/-- Endpoint scalar-linear duality identifies the weak convergence tests. -/
theorem weak_l1_convergence_tests : WeakConvergenceTests.{u} := by
  intro X 𝕜 _ _ μ _ f g
  constructor
  · intro hf h
    have heq (F : Lp 𝕜 1 μ) :
        lpIntegralPairing μ 1 ∞ h F = ∫ x, F x * h x ∂μ :=
      (lp_pairing_integral μ 1 ∞ h F).2
    simpa only [heq] using hf (lpIntegralPairing μ 1 ∞ h)
  · intro hf L
    obtain ⟨h, hh, _⟩ := lp_one_infinity_duality_sigmaFinite μ L
    simpa only [(hh.1 _).2] using hf h

/-- Centering is valid in the ordinary continuous scalar-linear dual. -/
theorem weak_l1_centering : Centering.{u} := by
  intro X 𝕜 _ _ μ f g
  constructor
  · intro hf L
    simpa only [map_sub, map_zero, sub_self] using (hf L).sub_const (L g)
  · intro hf L
    have h := (hf L).add_const (L g)
    simpa only [map_sub, map_zero, sub_add_cancel, zero_add] using h

/-- A pointwise norm-integral over any measurable set is independent of
which ordinary almost-everywhere representative was selected. -/
theorem norm_setIntegral_congr_ae {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f g : X → 𝕜}
    (h : f =ᵐ[μ] g) (A : Set X) :
    (∫ x in A, ‖f x‖ ∂μ) = ∫ x in A, ‖g x‖ ∂μ :=
  integral_congr_ae ((ae_restrict_of_ae h).mono fun _ hx => congrArg norm hx)

theorem weak_l1_controls_ae : ControlsAeInvariant.{u,v} := by
  intro X ι 𝕜 _ _ μ f g hfg
  have hs : SmallSetControl μ f ↔ SmallSetControl μ g := by
    unfold SmallSetControl
    simp_rw [← norm_setIntegral_congr_ae (hfg _) _]
  have ht : TailControl μ f ↔ TailControl μ g := by
    unfold TailControl
    simp_rw [← norm_setIntegral_congr_ae (hfg _) _]
  exact and_congr hs ht

/-- Triangle inequality on a restricted measure, used to restore the limit. -/
theorem norm_setIntegral_add_le {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f g : X → 𝕜}
    (hf : Integrable f μ) (hg : Integrable g μ) (A : Set X) :
    (∫ x in A, ‖f x + g x‖ ∂μ) ≤
      (∫ x in A, ‖f x‖ ∂μ) + ∫ x in A, ‖g x‖ ∂μ := by
  calc
    _ ≤ ∫ x in A, ‖f x‖ + ‖g x‖ ∂μ :=
      integral_mono (hf.integrableOn.add hg.integrableOn).norm
        (hf.integrableOn.norm.add hg.integrableOn.norm) (fun _ => norm_add_le _ _)
    _ = _ := integral_add hf.integrableOn.norm hg.integrableOn.norm

/-- Both integral controls are preserved under addition. -/
theorem weak_l1_controls_add : ControlsAdd.{u,v} := by
  intro X ι 𝕜 _ _ μ f g hf hg hfc hgc
  constructor
  · intro ε hε
    obtain ⟨δf, hδf, hsf⟩ := hfc.1 (ε / 2) (by positivity)
    obtain ⟨δg, hδg, hsg⟩ := hgc.1 (ε / 2) (by positivity)
    refine ⟨min δf δg, lt_min hδf hδg, fun A hA hμA i => ?_⟩
    have hAf := hμA.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    have hAg := hμA.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    have hb := add_lt_add (hsf A hA hAf i) (hsg A hA hAg i)
    exact (norm_setIntegral_add_le (hf i) (hg i) A).trans_lt (by linarith)
  · intro ε hε
    obtain ⟨F, hF, hμF, htf⟩ := hfc.2 (ε / 2) (by positivity)
    obtain ⟨G, hG, hμG, htg⟩ := hgc.2 (ε / 2) (by positivity)
    refine ⟨F ∪ G, hF.union hG, (measure_union_le F G).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hμF, hμG⟩), fun i => ?_⟩
    have hfi : (∫ x in (F ∪ G)ᶜ, ‖f i x‖ ∂μ) ≤ ∫ x in Fᶜ, ‖f i x‖ ∂μ :=
      setIntegral_mono_set (hf i).norm.integrableOn
        (ae_of_all _ (fun _ => norm_nonneg _))
        (ae_of_all _ (fun _ hx => fun h => hx (Or.inl h)))
    have hgi : (∫ x in (F ∪ G)ᶜ, ‖g i x‖ ∂μ) ≤ ∫ x in Gᶜ, ‖g i x‖ ∂μ :=
      setIntegral_mono_set (hg i).norm.integrableOn
        (ae_of_all _ (fun _ => norm_nonneg _))
        (ae_of_all _ (fun _ hx => fun h => hx (Or.inr h)))
    exact (norm_setIntegral_add_le (hf i) (hg i) _).trans_lt (by
      have := htf i
      have := htg i
      linarith)

/-- At p=1 the eLp seminorm is literally the nonnegative norm integral. -/
theorem eLpNorm_one_eq_ofReal_integral_norm {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f : X → 𝕜}
    (hf : Integrable f μ) :
    eLpNorm f 1 μ = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ofReal_integral_norm_eq_lintegral_enorm hf]

/-- Finite-family controls use neither finiteness nor sigma-finiteness of μ. -/
theorem weak_l1_finite_family_controls : FiniteFamilyControls.{u,v} := by
  intro X ι 𝕜 _ _ _ μ f hf
  constructor
  · intro ε hε
    have hui : UnifIntegrable f 1 μ :=
      unifIntegrable_finite le_rfl (by simp) (fun i => (memLp_one_iff_integrable.mpr (hf i)))
    obtain ⟨δ, hδ, hs⟩ := unifIntegrable_iff'.mp hui
      (ENNReal.ofReal (ε / 2)) (by positivity)
    obtain ⟨δ', hδ', hδ'δ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
    refine ⟨(δ' : ℝ), ENNReal.coe_pos.mp hδ', fun A hA hμA i => ?_⟩
    rw [ENNReal.ofReal_coe_nnreal] at hμA
    have hb := hs i A hA (hμA.le.trans hδ'δ.le)
    rw [eLpNorm_one_eq_ofReal_integral_norm (hf i).integrableOn] at hb
    have hi := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ ε / 2)).mp hb
    linarith
  · intro ε hε
    have hut : UnifTight f 1 μ :=
      unifTight_finite (by simp) (fun i => (memLp_one_iff_integrable.mpr (hf i)))
    obtain ⟨F, hF, hμF, htail⟩ := hut.exists_measurableSet_indicator
      (show ENNReal.ofReal (ε / 2) ≠ 0 by positivity)
    refine ⟨F, hF, hμF, fun i => ?_⟩
    have hb := htail i
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hF.compl.nullMeasurableSet,
      eLpNorm_one_eq_ofReal_integral_norm (hf i).integrableOn] at hb
    have hi := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ ε / 2)).mp hb
    linarith

/-- Raw bounded tests, including the measurable phase functions in a gliding
hump construction, define ordinary L-infinity classes. -/
theorem weak_l1_bounded_tests : BoundedTests.{u} := by
  intro X 𝕜 _ _ μ _ f g hf h hm hb
  have hLp : MemLp h ∞ μ := memLp_top_of_bound hm 1 hb
  have heq (F : Lp 𝕜 1 μ) :
      (∫ x, F x * hLp.toLp h x ∂μ) = ∫ x, F x * h x ∂μ :=
    integral_congr_ae (Filter.EventuallyEq.rfl.mul hLp.coeFn_toLp)
  simpa only [heq] using (weak_l1_convergence_tests μ f g).mp hf (hLp.toLp h)

/-- No alternative weak topology is used in the specification. -/
theorem weak_l1_native_weak_convergence : NativeWeakConvergence.{u} := by
  intro X 𝕜 _ _ μ f g
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing 𝕜 (Lp 𝕜 1 μ)).flip)
    (separatingDual_iff_injective.mp (inferInstance : SeparatingDual 𝕜 (Lp 𝕜 1 μ)))).symm

/-- Controls transfer along arbitrary reindexing, in particular from a
one-element family to a constant sequence. -/
theorem l1_controls_comp {X : Type u} {ι : Type v} {κ : Type*} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f : ι → X → 𝕜}
    (hf : Controls μ f) (j : κ → ι) : Controls μ (fun k => f (j k)) := by
  constructor
  · intro ε hε
    obtain ⟨δ, hδ, hs⟩ := hf.1 ε hε
    exact ⟨δ, hδ, fun A hA hμA k => hs A hA hμA (j k)⟩
  · intro ε hε
    obtain ⟨F, hF, hμF, ht⟩ := hf.2 ε hε
    exact ⟨F, hF, hμF, fun k => ht (j k)⟩

theorem weak_l1_controls_centering : CenteringControls.{u} := by
  intro X 𝕜 _ _ μ f g
  have hi (h : Lp 𝕜 1 μ) : Integrable (h : X → 𝕜) μ :=
    memLp_one_iff_integrable.mp (Lp.memLp h)
  have hc (h : Lp 𝕜 1 μ) : Controls μ (fun _ : ℕ => (h : X → 𝕜)) :=
    l1_controls_comp
      (weak_l1_finite_family_controls μ (fun _ : Unit => (h : X → 𝕜)) (fun _ => hi h))
      (fun _ => ())
  constructor
  · intro hf
    have ha := weak_l1_controls_add μ (fun n => (f n : X → 𝕜))
      (fun _ : ℕ => ((-g : Lp 𝕜 1 μ) : X → 𝕜))
      (fun n => hi (f n)) (fun _ => hi (-g)) hf (hc (-g))
    apply (weak_l1_controls_ae μ _ _ ?_).mp ha
    intro n
    filter_upwards [Lp.coeFn_sub (f n) g, Lp.coeFn_neg g] with x hx hy
    simp only [Pi.sub_apply] at hx
    simp only [Pi.neg_apply] at hy
    rw [hx, hy, sub_eq_add_neg]
  · intro hf
    have ha := weak_l1_controls_add μ
      (fun n : ℕ => ((f n - g : Lp 𝕜 1 μ) : X → 𝕜))
      (fun _ : ℕ => (g : X → 𝕜))
      (fun n => hi (f n - g)) (fun _ => hi g) hf (hc g)
    apply (weak_l1_controls_ae μ _ _ ?_).mp ha
    intro n
    filter_upwards [Lp.coeFn_sub (f n) g] with x hx
    simp only [Pi.sub_apply] at hx
    rw [hx, sub_add_cancel]

/-- Continuity from above for one integrable function. This supplies the
finite-family exclusion needed when selecting strictly increasing indices. -/
theorem integrable_norm_decreasing_sets {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f : X → 𝕜}
    (hf : Integrable f μ) (A : ℕ → Set X)
    (hA : ∀ k, MeasurableSet (A k)) (hanti : Antitone A)
    (hnull : μ (⋂ k, A k) = 0) :
    Tendsto (fun k => ∫ x in A k, ‖f x‖ ∂μ) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone hA hanti
    (show ∃ k, IntegrableOn (fun x => ‖f x‖) (A k) μ from
      ⟨0, hf.norm.integrableOn⟩)
  simpa only [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure] using h

/-- A bounded measurable multiplier gives an integrable scalar product. -/
theorem integrable_mul_unit_bounded {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f h : X → 𝕜}
    (hf : Integrable f μ) (hm : AEStronglyMeasurable h μ)
    (hb : ∀ᵐ x ∂μ, ‖h x‖ ≤ 1) : Integrable (fun x => f x * h x) μ :=
  (memLp_one_iff_integrable.mpr hf).integrable_mul (memLp_top_of_bound hm 1 hb)

/-- Subsequent changes of a unit-bounded test function on B cost at most
 twice the norm integral on B. This is the quantitative patching estimate. -/
theorem integral_mul_patch_error {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f g h : X → 𝕜}
    (hf : Integrable f μ) (hgm : AEStronglyMeasurable g μ)
    (hhm : AEStronglyMeasurable h μ)
    (hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1) (hhb : ∀ᵐ x ∂μ, ‖h x‖ ≤ 1)
    (B : Set X) (hB : MeasurableSet B)
    (heq : ∀ᵐ x ∂μ, x ∉ B → g x = h x) :
    ‖(∫ x, f x * g x ∂μ) - ∫ x, f x * h x ∂μ‖ ≤
      2 * ∫ x in B, ‖f x‖ ∂μ := by
  rw [← integral_sub (integrable_mul_unit_bounded hf hgm hgb)
    (integrable_mul_unit_bounded hf hhm hhb)]
  have hbound : ∀ᵐ x ∂μ,
      ‖f x * g x - f x * h x‖ ≤ B.indicator (fun x => 2 * ‖f x‖) x := by
    filter_upwards [hgb, hhb, heq] with x hgx hhx heqx
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← mul_sub, norm_mul]
      have hdiff : ‖g x - h x‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
      nlinarith [norm_nonneg (f x)]
    · rw [Set.indicator_of_notMem hx, heqx hx, sub_self, norm_zero]
  have hi : Integrable (B.indicator (fun x => 2 * ‖f x‖)) μ :=
    (hf.norm.const_mul 2).indicator hB
  have hb := norm_integral_le_of_norm_le hi hbound
  simpa only [integral_indicator hB, integral_const_mul] using hb

/-- Align the new patch with the integral over the unchanged region. The
zero outside contribution is included, for both real and complex scalars. -/
theorem exists_unit_phase_align : UnitPhaseAlignment := by
  intro 𝕜 _ z r hr
  by_cases hz : z = 0
  · subst z
    exact ⟨1, norm_one, by simp [abs_of_nonneg hr]⟩
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hnz : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast hn.ne'
    let c : 𝕜 := z / (‖z‖ : 𝕜)
    have hc : ‖c‖ = 1 := by
      dsimp [c]
      rw [norm_div, RCLike.norm_ofReal, abs_of_pos hn, div_self hn.ne']
    have hcz : c * (‖z‖ : 𝕜) = z := div_mul_cancel₀ _ hnz
    refine ⟨c, hc, ?_⟩
    calc
      ‖z + c * (r : 𝕜)‖ = ‖c * ((‖z‖ + r : ℝ) : 𝕜)‖ := by
        rw [RCLike.ofReal_add, mul_add, hcz]
      _ = ‖z‖ + r := by
        rw [norm_mul, hc, one_mul, RCLike.norm_ofReal,
          abs_of_nonneg (by positivity)]

/-- The conjugate phase, assigned zero at zero, is bounded by one. -/
def conjugatePhase {𝕜 : Type} [RCLike 𝕜] (z : 𝕜) : 𝕜 :=
  star z / (‖z‖ : 𝕜)

theorem conjugatePhase_norm_le {𝕜 : Type} [RCLike 𝕜] (z : 𝕜) :
    ‖conjugatePhase z‖ ≤ 1 := by
  rw [conjugatePhase, norm_div, norm_star, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg z)]
  exact div_self_le_one ‖z‖

theorem mul_conjugatePhase {𝕜 : Type} [RCLike 𝕜] (z : 𝕜) :
    z * conjugatePhase z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [hz, conjugatePhase]
  · have hn : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    rw [conjugatePhase, ← mul_div_assoc, RCLike.star_def, RCLike.mul_conj]
    rw [pow_two, mul_div_cancel_right₀ _ hn]

theorem aestronglyMeasurable_conjugatePhase {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f : X → 𝕜}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => conjugatePhase (f x)) μ :=
  hf.star.div₀ (RCLike.continuous_ofReal.comp_aestronglyMeasurable hf.norm)

/-- One patch can always align its mass with the unchanged contribution. -/
theorem exists_integral_phase_patch {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f g : X → 𝕜}
    (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ)
    (hgb : ∀ x, ‖g x‖ ≤ 1) (A : Set X) (hA : MeasurableSet A) :
    ∃ h : X → 𝕜, AEStronglyMeasurable h μ ∧ (∀ x, ‖h x‖ ≤ 1) ∧
      (∀ x, x ∉ A → h x = g x) ∧
      (∫ x in A, ‖f x‖ ∂μ) ≤ ‖∫ x, f x * h x ∂μ‖ := by
  classical
  let r : ℝ := ∫ x in A, ‖f x‖ ∂μ
  let z : 𝕜 := ∫ x in Aᶜ, f x * g x ∂μ
  obtain ⟨c, hc, halign⟩ := exists_unit_phase_align z r
    (integral_nonneg (fun _ => norm_nonneg _))
  let p : X → 𝕜 := fun x => c * conjugatePhase (f x)
  have hpm : AEStronglyMeasurable p μ :=
    aestronglyMeasurable_const.mul (aestronglyMeasurable_conjugatePhase hf.aestronglyMeasurable)
  have hpb (x : X) : ‖p x‖ ≤ 1 := by
    simpa only [p, norm_mul, hc, one_mul] using conjugatePhase_norm_le (f x)
  let h := A.piecewise p g
  have hhm : AEStronglyMeasurable h μ :=
    AEStronglyMeasurable.piecewise hA.nullMeasurableSet hpm.restrict hg.restrict
  have hhb (x : X) : ‖h x‖ ≤ 1 := by
    by_cases hx : x ∈ A
    · simpa [h, hx] using hpb x
    · simpa [h, hx] using hgb x
  refine ⟨h, hhm, hhb, fun x hx => Set.piecewise_eq_of_notMem A p g hx, ?_⟩
  have hprod (x : X) : f x * p x = c * (‖f x‖ : 𝕜) := by
    dsimp [p]
    rw [mul_left_comm, mul_conjugatePhase]
  have hi : (∫ x, f x * h x ∂μ) = c * (r : 𝕜) + z := by
    calc
      _ = ∫ x, A.piecewise (fun x => f x * p x) (fun x => f x * g x) x ∂μ := by
        congr 1
        ext x
        by_cases hx : x ∈ A <;> simp [h, hx]
      _ = (∫ x in A, f x * p x ∂μ) + ∫ x in Aᶜ, f x * g x ∂μ :=
        integral_piecewise hA
          (integrable_mul_unit_bounded hf hpm (ae_of_all _ hpb)).integrableOn
          (integrable_mul_unit_bounded hf hg (ae_of_all _ hgb)).integrableOn
      _ = c * (r : 𝕜) + z := by
        simp_rw [hprod]
        rw [integral_const_mul, integral_ofReal]
  rw [hi, add_comm, halign]
  exact le_add_of_nonneg_left (norm_nonneg z)

/-- Successive phase patches; g(n+1) is the test after patch n. -/
theorem exists_successive_phase_patches {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} (f : ℕ → X → 𝕜)
    (hf : ∀ n, Integrable (f n) μ) (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet (A n)) :
    ∃ g : ℕ → X → 𝕜,
      (∀ n, AEStronglyMeasurable (g n) μ ∧ ∀ x, ‖g n x‖ ≤ 1) ∧
      (∀ n x, x ∉ A n → g (n+1) x = g n x) ∧
      ∀ n, (∫ x in A n, ‖f n x‖ ∂μ) ≤ ‖∫ x, f n x * g (n+1) x ∂μ‖ := by
  classical
  let T := {g : X → 𝕜 // AEStronglyMeasurable g μ ∧ ∀ x, ‖g x‖ ≤ 1}
  have hs (n : ℕ) (g : T) : ∃ h : T,
      (∀ x, x ∉ A n → h.val x = g.val x) ∧
      (∫ x in A n, ‖f n x‖ ∂μ) ≤ ‖∫ x, f n x * h.val x ∂μ‖ := by
    obtain ⟨h, hm, hb, heq, hi⟩ :=
      exists_integral_phase_patch (hf n) g.property.1 g.property.2 (A n) (hA n)
    exact ⟨⟨h, hm, hb⟩, heq, hi⟩
  choose step hstep using hs
  let g : ℕ → T := fun n => Nat.rec
    ⟨(fun _ => 0), aestronglyMeasurable_const, fun _ => by simp⟩ step n
  refine ⟨fun n => (g n).val, fun n => (g n).property, ?_, ?_⟩
  · intro n
    exact (hstep n (g n)).1
  · intro n
    exact (hstep n (g n)).2

/-- Once no further patch meets x, all later tests agree at x. -/
theorem successive_patches_stable {X E : Type*} (g : ℕ → X → E) (A : ℕ → Set X)
    (hstep : ∀ n x, x ∉ A n → g (n+1) x = g n x)
    (x : X) (N : ℕ) (hno : ∀ k, N ≤ k → x ∉ A k)
    (m : ℕ) (hm : N ≤ m) : g m x = g N x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, hstep (N+d) x (hno _ (Nat.le_add_right _ _)), ih (Nat.le_add_right _ _)]

/-- The quantitative gliding-hump step. The sets need not be disjoint or
nested; eventual absence and the integral on each future union suffice. -/
theorem exists_gliding_hump_test {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} (f : ℕ → X → 𝕜)
    (hf : ∀ n, Integrable (f n) μ) (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet (A n))
    (hfinite : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ A n)
    (ε : ℝ) (hmass : ∀ n, ε ≤ ∫ x in A n, ‖f n x‖ ∂μ)
    (hfuture : ∀ n, (∫ x in ⋃ k, ⋃ (_ : n < k), A k, ‖f n x‖ ∂μ) < ε / 8) :
    ∃ h : X → 𝕜, AEStronglyMeasurable h μ ∧
      (∀ᵐ x ∂μ, ‖h x‖ ≤ 1) ∧
      ∀ n, 3 * ε / 4 < ‖∫ x, f n x * h x ∂μ‖ := by
  obtain ⟨g, hgm, hstep, hgi⟩ := exists_successive_phase_patches f hf A hA
  have hconv : ∀ᵐ x ∂μ, ∃ l : 𝕜, Tendsto (fun n => g n x) atTop (𝓝 l) := by
    filter_upwards [hfinite] with x hx
    obtain ⟨N, hN⟩ := eventually_atTop.1 hx
    refine ⟨g N x, tendsto_const_nhds.congr' ?_⟩
    exact (eventually_ge_atTop N).mono fun m hm =>
      (successive_patches_stable g A hstep x N hN m hm).symm
  obtain ⟨h, hhm, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae
    (fun n => (hgm n).1) hconv
  have hhb : ∀ᵐ x ∂μ, ‖h x‖ ≤ 1 := by
    filter_upwards [hlim] with x hx
    exact le_of_tendsto hx.norm (Eventually.of_forall fun n => (hgm n).2 x)
  refine ⟨h, hhm.aestronglyMeasurable, hhb, fun n => ?_⟩
  let B : Set X := ⋃ k, ⋃ (_ : n < k), A k
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun _ => hA k
  have heq : ∀ᵐ x ∂μ, x ∉ B → g (n+1) x = h x := by
    filter_upwards [hlim] with x hx hxB
    have hno : ∀ k, n+1 ≤ k → x ∉ A k := by
      intro k hk hxk
      exact hxB (Set.mem_iUnion_of_mem k (Set.mem_iUnion_of_mem (by omega : n < k) hxk))
    have hgconst : Tendsto (fun m => g m x) atTop (𝓝 (g (n+1) x)) :=
      tendsto_const_nhds.congr' ((eventually_ge_atTop (n+1)).mono fun m hm =>
        (successive_patches_stable g A hstep x (n+1) hno m hm).symm)
    exact tendsto_nhds_unique hgconst hx
  have herr := integral_mul_patch_error (hf n) (hgm (n+1)).1
    hhm.aestronglyMeasurable (ae_of_all _ (hgm (n+1)).2) hhb B hBm heq
  have htri := norm_sub_norm_le (∫ x, f n x * g (n+1) x ∂μ)
    (∫ x, f n x * h x ∂μ)
  have hmassn := (hmass n).trans (hgi n)
  have hfn := hfuture n
  change (∫ x in B, ‖f n x‖ ∂μ) < ε / 8 at hfn
  linarith

/-- A diagonal selection excludes every finite initial family. -/
theorem select_bad_integral_matrix (I : ℕ → ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hlim : ∀ n, Tendsto (I n) atTop (𝓝 0))
    (hbad : ∀ k, ∃ n, ε ≤ I n k) :
    ∃ j k : ℕ → ℕ, StrictMono j ∧ StrictMono k ∧
      (∀ m, ε ≤ I (j m) (k m)) ∧
      ∀ m, I (j m) (k (m+1)) < ε / 8 := by
  classical
  have hs (p : ℕ × ℕ) : ∃ q : ℕ × ℕ,
      p.1 < q.1 ∧ p.2 < q.2 ∧ ε ≤ I q.2 q.1 ∧ I p.2 q.1 < ε / 8 := by
    have heach : ∀ i : Fin (p.2+1), ∀ᶠ k in atTop, I i.val k < ε / 8 :=
      fun i => (hlim i.val).eventually (gt_mem_nhds (by positivity))
    have hall := (eventually_all).mpr heach
    obtain ⟨k, hk, hIk⟩ := ((eventually_gt_atTop p.1).and hall).exists
    obtain ⟨n, hn⟩ := hbad k
    have hpn : p.2 < n := by
      by_contra h
      have hi := hIk (⟨n, by omega⟩ : Fin (p.2+1))
      dsimp at hi
      linarith
    exact ⟨(k,n), hk, hpn, hn, hIk ⟨p.2, by omega⟩⟩
  choose next hnext using hs
  obtain ⟨n₀, hn₀⟩ := hbad 0
  let s : ℕ → ℕ × ℕ := fun m => Nat.rec (0,n₀) (fun _ p => next p) m
  have hsnext (m : ℕ) : s (m+1) = next (s m) := rfl
  have hk : StrictMono (fun m => (s m).1) := strictMono_nat_of_lt_succ
    (fun m => (hnext (s m)).1)
  have hj : StrictMono (fun m => (s m).2) := strictMono_nat_of_lt_succ
    (fun m => (hnext (s m)).2.1)
  refine ⟨fun m => (s m).2, fun m => (s m).1, hj, hk, ?_, ?_⟩
  · intro m
    cases m with
    | zero => exact hn₀
    | succ m => exact (hnext (s m)).2.2.1
  · intro m
    exact (hnext (s m)).2.2.2

/-- Weak nullity forces uniform continuity on any decreasing measurable
sequence with null intersection. This formulation also handles infinite tails. -/
theorem weak_l1_uniform_decreasing_sets {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (f : ℕ → Lp 𝕜 1 μ) (hw : WeaklyConverges μ f 0)
    (A : ℕ → Set X) (hA : ∀ k, MeasurableSet (A k))
    (hanti : Antitone A) (hnull : μ (⋂ k, A k) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ K, ∀ n, (∫ x in A K, ‖f n x‖ ∂μ) < ε := by
  intro ε hε
  by_contra hfail
  push Not at hfail
  have hf (n : ℕ) : Integrable (f n : X → 𝕜) μ :=
    memLp_one_iff_integrable.mp (Lp.memLp (f n))
  obtain ⟨j, k, hj, hk, hmass, hsmall⟩ := select_bad_integral_matrix
    (fun n k => ∫ x in A k, ‖f n x‖ ∂μ) ε hε
    (fun n => integrable_norm_decreasing_sets (hf n) A hA hanti hnull) hfail
  have haef : ∀ᵐ x ∂μ, ∀ᶠ m in atTop, x ∉ A (k m) := by
    have hout : ∀ᵐ x ∂μ, x ∉ ⋂ k, A k := by
      rw [ae_iff]
      convert hnull using 2
      ext x
      simp
    filter_upwards [hout] with x hx
    have hex : ∃ K, x ∉ A K := by
      by_contra h
      push Not at h
      exact hx (Set.mem_iInter.mpr h)
    obtain ⟨K, hK⟩ := hex
    exact (hk.tendsto_atTop.eventually (eventually_ge_atTop K)).mono fun m hm hxm =>
      hK (hanti hm hxm)
  have hfuture (m : ℕ) :
      (∫ x in ⋃ l, ⋃ (_ : m < l), A (k l), ‖f (j m) x‖ ∂μ) < ε / 8 := by
    have hsub : (⋃ l, ⋃ (_ : m < l), A (k l)) ⊆ A (k (m+1)) := by
      refine Set.iUnion_subset fun l => Set.iUnion_subset fun hl => ?_
      exact hanti (hk.monotone (by omega))
    exact (setIntegral_mono_set (hf (j m)).norm.integrableOn
      (ae_of_all _ (fun _ => norm_nonneg _)) (ae_of_all _ (fun _ hx => hsub hx))).trans_lt (hsmall m)
  obtain ⟨h, hhm, hhb, hlarge⟩ := exists_gliding_hump_test
    (fun m x => f (j m) x) (fun m => hf (j m)) (fun m => A (k m))
    (fun m => hA (k m)) haef ε hmass hfuture
  have htest := (weak_l1_bounded_tests μ f 0 hw h hhm hhb).comp hj.tendsto_atTop
  have hzero : Tendsto (fun m => ‖∫ x, f (j m) x * h x ∂μ‖) atTop (𝓝 0) := by
    have hz : (∫ x, (0 : Lp 𝕜 1 μ) x * h x ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero (E := 𝕜) (p := 1) (μ := μ)] with x hx
      change ((0 : Lp 𝕜 1 μ) : X → 𝕜) x * h x = 0
      change ((0 : Lp 𝕜 1 μ) : X → 𝕜) x = 0 at hx
      rw [hx, zero_mul]
    simpa only [Function.comp_apply, hz, norm_zero] using htest.norm
  obtain ⟨m, hm⟩ := (hzero.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 3*ε/4))).exists
  exact (not_lt_of_ge (hlarge m).le) hm

/-- The full weakly-null conclusion, including tightness on infinite-measure spaces. -/
theorem weak_l1_null_controls : WeakNullControls.{u} := by
  intro X 𝕜 _ _ μ _ f hw
  have hf (n : ℕ) : Integrable (f n : X → 𝕜) μ :=
    memLp_one_iff_integrable.mp (Lp.memLp (f n))
  constructor
  · by_contra hfail
    change ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ C : Set X, MeasurableSet C → μ C < ENNReal.ofReal δ →
        ∀ n, (∫ x in C, ‖f n x‖ ∂μ) < ε) at hfail
    push Not at hfail
    obtain ⟨ε, hε, hfail⟩ := hfail
    have hchoose (k : ℕ) : ∃ C : Set X, MeasurableSet C ∧
        μ C < ENNReal.ofReal ((1/2 : ℝ)^k) ∧
        ∃ n, ε ≤ ∫ x in C, ‖f n x‖ ∂μ :=
      hfail ((1/2 : ℝ)^k) (by positivity)
    choose C hCm hCμ j hbad using hchoose
    have hgeom : (∑' k : ℕ, ENNReal.ofReal ((1/2 : ℝ)^k)) = 2 := by
      simp_rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/2)]
      have he : ENNReal.ofReal (1/2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat, one_div]
      rw [he, ENNReal.tsum_geometric_two]
    have hsum : (∑' k, μ (C k)) ≠ ∞ :=
      ne_of_lt ((ENNReal.tsum_le_tsum (fun k => (hCμ k).le)).trans_lt
        (by rw [hgeom]; norm_num))
    let A : ℕ → Set X := fun k => ⋃ l, ⋃ (_ : k ≤ l), C l
    have hA (k : ℕ) : MeasurableSet (A k) := MeasurableSet.iUnion fun l =>
      MeasurableSet.iUnion fun _ => hCm l
    have hanti : Antitone A := by
      intro a b hab x hx
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hbl, hxl⟩ := Set.mem_iUnion.mp hl
      exact Set.mem_iUnion_of_mem l (Set.mem_iUnion_of_mem (hab.trans hbl) hxl)
    have hnull : μ (⋂ k, A k) = 0 := by
      change μ (⨅ k, ⨆ l ≥ k, C l) = 0
      simpa only [limsup_eq_iInf_iSup_of_nat] using
        (measure_limsup_atTop_eq_zero hsum)
    obtain ⟨K, hK⟩ := weak_l1_uniform_decreasing_sets μ f hw A hA hanti hnull ε hε
    have hsub : C K ⊆ A K := fun x hx =>
      Set.mem_iUnion_of_mem K (Set.mem_iUnion_of_mem (le_refl K) hx)
    have hmono := setIntegral_mono_set (hf (j K)).norm.integrableOn
      (ae_of_all _ (fun _ => norm_nonneg _)) (ae_of_all _ (fun _ hx => hsub hx))
    exact (not_lt_of_ge ((hbad K).trans hmono)) (hK (j K))
  · intro ε hε
    let A : ℕ → Set X := fun k => (spanningSets μ k)ᶜ
    have hA (k : ℕ) : MeasurableSet (A k) := (measurableSet_spanningSets μ k).compl
    have hanti : Antitone A := fun _ _ h => Set.compl_subset_compl.mpr
      (monotone_spanningSets μ h)
    have hnull : μ (⋂ k, A k) = 0 := by
      simp only [A, ← Set.compl_iUnion, iUnion_spanningSets, Set.compl_univ, measure_empty]
    obtain ⟨K, hK⟩ := weak_l1_uniform_decreasing_sets μ f hw A hA hanti hnull ε hε
    exact ⟨spanningSets μ K, measurableSet_spanningSets μ K,
      measure_spanningSets_lt_top μ K, hK⟩

/-- Centering and restoration of the limit give both assertions for every
weakly convergent L¹ sequence. -/
theorem weak_l1_convergent_controls : WeakConvergentControls.{u} := by
  intro X 𝕜 _ _ μ _ f g hw
  have hc := weak_l1_null_controls μ (fun n => f n - g)
    ((weak_l1_centering μ f g).mp hw)
  exact ⟨(weak_l1_controls_centering μ f g).mpr hc, hc⟩

end ExpandedFA.FunctionSpaces
