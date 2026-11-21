import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.StrongWeakLowerSemicontinuity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.CaratheodoryIntegrands
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.CountableAffineSupports
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.AffineEnvelopeLowerLimit
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
universe u
namespace VariationalNotes.Sobolev

/-- The manuscript's lower bound makes the signed energy well defined for every
mixed-exponent field, even on an incomplete measure space. -/
theorem mixed_energy_negativePartIntegrable :
    StrongWeakSpecs.mixed_energy_negativePartIntegrable.{u} := by
  intro S _ μ _ m k d q r F hF a ha C _hC hbound s z
  have hFm : AEMeasurable (fun x => F x (s x) (fun i => z i x)) μ :=
    MixedCaratheodory.aemeasurable_lp_substitution hF s z
  have hpower : Integrable (fun x => ‖s x‖ ^ q.toReal) μ :=
    (Lp.memLp s).integrable_norm_rpow'
  apply negativePartIntegrable_of_lower_bound hFm (ha.add (hpower.const_mul C))
  filter_upwards [hbound] with x hx
  change -(a x + C * ‖s x‖ ^ q.toReal) ≤ _
  have hh := hx (s x) (fun i => z i x)
  linarith

/-- In particular, neither the limiting energy nor any sequence energy is `-∞`. -/
lemma mixed_energy_ne_bot {S : Type u} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {m k : ℕ} {d : Fin k → ℕ}
    {q : ℝ≥0∞} {r : Fin k → ℝ≥0∞}
    (F : S → EuclideanSpace ℝ (Fin m) →
      (∀ i, EuclideanSpace ℝ (Fin (d i))) → ℝ)
    (hF : MixedCaratheodory μ F) (a : S → ℝ) (ha : Integrable a μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂μ, ∀ s z, -a x - C * ‖s‖ ^ q.toReal ≤ F x s z)
    (s : Lp (EuclideanSpace ℝ (Fin m)) q μ)
    (z : ∀ i, Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ) :
    extendedIntegral μ (fun x => F x (s x) (fun i => z i x)) ≠ ⊥ :=
  extendedIntegral_ne_bot (hF.aemeasurable_lp_substitution s z)
    (mixed_energy_negativePartIntegrable μ F hF a ha C hC hbound s z)

/-- The real integral of the state power equals the power of the `Lp` norm.
This retains the exact Euclidean growth term in the manuscript. -/
lemma integral_norm_rpow_eq_norm_rpow {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] {μ : Measure S} {q : ℝ≥0∞}
    (hq₀ : q ≠ 0) (hq_top : q ≠ ∞) (s : Lp E q μ) :
    (∫ x, ‖s x‖ ^ q.toReal ∂μ) = ‖s‖ ^ q.toReal := by
  have hqR : q.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hq₀, hq_top⟩
  have hn := lpNorm_eq_integral_norm_rpow_toReal hq₀ hq_top (Lp.aestronglyMeasurable s)
  change ‖s‖ = (∫ x, ‖s x‖ ^ q.toReal ∂μ) ^ q.toReal⁻¹ at hn
  rw [hn, Real.rpow_inv_rpow (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hqR]

/-- Strong `Lp` convergence makes the integrable correction converge, including
at `q = 1`. Only norm convergence, rather than a pointwise majorant, is needed. -/
lemma tendsto_integral_state_correction {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] {μ : Measure S} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq_top : q ≠ ∞) {sₙ : ℕ → Lp E q μ} {s : Lp E q μ}
    (hs : Tendsto sₙ atTop (𝓝 s)) (a : S → ℝ) (ha : Integrable a μ) (C : ℝ) :
    Tendsto (fun n => ∫ x, a x + C * ‖sₙ n x‖ ^ q.toReal ∂μ) atTop
      (𝓝 (∫ x, a x + C * ‖s x‖ ^ q.toReal ∂μ)) := by
  have hq₀ : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ q))
  have hi (v : Lp E q μ) :
      (∫ x, a x + C * ‖v x‖ ^ q.toReal ∂μ) =
        (∫ x, a x ∂μ) + C * ‖v‖ ^ q.toReal := by
    rw [integral_add ha (((Lp.memLp v).integrable_norm_rpow hq₀ hq_top).const_mul C),
      integral_const_mul, integral_norm_rpow_eq_norm_rpow hq₀ hq_top]
  simp_rw [hi]
  exact tendsto_const_nhds.add (tendsto_const_nhds.mul
    (hs.norm.rpow_const (Or.inr ENNReal.toReal_nonneg)))

/-- Adding an integrable nonnegative lower-bound correction is valid even
when the positive energy is infinite. -/
lemma extendedIntegral_add_nonnegative_correction {S : Type*} [MeasurableSpace S]
    {μ : Measure S} {f h : S → ℝ} (hf : AEMeasurable f μ)
    (hh : Integrable h μ) (hnonneg : ∀ᵐ x ∂μ, 0 ≤ h x)
    (hsum : ∀ᵐ x ∂μ, 0 ≤ f x + h x) :
    extendedIntegral μ f + (∫ x, h x ∂μ : ℝ) =
      (∫⁻ x, ENNReal.ofReal (f x + h x) ∂μ : ℝ≥0∞) := by
  have hnegative : NegativePartIntegrable μ f := by
    apply negativePartIntegrable_of_lower_bound hf hh
    filter_upwards [hsum] with x hx
    linarith
  have hnfinite := (negativePartIntegrable_iff hf).mp hnegative
  have hid : (fun x => ENNReal.ofReal (f x) + ENNReal.ofReal (h x)) =ᵐ[μ]
      (fun x => ENNReal.ofReal (f x + h x) + ENNReal.ofReal (-f x)) := by
    filter_upwards [hnonneg, hsum] with x hx hfx
    by_cases hpos : 0 ≤ f x
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hpos), add_zero,
        ENNReal.ofReal_add hpos hx]
    · have hneg : f x ≤ 0 := le_of_not_ge hpos
      rw [ENNReal.ofReal_of_nonpos hneg, zero_add,
        ← ENNReal.ofReal_add hfx (neg_nonneg.mpr hneg)]
      congr 1
      ring
  have heq := lintegral_congr_ae hid
  have hnegm : AEMeasurable (fun x => ENNReal.ofReal (-f x)) μ := by
    simpa only [Pi.neg_apply] using hf.neg.ennreal_ofReal
  rw [lintegral_add_left' hf.ennreal_ofReal,
    lintegral_add_right' _ hnegm] at heq
  have heqE := congrArg (fun t : ℝ≥0∞ => (t : EReal)) heq
  simp only [EReal.coe_ennreal_add] at heqE
  have hc : (∫⁻ x, ENNReal.ofReal (h x) ∂μ : ℝ≥0∞).toEReal =
      (∫ x, h x ∂μ : ℝ) :=
    (extendedIntegral_of_nonneg hnonneg).symm.trans (extendedIntegral_eq_integral hh)
  rw [hc] at heqE
  have hnE := EReal.coe_ennreal_toReal hnfinite
  have heqsub := congrArg
    (fun t : EReal => t - ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal : ℝ)) heqE
  rw [← hnE] at heqsub
  rw [EReal.add_sub_cancel_right] at heqsub
  unfold extendedIntegral
  rw [← hnE]
  calc
    _ = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ℝ≥0∞) : EReal) +
        (∫ x, h x ∂μ : ℝ) - ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal : ℝ) := by
      simp only [sub_eq_add_neg]
      ac_rfl
    _ = _ := heqsub

/-- A convergent finite scalar correction commutes with the extended liminf,
including when the latter is either infinity. -/
lemma liminf_add_tendsto_real (f : ℕ → EReal) {cₙ : ℕ → ℝ} {c : ℝ}
    (hc : Tendsto cₙ atTop (𝓝 c)) :
    liminf (fun n => f n + (cₙ n : EReal)) atTop = liminf f atTop + (c : EReal) := by
  have hcE : Tendsto (fun n => (cₙ n : EReal)) atTop (𝓝 (c : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hc
  apply le_antisymm
  · have hh := EReal.liminf_add_le (u := fun n => (cₙ n : EReal)) (v := f)
      (f := atTop) (Or.inl (by rw [hcE.limsup_eq]; exact EReal.coe_ne_bot _))
      (Or.inl (by rw [hcE.limsup_eq]; exact EReal.coe_ne_top _))
    change liminf (fun n => (cₙ n : EReal) + f n) atTop ≤ _ at hh
    rw [hcE.limsup_eq] at hh
    simpa only [add_comm] using hh
  · have hh := EReal.le_liminf_add (u := f) (v := fun n => (cₙ n : EReal)) (f := atTop)
    change liminf f atTop + liminf (fun n => (cₙ n : EReal)) atTop ≤
      liminf (fun n => f n + (cₙ n : EReal)) atTop at hh
    simpa only [hcE.liminf_eq] using hh

/-- Removing the normalization preserves the desired lower semicontinuity. -/
lemma le_liminf_of_add_correction {A : EReal} {f : ℕ → EReal}
    {cₙ : ℕ → ℝ} {c : ℝ} (hc : Tendsto cₙ atTop (𝓝 c))
    (h : A + (c : EReal) ≤ liminf (fun n => f n + (cₙ n : EReal)) atTop) :
    A ≤ liminf f atTop := by
  rw [liminf_add_tendsto_real f hc] at h
  exact (EReal.addLECancellable_coe c).add_le_add_iff_right.mp h

/-- Normalization preserves the finite Carathéodory property. The correction's
base function is measurable; an integrable function can be replaced a.e. by
its measurable representative before this lemma is applied. -/
lemma MixedCaratheodory.add_state_power {S : Type*} [MeasurableSpace S]
    {μ : Measure S} {m k : ℕ} {d : Fin k → ℕ}
    {F : S → EuclideanSpace ℝ (Fin m) →
      (∀ i, EuclideanSpace ℝ (Fin (d i))) → ℝ}
    (hF : MixedCaratheodory μ F) {a : S → ℝ} (ha : Measurable a)
    (C : ℝ) (q : ℝ≥0∞) :
    MixedCaratheodory μ (fun x s z => F x s z + (a x + C * ‖s‖ ^ q.toReal)) := by
  constructor
  · intro p
    exact (hF.1 p).add (ha.add measurable_const)
  · filter_upwards [hF.2] with x hx
    exact hx.add (continuous_const.add (continuous_const.mul
      (continuous_fst.norm.rpow_const (fun _ => Or.inr ENNReal.toReal_nonneg))))

/-- Transfer the Euclidean affine supports to a product of independent fibers.
The adjoints of the coordinate inclusions split each affine functional into its
fiber slopes; no exponent or norm identification of the `Lp` spaces is used. -/
lemma mixed_countable_affine_envelope
    {S : Type u} [MeasurableSpace S] (μ : Measure S)
    {m k : ℕ} {d : Fin k → ℕ}
    (G : S → EuclideanSpace ℝ (Fin m) →
      (∀ i, EuclideanSpace ℝ (Fin (d i))) → ℝ)
    (hG : MixedCaratheodory μ G)
    (hconv : ∀ᵐ x ∂μ, ∀ s, ConvexOn ℝ univ (G x s))
    (hpos : ∀ᵐ x ∂μ, ∀ s y, 0 ≤ G x s y) :
    ∃ c b, AffineEnvelopeSpecs.CountableAffineEnvelope μ G c b := by
  classical
  let B := fun i : Fin k => EuclideanSpace ℝ (Fin (d i))
  let V := ∀ i, B i
  let D := Module.finrank ℝ V
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin D) :=
    (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv |>.trans
      (EuclideanSpace.equiv (Fin D) ℝ).symm
  let H := fun x s y => G x s (e.symm y)
  have hH : Caratheodory μ
      (fun x (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin D)) => H x p.1 p.2) := by
    refine ⟨fun p => hG.1 (p.1, e.symm p.2), ?_⟩
    filter_upwards [hG.2] with x hx
    exact hx.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
  have hHconv : ∀ᵐ x ∂μ, ∀ s, ConvexOn ℝ univ (H x s) := by
    filter_upwards [hconv] with x hx
    intro s
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
    have hh := (hx s).2 (mem_univ (e.symm y)) (mem_univ (e.symm z)) ha hb hab
    simpa only [H, map_add, map_smul] using hh
  have hHpos : ∀ᵐ x ∂μ, ∀ s y, 0 ≤ H x s y :=
    hpos.mono (fun x hx s y => hx s (e.symm y))
  obtain ⟨N, c, b, hNm, hN0, _, hminor, hlub, hcont, hmeas⟩ :=
    AffineSupports.countable_affine_supports μ H hH hHconv hHpos
  let J (i : Fin k) : B i →L[ℝ] EuclideanSpace ℝ (Fin D) :=
    (e.toLinearMap.comp (LinearMap.single ℝ B i)).toContinuousLinearMap
  let slopes := fun j i x s => (J i).adjoint (b j x s)
  have hsplit (v : EuclideanSpace ℝ (Fin D)) (y : V) :
      (∑ i, inner ℝ ((J i).adjoint v) (y i)) = inner ℝ v (e y) := by
    simp_rw [ContinuousLinearMap.adjoint_inner_left, ← inner_sum]
    congr 1
    change ∑ i, e (Pi.single i (y i)) = e y
    rw [← map_sum, Finset.univ_sum_single]
  refine ⟨c, slopes, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j x => (hcont j x).1
  · intro j i x
    exact (J i).adjoint.continuous.comp (hcont j x).2
  · intro j s hs
    have hm := (hmeas j (hs.mk s) hs.measurable_mk).1
    exact hm.aemeasurable.congr (hs.ae_eq_mk.mono (fun x hx => by
      change c j x (hs.mk s x) = c j x (s x)
      rw [hx]))
  · intro j i s hs
    have hm := (J i).adjoint.continuous.measurable.comp
      (hmeas j (hs.mk s) hs.measurable_mk).2
    exact hm.aemeasurable.congr (hs.ae_eq_mk.mono (fun x hx => by
      change (J i).adjoint (b j x (hs.mk s x)) = (J i).adjoint (b j x (s x))
      rw [hx]))
  · have hNae : ∀ᵐ x ∂μ, x ∉ N := by
      rw [ae_iff]
      simpa using hN0
    filter_upwards [hNae] with x hx
    intro s y
    have heq : (fun j => c j x s + ∑ i, inner ℝ (slopes j i x s) (y i)) =
        (fun j => c j x s + inner ℝ (b j x s) (e y)) := by
      funext j
      rw [hsplit]
    rw [heq]
    have hident : H x s (e y) = G x s y := by simp [H]
    rw [← hident]
    refine ⟨?_, hlub x hx s (e y)⟩
    intro j
    change c j x s + ∑ i, inner ℝ ((J i).adjoint (b j x s)) (y i) ≤ _
    rw [hsplit]
    exact hminor x hx j s (e y)

/-- Nonnegative strong–weak lower semicontinuity, obtained by applying the
affine-envelope theorem along an a.e. convergent state subsequence of a
sequence realizing the energy lower limit. -/
lemma nonnegative_strong_weak_lowerSemicontinuity
    {S : Type u} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    {m k : ℕ} {d : Fin k → ℕ} (q : ℝ≥0∞) (r : Fin k → ℝ≥0∞)
    (hq : 1 ≤ q) (hq_top : q ≠ ∞)
    (hr : ∀ i, 1 < r i) (hr_top : ∀ i, r i ≠ ∞) :
    letI : Fact (1 ≤ q) := ⟨hq⟩
    letI : ∀ i, Fact (1 ≤ r i) := fun i => ⟨(hr i).le⟩
    ∀ (G : S → EuclideanSpace ℝ (Fin m) →
        (∀ i, EuclideanSpace ℝ (Fin (d i))) → ℝ),
      MixedCaratheodory μ G →
      (∀ᵐ x ∂μ, ∀ s, ConvexOn ℝ univ (G x s)) →
      (∀ᵐ x ∂μ, ∀ s z, 0 ≤ G x s z) →
      ∀ (sₙ : ℕ → Lp (EuclideanSpace ℝ (Fin m)) q μ)
        (s : Lp (EuclideanSpace ℝ (Fin m)) q μ)
        (zₙ : ℕ → ∀ i, Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ)
        (z : ∀ i, Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ),
        Tendsto sₙ atTop (𝓝 s) →
        (∀ i, Tendsto (fun n => toWeakSpace ℝ _ (zₙ n i)) atTop
          (𝓝 (toWeakSpace ℝ _ (z i)))) →
        extendedIntegral μ (fun x => G x (s x) (fun i => z i x)) ≤
          liminf (fun n => extendedIntegral μ
            (fun x => G x (sₙ n x) (fun i => zₙ n i x))) atTop := by
  letI : Fact (1 ≤ q) := ⟨hq⟩
  letI : ∀ i, Fact (1 ≤ r i) := fun i => ⟨(hr i).le⟩
  intro G hG hconv hpos sₙ s zₙ z hs hz
  obtain ⟨c, b, henv⟩ := mixed_countable_affine_envelope μ G hG hconv hpos
  let energy : ℕ → EReal := fun n => extendedIntegral μ
    (fun x => G x (sₙ n x) (fun i => zₙ n i x))
  obtain ⟨ns, hens, hns⟩ := exists_seq_tendsto_liminf (f := atTop) (u := energy)
  obtain ⟨φ, hφ, hsφ⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hs.comp hns)).exists_seq_tendsto_ae
  have hcore := affineEnvelope_lowerLimit S μ m k d r hr
    (fun i => lt_top_iff_ne_top.mpr (hr_top i)) G c b
    (fun n x => sₙ (ns (φ n)) x) (fun x => s x)
    (fun i n => zₙ (ns (φ n)) i) z hG hpos henv
    (fun n => (Lp.aestronglyMeasurable (sₙ (ns (φ n)))).aemeasurable)
    (Lp.aestronglyMeasurable s).aemeasurable hsφ
    (fun i => (hz i).comp (hns.comp hφ.tendsto_atTop))
  have heconv := hens.comp hφ.tendsto_atTop
  exact hcore.trans_eq heconv.liminf_eq

/-- Full theorem, with weak convergence in each independent `Lp` space.
The signed-to-nonnegative reduction uses an everywhere measurable nonnegative
representative of `|a|`, so it is valid on incomplete measure spaces too. -/
theorem strong_weak_lowerSemicontinuity :
    StrongWeakSpecs.strong_weak_lowerSemicontinuity.{u} := by
  intro S _ μ _ m k d q r hq hq_top hr hr_top
  letI : Fact (1 ≤ q) := ⟨hq⟩
  letI : ∀ i, Fact (1 ≤ r i) := fun i => ⟨(hr i).le⟩
  intro F hF hconv a ha C hC hbound sₙ s zₙ z hs hz
  have ham := ha.aestronglyMeasurable.aemeasurable
  let a₀ : S → ℝ := fun x => |ham.mk a x|
  have ha₀m : Measurable a₀ := continuous_abs.measurable.comp ham.measurable_mk
  have ha₀eq : (fun x => |a x|) =ᵐ[μ] a₀ := ham.ae_eq_mk.fun_comp abs
  have ha₀ : Integrable a₀ μ := ha.abs.congr ha₀eq
  have ha₀nonneg (x : S) : 0 ≤ a₀ x := abs_nonneg _
  let G := fun x s z => F x s z + (a₀ x + C * ‖s‖ ^ q.toReal)
  have hG : MixedCaratheodory μ G :=
    MixedCaratheodory.add_state_power hF ha₀m C q
  have hGconv : ∀ᵐ x ∂μ, ∀ s, ConvexOn ℝ univ (G x s) := by
    filter_upwards [hconv] with x hx
    intro s
    exact (hx s).add_const (a₀ x + C * ‖s‖ ^ q.toReal)
  have hGnonneg : ∀ᵐ x ∂μ, ∀ s z, 0 ≤ G x s z := by
    filter_upwards [hbound, ha₀eq] with x hx hax
    intro s z
    have hh := hx s z
    have ha_le : a x ≤ a₀ x := hax ▸ le_abs_self (a x)
    dsimp only [G]
    linarith
  have hq₀ : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  have henergy (v : Lp (EuclideanSpace ℝ (Fin m)) q μ)
      (w : ∀ i, Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ) :
      extendedIntegral μ (fun x => F x (v x) (fun i => w i x)) +
        (∫ x, a₀ x + C * ‖v x‖ ^ q.toReal ∂μ : ℝ) =
      extendedIntegral μ (fun x => G x (v x) (fun i => w i x)) := by
    have hcorr : Integrable (fun x => a₀ x + C * ‖v x‖ ^ q.toReal) μ :=
      ha₀.add (((Lp.memLp v).integrable_norm_rpow hq₀ hq_top).const_mul C)
    have hnn : ∀ᵐ x ∂μ, 0 ≤ a₀ x + C * ‖v x‖ ^ q.toReal :=
      Eventually.of_forall (fun x => add_nonneg (ha₀nonneg x)
        (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)))
    have hsum := hGnonneg.mono (fun x hx => hx (v x) (fun i => w i x))
    exact (extendedIntegral_add_nonnegative_correction
      (MixedCaratheodory.aemeasurable_lp_substitution hF v w) hcorr hnn hsum).trans
      (extendedIntegral_of_nonneg hsum).symm
  have hcore := nonnegative_strong_weak_lowerSemicontinuity μ q r hq hq_top hr hr_top
    G hG hGconv hGnonneg sₙ s zₙ z hs hz
  simp_rw [← henergy] at hcore
  exact le_liminf_of_add_correction
    (tendsto_integral_state_correction hq_top hs a₀ ha₀ C) hcore

end VariationalNotes.Sobolev
