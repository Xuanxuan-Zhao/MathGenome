import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.FunctionalVisibleSigmafiniteSupport
import MathGenome.Internal.RealAnalysis.D11.Ch20.LpDualSigmafiniteLocal
import MathGenome.Internal.RealAnalysis.D11.Ch10.SigmafiniteSupport
import Mathlib.Analysis.Normed.Operator.NNNorm

open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch20.FunctionalVisibleSigmafiniteSupport
open LpDualSigmafiniteLocal
variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]

/-- The chosen measurable representative has sigma-finite literal support. -/
lemma lp_support (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp 𝕜 p μ) :
    MeasurableSet (Function.support (f : X → 𝕜)) ∧
      SigmaFinite (μ.restrict (Function.support (f : X → 𝕜))) := by
  borelize 𝕜
  have hpR : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  have hf : (f : X → 𝕜) ∈ Ch10.LpDefinition.rawLp μ p.toReal := by
    apply (Ch10.LpDefinition.rawLp_iff_memLp μ p.toReal _ hpR).mpr
    exact ⟨(Lp.stronglyMeasurable f).measurable,
      by simpa only [ENNReal.ofReal_toReal hp] using Lp.memLp f⟩
  exact (Ch01.MeasureDefinitions.sigmaFiniteSet_iff μ _).mp
    (Ch10.SigmafiniteSupport.sigmafinite_support μ p.toReal f hpR hf)

lemma cutoff_eq_of_support_subset (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (F : Set X) (hF : MeasurableSet F) (f : Lp 𝕜 p μ)
    (hf : Function.support (f : X → 𝕜) ⊆ F) :
    cutoffLp μ p F hF f = f := by
  apply Lp.ext
  exact (cutoffLp_coe μ p F hF f).trans
    (ae_of_all μ (fun x => congrFun (Set.indicator_eq_self.mpr hf) x))

/-- A countable union of measurable sigma-finite sets is sigma-finite. -/
lemma sigmaFinite_iUnion {ι : Type*} [Countable ι] (μ : Measure X)
    (E : ι → Set X) (hE : ∀ i, MeasurableSet (E i))
    (hσ : ∀ i, SigmaFinite (μ.restrict (E i))) :
    SigmaFinite (μ.restrict (⋃ i, E i)) := by
  letI : ∀ i, SigmaFinite (μ.restrict (E i)) := hσ
  apply Measure.sigmaFinite_of_countable
    (S := insert (⋃ i, E i)ᶜ
      (Set.range (fun k : ι × ℕ => spanningSets (μ.restrict (E k.1)) k.2 ∩ E k.1)))
    ((Set.countable_range _).insert _)
  · intro s hs
    rcases hs with rfl | ⟨⟨i, n⟩, rfl⟩
    · rw [Measure.restrict_apply (MeasurableSet.iUnion hE).compl, compl_inter_self,
        measure_empty]
      exact ENNReal.zero_lt_top
    rw [Measure.restrict_apply ((measurableSet_spanningSets _ _).inter (hE i))]
    have hsub : spanningSets (μ.restrict (E i)) n ∩ E i ⊆ ⋃ i, E i :=
      fun x hx => mem_iUnion.mpr ⟨i, hx.2⟩
    rw [inter_eq_left.mpr hsub]
    rw [← Measure.restrict_apply (measurableSet_spanningSets _ _)]
    exact measure_spanningSets_lt_top _ _
  · apply le_antisymm (subset_univ _)
    intro x _
    by_cases hx : x ∈ ⋃ i, E i
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp
        ((iUnion_spanningSets (μ.restrict (E i))).symm ▸ mem_univ x)
      exact mem_sUnion.mpr ⟨_, Or.inr ⟨(i, n), rfl⟩, hxn, hxi⟩
    · exact mem_sUnion.mpr ⟨_, Or.inl rfl, hx⟩

/-- At a finite positive exponent, a cutoff preserves the norm only when
it preserves the class. This is the strictness needed in the support argument. -/
lemma cutoff_eq_of_norm_eq (μ : Measure X) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq0 : q ≠ 0) (hq : q ≠ ∞) (F : Set X) (hF : MeasurableSet F)
    (g : Lp 𝕜 q μ) (he : ‖cutoffLp μ q F hF g‖ = ‖g‖) :
    cutoffLp μ q F hF g = g := by
  let k := cutoffLp μ q F hF g
  have hpow : (fun x => ‖k x‖ ^ q.toReal) =ᵐ[μ]
      (fun x => ‖g x‖ ^ q.toReal) := by
    apply (integral_eq_iff_of_ae_le
      ((Lp.memLp k).integrable_norm_rpow hq0 hq)
      ((Lp.memLp g).integrable_norm_rpow hq0 hq) ?_).mp
    · rw [PairingNormFiniteQ.integral_norm_power μ q hq0 hq k,
        PairingNormFiniteQ.integral_norm_power μ q hq0 hq g, he]
    · filter_upwards [cutoffLp_coe μ q F hF g] with x hx
      change ‖k x‖ ^ q.toReal ≤ ‖g x‖ ^ q.toReal
      rw [show k x = F.indicator (g : X → 𝕜) x from hx]
      exact Real.rpow_le_rpow (norm_nonneg _)
        (norm_indicator_le_norm_self (f := (g : X → 𝕜)) (a := x)) ENNReal.toReal_nonneg
  apply Lp.ext
  filter_upwards [cutoffLp_coe μ q F hF g, hpow] with x hx hp
  by_cases h : x ∈ F
  · simpa only [Set.indicator_of_mem h] using hx
  · have hk : k x = 0 := by simpa [h] using hx
    have hg : g x = 0 := by
      rw [hk, norm_zero, Real.zero_rpow (ENNReal.toReal_pos hq0 hq).ne'] at hp
      exact norm_eq_zero.mp
        ((Real.rpow_eq_zero (norm_nonneg _) (ENNReal.toReal_pos hq0 hq).ne').mp hp.symm)
    exact hk.trans hg.symm

/-- Rational near-norming tests yield a measurable sigma-finite set on
which the cutoff functional has its full original norm. -/
lemma exists_norming_set (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) :
    ∃ F : Set X, ∃ hF : MeasurableSet F, SigmaFinite (μ.restrict F) ∧
      ‖ℓ.comp (cutoffLp μ p F hF)‖ = ‖ℓ‖ := by
  classical
  have hw (r : ℚ) : ∃ f : Lp 𝕜 p μ,
      (0 ≤ (r : ℝ) ∧ (r : ℝ) < ‖ℓ‖) → (r : ℝ) * ‖f‖ < ‖ℓ f‖ := by
    by_cases h : 0 ≤ (r : ℝ) ∧ (r : ℝ) < ‖ℓ‖
    · obtain ⟨f, hf⟩ := ℓ.exists_mul_lt_of_lt_opNorm h.1 h.2
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h' => False.elim (h h')⟩
  choose f hf using hw
  let E (r : ℚ) := Function.support (f r : X → 𝕜)
  have hE r := lp_support μ p hp (f r)
  let F := ⋃ r, E r
  have hF : MeasurableSet F := MeasurableSet.iUnion fun r => (hE r).1
  refine ⟨F, hF, sigmaFinite_iUnion μ E (fun r => (hE r).1)
    (fun r => (hE r).2), le_antisymm ?_ ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    exact (ℓ.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_cutoffLp_le μ p F hF v) (norm_nonneg _))
  · by_contra! hlt
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn hlt
    have h := hf r ⟨(norm_nonneg _).trans hr₁.le, hr₂⟩
    have he : cutoffLp μ p F hF (f r) = f r :=
      cutoff_eq_of_support_subset μ p F hF (f r) (subset_iUnion E r)
    have hb := (ℓ.comp (cutoffLp μ p F hF)).le_opNorm (f r)
    rw [ContinuousLinearMap.comp_apply, he] at hb
    have hn : 0 < ‖f r‖ := by
      by_contra! hn
      have hz : f r = 0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
      simp [hz] at h
    exact (not_lt_of_ge hb) ((mul_lt_mul_of_pos_right hr₁ hn).trans h)

/-- Local duality, followed by extension by zero, represents the cutoff
functional on an arbitrary ambient measure. -/
lemma sigmaFinite_piece_density (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜)
    (A : Set X) (hA : MeasurableSet A) [SigmaFinite (μ.restrict A)] :
    ∃ H : Lp 𝕜 q μ,
      (∀ f, IntegralPairing.pairing μ p q H f = ℓ (cutoffLp μ p A hA f)) ∧
      ‖H‖ ≤ ‖ℓ‖ := by
  obtain ⟨k, hk, _⟩ := sigmaFinite_duality
    (μ.restrict A) p q hp (ℓ.comp (extendLp μ p A hA))
  let H := extendLp μ q A hA k
  have hr f : IntegralPairing.pairing μ p q H f = ℓ (cutoffLp μ p A hA f) := by
    rw [show H = extendLp μ q A hA k from rfl, pairing_extend]
    exact (IntegralPairing.pairing_eq_integral (μ.restrict A) p q k _).2.trans
      ((hk.1 _).2.symm)
  refine ⟨H, hr, ?_⟩
  change ‖extendLp μ q A hA k‖ ≤ _
  rw [norm_extendLp, hk.2]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  exact (ℓ.le_opNorm _).trans_eq (congrArg (fun t => ‖ℓ‖ * t) (norm_extendLp μ p A hA f))

/-- A sigma-finite norming set detects the entire functional when the
conjugate exponent is finite. -/
lemma norming_set_visible (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (hq : q ≠ ∞) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜)
    (F : Set X) (hF : MeasurableSet F) [SigmaFinite (μ.restrict F)]
    (hn : ‖ℓ.comp (cutoffLp μ p F hF)‖ = ‖ℓ‖) (f : Lp 𝕜 p μ) :
    ℓ f = ℓ (cutoffLp μ p F hF f) := by
  let S := Function.support (f : X → 𝕜)
  obtain ⟨hS, hσS⟩ := lp_support μ p hp f
  letI : SigmaFinite (μ.restrict S) := hσS
  let A := F ∪ S
  have hA : MeasurableSet A := hF.union hS
  have hFA : F ⊆ A := subset_union_left
  have hfA : cutoffLp μ p A hA f = f :=
    cutoff_eq_of_support_subset μ p A hA f subset_union_right
  obtain ⟨H, hH, hbound⟩ := sigmaFinite_piece_density μ p q hp ℓ A hA
  have he : IntegralPairing.pairing μ p q (cutoffLp μ q F hF H) =
      ℓ.comp (cutoffLp μ p F hF) := by
    ext v
    rw [pairing_cutoff, hH,
      cutoffLp_comp μ p F A hF hA hFA, ContinuousLinearMap.comp_apply]
  have hnorm : ‖cutoffLp μ q F hF H‖ = ‖ℓ‖ := by
    exact (PairingNormFiniteQ.norm_pairing μ p q hq _).symm.trans
      ((congrArg norm he).trans hn)
  have hfix : cutoffLp μ q F hF H = H :=
    cutoff_eq_of_norm_eq μ q (ENNReal.HolderConjugate.ne_zero q p) hq F hF H
      (le_antisymm (norm_cutoffLp_le μ q F hF H) (hbound.trans hnorm.symm.le))
  calc
    ℓ f = IntegralPairing.pairing μ p q H f := by rw [hH, hfA]
    _ = IntegralPairing.pairing μ p q (cutoffLp μ q F hF H) f := by rw [hfix]
    _ = IntegralPairing.pairing μ p q H (cutoffLp μ p F hF f) :=
      pairing_cutoff μ p q F hF H f
    _ = ℓ (cutoffLp μ p F hF f) := by
      rw [hH, cutoffLp_comp μ p F A hF hA hFA]

/-- Every bounded scalar functional on finite-p Lp, p>1, has a measurable
sigma-finite visible support, even on an arbitrary positive measure space. -/
theorem functional_visible_sigmafinite_support :
    Specs.D11.Ch20.FunctionalVisibleSigmafiniteSupport.functional_visible_sigmafinite_support := by
  intro X 𝕜 _ _ μ p _ hp1 hp ℓ
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  letI : ENNReal.HolderConjugate p q := by
    apply ENNReal.holderConjugate_iff.mpr
    dsimp [q]
    rw [inv_inv, add_tsub_cancel_of_le]
    simpa using ENNReal.inv_le_inv.mpr hp1.le
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : q ≠ ∞ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  obtain ⟨F, hF, hσF, hn⟩ := exists_norming_set μ p hp ℓ
  letI : SigmaFinite (μ.restrict F) := hσF
  refine ⟨F, hF, hσF, fun f => ⟨cutoffLp μ p F hF f,
    cutoffLp_coe μ p F hF f, ?_⟩⟩
  exact norming_set_visible μ p q hp hq ℓ F hF hn f

end D11.Ch20.FunctionalVisibleSigmafiniteSupport
