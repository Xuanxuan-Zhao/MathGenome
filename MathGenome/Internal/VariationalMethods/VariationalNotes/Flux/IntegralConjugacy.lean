import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.IntegralRegularity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.LpDuality
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Conjugates
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.IntegralConjugacy
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Topology.Order.IsLUB
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology

namespace VariationalNotes.Flux

def pointwiseConjugate {S E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : S → E → ℝ) (x : S) (w : E) : EReal :=
  IntegralConjugacySpecs.pointwiseConjugate F x w

/-- The pointwise supremum uses exactly the common continuous-dual conjugate. -/
theorem pointwise_conjugate_eq : IntegralConjugacySpecs.pointwise_conjugate_eq_type := by
  intro S E _ _ F x w
  rw [ConvexAnalysis.Specs.conjugate]
  apply le_antisymm
  · apply iSup_le
    intro z
    have hz : z ∈ ConvexAnalysis.Specs.effectiveDomain (fun z => (F x z : WithTop ℝ)) :=
      WithTop.coe_lt_top _
    simpa using (le_iSup₂ (f := fun z (_ : z ∈ ConvexAnalysis.Specs.effectiveDomain
      (fun z => (F x z : WithTop ℝ))) =>
        ((innerSL ℝ w z - (F x z : WithTop ℝ).untopD 0 : ℝ) : EReal)) z hz)
  · apply iSup₂_le
    intro z _
    simpa only [IntegralConjugacySpecs.pointwiseConjugate, WithTop.untopD_coe,
      innerSL_apply_apply] using
      (le_iSup (fun z => ((inner ℝ w z - F x z : ℝ) : EReal)) z)

/-- Scaled Young inequality absorbs the coercive p-power with its given coefficient. -/
theorem coercive_young_bound {p q a₀ : ℝ} (hpq : p.HolderConjugate q) (ha₀ : 0 < a₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      s * t - a₀ * t ^ p ≤ C * s ^ q := by
  let k : ℝ := (a₀ * p) ^ p⁻¹
  have hk : 0 < k := Real.rpow_pos_of_pos (mul_pos ha₀ hpq.pos) _
  have hkp : k ^ p = a₀ * p := Real.rpow_inv_rpow (mul_nonneg ha₀.le hpq.pos.le) hpq.ne_zero
  refine ⟨k⁻¹ ^ q / q, div_nonneg
    (Real.rpow_nonneg (inv_nonneg.mpr hk.le) _) hpq.symm.pos.le, ?_⟩
  intro s t hs ht
  have hy := Real.young_inequality_of_nonneg (mul_nonneg ht hk.le)
    (mul_nonneg hs (inv_nonneg.mpr hk.le)) hpq
  rw [Real.mul_rpow ht hk.le, hkp, Real.mul_rpow hs (inv_nonneg.mpr hk.le)] at hy
  have heq : (t * k) * (s * k⁻¹) = s * t := by field_simp
  have heq' : t ^ p * (a₀ * p) / p = a₀ * t ^ p := by field_simp [hpq.ne_zero]
  rw [heq, heq'] at hy
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    (sub_le_iff_le_add.mpr (by simpa [add_comm] using hy) :
      s * t - a₀ * t ^ p ≤ s ^ q * k⁻¹ ^ q / q)

/-- Embedding a bounded real supremum into the extended reals preserves its value. -/
theorem ereal_iSup_coe {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hb : BddAbove (range f)) : (⨆ i, (f i : EReal)) = ((⨆ i, f i : ℝ) : EReal) := by
  let r : EReal := ⨆ i, (f i : EReal)
  have hrb : r ≠ ⊥ := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot (f i))
      (le_iSup (fun i => (f i : EReal)) i)
  have hrt : r ≠ ⊤ := by
    obtain ⟨b, hb⟩ := hb
    exact ne_top_of_le_ne_top (EReal.coe_ne_top b)
      (iSup_le fun i => EReal.coe_le_coe (hb (mem_range_self i)))
  have hr : (r.toReal : EReal) = r := EReal.coe_toReal hrt hrb
  apply le_antisymm
  · exact iSup_le fun i => EReal.coe_le_coe (le_ciSup hb i)
  · change ((⨆ i, f i : ℝ) : EReal) ≤ r
    rw [← hr]
    apply EReal.coe_le_coe
    apply ciSup_le
    intro i
    exact EReal.coe_le_coe_iff.mp ((le_iSup (fun i => (f i : EReal)) i).trans_eq hr.symm)

section Fiber
variable {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace S] [MeasurableSpace E] [BorelSpace E] in
/-- A continuous, bounded-above fiber supremum can be computed on one dense sequence. -/
theorem pointwiseConjugate_denseSeq (F : S → E → ℝ) (x : S) (w : E)
    (hc : Continuous (F x))
    (hb : BddAbove (range (fun z => inner ℝ w z - F x z))) :
    pointwiseConjugate F x w =
      ((⨆ n : ℕ, inner ℝ w (denseSeq E n) - F x (denseSeq E n) : ℝ) : EReal) := by
  have hcont : Continuous (fun z => inner ℝ w z - F x z) :=
    (continuous_const.inner continuous_id).sub hc
  have hd := (denseRange_denseSeq E).ciSup hcont hb
  change (⨆ z, ((inner ℝ w z - F x z : ℝ) : EReal)) = _
  rw [ereal_iSup_coe _ hb, ← hd]
  congr 1
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨z, n, rfl⟩
    exact le_ciSup (hb.mono (range_comp_subset_range _ _)) n
  · apply ciSup_le
    intro n
    have hb' : BddAbove (range (fun z : range (denseSeq E) =>
        inner ℝ w (z : E) - F x (z : E))) := hb.range_comp_right Subtype.val
    exact le_ciSup hb' ⟨denseSeq E n, mem_range_self n⟩

/-- Continuity and coercivity identify the conjugate with a measurable countable
supremum. Its real value lies between an integrable lower and upper bound. -/
theorem conjugate_integrable : IntegralConjugacySpecs.conjugate_integrable_type := by
  intro S E _ _ _ _ _ _ μ p hp F hF hg σ
  have hpq := Real.HolderConjugate.conjExponent hp
  obtain ⟨a₀, a₁, a, ha₀, ha₁, ha, hapos, hg⟩ := hg
  obtain ⟨C, hC, hYoung⟩ := coercive_young_bound hpq ha₀
  have hpt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hpq.pos.le
  have hqt : (ENNReal.ofReal (p / (p - 1))).toReal = p / (p - 1) :=
    ENNReal.toReal_ofReal hpq.symm.pos.le
  let g : S → ℝ := fun x => ⨆ n : ℕ,
    inner ℝ (σ x) (denseSeq E n) - F x (denseSeq E n)
  have hmeas : Measurable g := Measurable.iSup fun n =>
    ((Lp.stronglyMeasurable σ).measurable.inner measurable_const).sub (hF.1 _)
  have hb (x : S) (hx : ∀ z, a₀ * ‖z‖ ^ (ENNReal.ofReal p).toReal - a x ≤ F x z ∧
      F x z ≤ a x + a₁ * ‖z‖ ^ (ENNReal.ofReal p).toReal) (z : E) :
      inner ℝ (σ x) z - F x z ≤ a x + C * ‖σ x‖ ^ (p / (p - 1)) := by
    have hl := (hx z).1
    rw [hpt] at hl
    have hy := hYoung ‖σ x‖ ‖z‖ (norm_nonneg _) (norm_nonneg _)
    change ‖σ x‖ * ‖z‖ - a₀ * ‖z‖ ^ p ≤ C * ‖σ x‖ ^ (p / (p - 1)) at hy
    have hi := real_inner_le_norm (σ x) z
    linarith
  have hae : ∀ᵐ x ∂μ,
      pointwiseConjugate F x (σ x) = (g x : EReal) ∧
      -a x ≤ g x ∧ g x ≤ a x + C * ‖σ x‖ ^ (p / (p - 1)) := by
    filter_upwards [hF.2, hg] with x hc hx
    have hbdd : BddAbove (range (fun z => inner ℝ (σ x) z - F x z)) :=
      ⟨_, by rintro _ ⟨z, rfl⟩; exact hb x hx z⟩
    have heq := pointwiseConjugate_denseSeq F x (σ x) hc hbdd
    refine ⟨heq, ?_, ?_⟩
    · have hl := le_iSup (fun z => ((inner ℝ (σ x) z - F x z : ℝ) : EReal)) 0
      change ((inner ℝ (σ x) 0 - F x 0 : ℝ) : EReal) ≤ pointwiseConjugate F x (σ x) at hl
      rw [heq] at hl
      have hu := (hx 0).2
      simp only [norm_zero, hpt, Real.zero_rpow hpq.ne_zero, mul_zero, add_zero] at hu
      have hl' : -F x 0 ≤ g x := by simpa using EReal.coe_le_coe_iff.mp hl
      linarith
    · exact ciSup_le (fun n => hb x hx _)
  have hg_real : (fun x => (pointwiseConjugate F x (σ x)).toReal) =ᵐ[μ] g := by
    filter_upwards [hae] with x hx
    rw [hx.1, EReal.toReal_coe]
  have hgi : Integrable g μ := by
    apply integrable_of_le_of_le hmeas.aestronglyMeasurable
      (hae.mono fun x hx => hx.2.1) (hae.mono fun x hx => hx.2.2) ha.neg
    have hi := (Lp.memLp σ).integrable_norm_rpow
      (ne_of_gt (ENNReal.ofReal_pos.mpr hpq.symm.pos)) ENNReal.ofReal_ne_top
    rw [hqt] at hi
    exact ha.add (hi.const_mul C)
  refine ⟨?_, ?_, hgi.congr hg_real.symm⟩
  · exact (continuous_coe_real_ereal.measurable.comp hmeas).aemeasurable.congr
      (hae.mono fun x hx => hx.1.symm)
  · filter_upwards [hae] with x hx
    change pointwiseConjugate F x (σ x) ≠ ⊤ ∧ pointwiseConjugate F x (σ x) ≠ ⊥
    rw [hx.1]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- In the complete Lebesgue convention, a.e. measurability is measurability. -/
theorem conjugate_measurable : IntegralConjugacySpecs.conjugate_measurable_type := by
  intro S E _ _ _ _ _ _ μ _ p hp F hF hg σ
  exact aemeasurable_iff_measurable.mp (conjugate_integrable p hp F hF hg σ).1

end Fiber

namespace FiniteMax
variable {S E : Type*} [Zero E]

/-- Running maximum, including the value at zero before enumerating a dense set. -/
def score (h : S → E → ℝ) (q : ℕ → E) : ℕ → S → ℝ
  | 0, x => h x 0
  | n + 1, x => max (score h q n x) (h x (q n))

/-- A finite-valued maximizing selection. Its comparisons use measurable scores. -/
def choice (h : S → E → ℝ) (q : ℕ → E) : ℕ → S → E
  | 0, _ => 0
  | n + 1, x => if score h q n x ≤ h x (q n) then q n else choice h q n x

theorem choice_score (h : S → E → ℝ) (q : ℕ → E) (n : ℕ) (x : S) :
    h x (choice h q n x) = score h q n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases he : score h q n x ≤ h x (q n)
    · simp only [choice, he, ite_true, score, max_eq_right he]
    · simp only [choice, he, ite_false, score, max_eq_left (le_of_not_ge he), ih]

theorem monotone_score (h : S → E → ℝ) (q : ℕ → E) (x : S) :
    Monotone (fun n => score h q n x) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

theorem le_score_succ (h : S → E → ℝ) (q : ℕ → E) (n : ℕ) (x : S) :
    h x (q n) ≤ score h q (n + 1) x := le_max_right _ _

theorem score_le {h : S → E → ℝ} {q : ℕ → E} {x : S} {b : ℝ}
    (hb : ∀ z, h x z ≤ b) (n : ℕ) : score h q n x ≤ b := by
  rw [← choice_score]
  exact hb _

theorem zero_le_score (h : S → E → ℝ) (q : ℕ → E) (n : ℕ) (x : S) :
    h x 0 ≤ score h q n x := (monotone_score h q x) (Nat.zero_le n)

theorem measurable_score [MeasurableSpace S] {h : S → E → ℝ}
    (hh : ∀ z, Measurable (fun x => h x z)) (q : ℕ → E) (n : ℕ) :
    Measurable (score h q n) := by
  induction n with
  | zero => exact hh 0
  | succ n ih => exact ih.max (hh _)

theorem memLp_choice [MeasurableSpace S] [NormedAddCommGroup E]
    {h : S → E → ℝ} (hh : ∀ z, Measurable (fun x => h x z))
    (q : ℕ → E) (μ : Measure S) [IsFiniteMeasure μ] (p : ℝ≥0∞) (n : ℕ) :
    MemLp (choice h q n) p μ := by
  classical
  induction n with
  | zero => exact memLp_const 0
  | succ n ih =>
    have hs := measurableSet_le (measurable_score hh q n) (hh (q n))
    have heq : choice h q (n + 1) =
        {x | score h q n x ≤ h x (q n)}.piecewise (fun _ => q n) (choice h q n) := by
      funext x
      simp only [choice, Set.piecewise]
      rfl
    rw [heq]
    exact MemLp.piecewise hs.nullMeasurableSet
        ((memLp_const (q n) : MemLp (fun _ : S => q n) p μ).restrict _)
        (ih.restrict _)

end FiniteMax

/-- Conjugation commutes with integration under the original growth assumptions. -/
theorem integral_conjugate_eq : IntegralConjugacySpecs.integral_conjugate_eq_type := by
  intro S E _ _ _ _ _ _ μ _ p hp F hF hg
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  intro σ L hL
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal (p / (p - 1))
  have hpq := Real.HolderConjugate.conjExponent hp
  let : ENNReal.HolderConjugate P Q := hpq.ennrealOfReal
  have hp₀ : P ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hpq.pos)
  let star : S → ℝ := fun x => (pointwiseConjugate F x (σ x)).toReal
  obtain ⟨_, hfinite, hstar⟩ := conjugate_integrable p hp F hF hg σ
  change Integrable star μ at hstar
  have hcoe : ∀ᵐ x ∂μ, (star x : EReal) = pointwiseConjugate F x (σ x) :=
    hfinite.mono fun x hx => EReal.coe_toReal hx.1 hx.2
  have hint (v : Lp E P μ) : Integrable (fun x => inner ℝ (σ x) (v x)) μ :=
    memLp_one_iff_integrable.mp ((innerSL ℝ).memLp_of_bilin 1 (Lp.memLp σ) (Lp.memLp v))
  have henergy (v : Lp E P μ) : Integrable (fun x => F x (v x)) μ :=
    integrable_substitution hp₀ ENNReal.ofReal_ne_top hF hg (Lp.memLp v)
  have hpoint (x : S) (hx : (star x : EReal) = pointwiseConjugate F x (σ x)) (z : E) :
      inner ℝ (σ x) z - F x z ≤ star x := by
    apply EReal.coe_le_coe_iff.mp
    rw [hx]
    exact le_iSup (fun z => ((inner ℝ (σ x) z - F x z : ℝ) : EReal)) z
  let G : Lp E P μ → WithTop ℝ := fun v =>
    (IntegralRegularitySpecs.integralFunctional μ F v : WithTop ℝ)
  have hterm (v : Lp E P μ) :
      ((L v - IntegralRegularitySpecs.integralFunctional μ F v : ℝ) : EReal) ≤
        ConvexAnalysis.Specs.conjugate G L := by
    exact ConvexAnalysis.conjugate_finite_lower_bound G v _ rfl L
  apply le_antisymm
  · change (⨆ v ∈ ConvexAnalysis.Specs.effectiveDomain G,
      ((L v - (G v).untopD 0 : ℝ) : EReal)) ≤ (∫ x, star x ∂μ : ℝ)
    apply iSup₂_le
    intro v _
    change ((L v - ∫ x, F x (v x) ∂μ : ℝ) : EReal) ≤ (∫ x, star x ∂μ : ℝ)
    apply EReal.coe_le_coe
    rw [hL v, ← integral_sub (hint v) (henergy v)]
    apply integral_mono_ae ((hint v).sub (henergy v)) hstar
    exact hcoe.mono fun x hx => hpoint x hx (v x)
  · let h : S → E → ℝ := fun x z => inner ℝ (σ x) z - F x z
    have hm (z : E) : Measurable (fun x => h x z) :=
      ((Lp.stronglyMeasurable σ).measurable.inner measurable_const).sub (hF.1 z)
    let q := denseSeq E
    let v := FiniteMax.choice h q
    let s := FiniteMax.score h q
    have hv (n : ℕ) : MemLp (v n) P μ := FiniteMax.memLp_choice hm q μ P n
    have hs (n : ℕ) : Measurable (s n) := FiniteMax.measurable_score hm q n
    have hb : ∀ᵐ x ∂μ, ∀ n, ‖s n x‖ ≤ |F x 0| + |star x| := by
      filter_upwards [hcoe] with x hx n
      have hu : s n x ≤ star x := FiniteMax.score_le (hpoint x hx) n
      have hl : -F x 0 ≤ s n x := by
        simpa [h] using FiniteMax.zero_le_score h q n x
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [le_abs_self (F x 0), abs_nonneg (star x)]
      · linarith [le_abs_self (star x), abs_nonneg (F x 0)]
    have hi0 : Integrable (fun x => F x 0) μ :=
      integrable_substitution hp₀ ENNReal.ofReal_ne_top hF hg (memLp_const 0)
    have hdom : Integrable (fun x => |F x 0| + |star x|) μ := hi0.abs.add hstar.abs
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => s n x) atTop (𝓝 (star x)) := by
      filter_upwards [hcoe, hF.2] with x hx hc
      have hbs : BddAbove (range (fun n => s n x)) :=
        ⟨star x, by rintro _ ⟨n, rfl⟩; exact FiniteMax.score_le (hpoint x hx) n⟩
      have hbf : BddAbove (range (h x)) :=
        ⟨star x, by rintro _ ⟨z, rfl⟩; exact hpoint x hx z⟩
      have heq : star x = ⨆ n, h x (q n) := by
        apply EReal.coe_injective
        exact hx.trans (pointwiseConjugate_denseSeq F x (σ x) hc hbf)
      have hsup : (⨆ n, s n x) = star x := by
        apply le_antisymm
        · exact ciSup_le fun n => FiniteMax.score_le (hpoint x hx) n
        · rw [heq]
          apply ciSup_le
          intro n
          exact (FiniteMax.le_score_succ h q n x).trans (le_ciSup hbs (n + 1))
      rw [← hsup]
      exact tendsto_atTop_ciSup (FiniteMax.monotone_score h q x) hbs
    have hDCT := tendsto_integral_of_dominated_convergence
      (fun x => |F x 0| + |star x|) (fun n => (hs n).aestronglyMeasurable)
      hdom (fun n => hb.mono fun x hx => hx n) hlim
    have hseq (n : ℕ) : ((∫ x, s n x ∂μ : ℝ) : EReal) ≤
        ConvexAnalysis.Specs.conjugate G L := by
      let vn := (hv n).toLp (v n)
      have hae : (fun x => inner ℝ (σ x) (vn x) - F x (vn x)) =ᵐ[μ] s n := by
        filter_upwards [(hv n).coeFn_toLp] with x hx
        rw [hx]
        exact FiniteMax.choice_score h q n x
      have heq : ∫ x, s n x ∂μ = L vn - IntegralRegularitySpecs.integralFunctional μ F vn := by
        rw [← integral_congr_ae hae, integral_sub (hint vn) (henergy vn), hL vn]
        rfl
      rw [heq]
      exact hterm vn
    exact le_of_tendsto (continuous_coe_real_ereal.continuousAt.tendsto.comp hDCT)
      (Eventually.of_forall hseq)

/-- The full manuscript theorem with the accepted isometric identification of the dual. -/
theorem euclidean_integral_conjugacy : IntegralConjugacySpecs.euclidean_integral_conjugacy_type := by
  intro d hd Ω hΩ hvol p hp F μ hF hg hc
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal (p / (p - 1))
  let : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let : Fact (1 ≤ Q) := ⟨ENNReal.one_le_ofReal.mpr
    (Real.HolderConjugate.conjExponent hp).symm.lt.le⟩
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hvol⟩
  have hp₀ : P ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hp))
  obtain ⟨T, hT, _⟩ := LpDuality.isometric_duality d hd Ω hΩ hvol p hp
  refine ⟨fun v => integrable_substitution hp₀ ENNReal.ofReal_ne_top hF hg (Lp.memLp v),
    convex_integralFunctional ENNReal.ofReal_ne_top hF hg hc,
    continuous_integralFunctional ENNReal.ofReal_ne_top hF hg hc, T,
    fun σ v => (hT σ v).2, ?_⟩
  intro σ
  obtain ⟨hm, hf, hi⟩ := conjugate_integrable p hp F hF hg σ
  exact ⟨hm, hf, hi, integral_conjugate_eq p hp F hF hg σ (T σ) (fun v => (hT σ v).2)⟩

/-- The complete formula also applies directly to integrands defined only on Ω. -/
theorem euclidean_subtype_integral_conjugacy :
    IntegralConjugacySpecs.euclidean_subtype_integral_conjugacy_type := by
  intro d Ω hvol p hp F μ hF hg hc
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal (p / (p - 1))
  let : ENNReal.HolderConjugate P Q :=
    (Real.HolderConjugate.conjExponent hp).ennrealOfReal
  let : Fact (1 ≤ P) := ⟨ENNReal.HolderConjugate.one_le P Q⟩
  let : Fact (1 ≤ Q) := ⟨ENNReal.HolderConjugate.one_le Q P⟩
  have hμ : μ univ ≤ volume Ω := by
    simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using
      Measure.comap_apply_le (Subtype.val : Ω → EuclideanSpace ℝ (Fin d)) volume
        nullMeasurableSet_univ
  let : IsFiniteMeasure μ := ⟨lt_of_le_of_lt hμ hvol⟩
  have hp₀ : P ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hp))
  refine ⟨fun v => ⟨integrable_substitution hp₀ ENNReal.ofReal_ne_top hF hg (Lp.memLp v),
      lpIntegralEnergy_eq hp₀ ENNReal.ofReal_ne_top hF hg v⟩,
    convex_integralFunctional ENNReal.ofReal_ne_top hF hg hc,
    continuous_integralFunctional ENNReal.ofReal_ne_top hF hg hc, ?_⟩
  intro σ
  obtain ⟨hm, hf, hi⟩ := conjugate_integrable p hp F hF hg σ
  exact ⟨hm, hf, hi, integral_conjugate_eq p hp F hF hg σ
    ((innerSL ℝ).lpPairing μ Q P σ)
    (fun v => (innerSL ℝ).lpPairing_eq_integral σ v)⟩

end VariationalNotes.Flux
