import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.SimpleApproximation
import MathGenome.Internal.RealAnalysis.D11.Ch04.ScalarOperationsLimits
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
universe u v
noncomputable section
namespace D11.Ch04.SimpleApproximation

/-! Simple means finite range, whether or not the function is measurable.
The bundled measurable interface is Mathlib's `SimpleFunc`. The approximants
below use finite dyadic roundings followed by successive maxima. Signing these
nonnegative approximants gives increasing absolute values without arithmetic
on indeterminate infinities. No measure, total-mass, or support condition occurs.
-/

def isSimple {X : Type u} {K : Type v} (f : X → K) : Prop := (Set.range f).Finite

def isNonnegativeSimple {X : Type u} (f : X → ℝ) : Prop :=
  isSimple f ∧ ∀ x, 0 ≤ f x

theorem zero_level_formula : Specs.D11.Ch04.SimpleApproximation.zero_level_formula := by
  intro X K _ f
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion,
    Set.mem_sdiff, mem_range, not_exists]
  constructor
  · rintro hx c ⟨_, hc⟩ hxc
    exact hc (hxc ▸ hx)
  · intro hx
    by_contra h
    exact hx (f x) ⟨⟨x, rfl⟩, h⟩ rfl

theorem measurable_zero_level : Specs.D11.Ch04.SimpleApproximation.measurable_zero_level := by
  intro X K _ _ f hf h
  rw [zero_level_formula]
  exact (MeasurableSet.biUnion hf.sdiff.countable
    (fun c hc => h c hc.2)).compl

theorem measurable_iff_nonzero_levels :
    Specs.D11.Ch04.SimpleApproximation.measurable_iff_nonzero_levels := by
  intro X K _ _ _ _ f hf
  constructor
  · intro h c _
    exact h (measurableSet_singleton c)
  · intro h
    have hz := measurable_zero_level f hf h
    have hall : ∀ c, MeasurableSet (f ⁻¹' {c}) := by
      intro c
      by_cases hc : c = 0
      · simpa [hc] using hz
      · exact h c hc
    exact (SimpleFunc.mk f hall hf).measurable

theorem bundled_iff : Specs.D11.Ch04.SimpleApproximation.bundled_iff := by
  intro X K _ _ _ f
  constructor
  · rintro ⟨hf, hm⟩
    exact ⟨⟨f, fun c => hm (measurableSet_singleton c), hf⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.finite_range, s.measurable⟩

theorem empty_representation : Specs.D11.Ch04.SimpleApproximation.empty_representation := by
  intro X K _ E x
  exact Finset.sum_empty

theorem zero_coefficient : Specs.D11.Ch04.SimpleApproximation.zero_coefficient := by
  intro X K _ E
  exact Set.indicator_zero (M := K) E

theorem indicator_representation : Specs.D11.Ch04.SimpleApproximation.indicator_representation := by
  classical
  intro X K _ _ _ _ f
  constructor
  · rintro ⟨hf, hm⟩
    refine ⟨hf.toFinset, fun c => f ⁻¹' {c}, ?_, ?_, ?_⟩
    · intro c _
      exact hm (measurableSet_singleton c)
    · intro c _ d _ hcd
      exact Set.disjoint_left.mpr (fun _ hc hd => hcd (hc.symm.trans hd))
    · intro x
      symm
      calc
        _ = (f ⁻¹' {f x}).indicator (fun _ => f x) x := by
          apply Finset.sum_eq_single (f x)
          · intro c _ hc
            simp [hc.symm]
          · intro hx
            exact (hx (hf.mem_toFinset.mpr ⟨x, rfl⟩)).elim
        _ = f x := by simp
  · rintro ⟨I, E, hE, _, hsum⟩
    let s : SimpleFunc X K := ∑ c ∈ I, (SimpleFunc.const X c).restrict (E c)
    have hs : (s : X → K) = f := by
      funext x
      change (∑ c ∈ I, (SimpleFunc.const X c).restrict (E c)) x = f x
      let ev : SimpleFunc X K →+ K :=
        { toFun := fun s => s x, map_zero' := rfl, map_add' := fun _ _ => rfl }
      change ev (∑ c ∈ I, (SimpleFunc.const X c).restrict (E c)) = f x
      rw [map_sum, hsum x]
      apply Finset.sum_congr rfl
      intro c hc
      change ((SimpleFunc.const X c).restrict (E c)) x = _
      rw [SimpleFunc.restrict_apply _ (hE c hc)]
      rfl
    rw [← hs]
    exact ⟨s.finite_range, s.measurable⟩


theorem nonnegative_simple_iff : Specs.D11.Ch04.SimpleApproximation.nonnegative_simple_iff := by
  intro X _ f
  constructor
  · rintro ⟨⟨hf, h0⟩, hm⟩
    let g : X → ℝ≥0 := fun x => ⟨f x, h0 x⟩
    have hg : Measurable g := hm.subtype_mk
    have hfin : (range g).Finite := by
      have heq : g = (fun r : ℝ => Real.toNNReal r) ∘ f := by
        funext x
        exact Subtype.ext (by simp [g, Real.toNNReal_of_nonneg (h0 x)])
      rw [heq]
      simpa only [Set.range_comp] using hf.image Real.toNNReal
    exact ⟨⟨g, fun c => hg (measurableSet_singleton c), hfin⟩, fun _ => rfl⟩
  · rintro ⟨s, hs⟩
    have hf : f = fun x => (s x : ℝ) := funext (fun x => (hs x).symm)
    rw [hf]
    exact ⟨⟨by
        change (range (fun x => (s x : ℝ))).Finite
        rw [Set.range_comp' ((↑) : ℝ≥0 → ℝ)]
        exact s.finite_range.image _,
      fun x => (s x).coe_nonneg⟩, s.measurable.coe_nnreal_real⟩

section Approximation
variable {X : Type u} [MeasurableSpace X]

/-- Finite dyadic rounding of a finite truncation. -/
private def rounded (f : X → ℝ≥0∞) (n : ℕ) (x : X) : ℝ :=
  (⌊(2 : ℝ)^n * (min (f x) n).toReal⌋₊ : ℝ) / (2 : ℝ)^n

omit [MeasurableSpace X] in
private lemma trunc_ne_top (f : X → ℝ≥0∞) (n : ℕ) (x : X) :
    min (f x) (n : ℝ≥0∞) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)

omit [MeasurableSpace X] in
private lemma rounded_nonneg (f : X → ℝ≥0∞) (n : ℕ) (x : X) : 0 ≤ rounded f n x := by
  unfold rounded
  positivity

omit [MeasurableSpace X] in
private lemma rounded_le_trunc (f : X → ℝ≥0∞) (n : ℕ) (x : X) :
    rounded f n x ≤ (min (f x) n).toReal := by
  unfold rounded
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^n)).mpr
  simpa [mul_comm] using Nat.floor_le
    (by positivity : 0 ≤ (2 : ℝ)^n * (min (f x) n).toReal)

omit [MeasurableSpace X] in
private lemma rounded_le (f : X → ℝ≥0∞) (n : ℕ) (x : X) :
    ENNReal.ofReal (rounded f n x) ≤ f x := by
  calc
    ENNReal.ofReal (rounded f n x) ≤ ENNReal.ofReal (min (f x) n).toReal :=
      ENNReal.ofReal_le_ofReal (rounded_le_trunc f n x)
    _ = min (f x) n := ENNReal.ofReal_toReal (trunc_ne_top f n x)
    _ ≤ f x := min_le_left _ _

omit [MeasurableSpace X] in
private lemma rounded_error (f : X → ℝ≥0∞) (n : ℕ) (x : X) :
    (min (f x) n).toReal - rounded f n x < (2 : ℝ)⁻¹ ^ n := by
  have hp : (0 : ℝ) < 2^n := by positivity
  have hfloor := Nat.lt_floor_add_one ((2 : ℝ)^n * (min (f x) n).toReal)
  unfold rounded
  rw [inv_pow, ← one_div]
  apply (lt_div_iff₀ hp).mpr
  have hmul : ((⌊(2 : ℝ)^n * (min (f x) n).toReal⌋₊ : ℝ) / 2^n) * 2^n =
      (⌊(2 : ℝ)^n * (min (f x) n).toReal⌋₊ : ℝ) := div_mul_cancel₀ _ hp.ne'
  nlinarith

private def roundedSimple (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) : SimpleFunc X ℝ where
  toFun := rounded f n
  measurableSet_fiber' c := by
    have h : Measurable (rounded f n) := by
      unfold rounded
      exact ((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp
        (((hf.min measurable_const).ennreal_toReal.const_mul _).nat_floor) :
        Measurable (fun x => (⌊(2 : ℝ)^n * (min (f x) n).toReal⌋₊ : ℝ))).div_const _
    exact h (measurableSet_singleton c)
  finite_range' := by
    let k : X → ℕ := fun x => ⌊(2 : ℝ)^n * (min (f x) n).toReal⌋₊
    have hk : ∀ x, k x ≤ 2^n*n := by
      intro x
      apply Nat.floor_le_of_le
      have htr : (min (f x) n).toReal ≤ (n : ℝ) := by
        simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top n) (min_le_right (f x) n)
      push_cast
      exact mul_le_mul_of_nonneg_left htr (by positivity)
    have hfin : (range k).Finite := (Set.finite_Iic (2^n*n)).subset (by rintro _ ⟨x, rfl⟩; exact hk x)
    exact (hfin.image (fun j : ℕ => (j : ℝ)/(2 : ℝ)^n)).subset (by rintro _ ⟨x, rfl⟩; exact ⟨k x, ⟨x, rfl⟩, rfl⟩)

/-- Taking successive maxima makes monotonicity independent of the choice of
rounding mesh. Every term remains finite, measurable, and below the target. -/
private def lowerSimple (f : X → ℝ≥0∞) (hf : Measurable f) : ℕ → SimpleFunc X ℝ
  | 0 => roundedSimple f hf 0
  | n+1 => lowerSimple f hf n ⊔ roundedSimple f hf (n+1)

private lemma lower_nonneg (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) (x : X) :
    0 ≤ lowerSimple f hf n x := by
  induction n with
  | zero => exact rounded_nonneg f 0 x
  | succ n ih => exact le_trans ih (le_max_left _ _)

private lemma lower_mono (f : X → ℝ≥0∞) (hf : Measurable f) (x : X) :
    Monotone (fun n => lowerSimple f hf n x) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

private lemma rounded_le_lower (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) (x : X) :
    rounded f n x ≤ lowerSimple f hf n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

private lemma lower_le (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) (x : X) :
    ENNReal.ofReal (lowerSimple f hf n x) ≤ f x := by
  induction n with
  | zero => exact rounded_le f 0 x
  | succ n ih =>
    change ENNReal.ofReal (max (lowerSimple f hf n x) (rounded f (n+1) x)) ≤ f x
    rw [ENNReal.ofReal_max]
    exact max_le ih (rounded_le f (n+1) x)


private lemma lower_error (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) (x : X)
    (hx : f x ≠ ⊤) (hn : f x ≤ n) :
    |lowerSimple f hf n x - (f x).toReal| < (2 : ℝ)⁻¹^n := by
  have hle : lowerSimple f hf n x ≤ (f x).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hx).mp (lower_le f hf n x)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  have h := rounded_error f n x
  rw [min_eq_left hn] at h
  have hl := rounded_le_lower f hf n x
  linarith

private lemma mesh_tendsto : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹^n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private lemma lower_tendsto_real (f : X → ℝ≥0∞) (hf : Measurable f) (x : X)
    (hx : f x ≠ ⊤) :
    Tendsto (fun n => lowerSimple f hf n x) atTop (𝓝 (f x).toReal) := by
  have he : ∀ᶠ n : ℕ in atTop, f x ≤ n := by
    obtain ⟨N, hN⟩ := exists_nat_ge (f x).toReal
    filter_upwards [eventually_ge_atTop N] with n hn
    apply (ENNReal.toReal_le_toReal hx (ENNReal.natCast_ne_top n)).mp
    simpa using hN.trans (by exact_mod_cast hn)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub mesh_tendsto) tendsto_const_nhds ?_ ?_
  · filter_upwards [he] with n hn
    have h := lower_error f hf n x hx hn
    rw [inv_pow] at h
    linarith [neg_le_abs (lowerSimple f hf n x - (f x).toReal)]
  · exact Eventually.of_forall (fun n =>
      (ENNReal.ofReal_le_iff_le_toReal hx).mp (lower_le f hf n x))

private lemma lower_tendsto (f : X → ℝ≥0∞) (hf : Measurable f) (x : X) :
    Tendsto (fun n => ENNReal.ofReal (lowerSimple f hf n x)) atTop (𝓝 (f x)) := by
  by_cases hx : f x = ⊤
  · rw [hx]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le ENNReal.tendsto_nat_nhds_top
      tendsto_const_nhds ?_ (fun _ => le_top)
    intro n
    have hr : rounded f n x = n := by
      simp only [rounded, hx, min_top_left, ENNReal.toReal_natCast]
      have hp : (2 : ℝ)^n * (n : ℝ) = ((2^n*n : ℕ) : ℝ) := by push_cast; rfl
      rw [hp, Nat.floor_natCast]
      push_cast
      field_simp
    simpa only [hr, ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (rounded_le_lower f hf n x)
  · simpa only [ENNReal.ofReal_toReal hx] using
      ENNReal.tendsto_ofReal (lower_tendsto_real f hf x hx)

theorem nonnegative_approximation : Specs.D11.Ch04.SimpleApproximation.nonnegative_approximation := by
  intro X _ f hf
  exact ⟨lowerSimple f hf, lower_nonneg f hf, lower_mono f hf,
    lower_le f hf, lower_tendsto f hf⟩


private def magnitude (f : X → EReal) (x : X) : ℝ≥0∞ :=
  (max (f x) (-f x)).toENNReal

private lemma magnitude_nonneg (a : EReal) : 0 ≤ max a (-a) := by
  rcases le_total 0 a with h | h
  · exact h.trans (le_max_left _ _)
  · exact (EReal.neg_nonneg.mpr h).trans (le_max_right _ _)

private lemma magnitude_measurable (f : X → EReal) (hf : Measurable f) :
    Measurable (magnitude f) :=
  (hf.max hf.neg).ereal_toENNReal

private def signedSimple (f : X → EReal) (hf : Measurable f) (n : ℕ) : SimpleFunc X ℝ :=
  let a := lowerSimple (magnitude f) (magnitude_measurable f hf) n
  SimpleFunc.piecewise {x | f x < 0} (measurableSet_lt hf measurable_const) (-a) a

private lemma abs_signed (f : X → EReal) (hf : Measurable f) (n : ℕ) (x : X) :
    |signedSimple f hf n x| = lowerSimple (magnitude f) (magnitude_measurable f hf) n x := by
  simp only [signedSimple, SimpleFunc.piecewise_apply, mem_ofPred_eq]
  split_ifs
  · rw [SimpleFunc.neg_apply, abs_neg, abs_of_nonneg (lower_nonneg _ _ _ _)]
  · exact abs_of_nonneg (lower_nonneg _ _ _ _)

private lemma signed_abs_le (f : X → EReal) (hf : Measurable f) (n : ℕ) (x : X) :
    ((|signedSimple f hf n x| : ℝ) : EReal) ≤ max (f x) (-f x) := by
  rw [abs_signed]
  have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    (lower_le (magnitude f) (magnitude_measurable f hf) n x)
  rw [EReal.coe_ennreal_ofReal, max_eq_left (lower_nonneg _ _ _ _),
    show (magnitude f x : EReal) = max (f x) (-f x) from
      EReal.coe_toENNReal (magnitude_nonneg (f x))] at h
  exact h

private lemma signed_abs_mono (f : X → EReal) (hf : Measurable f) (n : ℕ) (x : X) :
    |signedSimple f hf n x| ≤ |signedSimple f hf (n+1) x| := by
  simp only [abs_signed]
  exact lower_mono _ _ x (Nat.le_succ n)

private lemma signed_tendsto (f : X → EReal) (hf : Measurable f) (x : X) :
    Tendsto (fun n => (signedSimple f hf n x : EReal)) atTop (𝓝 (f x)) := by
  have h := (continuous_coe_ennreal_ereal.tendsto (magnitude f x)).comp
    (lower_tendsto (magnitude f) (magnitude_measurable f hf) x)
  have heq : ∀ n, ((ENNReal.ofReal (lowerSimple (magnitude f) (magnitude_measurable f hf) n x) :
      ℝ≥0∞) : EReal) = (lowerSimple (magnitude f) (magnitude_measurable f hf) n x : EReal) := by
    intro n
    rw [EReal.coe_ennreal_ofReal, max_eq_left (lower_nonneg _ _ _ _)]
  simp only [Function.comp_def, heq] at h
  rw [show (magnitude f x : EReal) = max (f x) (-f x) from
    EReal.coe_toENNReal (magnitude_nonneg (f x))] at h
  by_cases hx : f x < 0
  · have hmax : max (f x) (-f x) = -f x :=
      max_eq_right (hx.le.trans (EReal.neg_nonneg.mpr hx.le))
    have hn := h.neg
    rw [hmax, neg_neg] at hn
    simpa only [signedSimple, SimpleFunc.piecewise_apply, mem_ofPred_eq, hx, ite_true,
      SimpleFunc.neg_apply, EReal.coe_neg] using hn
  · have hx0 := le_of_not_gt hx
    have hmax : max (f x) (-f x) = f x :=
      max_eq_left ((EReal.neg_le_zero.mpr hx0).trans hx0)
    rw [hmax] at h
    simpa only [signedSimple, SimpleFunc.piecewise_apply, mem_ofPred_eq, hx, ite_false] using h

theorem extended_real_approximation : Specs.D11.Ch04.SimpleApproximation.extended_real_approximation := by
  intro X _ f hf
  exact ⟨signedSimple f hf, signed_abs_mono f hf, signed_abs_le f hf, signed_tendsto f hf⟩


omit [MeasurableSpace X] in
private lemma magnitude_coe (f : X → ℝ) (x : X) :
    magnitude (fun y => (f y : EReal)) x = ENNReal.ofReal |f x| := by
  unfold magnitude
  have hmax : max (f x : EReal) (-(f x : EReal)) = ((|f x| : ℝ) : EReal) := by
    rw [abs_eq_max_neg]
    exact (EReal.coe_strictMono.monotone.map_max).symm
  rw [hmax, EReal.real_coe_toENNReal]

private lemma signed_real_abs_le (f : X → ℝ) (hf : Measurable f) (n : ℕ) (x : X) :
    |signedSimple (fun y => (f y : EReal)) hf.coe_real_ereal n x| ≤ |f x| := by
  have h := signed_abs_le (fun y => (f y : EReal)) hf.coe_real_ereal n x
  have hmax : max (f x : EReal) (-(f x : EReal)) = ((|f x| : ℝ) : EReal) := by
    rw [abs_eq_max_neg]
    exact (EReal.coe_strictMono.monotone.map_max).symm
  rw [hmax, EReal.coe_le_coe_iff] at h
  exact h

theorem real_approximation : Specs.D11.Ch04.SimpleApproximation.real_approximation := by
  intro X _ f hf
  refine ⟨signedSimple (fun x => (f x : EReal)) hf.coe_real_ereal,
    signed_abs_mono _ _, signed_real_abs_le f hf, ?_⟩
  intro x
  exact EReal.tendsto_coe.mp (signed_tendsto _ _ x)

private lemma signed_real_error (f : X → ℝ) (hf : Measurable f) (n : ℕ) (x : X)
    (hn : |f x| ≤ n) :
    |signedSimple (fun y => (f y : EReal)) hf.coe_real_ereal n x - f x| < (2 : ℝ)⁻¹^n := by
  let g := magnitude (fun y => (f y : EReal))
  have hg := magnitude_measurable (fun y => (f y : EReal)) hf.coe_real_ereal
  have hfinite : g x ≠ ⊤ := by simp [g, magnitude_coe]
  have hbound : g x ≤ n := by
    simpa only [g, magnitude_coe, ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hn
  have herr := lower_error g hg n x hfinite hbound
  have hreal : (g x).toReal = |f x| := by
    rw [show g x = ENNReal.ofReal |f x| from magnitude_coe f x,
      ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [hreal] at herr
  change |signedSimple (fun y => (f y : EReal)) hf.coe_real_ereal n x - f x| < _
  simp only [signedSimple, SimpleFunc.piecewise_apply, mem_ofPred_eq,
    ← EReal.coe_zero, EReal.coe_lt_coe_iff]
  split_ifs with hx
  · change |-lowerSimple g hg n x - f x| < _
    have heq : -lowerSimple g hg n x - f x = -(lowerSimple g hg n x - |f x|) := by
      rw [abs_of_neg hx]
      ring
    rwa [heq, abs_neg]
  · simpa only [abs_of_nonneg (le_of_not_gt hx)] using herr

theorem bounded_real_uniform_approximation :
    Specs.D11.Ch04.SimpleApproximation.bounded_real_uniform_approximation := by
  intro X _ f hf hB
  obtain ⟨B, hB⟩ := hB
  refine ⟨signedSimple (fun x => (f x : EReal)) hf.coe_real_ereal,
    signed_abs_mono _ _, signed_real_abs_le f hf, ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge B
  filter_upwards [mesh_tendsto.eventually (gt_mem_nhds hε), eventually_ge_atTop N] with n hnε hn
  intro x
  have hxn : |f x| ≤ (n : ℝ) := (hB x).trans (hN.trans (by exact_mod_cast hn))
  simpa only [Real.dist_eq, abs_sub_comm] using (signed_real_error f hf n x hxn).trans hnε


private def combineComplex (r i : SimpleFunc X ℝ) : SimpleFunc X ℂ :=
  r.map Complex.ofReal + (i.map Complex.ofReal) * SimpleFunc.const X Complex.I

private lemma combineComplex_apply (r i : SimpleFunc X ℝ) (x : X) :
    combineComplex r i x = (r x : ℂ) + (i x : ℂ) * Complex.I := rfl

theorem complex_approximation : Specs.D11.Ch04.SimpleApproximation.complex_approximation := by
  intro X _ f hf
  let r := signedSimple (fun x => ((f x).re : EReal)) (Complex.continuous_re.measurable.comp hf).coe_real_ereal
  let i := signedSimple (fun x => ((f x).im : EReal)) (Complex.continuous_im.measurable.comp hf).coe_real_ereal
  refine ⟨fun n => combineComplex (r n) (i n), ?_⟩
  intro x
  have hr : Tendsto (fun n => r n x) atTop (𝓝 (f x).re) :=
    EReal.tendsto_coe.mp (signed_tendsto _ _ x)
  have hi : Tendsto (fun n => i n x) atTop (𝓝 (f x).im) :=
    EReal.tendsto_coe.mp (signed_tendsto _ _ x)
  have hc := ((Complex.continuous_ofReal.tendsto _).comp hr).add
    (((Complex.continuous_ofReal.tendsto _).comp hi).mul_const Complex.I)
  simpa only [combineComplex_apply, Function.comp_def, Complex.re_add_im] using hc

theorem bounded_complex_uniform_approximation :
    Specs.D11.Ch04.SimpleApproximation.bounded_complex_uniform_approximation := by
  intro X _ f hf hB
  obtain ⟨B, hB⟩ := hB
  obtain ⟨r, _, _, hr⟩ := bounded_real_uniform_approximation (fun x => (f x).re) (Complex.continuous_re.measurable.comp hf)
    ⟨B, fun x => (Complex.abs_re_le_norm (f x)).trans (hB x)⟩
  obtain ⟨i, _, _, hi⟩ := bounded_real_uniform_approximation (fun x => (f x).im) (Complex.continuous_im.measurable.comp hf)
    ⟨B, fun x => (Complex.abs_im_le_norm (f x)).trans (hB x)⟩
  refine ⟨fun n => combineComplex (r n) (i n), ?_⟩
  rw [Metric.tendstoUniformly_iff] at hr hi ⊢
  intro ε hε
  filter_upwards [hr (ε/2) (by positivity), hi (ε/2) (by positivity)] with n hnre hnim
  intro x
  have he : dist (f x) (combineComplex (r n) (i n) x) ≤
      dist (f x).re (r n x) + dist (f x).im (i n x) := by
    simpa [dist_eq_norm, combineComplex_apply, Real.norm_eq_abs] using
      Complex.norm_le_abs_re_add_abs_im (f x - ((r n x : ℂ) + (i n x : ℂ)*Complex.I))
  linarith [hnre x, hnim x]

end Approximation
end D11.Ch04.SimpleApproximation
