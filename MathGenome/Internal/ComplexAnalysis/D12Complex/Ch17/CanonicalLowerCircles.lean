import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.CanonicalLowerCircles
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.ExponentCountingRank
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.CanonicalFactors
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open Filter Set
open scoped Topology
namespace D12Complex.CanonicalLowerCircles
open ExponentCountingRank CanonicalFactors

theorem summable_above :
    Specs.D12Complex.Ch17.CanonicalLowerCircles.summable_above_type := by
  intro ι a ρ hloc hg s hs
  obtain ⟨u, hρu, hus⟩ := exists_between hs
  exact counting_bound_summable a hloc hus (hg u hρu)

lemma factor_differentiable {ι : Type} (a : ι → ℂ) (p : ℕ) (i : ι) :
    Differentiable ℂ (fun z => factor p (z / a i)) := by
  intro z
  exact ((factor_entire p).2 _ (mem_univ _)).comp z
    (differentiableAt_id.div_const (a i))

/-- A disk majorant outside finitely many divisor entries. -/
lemma factor_error_bound {ι : Type} (a : ι → ℂ) (p : ℕ)
    (hloc : LocallyFiniteDivisor a) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ i in cofinite, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖factor p (z / a i) - 1‖ ≤
        (6 * R ^ (p + 1)) * ‖a i‖ ^ (-((p : ℝ) + 1)) := by
  filter_upwards [(hloc (2 * R)).compl_mem_cofinite] with i hi z hz
  have ha : 2 * R < ‖a i‖ := not_le.mp hi
  have ha0 : 0 < ‖a i‖ := lt_of_le_of_lt (by positivity) ha
  have hw : ‖z / a i‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ ha0]
    linarith
  calc
    ‖factor p (z / a i) - 1‖ ≤ 6 * ‖z / a i‖ ^ (p + 1) :=
      norm_factor_sub_one_le p _ hw
    _ ≤ 6 * (R / ‖a i‖) ^ (p + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_left₀ (norm_nonneg _) (by
        rw [norm_div]; exact div_le_div_of_nonneg_right hz ha0.le) _
    _ = (6 * R ^ (p + 1)) * ‖a i‖ ^ (-((p : ℝ) + 1)) := by
      rw [div_pow, Real.rpow_neg ha0.le]
      simp only [← Nat.cast_add_one, Real.rpow_natCast]
      ring

/-- Normal convergence for any finite or infinite index set satisfying
the actual (p+1)-summability criterion. -/
lemma hasProdLocallyUniformlyOn_of_summable {ι : Type} (a : ι → ℂ) (p : ℕ)
    (hloc : LocallyFiniteDivisor a)
    (hs : Summable (fun i => ‖a i‖ ^ (-((p : ℝ) + 1)))) :
    HasProdLocallyUniformlyOn (fun i z => factor p (z / a i))
      (canonicalProduct p a) univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  have hbound := factor_error_bound a p hloc R hR.le
  have h := Summable.hasProdUniformlyOn_one_add hK (hs.mul_left (6 * R ^ (p + 1)))
    (f := fun i z => factor p (z / a i) - 1) ?_ ?_
  · unfold canonicalProduct
    simpa only [add_sub_cancel, factor] using h
  · filter_upwards [hbound] with i hi z hz
    exact hi z (by simpa using hKR hz)
  · intro i
    exact ((factor_differentiable a p i).continuous.sub continuous_const).continuousOn

lemma product_entire_of_summable {ι : Type} (a : ι → ℂ) (p : ℕ)
    (hloc : LocallyFiniteDivisor a)
    (hs : Summable (fun i => ‖a i‖ ^ (-((p : ℝ) + 1)))) :
    HolomorphicOn univ (canonicalProduct p a) := by
  have hh := hasProdLocallyUniformlyOn_of_summable a p hloc hs
  have hd := hh.differentiableOn (Eventually.of_forall fun S : Finset ι =>
    (Differentiable.fun_finsetProd (fun i _ => factor_differentiable a p i)).differentiableOn)
    isOpen_univ
  exact ⟨isOpen_univ, fun z _ => hd.differentiableAt (isOpen_univ.mem_nhds (mem_univ z))⟩

lemma product_eq_zero_iff_of_summable {ι : Type} (a : ι → ℂ) (p : ℕ)
    (hloc : LocallyFiniteDivisor a) (hne : ∀ i, a i ≠ 0)
    (hs : Summable (fun i => ‖a i‖ ^ (-((p : ℝ) + 1)))) (z : ℂ) :
    canonicalProduct p a z = 0 ↔ ∃ i, z = a i := by
  have herr : Summable (fun i => ‖factor p (z / a i) - 1‖) := by
    apply (hs.mul_left (6 * ‖z‖ ^ (p + 1))).of_norm_bounded_eventually
    filter_upwards [factor_error_bound a p hloc ‖z‖ (norm_nonneg z)] with i hi
    simpa only [norm_norm] using hi z le_rfl
  have hf : ∀ i, factor p (z / a i) = 0 ↔ z = a i := by
    intro i
    rw [factor_eq_zero_iff, div_eq_one_iff_eq (hne i)]
  constructor
  · intro hz
    by_contra h
    have hall : ∀ i, factor p (z / a i) ≠ 0 := by
      intro i hi
      exact h ⟨i, (hf i).mp hi⟩
    have hnon := tprod_one_add_ne_zero_of_summable
      (f := fun i => factor p (z / a i) - 1)
      (by simpa only [add_sub_cancel] using hall) herr
    exact hnon (by simpa only [add_sub_cancel, canonicalProduct, factor] using hz)
  · rintro ⟨i, hi⟩
    exact (hasProd_zero_of_exists_eq_zero ⟨i, (hf i).mpr hi⟩).tprod_eq

theorem canonical_product_converges :
    Specs.D12Complex.Ch17.CanonicalLowerCircles.canonical_product_converges_type := by
  intro ι a ρ _ hloc hne hg
  have hs := summable_above a ρ hloc hg ((⌊ρ⌋₊ : ℝ) + 1) (Nat.lt_floor_add_one ρ)
  exact ⟨hasProdLocallyUniformlyOn_of_summable a ⌊ρ⌋₊ hloc hs,
    product_entire_of_summable a ⌊ρ⌋₊ hloc hs,
    product_eq_zero_iff_of_summable a ⌊ρ⌋₊ hloc hne hs⟩

/-- Comparing two inverse powers inside a disk. This replaces the near
dyadic-shell estimate in the source proof once an s-sum is known. -/
lemma inverse_power_le_near {x R q s : ℝ} (hx : 0 < x) (hxR : x ≤ R)
    (hqs : q ≤ s) :
    x ^ (-q) ≤ R ^ (s - q) * x ^ (-s) := by
  calc
    x ^ (-q) = x ^ (s - q) * x ^ (-s) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx.le hxR (sub_nonneg.mpr hqs))
      (Real.rpow_nonneg hx.le _)

/-- The analogous comparison outside a disk uses a nonpositive exponent. -/
lemma inverse_power_le_far {x R q s : ℝ} (hR : 0 < R) (hRx : R ≤ x)
    (hsq : s ≤ q) :
    x ^ (-q) ≤ R ^ (s - q) * x ^ (-s) := by
  have hx := hR.trans_le hRx
  calc
    x ^ (-q) = x ^ (s - q) * x ^ (-s) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hR hRx (sub_nonpos.mpr hsq))
      (Real.rpow_nonneg hx.le _)

lemma inverse_power_sum_bound {ι : Type} (a : ι → ℂ) (S : Set ι)
    {q s B : ℝ} (hs : Summable (fun i => ‖a i‖ ^ (-s))) (hB : 0 ≤ B)
    (hb : ∀ i : S, ‖a i.val‖ ^ (-q) ≤ B * ‖a i.val‖ ^ (-s)) :
    Summable (fun i : S => ‖a i.val‖ ^ (-q)) ∧
    (∑' i : S, ‖a i.val‖ ^ (-q)) ≤ B * ∑' i, ‖a i‖ ^ (-s) := by
  have hmajor := (hs.subtype (fun i => i ∈ S)).mul_left B
  have hminor := hmajor.of_nonneg_of_le
    (fun i => Real.rpow_nonneg (norm_nonneg (a i.val)) _) hb
  refine ⟨hminor, ?_⟩
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.coe_injective
    (fun i _ => mul_nonneg hB (Real.rpow_nonneg (norm_nonneg _) _))
    hb hminor (hs.mul_left B)

lemma near_inverse_power_sum {ι : Type} (a : ι → ℂ) (hne : ∀ i, a i ≠ 0)
    {q s R : ℝ} (hR : 0 < R) (hqs : q ≤ s)
    (hs : Summable (fun i => ‖a i‖ ^ (-s))) :
    (∑' i : {i // ‖a i‖ ≤ R}, ‖a i.val‖ ^ (-q)) ≤
      R ^ (s - q) * ∑' i, ‖a i‖ ^ (-s) := by
  exact (inverse_power_sum_bound a {i | ‖a i‖ ≤ R} hs
    (Real.rpow_nonneg hR.le _) (fun i =>
      inverse_power_le_near (norm_pos_iff.mpr (hne i.val)) i.property hqs)).2

lemma far_inverse_power_sum {ι : Type} (a : ι → ℂ)
    {q s R : ℝ} (hR : 0 < R) (hsq : s ≤ q)
    (hs : Summable (fun i => ‖a i‖ ^ (-s))) :
    (∑' i : {i // R < ‖a i‖}, ‖a i.val‖ ^ (-q)) ≤
      R ^ (s - q) * ∑' i, ‖a i‖ ^ (-s) := by
  exact (inverse_power_sum_bound a {i | R < ‖a i‖} hs
    (Real.rpow_nonneg hR.le _) (fun i =>
      inverse_power_le_far hR i.property.le hsq)).2

/-- The far logarithmic tail converges absolutely, with a uniform disk
bound. In applications L = 4R and ‖z‖ ≤ 2R. -/
lemma far_logarithms_bound {ι : Type} (a : ι → ℂ) (p : ℕ)
    {s L : ℝ} (hL : 0 < L) (hsp : s ≤ (p : ℝ) + 1)
    (hs : Summable (fun i => ‖a i‖ ^ (-s))) (z : ℂ) (hz : ‖z‖ ≤ L / 2) :
    Summable (fun i : {i // L < ‖a i‖} => logFactor p (z / a i.val)) ∧
    ‖∑' i : {i // L < ‖a i‖}, logFactor p (z / a i.val)‖ ≤
      (2 * ‖z‖ ^ (p + 1)) * (L ^ (s - ((p : ℝ) + 1)) * ∑' i, ‖a i‖ ^ (-s)) := by
  have hp := inverse_power_sum_bound a {i | L < ‖a i‖} hs
    (Real.rpow_nonneg hL.le _) (fun i => inverse_power_le_far hL i.property.le hsp)
  have hb (i : {i // L < ‖a i‖}) :
      ‖logFactor p (z / a i.val)‖ ≤
        (2 * ‖z‖ ^ (p + 1)) * ‖a i.val‖ ^ (-((p : ℝ) + 1)) := by
    have ha := hL.trans i.property
    have hw : ‖z / a i.val‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ ha]
      linarith [i.property]
    calc
      _ ≤ 2 * ‖z / a i.val‖ ^ (p + 1) := norm_logFactor_le p _ hw
      _ = _ := by
        rw [norm_div, div_pow, Real.rpow_neg ha.le]
        simp only [← Nat.cast_add_one, Real.rpow_natCast]
        ring
  have hmajor := hp.1.mul_left (2 * ‖z‖ ^ (p + 1))
  have hnorm := hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hnorm.of_norm, ?_⟩
  calc
    _ ≤ ∑' i : {i // L < ‖a i‖}, ‖logFactor p (z / a i.val)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i : {i // L < ‖a i‖},
        (2 * ‖z‖ ^ (p + 1)) * ‖a i.val‖ ^ (-((p : ℝ) + 1)) :=
      hnorm.tsum_le_tsum hb hmajor
    _ = (2 * ‖z‖ ^ (p + 1)) *
        ∑' i : {i // L < ‖a i‖}, ‖a i.val‖ ^ (-((p : ℝ) + 1)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hp.2 (by positivity)

/-- Exponentiation of the convergent branch logs gives the actual product
of the far factors. No principal logarithm of that product is assumed. -/
lemma far_hasProd {ι : Type} (a : ι → ℂ) (p : ℕ)
    {s L : ℝ} (hL : 0 < L) (hsp : s ≤ (p : ℝ) + 1)
    (hs : Summable (fun i => ‖a i‖ ^ (-s))) (z : ℂ) (hz : ‖z‖ ≤ L / 2) :
    HasProd (fun i : {i // L < ‖a i‖} => factor p (z / a i.val))
      (Complex.exp (∑' i : {i // L < ‖a i‖}, logFactor p (z / a i.val))) := by
  have hsum := (far_logarithms_bound a p hL hsp hs z hz).1.hasSum
  have he : HasProd
      (fun i : {i // L < ‖a i‖} => Complex.exp (logFactor p (z / a i.val)))
      (Complex.exp (∑' i : {i // L < ‖a i‖}, logFactor p (z / a i.val))) := by
    simpa only [← Complex.exp_eq_exp_ℂ, Function.comp_def] using hsum.exp
  apply he.congr
  intro S
  apply Finset.prod_congr rfl
  intro i _
  apply exp_logFactor
  rw [norm_div, div_lt_one (hL.trans i.property)]
  linarith [i.property]

/-- The finite near product and the exponential tail multiply to the
canonical product even when one of the near factors vanishes. -/
lemma product_eq_near_mul_exp {ι : Type} (a : ι → ℂ) (p : ℕ)
    (hloc : LocallyFiniteDivisor a) {s L : ℝ} (hL : 0 < L)
    (hsp : s ≤ (p : ℝ) + 1) (hs : Summable (fun i => ‖a i‖ ^ (-s)))
    (z : ℂ) (hz : ‖z‖ ≤ L / 2) :
    canonicalProduct p a z =
      (∏ i ∈ (hloc L).toFinset, factor p (z / a i)) *
        Complex.exp (∑' i : {i // L < ‖a i‖}, logFactor p (z / a i.val)) := by
  classical
  unfold LocallyFiniteDivisor at hloc
  let S := (hloc L).toFinset
  have hSc : (S : Set ι)ᶜ = {i | L < ‖a i‖} := by
    ext i
    simp only [Set.mem_compl_iff, Finset.mem_coe, S, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, not_le]
  have ht : HasProd (fun i : ((S : Set ι)ᶜ : Set ι) => factor p (z / a i.val))
      (Complex.exp (∑' i : {i // L < ‖a i‖}, logFactor p (z / a i.val))) := by
    rw [hSc]
    exact far_hasProd a p hL hsp hs z hz
  exact ((S.hasProd (fun i => factor p (z / a i))).mul_compl ht).tprod_eq

lemma log_norm_product_eq_near_add_re {ι : Type} (a : ι → ℂ) (p : ℕ)
    (hloc : LocallyFiniteDivisor a) {s L : ℝ} (hL : 0 < L)
    (hsp : s ≤ (p : ℝ) + 1) (hs : Summable (fun i => ‖a i‖ ^ (-s)))
    (z : ℂ) (hz : ‖z‖ ≤ L / 2)
    (hn : (∏ i ∈ (hloc L).toFinset, factor p (z / a i)) ≠ 0) :
    Real.log ‖canonicalProduct p a z‖ =
      Real.log ‖∏ i ∈ (hloc L).toFinset, factor p (z / a i)‖ +
        (∑' i : {i // L < ‖a i‖}, logFactor p (z / a i.val)).re := by
  rw [product_eq_near_mul_exp a p hloc hL hsp hs z hz, norm_mul,
    Complex.norm_exp, Real.log_mul (norm_ne_zero_iff.mpr hn) (Real.exp_ne_zero _),
    Real.log_exp]

/-- The far contribution is O(R^s) on the whole disk of radius 2R.
The constant is independent of R and z. -/
lemma far_logarithms_le_power {ι : Type} (a : ι → ℂ) (p : ℕ) (s : ℝ)
    (hsp : s ≤ (p : ℝ) + 1) (hs : Summable (fun i => ‖a i‖ ^ (-s))) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ ≤ 2 * R →
      ‖∑' i : {i // 4 * R < ‖a i‖}, logFactor p (z / a i.val)‖ ≤ C * R ^ s := by
  let A := ∑' i, ‖a i‖ ^ (-s)
  have hA : 0 ≤ A := tsum_nonneg (fun i => Real.rpow_nonneg (norm_nonneg _) _)
  let B : ℝ := 2 * 2 ^ (p + 1) * 4 ^ (s - ((p : ℝ) + 1)) * A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + 1, by linarith, ?_⟩
  intro R hR z hz
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hb := (far_logarithms_bound a p (by positivity : 0 < 4 * R)
    hsp hs z (by linarith)).2
  have heq : (2 * (2 * R) ^ (p + 1)) *
      ((4 * R) ^ (s - ((p : ℝ) + 1)) * A) = B * R ^ s := by
    calc
      _ = B * (R ^ (p + 1) * R ^ (s - ((p : ℝ) + 1))) := by
        rw [mul_pow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hR0.le]
        dsimp [B]
        ring
      _ = B * R ^ s := by
        congr 1
        rw [← Real.rpow_natCast R (p + 1), ← Real.rpow_add hR0]
        congr 1
        push_cast
        ring
  calc
    _ ≤ (2 * (2 * R) ^ (p + 1)) *
        ((4 * R) ^ (s - ((p : ℝ) + 1)) * A) := by
      apply hb.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _) (by norm_num))
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) hA)
    _ = B * R ^ s := heq
    _ ≤ (B + 1) * R ^ s := mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg hR0.le _)

/-- A finite union of intervals cannot cover a longer interval. -/
lemma exists_radius_separated_finset {ι : Type} (S : Finset ι) (b : ι → ℝ)
    {R δ : ℝ} (hδ : 0 ≤ δ) (hR : 2 * δ * S.card < R) :
    ∃ r ∈ Set.Icc R (2 * R), ∀ i ∈ S, δ ≤ |r - b i| := by
  classical
  by_contra! h
  have hcover : Set.Icc R (2 * R) ⊆ ⋃ i ∈ S, Metric.ball (b i) δ := by
    intro r hr
    obtain ⟨i, hi, hir⟩ := h r hr
    exact Set.mem_iUnion₂.mpr ⟨i, hi, by simpa [Real.dist_eq] using hir⟩
  have hv := (MeasureTheory.measure_mono (μ := MeasureTheory.volume) hcover).trans
    (MeasureTheory.measure_biUnion_finset_le S (fun i => Metric.ball (b i) δ))
  simp only [Real.volume_Icc, Real.volume_ball, Finset.sum_const, nsmul_eq_mul] at hv
  rw [show 2 * R - R = R by ring] at hv
  have hv' : ENNReal.ofReal R ≤ ENNReal.ofReal (2 * δ * S.card) := by
    simpa [ENNReal.ofReal_mul, hδ, mul_comm, mul_left_comm] using hv
  exact (not_le.mpr hR) ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hv')

/-- Large annuli contain a circle with a uniform radial gap from all near zeros. -/
lemma separated_radii {ι : Type} (a : ι → ℂ)
    (hloc : LocallyFiniteDivisor a) (hne : ∀ i, a i ≠ 0)
    {s : ℝ} (hs0 : 0 < s) (hs : Summable (fun i => ‖a i‖ ^ (-s))) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ r ∈ Set.Icc R (2 * R), ∀ i, ‖a i‖ ≤ 4 * R → R ^ (-s) ≤ |r - ‖a i‖| := by
  classical
  obtain ⟨A, hA, hcount⟩ := summable_bounds_counting a hloc hne hs0 hs
  refine ⟨2 * A * 4 ^ s + 1, by nlinarith [mul_nonneg hA (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) s)], ?_⟩
  intro R hR
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  let S := (hloc (4 * R)).toFinset
  have hcard : S.card = countingFunction a (4 * R) := by
    exact (Set.ncard_eq_toFinset_card _ (hloc (4 * R))).symm
  have hlen : 2 * R ^ (-s) * S.card < R := by
    calc
      _ ≤ 2 * R ^ (-s) * (A * (4 * R) ^ s) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (hcount _ (by positivity)) (by positivity)
      _ = 2 * A * 4 ^ s := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hR0.le]
        have he : R ^ (-s) * R ^ s = 1 := by rw [← Real.rpow_add hR0]; simp
        calc
          _ = 2 * A * 4 ^ s * (R ^ (-s) * R ^ s) := by ring
          _ = _ := by rw [he, mul_one]
      _ < R := by linarith
  obtain ⟨r, hr, hgap⟩ := exists_radius_separated_finset S (fun i => ‖a i‖)
    (Real.rpow_nonneg hR0.le _) hlen
  exact ⟨r, hr, fun i hi => hgap i ((hloc (4 * R)).mem_toFinset.mpr hi)⟩

/-- Finite near sums inherit a quantitative bound from the convergent s-sum. -/
lemma near_power_finset_bound {ι : Type} (a : ι → ℂ) (hne : ∀ i, a i ≠ 0)
    {s L q : ℝ} (hL : 0 < L) (hqs : q ≤ s)
    (hs : Summable (fun i => ‖a i‖ ^ (-s))) (S : Finset ι)
    (hS : ∀ i ∈ S, ‖a i‖ ≤ L) :
    (∑ i ∈ S, ‖a i‖ ^ (-q)) ≤ L ^ (s - q) * ∑' i, ‖a i‖ ^ (-s) := by
  calc
    _ ≤ ∑ i ∈ S, L ^ (s - q) * ‖a i‖ ^ (-s) :=
      Finset.sum_le_sum (fun i hi => inverse_power_le_near
        (norm_pos_iff.mpr (hne i)) (hS i hi) hqs)
    _ = L ^ (s - q) * ∑ i ∈ S, ‖a i‖ ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum S (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))
      (Real.rpow_nonneg hL.le _)

/-- The sum of all exponential corrections of near factors is O(R^s). -/
lemma near_corrections_bound {ι : Type} (a : ι → ℂ) (p : ℕ)
    (hne : ∀ i, a i ≠ 0) {s : ℝ} (hps : (p : ℝ) ≤ s)
    (hs : Summable (fun i => ‖a i‖ ^ (-s))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 < R → ∀ S : Finset ι,
      (∀ i ∈ S, ‖a i‖ ≤ 4 * R) → ∀ z : ℂ, ‖z‖ ≤ 2 * R →
      ‖∑ i ∈ S, ∑ k ∈ Finset.range p,
        (z / a i) ^ (k + 1) / (k + 1 : ℂ)‖ ≤ B * R ^ s := by
  let A := ∑' i, ‖a i‖ ^ (-s)
  have hA : 0 ≤ A := tsum_nonneg (fun i => Real.rpow_nonneg (norm_nonneg _) _)
  let b := fun k : ℕ => 2 ^ (k + 1) * 4 ^ (s - (k + 1 : ℕ)) * A
  refine ⟨∑ k ∈ Finset.range p, b k, Finset.sum_nonneg (fun k _ => by dsimp [b]; positivity), ?_⟩
  intro R hR S hS z hz
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ k ∈ Finset.range p, ‖∑ i ∈ S, (z / a i) ^ (k + 1) / (k + 1 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range p, b k * R ^ s := by
      apply Finset.sum_le_sum
      intro k hk
      have hks : (k + 1 : ℕ) ≤ p := Finset.mem_range.mp hk
      have hqs : ((k + 1 : ℕ) : ℝ) ≤ s := (by exact_mod_cast hks :
        ((k + 1 : ℕ) : ℝ) ≤ (p : ℝ)).trans hps
      calc
        _ ≤ ∑ i ∈ S, ‖(z / a i) ^ (k + 1) / (k + 1 : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ S, (2 * R) ^ (k + 1) * ‖a i‖ ^ (-((k + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_div, norm_pow, ← Nat.cast_add_one, Complex.norm_natCast]
          calc
            _ ≤ ‖z / a i‖ ^ (k + 1) := div_le_self (by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
            _ ≤ (2 * R) ^ (k + 1) * ‖a i‖ ^ (-((k + 1 : ℕ) : ℝ)) := by
              rw [norm_div, div_pow, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)
        _ = (2 * R) ^ (k + 1) * ∑ i ∈ S, ‖a i‖ ^ (-((k + 1 : ℕ) : ℝ)) := by rw [Finset.mul_sum]
        _ ≤ (2 * R) ^ (k + 1) * ((4 * R) ^ (s - (k + 1 : ℕ)) * A) :=
          mul_le_mul_of_nonneg_left (near_power_finset_bound a hne (by positivity) hqs hs S hS) (by positivity)
        _ = b k * R ^ s := by
          rw [mul_pow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hR.le]
          have he : R ^ (k + 1) * R ^ (s - (k + 1 : ℕ)) = R ^ s := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hR]
            congr 1
            ring
          dsimp [b]
          calc
            _ = (2 ^ (k + 1) * 4 ^ (s - (k + 1 : ℕ)) * A) *
              (R ^ (k + 1) * R ^ (s - (k + 1 : ℕ))) := by ring
            _ = _ := by rw [he]
    _ = _ := by rw [Finset.sum_mul]

/-- Radial separation supplies a lower bound for each linear factor. -/
lemma log_linear_factor_lower {a z : ℂ} {R r s : ℝ} (ha : a ≠ 0)
    (hR : 0 < R) (haR : ‖a‖ ≤ 4 * R) (hz : ‖z‖ = r)
    (hgap : R ^ (-s) ≤ |r - ‖a‖|) :
    1 - z / a ≠ 0 ∧
      -(s + 1) * Real.log R - Real.log 4 ≤ Real.log ‖1 - z / a‖ := by
  have ha0 := norm_pos_iff.mpr ha
  have hsep : R ^ (-s) ≤ ‖a - z‖ := by
    calc
      _ ≤ |‖z‖ - ‖a‖| := by rwa [hz]
      _ ≤ ‖z - a‖ := abs_norm_sub_norm_le z a
      _ = ‖a - z‖ := norm_sub_rev _ _
  have he : 1 - z / a = (a - z) / a := by field_simp
  have hb : R ^ (-s) / (4 * R) ≤ ‖1 - z / a‖ := by
    rw [he, norm_div]
    exact div_le_div₀ (norm_nonneg _) hsep ha0 haR
  have hpos : 0 < R ^ (-s) / (4 * R) := by positivity
  refine ⟨norm_pos_iff.mp (hpos.trans_le hb), ?_⟩
  calc
    _ = Real.log (R ^ (-s) / (4 * R)) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_rpow hR,
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hR.ne']
      ring
    _ ≤ _ := Real.log_le_log hpos hb

/-- On separated circles, the logarithm of the finite near product has the
expected R^s log R lower bound, uniformly in the angular variable. -/
lemma near_product_lower {ι : Type} (a : ι → ℂ) (p : ℕ)
    (hloc : LocallyFiniteDivisor a) (hne : ∀ i, a i ≠ 0)
    {s : ℝ} (hs0 : 0 < s) (hps : (p : ℝ) ≤ s)
    (hs : Summable (fun i => ‖a i‖ ^ (-s))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 1 ≤ R → ∀ r ∈ Set.Icc R (2 * R),
      (∀ i, ‖a i‖ ≤ 4 * R → R ^ (-s) ≤ |r - ‖a i‖|) →
      ∀ z : ℂ, ‖z‖ = r →
        (∏ i ∈ (hloc (4 * R)).toFinset, factor p (z / a i)) ≠ 0 ∧
        -D * R ^ s * (1 + Real.log R) ≤
          Real.log ‖∏ i ∈ (hloc (4 * R)).toFinset, factor p (z / a i)‖ := by
  classical
  obtain ⟨A, hA, hcount⟩ := summable_bounds_counting a hloc hne hs0 hs
  obtain ⟨B, hB, hcorr⟩ := near_corrections_bound a p hne hps hs
  let H := A * 4 ^ s
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let K := s + 1 + Real.log 4
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; linarith
  refine ⟨H * K + B, by positivity, ?_⟩
  intro R hR r hr hgap z hz
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hRs : 0 ≤ R ^ s := Real.rpow_nonneg hR0.le _
  let S := (hloc (4 * R)).toFinset
  have hS (i) (hi : i ∈ S) : ‖a i‖ ≤ 4 * R := (hloc (4 * R)).mem_toFinset.mp hi
  have hlin (i) (hi : i ∈ S) := log_linear_factor_lower (hne i) hR0 (hS i hi) hz (hgap i (hS i hi))
  have hn (i) (hi : i ∈ S) : factor p (z / a i) ≠ 0 := by
    apply (factor_eq_zero_iff p _).not.mpr
    exact fun h => (hlin i hi).1 (by rw [h]; simp)
  refine ⟨Finset.prod_ne_zero_iff.mpr hn, ?_⟩
  have hcard : (S.card : ℝ) ≤ H * R ^ s := by
    have he : S.card = countingFunction a (4 * R) :=
      (Set.ncard_eq_toFinset_card _ (hloc (4 * R))).symm
    rw [he]
    convert hcount (4 * R) (by positivity) using 1
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hR0.le]
    dsimp [H]
    ring
  have hlinear : -H * R ^ s * ((s + 1) * Real.log R + Real.log 4) ≤
      ∑ i ∈ S, Real.log ‖1 - z / a i‖ := by
    calc
      _ ≤ (S.card : ℝ) * (-(s + 1) * Real.log R - Real.log 4) := by
        have := mul_le_mul_of_nonneg_right hcard
          (show 0 ≤ (s + 1) * Real.log R + Real.log 4 by positivity)
        nlinarith
      _ = ∑ i ∈ S, (-(s + 1) * Real.log R - Real.log 4) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => (hlin i hi).2)
  have hc := hcorr R hR0 S hS z (by rw [hz]; exact hr.2)
  have hcre : -B * R ^ s ≤
      (∑ i ∈ S, ∑ k ∈ Finset.range p, (z / a i) ^ (k + 1) / (k + 1 : ℂ)).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm
      (∑ i ∈ S, ∑ k ∈ Finset.range p, (z / a i) ^ (k + 1) / (k + 1 : ℂ)))).1
    linarith
  have heq : Real.log ‖∏ i ∈ S, factor p (z / a i)‖ =
      (∑ i ∈ S, Real.log ‖1 - z / a i‖) +
      (∑ i ∈ S, ∑ k ∈ Finset.range p, (z / a i) ^ (k + 1) / (k + 1 : ℂ)).re := by
    rw [norm_prod, Real.log_prod (fun i hi => norm_ne_zero_iff.mpr (hn i hi))]
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [factor, Specs.D12Complex.Ch16.CanonicalFactors.factor_value, norm_mul,
      Complex.norm_exp, Real.log_mul (norm_ne_zero_iff.mpr ((hlin i hi).1))
        (Real.exp_ne_zero _), Real.log_exp]
  change -((H * K + B)) * R ^ s * (1 + Real.log R) ≤ Real.log ‖∏ i ∈ S, factor p (z / a i)‖
  rw [heq]
  have hab : (s + 1) * Real.log R + Real.log 4 ≤ K * (1 + Real.log R) := by
    dsimp [K]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hab (mul_nonneg hH hRs)
  have hb := mul_nonneg (mul_nonneg hB hRs) hlogR
  nlinarith

/-- A positive gap between exponents absorbs the logarithmic loss. -/
lemma power_log_absorb {s t D E R : ℝ} (hst : s < t) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hR : 1 ≤ R) :
    D * R ^ s * (1 + Real.log R) + E * R ^ s ≤
      (D * (1 + 1 / (t - s)) + E) * R ^ t := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hpow : R ^ s ≤ R ^ t := Real.rpow_le_rpow_of_exponent_le hR hst.le
  have hlog : R ^ s * Real.log R ≤ R ^ t / (t - s) := by
    calc
      _ ≤ R ^ s * (R ^ (t - s) / (t - s)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hR0.le (sub_pos.mpr hst))
          (Real.rpow_nonneg hR0.le _)
      _ = _ := by rw [← mul_div_assoc, ← Real.rpow_add hR0]; congr 2; ring
  have h₁ := mul_le_mul_of_nonneg_left hpow hD
  have h₂ := mul_le_mul_of_nonneg_left hpow hE
  have h₃ := mul_le_mul_of_nonneg_left hlog hD
  calc
    _ ≤ D * R ^ t + D * (R ^ t / (t - s)) + E * R ^ t := by nlinarith
    _ = _ := by ring

/-- The avoiding-circle lower estimate, uniformly at every point of each
selected circle. Finite and empty divisors use the same argument. -/
theorem lower_circles : Specs.D12Complex.Ch17.CanonicalLowerCircles.lower_circles_type := by
  classical
  intro ι a ρ hρ hloc hne hg t hρt htp
  obtain ⟨s, hρs, hst⟩ := exists_between hρt
  have hs0 : 0 < s := lt_of_le_of_lt hρ hρs
  have hps : (⌊ρ⌋₊ : ℝ) ≤ s := (Nat.floor_le hρ).trans hρs.le
  have hsp : s ≤ (⌊ρ⌋₊ : ℝ) + 1 := (hst.trans htp).le
  have hs := summable_above a ρ hloc hg s hρs
  obtain ⟨R₀, hR₀, hsep⟩ := separated_radii a hloc hne hs0 hs
  obtain ⟨D, hD, hnear⟩ := near_product_lower a ⌊ρ⌋₊ hloc hne hs0 hps hs
  obtain ⟨E, hE, hfar⟩ := far_logarithms_le_power a ⌊ρ⌋₊ s hsp hs
  let R : ℕ → ℝ := fun k => R₀ + k
  have hR (k : ℕ) : 1 ≤ R k := by dsimp [R]; linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
  have hR₀k (k : ℕ) : R₀ ≤ R k := by dsimp [R]; linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
  choose r hr hgap using fun k => hsep (R k) (hR₀k k)
  let C := D * (1 + 1 / (t - s)) + E + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r, C, hC, ?_, ?_⟩
  · apply tendsto_atTop_mono (fun k => (hr k).1)
    exact tendsto_atTop_add_const_left atTop R₀ tendsto_natCast_atTop_atTop
  · intro k
    have hR0 : 0 < R k := zero_lt_one.trans_le (hR k)
    have hr0 : 0 < r k := hR0.trans_le (hr k).1
    refine ⟨hr0, ?_, ?_⟩
    · intro i hi
      have hle : ‖a i‖ ≤ 4 * R k := by rw [hi]; linarith [(hr k).2]
      have hh := hgap k i hle
      rw [hi, sub_self, abs_zero] at hh
      exact (not_le.mpr (Real.rpow_pos_of_pos hR0 (-s))) hh
    · intro z hz
      obtain ⟨hn, hnb⟩ := hnear (R k) (hR k) (r k) (hr k) (hgap k) z hz
      have hzR : ‖z‖ ≤ 2 * R k := by rw [hz]; exact (hr k).2
      have hdecomp := product_eq_near_mul_exp a ⌊ρ⌋₊ hloc
        (by positivity : 0 < 4 * R k) hsp hs z (by linarith)
      refine ⟨?_, ?_⟩
      · rw [hdecomp]
        exact mul_ne_zero hn (Complex.exp_ne_zero _)
      · have heq := log_norm_product_eq_near_add_re a ⌊ρ⌋₊ hloc
          (by positivity : 0 < 4 * R k) hsp hs z (by linarith) hn
        have hb := hfar (R k) (hR k) z hzR
        have hre : -E * (R k) ^ s ≤
            (∑' i : {i // 4 * R k < ‖a i‖}, logFactor ⌊ρ⌋₊ (z / a i.val)).re := by
          have hh := (abs_le.mp (Complex.abs_re_le_norm
            (∑' i : {i // 4 * R k < ‖a i‖}, logFactor ⌊ρ⌋₊ (z / a i.val)))).1
          linarith
        have habs := power_log_absorb hst hD hE.le (hR k)
        have hpow : (R k) ^ t ≤ (r k) ^ t :=
          Real.rpow_le_rpow hR0.le (hr k).1 (lt_of_le_of_lt hρ hρt).le
        have hbig : (D * (1 + 1 / (t - s)) + E) * (R k) ^ t ≤ C * (r k) ^ t := by
          calc
            _ ≤ C * (R k) ^ t := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
              (Real.rpow_nonneg hR0.le _)
            _ ≤ _ := mul_le_mul_of_nonneg_left hpow hC.le
        rw [heq]
        linarith

/-- Full statement of paper.tex:2977–3016, with actual normal convergence. -/
theorem canonical_lower_circles :
    Specs.D12Complex.Ch17.CanonicalLowerCircles.canonical_lower_circles_type :=
  ⟨canonical_product_converges, lower_circles⟩

end D12Complex.CanonicalLowerCircles
