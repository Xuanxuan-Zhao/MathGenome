import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Morrey
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.MorreyEmbedding

import MathGenome.Internal.FourierSobolev.P102.Fractional.Extension
/-! Work on the supercritical fractional representative theorem.
The whole-space estimates follow from ball comparisons, dyadic summation, and
Lebesgue differentiation. The closure conclusion uses exactly the frozen
extension proposition as a premise. The closed original targets are intentionally
not declared in this conditional draft.
-/
set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
open BoundedContinuousFunction
universe u

namespace P102.Fractional.Morrey
open P102.Fractional

theorem fullNorm_eq_norm {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (u : Space 𝕜 G s p) : fullNorm u = ‖u‖ :=
  (space_norm hp u).symm

theorem fullNorm_nonneg {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Space 𝕜 G s p) : 0 ≤ fullNorm u :=
  add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg

theorem seminorm_le_fullNorm {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Space 𝕜 G s p) :
    (seminorm G s p (firstProjection u)).toReal ≤ fullNorm u :=
  le_add_of_nonneg_left (norm_nonneg _)

/-- The strict supercritical inequality gives a positive Hölder exponent. -/
theorem exponent_pos {d : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (hsp : (d : ℝ) < s * p.toReal) : 0 < exponent d s p := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  exact sub_pos.mpr ((div_lt_iff₀ hpr).mpr hsp)

theorem exponent_lt_one {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : s < 1)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) : exponent d s p < 1 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hd)
  exact (sub_lt_self s (div_pos hd0 hpr)).trans hs

/-- Any two continuous representatives of the same a.e. whole-space class
coincide everywhere, independently of the quantitative bounds. -/
theorem continuous_representative_unique {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {u : Domain d → 𝕜} {f g : Domain d → 𝕜}
    (hf : Continuous f) (hg : Continuous g)
    (hfu : f =ᵐ[volume] u) (hgu : g =ᵐ[volume] u) : f = g :=
  Measure.eq_of_ae_eq (hfu.trans hgu.symm) hf hg

theorem bounded_representative_unique {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {u : Domain d → 𝕜} {f g : Domain d →ᵇ 𝕜}
    (hfu : (f : Domain d → 𝕜) =ᵐ[volume] u)
    (hgu : (g : Domain d → 𝕜) =ᵐ[volume] u) : f = g := by
  exact DFunLike.coe_injective
    (continuous_representative_unique f.continuous g.continuous hfu hgu)

/-- A real-valued Hölder estimate gives uniform continuity on its set of
validity, with no boundedness assumption on that set. -/
theorem uniformContinuousOn_of_holder_bound {X : Type*} [PseudoMetricSpace X]
    {𝕜 : Type*} [RCLike 𝕜] {S : Set X} {f : X → 𝕜} {K a : ℝ}
    (hK : 0 ≤ K) (ha : 0 < a)
    (h : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ K * dist x y ^ a) :
    UniformContinuousOn f S := by
  let C : ℝ≥0 := ⟨K, hK⟩
  let r : ℝ≥0 := ⟨a, ha.le⟩
  have hh : HolderOnWith C r f S := by
    intro x hx y hy
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal (dist (f x) (f y)) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal (dist x y) ^ a
    rw [← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg ha.le,
      ← ENNReal.ofReal_mul C.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm]
    exact h x hx y hy
  exact hh.uniformContinuousOn ha

/-- Construction from estimates on a full-measure set. This gives recovery of
the original a.e. class as well as a pointwise bound at every point, including
points where the chosen Lp representative has no Lebesgue value. -/
theorem boundedRepresentative_of_ae_bounds {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Domain d → 𝕜) (S : Set (Domain d)) (hS : ∀ᵐ x ∂volume, x ∈ S)
    {K M a : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (ha : 0 < a)
    (hHolder : ∀ x ∈ S, ∀ y ∈ S, ‖u x - u y‖ ≤ K * dist x y ^ a)
    (hBound : ∀ x ∈ S, ‖u x‖ ≤ M) :
    ∃! f : Domain d →ᵇ 𝕜, (f : Domain d → 𝕜) =ᵐ[volume] u ∧
      (∀ x y, ‖f x - f y‖ ≤ K * dist x y ^ a) ∧ ‖f‖ ≤ M := by
  have hDense : Dense S := Measure.dense_of_ae hS
  let g : S → 𝕜 := fun x => u x
  have hg : UniformContinuous g := uniformContinuousOn_iff_restrict.mp
    (uniformContinuousOn_of_holder_bound hK ha hHolder)
  let f := hDense.extend g
  have hf : Continuous f := (hDense.uniformContinuous_extend hg).continuous
  have heq (x) (hx : x ∈ S) : f x = u x := hDense.extend_eq hg.continuous ⟨x, hx⟩
  have hNorm : ∀ x, ‖f x‖ ≤ M := by
    have hclosed : IsClosed {x | ‖f x‖ ≤ M} := isClosed_le hf.norm continuous_const
    have hsub : S ⊆ {x | ‖f x‖ ≤ M} := by
      intro x hx
      change ‖f x‖ ≤ M
      rw [heq x hx]
      exact hBound x hx
    intro x
    exact closure_minimal hsub hclosed (hDense x)
  have hEst : ∀ x y, ‖f x - f y‖ ≤ K * dist x y ^ a := by
    have hclosed : IsClosed {z : Domain d × Domain d |
        ‖f z.1 - f z.2‖ ≤ K * dist z.1 z.2 ^ a} :=
      isClosed_le ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).norm
        (continuous_const.mul ((continuous_fst.dist continuous_snd).rpow_const
          (fun _ => Or.inr ha.le)))
    intro x y
    change (x, y) ∈ {z : Domain d × Domain d |
      ‖f z.1 - f z.2‖ ≤ K * dist z.1 z.2 ^ a}
    apply closure_minimal (t := {z : Domain d × Domain d |
        ‖f z.1 - f z.2‖ ≤ K * dist z.1 z.2 ^ a}) ?_ hclosed
      (by rw [(hDense.prod hDense).closure_eq]; trivial)
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change ‖f x - f y‖ ≤ _
    rw [heq x hx, heq y hy]
    exact hHolder x hx y hy
  let F : Domain d →ᵇ 𝕜 := ofNormedAddCommGroup f hf M hNorm
  have hAE : (F : Domain d → 𝕜) =ᵐ[volume] u := hS.mono heq
  refine ⟨F, ⟨hAE, hEst, norm_ofNormedAddCommGroup_le hf hM hNorm⟩, ?_⟩
  intro F' hF'
  exact bounded_representative_unique hF'.1 hAE

/-- The first energy estimate in the ball-oscillation argument. The diagonal
has value zero on both sides. The result is an inequality of extended
integrals, so it remains valid before finiteness has been established. -/
theorem local_pair_integral_le_energy {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Domain d → 𝕜) {B : Set (Domain d)} (hB : MeasurableSet B)
    {s : ℝ} (hs : 0 ≤ s) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {R : ℝ} (_hR : 0 < R) (hdiam : ∀ x ∈ B, ∀ y ∈ B, ‖x - y‖ ≤ R) :
    (∫⁻ x in B, ∫⁻ y in B, ‖u x - u y‖ₑ ^ p.toReal) ≤
      ENNReal.ofReal R ^ ((d : ℝ) + s * p.toReal) * energy Set.univ s p u := by
  let q : ℝ := (d : ℝ) + s * p.toReal
  let A : ℝ≥0∞ := ENNReal.ofReal R ^ q
  let F : Domain d → Domain d → ℝ≥0∞ := fun x y =>
    if x = y then 0 else ‖u x - u y‖ₑ ^ p.toReal /
      ENNReal.ofReal ‖x - y‖ ^ q
  have hq : 0 ≤ q := add_nonneg (Nat.cast_nonneg _) (mul_nonneg hs ENNReal.toReal_nonneg)
  have hA : A ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq ENNReal.ofReal_ne_top
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hpoint (x) (hx : x ∈ B) (y) (hy : y ∈ B) :
      ‖u x - u y‖ₑ ^ p.toReal ≤ A * F x y := by
    by_cases hxy : x = y
    · simp [F, hxy, ENNReal.zero_rpow_of_pos hpr]
    have hn : ENNReal.ofReal ‖x - y‖ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).ne'
    have hden0 : ENNReal.ofReal ‖x - y‖ ^ q ≠ 0 := by positivity
    have hdent : ENNReal.ofReal ‖x - y‖ ^ q ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hq ENNReal.ofReal_ne_top
    calc
      ‖u x - u y‖ₑ ^ p.toReal = ENNReal.ofReal ‖x - y‖ ^ q * F x y := by
        simp only [F, ite_eq_right_iff.mpr (fun h => (hxy h).elim),
          ENNReal.mul_div_cancel hden0 hdent]
      _ ≤ A * F x y := by
        gcongr
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hdiam x hx y hy)) hq
  calc
    (∫⁻ x in B, ∫⁻ y in B, ‖u x - u y‖ₑ ^ p.toReal) ≤
        ∫⁻ x in B, ∫⁻ y in B, A * F x y := by
      apply setLIntegral_mono' hB
      intro x hx
      exact setLIntegral_mono' hB (fun y hy => hpoint x hx y hy)
    _ = A * ∫⁻ x in B, ∫⁻ y in B, F x y := by
      simp_rw [lintegral_const_mul' A _ hA]
    _ ≤ A * ∫⁻ x, ∫⁻ y, F x y := by
      apply mul_le_mul_right
      exact (lintegral_mono (fun x => setLIntegral_le_lintegral B (F x))).trans
        (setLIntegral_le_lintegral B _)
    _ = _ := by simp only [energy, domainMeasure, Measure.restrict_univ]; rfl

theorem closedBall_pair_integral_le_energy {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Domain d → 𝕜) {s : ℝ} (hs : 0 ≤ s) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (c : Domain d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x in Metric.closedBall c r, ∫⁻ y in Metric.closedBall c r,
      ‖u x - u y‖ₑ ^ p.toReal) ≤
      ENNReal.ofReal (2 * r) ^ ((d : ℝ) + s * p.toReal) * energy Set.univ s p u := by
  apply local_pair_integral_le_energy u measurableSet_closedBall hs hp (mul_pos (by norm_num) hr)
  intro x hx y hy
  rw [← dist_eq_norm]
  calc
    dist x y ≤ dist x c + dist c y := dist_triangle x c y
    _ ≤ r + r := add_le_add (Metric.mem_closedBall.mp hx) (by
      rw [dist_comm]
      exact Metric.mem_closedBall.mp hy)
    _ = 2 * r := by ring

/-- Jensen on the product of the two normalized measures. -/
theorem average_sub_average_enorm_le {X Y E : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0) {f : X → E} {g : Y → E}
    (hf : Integrable f μ) (hg : Integrable g ν)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    ‖(⨍ x, f x ∂μ) - (⨍ y, g y ∂ν)‖ₑ ≤
      ((μ univ)⁻¹ * (ν univ)⁻¹ *
        ∫⁻ x, ∫⁻ y, ‖f x - g y‖ₑ ^ p.toReal ∂ν ∂μ) ^ (1 / p.toReal) := by
  let : NeZero μ := ⟨hμ⟩
  let : NeZero ν := ⟨hν⟩
  let μ' : Measure X := (μ univ)⁻¹ • μ
  let ν' : Measure Y := (ν univ)⁻¹ • ν
  have hf' : Integrable f μ' := hf.to_average
  have hg' : Integrable g ν' := hg.to_average
  have hi : Integrable (fun z : X × Y => f z.1 - g z.2) (μ'.prod ν') :=
    (hf'.comp_fst ν').sub (hg'.comp_snd μ')
  have heq : (∫ z : X × Y, f z.1 - g z.2 ∂μ'.prod ν') =
      (⨍ x, f x ∂μ) - (⨍ y, g y ∂ν) := by
    rw [integral_prod _ hi]
    simp_rw [integral_sub (integrable_const _) hg', integral_const,
      MeasureTheory.probReal_univ, one_smul]
    rw [integral_sub hf' (integrable_const _), integral_const,
      MeasureTheory.probReal_univ, one_smul]
    rfl
  rw [← heq]
  calc
    ‖∫ z : X × Y, f z.1 - g z.2 ∂μ'.prod ν'‖ₑ ≤
        ∫⁻ z : X × Y, ‖f z.1 - g z.2‖ₑ ∂μ'.prod ν' :=
      enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun z : X × Y => f z.1 - g z.2) 1 (μ'.prod ν') :=
      (eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable).symm
    _ ≤ eLpNorm (fun z : X × Y => f z.1 - g z.2) p (μ'.prod ν') :=
      eLpNorm_le_eLpNorm_of_exponent_le hp1
    _ = _ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (zero_lt_one.trans_le hp1).ne' hp
        hi.aestronglyMeasurable]
      rw [lintegral_prod _ (hi.aestronglyMeasurable.enorm.pow_const _)]
      dsimp only [μ', ν']
      simp_rw [lintegral_smul_measure, smul_eq_mul]
      rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (NeZero.ne (ν univ)))]
      congr 1
      ring

private theorem coefficient_scaling {r V q b : ℝ} {d : ℕ}
    (hr : 0 < r) (hV : 0 < V) :
    ((r ^ d * V)⁻¹ * (r ^ d * V)⁻¹ * (4 * r) ^ q) ^ b =
      (V⁻¹ * V⁻¹ * (4 : ℝ) ^ q) ^ b * r ^ ((q - 2 * d) * b) := by
  have heq : (r ^ d * V)⁻¹ * (r ^ d * V)⁻¹ * (4 * r) ^ q =
      (V⁻¹ * V⁻¹ * (4 : ℝ) ^ q) * r ^ (q - 2 * d) := by
    rw [mul_inv, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr.le]
    rw [← Real.rpow_natCast, ← Real.rpow_neg hr.le]
    calc
      _ = (V⁻¹ * V⁻¹ * (4 : ℝ) ^ q) *
        ((r ^ (-(d : ℝ)) * r ^ (-(d : ℝ))) * r ^ q) := by ring
      _ = _ := by
        rw [← Real.rpow_add hr, ← Real.rpow_add hr]
        congr 2
        ring
  rw [heq, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hr.le]

/-- The radius-independent ball-comparison coefficient. -/
def ballComparisonConstant (d : ℕ) (s : ℝ) (p : ℝ≥0∞) : ℝ :=
  ((volume.real (Metric.closedBall (0 : Domain d) (1 / 2)))⁻¹ *
    (volume.real (Metric.closedBall (0 : Domain d) (1 / 2)))⁻¹ *
    (4 : ℝ) ^ ((d : ℝ) + s * p.toReal)) ^ (1 / p.toReal)

theorem ballComparisonConstant_pos (d : ℕ) (s : ℝ) (p : ℝ≥0∞) :
    0 < ballComparisonConstant d s p := by
  have hV : 0 < volume.real (Metric.closedBall (0 : Domain d) (1 / 2)) :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by norm_num)).ne'
      (isCompact_closedBall _ _).measure_ne_top
  unfold ballComparisonConstant
  positivity

theorem ball_comparison_coefficient {d : ℕ} {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {r : ℝ} (hr : 0 < r) :
    (((volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
        (volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
        ENNReal.ofReal (4 * r) ^ ((d : ℝ) + s * p.toReal)) ^ (1 / p.toReal)).toReal =
      ballComparisonConstant d s p * r ^ exponent d s p := by
  have hV : 0 < volume.real (Metric.closedBall (0 : Domain d) (1 / 2)) :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by norm_num)).ne'
      (isCompact_closedBall _ _).measure_ne_top
  have hv : volume.real (Metric.closedBall (0 : Domain d) (r / 2)) =
      r ^ d * volume.real (Metric.closedBall (0 : Domain d) (1 / 2)) := by
    change (volume (Metric.closedBall (0 : Domain d) (r / 2))).toReal = _
    rw [show r / 2 = r * (1 / 2) by ring,
      Measure.addHaar_closedBall_mul_of_pos volume _ hr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    simp [Measure.real]
  simp only [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_ofReal (show 0 ≤ 4 * r by positivity)]
  change ((volume.real (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
    (volume.real (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
    (4 * r) ^ ((d : ℝ) + s * p.toReal)) ^ (1 / p.toReal) = _
  rw [hv, coefficient_scaling hr hV]
  change ballComparisonConstant d s p *
    r ^ (((d : ℝ) + s * p.toReal - 2 * d) * (1 / p.toReal)) = _
  congr 2
  unfold exponent
  have hp0 : p.toReal ≠ 0 := (ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp).ne'
  field_simp
  ring

/-- A single comparison covers nested scales and neighboring centers. -/
theorem ball_average_comparison_enorm {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {f : Domain d → 𝕜} (hf : LocallyIntegrable f volume)
    {s : ℝ} (hs : 0 ≤ s) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (x y : Domain d) {r t : ℝ} (hr : 0 < r)
    (ht0 : r / 2 ≤ t) (ht1 : t ≤ r) (hxy : dist x y ≤ r) :
    ‖(⨍ z in Metric.closedBall x r, f z) -
      (⨍ z in Metric.closedBall y t, f z)‖ₑ ≤
      ((volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
        (volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
        ENNReal.ofReal (4 * r) ^ ((d : ℝ) + s * p.toReal)) ^ (1 / p.toReal) *
        seminorm Set.univ s p f := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall x r)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall x r).measure_ne_top
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall y t)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall y t).measure_ne_top
  have ht : 0 < t := (half_pos hr).trans_le ht0
  let B := Metric.closedBall x (2 * r)
  have hxB : Metric.closedBall x r ⊆ B := Metric.closedBall_subset_closedBall (by linarith)
  have hyB : Metric.closedBall y t ⊆ B := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ ≤ t + r := add_le_add (Metric.mem_closedBall.mp hz) (by rwa [dist_comm])
      _ ≤ 2 * r := by linarith
  have hint : (∫⁻ a in Metric.closedBall x r, ∫⁻ b in Metric.closedBall y t,
      ‖f a - f b‖ₑ ^ p.toReal) ≤
      ENNReal.ofReal (4 * r) ^ ((d : ℝ) + s * p.toReal) * energy Set.univ s p f := by
    calc
      _ ≤ ∫⁻ a in B, ∫⁻ b in B, ‖f a - f b‖ₑ ^ p.toReal := by
        exact (lintegral_mono (fun a => lintegral_mono_set hyB)).trans
          (lintegral_mono_set hxB)
      _ ≤ _ := by
        simpa only [B, show 2 * (2 * r) = 4 * r by ring] using
          closedBall_pair_integral_le_energy f hs hp x (r := 2 * r)
            (mul_pos (by norm_num) hr)
  have hvol (c : Domain d) {v : ℝ} (hv : r / 2 ≤ v) :
      volume (Metric.closedBall (0 : Domain d) (r / 2)) ≤ volume (Metric.closedBall c v) := by
    rw [MeasureTheory.Measure.addHaar_closedBall_center volume c v]
    exact measure_mono (Metric.closedBall_subset_closedBall hv)
  have hmu : volume.restrict (Metric.closedBall x r) ≠ 0 := by
    exact mt Measure.restrict_eq_zero.mp ((Metric.measure_closedBall_pos volume x hr).ne')
  have hnu : volume.restrict (Metric.closedBall y t) ≠ 0 := by
    exact mt Measure.restrict_eq_zero.mp ((Metric.measure_closedBall_pos volume y ht).ne')
  have h := average_sub_average_enorm_le hmu hnu
    (hf.integrableOn_isCompact (isCompact_closedBall x r))
    (hf.integrableOn_isCompact (isCompact_closedBall y t)) (Fact.out : 1 ≤ p) hp
  simp only [Measure.restrict_apply_univ] at h
  calc
    _ ≤ _ := h
    _ ≤ (((volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
        (volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
        ENNReal.ofReal (4 * r) ^ ((d : ℝ) + s * p.toReal)) * energy Set.univ s p f) ^
        (1 / p.toReal) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      calc
        _ ≤ (volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
          (volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
          (ENNReal.ofReal (4 * r) ^ ((d : ℝ) + s * p.toReal) * energy Set.univ s p f) := by
            exact mul_le_mul' (mul_le_mul'
              (ENNReal.inv_le_inv.mpr (hvol x (v := r) (by linarith)))
              (ENNReal.inv_le_inv.mpr (hvol y ht0))) hint
        _ = _ := by ring
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]; rfl

/-- The ball comparison in ordinary real norms, with the precise scale exponent. -/
theorem ball_average_comparison {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {f : Domain d → 𝕜} (hf : LocallyIntegrable f volume)
    {s : ℝ} (hs : 0 ≤ s) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hfin : seminorm Set.univ s p f ≠ ∞)
    (x y : Domain d) {r t : ℝ} (hr : 0 < r)
    (ht0 : r / 2 ≤ t) (ht1 : t ≤ r) (hxy : dist x y ≤ r) :
    ‖(⨍ z in Metric.closedBall x r, f z) -
      (⨍ z in Metric.closedBall y t, f z)‖ ≤
      ballComparisonConstant d s p * (seminorm Set.univ s p f).toReal *
        r ^ exponent d s p := by
  have hc : (((volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
        (volume (Metric.closedBall (0 : Domain d) (r / 2)))⁻¹ *
        ENNReal.ofReal (4 * r) ^ ((d : ℝ) + s * p.toReal)) ^ (1 / p.toReal)) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top <;> exact ENNReal.inv_ne_top.mpr
        (Metric.measure_closedBall_pos volume _ (half_pos hr)).ne'
    · exact ENNReal.rpow_ne_top_of_nonneg
        (add_nonneg (Nat.cast_nonneg _) (mul_nonneg hs ENNReal.toReal_nonneg))
        ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hc hfin)
    (ball_average_comparison_enorm hf hs hp x y hr ht0 ht1 hxy)
  simp only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, ENNReal.toReal_mul,
    ball_comparison_coefficient hp hr] at h
  convert h using 1; ring

/-- Hölder's inequality for a mean, stated with the exact normalization factor. -/
theorem average_enorm_le {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : μ ≠ 0) {f : X → E}
    (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    ‖⨍ x, f x ∂μ‖ₑ ≤ (μ univ)⁻¹ ^ (1 / p.toReal) * eLpNorm f p μ := by
  let : NeZero μ := ⟨hμ⟩
  calc
    ‖⨍ x, f x ∂μ‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂(μ univ)⁻¹ • μ :=
      enorm_integral_le_lintegral_enorm _
    _ = eLpNorm f 1 ((μ univ)⁻¹ • μ) :=
      (eLpNorm_one_eq_lintegral_enorm (hf.smul_measure _)).symm
    _ ≤ eLpNorm f p ((μ univ)⁻¹ • μ) := eLpNorm_le_eLpNorm_of_exponent_le hp1
    _ = _ := by
      rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top (zero_lt_one.trans_le hp1).ne' hp]
      simp only [one_div, ENNReal.toReal_inv, smul_eq_mul]

theorem unit_ball_average_bound {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Space 𝕜 (Set.univ : Set (Domain d)) s p) (x : Domain d) :
    ‖⨍ z in Metric.closedBall x 1, firstProjection u z‖ ≤
      (volume.real (Metric.closedBall (0 : Domain d) 1))⁻¹ ^ (1 / p.toReal) *
        ‖firstProjection u‖ := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall x 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall x 1).measure_ne_top
  have hμ : volume.restrict (Metric.closedBall x 1) ≠ 0 :=
    mt Measure.restrict_eq_zero.mp (Metric.measure_closedBall_pos volume x zero_lt_one).ne'
  have hlp : MemLp (firstProjection u : Domain d → 𝕜) p volume := by
    simpa only [domainMeasure, Measure.restrict_univ] using Lp.memLp (firstProjection u)
  have h := average_enorm_le hμ hlp.aestronglyMeasurable.restrict (Fact.out : 1 ≤ p) hp
  simp only [Measure.restrict_apply_univ] at h
  have h' := h.trans (mul_le_mul_right
    (eLpNorm_mono_measure (firstProjection u) Measure.restrict_le_self) _)
  have hfinite : (volume (Metric.closedBall x 1))⁻¹ ^ (1 / p.toReal) *
      eLpNorm (firstProjection u) p volume ≠ ∞ := by
    apply ENNReal.mul_ne_top _ hlp.eLpNorm_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.mpr
      (Metric.measure_closedBall_pos volume x zero_lt_one).ne')
  have ht := ENNReal.toReal_mono hfinite h'
  simp only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_inv] at ht
  rw [Measure.addHaar_closedBall_center volume x 1] at ht
  convert ht using 1
  rw [Lp.norm_def]
  simp only [domainMeasure, Measure.restrict_univ, Measure.real]

/-- On the canonical Euclidean space, ball averages recover the given Lp
representative a.e. This uses Mathlib's Lebesgue differentiation theorem
directly, avoiding a change to the completed coordinate model of U2. -/
theorem ae_average_closedBall_tendsto {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Space 𝕜 (Set.univ : Set (Domain d)) s p) :
    ∀ᵐ x ∂volume, Tendsto
      (fun r : ℝ => ⨍ y in Metric.closedBall x r, firstProjection u y)
      (𝓝[>] (0 : ℝ)) (𝓝 (firstProjection u x)) := by
  have hlp : MemLp (firstProjection u : Domain d → 𝕜) p volume := by
    simpa only [domainMeasure, Measure.restrict_univ] using Lp.memLp (firstProjection u)
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume
    (hlp.locallyIntegrable Fact.out) 1] with x hx
  apply hx (fun _ : ℝ => x) id tendsto_id
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact Metric.mem_closedBall_self (by simpa using hr.le)

@[simp] theorem closureValue_apply {d : ℕ} {𝕜 : Type*} [Zero 𝕜]
    {G : Set (Domain d)} (f : closure G → 𝕜) (x : closure G) :
    closureValue f (x : Domain d) = f x := by
  simp [closureValue, x.property]

theorem closureValue_continuousOn {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {f : closure G → 𝕜} (hf : Continuous f) :
    ContinuousOn (closureValue f) (closure G) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : closure G => closureValue f x)
  simpa only [closureValue_apply] using hf

/-- Equality a.e. on an open set determines a continuous function on its
entire closure, even when that open set is disconnected or empty. -/
theorem closure_representative_unique {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} (hG : IsOpen G) {u : Domain d → 𝕜}
    {f g : closure G → 𝕜} (hf : Continuous f) (hg : Continuous g)
    (hfu : closureValue f =ᵐ[domainMeasure G] u)
    (hgu : closureValue g =ᵐ[domainMeasure G] u) : f = g := by
  have hfc := closureValue_continuousOn hf
  have hgc := closureValue_continuousOn hg
  have hEq : EqOn (closureValue f) (closureValue g) G :=
    Measure.eqOn_open_of_ae_eq (hfu.trans hgu.symm) hG
      (hfc.mono subset_closure) (hgc.mono subset_closure)
  have hc : EqOn (closureValue f) (closureValue g) (closure G) :=
    hEq.of_subset_closure hfc hgc subset_closure (Subset.refl _)
  funext x
  simpa only [closureValue_apply] using hc x.property

theorem bounded_closure_representative_unique {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} (hG : IsOpen G) {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {u : Space 𝕜 G s p} {f g : closure G →ᵇ 𝕜}
    (hf : RepresentsOnClosure u f) (hg : RepresentsOnClosure u g) : f = g := by
  exact DFunLike.coe_injective
    (closure_representative_unique hG f.continuous g.continuous hf hg)

/-- The fixed coordinate identification does not alter openness. -/
theorem isOpen_of_isBoundedLipschitzOpen {n : ℕ} {G : Set (Domain (n + 1))}
    (hG : IsBoundedLipschitzOpen G) : IsOpen G := by
  exact (geometryCoordinates n).toHomeomorph.isOpen_preimage.mp hG.1

/-- Restricting a bounded continuous whole-space representative gives the
correct class on the closure. No boundary values of the Lp representative
are presumed. -/
theorem restrict_representsOnClosure {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} (hG : MeasurableSet G) {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {u : Space 𝕜 G s p}
    {v : Space 𝕜 (Set.univ : Set (Domain d)) s p} {f : Domain d →ᵇ 𝕜}
    (hf : (f : Domain d → 𝕜) =ᵐ[volume] firstProjection v)
    (hv : (firstProjection v : Domain d → 𝕜) =ᵐ[domainMeasure G] firstProjection u) :
    RepresentsOnClosure u (f.domRestrict (closure G)) := by
  have hfr := ae_restrict_of_ae hf (s := G)
  have hmem : ∀ᵐ x ∂domainMeasure G, x ∈ G := ae_restrict_mem hG
  filter_upwards [hfr, hv, hmem] with x hfx hvx hx
  simpa [closureValue, subset_closure hx] using hfx.trans hvx

/-- A quantitative domain reduction. This is a proved implication, not the
original conditional target: the whole-space theorem remains an explicit,
unproved antecedent until its oscillation argument has been supplied.
The first antecedent is exactly the frozen extension Prop, with its original
scalar universe and every quantifier intact. -/
theorem onClosure_of_wholeSpace
    (hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (hWhole : Specs.P102.Fractional.Morrey.wholeSpace.{u}) :
    Specs.P102.Fractional.Morrey.onClosure.{u} := by
  intro n G hG s hs0 hs1 p _ hp hsp 𝕜 _
  obtain ⟨K, hK, Ce, E, hE, hsupport, hEnorm⟩ :=
    hExtension n G hG s hs0 hs1 p hp 𝕜
  obtain ⟨Cw, hCw, hw⟩ := hWhole (n + 1) (Nat.le_add_left 1 n) s hs0 hs1 p hp hsp 𝕜
  refine ⟨2 * Cw * Ce + 1, by positivity, ?_⟩
  intro u
  obtain ⟨f, ⟨hf, hHolder, hNorm⟩, hfuniq⟩ := hw (E u)
  let g : closure G →ᵇ 𝕜 := f.domRestrict (closure G)
  have hN : fullNorm (E u) ≤ (Ce : ℝ) * fullNorm u := by
    rw [fullNorm_eq_norm hp]
    exact hEnorm u
  have hbound : ‖g‖ ≤ (Cw : ℝ) * Ce * fullNorm u := by
    calc
      ‖g‖ ≤ ‖f‖ := BoundedContinuousFunction.norm_compContinuous_le _ _
      _ ≤ (Cw : ℝ) * fullNorm (E u) := hNorm
      _ ≤ (Cw : ℝ) * ((Ce : ℝ) * fullNorm u) :=
        mul_le_mul_of_nonneg_left hN Cw.coe_nonneg
      _ = _ := by ring
  let H : ℝ≥0 := ⟨(Cw : ℝ) * Ce * fullNorm u,
    mul_nonneg (mul_nonneg Cw.coe_nonneg Ce.coe_nonneg) (fullNorm_nonneg u)⟩
  have hrep : RepresentsOnClosure u g :=
    restrict_representsOnClosure (isOpen_of_isBoundedLipschitzOpen hG).measurableSet hf (hE u)
  refine ⟨g, ⟨hrep, H, ?_, ?_⟩, ?_⟩
  · change ‖g‖ + ((Cw : ℝ) * Ce * fullNorm u) ≤ _
    push_cast
    nlinarith [fullNorm_nonneg u]
  · intro x y
    calc
      ‖g x - g y‖ ≤ (Cw : ℝ) *
          (seminorm Set.univ s p (firstProjection (E u))).toReal *
          dist (x : Domain (n + 1)) (y : Domain (n + 1)) ^ exponent (n + 1) s p :=
        hHolder x y
      _ ≤ (Cw : ℝ) * ((Ce : ℝ) * fullNorm u) *
          dist (x : Domain (n + 1)) (y : Domain (n + 1)) ^ exponent (n + 1) s p := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
        exact mul_le_mul_of_nonneg_left ((seminorm_le_fullNorm (E u)).trans hN)
          Cw.coe_nonneg
      _ = _ := by
        change (Cw : ℝ) * ((Ce : ℝ) * fullNorm u) * _ =
          ((Cw : ℝ) * Ce * fullNorm u) * _
        ring
  · intro g' hg'
    exact bounded_closure_representative_unique (isOpen_of_isBoundedLipschitzOpen hG) hg'.1 hrep

/-- Conditional draft of the whole-space theorem. Its extension premise is the
full frozen proposition, although the whole-space argument does not use it. -/
theorem whole_space_conditional
    (_hExtension : Specs.P102.Fractional.Extension.extension.{u}) :
    Specs.P102.Fractional.Morrey.wholeSpace.{u} := by
  intro d hd s hs0 hs1 p _ hp hsp 𝕜 _
  let a := exponent d s p
  have ha : 0 < a := exponent_pos hp hsp
  let A := ballComparisonConstant d s p
  have hA : 0 < A := ballComparisonConstant_pos d s p
  let D := (volume.real (Metric.closedBall (0 : Domain d) 1))⁻¹ ^ (1 / p.toReal)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let Q := 1 - (1 / 2 : ℝ) ^ a
  have hQ : 0 < Q := sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) ha)
  let Ch := 2 * A / Q + A
  let Cs := A / Q + D
  have hCh : 0 ≤ Ch := by dsimp only [Ch]; positivity
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  let C : ℝ≥0 := ⟨Ch + Cs + 1, by positivity⟩
  have hChC : Ch ≤ (C : ℝ) := by change Ch ≤ Ch + Cs + 1; linarith
  have hCsC : Cs ≤ (C : ℝ) := by change Cs ≤ Ch + Cs + 1; linarith
  refine ⟨C, ?_, ?_⟩
  · change 0 < Ch + Cs + 1
    positivity
  intro u
  let N := (seminorm Set.univ s p (firstProjection u)).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hfull : 0 ≤ fullNorm u := fullNorm_nonneg u
  have hfin : seminorm Set.univ s p (firstProjection u) ≠ ∞ :=
    ((firstProjection_range_seminorm hp (firstProjection u)).mp ⟨u, rfl⟩).ne
  have hlp : MemLp (firstProjection u : Domain d → 𝕜) p volume := by
    simpa only [domainMeasure, Measure.restrict_univ] using Lp.memLp (firstProjection u)
  have hloc := hlp.locallyIntegrable (Fact.out : 1 ≤ p)
  let F : ℝ → Domain d → 𝕜 := fun r x => ⨍ z in Metric.closedBall x r, firstProjection u z
  let S := {x | Tendsto (fun r => F r x) (𝓝[>] (0 : ℝ)) (𝓝 (firstProjection u x))}
  have hS : ∀ᵐ x ∂volume, x ∈ S := ae_average_closedBall_tendsto u
  have hincr (x : Domain d) (r : ℝ) (hr : 0 < r) :
      ‖F r x - F (r / 2) x‖ ≤ (A * N) * r ^ a := by
    exact ball_average_comparison hloc hs0.le hp hfin x x hr le_rfl
      (by linarith) (by simpa using hr.le)
  have hcross (x y : Domain d) {r : ℝ} (hr : 0 < r) (hxy : dist x y ≤ r) :
      ‖F r x - F r y‖ ≤ (A * N) * r ^ a := by
    exact ball_average_comparison hloc hs0.le hp hfin x y hr
      (by linarith) le_rfl hxy
  have hHolder : ∀ x ∈ S, ∀ y ∈ S, ‖firstProjection u x - firstProjection u y‖ ≤
      (C : ℝ) * N * dist x y ^ a := by
    intro x hx y hy
    by_cases heq : x = y
    · subst y
      simp only [sub_self, norm_zero]
      positivity
    have hdist : 0 < dist x y := dist_pos.mpr heq
    have hb := ExpandedFA.Sobolev.Morrey.dyadic_pair_bound
      (fun r => F r x) (fun r => F r y) (firstProjection u x) (firstProjection u y)
      hdist ha (hincr x) (hincr y) hx hy (hcross x y hdist le_rfl)
    calc
      _ ≤ (2 * (A * N) / Q + A * N) * dist x y ^ a := hb
      _ = Ch * N * dist x y ^ a := by dsimp only [Ch]; ring
      _ ≤ (C : ℝ) * N * dist x y ^ a := by
        gcongr
  have hBound : ∀ x ∈ S, ‖firstProjection u x‖ ≤ (C : ℝ) * fullNorm u := by
    intro x hx
    have he := ExpandedFA.Sobolev.Morrey.dyadic_error_bound
      (fun r => F r x) (firstProjection u x) zero_lt_one ha (hincr x) hx
    have he' : ‖F 1 x - firstProjection u x‖ ≤ A / Q * N := by
      change ‖F 1 x - firstProjection u x‖ ≤ (A * N) / Q * 1 ^ a at he
      rw [Real.one_rpow, mul_one] at he
      convert he using 1; ring
    have hm : ‖F 1 x‖ ≤ D * ‖firstProjection u‖ := unit_ball_average_bound hp u x
    calc
      ‖firstProjection u x‖ ≤ ‖F 1 x - firstProjection u x‖ + ‖F 1 x‖ := by
        have ht := norm_add_le (firstProjection u x - F 1 x) (F 1 x)
        simpa only [sub_add_cancel, norm_sub_rev] using ht
      _ ≤ A / Q * N + D * ‖firstProjection u‖ := add_le_add he' hm
      _ ≤ Cs * fullNorm u := by
        change A / Q * N + D * ‖firstProjection u‖ ≤
          (A / Q + D) * (‖firstProjection u‖ + N)
        nlinarith [mul_nonneg (div_nonneg hA.le hQ.le) (norm_nonneg (firstProjection u)),
          mul_nonneg hD hN]
      _ ≤ (C : ℝ) * fullNorm u := mul_le_mul_of_nonneg_right hCsC hfull
  exact boundedRepresentative_of_ae_bounds (firstProjection u) S hS
    (mul_nonneg C.coe_nonneg hN) (mul_nonneg C.coe_nonneg hfull) ha hHolder hBound

/-- Conditional draft of the closure theorem with exactly the frozen premise. -/
theorem on_closure_conditional
    (hExtension : Specs.P102.Fractional.Extension.extension.{u}) :
    Specs.P102.Fractional.Morrey.onClosure.{u} :=
  onClosure_of_wholeSpace hExtension (whole_space_conditional hExtension)

end P102.Fractional.Morrey

universe v8_closure_f605c102e9cb0d59_u0
theorem _root_.«P102».«Fractional».«Morrey».«on_closure» : _root_.«Specs».«P102».«Fractional».«Morrey».«onClosure».{v8_closure_f605c102e9cb0d59_u0} :=
  @_root_.«P102».«Fractional».«Morrey».«on_closure_conditional».{v8_closure_f605c102e9cb0d59_u0} (@_root_.«P102».«Fractional».«bounded_linear_extension».{v8_closure_f605c102e9cb0d59_u0})
theorem _root_.«P102».«Fractional».«Morrey».«whole_space» : _root_.«Specs».«P102».«Fractional».«Morrey».«wholeSpace».{v8_closure_f605c102e9cb0d59_u0} :=
  @_root_.«P102».«Fractional».«Morrey».«whole_space_conditional».{v8_closure_f605c102e9cb0d59_u0} (@_root_.«P102».«Fractional».«bounded_linear_extension».{v8_closure_f605c102e9cb0d59_u0})
