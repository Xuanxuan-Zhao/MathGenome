import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderTrailingStep
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.HouseholderReflector
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.DotProduct
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.HouseholderTrailingStep
open MatrixDefinitions HouseholderTrailingDefinitions Rounding

/-- Componentwise multiplication by bounded coefficients is bounded in the
Euclidean norm, also in dimension zero. -/
lemma norm_coordinate_mul_le {d : ℕ} (a : Fin d → ℝ) (x : Vec ℝ d)
    {c : ℝ} (hc : 0 ≤ c) (ha : ∀ i, |a i| ≤ c) :
    ‖WithLp.toLp 2 (fun i => a i * x i)‖ ≤ c * ‖x‖ := by
  calc
    _ ≤ ‖c • x‖ := by
      apply norm_le_norm_of_abs_le_abs
      intro i
      change |a i * x i| ≤ |c * x i|
      rw [abs_mul, abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)
    _ = c * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

lemma sum_abs_mul_le {d : ℕ} (w y : Vec ℝ d) :
    (∑ i, |w i * y i|) ≤ ‖w‖ * ‖y‖ := by
  have h := real_inner_le_norm |w| |y|
  change (∑ i, |y i| * |w i|) ≤ ‖|w|‖ * ‖|y|‖ at h
  simpa only [norm_abs_eq_norm, abs_mul, mul_comm] using h

lemma dot_abs_le {d : ℕ} (w y : Vec ℝ d) :
    |(⇑w) ⬝ᵥ (⇑y)| ≤ ‖w‖ * ‖y‖ := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_abs_mul_le w y)

lemma denominator_error {d : ℕ} (fq : Bool) (round : ℝ → ℝ)
    (u : ℝ) (D : Set ℝ) (w : Vec ℝ d)
    (hm : Rounding.Specs.RelativeModelValue round u D) (hdu : (d : ℝ) * u < 1)
    (hs : DotSpecs.finiteSafe fq round D (⇑w) (⇑w)) :
    |denominator fq round w - ‖w‖ ^ 2| ≤ gamma d u * ‖w‖ ^ 2 := by
  have h := (finite_sequential_dot_product fq round d (⇑w) (⇑w) u D hm hdu hs).2
  change |denominator fq round w - ∑ i, w i * w i| ≤
    gamma d u * ∑ i, |w i * w i| at h
  simpa only [abs_mul_self, abs_sq, ← pow_two, ← EuclideanSpace.real_norm_sq_eq] using h

lemma denominator_positive {d : ℕ} (fq : Bool) (round : ℝ → ℝ)
    (u : ℝ) (D : Set ℝ) (w : Vec ℝ d) (hw : w ≠ 0)
    (hm : Rounding.Specs.RelativeModelValue round u D) (hdu : (d : ℝ) * u < 1)
    (hg : gamma d u < 1) (hs : DotSpecs.finiteSafe fq round D (⇑w) (⇑w)) :
    0 < denominator fq round w := by
  have he := (abs_le.mp (denominator_error fq round u D w hm hdu hs)).1
  have hn : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have hh := mul_pos (sub_pos.mpr hg) hn
  nlinarith

/-- Two rounding factors divided by the squared-norm dot-product factor. -/
lemma ratio_bounds {u g a b e : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hg : 0 ≤ g) (hg1 : g < 1) (ha : |a| ≤ u) (hb : |b| ≤ u) (he : |e| ≤ g) :
    let r := (1 + a) * (1 + b) / (1 + e)
    0 < r ∧ r ≤ R₀ g u ∧ |r - 1| ≤ D₀ g u := by
  dsimp only
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have he' := abs_le.mp he
  have hpa : 0 < 1 + a := by linarith
  have hpb : 0 < 1 + b := by linarith
  have hpe : 0 < 1 + e := by linarith
  have hlow : (1 - u) ^ 2 ≤ (1 + a) * (1 + b) := by
    calc
      _ = (1 - u) * (1 - u) := sq _
      _ ≤ (1 + a) * (1 + b) := mul_le_mul (by linarith) (by linarith)
        (by linarith) (le_of_lt hpa)
  have hhigh : (1 + a) * (1 + b) ≤ (1 + u) ^ 2 := by
    calc
      _ ≤ (1 + u) * (1 + u) := mul_le_mul (by linarith) (by linarith)
        (le_of_lt hpb) (by linarith)
      _ = _ := (sq _).symm
  have hrhigh : (1 + a) * (1 + b) / (1 + e) ≤ R₀ g u := by
    unfold R₀
    apply (div_le_div_iff₀ hpe (by linarith)).2
    calc
      _ ≤ (1 + u) ^ 2 * (1 - g) :=
        mul_le_mul_of_nonneg_right hhigh (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have hrlow : (1 - u) ^ 2 / (1 + g) ≤ (1 + a) * (1 + b) / (1 + e) := by
    apply (div_le_div_iff₀ (by linarith) hpe).2
    calc
      _ ≤ (1 - u) ^ 2 * (1 + g) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hlow (by linarith)
  refine ⟨div_pos (mul_pos hpa hpb) hpe, hrhigh, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hh := le_max_right (R₀ g u - 1) (1 - (1 - u) ^ 2 / (1 + g))
    unfold D₀
    linarith
  · have hh := le_max_left (R₀ g u - 1) (1 - (1 - u) ^ 2 / (1 + g))
    unfold D₀
    linarith

lemma scale_representation {d : ℕ} (fp fq : Bool) (round : ℝ → ℝ)
    (u : ℝ) (D : Set ℝ) (w y : Vec ℝ d) (hw : w ≠ 0)
    (hm : Rounding.Specs.RelativeModelValue round u D) (hdu : (d : ℝ) * u < 1)
    (hg : gamma d u < 1) (hs : Safe fp fq round D w y) :
    ∃ r : ℝ, scale fp fq round w y = (2 * numerator fp round w y / ‖w‖ ^ 2) * r ∧
      0 < r ∧ r ≤ R₀ (gamma d u) u ∧ |r - 1| ≤ D₀ (gamma d u) u := by
  have hq : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  let e := (denominator fq round w - ‖w‖ ^ 2) / ‖w‖ ^ 2
  have he : |e| ≤ gamma d u := by
    dsimp [e]
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr (denominator_error fq round u D w hm hdu hs.2.1)
  have hqe : denominator fq round w = ‖w‖ ^ 2 * (1 + e) := by
    dsimp [e]
    field_simp
    ring
  obtain ⟨a, ha, hau⟩ := hm.2.2 _ hs.2.2.1
  obtain ⟨b, hb, hbu⟩ := hm.2.2 _ hs.2.2.2.1
  have hg0 := gamma_nonneg (n := d) ⟨hm.1, hm.2.1, hdu⟩
  have hr := ratio_bounds hm.1 hm.2.1 hg0 hg hau hbu he
  refine ⟨(1 + a) * (1 + b) / (1 + e), ?_, hr⟩
  unfold scale
  rw [hb, ha, hqe]
  field_simp

/-- Scalar perturbation estimates after cancelling one power of the direction's norm. -/
lemma coefficient_estimates {a b p ph r R D g : ℝ} (ha : 0 < a) (_hb : 0 ≤ b)
    (_hg : 0 ≤ g) (hR : 0 ≤ R) (hD : 0 ≤ D) (hr0 : 0 ≤ r)
    (hr : r ≤ R) (hrD : |r - 1| ≤ D) (hp : |p| ≤ a * b)
    (he : |ph - p| ≤ g * (a * b)) :
    |(2 * ph / a ^ 2) * r - 2 * p / a ^ 2| * a ≤ 2 * (D + R * g) * b ∧
    |(2 * ph / a ^ 2) * r| * a ≤ 2 * R * (1 + g) * b := by
  have hE : |r * ph - p| ≤ (D + R * g) * (a * b) := by
    calc
      _ = |(r - 1) * p + r * (ph - p)| := by congr 1; ring
      _ ≤ |(r - 1) * p| + |r * (ph - p)| := abs_add_le _ _
      _ = |r - 1| * |p| + r * |ph - p| := by rw [abs_mul, abs_mul, abs_of_nonneg hr0]
      _ ≤ D * (a * b) + R * (g * (a * b)) :=
        add_le_add (mul_le_mul hrD hp (abs_nonneg _) hD)
          (mul_le_mul hr he (abs_nonneg _) hR)
      _ = _ := by ring
  have hph : |ph| ≤ (1 + g) * (a * b) := by
    calc
      _ = |(ph - p) + p| := by congr 1; ring
      _ ≤ |ph - p| + |p| := abs_add_le _ _
      _ ≤ g * (a * b) + a * b := add_le_add he hp
      _ = _ := by ring
  have hF : |r * ph| ≤ R * (1 + g) * (a * b) := by
    rw [abs_mul, abs_of_nonneg hr0]
    calc
      _ ≤ R * ((1 + g) * (a * b)) := mul_le_mul hr hph (abs_nonneg _) hR
      _ = _ := by ring
  have ht : 0 ≤ 2 / a := le_of_lt (div_pos (by norm_num) ha)
  have hcancel (z : ℝ) : (2 / a) * (z * (a * b)) = 2 * z * b := by
    field_simp
  have herr : |(2 * ph / a ^ 2) * r - 2 * p / a ^ 2| * a =
      (2 / a) * |r * ph - p| := by
    rw [show (2 * ph / a ^ 2) * r - 2 * p / a ^ 2 =
      (2 / a ^ 2) * (r * ph - p) by ring]
    rw [abs_mul, abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg _))]
    field_simp
  have hmag : |(2 * ph / a ^ 2) * r| * a = (2 / a) * |r * ph| := by
    rw [show (2 * ph / a ^ 2) * r = (2 / a ^ 2) * (r * ph) by ring]
    rw [abs_mul, abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg _))]
    field_simp
  rw [herr, hmag]
  constructor
  · exact (mul_le_mul_of_nonneg_left hE ht).trans_eq (hcancel _)
  · exact (mul_le_mul_of_nonneg_left hF ht).trans_eq (by rw [hcancel]; ring)

/-- The two componentwise roundings, keeping their separate range checks. -/
lemma component_update_error {d : ℕ} (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (t : ℝ) (w y : Vec ℝ d) (hm : Rounding.Specs.RelativeModelValue round u D)
    (hs : ∀ i, t * w i ∈ D ∧ y i - round (t * w i) ∈ D) :
    ‖WithLp.toLp 2 (fun i => round (y i - round (t * w i))) - (y - t • w)‖ ≤
      u * ‖y‖ + (2 * u + u ^ 2) * |t| * ‖w‖ := by
  have hu : 0 ≤ u := hm.1
  choose δ hδ hδu using fun i => hm.2.2 (t * w i) (hs i).1
  choose ε hε hεu using fun i => hm.2.2 (y i - round (t * w i)) (hs i).2
  let c : Fin d → ℝ := fun i => δ i + ε i + δ i * ε i
  have hc : ∀ i, |c i| ≤ 2 * u + u ^ 2 := by
    intro i
    calc
      _ ≤ |δ i + ε i| + |δ i * ε i| := abs_add_le _ _
      _ ≤ (|δ i| + |ε i|) + |δ i| * |ε i| := by
        rw [abs_mul]; exact add_le_add (abs_add_le (δ i) (ε i)) (le_refl _)
      _ ≤ (u + u) + u * u := add_le_add (add_le_add (hδu i) (hεu i))
        (mul_le_mul (hδu i) (hεu i) (abs_nonneg _) hm.1)
      _ = _ := by ring
  have hid : WithLp.toLp 2 (fun i => round (y i - round (t * w i))) - (y - t • w) =
      WithLp.toLp 2 (fun i => ε i * y i) -
        t • WithLp.toLp 2 (fun i => c i * w i) := by
    ext i
    change round (y i - round (t * w i)) - (y i - t * w i) =
      ε i * y i - t * (c i * w i)
    rw [hε i, hδ i]
    dsimp [c]
    ring
  rw [hid]
  calc
    _ ≤ ‖WithLp.toLp 2 (fun i => ε i * y i)‖ +
        ‖t • WithLp.toLp 2 (fun i => c i * w i)‖ := norm_sub_le _ _
    _ ≤ u * ‖y‖ + |t| * ((2 * u + u ^ 2) * ‖w‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (norm_coordinate_mul_le ε y hm.1 hεu)
        (mul_le_mul_of_nonneg_left
          (norm_coordinate_mul_le c w (by positivity) hc) (abs_nonneg _))
    _ = _ := by ring

lemma reflector_action {d : ℕ} (w y : Vec ℝ d) :
    (HouseholderDefinitions.reflector w).toEuclideanLin y =
      y - (2 * ((⇑w) ⬝ᵥ (⇑y)) / ‖w‖ ^ 2) • w := by
  ext i
  simp only [Matrix.toLpLin_apply, HouseholderDefinitions.reflector,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, PiLp.toLp_apply, Pi.sub_apply, Pi.smul_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, HouseholderReflector.norm_sq_dot]
  ring

/-- W32's full local trailing-tail estimate for an arbitrary nonzero stored
real direction; no pivot-column construction is required. -/
theorem trailing_step : _root_.Specs.NumAnalysis206.HouseholderTrailingStep.trailing_step := by
  intro d fp fq round u D w y hw hm hdu hg hs
  have hu : 0 ≤ u := hm.1
  have hg' : gamma d u < 1 := hg
  have hg0 := gamma_nonneg (n := d) ⟨hm.1, hm.2.1, hdu⟩
  refine ⟨denominator_positive fq round u D w hw hm hdu hg' hs.2.1, ?_⟩
  obtain ⟨r, htr, hr0, hrR, hrD⟩ := scale_representation fp fq round u D w y hw hm hdu hg' hs
  have hR : 0 ≤ R₀ (gamma d u) u := le_trans hr0.le hrR
  have hD : 0 ≤ D₀ (gamma d u) u := (abs_nonneg _).trans hrD
  have hp := dot_abs_le w y
  have he : |numerator fp round w y - ((⇑w) ⬝ᵥ (⇑y))| ≤
      gamma d u * (‖w‖ * ‖y‖) := by
    have hh := (finite_sequential_dot_product fp round d (⇑w) (⇑y) u D hm hdu hs.1).2
    change |numerator fp round w y - ((⇑w) ⬝ᵥ (⇑y))| ≤
      gamma d u * ∑ i, |w i * y i| at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (sum_abs_mul_le w y) hg0)
  obtain ⟨htdiff, htmag⟩ := coefficient_estimates (norm_pos_iff.mpr hw) (norm_nonneg y)
    hg0 hR hD hr0.le hrR hrD hp he
  rw [← htr] at htdiff htmag
  let t := scale fp fq round w y
  let t₀ := 2 * ((⇑w) ⬝ᵥ (⇑y)) / ‖w‖ ^ 2
  have hcomp : ‖update fp fq round w y - (y - t • w)‖ ≤
      u * ‖y‖ + (2 * u + u ^ 2) * |t| * ‖w‖ :=
    component_update_error round u D t w y hm hs.2.2.2.2
  have hid : (y - t • w) - (y - t₀ • w) = -(t - t₀) • w := by
    ext i
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [reflector_action]
  change ‖update fp fq round w y - (y - t₀ • w)‖ ≤ ctail (gamma d u) u * ‖y‖
  calc
    _ = ‖(update fp fq round w y - (y - t • w)) +
        ((y - t • w) - (y - t₀ • w))‖ := by congr 1; abel
    _ ≤ ‖update fp fq round w y - (y - t • w)‖ +
        ‖(y - t • w) - (y - t₀ • w)‖ := norm_add_le _ _
    _ = ‖update fp fq round w y - (y - t • w)‖ + |t - t₀| * ‖w‖ := by
      rw [hid, norm_smul, Real.norm_eq_abs, abs_neg]
    _ ≤ (u * ‖y‖ + (2 * u + u ^ 2) * |t| * ‖w‖) +
        2 * (D₀ (gamma d u) u + R₀ (gamma d u) u * gamma d u) * ‖y‖ :=
      add_le_add hcomp htdiff
    _ ≤ (u * ‖y‖ + (2 * u + u ^ 2) *
        (2 * R₀ (gamma d u) u * (1 + gamma d u) * ‖y‖)) +
        2 * (D₀ (gamma d u) u + R₀ (gamma d u) u * gamma d u) * ‖y‖ := by
      have hh := mul_le_mul_of_nonneg_left htmag (show 0 ≤ 2 * u + u ^ 2 by positivity)
      dsimp only [t]
      nlinarith only [hh]
    _ = _ := by unfold ctail; ring

end NumAnalysis206.HouseholderTrailingStep
