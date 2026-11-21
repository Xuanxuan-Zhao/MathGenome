import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.WeightedInterpolation
import MathGenome.Internal.LinearPDE.P201.Elliptic.ConstantSchauder
import Batteries.Tactic.OpenPrivate

/-! Weighted interpolation with genuine within derivatives. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace P201.Elliptic.WeightedInterpolation
open P201Specs.Elliptic.WeightedInterpolation
open P201Specs.Elliptic.ConstantSchauder
open P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.NewtonHessian
open P201.Elliptic.ConstantSchauder
open private coordinate_norm from MathGenome.Internal.LinearPDE.P201.Elliptic.HalfSpaceLift

lemma holder_interpolation_scalar {α δ M L t q : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (ht : 0 ≤ t) (hqM : q ≤ 2 * M) (hqL : q ≤ L * t) :
    q ≤ (δ ^ (1 - α) * L + 2 * M / δ ^ α) * t ^ α := by
  have hδa : 0 < δ ^ α := Real.rpow_pos_of_pos hδ _
  have hta : 0 ≤ t ^ α := Real.rpow_nonneg ht _
  by_cases htd : t ≤ δ
  · have htprod : t ≤ δ ^ (1 - α) * t ^ α := by
      by_cases ht0 : t = 0
      · rw [ht0]; positivity
      have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      calc
        t = t ^ (1 - α) * t ^ α := by
          rw [← Real.rpow_add htp]; simp
        _ ≤ δ ^ (1 - α) * t ^ α :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht htd (by linarith)) hta
    calc
      q ≤ L * t := hqL
      _ ≤ L * (δ ^ (1 - α) * t ^ α) := mul_le_mul_of_nonneg_left htprod hL
      _ ≤ (δ ^ (1 - α) * L + 2 * M / δ ^ α) * t ^ α := by
        have : 0 ≤ 2 * M / δ ^ α := by positivity
        nlinarith
  · have hda : δ ^ α ≤ t ^ α := Real.rpow_le_rpow hδ.le (le_of_not_ge htd) hα
    calc
      q ≤ 2 * M := hqM
      _ ≤ (2 * M / δ ^ α) * t ^ α := by
        calc
          2 * M = (2 * M / δ ^ α) * δ ^ α := by field_simp
          _ ≤ (2 * M / δ ^ α) * t ^ α :=
            mul_le_mul_of_nonneg_left hda (by positivity)
      _ ≤ (δ ^ (1 - α) * L + 2 * M / δ ^ α) * t ^ α := by
        have : 0 ≤ δ ^ (1 - α) * L := by positivity
        nlinarith

open Set Metric

lemma weighted_holder_interpolation {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {d : E → ℝ} {v : E → F} {v' : E → E →L[ℝ] F}
    {α h M L : ℝ} (j : ℕ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hh : 0 < h)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hd : ∀ x ∈ s, 0 < d x)
    (hc : ∀ t : ℝ, Convex ℝ {x | x ∈ s ∧ t ≤ d x})
    (hv : ∀ x ∈ s, HasFDerivWithinAt v (v' x) s x)
    (hb : ∀ x ∈ s, d x ^ j * ‖v x‖ ≤ M)
    (hD : ∀ x ∈ s, d x ^ (j + 1) * ‖v' x‖ ≤ L)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (min (d x) (d y)) ^ ((j : ℝ) + α) * ‖v x - v y‖ ≤
      (h ^ (1 - α) * L + 2 * M / h ^ α) * dist x y ^ α := by
  let r := min (d x) (d y)
  have hr : 0 < r := lt_min (hd x hx) (hd y hy)
  have hrx : r ≤ d x := min_le_left _ _
  have hry : r ≤ d y := min_le_right _ _
  have hxb : r ^ j * ‖v x‖ ≤ M :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hrx j) (norm_nonneg _)).trans (hb x hx)
  have hyb : r ^ j * ‖v y‖ ≤ M :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hry j) (norm_nonneg _)).trans (hb y hy)
  have hsup : r ^ j * ‖v x - v y‖ ≤ 2 * M := by
    have h := mul_le_mul_of_nonneg_left (norm_sub_le (v x) (v y)) (pow_nonneg hr.le j)
    nlinarith
  have hdiff : ‖v x - v y‖ ≤ (L / r ^ (j + 1)) * dist x y := by
    have hsubset : {z | z ∈ s ∧ r ≤ d z} ⊆ s := fun z hz => hz.1
    have hbound : ∀ z ∈ {z | z ∈ s ∧ r ≤ d z}, ‖v' z‖ ≤ L / r ^ (j + 1) := by
      intro z hz
      apply (le_div_iff₀ (pow_pos hr _)).mpr
      calc
        ‖v' z‖ * r ^ (j + 1) = r ^ (j + 1) * ‖v' z‖ := by ring
        _ ≤ d z ^ (j + 1) * ‖v' z‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hz.2 _) (norm_nonneg _)
        _ ≤ L := hD z hz.1
    simpa only [dist_eq_norm] using (hc r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hv z hz.1).mono hsubset) hbound ⟨hy, hry⟩ ⟨hx, hrx⟩
  have hlinear : r ^ j * ‖v x - v y‖ ≤ L * (dist x y / r) := by
    calc
      r ^ j * ‖v x - v y‖ ≤ r ^ j * ((L / r ^ (j + 1)) * dist x y) :=
        mul_le_mul_of_nonneg_left hdiff (pow_nonneg hr.le j)
      _ = L * (dist x y / r) := by
        rw [pow_succ]
        field_simp
  have hi := holder_interpolation_scalar hα hα1 hh hM hL
    (div_nonneg dist_nonneg hr.le) hsup hlinear
  have hpow : r ^ ((j : ℝ) + α) = r ^ j * r ^ α := by
    rw [Real.rpow_add hr, Real.rpow_natCast]
  have hratio : r ^ α * (dist x y / r) ^ α = dist x y ^ α := by
    rw [Real.div_rpow dist_nonneg hr.le]
    field_simp
  calc
    r ^ ((j : ℝ) + α) * ‖v x - v y‖ = r ^ α * (r ^ j * ‖v x - v y‖) := by
      rw [hpow]; ring
    _ ≤ r ^ α * ((h ^ (1 - α) * L + 2 * M / h ^ α) * (dist x y / r) ^ α) :=
      mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hr.le _)
    _ = (h ^ (1 - α) * L + 2 * M / h ^ α) * dist x y ^ α := by
      rw [← mul_assoc, mul_comm (r ^ α), mul_assoc, hratio]

/-- In a convex portion of a ball, the spherical-distance weight has convex
superlevel sets. This applies also to a half-ball together with its flat face. -/
lemma radial_weighted_holder_interpolation {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {v : E → F} {v' : E → E →L[ℝ] F} {center : E}
    {α h M L R : ℝ} (j : ℕ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hh : 0 < h)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hs : Convex ℝ s) (hsR : s ⊆ ball center R)
    (hv : ∀ x ∈ s, HasFDerivWithinAt v (v' x) s x)
    (hb : ∀ x ∈ s, (R - dist x center) ^ j * ‖v x‖ ≤ M)
    (hD : ∀ x ∈ s, (R - dist x center) ^ (j + 1) * ‖v' x‖ ≤ L)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (min (R - dist x center) (R - dist y center)) ^ ((j : ℝ) + α) * ‖v x - v y‖ ≤
      (h ^ (1 - α) * L + 2 * M / h ^ α) * dist x y ^ α := by
  apply weighted_holder_interpolation j hα hα1 hh hM hL
    (fun z hz => sub_pos.mpr (mem_ball.mp (hsR hz))) _ hv hb hD hx hy
  intro t
  have heq : {z | z ∈ s ∧ t ≤ R - dist z center} = s ∩ closedBall center (R - t) := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_closedBall]
    constructor
    · rintro ⟨hz, ht⟩; exact ⟨hz, by linarith⟩
    · rintro ⟨hz, ht⟩; exact ⟨hz, by linarith⟩
  rw [heq]
  exact hs.inter (convex_closedBall center (R - t))

lemma holder_interpolation_scale {α ε : ℝ} (hα : α < 1) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ^ (1 - α) = ε := by
  refine ⟨ε ^ (1 / (1 - α)), Real.rpow_pos_of_pos hε _, ?_⟩
  rw [← Real.rpow_mul hε.le]
  have hne : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα)
  rw [one_div_mul_cancel hne, Real.rpow_one]

/-- A one-sided second-order Taylor remainder from two applications of the
mean value theorem. The second derivative need only exist within the segment. -/
lemma one_sided_second_remainder_bound {f f₁ f₂ : ℝ → ℝ} {T K : ℝ}
    (_hT : 0 ≤ T) (hK : 0 ≤ K)
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f₁ t) (Icc 0 T) t)
    (hf₁ : ∀ t ∈ Icc 0 T, HasDerivWithinAt f₁ (f₂ t) (Icc 0 T) t)
    (hD : ∀ t ∈ Icc 0 T, ‖f₂ t - f₂ 0‖ ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖f t - f 0 - f₁ 0 * t - f₂ 0 * t ^ 2 / 2‖ ≤ K * T * t := by
  have hfirst : ∀ t ∈ Icc 0 T, ‖f₁ t - f₁ 0 - f₂ 0 * t‖ ≤ K * t := by
    have hd : ∀ t ∈ Icc 0 T,
        HasDerivWithinAt (fun t => f₁ t - f₁ 0 - f₂ 0 * t)
          (f₂ t - f₂ 0) (Icc 0 T) t := by
      intro t ht
      convert ((hf₁ t ht).sub_const (f₁ 0)).sub
        ((hasDerivWithinAt_id t (Icc 0 T)).const_mul (f₂ 0)) using 1 <;> (try funext u) <;> (try simp only [Pi.sub_apply, id_eq]) <;> ring
    intro t ht
    simpa using norm_image_sub_le_of_norm_deriv_le_segment' hd
      (fun t ht => hD t (Ico_subset_Icc_self ht)) t ht
  have hd : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => f t - f 0 - f₁ 0 * t - f₂ 0 * t ^ 2 / 2)
        (f₁ t - f₁ 0 - f₂ 0 * t) (Icc 0 T) t := by
    intro t ht
    convert (((hf t ht).sub_const (f 0)).sub
      ((hasDerivWithinAt_id t (Icc 0 T)).const_mul (f₁ 0))).sub
      ((((hasDerivWithinAt_id t (Icc 0 T)).pow 2).const_mul (f₂ 0)).div_const 2) using 1 <;> (try funext u) <;> (try simp only [Pi.sub_apply, Pi.pow_apply, id_eq]) <;> ring
  have hb : ∀ t ∈ Ico 0 T, ‖f₁ t - f₁ 0 - f₂ 0 * t‖ ≤ K * T := by
    intro t ht
    exact (hfirst t (Ico_subset_Icc_self ht)).trans (mul_le_mul_of_nonneg_left ht.2.le hK)
  simpa using norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ht

/-- A genuine one-sided second-difference interpolation estimate. It uses
only three function values and the oscillation of the actual second derivative
on the same segment; it contains no PDE estimate among its hypotheses. -/
lemma one_sided_second_difference_bound {f f₁ f₂ : ℝ → ℝ} {h M K : ℝ}
    (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt f (f₁ t) (Icc 0 (2 * h)) t)
    (hf₁ : ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt f₁ (f₂ t) (Icc 0 (2 * h)) t)
    (hD : ∀ t ∈ Icc 0 (2 * h), ‖f₂ t - f₂ 0‖ ≤ K)
    (hb0 : ‖f 0‖ ≤ M) (hbh : ‖f h‖ ≤ M) (hb2h : ‖f (2 * h)‖ ≤ M) :
    ‖f₂ 0‖ ≤ 4 * M / h ^ 2 + 8 * K := by
  let r₁ := f h - f 0 - f₁ 0 * h - f₂ 0 * h ^ 2 / 2
  let r₂ := f (2 * h) - f 0 - f₁ 0 * (2 * h) - f₂ 0 * (2 * h) ^ 2 / 2
  have hr₁ : ‖r₁‖ ≤ 2 * K * h ^ 2 := by
    have hr := one_sided_second_remainder_bound (by positivity : 0 ≤ 2 * h) hK hf hf₁ hD
      (show h ∈ Icc 0 (2 * h) by constructor <;> linarith)
    change ‖f h - f 0 - f₁ 0 * h - f₂ 0 * h ^ 2 / 2‖ ≤ 2 * K * h ^ 2
    convert hr using 1 <;> ring
  have hr₂ : ‖r₂‖ ≤ 4 * K * h ^ 2 := by
    have hr := one_sided_second_remainder_bound (by positivity : 0 ≤ 2 * h) hK hf hf₁ hD
      (show 2 * h ∈ Icc 0 (2 * h) by constructor <;> linarith)
    change ‖f (2 * h) - f 0 - f₁ 0 * (2 * h) - f₂ 0 * (2 * h) ^ 2 / 2‖ ≤ 4 * K * h ^ 2
    convert hr using 1 <;> ring
  have hdelta : ‖f (2 * h) - 2 * f h + f 0‖ ≤ 4 * M := by
    calc
      _ ≤ ‖f (2 * h) - 2 * f h‖ + ‖f 0‖ := norm_add_le _ _
      _ ≤ ‖f (2 * h)‖ + ‖2 * f h‖ + ‖f 0‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖f (2 * h)‖ + 2 * ‖f h‖ + ‖f 0‖ := by simp
      _ ≤ 4 * M := by linarith
  have heq : h ^ 2 * f₂ 0 = (f (2 * h) - 2 * f h + f 0) - r₂ + 2 * r₁ := by
    dsimp [r₁, r₂]
    ring
  have hmain : h ^ 2 * ‖f₂ 0‖ ≤ 4 * M + 8 * K * h ^ 2 := by
    calc
      _ = ‖h ^ 2 * f₂ 0‖ := by rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      _ = ‖(f (2 * h) - 2 * f h + f 0) - r₂ + 2 * r₁‖ := by rw [heq]
      _ ≤ ‖(f (2 * h) - 2 * f h + f 0) - r₂‖ + ‖2 * r₁‖ := norm_add_le _ _
      _ ≤ ‖f (2 * h) - 2 * f h + f 0‖ + ‖r₂‖ + ‖2 * r₁‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖f (2 * h) - 2 * f h + f 0‖ + ‖r₂‖ + 2 * ‖r₁‖ := by simp
      _ ≤ 4 * M + 8 * K * h ^ 2 := by linarith
  calc
    ‖f₂ 0‖ ≤ (4 * M + 8 * K * h ^ 2) / h ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hh)).mpr (by simpa only [mul_comm] using hmain)
    _ = 4 * M / h ^ 2 + 8 * K := by field_simp

/-- The Hölder-oscillation form used in the Hessian interpolation argument.
The step is one-sided, so no negative direction or extension across a flat
boundary is required. -/
lemma one_sided_second_difference_holder_bound {f f₁ f₂ : ℝ → ℝ} {α h M H : ℝ}
    (hα : 0 ≤ α) (hh : 0 < h) (hH : 0 ≤ H)
    (hf : ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt f (f₁ t) (Icc 0 (2 * h)) t)
    (hf₁ : ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt f₁ (f₂ t) (Icc 0 (2 * h)) t)
    (hD : ∀ t ∈ Icc 0 (2 * h), ‖f₂ t - f₂ 0‖ ≤ H * t ^ α)
    (hb0 : ‖f 0‖ ≤ M) (hbh : ‖f h‖ ≤ M) (hb2h : ‖f (2 * h)‖ ≤ M) :
    ‖f₂ 0‖ ≤ 4 * M / h ^ 2 + 8 * H * (2 * h) ^ α := by
  have hK : 0 ≤ H * (2 * h) ^ α := by positivity
  have hb := one_sided_second_difference_bound hh hK hf hf₁
    (fun t ht => (hD t ht).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 hα) hH)) hb0 hbh hb2h
  convert hb using 1 <;> ring

/-- The corresponding one-sided first-difference estimate, retaining its
small step in front of the second derivative bound. -/
lemma one_sided_first_difference_bound {f f₁ f₂ : ℝ → ℝ} {h M L : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc 0 h, HasDerivWithinAt f (f₁ t) (Icc 0 h) t)
    (hf₁ : ∀ t ∈ Icc 0 h, HasDerivWithinAt f₁ (f₂ t) (Icc 0 h) t)
    (hD : ∀ t ∈ Icc 0 h, ‖f₂ t‖ ≤ L)
    (hb0 : ‖f 0‖ ≤ M) (hbh : ‖f h‖ ≤ M) :
    ‖f₁ 0‖ ≤ 2 * M / h + h * L := by
  have hfirst : ∀ t ∈ Icc 0 h, ‖f₁ t - f₁ 0‖ ≤ L * t := by
    simpa only [sub_zero] using (norm_image_sub_le_of_norm_deriv_le_segment' hf₁
      (fun t ht => hD t (Ico_subset_Icc_self ht)))
  have hdr : ∀ t ∈ Icc 0 h,
      HasDerivWithinAt (fun t => f t - f 0 - f₁ 0 * t)
        (f₁ t - f₁ 0) (Icc 0 h) t := by
    intro t ht
    convert ((hf t ht).sub_const (f 0)).sub
      ((hasDerivWithinAt_id t (Icc 0 h)).const_mul (f₁ 0)) using 1
    · funext u; simp only [Pi.sub_apply, id_eq]
    · ring
  have hrem : ‖f h - f 0 - f₁ 0 * h‖ ≤ L * h ^ 2 := by
    have hr := norm_image_sub_le_of_norm_deriv_le_segment' hdr
      (fun t ht => (hfirst t (Ico_subset_Icc_self ht)).trans
        (mul_le_mul_of_nonneg_left ht.2.le hL)) h ⟨hh.le, le_rfl⟩
    simpa only [mul_zero, sub_self, sub_zero, pow_two, mul_assoc] using hr
  have hm : ‖h * f₁ 0‖ ≤ 2 * M + L * h ^ 2 := by
    calc
      _ = ‖(f h - f 0) - (f h - f 0 - f₁ 0 * h)‖ := by congr 1; ring
      _ ≤ ‖f h - f 0‖ + ‖f h - f 0 - f₁ 0 * h‖ := norm_sub_le _ _
      _ ≤ ‖f h‖ + ‖f 0‖ + ‖f h - f 0 - f₁ 0 * h‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ 2 * M + L * h ^ 2 := by linarith
  rw [norm_mul, Real.norm_of_nonneg hh.le] at hm
  calc
    ‖f₁ 0‖ ≤ (2 * M + L * h ^ 2) / h :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hm)
    _ = 2 * M / h + h * L := by field_simp

/-- Applying the one-sided interpolation argument to an actual spatial
segment. Both displayed fields are required to be actual first and second
within derivatives; no freely chosen Hessian field is substituted. -/
lemma directional_second_difference_holder_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} {u : E → ℝ}
    {Du : E → E →L[ℝ] ℝ} {D₂u : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x v : E} {α h M H : ℝ} (hα : 0 ≤ α) (hh : 0 < h) (hH : 0 ≤ H)
    (hseg : MapsTo (fun t : ℝ => x + t • v) (Icc 0 (2 * h)) s)
    (hu : ∀ z ∈ s, HasFDerivWithinAt u (Du z) s z)
    (hDu : ∀ z ∈ s, HasFDerivWithinAt Du (D₂u z) s z)
    (hD : ∀ t ∈ Icc 0 (2 * h),
      ‖(D₂u (x + t • v) v) v - (D₂u x v) v‖ ≤ H * t ^ α)
    (hb0 : ‖u x‖ ≤ M) (hbh : ‖u (x + h • v)‖ ≤ M)
    (hb2h : ‖u (x + (2 * h) • v)‖ ≤ M) :
    ‖(D₂u x v) v‖ ≤ 4 * M / h ^ 2 + 8 * H * (2 * h) ^ α := by
  have hcurve : ∀ t : ℝ,
      HasDerivWithinAt (fun t : ℝ => x + t • v) v (Icc 0 (2 * h)) t := by
    intro t
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id t).smul_const v).const_add x |>.hasDerivWithinAt
  have hf : ∀ t ∈ Icc 0 (2 * h),
      HasDerivWithinAt (fun t => u (x + t • v)) (Du (x + t • v) v) (Icc 0 (2 * h)) t := by
    intro t ht
    exact (hu _ (hseg ht)).comp_hasDerivWithinAt t (hcurve t) hseg
  have hf₁ : ∀ t ∈ Icc 0 (2 * h),
      HasDerivWithinAt (fun t => Du (x + t • v) v)
        ((D₂u (x + t • v) v) v) (Icc 0 (2 * h)) t := by
    intro t ht
    have h := (hDu _ (hseg ht)).comp_hasDerivWithinAt t (hcurve t) hseg
    exact ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp_hasDerivWithinAt t h
  simpa only [zero_smul, add_zero] using
    one_sided_second_difference_holder_bound hα hh hH hf hf₁
      (by simpa only [zero_smul, add_zero] using hD)
      (by simpa only [zero_smul, add_zero] using hb0) hbh hb2h

/-- Polarization controls mixed Hessian entries using forward directions
only. The symmetry hypothesis is precisely the equality of mixed second
Fréchet derivatives supplied by local C² regularity. -/
lemma symmetric_bilinear_mixed_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) {Qv Qw Qsum : ℝ}
    (hSymm : B v w = B w v)
    (hv : ‖B v v‖ ≤ Qv) (hw : ‖B w w‖ ≤ Qw)
    (hsum : ‖B (v + w) (v + w)‖ ≤ Qsum) :
    ‖B v w‖ ≤ (Qsum + Qv + Qw) / 2 := by
  have heq : 2 * B v w = B (v + w) (v + w) - B v v - B w w := by
    simp only [map_add, add_apply]
    rw [← hSymm]
    ring
  have hb : 2 * ‖B v w‖ ≤ Qsum + Qv + Qw := by
    calc
      _ = ‖2 * B v w‖ := by simp
      _ = ‖B (v + w) (v + w) - B v v - B w w‖ := by rw [heq]
      _ ≤ ‖B (v + w) (v + w) - B v v‖ + ‖B w w‖ := norm_sub_le _ _
      _ ≤ (‖B (v + w) (v + w)‖ + ‖B v v‖) + ‖B w w‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ Qsum + Qv + Qw := by linarith
  linarith


lemma radialWeight_pos {n : ℕ} {a : Space n} {R : ℝ} {s : Set (Space n)}
    (hs : s ⊆ ball a R) {x : Space n} (hx : x ∈ s) : 0 < radialWeight a R x :=
  sub_pos.mpr (mem_ball.mp (hs hx))

lemma radialWeight_le {n : ℕ} (a x : Space n) (R : ℝ) :
    radialWeight a R x ≤ R := sub_le_self _ dist_nonneg

lemma weighted_values_bddAbove {n : ℕ} {a : Space n} {R : ℝ} {s : Set (Space n)}
    {g : Space n → ℝ} (hR : 0 ≤ R) (hs : s ⊆ ball a R)
    (hg : IsBoundedOn g s) (j : ℕ) : BddAbove (weightedValueSet j a R g s) := by
  obtain ⟨M, hM, hb⟩ := hg
  refine ⟨R ^ j * M, ?_⟩
  rintro q ⟨x, hx, rfl⟩
  exact mul_le_mul (pow_le_pow_left₀ (radialWeight_pos hs hx).le
    (radialWeight_le a x R) j) (hb x hx) (norm_nonneg _) (pow_nonneg hR j)

lemma weighted_pairs_bddAbove_of_holder {n : ℕ} {a : Space n} {R α : ℝ}
    {s : Set (Space n)} {g : Space n → ℝ} (hα : 0 ≤ α) (hR : 0 < R)
    (hs : s ⊆ ball a R) (hg : IsHolderOn α g s) (j : ℕ) :
    BddAbove (weightedPairSet j α a R g s) := by
  obtain ⟨M, H, hM, hH, hb, hdiff⟩ := hg
  refine ⟨R ^ ((j : ℝ) + α) * H, ?_⟩
  rintro q ⟨x, hx, y, hy, hxy, rfl⟩
  have hd : 0 < dist x y ^ α := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
  apply (div_le_iff₀ hd).mpr
  have hw : min (radialWeight a R x) (radialWeight a R y) ^ ((j : ℝ) + α) ≤
      R ^ ((j : ℝ) + α) :=
    Real.rpow_le_rpow (le_min (radialWeight_pos hs hx).le (radialWeight_pos hs hy).le)
      ((min_le_left _ _).trans (radialWeight_le a x R)) (by positivity)
  calc
    _ ≤ R ^ ((j : ℝ) + α) * (H * dist x y ^ α) :=
      mul_le_mul hw (hdiff x hx y hy) (norm_nonneg _) (Real.rpow_nonneg hR.le _)
    _ = _ := by ring

/-- Finite coordinate families of finite bounds can be bounded by their sum. -/
lemma uniform_finite_bound {ι : Type*} [Fintype ι] {n : ℕ}
    {g : ι → Space n → ℝ} {s : Set (Space n)} (hg : ∀ i, IsBoundedOn (g i) s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ s, ‖g i x‖ ≤ M := by
  classical
  choose M hM hb using hg
  refine ⟨∑ i, M i, Finset.sum_nonneg (fun i _ => hM i), ?_⟩
  intro i x hx
  exact (hb i x hx).trans
    (Finset.single_le_sum (fun k _ => hM k) (Finset.mem_univ i))

lemma weighted_pairs_bddAbove_of_deriv {n : ℕ} {a : Space n} {R α : ℝ}
    {s : Set (Space n)} {g : Space n → ℝ} {Dg : Space n → Space n →L[ℝ] ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hR : 0 < R) (hc : Convex ℝ s)
    (hs : s ⊆ ball a R) (hg : IsBoundedOn g s)
    (hd : ∀ x ∈ s, HasFDerivWithinAt g (Dg x) s x)
    (hb : ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ s, ‖Dg x‖ ≤ L) (j : ℕ) :
    BddAbove (weightedPairSet j α a R g s) := by
  obtain ⟨M, hM, hgb⟩ := hg
  obtain ⟨L, hL, hDb⟩ := hb
  let M' := R ^ j * M
  let L' := R ^ (j + 1) * L
  have hM' : 0 ≤ M' := by positivity
  have hL' : 0 ≤ L' := by positivity
  refine ⟨M' * 2 + L', ?_⟩
  rintro q ⟨x, hx, y, hy, hxy, rfl⟩
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) α)).mpr
  have h := radial_weighted_holder_interpolation j hα hα1 zero_lt_one hM' hL' hc hs hd
    (fun z hz => mul_le_mul
      (pow_le_pow_left₀ (radialWeight_pos hs hz).le (radialWeight_le a z R) j)
      (hgb z hz) (norm_nonneg _) (pow_nonneg hR.le j))
    (fun z hz => mul_le_mul
      (pow_le_pow_left₀ (radialWeight_pos hs hz).le (radialWeight_le a z R) (j + 1))
      (hDb z hz) (norm_nonneg _) (pow_nonneg hR.le (j + 1))) hx hy
  simpa only [Real.one_rpow, one_mul, mul_one, div_one, radialWeight, add_comm, mul_comm] using h

/-- Every defining supremum is finite, including the lower-order pair sets.
This result uses the actual differentiable jets, not assumed Hölder bounds for
u or Du. -/
theorem finite_weighted_norms : BoundednessStatement := by
  intro n α R a s u hα hα1 hR hc hs hsR hu
  have hb1 := uniform_finite_bound hu.2.2.1
  obtain ⟨L, hL, hfirst⟩ := hb1
  have hgrad : ∀ x ∈ s, ‖fderivWithin ℝ u s x‖ ≤ (n : ℝ) * L :=
    fun x hx => within_fderiv_bound (fun i => hfirst i x hx)
  have hfirstC (i : Fin n) : ContDiffOn ℝ 1 (firstPartialWithin u s i) s :=
    (hu.1.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
  have hb2 : ∀ ij : Fin n × Fin n, IsBoundedOn (secondPartialWithin u s ij.1 ij.2) s := by
    intro ij
    obtain ⟨M, H, hM, _, hb, _⟩ := hu.2.2.2 ij.1 ij.2
    exact ⟨M, hM, hb⟩
  obtain ⟨Q, hQ, hsecond⟩ := uniform_finite_bound hb2
  have hfirstD (i : Fin n) :
      ∀ x ∈ s, ‖fderivWithin ℝ (firstPartialWithin u s i) s x‖ ≤ (n : ℝ) * Q := by
    intro x hx
    apply within_fderiv_bound
    intro j
    exact hsecond (j, i) x hx
  refine ⟨weighted_values_bddAbove hR.le hsR hu.2.1 0,
    fun i => weighted_values_bddAbove hR.le hsR (hu.2.2.1 i) 1,
    fun i j => weighted_values_bddAbove hR.le hsR (hb2 (i, j)) 2,
    ?_, ?_, fun i j => weighted_pairs_bddAbove_of_holder hα hR hsR (hu.2.2.2 i j) 2⟩
  · exact weighted_pairs_bddAbove_of_deriv hα hα1 hR hc hsR hu.2.1
      (fun x hx => (hu.1.differentiableOn (by norm_num) x hx).hasFDerivWithinAt)
      ⟨(n : ℝ) * L, by positivity, hgrad⟩ 0
  · intro i
    exact weighted_pairs_bddAbove_of_deriv hα hα1 hR hc hsR (hu.2.2.1 i)
      (fun x hx => ((hfirstC i).differentiableOn (by norm_num) x hx).hasFDerivWithinAt)
      ⟨(n : ℝ) * Q, by positivity, hfirstD i⟩ 1

/-- Local scalar bounds patch on a compact set, including an empty set. -/
lemma boundedOn_of_local_on_compact {n : ℕ} {g : Space n → ℝ}
    {s : Set (Space n)} (hcompact : IsCompact s)
    (hlocal : ∀ x ∈ s, ∃ r : ℝ, 0 < r ∧ IsBoundedOn g (s ∩ ball x r)) :
    IsBoundedOn g s := by
  classical
  choose r hr hg using fun x : s => hlocal x x.property
  choose M hM hb using hg
  have hcover : s ⊆ ⋃ x : s, ball (x : Space n) (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover _ (fun x => isOpen_ball) hcover
  refine ⟨∑ x ∈ t, M x, Finset.sum_nonneg (fun x _ => hM x), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact (hb y x ⟨hx, hxy⟩).trans (Finset.single_le_sum (fun z _ => hM z) hy)

/-- The compact Lebesgue-number argument supplies all-pairs Hölder bounds. -/
lemma isHolderOn_of_local_on_compact {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {g : Space n → ℝ} {s : Set (Space n)} (hc : IsCompact s)
    (hlocal : ∀ x ∈ s, ∃ r : ℝ, 0 < r ∧ IsHolderOn α g (s ∩ ball x r)) :
    IsHolderOn α g s := by
  classical
  choose r hr hg using fun x : s => hlocal x x.property
  choose M H hM hH hb hd using hg
  let U : s → Set (Space n) := fun x => ball (x : Space n) (r x)
  have hcover : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover U (fun x => isOpen_ball) hcover
  let A := ∑ i ∈ t, M i
  let B := ∑ i ∈ t, H i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hM i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hH i)
  have hgb : ∀ x ∈ s, ‖g x‖ ≤ A := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact (hb i x ⟨hx, hxi⟩).trans (Finset.single_le_sum (fun j _ => hM j) hi)
  have hcover' : s ⊆ ⋃ i : t, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric hc (fun i : t => isOpen_ball) hcover'
  have hδα : 0 < δ ^ α := Real.rpow_pos_of_pos hδ _
  refine ⟨A, B + 2 * A / δ ^ α, hA, by positivity, hgb, ?_⟩
  intro x hx y hy
  by_cases hxy : dist x y < δ
  · obtain ⟨i, hi⟩ := hLeb x hx
    have hxi : x ∈ U i := hi (by simpa using hδ)
    have hyi : y ∈ U i := hi (by simpa only [mem_ball, dist_comm] using hxy)
    have hib : H i ≤ B := Finset.single_le_sum (fun j _ => hH j) i.property
    exact (hd i x ⟨hx, hxi⟩ y ⟨hy, hyi⟩).trans
      (mul_le_mul_of_nonneg_right (hib.trans (le_add_of_nonneg_right (by positivity)))
        (Real.rpow_nonneg dist_nonneg _))
  · have hpow : δ ^ α ≤ dist x y ^ α :=
      Real.rpow_le_rpow hδ.le (le_of_not_gt hxy) hα
    calc
      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * A := by linarith [hgb x hx, hgb y hy]
      _ = (2 * A / δ ^ α) * δ ^ α := by field_simp
      _ ≤ (2 * A / δ ^ α) * dist x y ^ α :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (B + 2 * A / δ ^ α) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB)
          (Real.rpow_nonneg dist_nonneg _)

lemma within_jets_restrict_open {n : ℕ} (u : Space n → ℝ)
    (s : Set (Space n)) {U : Set (Space n)} (hU : IsOpen U) {x : Space n} (hx : x ∈ U) :
    (∀ i, firstPartialWithin u (s ∩ U) i x = firstPartialWithin u s i x) ∧
    ∀ i j, secondPartialWithin u (s ∩ U) i j x = secondPartialWithin u s i j x := by
  have heq : s ∩ U =ᶠ[𝓝 x] s := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [mem_inter_iff, hy, and_true]
  exact ⟨fun i => within_first_congr_set u heq i,
    fun i j => within_second_congr_set u heq i j⟩

lemma local_within_jet_bounds_on_compact {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {u : Space n → ℝ} {s k : Set (Space n)} (hc : IsCompact k) (hk : k ⊆ s)
    (hu : IsLocC2HolderWithinOn α u s) :
    IsBoundedOn u k ∧ (∀ i, IsBoundedOn (firstPartialWithin u s i) k) ∧
      ∀ i j, IsHolderOn α (secondPartialWithin u s i j) k := by
  have hp : ∀ x ∈ k, ∃ δ : ℝ, 0 < δ ∧ IsBoundedOn u (k ∩ ball x δ) ∧
      (∀ i, IsBoundedOn (firstPartialWithin u s i) (k ∩ ball x δ)) ∧
      ∀ i j, IsHolderOn α (secondPartialWithin u s i j) (k ∩ ball x δ) := by
    intro x hx
    obtain ⟨δ, hδ, hpatch⟩ := hu.2 x (hk hx)
    have hsub : k ∩ ball x δ ⊆ s ∩ ball x δ := fun y hy => ⟨hk hy.1, hy.2⟩
    refine ⟨δ, hδ, P201.Elliptic.PoissonSchauder.boundedOn_mono hpatch.2.1 hsub, ?_, ?_⟩
    · intro i
      obtain ⟨M, hM, hb⟩ := hpatch.2.2.1 i
      refine ⟨M, hM, ?_⟩
      intro y hy
      rw [← (within_jets_restrict_open u s isOpen_ball hy.2).1 i]
      exact hb y (hsub hy)
    · intro i j
      apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
        (P201.Elliptic.PoissonSchauder.isHolderOn_mono (hpatch.2.2.2 i j) hsub)
      intro y hy
      exact ((within_jets_restrict_open u s isOpen_ball hy.2).2 i j).symm
  refine ⟨boundedOn_of_local_on_compact hc (fun x hx => ?_), ?_, ?_⟩
  · obtain ⟨δ, hδ, hb, _⟩ := hp x hx
    exact ⟨δ, hδ, hb⟩
  · intro i
    apply boundedOn_of_local_on_compact hc
    intro x hx
    obtain ⟨δ, hδ, _, hb, _⟩ := hp x hx
    exact ⟨δ, hδ, hb i⟩
  · intro i j
    apply isHolderOn_of_local_on_compact hα hc
    intro x hx
    obtain ⟨δ, hδ, _, _, hb⟩ := hp x hx
    exact ⟨δ, hδ, hb i j⟩

lemma locally_within_regular_restriction {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {u : Space n → ℝ} {s k U : Set (Space n)} (hc : IsCompact k) (hk : k ⊆ s)
    (hU : IsOpen U) (hUk : s ∩ U ⊆ k) (hu : IsLocC2HolderWithinOn α u s) :
    IsC2HolderUpToOn α u (s ∩ U) := by
  obtain ⟨hb, hfirst, hsecond⟩ := local_within_jet_bounds_on_compact hα hc hk hu
  refine ⟨hu.1.mono inter_subset_left,
    P201.Elliptic.PoissonSchauder.boundedOn_mono hb hUk, ?_, ?_⟩
  · intro i
    obtain ⟨M, hM, hb⟩ := hfirst i
    refine ⟨M, hM, ?_⟩
    intro x hx
    rw [(within_jets_restrict_open u s hU hx.2).1 i]
    exact hb x (hUk hx)
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono (hsecond i j) hUk)
    intro x hx
    exact (within_jets_restrict_open u s hU hx.2).2 i j

lemma c2HolderOn_of_local_on_compact {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (Ω : Domain n) {s : Set (Space n)} (hc : IsCompact s) (hs : s ⊆ Ω)
    {u : Space n → ℝ} (hu : IsC2HolderLocOn α u Ω) : IsC2HolderOn α u s := by
  refine ⟨hu.1.mono hs,
    P201.Elliptic.PoissonSchauder.boundedOn_of_continuousOn_compact hc
      (hu.1.continuousOn.mono hs), ?_, ?_⟩
  · intro i
    have hd : ContinuousOn (multiPartial u {i}) Ω :=
      (P102.U4.partialWord_contDiffOn Ω hu.1 (({i} : MultiIndex n).sort (· ≤ ·)) 0
        (by simp)).continuousOn
    exact P201.Elliptic.PoissonSchauder.boundedOn_of_continuousOn_compact hc (hd.mono hs)
  · intro i j
    apply isHolderOn_of_local_on_compact hα hc
    intro x hx
    obtain ⟨r, hr, hrΩ, hholder⟩ := hu.2 x (hs hx)
    exact ⟨r, hr, P201.Elliptic.PoissonSchauder.isHolderOn_mono (hholder i j)
      inter_subset_right⟩

lemma ball_regular_restriction {n : ℕ} {α R : ℝ} {a : Space n} {u : Space n → ℝ}
    (hα : 0 ≤ α) (hu : IsC2HolderLocOn α u ⟨ball a R, isOpen_ball⟩)
    {r : ℝ} (hrR : r < R) : IsC2HolderUpToOn α u (ball a r) := by
  have hsub : closedBall a r ⊆ ball a R := closedBall_subset_ball hrR
  have hclass := c2HolderOn_of_local_on_compact hα ⟨ball a R, isOpen_ball⟩
    (isCompact_closedBall a r) hsub hu
  have hb : IsC2HolderOn α u (ball a r) :=
    P201.Elliptic.PoissonSchauder.c2HolderOn_mono hclass ball_subset_closedBall
  have hjets := within_jets_of_extension ⟨ball a R, isOpen_ball⟩ isOpen_ball.uniqueDiffOn
    (ball_subset_ball hrR.le) hu.1 (fun _ _ => rfl)
  refine ⟨hb.1, hb.2.1, ?_, ?_⟩
  · intro i
    obtain ⟨M, hM, hMi⟩ := hb.2.2.1 i
    exact ⟨M, hM, fun x hx => by rw [(hjets.1 i) hx]; exact hMi x hx⟩
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr (hb.2.2.2 i j)
    exact hjets.2 i j

lemma halfBall_regular_restriction {m : ℕ} {α R : ℝ} {u : Space (m + 1) → ℝ}
    (hα : 0 ≤ α) (hu : IsLocC2HolderWithinOn α u (halfBallWithFace m R))
    {r : ℝ} (hrR : r < R) : IsC2HolderUpToOn α u (halfBallWithFace m r) := by
  let k : Set (Space (m + 1)) := closedBall 0 r ∩ P201Specs.Elliptic.HalfSpaceLift.closedHalfSpace m
  have hc : IsCompact k := (isCompact_closedBall (0 : Space (m + 1)) r).inter_right
    (P201.Elliptic.HalfSpaceLift.isClosed_closedHalfSpace m)
  have hk : k ⊆ halfBallWithFace m R := fun x hx =>
    ⟨closedBall_subset_ball hrR hx.1, hx.2⟩
  have heq : halfBallWithFace m R ∩ ball 0 r = halfBallWithFace m r := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩; exact ⟨hx', hx.2⟩
    · intro hx; exact ⟨⟨ball_subset_ball hrR.le hx.1, hx.2⟩, hx.1⟩
  rw [← heq]
  exact locally_within_regular_restriction hα hc hk isOpen_ball
    (fun x hx => ⟨ball_subset_closedBall hx.2, hx.1.2⟩) hu

/-- Constants from interpolation can be applied at every inner radius; no
new scale-dependent constant is used in this restriction bridge. -/
theorem restriction : RestrictionStatement := by
  constructor
  · intro n α R a u hα hα1 hR hu r hr hrR
    have hclass := ball_regular_restriction hα.le hu hrR
    exact ⟨hclass, finite_weighted_norms hα.le hα1.le hr (convex_ball a r)
      isOpen_ball.uniqueDiffOn Subset.rfl hclass⟩
  · intro m α R u hα hα1 hR hu r hr hrR
    have hclass := halfBall_regular_restriction hα.le hu hrR
    exact ⟨hclass, finite_weighted_norms hα.le hα1.le hr
      ((convex_ball 0 r).inter (P201.Elliptic.HalfSpaceLift.convex_closedHalfSpace m))
      (uniqueDiffOn_halfBallWithFace m r) inter_subset_left hclass⟩


lemma radial_jets_restrict {n : ℕ} (u : Space n → ℝ) (a : Space n)
    (q : Set (Space n)) {r R : ℝ} (hrR : r < R) {x : Space n} (hx : x ∈ ball a r) :
    (∀ i, firstPartialWithin u (ball a r ∩ q) i x =
      firstPartialWithin u (ball a R ∩ q) i x) ∧
    ∀ i j, secondPartialWithin u (ball a r ∩ q) i j x =
      secondPartialWithin u (ball a R ∩ q) i j x := by
  have he : ball a r ∩ q =ᶠ[𝓝 x] ball a R ∩ q := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact propext ⟨fun h => ⟨ball_subset_ball hrR.le h.1, h.2⟩, fun h => ⟨hy, h.2⟩⟩
  exact ⟨fun i => within_first_congr_set u he i, fun i j => within_second_congr_set u he i j⟩

/-- Uniform inner-radius bounds pass directly to each outer point and pair.
The ambient representative is arbitrary, and no outer norm finiteness is used. -/
lemma jetBounds_exhaustion {n : ℕ} {α R A B H : ℝ} {a : Space n}
    {q : Set (Space n)} {u : Space n → ℝ} (hα : 0 < α) (hR : 0 < R)
    (hb : ∀ r : ℝ, R / 2 < r → r < R → JetBounds α a r (ball a r ∩ q) u A B H) :
    JetBounds α a R (ball a R ∩ q) u A B H := by
  have hhalf : R / 2 < R := by linarith
  constructor
  · intro i x hx
    have hc : Continuous (fun r : ℝ =>
        (r - dist x a) * ‖firstPartialWithin u (ball a R ∩ q) i x‖) := by fun_prop
    apply le_of_tendsto (x := 𝓝[<] R) (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsLT hhalf, Ioo_mem_nhdsLT (mem_ball.mp hx.1)] with r hr hxr
    have hxi : x ∈ ball a r := mem_ball.mpr hxr.1
    have h := (hb r hr.1 hr.2).1 i x ⟨hxi, hx.2⟩
    simpa only [radialWeight, (radial_jets_restrict u a q hr.2 hxi).1 i] using h
  constructor
  · intro i j x hx
    have hc : Continuous (fun r : ℝ =>
        (r - dist x a) ^ 2 * ‖secondPartialWithin u (ball a R ∩ q) i j x‖) := by fun_prop
    apply le_of_tendsto (x := 𝓝[<] R) (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsLT hhalf, Ioo_mem_nhdsLT (mem_ball.mp hx.1)] with r hr hxr
    have hxi : x ∈ ball a r := mem_ball.mpr hxr.1
    have h := (hb r hr.1 hr.2).2.1 i j x ⟨hxi, hx.2⟩
    simpa only [radialWeight, (radial_jets_restrict u a q hr.2 hxi).2 i j] using h
  · intro i j x hx y hy
    have hc : Continuous (fun r : ℝ =>
        min (r - dist x a) (r - dist y a) ^ (2 + α) *
        ‖secondPartialWithin u (ball a R ∩ q) i j x -
          secondPartialWithin u (ball a R ∩ q) i j y‖) := by
      apply Continuous.mul _ continuous_const
      exact ((continuous_id.sub continuous_const).min
        (continuous_id.sub continuous_const)).rpow_const (fun _ => Or.inr (by linarith))
    apply le_of_tendsto (x := 𝓝[<] R) (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsLT hhalf, Ioo_mem_nhdsLT (mem_ball.mp hx.1),
      Ioo_mem_nhdsLT (mem_ball.mp hy.1)] with r hr hxr hyr
    have hxi : x ∈ ball a r := mem_ball.mpr hxr.1
    have hyi : y ∈ ball a r := mem_ball.mpr hyr.1
    have h := (hb r hr.1 hr.2).2.2 i j x ⟨hxi, hx.2⟩ y ⟨hyi, hy.2⟩
    simpa only [radialWeight, (radial_jets_restrict u a q hr.2 hxi).2 i j,
      (radial_jets_restrict u a q hr.2 hyi).2 i j] using h

theorem exhaustion : ExhaustionStatement := by
  constructor
  · intro n α R A B H a u hα hR hb
    simpa only [inter_univ] using jetBounds_exhaustion (q := univ) hα hR
      (fun r hr hrR => by simpa only [inter_univ] using hb r hr hrR)
  · intro m α R A B H u hα hR hb
    exact jetBounds_exhaustion hα hR hb

/-- A forward rectangular second difference controls each ordered coordinate
Hessian entry directly. This avoids any assumption about an ambient extension
or about a separately supplied Hessian. -/
lemma mixed_forward_difference_bound {n : ℕ} {u : Space n → ℝ} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (hu : ContDiffOn ℝ 2 u s)
    {x : Space n} (i j : Fin n) {h K M : ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hseg : ∀ t ∈ Icc 0 h, ∀ r ∈ Icc 0 h,
      x + t • coordinate n i + r • coordinate n j ∈ s)
    (hosc : ∀ t ∈ Icc 0 h, ∀ r ∈ Icc 0 h,
      ‖secondPartialWithin u s i j (x + t • coordinate n i + r • coordinate n j) -
        secondPartialWithin u s i j x‖ ≤ K)
    (hb : ∀ z ∈ s, ‖u z‖ ≤ M) :
    ‖secondPartialWithin u s i j x‖ ≤ 4 * M / h ^ 2 + K := by
  let p := fun t r : ℝ => x + t • coordinate n i + r • coordinate n j
  let Q := secondPartialWithin u s i j x
  have h0 : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, hh.le⟩
  have h1 : h ∈ Icc 0 h := ⟨hh.le, le_rfl⟩
  have hj : ContDiffOn ℝ 1 (firstPartialWithin u s j) s :=
    (hu.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
  have hcurve₁ (r t : ℝ) : HasDerivWithinAt (fun t : ℝ => p t r)
      (coordinate n i) (Icc 0 h) t := by
    simpa only [p, one_smul, id_eq] using
      (((hasDerivAt_id t).smul_const (coordinate n i)).const_add x).add_const
        (r • coordinate n j) |>.hasDerivWithinAt
  have hcurve₂ (t r : ℝ) : HasDerivWithinAt (fun r : ℝ => p t r)
      (coordinate n j) (Icc 0 h) r := by
    simpa only [p, one_smul, id_eq] using
      ((hasDerivAt_id r).smul_const (coordinate n j)).const_add (x + t • coordinate n i)
        |>.hasDerivWithinAt
  have hdiff : ∀ r ∈ Icc 0 h,
      ‖firstPartialWithin u s j (p h r) - firstPartialWithin u s j (p 0 r) - Q * h‖ ≤ K * h := by
    intro r hr
    have hd : ∀ t ∈ Icc 0 h,
        HasDerivWithinAt (fun t => firstPartialWithin u s j (p t r) - Q * t)
          (secondPartialWithin u s i j (p t r) - Q) (Icc 0 h) t := by
      intro t ht
      have hD := ((hj.differentiableOn (by norm_num) _ (hseg t ht r hr)).hasFDerivWithinAt).comp_hasDerivWithinAt t (hcurve₁ r t) (fun a ha => hseg a ha r hr)
      convert hD.sub ((hasDerivWithinAt_id t (Icc 0 h)).const_mul Q) using 1 <;>
        (try funext a) <;> simp [Pi.sub_apply, Function.comp_def, secondPartialWithin, p]
    have he := norm_image_sub_le_of_norm_deriv_le_segment' hd
      (fun t ht => hosc t (Ico_subset_Icc_self ht) r hr) h h1
    convert he using 1 <;> congr 1 <;> ring
  let f := fun r : ℝ => u (p h r) - u (p 0 r) - Q * h * r
  have hd : ∀ r ∈ Icc 0 h,
      HasDerivWithinAt f
        (firstPartialWithin u s j (p h r) - firstPartialWithin u s j (p 0 r) - Q * h)
        (Icc 0 h) r := by
    intro r hr
    have hD (t : ℝ) (ht : t ∈ Icc 0 h) :=
      ((hu.differentiableOn (by norm_num) _ (hseg t ht r hr)).hasFDerivWithinAt).comp_hasDerivWithinAt r (hcurve₂ t r) (fun b hb => hseg t ht b hb)
    convert ((hD h h1).sub (hD 0 h0)).sub
      ((hasDerivWithinAt_id r (Icc 0 h)).const_mul (Q * h)) using 1 <;>
      (try funext a) <;> simp [Pi.sub_apply, Function.comp_def, firstPartialWithin, f, p]
  have hrem : ‖f h - f 0‖ ≤ K * h ^ 2 := by
    have he := norm_image_sub_le_of_norm_deriv_le_segment' hd
      (fun r hr => hdiff r (Ico_subset_Icc_self hr)) h h1
    simpa only [pow_two, mul_assoc, sub_zero] using he
  have hv : ‖u (p h h) - u (p 0 h) - (u (p h 0) - u (p 0 0))‖ ≤ 4 * M := by
    calc
      _ ≤ ‖u (p h h) - u (p 0 h)‖ + ‖u (p h 0) - u (p 0 0)‖ := norm_sub_le _ _
      _ ≤ (‖u (p h h)‖ + ‖u (p 0 h)‖) + (‖u (p h 0)‖ + ‖u (p 0 0)‖) :=
        add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ ≤ 4 * M := by
        have ha := hb _ (hseg h h1 h h1)
        have hb' := hb _ (hseg 0 h0 h h1)
        have hc := hb _ (hseg h h1 0 h0)
        have hd' := hb _ (hseg 0 h0 0 h0)
        change ‖u (p h h)‖ ≤ M at ha
        change ‖u (p 0 h)‖ ≤ M at hb'
        change ‖u (p h 0)‖ ≤ M at hc
        change ‖u (p 0 0)‖ ≤ M at hd'
        linarith
  have heq : Q * h ^ 2 =
      (u (p h h) - u (p 0 h) - (u (p h 0) - u (p 0 0))) - (f h - f 0) := by
    dsimp [f]; ring
  have hmain : ‖Q‖ * h ^ 2 ≤ 4 * M + K * h ^ 2 := by
    calc
      _ = ‖Q * h ^ 2‖ := by rw [norm_mul, Real.norm_of_nonneg (sq_nonneg h)]
      _ = _ := congrArg norm heq
      _ ≤ ‖u (p h h) - u (p 0 h) - (u (p h 0) - u (p 0 0))‖ + ‖f h - f 0‖ := norm_sub_le _ _
      _ ≤ 4 * M + K * h ^ 2 := add_le_add hv hrem
  have hmain := (le_div_iff₀ (sq_pos_of_pos hh)).mpr hmain
  calc
    ‖secondPartialWithin u s i j x‖ ≤ (4 * M + K * h ^ 2) / h ^ 2 := hmain
    _ = _ := by field_simp

lemma weightedSupOn_nonneg {n : ℕ} {a : Space n} {R : ℝ} {s : Set (Space n)}
    (hs : s ⊆ ball a R) (g : Space n → ℝ) (j : ℕ) :
    0 ≤ weightedSupOn j a R g s := by
  apply P201.Elliptic.PoissonSchauder.sSup_nonneg_of_nonneg
  rintro v ⟨x, hx, rfl⟩
  exact mul_nonneg (pow_nonneg (radialWeight_pos hs hx).le j) (norm_nonneg _)

lemma weightedSeminormOn_nonneg {n : ℕ} (a : Space n) (R α : ℝ) (s : Set (Space n))
    (g : Space n → ℝ) (j : ℕ) (hs : s ⊆ ball a R) : 0 ≤ weightedSeminormOn j α a R g s := by
  apply P201.Elliptic.PoissonSchauder.sSup_nonneg_of_nonneg
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (le_min (radialWeight_pos hs hx).le (radialWeight_pos hs hy).le) _) (norm_nonneg _))
    (Real.rpow_nonneg dist_nonneg _)

lemma weightedSupOn_le {n : ℕ} {a : Space n} {R C : ℝ} {s : Set (Space n)}
    {g : Space n → ℝ} {j : ℕ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ s, radialWeight a R x ^ j * ‖g x‖ ≤ C) :
    weightedSupOn j a R g s ≤ C := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa [weightedSupOn, weightedValueSet] using hC
  · apply csSup_le (s := weightedValueSet j a R g s)
      ⟨radialWeight a R hs.choose ^ j * ‖g hs.choose‖, hs.choose, hs.choose_spec, rfl⟩
    rintro q ⟨x, hx, rfl⟩
    exact hb x hx

lemma weightedSeminormOn_le {n : ℕ} {a : Space n} {R C α : ℝ} {s : Set (Space n)}
    {g : Space n → ℝ} {j : ℕ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ s, ∀ y ∈ s,
      min (radialWeight a R x) (radialWeight a R y) ^ ((j : ℝ) + α) * ‖g x - g y‖ ≤
        C * dist x y ^ α) : weightedSeminormOn j α a R g s ≤ C := by
  by_cases he : (weightedPairSet j α a R g s).Nonempty
  · apply csSup_le he
    rintro q ⟨x, hx, y, hy, hxy, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) α)).mpr (hb x hx y hy)
  · unfold weightedSeminormOn
    rw [Set.not_nonempty_iff_eq_empty.mp he]
    simpa only [Real.sSup_empty] using hC

lemma weighted_pair_bound {n : ℕ} {a : Space n} {R α : ℝ} {s : Set (Space n)}
    {g : Space n → ℝ} {j : ℕ} (hs : s ⊆ ball a R) (hb : BddAbove (weightedPairSet j α a R g s))
    {x y : Space n} (hx : x ∈ s) (hy : y ∈ s) :
    min (radialWeight a R x) (radialWeight a R y) ^ ((j : ℝ) + α) * ‖g x - g y‖ ≤
      weightedSeminormOn j α a R g s * dist x y ^ α := by
  by_cases hxy : x = y
  · subst y
    simpa only [sub_self, norm_zero, mul_zero] using mul_nonneg
      (weightedSeminormOn_nonneg a R α s g j hs) (Real.rpow_nonneg dist_nonneg α)
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) α)).mp
      (le_csSup hb ⟨x, hx, y, hy, hxy, rfl⟩)

/-- Every forward coordinate rectangle of this size stays inside the sphere;
its spherical distance remains comparable to that of its starting point. -/
lemma forward_rectangle_geometry {n : ℕ} {a x : Space n} {R η : ℝ}
    {q : Set (Space n)}
    (hq : ∀ z ∈ q, ∀ i : Fin n, ∀ t : ℝ, 0 ≤ t → z + t • coordinate n i ∈ q)
    (hx : x ∈ ball a R ∩ q) (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (i j : Fin n) {t r : ℝ}
    (ht : t ∈ Icc 0 (η * radialWeight a R x / 2))
    (hr : r ∈ Icc 0 (η * radialWeight a R x / 2)) :
    x + t • coordinate n i + r • coordinate n j ∈ ball a R ∩ q ∧
      radialWeight a R x / 2 ≤ radialWeight a R (x + t • coordinate n i + r • coordinate n j) ∧
      dist (x + t • coordinate n i + r • coordinate n j) x ≤ η * radialWeight a R x := by
  let d := radialWeight a R x
  have hd : 0 < d := radialWeight_pos inter_subset_left hx
  have htadd : t + r ≤ η * d := by dsimp [d]; linarith [ht.2, hr.2]
  have hdist : dist (x + t • coordinate n i + r • coordinate n j) x ≤ η * d := by
    calc
      _ = ‖t • coordinate n i + r • coordinate n j‖ := by
        rw [dist_eq_norm]; congr 1; abel
      _ ≤ ‖t • coordinate n i‖ + ‖r • coordinate n j‖ := norm_add_le _ _
      _ = t + r := by simp [norm_smul, Real.norm_of_nonneg ht.1,
          Real.norm_of_nonneg hr.1, coordinate_norm]
      _ ≤ η * d := htadd
  have htriangle := dist_triangle (x + t • coordinate n i + r • coordinate n j) x a
  have hdη : η * d ≤ d / 4 := by nlinarith
  refine ⟨⟨mem_ball.mpr ?_, hq _ (hq x hx.2 i t ht.1) j r hr.1⟩, ?_, hdist⟩
  · dsimp [d, radialWeight] at hd hdist hdη
    linarith
  · dsimp [d, radialWeight] at hd hdist hdη ⊢
    linarith

/-- Scaling identity for the Hölder oscillation on a forward rectangle. -/
lemma scaled_oscillation_identity {d η α N : ℝ} (hd : 0 < d) (hη : 0 < η) :
    d ^ 2 * (N * (η * d) ^ α / (d / 2) ^ (2 + α)) =
      (4 * (2 : ℝ) ^ α * η ^ α) * N := by
  rw [Real.mul_rpow hη.le hd.le, Real.div_rpow hd.le (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_add hd, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_two, Real.rpow_two]
  field_simp
  <;> ring

/-- The weighted Hessian interpolation before choosing the small step.
The coefficient of N₂ tends to zero with η. -/
lemma weighted_hessian_estimate {n : ℕ} {a : Space n} {R α η : ℝ}
    {q : Set (Space n)} {u : Space n → ℝ} (hα : 0 ≤ α)
    (hR : 0 < R) (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (hq : ∀ z ∈ q, ∀ i : Fin n, ∀ t : ℝ, 0 ≤ t → z + t • coordinate n i ∈ q)
    (hs : UniqueDiffOn ℝ (ball a R ∩ q))
    (hu : IsC2HolderUpToOn α u (ball a R ∩ q))
    (hf : FiniteWeightedNorms α a R u (ball a R ∩ q)) :
    M2 a R u (ball a R ∩ q) ≤ (16 * (n : ℝ) ^ 2 / η ^ 2) * M0 u (ball a R ∩ q) +
      (4 * (2 : ℝ) ^ α * η ^ α) * N2 α a R u (ball a R ∩ q) := by
  classical
  let s := ball a R ∩ q
  have hM : 0 ≤ M0 u s := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hentry (i j : Fin n) :
      weightedSupOn 2 a R (secondPartialWithin u s i j) s ≤
        (16 / η ^ 2) * M0 u s + (4 * (2 : ℝ) ^ α * η ^ α) *
          weightedSeminormOn 2 α a R (secondPartialWithin u s i j) s := by
    let N := weightedSeminormOn 2 α a R (secondPartialWithin u s i j) s
    have hN : 0 ≤ N := weightedSeminormOn_nonneg _ _ _ _ _ _ inter_subset_left
    apply weightedSupOn_le (by positivity)
    intro x hx
    let d := radialWeight a R x
    have hd : 0 < d := radialWeight_pos inter_subset_left hx
    let h := η * d / 2
    have hh : 0 < h := by positivity
    let K := N * (η * d) ^ α / (d / 2) ^ (2 + α)
    have hK : 0 ≤ K := by positivity
    have hgeom := fun {t r : ℝ} => forward_rectangle_geometry hq hx hη hη1 i j (t := t) (r := r)
    have hosc : ∀ t ∈ Icc 0 h, ∀ r ∈ Icc 0 h,
        ‖secondPartialWithin u s i j (x + t • coordinate n i + r • coordinate n j) -
          secondPartialWithin u s i j x‖ ≤ K := by
      intro t ht r hr
      obtain ⟨hz, hw, hdist⟩ := hgeom ht hr
      have hpair := weighted_pair_bound inter_subset_left (hf.2.2.2.2.2 i j) hz hx
      have hw' : d / 2 ≤ min (radialWeight a R (x + t • coordinate n i + r • coordinate n j)) d :=
        le_min hw (by linarith)
      have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ d / 2) hw' (by positivity : 0 ≤ 2 + α)
      have hdα := Real.rpow_le_rpow dist_nonneg hdist hα
      apply (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < d / 2) (2 + α))).mpr
      calc
        _ ≤ min (radialWeight a R (x + t • coordinate n i + r • coordinate n j)) d ^ (2 + α) *
            ‖secondPartialWithin u s i j (x + t • coordinate n i + r • coordinate n j) -
              secondPartialWithin u s i j x‖ := by
          simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpow (norm_nonneg
            (secondPartialWithin u s i j (x + t • coordinate n i + r • coordinate n j) -
              secondPartialWithin u s i j x))
        _ ≤ N * dist (x + t • coordinate n i + r • coordinate n j) x ^ α := hpair
        _ ≤ N * (η * d) ^ α := mul_le_mul_of_nonneg_left hdα hN
    have hdiff := mixed_forward_difference_bound hs hu.1 i j hh hK
      (fun t ht r hr => (hgeom ht hr).1) hosc
      (fun z hz => P201.Elliptic.PoissonSchauder.norm_le_supNormOn hu.2.1 hz)
    have hscaled := mul_le_mul_of_nonneg_left hdiff (sq_nonneg d)
    have hid : d ^ 2 * (4 * M0 u s / h ^ 2 + K) =
        (16 / η ^ 2) * M0 u s + (4 * (2 : ℝ) ^ α * η ^ α) * N := by
      rw [mul_add, scaled_oscillation_identity hd hη]
      dsimp [h]
      field_simp
      <;> ring
    change d ^ 2 * ‖secondPartialWithin u s i j x‖ ≤ d ^ 2 * (4 * M0 u s / h ^ 2 + K) at hscaled
    rw [hid] at hscaled
    exact hscaled
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hentry i j))
  convert hsum using 1 <;>
    simp only [M2, N2, s, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring

lemma M1_nonneg {n : ℕ} {a : Space n} {R : ℝ} {s : Set (Space n)}
    (hs : s ⊆ ball a R) (u : Space n → ℝ) : 0 ≤ M1 a R u s :=
  Finset.sum_nonneg (fun i _ => weightedSupOn_nonneg hs _ _)

lemma M2_nonneg {n : ℕ} {a : Space n} {R : ℝ} {s : Set (Space n)}
    (hs : s ⊆ ball a R) (u : Space n → ℝ) : 0 ≤ M2 a R u s :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => weightedSupOn_nonneg hs _ _))

lemma N2_nonneg {n : ℕ} {a : Space n} {R α : ℝ} {s : Set (Space n)}
    (hs : s ⊆ ball a R) (u : Space n → ℝ) : 0 ≤ N2 α a R u s :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => weightedSeminormOn_nonneg _ _ _ _ _ _ hs))

lemma first_weighted_le_M1 {n : ℕ} {a : Space n} {R α : ℝ} {s : Set (Space n)}
    {u : Space n → ℝ} (hs : s ⊆ ball a R) (hf : FiniteWeightedNorms α a R u s)
    (i : Fin n) {x : Space n} (hx : x ∈ s) :
    radialWeight a R x * ‖firstPartialWithin u s i x‖ ≤ M1 a R u s := by
  have h : radialWeight a R x ^ 1 * ‖firstPartialWithin u s i x‖ ≤
      weightedSupOn 1 a R (firstPartialWithin u s i) s := le_csSup (hf.2.1 i) ⟨x, hx, rfl⟩
  rw [pow_one] at h
  exact h.trans
      (Finset.single_le_sum (fun k _ => weightedSupOn_nonneg hs _ _) (Finset.mem_univ i))

lemma second_weighted_le_M2 {n : ℕ} {a : Space n} {R α : ℝ} {s : Set (Space n)}
    {u : Space n → ℝ} (hs : s ⊆ ball a R) (hf : FiniteWeightedNorms α a R u s)
    (i j : Fin n) {x : Space n} (hx : x ∈ s) :
    radialWeight a R x ^ 2 * ‖secondPartialWithin u s i j x‖ ≤ M2 a R u s := by
  have h : radialWeight a R x ^ 2 * ‖secondPartialWithin u s i j x‖ ≤
      weightedSupOn 2 a R (secondPartialWithin u s i j) s :=
    le_csSup (hf.2.2.1 i j) ⟨x, hx, rfl⟩
  apply h.trans
  apply (Finset.single_le_sum (fun k _ => weightedSupOn_nonneg hs _ _) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg
    (fun l _ => weightedSupOn_nonneg hs _ _)) (Finset.mem_univ i)

lemma weighted_gradient_bound {n : ℕ} {a : Space n} {R α : ℝ} {s : Set (Space n)}
    {u : Space n → ℝ} (hs : s ⊆ ball a R) (hf : FiniteWeightedNorms α a R u s)
    {x : Space n} (hx : x ∈ s) :
    radialWeight a R x * ‖fderivWithin ℝ u s x‖ ≤ (n : ℝ) * M1 a R u s := by
  have hd := radialWeight_pos hs hx
  have hb : ∀ i, ‖firstPartialWithin u s i x‖ ≤ M1 a R u s / radialWeight a R x := by
    intro i
    apply (le_div_iff₀ hd).mpr
    simpa only [mul_comm] using first_weighted_le_M1 hs hf i hx
  have h := mul_le_mul_of_nonneg_left (within_fderiv_bound hb) hd.le
  calc
    _ ≤ _ := h
    _ = _ := by field_simp

lemma weighted_first_jet_derivative_bound {n : ℕ} {a : Space n} {R α : ℝ} {s : Set (Space n)}
    {u : Space n → ℝ} (hs : s ⊆ ball a R) (hf : FiniteWeightedNorms α a R u s)
    (i : Fin n) {x : Space n} (hx : x ∈ s) :
    radialWeight a R x ^ 2 * ‖fderivWithin ℝ (firstPartialWithin u s i) s x‖ ≤
      (n : ℝ) * M2 a R u s := by
  have hd := sq_pos_of_pos (radialWeight_pos hs hx)
  have hb : ∀ j, ‖firstPartialWithin (firstPartialWithin u s i) s j x‖ ≤
      M2 a R u s / radialWeight a R x ^ 2 := by
    intro j
    apply (le_div_iff₀ hd).mpr
    simpa only [mul_comm, firstPartialWithin, secondPartialWithin] using second_weighted_le_M2 hs hf j i hx
  have h := mul_le_mul_of_nonneg_left (within_fderiv_bound hb) hd.le
  calc
    _ ≤ _ := h
    _ = _ := by field_simp [(radialWeight_pos hs hx).ne']

lemma weighted_lower_pair_estimates {n : ℕ} {a : Space n} {R α : ℝ}
    {s : Set (Space n)} {u : Space n → ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hc : Convex ℝ s) (hs : UniqueDiffOn ℝ s) (hsR : s ⊆ ball a R)
    (hu : IsC2HolderUpToOn α u s) (hf : FiniteWeightedNorms α a R u s) :
    N0 α a R u s ≤ (n : ℝ) * M1 a R u s + 2 * M0 u s ∧
    N1 α a R u s ≤ (n : ℝ) ^ 2 * M2 a R u s + 2 * (n : ℝ) * M1 a R u s := by
  have hM0 : 0 ≤ M0 u s := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hM1 := M1_nonneg hsR u
  have hM2 := M2_nonneg hsR u
  constructor
  · apply weightedSeminormOn_le (by positivity)
    intro x hx y hy
    have h := radial_weighted_holder_interpolation 0 hα hα1 zero_lt_one hM0
      (show 0 ≤ (n : ℝ) * M1 a R u s by positivity) hc hsR
      (fun z hz => (hu.1.differentiableOn (by norm_num) z hz).hasFDerivWithinAt)
      (fun z hz => by simpa only [pow_zero, one_mul, M0] using
        P201.Elliptic.PoissonSchauder.norm_le_supNormOn hu.2.1 hz)
      (fun z hz => by simpa only [zero_add, pow_one, radialWeight] using weighted_gradient_bound hsR hf hz) hx hy
    simpa only [Real.one_rpow, one_mul, div_one, radialWeight] using h
  · have hentry (i : Fin n) :
        weightedSeminormOn 1 α a R (firstPartialWithin u s i) s ≤
          (n : ℝ) * M2 a R u s + 2 * M1 a R u s := by
      apply weightedSeminormOn_le (by positivity)
      intro x hx y hy
      have hi : ContDiffOn ℝ 1 (firstPartialWithin u s i) s :=
        (hu.1.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
      have h := radial_weighted_holder_interpolation 1 hα hα1 zero_lt_one hM1
        (show 0 ≤ (n : ℝ) * M2 a R u s by positivity) hc hsR
        (fun z hz => (hi.differentiableOn (by norm_num) z hz).hasFDerivWithinAt)
        (fun z hz => by simpa only [pow_one, radialWeight] using first_weighted_le_M1 hsR hf i hz)
        (fun z hz => weighted_first_jet_derivative_bound hsR hf i hz) hx hy
      simpa only [Real.one_rpow, one_mul, div_one, radialWeight, Nat.cast_one] using h
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hentry i)
    convert hsum using 1 <;> simp only [N1, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] <;> ring

lemma weighted_first_estimate {n : ℕ} {a : Space n} {R α : ℝ}
    {q : Set (Space n)} {u : Space n → ℝ}
    (hq : ∀ z ∈ q, ∀ i : Fin n, ∀ t : ℝ, 0 ≤ t → z + t • coordinate n i ∈ q)
    (hs : UniqueDiffOn ℝ (ball a R ∩ q))
    (hu : IsC2HolderUpToOn α u (ball a R ∩ q))
    (hf : FiniteWeightedNorms α a R u (ball a R ∩ q)) :
    M1 a R u (ball a R ∩ q) ≤ 16 * (n : ℝ) * M0 u (ball a R ∩ q) +
      (n : ℝ) * M2 a R u (ball a R ∩ q) := by
  let s := ball a R ∩ q
  have hM0 : 0 ≤ M0 u s := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hM2 : 0 ≤ M2 a R u s := M2_nonneg inter_subset_left u
  have hentry (i : Fin n) : weightedSupOn 1 a R (firstPartialWithin u s i) s ≤
      16 * M0 u s + M2 a R u s := by
    apply weightedSupOn_le (by positivity)
    intro x hx
    let d := radialWeight a R x
    let h := d / 8
    have hd : 0 < d := radialWeight_pos inter_subset_left hx
    have hh : 0 < h := by positivity
    have hgeom := fun {t r : ℝ} => forward_rectangle_geometry hq hx
      (by norm_num : (0 : ℝ) < 1 / 4) le_rfl i i (t := t) (r := r)
    have he : (1 / 4 : ℝ) * radialWeight a R x / 2 = h := by dsimp [h, d]; ring
    have hseg : ∀ t ∈ Icc 0 h, x + t • coordinate n i ∈ s ∧
        d / 2 ≤ radialWeight a R (x + t • coordinate n i) := by
      intro t ht
      have h := hgeom (by simpa only [he] using ht) (show 0 ∈ Icc 0 ((1 / 4 : ℝ) * radialWeight a R x / 2) by
        constructor; rfl; positivity)
      simpa only [zero_smul, add_zero] using And.intro h.1 h.2.1
    have hcurve (t : ℝ) : HasDerivWithinAt (fun t : ℝ => x + t • coordinate n i)
        (coordinate n i) (Icc 0 h) t := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id t).smul_const (coordinate n i)).const_add x |>.hasDerivWithinAt
    have hi : ContDiffOn ℝ 1 (firstPartialWithin u s i) s :=
      (hu.1.fderivWithin hs (by norm_num)).clm_apply contDiffOn_const
    have hderiv : ∀ t ∈ Icc 0 h, HasDerivWithinAt (fun t => u (x + t • coordinate n i))
        (firstPartialWithin u s i (x + t • coordinate n i)) (Icc 0 h) t := by
      intro t ht
      exact ((hu.1.differentiableOn (by norm_num) _ (hseg t ht).1).hasFDerivWithinAt).comp_hasDerivWithinAt t (hcurve t) (fun r hr => (hseg r hr).1)
    have hderiv₁ : ∀ t ∈ Icc 0 h,
        HasDerivWithinAt (fun t => firstPartialWithin u s i (x + t • coordinate n i))
          (secondPartialWithin u s i i (x + t • coordinate n i)) (Icc 0 h) t := by
      intro t ht
      exact ((hi.differentiableOn (by norm_num) _ (hseg t ht).1).hasFDerivWithinAt).comp_hasDerivWithinAt t (hcurve t) (fun r hr => (hseg r hr).1)
    have hbound : ∀ t ∈ Icc 0 h,
        ‖secondPartialWithin u s i i (x + t • coordinate n i)‖ ≤ 4 * M2 a R u s / d ^ 2 := by
      intro t ht
      have hw := (hseg t ht).2
      have hb := second_weighted_le_M2 inter_subset_left hf i i (hseg t ht).1
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ d / 2) hw 2
      have := (mul_le_mul_of_nonneg_right hp
        (norm_nonneg (secondPartialWithin u s i i (x + t • coordinate n i)))).trans hb
      apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
      nlinarith
    have hb0 : ‖u (x + (0 : ℝ) • coordinate n i)‖ ≤ M0 u s :=
      P201.Elliptic.PoissonSchauder.norm_le_supNormOn hu.2.1 (hseg 0 ⟨le_rfl, hh.le⟩).1
    have hbh : ‖u (x + h • coordinate n i)‖ ≤ M0 u s :=
      P201.Elliptic.PoissonSchauder.norm_le_supNormOn hu.2.1 (hseg h ⟨hh.le, le_rfl⟩).1
    have hdiff := one_sided_first_difference_bound hh
      (show 0 ≤ 4 * M2 a R u s / d ^ 2 by positivity) hderiv hderiv₁ hbound hb0 hbh
    simp only [zero_smul, add_zero] at hdiff
    have hscaled := mul_le_mul_of_nonneg_left hdiff hd.le
    have heq : d * (2 * M0 u s / h + h * (4 * M2 a R u s / d ^ 2)) =
        16 * M0 u s + M2 a R u s / 2 := by dsimp [h]; field_simp; ring
    rw [heq] at hscaled
    simpa only [pow_one] using hscaled.trans (by linarith)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hentry i)
  convert hsum using 1 <;> simp only [M1, s, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring

/-- A dimension-only coefficient for reducing all lower-order terms to M₂. -/
def lowerOrderFactor (n : ℕ) : ℝ :=
  (16 * (n : ℝ) * (1 + 3 * (n : ℝ)) + 2) +
    ((1 + 3 * (n : ℝ)) * (n : ℝ) + 1 + (n : ℝ) ^ 2) + 1

lemma lowerOrderFactor_pos (n : ℕ) : 0 < lowerOrderFactor n := by
  unfold lowerOrderFactor
  positivity

lemma weighted_lower_order_estimate {n : ℕ} {a : Space n} {R α : ℝ}
    {q : Set (Space n)} {u : Space n → ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hc : Convex ℝ q)
    (hq : ∀ z ∈ q, ∀ i : Fin n, ∀ t : ℝ, 0 ≤ t → z + t • coordinate n i ∈ q)
    (hs : UniqueDiffOn ℝ (ball a R ∩ q))
    (hu : IsC2HolderUpToOn α u (ball a R ∩ q))
    (hf : FiniteWeightedNorms α a R u (ball a R ∩ q)) :
    M1 a R u (ball a R ∩ q) + M2 a R u (ball a R ∩ q) +
      N0 α a R u (ball a R ∩ q) + N1 α a R u (ball a R ∩ q) ≤
      lowerOrderFactor n * (M0 u (ball a R ∩ q) + M2 a R u (ball a R ∩ q)) := by
  let s := ball a R ∩ q
  have hpair := weighted_lower_pair_estimates hα hα1 ((convex_ball a R).inter hc)
    hs inter_subset_left hu hf
  have hfirst := weighted_first_estimate hq hs hu hf
  have hM0 : 0 ≤ M0 u s := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hM2 := M2_nonneg (s := s) inter_subset_left u
  let A := 16 * (n : ℝ) * (1 + 3 * (n : ℝ)) + 2
  let B := (1 + 3 * (n : ℝ)) * (n : ℝ) + 1 + (n : ℝ) ^ 2
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  calc
    _ ≤ (1 + 3 * (n : ℝ)) * M1 a R u s +
        (1 + (n : ℝ) ^ 2) * M2 a R u s + 2 * M0 u s := by
      dsimp [s] at *
      linarith [hpair.1, hpair.2]
    _ ≤ (1 + 3 * (n : ℝ)) * (16 * (n : ℝ) * M0 u s + (n : ℝ) * M2 a R u s) +
        (1 + (n : ℝ) ^ 2) * M2 a R u s + 2 * M0 u s := by
      have h := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 1 + 3 * (n : ℝ) by positivity)
      linarith
    _ = A * M0 u s + B * M2 a R u s := by dsimp [A, B]; ring
    _ ≤ lowerOrderFactor n * (M0 u s + M2 a R u s) := by
      change A * M0 u s + B * M2 a R u s ≤ (A + B + 1) * (M0 u s + M2 a R u s)
      nlinarith [mul_nonneg hA hM2, mul_nonneg hB hM0]

lemma hessian_interpolation_step {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 4 * (2 : ℝ) ^ α * η ^ α ≤ ε := by
  let b := ε / (4 * (2 : ℝ) ^ α)
  have hb : 0 < b := by positivity
  let t := b ^ (1 / α)
  have ht : 0 < t := Real.rpow_pos_of_pos hb _
  have hpow : t ^ α = b := by
    dsimp [t]
    rw [← Real.rpow_mul hb.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  refine ⟨min (1 / 4) t, lt_min (by norm_num) ht, min_le_left _ _, ?_⟩
  have hsmall : min (1 / 4) t ^ α ≤ b := by
    rw [← hpow]
    exact Real.rpow_le_rpow (le_min (by norm_num) ht.le) (min_le_right _ _) hα.le
  calc
    4 * (2 : ℝ) ^ α * min (1 / 4) t ^ α ≤ 4 * (2 : ℝ) ^ α * b :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = ε := by dsimp [b]; field_simp

/-- Uniform interpolation for every forward-coordinate invariant convex cut
of a ball. The constant is fixed before the center, radius, cut and function. -/
lemma interpolation_on_forward_convex_cut (n : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Space n) (R : ℝ) (q : Set (Space n)), 0 < R →
      Convex ℝ q →
      (∀ z ∈ q, ∀ i : Fin n, ∀ t : ℝ, 0 ≤ t → z + t • coordinate n i ∈ q) →
      UniqueDiffOn ℝ (ball a R ∩ q) → ∀ u : Space n → ℝ,
      IsC2HolderUpToOn α u (ball a R ∩ q) →
      FiniteWeightedNorms α a R u (ball a R ∩ q) ∧
        InterpolationBound α ε C a R u (ball a R ∩ q) := by
  let A := lowerOrderFactor n
  have hA : 0 < A := lowerOrderFactor_pos n
  obtain ⟨η, hη, hη1, hsmall⟩ := hessian_interpolation_step hα (div_pos hε hA)
  let C := A * (1 + 16 * (n : ℝ) ^ 2 / η ^ 2)
  have hC : 0 < C := mul_pos hA (by positivity)
  refine ⟨C, hC, ?_⟩
  intro a R q hR hc hq hs u hu
  have hf := finite_weighted_norms hα.le hα1.le hR ((convex_ball a R).inter hc)
    hs inter_subset_left hu
  refine ⟨hf, ?_⟩
  have hlower := weighted_lower_order_estimate hα.le hα1.le hc hq hs hu hf
  have hessian := weighted_hessian_estimate hα.le hR hη hη1 hq hs hu hf
  have hN := N2_nonneg (a := a) (R := R) (α := α) (s := ball a R ∩ q) inter_subset_left u
  have hsmall' : A * (4 * (2 : ℝ) ^ α * η ^ α) ≤ ε := by
    have h := (le_div_iff₀ hA).mp hsmall
    simpa only [mul_comm] using h
  change M1 a R u (ball a R ∩ q) + M2 a R u (ball a R ∩ q) +
    N0 α a R u (ball a R ∩ q) + N1 α a R u (ball a R ∩ q) ≤
      ε * N2 α a R u (ball a R ∩ q) + C * M0 u (ball a R ∩ q)
  calc
    _ ≤ A * (M0 u (ball a R ∩ q) + M2 a R u (ball a R ∩ q)) := hlower
    _ ≤ A * (M0 u (ball a R ∩ q) +
        ((16 * (n : ℝ) ^ 2 / η ^ 2) * M0 u (ball a R ∩ q) +
          (4 * (2 : ℝ) ^ α * η ^ α) * N2 α a R u (ball a R ∩ q))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hessian) hA.le
    _ ≤ ε * N2 α a R u (ball a R ∩ q) + C * M0 u (ball a R ∩ q) := by
      have h := mul_le_mul_of_nonneg_right hsmall' hN
      dsimp [C]
      nlinarith

theorem ball_interpolation : BallInterpolationStatement := by
  intro n hn α hα hα1 ε hε
  obtain ⟨C, hC, hbound⟩ := interpolation_on_forward_convex_cut n α hα hα1 ε hε
  refine ⟨C, hC, ?_⟩
  intro a R hR u hu
  simpa only [inter_univ] using hbound a R univ hR convex_univ
    (fun _ _ _ _ _ => mem_univ _)
    (by simpa only [inter_univ] using (isOpen_ball (x := a) (ε := R)).uniqueDiffOn)
    u (by simpa only [inter_univ] using hu)

theorem halfBall_interpolation : HalfBallInterpolationStatement := by
  intro m α hα hα1 ε hε
  obtain ⟨C, hC, hbound⟩ := interpolation_on_forward_convex_cut (m + 1) α hα hα1 ε hε
  refine ⟨C, hC, ?_⟩
  intro R hR u hu
  apply hbound 0 R (P201Specs.Elliptic.HalfSpaceLift.closedHalfSpace m) hR
    (P201.Elliptic.HalfSpaceLift.convex_closedHalfSpace m) _
    (uniqueDiffOn_halfBallWithFace m R) u hu
  intro z hz i t ht
  have hcoord : 0 ≤ P201Specs.Elliptic.HalfSpaceLift.height (coordinate (m + 1) i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [P201.Elliptic.HalfSpaceLift.height_coordinate_last,
        P201.Elliptic.HalfSpaceLift.height_coordinate_castSucc] <;> norm_num
  change 0 ≤ P201Specs.Elliptic.HalfSpaceLift.height (z + t • coordinate (m + 1) i)
  change 0 ≤ z (Fin.last m) + t * coordinate (m + 1) i (Fin.last m)
  exact add_nonneg hz (mul_nonneg ht hcoord)

end P201.Elliptic.WeightedInterpolation
