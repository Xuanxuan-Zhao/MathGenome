import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.CentralRichardson
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.IntervalTaylor
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
namespace NumAnalysis206.Quadrature
open Set Filter Asymptotics Topology
open NumAnalysis206.Approximation

abbrev centralDifference := Specs.NumAnalysis206.Quadrature.CentralRichardson.centralDifferenceValue
abbrev extrapolatedCentral := Specs.NumAnalysis206.Quadrature.CentralRichardson.extrapolatedCentralValue
abbrev fifthDerivativeSup := Specs.NumAnalysis206.Quadrature.CentralRichardson.fifthDerivativeSupValue

/-- The two order-five Taylor errors give the order-four central error. -/
private theorem central_error_of_jet {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ} {x H h M : ℝ}
    (hH : 0 < H) (hD : IntervalJet (x - H) (x + H) 5 f D)
    (hh : 0 < h) (hhH : h ≤ H)
    (hM : ∀ t ∈ Icc (x - H) (x + H), |D 5 t| ≤ M) :
    |centralDifference f x h - (D 1 x + D 3 x * h ^ 2 / 6)| ≤ M * h ^ 4 / 120 := by
  have hab : x - H ≤ x + H := by linarith
  have hx : x ∈ Icc (x - H) (x + H) := ⟨by linarith, by linarith⟩
  have hplus : x + h ∈ Icc (x - H) (x + H) := ⟨by linarith, by linarith⟩
  have hminus : x - h ∈ Icc (x - H) (x + H) := ⟨by linarith, by linarith⟩
  have hullplus : uIcc x (x + h) ⊆ Icc (x - H) (x + H) := by
    rw [uIcc_of_le (by linarith : x ≤ x + h)]
    exact Icc_subset_Icc hx.1 hplus.2
  have hullminus : uIcc x (x - h) ⊆ Icc (x - H) (x + H) := by
    rw [uIcc_of_ge (by linarith : x - h ≤ x)]
    exact Icc_subset_Icc hminus.1 hx.2
  have hp := jet_taylor_bound hab (by norm_num : 1 ≤ 5) hD hx hplus
    (fun t ht => hM t (hullplus ht))
  have hm := jet_taylor_bound hab (by norm_num : 1 ≤ 5) hD hx hminus
    (fun t ht => hM t (hullminus ht))
  norm_num [Nat.factorial] at hp hm
  have hp' : |f (x + h) - jetTaylorSum D 5 x (x + h)| ≤ M * h ^ 5 / 120 := by
    simpa [show x + h - x = h by ring, abs_of_pos hh] using hp
  have hm' : |f (x - h) - jetTaylorSum D 5 x (x - h)| ≤ M * h ^ 5 / 120 := by
    simpa [show x - h - x = -h by ring, abs_neg, abs_of_pos hh] using hm
  have hcancel :
      jetTaylorSum D 5 x (x + h) - jetTaylorSum D 5 x (x - h) =
        2 * h * (D 1 x + D 3 x * h ^ 2 / 6) := by
    norm_num [jetTaylorSum, IntervalTaylorSpec.sumValue, Finset.sum_range_succ,
      Nat.factorial]
    ring
  have hid : centralDifference f x h - (D 1 x + D 3 x * h ^ 2 / 6) =
      ((f (x + h) - jetTaylorSum D 5 x (x + h)) -
       (f (x - h) - jetTaylorSum D 5 x (x - h))) / (2 * h) := by
    unfold centralDifference Specs.NumAnalysis206.Quadrature.CentralRichardson.centralDifferenceValue
    apply (eq_div_iff (by positivity : (2 : ℝ) * h ≠ 0)).mpr
    have heq : (f (x + h) - f (x - h)) / (2 * h) * (2 * h) =
        f (x + h) - f (x - h) := div_mul_cancel₀ _ (by positivity)
    nlinarith [hcancel]
  rw [hid, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * h)]
  calc
    _ ≤ (M * h ^ 5 / 120 + M * h ^ 5 / 120) / (2 * h) :=
      div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hp' hm')) (by positivity)
    _ = M * h ^ 4 / 120 := by field_simp; ring

/-- Canonical derivative data on the nondegenerate allowed neighborhood. -/
private theorem central_jet {f : ℝ → ℝ} {x H : ℝ} (hH : 0 < H)
    (hf : IntervalContDiff (x - H) (x + H) 5 f) :
    IntervalJet (x - H) (x + H) 5 f
      (fun j => iteratedDerivWithin j f (Icc (x - H) (x + H))) := by
  have hab : x - H < x + H := by linarith
  exact jet_of_contDiff hab ((smooth_iff_contDiff hab.le).mp hf)

/-- At the center, the interval derivatives are the ordinary derivatives.
The neighborhood hypothesis here follows from `H > 0`, not from any extension. -/
private theorem central_iterated_eq {f : ℝ → ℝ} {x H : ℝ}
    (hH : 0 < H) (hf : IntervalContDiff (x - H) (x + H) 5 f)
    (j : ℕ) (hj : j ≤ 5) :
    iteratedDerivWithin j f (Icc (x - H) (x + H)) x = iteratedDeriv j f x := by
  have hab : x - H < x + H := by linarith
  have hcf := (smooth_iff_contDiff hab.le).mp hf
  have hx : Icc (x - H) (x + H) ∈ 𝓝 x := Icc_mem_nhds (by linarith) (by linarith)
  exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
    ((hcf.of_le (by exact_mod_cast hj)).contDiffAt hx) (mem_of_mem_nhds hx)

/-- Continuity on the compact interval makes the stated supremum a true bound. -/
private theorem fifth_derivative_le_sup {f : ℝ → ℝ} {x H t : ℝ}
    (hH : 0 < H) (hf : IntervalContDiff (x - H) (x + H) 5 f)
    (ht : t ∈ Icc (x - H) (x + H)) :
    |iteratedDerivWithin 5 f (Icc (x - H) (x + H)) t| ≤
      fifthDerivativeSup f x H := by
  have hD := central_jet hH hf
  have hb := isCompact_Icc.bddAbove_image (hD.2.1 5 le_rfl).abs
  exact le_csSup hb (mem_image_of_mem _ ht)

/-- Taylor through degree four, with a single remainder function valid for
all positive steps up to `H`, including the largest allowed step. -/
theorem central_expansion : Specs.NumAnalysis206.Quadrature.CentralRichardson.expansion := by
  intro f x H hH hf
  have h1 : iteratedDerivWithin 1 f (Icc (x - H) (x + H)) x = deriv f x := by
    simpa only [iteratedDeriv_one] using central_iterated_eq hH hf 1 (by norm_num)
  have h3 := central_iterated_eq hH hf 3 (by norm_num)
  refine ⟨fun h => centralDifference f x h - (deriv f x + iteratedDeriv 3 f x * h ^ 2 / 6), ?_⟩
  intro h hh hhH
  constructor
  · ring
  · simpa only [h1, h3] using
      central_error_of_jet hH (central_jet hH hf) hh hhH
        (fun t ht => fifth_derivative_le_sup hH hf ht)

/-- Richardson cancels the quadratic term. Its two remainder weights give
`(4 / 16 + 1) / (3 * 120) = 1 / 288`. -/
theorem central_richardson_bound : Specs.NumAnalysis206.Quadrature.CentralRichardson.bound := by
  intro f x H h hH hf hh hhH
  obtain ⟨r, hr⟩ := central_expansion hH hf
  obtain ⟨heq, hrem⟩ := hr h hh hhH
  obtain ⟨heqhalf, hremhalf⟩ := hr (h / 2) (by positivity) (by linarith)
  have hid : extrapolatedCentral f x h -
      deriv f x =
      (4 * r (h / 2) - r h) / 3 := by
    unfold extrapolatedCentral
      Specs.NumAnalysis206.Quadrature.CentralRichardson.extrapolatedCentralValue
    rw [heqhalf, heq]
    ring
  rw [hid, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  calc
    |4 * r (h / 2) - r h| / 3 ≤ (4 * |r (h / 2)| + |r h|) / 3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      simpa [abs_mul] using abs_sub (4 * r (h / 2)) (r h)
    _ ≤ (4 * (fifthDerivativeSup f x H * (h / 2) ^ 4 / 120) +
        fifthDerivativeSup f x H * h ^ 4 / 120) / 3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith
    _ = fifthDerivativeSup f x H * h ^ 4 / 288 := by ring

/-- Fourth-order truncation on the positive one-sided limit filter. -/
theorem central_richardson_order : Specs.NumAnalysis206.Quadrature.CentralRichardson.fourthOrder := by
  intro f x H hH hf
  apply IsBigO.of_bound (fifthDerivativeSup f x H / 288)
  have hsmall : ∀ᶠ h : ℝ in 𝓝[Ioi 0] 0, h < H :=
    nhdsWithin_le_nhds (Iio_mem_nhds hH)
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhH
  have hb := central_richardson_bound hH hf hh hhH.le
  simpa only [Real.norm_eq_abs, abs_pow, abs_of_pos (show 0 < h from hh),
    div_mul_eq_mul_div] using hb

end NumAnalysis206.Quadrature
