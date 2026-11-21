import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.BanachMoreau
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.MoreauDualMaximizer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06FenchelMoreau
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-! Differentiability and monotone approximation for the Banach Moreau
 envelopes, `fa2:p2:banach-moreau`. The dual-stage results supply the
 continuous unique maximizers. Supporting affine inequalities squeeze the
 derivative remainder. Fenchel–Moreau gives the limit, including +∞. -/
namespace ExpandedFA.BanachConvex.Moreau
open Set Filter P1.ExtendedConvexFunctions
open scoped Topology
local notation "val" => P1.C06Conjugates.Spec.ExtendedRealValueValue
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Comparing an optimizer at x with the dual value at y gives a global
supporting affine function of the real envelope. -/
lemma envelope_support (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) (x y : X) (f : X →L[ℝ] ℝ)
    (hf : objective φ n x f = primal φ n x) :
    envelope φ n x + f (y - x) ≤ envelope φ n y := by
  rw [primal_finite φ hp hc hl n hn] at hf
  obtain ⟨r, hr, heq⟩ := conjugate_real_of_objective_eq φ hp n x f _ hf
  have hy := (primal_eq_max φ hp hc hl n hn y).1 f
  rw [primal_finite φ hp hc hl n hn] at hy
  simp only [objective, hr, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hy
  rw [map_sub]
  linarith

lemma envelope_remainder (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) (S : X → (X →L[ℝ] ℝ))
    (hS : ∀ x, objective φ n x (S x) = primal φ n x) (x y : X) :
    0 ≤ envelope φ n y - envelope φ n x - S x (y - x) ∧
    envelope φ n y - envelope φ n x - S x (y - x) ≤
      ‖S y - S x‖ * ‖y - x‖ := by
  have hlower := envelope_support φ hp hc hl n hn x y (S x) (hS x)
  have hupper := envelope_support φ hp hc hl n hn y x (S y) (hS y)
  have hb := (S y - S x).le_opNorm (y - x)
  rw [Real.norm_eq_abs] at hb
  have hneg : S y (x - y) = -S y (y - x) := by rw [← map_neg, neg_sub]
  rw [hneg] at hupper
  simp only [sub_apply] at hb
  exact ⟨by linarith, by linarith [(abs_le.mp hb).2]⟩

lemma envelope_hasFDerivAt (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) (S : X → (X →L[ℝ] ℝ))
    (hS : ∀ x, objective φ n x (S x) = primal φ n x)
    (hcont : Continuous S) (x : X) : HasFDerivAt (envelope φ n) (S x) x := by
  rw [hasFDerivAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have he : ∀ᶠ y in 𝓝 x, ‖S y - S x‖ < ε := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      (hcont.continuousAt (x := x)).eventually (Metric.ball_mem_nhds (S x) hε)
  filter_upwards [he] with y hy
  obtain ⟨hlower, hupper⟩ := envelope_remainder φ hp hc hl n hn S hS x y
  rw [Real.norm_eq_abs, abs_of_nonneg hlower]
  exact hupper.trans (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _))

theorem banach_moreau_regularity : BanachSpec.Regularity := by
  intro X _ _ _ _ φ hp hc hl n hn
  obtain ⟨hfinite, hconvex⟩ := finite_convex X φ hp hc hl n hn
  obtain ⟨S, hS, hcont, _⟩ := maximizer_regularity X φ hp hc hl n hn
  have hderiv := envelope_hasFDerivAt φ hp hc hl n hn S
    (fun x => (hS x (S x)).mpr rfl) hcont
  refine ⟨hfinite, hconvex, contDiff_one_iff_hasFDerivAt.mpr ⟨S, hcont, hderiv⟩,
    S, hcont, hderiv, fun x => (hderiv x).fderiv, ?_, hS⟩
  intro x
  exact (exact_dual X φ hp hc hl n hn x).1

omit [NormedSpace ℝ X] in
/-- The primal infimum increases with the quadratic coefficient. -/
lemma primal_monotone (φ : ExtendedFunction X) (x : X) :
    Monotone (fun n : ℕ => primal φ n x) := by
  intro m n hmn
  apply iInf_mono
  intro y
  apply add_le_add le_rfl
  apply EReal.coe_le_coe_iff.mpr
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  nlinarith [sq_nonneg ‖x - y‖]

omit [NormedSpace ℝ X] in
lemma primal_le_value (φ : ExtendedFunction X) (n : ℕ) (x : X) :
    primal φ n x ≤ val (φ x) := by
  have h := iInf_le (fun y => val (φ y) + ((n * ‖x - y‖ ^ 2 / 2 : ℝ) : EReal)) x
  simpa only [primal, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_div, EReal.coe_zero, add_zero] using h

/-- Each finite conjugate produces a dual lower bound whose quadratic
penalty tends to zero. This statement uses no compactness or primal optimizer. -/
lemma affine_le_iSup_primal (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (x : X) (f : X →L[ℝ] ℝ) (r : ℝ)
    (hr : P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = (r : EReal)) :
    ((f x - r : ℝ) : EReal) ≤ ⨆ k : ℕ, primal φ (k + 1) x := by
  have hpen : Tendsto (fun k : ℕ => ‖f‖ ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (‖f‖^2/2)
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev,
      one_mul, mul_zero, zero_mul, mul_assoc, mul_left_comm, mul_comm] using h
  have hlim : Tendsto (fun k : ℕ => ((f x - r - ‖f‖^2 / (2 * ((k+1 : ℕ) : ℝ)) : ℝ) : EReal))
      atTop (𝓝 ((f x - r : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa only [sub_zero] using tendsto_const_nhds.sub hpen
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro k
  have h := (primal_eq_max φ hp hc hl (k + 1) (by omega) x).1 f
  simp only [objective, hr, ← EReal.coe_sub] at h
  exact h.trans (le_iSup (fun k : ℕ => primal φ (k + 1) x) k)

lemma iSup_primal_eq_value (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (x : X) : (⨆ k : ℕ, primal φ (k + 1) x) = val (φ x) := by
  apply le_antisymm (iSup_le (fun _ => primal_le_value φ _ x))
  rw [← P1.C06FenchelMoreau.fenchel_moreau X φ hp hc hl x]
  apply iSup_le
  intro f
  by_cases ht : P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = ⊤
  · change (f x : EReal) - P1.C06Conjugates.Spec.ConvexConjugateValue X φ f ≤ _
    rw [ht, EReal.sub_top]
    exact bot_le
  · have hb := P1.C06Conjugates.convexConjugate_ne_bot X φ hp f
    have hr := (EReal.coe_toReal ht hb).symm
    change (f x : EReal) - P1.C06Conjugates.Spec.ConvexConjugateValue X φ f ≤ _
    rw [hr, ← EReal.coe_sub]
    exact affine_le_iSup_primal φ hp hc hl x f _ hr

theorem banach_moreau_approximation : BanachSpec.Approximation := by
  intro X _ _ _ _ φ hp hc hl x
  have hmono : Monotone (fun k : ℕ => primal φ (k + 1) x) :=
    (primal_monotone φ x).comp (fun _ _ h => Nat.add_le_add_right h 1)
  have hsup := iSup_primal_eq_value φ hp hc hl x
  refine ⟨hmono, fun k => primal_le_value φ (k + 1) x, hsup, ?_⟩
  rw [← hsup]
  exact tendsto_atTop_iSup hmono

end ExpandedFA.BanachConvex.Moreau
