import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.JacksonInverse
import MathGenome.Internal.FourierSobolev.P102.Approximation.BernsteinDerivative
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

import MathGenome.Internal.FourierSobolev.P102.Approximation.JacksonPeriodic
noncomputable section
open Set Filter
open scoped Topology

namespace P102.Approximation.JacksonInverse

section BestError

variable {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜]
  (V : ℕ → Submodule 𝕜 C(X, 𝕜)) (f : C(X, 𝕜))

/-- The infimum formulation does not require existence of a best approximant. -/
def bestError (n : ℕ) : ℝ := sInf {r : ℝ | ∃ p ∈ V n, r = ‖f - p‖}

theorem errorSet_nonempty (n : ℕ) :
    {r : ℝ | ∃ p ∈ V n, r = ‖f - p‖}.Nonempty :=
  ⟨‖f‖, 0, (V n).zero_mem, by simp⟩

theorem errorSet_bddBelow (n : ℕ) :
    BddBelow {r : ℝ | ∃ p ∈ V n, r = ‖f - p‖} := by
  refine ⟨0, ?_⟩
  rintro r ⟨p, hp, rfl⟩
  exact norm_nonneg _

theorem bestError_nonneg (n : ℕ) : 0 ≤ bestError V f n := by
  apply le_csInf (errorSet_nonempty V f n)
  rintro r ⟨p, hp, rfl⟩
  exact norm_nonneg _

theorem bestError_le_norm (n : ℕ) : bestError V f n ≤ ‖f‖ :=
  csInf_le (errorSet_bddBelow V f n) ⟨0, (V n).zero_mem, by simp⟩

theorem exists_near_best (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ V n, ‖f - p‖ < bestError V f n + ε := by
  obtain ⟨r, ⟨p, hp, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
    (errorSet_nonempty V f n) (lt_add_of_pos_right (bestError V f n) hε)
  exact ⟨p, hp, hr⟩

/-- Enlarge an eventual constant to include every positive degree.  The zero
polynomial bounds all finitely many low-degree errors, including constants. -/
theorem bestError_uniform_rate {α : ℝ} (hα : 0 < α)
    (h : Asymptotics.IsBigO atTop (bestError V f)
      (fun n : ℕ => (n : ℝ) ^ (-α))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 1 ≤ n →
      bestError V f n ≤ A * (n : ℝ) ^ (-α) := by
  obtain ⟨c, hc, hbound⟩ := h.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound.bound
  let M : ℝ := (N + 1 : ℕ)
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨c + ‖f‖ * M ^ α, by positivity, ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrpos : 0 ≤ (n : ℝ) ^ (-α) := Real.rpow_nonneg hnpos.le _
  by_cases hnN : N ≤ n
  · have hb := hN n hnN
    rw [Real.norm_of_nonneg (bestError_nonneg V f n),
      Real.norm_of_nonneg hrpos] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hrpos)
  · have hnm : (n : ℝ) ≤ M := by dsimp [M]; exact_mod_cast (by omega : n ≤ N + 1)
    have hprod : 1 ≤ M ^ α * (n : ℝ) ^ (-α) := by
      rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv]
      exact (one_le_div (Real.rpow_pos_of_pos hnpos _)).2
        (Real.rpow_le_rpow hnpos.le hnm hα.le)
    calc
      bestError V f n ≤ ‖f‖ := bestError_le_norm V f n
      _ ≤ ‖f‖ * (M ^ α * (n : ℝ) ^ (-α)) :=
        le_mul_of_one_le_right (norm_nonneg _) hprod
      _ ≤ (c + ‖f‖ * M ^ α) * (n : ℝ) ^ (-α) := by
        nlinarith [mul_nonneg hc.le hrpos]


end BestError

section Geometric

variable {X E : Type*} [MetricSpace X] [CompactSpace X]
  [NormedAddCommGroup E]

/-- A finite-frequency splitting estimate.  No convergence of derivative
series is required: one approximant handles the tail at the chosen scale. -/
theorem holder_of_dyadic_approximants
    (α : ℝ) (hα : 0 < α) (f : C(X, E)) (p : ℕ → C(X, E))
    (A : ℝ) (hA : 0 ≤ A)
    (hp : ∀ j, ‖f - p j‖ ≤ A * ((1 / 2 : ℝ) ^ α) ^ j)
    (D : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ j x y, ‖p j x - p j y‖ ≤
      D * (2 * (1 / 2 : ℝ) ^ α) ^ j * dist x y) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α := by
  let K : ℝ := (2 * A + D) * (2 : ℝ) ^ α
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 2 * ‖f‖, by positivity, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, dist_self]
    positivity
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  by_cases hsmall : dist x y ≤ 1
  · obtain ⟨j, hjlow, hjhigh⟩ := exists_nat_pow_near_of_lt_one hdist hsmall
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have hpow : 0 ≤ ((1 / 2 : ℝ) ^ α) ^ j := by positivity
    have hscale : (2 * (1 / 2 : ℝ) ^ α) ^ j * dist x y ≤
        ((1 / 2 : ℝ) ^ α) ^ j := by
      rw [mul_pow]
      have htwo : (2 : ℝ) ^ j * dist x y ≤ 1 := by
        have ht := mul_le_mul_of_nonneg_left hjhigh (by positivity : 0 ≤ (2 : ℝ) ^ j)
        have hcancel : (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by
          rw [← mul_pow]; norm_num
        rwa [hcancel] at ht
      nlinarith [mul_le_mul_of_nonneg_right htwo hpow]
    have hpower : ((1 / 2 : ℝ) ^ α) ^ j ≤ (2 : ℝ) ^ α * dist x y ^ α := by
      rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hdist.le]
      apply Real.rpow_le_rpow (by positivity) _ hα.le
      rw [pow_succ] at hjlow
      linarith
    have herror (z : X) : ‖f z - p j z‖ ≤ A * ((1 / 2 : ℝ) ^ α) ^ j :=
      ((f - p j).norm_coe_le_norm z).trans (hp j)
    have hincr : ‖f x - f y‖ ≤ (2 * A + D) * ((1 / 2 : ℝ) ^ α) ^ j := by
      calc
        ‖f x - f y‖ ≤ ‖f x - p j x‖ + ‖p j x - p j y‖ + ‖p j y - f y‖ :=
          by
            have h₁ := dist_triangle (f x) (p j y) (f y)
            have h₂ := dist_triangle (f x) (p j x) (p j y)
            simp only [dist_eq_norm] at h₁ h₂
            linarith
        _ ≤ A * ((1 / 2 : ℝ) ^ α) ^ j +
            D * (2 * (1 / 2 : ℝ) ^ α) ^ j * dist x y +
            A * ((1 / 2 : ℝ) ^ α) ^ j := by
          gcongr
          · exact herror x
          · exact hLip j x y
          · simpa only [norm_sub_rev] using herror y
        _ ≤ (2 * A + D) * ((1 / 2 : ℝ) ^ α) ^ j := by
          nlinarith [mul_le_mul_of_nonneg_left hscale hD]
    calc
      ‖f x - f y‖ ≤ (2 * A + D) * ((1 / 2 : ℝ) ^ α) ^ j := hincr
      _ ≤ K * dist x y ^ α := by
        dsimp [K]
        nlinarith [mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 2 * A + D)]
      _ ≤ (K + 2 * ‖f‖) * dist x y ^ α := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
          (Real.rpow_nonneg (dist_nonneg) _)
  · have hlarge : 1 ≤ dist x y ^ α :=
      Real.one_le_rpow (by linarith) hα.le
    calc
      ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * ‖f‖ := by linarith [f.norm_coe_le_norm x, f.norm_coe_le_norm y]
      _ ≤ (K + 2 * ‖f‖) * dist x y ^ α := by
        nlinarith [mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ K + 2 * ‖f‖)]

end Geometric

section Scheme

variable {X 𝕜 : Type*} [MetricSpace X] [CompactSpace X] [RCLike 𝕜]

/-- The dyadic inverse argument for nested approximation spaces with a
Bernstein increment bound.  The initial polynomial contributes its full norm;
in particular no assumption on its constant term is made. -/
theorem holder_of_bernstein_scheme
    (V : ℕ → Submodule 𝕜 C(X, 𝕜)) (hV : Monotone V)
    (B : ℝ) (hB : 0 ≤ B)
    (hbern : ∀ n p, p ∈ V n → ∀ x y,
      ‖p x - p y‖ ≤ B * n * ‖p‖ * dist x y)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (f : C(X, 𝕜))
    (hrate : Asymptotics.IsBigO atTop (bestError V f)
      (fun n : ℕ => (n : ℝ) ^ (-α))) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α := by
  obtain ⟨A₀, hA₀, hrate⟩ := bestError_uniform_rate V f hα hrate
  let r : ℝ := (1 / 2 : ℝ) ^ α
  have hr : 0 < r := by dsimp [r]; positivity
  have hdyadic (j : ℕ) : ((2 ^ j : ℕ) : ℝ) ^ (-α) = r ^ j := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    dsimp [r]
    rw [Real.rpow_neg_eq_inv_rpow]
    norm_num
  have hnear (j : ℕ) : ∃ p ∈ V (2 ^ j), ‖f - p‖ ≤ (A₀ + 1) * r ^ j := by
    obtain ⟨p, hp, he⟩ := exists_near_best V f (2 ^ j) (pow_pos hr j)
    refine ⟨p, hp, he.le.trans ?_⟩
    have hb := hrate (2 ^ j) (Nat.one_le_pow j 2 (by decide))
    rw [hdyadic] at hb
    nlinarith
  choose p hp herr using hnear
  let A := A₀ + 1
  have hA : 0 ≤ A := by dsimp [A]; linarith
  let q := 2 * r
  have hq : 1 < q := by
    have h := Real.rpow_lt_rpow_of_exponent_gt
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hα1
    rw [Real.rpow_one] at h
    dsimp [q, r]
    linarith
  let C := 2 * B * A * (1 + r)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let D := B * ‖p 0‖ + C / (q - 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDbase : B * ‖p 0‖ ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (div_nonneg hC (by linarith))
  have hDC : C ≤ D * (q - 1) := by
    dsimp [D]
    rw [add_mul, div_mul_cancel₀ _ (by linarith : q - 1 ≠ 0)]
    nlinarith [mul_nonneg (mul_nonneg hB (norm_nonneg (p 0))) (by linarith : 0 ≤ q - 1)]
  have hLip (j : ℕ) : ∀ x y,
      ‖p j x - p j y‖ ≤ D * q ^ j * dist x y := by
    induction j with
    | zero =>
      intro x y
      have hb := hbern 1 (p 0) (by simpa using hp 0) x y
      simp only [Nat.cast_one, mul_one, pow_zero] at hb ⊢
      exact hb.trans (mul_le_mul_of_nonneg_right hDbase dist_nonneg)
    | succ j ih =>
      intro x y
      have hdeg : p (j + 1) - p j ∈ V (2 ^ (j + 1)) :=
        (V _).sub_mem (hp (j + 1))
          (hV (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ j)) (hp j))
      have hdiff : ‖p (j + 1) - p j‖ ≤ A * (1 + r) * r ^ j := by
        calc
          ‖p (j + 1) - p j‖ = ‖(f - p j) - (f - p (j + 1))‖ := by congr 1; abel
          _ ≤ ‖f - p j‖ + ‖f - p (j + 1)‖ := norm_sub_le _ _
          _ ≤ A * r ^ j + A * r ^ (j + 1) := add_le_add (herr j) (herr (j + 1))
          _ = A * (1 + r) * r ^ j := by rw [pow_succ]; ring
      have hb := hbern (2 ^ (j + 1)) (p (j + 1) - p j) hdeg x y
      have hb' : ‖(p (j + 1) - p j) x - (p (j + 1) - p j) y‖ ≤
          C * q ^ j * dist x y := by
        calc
          _ ≤ B * (2 ^ (j + 1) : ℕ) * ‖p (j + 1) - p j‖ * dist x y := hb
          _ ≤ B * (2 ^ (j + 1) : ℕ) * (A * (1 + r) * r ^ j) * dist x y := by
            gcongr
          _ = C * q ^ j * dist x y := by
            simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, pow_succ, C, q, mul_pow]
            ring
      calc
        ‖p (j + 1) x - p (j + 1) y‖ =
            ‖(p j x - p j y) + ((p (j + 1) - p j) x - (p (j + 1) - p j) y)‖ := by
          congr 1
          simp only [ContinuousMap.sub_apply]
          abel
        _ ≤ ‖p j x - p j y‖ + ‖(p (j + 1) - p j) x - (p (j + 1) - p j) y‖ :=
          norm_add_le _ _
        _ ≤ D * q ^ j * dist x y + C * q ^ j * dist x y := add_le_add (ih x y) hb'
        _ ≤ D * q ^ (j + 1) * dist x y := by
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hDC (pow_nonneg (by linarith : 0 ≤ q) j))
            (dist_nonneg : 0 ≤ dist x y)
          rw [pow_succ]
          nlinarith
  exact holder_of_dyadic_approximants α hα f p A hA herr D hD hLip

end Scheme


section Circle

open P102.Periodic.Expected
variable (T : ℝ) [Fact (0 < T)]

/-- A derivative estimate on the periodic lift descends to the quotient arc
metric, by taking representatives arbitrarily close to the quotient norm. -/
theorem circle_increment_of_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p q : C(Circle T, E))
    (hq : ∀ t : ℝ, HasDerivAt (fun s : ℝ => p (s : Circle T)) (q (t : Circle T)) t)
    (L : ℝ) (hL : 0 ≤ L) (hbound : ‖q‖ ≤ L) (x y : Circle T) :
    ‖p x - p y‖ ≤ L * dist x y := by
  have hlift (s t : ℝ) :
      ‖p (s : Circle T) - p (t : Circle T)‖ ≤ L * ‖s - t‖ := by
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hq u).hasDerivWithinAt)
      (fun u _ => (q.norm_coe_le_norm _).trans hbound)
      convex_univ (mem_univ t) (mem_univ s)
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨s, hs, hsnorm⟩ := QuotientAddGroup.exists_norm_mk_lt
    (x - (t : Circle T)) (div_pos hε (show 0 < L + 1 by linarith))
  have hst : ((s + t : ℝ) : Circle T) = x := by
    rw [QuotientAddGroup.mk_add, hs]
    abel
  have h := hlift (s + t) t
  rw [hst, add_sub_cancel_right] at h
  have hsnorm' : ‖s‖ < dist x (t : Circle T) + ε / (L + 1) := by
    simpa only [dist_eq_norm] using hsnorm
  have hsmall : L * (ε / (L + 1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < L + 1 by linarith)).2
    nlinarith
  calc
    ‖p x - p (t : Circle T)‖ ≤ L * ‖s‖ := by simpa only [dist_eq_norm] using h
    _ ≤ L * (dist x (t : Circle T) + ε / (L + 1)) :=
      mul_le_mul_of_nonneg_left hsnorm'.le hL
    _ ≤ L * dist x (t : Circle T) + ε := by nlinarith

omit [Fact (0 < T)] in
/-- Inclusion of the genuine finite Fourier spaces when the degree increases. -/
theorem complexTrigDegree_mono : Monotone (complexTrigDegree T) := by
  intro m n hmn
  apply Submodule.map_mono
  apply Finsupp.supported_mono
  intro k hk
  rcases hk with ⟨hlo, hhi⟩
  constructor <;> omega

theorem realTrigDegree_mono : Monotone (realTrigDegree T) := by
  intro m n hmn
  apply Submodule.map_mono
  intro c hc
  refine ⟨?_, hc.2⟩
  exact Finsupp.supported_mono (by
    intro k hk
    rcases hk with ⟨hlo, hhi⟩
    constructor <;> omega) hc.1

theorem inverse_real (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (f : C(Circle T, ℝ))
    (hrate : Asymptotics.IsBigO atTop
      (fun n : ℕ => P102.Approximation.JacksonPeriodic.Expected.realBestErrorValue T f n)
      (fun n : ℕ => (n : ℝ) ^ (-α))) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α := by
  have hTpos : 0 < T := Fact.out
  apply holder_of_bernstein_scheme (realTrigDegree T) (realTrigDegree_mono T)
    (2 * Real.pi / T) (by positivity) _ α hα hα1 f hrate
  intro n p hp x y
  obtain ⟨q, hq, hb⟩ := P102.Approximation.bernstein_real T n p hp
  exact circle_increment_of_derivative T p q hq
    ((2 * Real.pi / T) * n * ‖p‖) (by positivity) hb x y

theorem inverse_complex (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (f : C(Circle T, ℂ))
    (hrate : Asymptotics.IsBigO atTop
      (fun n : ℕ => P102.Approximation.JacksonPeriodic.Expected.complexBestErrorValue T f n)
      (fun n : ℕ => (n : ℝ) ^ (-α))) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α := by
  have hTpos : 0 < T := Fact.out
  apply holder_of_bernstein_scheme (complexTrigDegree T) (complexTrigDegree_mono T)
    (2 * Real.pi / T) (by positivity) _ α hα hα1 f hrate
  intro n p hp x y
  obtain ⟨q, hq, hb⟩ := P102.Approximation.bernstein_complex T n p hp
  exact circle_increment_of_derivative T p q hq
    ((2 * Real.pi / T) * n * ‖p‖) (by positivity) hb x y

end Circle

/-- Conditional draft of the inverse.  Both full upstream statements occur
as premises in the contract's order, although this direction needs neither. -/
theorem inverse_conditional
    (_direct : P102.Approximation.JacksonPeriodic.Expected.directStatement)
    (_holder : P102.Approximation.JacksonPeriodic.Expected.holderStatement) :
    Expected.inverseStatement := by
  intro T hT α hα hα1
  exact ⟨inverse_real T α hα hα1, inverse_complex T α hα hα1⟩

/-- The original equivalence, conditional on the complete direct interfaces. -/
theorem equivalence_conditional
    (direct : P102.Approximation.JacksonPeriodic.Expected.directStatement)
    (holder : P102.Approximation.JacksonPeriodic.Expected.holderStatement) :
    Expected.equivalenceStatement := by
  intro T hT α hα hα1
  obtain ⟨hr, hc⟩ := inverse_conditional direct holder T α hα hα1
  constructor
  · intro f
    refine ⟨hr f, ?_⟩
    rintro ⟨H, hH, hf⟩
    exact (holder T α hα hα1 H hH).1 f hf
  · intro f
    refine ⟨hc f, ?_⟩
    rintro ⟨H, hH, hf⟩
    exact (holder T α hα hα1 H hH).2 f hf

end P102.Approximation.JacksonInverse

theorem _root_.«P102».«Approximation».«JacksonInverse».«equivalence» : _root_.«P102».«Approximation».«JacksonInverse».«Expected».«equivalenceStatement» :=
  @_root_.«P102».«Approximation».«JacksonInverse».«equivalence_conditional» (@_root_.«P102».«Approximation».«JacksonPeriodic».«direct_estimate») (@_root_.«P102».«Approximation».«JacksonPeriodic».«holder_rate»)
theorem _root_.«P102».«Approximation».«JacksonInverse».«inverse» : _root_.«P102».«Approximation».«JacksonInverse».«Expected».«inverseStatement» :=
  @_root_.«P102».«Approximation».«JacksonInverse».«inverse_conditional» (@_root_.«P102».«Approximation».«JacksonPeriodic».«direct_estimate») (@_root_.«P102».«Approximation».«JacksonPeriodic».«holder_rate»)
