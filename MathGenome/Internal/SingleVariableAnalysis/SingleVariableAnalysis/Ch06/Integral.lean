import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.Integral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.TaylorPolynomial
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Oriented
import Batteries.Tactic.OpenPrivate

/-!
K03.06.integral (paper.tex:2804–2822). Differentiate the finite sum
Σ_{k≤n} (x-t)^k D_k(t)/k!: its derivative terms cancel consecutively,
leaving (x-t)^n D_{n+1}(t)/n!. Apply the already proved proper Riemann
fundamental theorem on the compact hull and then its orientation convention.
Continuity proves Darboux integrability before any integral value is used.
The endpoint jets are the upstream closed derivative families, or equivalently
canonical within derivatives; no ambient endpoint differentiability is imposed.
-/

noncomputable section
namespace SingleVariableAnalysis
open Set
open scoped BigOperators
open private parts_continuous_real_integrable parts_continuous_complex_integrable
  from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts

universe u
variable {K : Type u} [RCLike K]

/-- The normalized powers in the integral Taylor formula. -/
def taylorIntegralWeight (k : ℕ) (x t : ℝ) : K :=
  (algebraMap ℝ K (x-t))^k / (k.factorial : K)

/-- Differentiating a normalized power cancels its factorial factor. -/
theorem taylorIntegralWeight_hasDerivAt (k : ℕ) (x t : ℝ) :
    HasDerivAt (taylorIntegralWeight (K := K) (k+1) x)
      (-taylorIntegralWeight (K := K) k x t) t := by
  have hc : HasDerivAt (fun s : ℝ => algebraMap ℝ K (x-s)) (-1) t := by
    simpa [Function.comp_def] using! (RCLike.ofRealCLM : ℝ →L[ℝ] K).hasDerivAt.scomp t
      ((hasDerivAt_const t x).sub (hasDerivAt_id t))
  convert (hc.pow (k+1)).div_const ((k+1).factorial : K) using 1
  · rfl
  · dsimp [taylorIntegralWeight]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hs : (k : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp

/-- A finite Taylor sum based at a moving point. Its derivative telescopes. -/
def movingTaylorSum (D : ℕ → ℝ → K) (n : ℕ) (x t : ℝ) : K :=
  ∑ k ∈ Finset.range (n+1), taylorIntegralWeight k x t * D k t

theorem movingTaylorSum_hasDerivAt (D : ℕ → ℝ → K) (n : ℕ) (x t : ℝ)
    (hD : ∀ j ≤ n, HasDerivAt (D j) (D (j+1) t) t) :
    HasDerivAt (movingTaylorSum D n x)
      (taylorIntegralWeight n x t * D (n+1) t) t := by
  induction n with
  | zero =>
    convert hD 0 le_rfl using 1
    · funext s
      simp [movingTaylorSum, taylorIntegralWeight]
    · simp [taylorIntegralWeight]
  | succ n ih =>
    have ih' := ih (fun j hj => hD j (by omega))
    have hlast := (taylorIntegralWeight_hasDerivAt (K := K) n x t).mul
      (hD (n+1) le_rfl)
    have he : movingTaylorSum D (n+1) x = fun s =>
        movingTaylorSum D n x s + taylorIntegralWeight (n+1) x s * D (n+1) s := by
      funext s
      exact Finset.sum_range_succ _ _
    rw [he]
    convert ih'.add hlast using 1
    ring

theorem movingTaylorSum_self (D : ℕ → ℝ → K) (n : ℕ) (x : ℝ) :
    movingTaylorSum D n x x = D 0 x := by
  unfold movingTaylorSum
  rw [Finset.sum_eq_single 0]
  · simp [taylorIntegralWeight]
  · intro k _ hk
    simp [taylorIntegralWeight, hk]
  · simp

theorem taylorIntegralWeight_continuous (k : ℕ) (x : ℝ) :
    Continuous (taylorIntegralWeight (K := K) k x) := by
  exact ((RCLike.continuous_ofReal.comp (continuous_const.sub continuous_id)).pow k).div_const _

theorem movingTaylorSum_continuousOn (D : ℕ → ℝ → K) (n : ℕ) (x : ℝ)
    (s : Set ℝ) (hD : ∀ j ≤ n, ContinuousOn (D j) s) :
    ContinuousOn (movingTaylorSum D n x) s := by
  apply continuousOn_finsetSum
  intro j hj
  exact (taylorIntegralWeight_continuous j x).continuousOn.mul (hD j (by
    have := Finset.mem_range.mp hj
    omega))

/-- Restrict compact regularity to the segment needed by the integral. -/
theorem integralRemainder_family_restriction (f : ℝ → K) (n : ℕ) (u v : ℝ)
    (D : ℕ → ℝ → K) (hD : ClosedDerivativeFamily (n+1) f u v D)
    (a x : ℝ) (ha : a ∈ Icc u v) (hx : x ∈ Icc u v) :
    (∀ j ≤ n+1, ContinuousOn (D j) (Icc (min a x) (max a x))) ∧
    (∀ t ∈ Ioo (min a x) (max a x), ∀ j ≤ n,
      HasDerivAt (D j) (D (j+1) t) t) := by
  have hs : Icc (min a x) (max a x) ⊆ Icc u v :=
    Icc_subset_Icc (le_min ha.1 hx.1) (max_le ha.2 hx.2)
  refine ⟨fun j hj => (hD.2.1 j hj).mono hs, ?_⟩
  intro t ht j hj
  have ht' : t ∈ Ioo u v :=
    ⟨(le_min ha.1 hx.1).trans_lt ht.1, ht.2.trans_le (max_le ha.2 hx.2)⟩
  exact (hD.2.2 j (by omega) t ⟨ht'.1.le, ht'.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht'.1 ht'.2)

theorem movingTaylorSum_formula (D : ℕ → ℝ → K) (n : ℕ) (x a : ℝ) :
    movingTaylorSum D n x a =
      ∑ k ∈ Finset.range (n+1), D k a / (k.factorial : K) *
        (algebraMap ℝ K (x-a))^k := by
  apply Finset.sum_congr rfl
  intro k _
  dsimp [taylorIntegralWeight]
  ring

/-- At an interior base point the closed-interval Taylor sum is precisely
upstream `TaylorPolynomialEval`, whose derivatives use the real variable. -/
theorem movingTaylorSum_eq_taylorPolynomialEval (f : ℝ → K) (n : ℕ) (u v : ℝ)
    (D : ℕ → ℝ → K) (hD : ClosedDerivativeFamily (n+1) f u v D)
    (a x : ℝ) (ha : a ∈ Ioo u v) :
    movingTaylorSum D n x a = TaylorPolynomialEval f n a x := by
  rw [movingTaylorSum_formula, taylorPolynomialEval_formula]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n+1 := by have := Finset.mem_range.mp hk; omega
  rw [closedDerivativeFamily_eq_interior (n+1) f u v D hD k hk' ha]

/-- Canonical within derivatives realize compact C^k regularity, also when
there is just one point and every within derivative relation is vacuous. -/
theorem integralRemainder_within_family {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (k : ℕ) (u v : ℝ)
    (huv : u ≤ v) (hf : ContDiffOn ℝ k f (Icc u v)) :
    ClosedDerivativeFamily k f u v (fun j => iteratedDerivWithin j f (Icc u v)) := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · refine ⟨by simp [Set.EqOn], ?_, ?_⟩
    · intro j _
      simp only [Icc_self]
      exact continuousOn_singleton _ _
    · intro j _ x hx
      have hxu : x = u := le_antisymm hx.2 hx.1
      subst x
      apply HasFDerivWithinAt.of_not_accPt
      rw [accPt_principal_iff_nhdsWithin]
      simp
  · obtain ⟨hc, hd⟩ :=
      (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (uniqueDiffOn_Icc hlt)).mp hf
    refine ⟨by simp [Set.EqOn], hc, ?_⟩
    intro j hj x hx
    dsimp only
    rw [iteratedDerivWithin_succ]
    exact (hd j hj x hx).hasDerivWithinAt

namespace Riemann
namespace O
export Specs.SingleVariableAnalysis.Ch08.Oriented
  (realIntegrableValue realIntegralValue complexIntegrableValue complexIntegralValue)
end O


/-- K03.06.integral for real values, including both endpoint orders. -/
theorem real_integral_remainder :
    Specs.SingleVariableAnalysis.Ch06.Integral.realIntegralRemainder := by
  intro f n u v D hD a ha x hx
  change ClosedDerivativeFamily (n+1) f u v D at hD
  obtain ⟨hc, hd⟩ := integralRemainder_family_restriction f n u v D hD a x ha hx
  let g : ℝ → ℝ := fun t => (x-t)^n * D (n+1) t
  have hgc : ContinuousOn g (Icc (min a x) (max a x)) := by
    exact ((taylorIntegralWeight_continuous (K := ℝ) n x).mul_const
      (n.factorial : ℝ)).continuousOn.mul (hc (n+1) le_rfl) |>.congr (by
        intro t _
        dsimp [g, taylorIntegralWeight]
        field_simp)
  have hg := parts_continuous_real_integrable min_le_max hgc
  obtain ⟨hm, hmv⟩ := real_mul_value hg (1 / (n.factorial : ℝ))
  have hqc := movingTaylorSum_continuousOn D n x _
    (fun j hj => hc j (by omega))
  have hqd : ∀ t ∈ Ioo (min a x) (max a x),
      HasDerivAt (movingTaylorSum D n x) ((1 / (n.factorial : ℝ)) * g t) t := by
    intro t ht
    convert movingTaylorSum_hasDerivAt D n x t (hd t ht) using 1
    dsimp [g, taylorIntegralWeight]
    ring
  have hftc := real_ftc_second (movingTaylorSum D n x)
    (fun t => (1 / (n.factorial : ℝ)) * g t) (min a x) (max a x)
    min_le_max hqc hqd hm
  change realIntegral _ hm = _ at hftc
  rw [hmv] at hftc
  have he : (1 / (n.factorial : ℝ)) *
      O.realIntegralValue g (a := a) (b := x) hg =
      movingTaylorSum D n x x - movingTaylorSum D n x a := by
    by_cases hax : a ≤ x
    · simpa only [O.realIntegralValue, ite_eq_left hax, min_eq_left hax,
        max_eq_right hax] using hftc
    · have hxa : x ≤ a := le_of_not_ge hax
      have hftc' : (1 / (n.factorial : ℝ)) * realIntegral g hg =
          movingTaylorSum D n x a - movingTaylorSum D n x x := by
        calc
          _ = movingTaylorSum D n x (max a x) - movingTaylorSum D n x (min a x) := hftc
          _ = _ := by rw [min_eq_right hxa, max_eq_left hxa]
      simp only [O.realIntegralValue, ite_eq_right hax, mul_neg]
      simpa only [neg_sub] using congrArg Neg.neg hftc'
  refine ⟨hg, ?_⟩
  rw [movingTaylorSum_self, hD.1 hx, movingTaylorSum_formula] at he
  exact he.symm

/-- K03.06.integral for complex values, including both endpoint orders. -/
theorem complex_integral_remainder :
    Specs.SingleVariableAnalysis.Ch06.Integral.complexIntegralRemainder := by
  intro f n u v D hD a ha x hx
  change ClosedDerivativeFamily (n+1) f u v D at hD
  obtain ⟨hc, hd⟩ := integralRemainder_family_restriction f n u v D hD a x ha hx
  let g : ℝ → ℂ := fun t => (algebraMap ℝ ℂ (x-t))^n * D (n+1) t
  have hgc : ContinuousOn g (Icc (min a x) (max a x)) := by
    exact ((taylorIntegralWeight_continuous (K := ℂ) n x).mul_const
      (n.factorial : ℂ)).continuousOn.mul (hc (n+1) le_rfl) |>.congr (by
        intro t _
        dsimp [g, taylorIntegralWeight]
        have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        field_simp)
  have hg := parts_continuous_complex_integrable min_le_max hgc
  obtain ⟨hm, hmv⟩ := complex_mul_value hg (1 / (n.factorial : ℂ))
  have hqc := movingTaylorSum_continuousOn D n x _
    (fun j hj => hc j (by omega))
  have hqd : ∀ t ∈ Ioo (min a x) (max a x),
      HasDerivAt (movingTaylorSum D n x) ((1 / (n.factorial : ℂ)) * g t) t := by
    intro t ht
    convert movingTaylorSum_hasDerivAt D n x t (hd t ht) using 1
    dsimp [g, taylorIntegralWeight]
    ring
  have hftc := complex_ftc_second (movingTaylorSum D n x)
    (fun t => (1 / (n.factorial : ℂ)) * g t) (min a x) (max a x)
    min_le_max hqc hqd hm
  change complexIntegral _ hm = _ at hftc
  rw [hmv] at hftc
  have he : (1 / (n.factorial : ℂ)) *
      O.complexIntegralValue g (a := a) (b := x) hg =
      movingTaylorSum D n x x - movingTaylorSum D n x a := by
    by_cases hax : a ≤ x
    · simpa only [O.complexIntegralValue, ite_eq_left hax, min_eq_left hax,
        max_eq_right hax] using hftc
    · have hxa : x ≤ a := le_of_not_ge hax
      have hftc' : (1 / (n.factorial : ℂ)) * complexIntegral g hg =
          movingTaylorSum D n x a - movingTaylorSum D n x x := by
        calc
          _ = movingTaylorSum D n x (max a x) - movingTaylorSum D n x (min a x) := hftc
          _ = _ := by rw [min_eq_right hxa, max_eq_left hxa]
      simp only [O.complexIntegralValue, ite_eq_right hax, mul_neg]
      simpa only [neg_sub] using congrArg Neg.neg hftc'
  refine ⟨hg, ?_⟩
  rw [movingTaylorSum_self, hD.1 hx, movingTaylorSum_formula] at he
  exact he.symm

theorem real_integral_remainder_within :
    Specs.SingleVariableAnalysis.Ch06.Integral.realIntegralRemainderWithin := by
  intro f n u v hf a ha x hx
  have hD := integralRemainder_within_family f (n+1) u v (ha.1.trans ha.2) hf
  change Specs.SingleVariableAnalysis.Ch04.Higher.closedDerivativeFamilyValue
    (n+1) f u v (fun j => iteratedDerivWithin j f (Icc u v)) at hD
  exact real_integral_remainder f n u v (fun j => iteratedDerivWithin j f (Icc u v))
    hD a ha x hx

theorem complex_integral_remainder_within :
    Specs.SingleVariableAnalysis.Ch06.Integral.complexIntegralRemainderWithin := by
  intro f n u v hf a ha x hx
  have hD := integralRemainder_within_family f (n+1) u v (ha.1.trans ha.2) hf
  change Specs.SingleVariableAnalysis.Ch04.Higher.closedDerivativeFamilyValue
    (n+1) f u v (fun j => iteratedDerivWithin j f (Icc u v)) at hD
  exact complex_integral_remainder f n u v (fun j => iteratedDerivWithin j f (Icc u v))
    hD a ha x hx

end Riemann
end SingleVariableAnalysis
