import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.WeylSumsProducts
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.WeylProducts
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

import Mathlib.Analysis.InnerProductSpace.NormDet

noncomputable section
universe u
namespace ExpandedFA.TraceIdeals.WeylSumsProducts
open Filter Finset
open scoped BigOperators ENNReal

/-- The supporting line at a differentiability point of a convex function. -/
lemma convex_support_line {F : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ F)
    (hd : Differentiable ℝ F) (a b : ℝ) :
    F a + deriv F a * (b-a) ≤ F b := by
  rcases lt_trichotomy a b with h | h | h
  · have hs := hc.deriv_le_slope (Set.mem_univ a) (Set.mem_univ b) h (hd a)
    rw [slope_def_field] at hs
    have := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    linarith
  · subst b
    simp
  · have hs := hc.slope_le_deriv (Set.mem_univ b) (Set.mem_univ a) h (hd a)
    rw [slope_def_field] at hs
    have := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

/-- The differentiable weak-majorization argument: supporting lines followed
by Abel's inequality, with nonnegative decreasing derivative weights. -/
lemma convex_sum_of_prefix_sums (n : ℕ) (a b : ℕ → ℝ)
    (ha : AntitoneOn a (Set.Iio n))
    (hab : ∀ k ≤ n, ∑ i ∈ range k, a i ≤ ∑ i ∈ range k, b i)
    {F : ℝ → ℝ} (hd : Differentiable ℝ F) (hm : Monotone F)
    (hc : ConvexOn ℝ Set.univ F) :
    (∑ i ∈ range n, F (a i)) ≤ ∑ i ∈ range n, F (b i) := by
  have hweight := Finset.sum_mul_le_sum_mul_of_sum_range_le hab
    (g := fun i => deriv F (a i))
    (fun _ => hm.deriv_nonneg)
    (fun i hi j hj hij => hc.monotoneOn_deriv (fun x _ => hd x)
      (Set.mem_univ _) (Set.mem_univ _) (ha hi hj hij))
  have hs := sum_le_sum (s := range n) (fun i _ => convex_support_line hc hd (a i) (b i))
  simp only [sum_add_distrib, mul_sub, sum_sub_distrib] at hs
  have hw : (∑ i ∈ range n, deriv F (a i) * a i) ≤
      ∑ i ∈ range n, deriv F (a i) * b i := by
    simpa only [mul_comm] using hweight
  linarith

/-- No logarithm of zero is taken: remove trailing zero entries first. -/
theorem log_majorization_bridge : Spec.LogMajorizationBridge := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro x y hx hy hanti hprod g hg0 hgpos hd hm hc
    have ih' := ih x y (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
      (hanti.mono (by intro i hi; exact lt_trans hi (Nat.lt_succ_self n)))
      (fun k hk => hprod k (by omega)) g hg0 hgpos hd hm hc
    by_cases hzero : x n = 0
    · rw [sum_range_succ, sum_range_succ, hzero, hg0, add_zero]
      exact ih'.trans (le_add_of_nonneg_right (hgpos _ (hy n (by omega))))
    have hxpos : ∀ i < n+1, 0 < x i := by
      intro i hi
      have hxn : 0 < x n := lt_of_le_of_ne (hx n (by omega)) (Ne.symm hzero)
      exact hxn.trans_le (hanti hi (by simp) (by omega))
    have hpy : 0 < ∏ i ∈ range (n+1), y i :=
      (prod_pos (fun i hi => hxpos i (mem_range.mp hi))).trans_le (hprod _ le_rfl)
    have hypos : ∀ i < n+1, 0 < y i := by
      intro i hi
      have hne : y i ≠ 0 := by
        intro hz
        have := prod_eq_zero (mem_range.mpr hi) hz
        linarith
      exact lt_of_le_of_ne (hy i hi) (Ne.symm hne)
    have hlogs : ∀ k ≤ n+1,
        ∑ i ∈ range k, Real.log (x i) ≤ ∑ i ∈ range k, Real.log (y i) := by
      intro k hk
      rw [← Real.log_prod (fun i hi => (hxpos i (lt_of_lt_of_le (mem_range.mp hi) hk)).ne'),
        ← Real.log_prod (fun i hi => (hypos i (lt_of_lt_of_le (mem_range.mp hi) hk)).ne')]
      exact Real.log_le_log (prod_pos (fun i hi => hxpos i (lt_of_lt_of_le (mem_range.mp hi) hk)))
        (hprod k hk)
    have hloga : AntitoneOn (fun i => Real.log (x i)) (Set.Iio (n+1)) := by
      intro i hi j hj hij
      exact Real.log_le_log (hxpos j hj) (hanti hi hj hij)
    have h := convex_sum_of_prefix_sums (n+1) _ _ hloga hlogs hd hm hc
    have hleft : (∑ i ∈ range (n+1), g (Real.exp (Real.log (x i)))) =
        ∑ i ∈ range (n+1), g (x i) := by
      apply sum_congr rfl
      intro i hi
      rw [Real.exp_log (hxpos i (mem_range.mp hi))]
    have hright : (∑ i ∈ range (n+1), g (Real.exp (Real.log (y i)))) =
        ∑ i ∈ range (n+1), g (y i) := by
      apply sum_congr rfl
      intro i hi
      rw [Real.exp_log (hypos i (mem_range.mp hi))]
    rwa [hleft, hright] at h

/-- Exponential powers after logarithmic change of variables. -/
lemma power_log_convex (p : ℕ) :
    Differentiable ℝ (fun t : ℝ => (Real.exp t)^p) ∧
    Monotone (fun t : ℝ => (Real.exp t)^p) ∧
    ConvexOn ℝ Set.univ (fun t : ℝ => (Real.exp t)^p) := by
  have he : (fun t : ℝ => (Real.exp t)^p) = (fun t => Real.exp ((p : ℝ)*t)) := by
    ext t
    exact (Real.exp_nat_mul t p).symm
  rw [he]
  refine ⟨Real.differentiable_exp.comp (differentiable_id.const_mul (p : ℝ)), ?_, ?_⟩
  · intro a b hab
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg p))
  · exact convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ (p : ℝ))

/-- Convexity of the logarithmic shifted-product function, including `r=0`. -/
lemma shifted_log_convex (r : ℝ) (hr : 0 ≤ r) :
    Differentiable ℝ (fun t : ℝ => Real.log (1+r*Real.exp t)) ∧
    Monotone (fun t : ℝ => Real.log (1+r*Real.exp t)) ∧
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (1+r*Real.exp t)) := by
  have hder (t : ℝ) : HasDerivAt (fun t : ℝ => Real.log (1+r*Real.exp t))
      (r*Real.exp t / (1+r*Real.exp t)) t := by
    convert (((Real.hasDerivAt_exp t).const_mul r).const_add 1).log (by positivity) using 1
  have hd : Differentiable ℝ (fun t : ℝ => Real.log (1+r*Real.exp t)) :=
    fun t => (hder t).differentiableAt
  refine ⟨hd, ?_, ?_⟩
  · intro a b hab
    apply Real.log_le_log (by positivity)
    gcongr
  · apply Monotone.convexOn_univ_of_deriv hd
    intro a b hab
    rw [(hder a).deriv, (hder b).deriv]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hab) hr
    nlinarith

/-- Increasing positive partial products. -/
lemma monotone_partial_products (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ f i) :
    Monotone (fun n => ∏ i ∈ range n, f i) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [prod_range_succ]
  have hn : 0 ≤ ∏ i ∈ range n, f i :=
    prod_nonneg (fun i _ => (zero_le_one.trans (hf i)))
  nlinarith [hf n]

/-- Domination of partial products ensures convergence of the smaller product. -/
lemma product_limit_of_partial_products_le (f g : ℕ → ℝ)
    (hf : ∀ i, 1 ≤ f i) (hg : ∀ i, 1 ≤ g i)
    (hfg : ∀ n, (∏ i ∈ range n, f i) ≤ ∏ i ∈ range n, g i)
    {P : ℝ} (hP : Tendsto (fun n => ∏ i ∈ range n, g i) atTop (nhds P)) :
    ∃ Q : ℝ, Tendsto (fun n => ∏ i ∈ range n, f i) atTop (nhds Q) ∧ Q ≤ P := by
  have hbound (n : ℕ) : (∏ i ∈ range n, f i) ≤ P :=
    (hfg n).trans ((monotone_partial_products g hg).ge_of_tendsto hP n)
  have hbdd : BddAbove (Set.range (fun n => ∏ i ∈ range n, f i)) := by
    exact ⟨P, fun _ ⟨n, hn⟩ => hn ▸ hbound n⟩
  have hQ := tendsto_atTop_ciSup (monotone_partial_products f hf) hbdd
  exact ⟨_, hQ, le_of_tendsto' hQ hbound⟩

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The accepted spectral product theorem on every actual prefix. -/
lemma eigenvalue_prefix_products (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (ev : ℕ → ℂ) (hev : Spec.AdmissibleEigenvalueSequence T ev) (n : ℕ) :
    (∏ j ∈ range n, ‖ev j‖) ≤
    ∏ j ∈ range n, CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1) := by
  have h := WeylProducts.padded_weyl_product H T hT n (fun i : Fin n => ev i.val) (hev.2 n)
  rw [Fin.prod_univ_eq_prod_range (fun j => ‖ev j‖) n,
    Fin.prod_univ_eq_prod_range
      (fun j => CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) n] at h
  exact h

/-- Apply the bridge to a nonnegative function of eigenvalue moduli. -/
lemma weyl_sum_transform (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (ev : ℕ → ℂ) (hev : Spec.AdmissibleEigenvalueSequence T ev)
    (g : ℝ → ℝ) (hg0 : g 0 = 0) (hgpos : ∀ t, 0 ≤ t → 0 ≤ g t)
    (hd : Differentiable ℝ (fun t => g (Real.exp t)))
    (hm : Monotone (fun t => g (Real.exp t)))
    (hc : ConvexOn ℝ Set.univ (fun t => g (Real.exp t))) (n : ℕ) :
    (∑ j ∈ range n, g ‖ev j‖) ≤
    ∑ j ∈ range n, g (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) := by
  exact log_majorization_bridge n _ _ (fun i _ => norm_nonneg _)
    (fun i _ => (CompactSpectral.SingularApproximation.singular_sequence_properties ℂ H H T hT).1
      (i+1) (by omega)) (hev.1.antitoneOn _) (fun k _ => eigenvalue_prefix_products T hT ev hev k)
    g hg0 hgpos hd hm hc

/-- All positive integer powers, notably the ordinary and squared sums. -/
theorem weyl_power_sums : Spec.WeylPowerSums.{u} := by
  intro H _ _ _ T hT ev hev p hp n
  obtain ⟨hd, hm, hc⟩ := power_log_convex p
  exact weyl_sum_transform T hT ev hev (fun t => t^p) (zero_pow (by omega))
    (fun t ht => pow_nonneg ht p) hd hm hc n

/-- The nonnegative extended-real sum inequality also covers divergence. -/
theorem weyl_extended_sums : Spec.WeylExtendedSums.{u} := by
  intro H _ _ _ T hT ev hev p hp
  rw [ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_eq_iSup_nat]
  apply iSup_mono
  intro n
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (norm_nonneg _) p),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg
      ((CompactSpectral.SingularApproximation.singular_sequence_properties ℂ H H T hT).1
        (i+1) (by omega)) p)]
  exact ENNReal.ofReal_le_ofReal (weyl_power_sums H T hT ev hev p hp n)

/-- Summability and the finite real sum bound when the singular-value power
sum is finite. No summability of the eigenvalues is assumed. -/
theorem weyl_summable_powers : Spec.WeylSummablePowers.{u} := by
  intro H _ _ _ T hT ev hev p hp hs
  have hb (n : ℕ) : (∑ j ∈ range n, ‖ev j‖^p) ≤
      ∑' j, (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1))^p := by
    apply (weyl_power_sums H T hT ev hev p hp n).trans
    exact hs.sum_le_tsum _ (fun i _ => pow_nonneg
      ((CompactSpectral.SingularApproximation.singular_sequence_properties ℂ H H T hT).1
        (i+1) (by omega)) p)
  exact ⟨summable_of_sum_range_le (fun i => pow_nonneg (norm_nonneg _) p) hb,
    Real.tsum_le_of_sum_range_le (fun i => pow_nonneg (norm_nonneg _) p) hb⟩

/-- Logarithmic convexity gives each finite shifted-product bound. -/
theorem weyl_finite_shifted_products : Spec.WeylFiniteShiftedProducts.{u} := by
  intro H _ _ _ T hT ev hev r hr n
  obtain ⟨hd, hm, hc⟩ := shifted_log_convex r hr
  have h := weyl_sum_transform T hT ev hev (fun t => Real.log (1+r*t))
    (by simp) (fun t ht => Real.log_nonneg (by nlinarith)) hd hm hc n
  have hs (j : ℕ) : 0 ≤ CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1) :=
    (CompactSpectral.SingularApproximation.singular_sequence_properties ℂ H H T hT).1
      (j+1) (by omega)
  rw [← Real.log_prod (fun i _ => (show 0 < 1+r*‖ev i‖ by positivity).ne'),
    ← Real.log_prod (fun i _ => (show 0 < 1+r*CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i+1)
      by have := hs i; positivity).ne')] at h
  exact (Real.log_le_log_iff (by positivity) (by
    apply prod_pos; intro i _; have := hs i; positivity)).mp h

/-- Pass to limits of the increasing partial products. -/
theorem weyl_infinite_shifted_products : Spec.WeylInfiniteShiftedProducts.{u} := by
  intro H _ _ _ T hT ev hev r hr P hP
  apply product_limit_of_partial_products_le _ _ _ _
    (fun n => weyl_finite_shifted_products H T hT ev hev r hr n) hP
  · intro i
    exact le_add_of_nonneg_right (mul_nonneg hr (norm_nonneg _))
  · intro i
    exact le_add_of_nonneg_right (mul_nonneg hr
      ((CompactSpectral.SingularApproximation.singular_sequence_properties ℂ H H T hT).1
        (i+1) (by omega)))

namespace Real
open CompactSpectral.SingularApproximation
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma shift_power_kernel (T : H →L[ℝ] H) (z : ℝ) (p : ℕ) :
    LinearMap.ker ((z • LinearMap.id - T.toLinearMap) ^ p) =
      Module.End.genEigenspace T.toLinearMap z p := by
  rw [Module.End.genEigenspace_nat]
  have hneg : z • LinearMap.id - T.toLinearMap =
      (-1 : ℝ) • (T.toLinearMap - z • (1 : Module.End ℝ H)) := by
    simp only [neg_one_smul, neg_sub, Module.End.one_eq_id]
  rw [hneg, smul_pow, LinearMap.ker_smul _ _ (pow_ne_zero p (by norm_num))]

/-- The multiplicity used here is finite at every nonzero scalar on the
original Hilbert space; no finite-dimensional or normality premise is added. -/
lemma compact_maxGenEigenspace_finiteDimensional (T : H →L[ℝ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    {z : ℝ} (hz : z ≠ 0) : FiniteDimensional ℝ (Module.End.maxGenEigenspace T.toLinearMap z) := by
  obtain ⟨p, hp, hfin, hstable, hunion⟩ :=
    Fredholm.compact_generalized_eigenspace_stabilizes T hT z hz
  have heq : Module.End.maxGenEigenspace T.toLinearMap z =
      LinearMap.ker ((z • LinearMap.id - T.toLinearMap) ^ p) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
      have hxm : x ∈ Module.End.genEigenspace T.toLinearMap z m := by
        exact Module.End.mem_genEigenspace_nat.mpr hm
      by_cases hmp : m ≤ p
      · rw [shift_power_kernel]
        exact (Module.End.genEigenspace T.toLinearMap z).monotone (by exact_mod_cast hmp) hxm
      · rw [← shift_power_kernel] at hxm
        rwa [hstable m (Nat.le_of_not_ge hmp)] at hxm
    · rw [shift_power_kernel]
      exact Module.End.genEigenspace_le_maximal T.toLinearMap z p
  rw [heq]
  exact hfin

section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open Module

lemma native_norm_image_sum_sq (A : E →ₗ[ℝ] E) {J : Type*} (e : J → Fin (finrank ℝ E))
    (he : Function.Injective e) (a : J → ℝ) (q : Finset J) :
    ‖A (∑ j ∈ q, a j • A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl (e j))‖ ^ 2 =
      ∑ j ∈ q, ‖a j‖ ^ 2 * A.singularValues (e j) ^ 2 := by
  let b := A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let G := A.adjoint.comp A
  have hg (j : J) : G (b (e j)) =
      (A.isSymmetric_adjoint_comp_self.eigenvalues rfl (e j) : ℝ) • b (e j) :=
    A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl (e j)
  have hb : Orthonormal ℝ (fun j => b (e j)) := b.orthonormal.comp e he
  have hm : G (∑ j ∈ q, a j • b (e j)) =
      ∑ j ∈ q, (a j * (A.isSymmetric_adjoint_comp_self.eigenvalues rfl (e j) : ℝ)) • b (e j) := by
    simp only [map_sum, map_smul, hg, smul_smul]
  change ‖A (∑ j ∈ q, a j • b (e j))‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq]
  rw [← A.adjoint_inner_right, ← LinearMap.comp_apply, hm]
  rw [hb.inner_sum]
  simp only [RCLike.conj_to_real, Real.norm_eq_abs, sq_abs]
  simp_rw [← A.sq_singularValues_fin rfl]
  apply sum_congr rfl
  intro i _
  ring

lemma native_singularValue_le_error (A F : E →L[ℝ] E) (k : ℕ)
    (hF : F.toLinearMap.rank < (k + 1 : ℕ)) :
    A.toLinearMap.singularValues k ≤ ‖A - F‖ := by
  classical
  by_cases hk : finrank ℝ E ≤ k
  · rw [A.toLinearMap.singularValues_of_finrank_le hk]
    exact norm_nonneg _
  have hk : k < finrank ℝ E := Nat.lt_of_not_ge hk
  let b := A.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let e : Fin (k+1) → Fin (finrank ℝ E) := fun j => ⟨j.val, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun j : Fin (finrank ℝ E) => j.val) hij
  have hb : Orthonormal ℝ (fun j => b (e j)) := b.orthonormal.comp e he
  let c := A.toLinearMap.singularValues k
  have hc : 0 ≤ c := A.toLinearMap.singularValues_nonneg k
  have hlow (a : Fin (k+1) → ℝ) :
      c * ‖∑ j, a j • b (e j)‖ ≤ ‖A (∑ j, a j • b (e j))‖ := by
    have hnorm : ‖∑ j, a j • b (e j)‖ ^ 2 = ∑ j, ‖a j‖ ^ 2 := by
      have h := congrArg RCLike.re (hb.inner_sum a a Finset.univ)
      simpa only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_re, map_sum,
        RCLike.conj_mul, ← RCLike.ofReal_pow] using h
    have hnormA := native_norm_image_sum_sq A.toLinearMap e he a Finset.univ
    change ‖A (∑ j, a j • b (e j))‖ ^ 2 = _ at hnormA
    have hs : (c * ‖∑ j, a j • b (e j)‖)^2 ≤ ‖A (∑ j, a j • b (e j))‖^2 := by
      rw [mul_pow, hnorm, hnormA, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [mul_comm (c^2)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply pow_le_pow_left₀ hc
      exact A.toLinearMap.singularValues_antitone (by dsimp [e]; omega)
    nlinarith [norm_nonneg (A (∑ j, a j • b (e j)))]
  by_contra h
  have hlt : ‖A - F‖ < c := lt_of_not_ge h
  have hli : LinearIndependent ℝ (fun j => F (b (e j))) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    let x := ∑ j, a j • b (e j)
    have hxF : F x = 0 := by simpa only [x, map_sum, map_smul] using ha
    have hxge := hlow a
    change c * ‖x‖ ≤ ‖A x‖ at hxge
    have hxle := (A - F).le_opNorm x
    rw [sub_apply, hxF, sub_zero] at hxle
    have hx : x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg x]
    exact Fintype.linearIndependent_iff.mp hb.linearIndependent a hx
  let f : Fin (k+1) → F.range := fun j => ⟨F (b (e j)), ⟨b (e j), rfl⟩⟩
  have hli' : LinearIndependent ℝ f := hli.of_comp F.range.subtype
  have hh := hli'.cardinal_lift_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast] at hh
  have hlt' := Cardinal.lift_lt.mpr hF
  exact (not_lt_of_ge hh) (by simpa only [Cardinal.lift_natCast] using hlt')

lemma native_singularValue_le_approximationNumber (A : E →L[ℝ] E) (k : ℕ) :
    A.toLinearMap.singularValues k ≤
      ExpandedFA.CompactSpectral.SingularApproximation.approximationNumber A (k+1) := by
  apply ExpandedFA.CompactSpectral.SingularApproximation.le_approximationNumber ℝ E E A
    (k+1) (Nat.succ_pos _) _
  intro F hF
  exact native_singularValue_le_error A F k hF

lemma finiteDet_le_singularProduct (A : E →L[ℝ] E) :
    ‖A.toLinearMap.det‖ ≤
      ∏ i : Fin (finrank ℝ E),
        ExpandedFA.CompactSpectral.SingularApproximation.Spec.SingularValueValue A (i.val + 1) := by
  have hA : ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue A.toLinearMap := by
    exact ((isCompact_closedBall (0 : E) 1).image A.continuous).closure
  rw [← A.toLinearMap.normDet_eq_norm_det, A.toLinearMap.normDet_eq_prod_singularValues,
    ← Fin.prod_univ_eq_prod_range]
  change (∏ i : Fin (finrank ℝ E), A.toLinearMap.singularValues i) ≤ _
  apply Finset.prod_le_prod₀
  · intro i _
    exact A.toLinearMap.singularValues_nonneg i
  · intro i _
    rw [(ExpandedFA.CompactSpectral.SingularApproximation.best_approximation
      ℝ E E A hA (i.val + 1) (Nat.succ_pos _)).1]
    exact native_singularValue_le_approximationNumber A i

end FiniteDimensional

variable [CompleteSpace H]

lemma compression_singularValue_le (T : H →L[ℝ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (M : Submodule ℝ H) [FiniteDimensional ℝ M] (n : ℕ) (hn : 0 < n) :
    CompactSpectral.SingularApproximation.Spec.SingularValueValue
        (M.orthogonalProjectionOnto.comp (T.comp M.subtypeL)) n ≤
      CompactSpectral.SingularApproximation.Spec.SingularValueValue T n := by
  have h := singularValue_ideal ℝ H H M M T M.orthogonalProjectionOnto M.subtypeL hT n hn
  have hs := (singular_sequence_properties ℝ H H T hT).1 n hn
  apply h.trans
  calc
    ‖M.orthogonalProjectionOnto‖ * ‖M.subtypeL‖ *
        CompactSpectral.SingularApproximation.Spec.SingularValueValue T n ≤
      1 * 1 * CompactSpectral.SingularApproximation.Spec.SingularValueValue T n := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul M.orthogonalProjectionOnto_norm_le M.norm_subtypeL_le
            (norm_nonneg M.subtypeL) (by norm_num)) hs
    _ = _ := by ring

/-- The restriction and the orthogonal compression are the same actual
operator. Both sides have the inherited norm, not a transported auxiliary norm. -/
lemma invariantDet_le_singularProduct (T : H →L[ℝ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (M : Submodule ℝ H) [FiniteDimensional ℝ M]
    (hM : ∀ x ∈ M, T x ∈ M) :
    ‖(T.toLinearMap.restrict hM).det‖ ≤
      ∏ i : Fin (Module.finrank ℝ M),
        CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i.val + 1) := by
  let A : M →L[ℝ] M := (T.toLinearMap.restrict hM).toContinuousLinearMap
  have hA : Compactness.DefinitionsSpec.IsCompactLinearMapValue A.toLinearMap :=
    ((isCompact_closedBall (0 : M) 1).image A.continuous).closure
  have heq : A = M.orthogonalProjectionOnto.comp (T.comp M.subtypeL) := by
    apply ContinuousLinearMap.ext
    intro x
    change (⟨T x, hM x x.property⟩ : M) = M.orthogonalProjectionOnto (T x)
    exact (M.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T x, hM x x.property⟩).symm
  apply (finiteDet_le_singularProduct A).trans
  apply Finset.prod_le_prod₀
  · intro i _
    exact (singular_sequence_properties ℝ M M A hA).1 (i.val + 1) (Nat.succ_pos _)
  · intro i _
    rw [heq]
    exact compression_singularValue_le T hT M (i.val + 1) (Nat.succ_pos _)

/-- Weyl's finite product bound for the original real operator, with
algebraic multiplicities and arbitrary zero padding. -/
theorem weyl_prefix_products : Spec.Real.WeylPrefixProducts.{u} := by
  classical
  intro H _ _ _ T hT ev hev n
  have hs (j : ℕ) : 0 ≤ CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1) := by
    exact (singular_sequence_properties ℝ H H T hT).1 (j+1) (Nat.succ_pos _)
  by_cases hz : ∃ i : Fin n, ev i.val = 0
  · obtain ⟨i, hi⟩ := hz
    rw [prod_eq_zero (mem_range.mpr i.isLt) (by simp [hi])]
    exact prod_nonneg (fun j _ => hs j)
  have hn : ∀ i : Fin n, ev i.val ≠ 0 := by simpa only [not_exists] using hz
  let e : Fin n → ℝ := fun i => ev i.val
  let q := Finset.univ.image e
  let m : ℝ → ℕ := fun z => (Finset.univ.filter (fun i => e i = z)).card
  have hfin : ∀ z ∈ q, FiniteDimensional ℝ (Module.End.maxGenEigenspace T.toLinearMap z) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact compact_maxGenEigenspace_finiteDimensional T hT (hn i)
  obtain ⟨M, _, hMfin, hM, hdim, hdet⟩ :=
    WeylProducts.finite_generalized_selection T.toLinearMap q m hfin
      (fun z hz => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        exact (hev.2 n).2 _ (hn i))
  letI := hMfin
  have hdim' : Module.finrank ℝ M = n := by
    rw [hdim]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_eq_sum_card_image e Finset.univ).symm
  have hdet' : (T.toLinearMap.restrict hM).det = ∏ i, e i := by
    rw [hdet]
    exact (Finset.prod_comp (s := Finset.univ) (fun z : ℝ => z) e).symm
  have h := invariantDet_le_singularProduct T hT M hM
  rw [hdet', norm_prod, hdim'] at h
  change (∏ i : Fin n, ‖ev i.val‖) ≤
    ∏ i : Fin n, CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i.val+1) at h
  rw [Fin.prod_univ_eq_prod_range (fun j => ‖ev j‖) n,
    Fin.prod_univ_eq_prod_range
      (fun j => CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) n] at h
  exact h

/-- Apply the bridge to a nonnegative function of eigenvalue moduli. -/
lemma weyl_sum_transform (T : H →L[ℝ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (ev : ℕ → ℝ) (hev : Spec.Real.AdmissibleEigenvalueSequence T ev)
    (g : ℝ → ℝ) (hg0 : g 0 = 0) (hgpos : ∀ t, 0 ≤ t → 0 ≤ g t)
    (hd : Differentiable ℝ (fun t => g (Real.exp t)))
    (hm : Monotone (fun t => g (Real.exp t)))
    (hc : ConvexOn ℝ Set.univ (fun t => g (Real.exp t))) (n : ℕ) :
    (∑ j ∈ range n, g ‖ev j‖) ≤
    ∑ j ∈ range n, g (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) := by
  exact log_majorization_bridge n _ _ (fun i _ => norm_nonneg _)
    (fun i _ => (CompactSpectral.SingularApproximation.singular_sequence_properties ℝ H H T hT).1
      (i+1) (by omega)) (hev.1.antitoneOn _) (fun k _ => weyl_prefix_products H T hT ev hev k)
    g hg0 hgpos hd hm hc

/-- All positive integer powers, notably the ordinary and squared sums. -/
theorem weyl_power_sums : Spec.Real.WeylPowerSums.{u} := by
  intro H _ _ _ T hT ev hev p hp n
  obtain ⟨hd, hm, hc⟩ := power_log_convex p
  exact weyl_sum_transform T hT ev hev (fun t => t^p) (zero_pow (by omega))
    (fun t ht => pow_nonneg ht p) hd hm hc n

/-- The nonnegative extended-real sum inequality also covers divergence. -/
theorem weyl_extended_sums : Spec.Real.WeylExtendedSums.{u} := by
  intro H _ _ _ T hT ev hev p hp
  rw [ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_eq_iSup_nat]
  apply iSup_mono
  intro n
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (norm_nonneg _) p),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg
      ((CompactSpectral.SingularApproximation.singular_sequence_properties ℝ H H T hT).1
        (i+1) (by omega)) p)]
  exact ENNReal.ofReal_le_ofReal (weyl_power_sums H T hT ev hev p hp n)

/-- Summability and the finite real sum bound when the singular-value power
sum is finite. No summability of the eigenvalues is assumed. -/
theorem weyl_summable_powers : Spec.Real.WeylSummablePowers.{u} := by
  intro H _ _ _ T hT ev hev p hp hs
  have hb (n : ℕ) : (∑ j ∈ range n, ‖ev j‖^p) ≤
      ∑' j, (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1))^p := by
    apply (weyl_power_sums H T hT ev hev p hp n).trans
    exact hs.sum_le_tsum _ (fun i _ => pow_nonneg
      ((CompactSpectral.SingularApproximation.singular_sequence_properties ℝ H H T hT).1
        (i+1) (by omega)) p)
  exact ⟨summable_of_sum_range_le (fun i => pow_nonneg (norm_nonneg _) p) hb,
    Real.tsum_le_of_sum_range_le (fun i => pow_nonneg (norm_nonneg _) p) hb⟩

/-- Logarithmic convexity gives each finite shifted-product bound. -/
theorem weyl_finite_shifted_products : Spec.Real.WeylFiniteShiftedProducts.{u} := by
  intro H _ _ _ T hT ev hev r hr n
  obtain ⟨hd, hm, hc⟩ := shifted_log_convex r hr
  have h := weyl_sum_transform T hT ev hev (fun t => Real.log (1+r*t))
    (by simp) (fun t ht => Real.log_nonneg (by nlinarith)) hd hm hc n
  have hs (j : ℕ) : 0 ≤ CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1) :=
    (CompactSpectral.SingularApproximation.singular_sequence_properties ℝ H H T hT).1
      (j+1) (by omega)
  rw [← Real.log_prod (fun i _ => (show 0 < 1+r*‖ev i‖ by positivity).ne'),
    ← Real.log_prod (fun i _ => (show 0 < 1+r*CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i+1)
      by have := hs i; positivity).ne')] at h
  exact (Real.log_le_log_iff (by positivity) (by
    apply prod_pos; intro i _; have := hs i; positivity)).mp h

/-- Pass to limits of the increasing partial products. -/
theorem weyl_infinite_shifted_products : Spec.Real.WeylInfiniteShiftedProducts.{u} := by
  intro H _ _ _ T hT ev hev r hr P hP
  apply product_limit_of_partial_products_le _ _ _ _
    (fun n => weyl_finite_shifted_products H T hT ev hev r hr n) hP
  · intro i
    exact le_add_of_nonneg_right (mul_nonneg hr (norm_nonneg _))
  · intro i
    exact le_add_of_nonneg_right (mul_nonneg hr
      ((CompactSpectral.SingularApproximation.singular_sequence_properties ℝ H H T hT).1
        (i+1) (by omega)))

end Real

end ExpandedFA.TraceIdeals.WeylSumsProducts
