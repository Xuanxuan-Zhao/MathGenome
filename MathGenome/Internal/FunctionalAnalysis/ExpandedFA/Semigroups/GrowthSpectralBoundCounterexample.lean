import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.GrowthSpectralBoundCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02HilbertSumComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.BoundedPerturbation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Module

/-!
The growth/spectral-bound gap from paper.tex 14627–14656. The canonical
Hilbert sum and maximal blockwise operator are fixed in the independent Specs.

The proof identifies the exact weighted domain by two pointwise estimates,
constructs the off-eigenvalue resolvent from uniformly bounded finite-block
inverses, and uses the accepted Hille–Yosida theorem for generation. Constant
vectors in blocks of increasing dimension have norm squared `n+1` and an
imaginary-eigenvalue residual of norm one. A derivative estimate for the
phase-corrected orbit then forces every semigroup operator to have norm one.
-/

noncomputable section
open scoped ENNReal NNReal

namespace ExpandedFA.Semigroups.GrowthGap

@[simp] theorem shift_apply (n : ℕ) (x : Block n) (j : Fin (n + 1)) :
    shift n x j = if h : 0 < j.val then x ⟨j.val - 1, by omega⟩ else 0 := rfl

@[simp] theorem shift_apply_zero (n : ℕ) (x : Block n) : shift n x 0 = 0 := by
  simp

@[simp] theorem shift_apply_succ (n : ℕ) (x : Block n) (j : Fin n) :
    shift n x j.succ = x j.castSucc := by
  have hj : 0 < j.succ.val := Nat.zero_lt_succ _
  rw [shift_apply, dite_eq_left hj]
  exact congrArg (fun i : Fin (n + 1) => x i) (Fin.ext (by simp))

theorem norm_shift_sq (n : ℕ) (x : Block n) :
    ‖shift n x‖ ^ 2 = ‖x‖ ^ 2 - ‖x (Fin.last n)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [shift_apply_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, shift_apply_succ, zero_add]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  ring

theorem shift_contractive : Spec.ShiftContractive := by
  intro n x
  have := norm_shift_sq n x
  nlinarith [sq_nonneg ‖x (Fin.last n)‖, norm_nonneg (shift n x), norm_nonneg x]

theorem norm_shift_le (n : ℕ) : ‖shift n‖ ≤ 1 := by
  exact (shift n).opNorm_le_bound zero_le_one (fun x => by simpa using shift_contractive n x)

@[simp] theorem blockGenerator_apply (n : ℕ) (x : Block n) :
    blockGenerator n x = eigenvalue n • x + shift n x := rfl

@[simp] theorem operator_apply (x : operator.domain) (n : ℕ) :
    operator x n = blockGenerator n (x.val n) := rfl

theorem shift_pow_apply (n k : ℕ) (x : Block n) (j : Fin (n + 1)) :
    ((shift n) ^ k) x j =
      if h : k ≤ j.val then x ⟨j.val - k, by omega⟩ else 0 := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, shift_apply]
    by_cases hj : 0 < j.val
    · rw [dite_eq_left hj, ih]
      dsimp only [Fin.val_mk]
      split_ifs with hk hk'
      · exact congrArg (fun i : Fin (n + 1) => x i) (Fin.ext (by dsimp; omega))
      · omega
      · omega
      · rfl
    · rw [dite_eq_right hj, dite_eq_right (by omega)]

theorem shift_nilpotent : Spec.ShiftNilpotent := by
  intro n
  ext x j
  rw [shift_pow_apply, dite_eq_right (by omega)]
  rfl

theorem eigenvalue_im (n : ℕ) : (eigenvalue n).im = (n + 1 : ℕ) := by
  simp [eigenvalue]

theorem weight_le_norm_eigenvalue (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ≤ ‖eigenvalue n‖ := by
  calc
    _ = |(eigenvalue n).im| := by rw [eigenvalue_im, abs_of_nonneg (by positivity)]
    _ ≤ _ := Complex.abs_im_le_norm _

theorem norm_eigenvalue_le (n : ℕ) :
    ‖eigenvalue n‖ ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
  calc
    _ ≤ ‖(-1 : ℂ)‖ + ‖((n + 1 : ℕ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, Complex.norm_natCast, Complex.norm_I, norm_neg, norm_one, mul_one, add_comm]

theorem weight_norm_le (n : ℕ) (x : Block n) :
    ((n + 1 : ℕ) : ℝ) * ‖x‖ ≤ ‖blockGenerator n x‖ + ‖x‖ := by
  calc
    _ ≤ ‖eigenvalue n‖ * ‖x‖ := mul_le_mul_of_nonneg_right
      (weight_le_norm_eigenvalue n) (norm_nonneg _)
    _ = ‖eigenvalue n • x‖ := (norm_smul _ _).symm
    _ = ‖blockGenerator n x - shift n x‖ := by rw [blockGenerator_apply, add_sub_cancel_right]
    _ ≤ ‖blockGenerator n x‖ + ‖shift n x‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl (shift_contractive n x)

theorem norm_blockGenerator_le (n : ℕ) (x : Block n) :
    ‖blockGenerator n x‖ ≤ 3 * (((n + 1 : ℕ) : ℝ) * ‖x‖) := by
  have hw : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  calc
    _ ≤ ‖eigenvalue n‖ * ‖x‖ + ‖shift n x‖ := by
      simpa only [blockGenerator_apply, norm_smul] using norm_add_le (eigenvalue n • x) (shift n x)
    _ ≤ (((n + 1 : ℕ) : ℝ) + 1) * ‖x‖ + ‖x‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_eigenvalue_le n) (norm_nonneg x))
        (shift_contractive n x)
    _ ≤ _ := by nlinarith [norm_nonneg x]

theorem weighted_mem_iff (x : Space) :
    Memℓp (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖x n‖) 2 ↔ x ∈ weightedDomain := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)), mul_pow]
  rfl

theorem domain_identification : Spec.DomainIdentification := by
  ext x
  change Memℓp (fun n => blockGenerator n (x n)) 2 ↔ x ∈ weightedDomain
  rw [← weighted_mem_iff]
  constructor
  · intro hx
    apply (hx.norm.add (lp.memℓp x).norm).mono
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact weight_norm_le n (x n)
  · intro hx
    exact (hx.const_smul (3 : ℝ)).mono fun n => norm_blockGenerator_le n (x n)

/-- The finite-dimensional pencil, with the same resolvent sign as the source. -/
def blockPencil (ζ : ℂ) (n : ℕ) : Block n →L[ℂ] Block n :=
  ζ • ContinuousLinearMap.id ℂ (Block n) - blockGenerator n

theorem blockPencil_eq (ζ : ℂ) (n : ℕ) :
    blockPencil ζ n = (ζ - eigenvalue n) • (1 : Block n →L[ℂ] Block n) - shift n := by
  ext x j
  change ζ * x j - (eigenvalue n * x j + shift n x j) =
    (ζ - eigenvalue n) * x j - shift n x j
  ring

theorem blockPencil_isUnit (ζ : ℂ) (n : ℕ) (hζ : ζ ≠ eigenvalue n) :
    IsUnit (blockPencil ζ n) := by
  have hc : ζ - eigenvalue n ≠ 0 := sub_ne_zero.mpr hζ
  have hs : IsNilpotent (shift n) := ⟨n + 1, shift_nilpotent n⟩
  have h₁ : IsUnit ((ζ - eigenvalue n) • (1 : Block n →L[ℂ] Block n)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ (Block n →L[ℂ] Block n))
  have hcomm : Commute (-shift n) ((ζ - eigenvalue n) • (1 : Block n →L[ℂ] Block n)) := by
    change (-shift n) * ((ζ - eigenvalue n) • 1) = ((ζ - eigenvalue n) • 1) * (-shift n)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (Algebra.commutes (ζ - eigenvalue n) (-shift n)).symm
  simpa only [blockPencil_eq, sub_eq_add_neg] using
    hs.neg.isUnit_add_left_of_commute h₁ hcomm

/-- Only an actual finite-block invertibility theorem is used to choose this map. -/
def blockInverse (ζ : ℂ) (n : ℕ) (hζ : ζ ≠ eigenvalue n) : Block n →L[ℂ] Block n :=
  ↑((blockPencil_isUnit ζ n hζ).unit⁻¹)

theorem blockInverse_right (ζ : ℂ) (n : ℕ) (hζ : ζ ≠ eigenvalue n) (x : Block n) :
    blockPencil ζ n (blockInverse ζ n hζ x) = x := by
  have h := (blockPencil_isUnit ζ n hζ).unit.mul_inv
  have hh : blockPencil ζ n * blockInverse ζ n hζ = 1 := by
    simpa only [blockInverse, IsUnit.unit_spec] using h
  exact congrArg (fun f : Block n →L[ℂ] Block n => f x) hh

theorem blockInverse_left (ζ : ℂ) (n : ℕ) (hζ : ζ ≠ eigenvalue n) (x : Block n) :
    blockInverse ζ n hζ (blockPencil ζ n x) = x := by
  have h := (blockPencil_isUnit ζ n hζ).unit.inv_mul
  have hh : blockInverse ζ n hζ * blockPencil ζ n = 1 := by
    simpa only [blockInverse, IsUnit.unit_spec] using h
  exact congrArg (fun f : Block n →L[ℂ] Block n => f x) hh

theorem blockPencil_lower (ζ : ℂ) (n : ℕ) (x : Block n) :
    ‖ζ - eigenvalue n‖ * ‖x‖ ≤ ‖blockPencil ζ n x‖ + ‖x‖ := by
  calc
    _ = ‖(ζ - eigenvalue n) • x‖ := (norm_smul _ _).symm
    _ = ‖blockPencil ζ n x + shift n x‖ := by
      rw [blockPencil_eq]
      simp
    _ ≤ ‖blockPencil ζ n x‖ + ‖shift n x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (shift_contractive n x)

theorem norm_blockInverse_le_one (ζ : ℂ) (n : ℕ) (hζ : ζ ≠ eigenvalue n)
    (hn : 2 ≤ ‖ζ - eigenvalue n‖) : ‖blockInverse ζ n hζ‖ ≤ 1 := by
  apply (blockInverse ζ n hζ).opNorm_le_bound zero_le_one
  intro x
  have h := blockPencil_lower ζ n (blockInverse ζ n hζ x)
  rw [blockInverse_right] at h
  nlinarith [norm_nonneg (blockInverse ζ n hζ x)]

/-- Finitely many exceptional blocks are allowed; the tail inverses are contractions. -/
theorem blockInverse_uniform_bound (ζ : ℂ) (hζ : ∀ n, ζ ≠ eigenvalue n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖blockInverse ζ n (hζ n)‖ ≤ C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (ζ.im + 2)
  have he : ∀ᶠ n : ℕ in Filter.atTop, ‖blockInverse ζ n (hζ n)‖ ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    apply norm_blockInverse_le_one
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hi := Complex.abs_im_le_norm (ζ - eigenvalue n)
    have hneg := neg_le_abs (ζ - eigenvalue n).im
    rw [Complex.sub_im, eigenvalue_im] at hi hneg
    push_cast at hi hneg
    linarith
  obtain ⟨C, hC⟩ := (Filter.isBoundedUnder_of_eventually_le he).bddAbove_range
  exact ⟨max C 0, le_max_right _ _, fun n => (hC ⟨n, rfl⟩).trans (le_max_left _ _)⟩

/-- A uniformly bounded family acts on the canonical square-summable sum. -/
def diagonalLinear (F : ∀ n, Block n →L[ℂ] Block n) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, ‖F n‖ ≤ C) : Space →ₗ[ℂ] Space where
  toFun x := ⟨fun n => F n (x n),
    ((lp.memℓp x).norm.const_smul C).mono fun n =>
      (F n).le_opNorm (x n) |>.trans (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg _))⟩
  map_add' x y := by apply lp.ext; funext n; exact (F n).map_add (x n) (y n)
  map_smul' c x := by apply lp.ext; funext n; exact (F n).map_smul c (x n)

theorem norm_diagonalLinear_le (F : ∀ n, Block n →L[ℂ] Block n) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, ‖F n‖ ≤ C) (x : Space) : ‖diagonalLinear F C hC hF x‖ ≤ C * ‖x‖ := by
  calc
    _ ≤ ‖C • lp.toNorm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖F n (x n)‖ ≤ ‖C * ‖x n‖‖
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
      exact (F n).le_opNorm (x n) |>.trans
        (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg _))
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, lp.norm_toNorm]

def diagonalMap (F : ∀ n, Block n →L[ℂ] Block n) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, ‖F n‖ ≤ C) : Space →L[ℂ] Space :=
  (diagonalLinear F C hC hF).mkContinuous C (norm_diagonalLinear_le F C hC hF)

@[simp] theorem diagonalMap_apply (F : ∀ n, Block n →L[ℂ] Block n) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, ‖F n‖ ≤ C) (x : Space) (n : ℕ) :
    diagonalMap F C hC hF x n = F n (x n) := rfl

/-- The bounded direct sum of inverses lands in the maximal domain, since
`A_n R_n y_n = ζ R_n y_n - y_n`. The weighted-domain theorem then applies. -/
def resolventInverse (ζ : ℂ) (hζ : ∀ n, ζ ≠ eigenvalue n) :
    Unbounded.ResolventInverse operator ζ := by
  let C := (blockInverse_uniform_bound ζ hζ).choose
  have hC : 0 ≤ C := (blockInverse_uniform_bound ζ hζ).choose_spec.1
  have hF : ∀ n, ‖blockInverse ζ n (hζ n)‖ ≤ C :=
    (blockInverse_uniform_bound ζ hζ).choose_spec.2
  let R := diagonalMap (fun n => blockInverse ζ n (hζ n)) C hC hF
  have hright (y : Space) (n : ℕ) :
      ζ • R y n - blockGenerator n (R y n) = y n :=
    blockInverse_right ζ n (hζ n) (y n)
  have hmem (y : Space) : R y ∈ operator.domain := by
    change Memℓp (fun n => blockGenerator n (R y n)) 2
    convert ((lp.memℓp (R y)).const_smul ζ).sub (lp.memℓp y) using 1
    funext n
    change blockGenerator n (R y n) = ζ • R y n - y n
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp (hright y n)).symm
  refine ⟨R, hmem, ?_, ?_⟩
  · intro y
    apply lp.ext
    funext n
    exact hright y n
  · intro x
    apply lp.ext
    funext n
    exact blockInverse_left ζ n (hζ n) (x.val n)

theorem single_mem_domain (n : ℕ) (x : Block n) : lp.single 2 n x ∈ operator.domain := by
  change Memℓp (fun m => blockGenerator m (lp.single 2 n x m)) 2
  convert lp.memℓp (lp.single 2 n (blockGenerator n x)) using 1
  funext m
  by_cases hm : m = n
  · subst m
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne 2 n x hm, map_zero,
      lp.single_apply_ne 2 n (blockGenerator n x) hm]

/-- The last coordinate of a forward shift is an eigenvector for eigenvalue zero. -/
def lastVector (n : ℕ) : Block n := PiLp.single 2 (Fin.last n) (1 : ℂ)

@[simp] theorem shift_lastVector (n : ℕ) : shift n (lastVector n) = 0 := by
  ext j
  rw [shift_apply]
  split_ifs with hj
  · change (show Block n from PiLp.single 2 (Fin.last n) (1 : ℂ)) ⟨j.val - 1, by omega⟩ = 0
    apply PiLp.single_eq_of_ne
    intro h
    have hh := congrArg Fin.val h
    dsimp at hh
    omega
  · rfl

@[simp] theorem lastVector_last (n : ℕ) : lastVector n (Fin.last n) = 1 := by
  simp [lastVector]

instance spaceNontrivial : Nontrivial Space := by
  apply nontrivial_of_ne (lp.single 2 0 (lastVector 0) : Space) 0
  intro h
  have hh := congrArg (fun x : Space => x 0 (Fin.last 0)) h
  change (1 : ℂ) = 0 at hh
  exact one_ne_zero hh

theorem eigenvalue_mem_spectrum (n : ℕ) : eigenvalue n ∈ C0SemigroupSpec.spectrumValue operator := by
  rintro ⟨R⟩
  let v : operator.domain := ⟨lp.single 2 n (lastVector n), single_mem_domain n _⟩
  have hv : eigenvalue n • (v : Space) - operator v = 0 := by
    apply lp.ext
    funext m
    change eigenvalue n • (lp.single 2 n (lastVector n) m) -
      blockGenerator m (lp.single 2 n (lastVector n) m) = 0
    by_cases hm : m = n
    · subst m
      simp only [lp.single_apply_self, blockGenerator_apply, shift_lastVector, add_zero, sub_self]
    · rw [lp.single_apply_ne 2 n (lastVector n) hm, smul_zero, map_zero, sub_self]
  have h := R.left_inverse v
  rw [hv, map_zero] at h
  have hh := congrArg (fun x : Space => x n (Fin.last n)) h
  simpa [v] using hh

theorem spectrum_identification : Spec.SpectrumIdentification := by
  ext ζ
  constructor
  · intro hζ
    by_contra hnot
    have hall : ∀ n, ζ ≠ eigenvalue n := fun n heq => hnot ⟨n, heq.symm⟩
    exact hζ ⟨resolventInverse ζ hall⟩
  · rintro ⟨n, rfl⟩
    exact eigenvalue_mem_spectrum n

theorem spectral_bound : Spec.SpectralBound := by
  change sSup {a : EReal | ∃ ζ ∈ C0SemigroupSpec.spectrumValue operator,
    (Complex.re ζ : EReal) = a} = (-1 : EReal)
  have hset : {a : EReal | ∃ ζ ∈ C0SemigroupSpec.spectrumValue operator,
      (Complex.re ζ : EReal) = a} = {(-1 : EReal)} := by
    ext a
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      rw [spectrum_identification] at hζ
      obtain ⟨n, rfl⟩ := hζ
      simp [eigenvalue]
    · intro ha
      have ha' : a = (-1 : EReal) := ha
      subst a
      refine ⟨eigenvalue 0, eigenvalue_mem_spectrum 0, ?_⟩
      simp [eigenvalue]
  rw [hset]
  simp

/-- The blockwise maximal operator has a closed graph. -/
theorem operator_closed : operator.IsClosed := by
  change IsClosed (operator.graph : Set (Space × Space))
  have hgraph : (operator.graph : Set (Space × Space)) =
      {p | ∀ n, p.2 n = blockGenerator n (p.1 n)} := by
    ext p
    constructor
    · intro hp n
      obtain ⟨x, hx, hxy⟩ := (LinearPMap.mem_graph_iff operator).mp hp
      rw [← hx]
      exact (congrArg (fun y : Space => y n) hxy).symm
    · intro hp
      have hx : p.1 ∈ operator.domain := by
        change Memℓp (fun n => blockGenerator n (p.1 n)) 2
        convert lp.memℓp p.2 using 1
        funext n
        exact (hp n).symm
      apply (LinearPMap.mem_graph_iff operator).mpr
      refine ⟨⟨p.1, hx⟩, rfl, ?_⟩
      apply lp.ext
      funext n
      exact (hp n).symm
  rw [hgraph]
  have heq : {p : Space × Space | ∀ n, p.2 n = blockGenerator n (p.1 n)} =
      ⋂ n : ℕ, {p : Space × Space | p.2 n = blockGenerator n (p.1 n)} := by ext; simp
  rw [heq]
  apply isClosed_iInter
  intro n
  exact isClosed_eq ((lp.evalCLM ℂ Block 2 n).continuous.comp continuous_snd)
    ((blockGenerator n).continuous.comp ((lp.evalCLM ℂ Block 2 n).continuous.comp continuous_fst))

theorem finiteSupport_mem_domain {x : Space}
    (hx : x ∈ P1.C02HilbertSum.Spec.finiteSupport Block) : x ∈ operator.domain := by
  change Set.Finite {n | x n ≠ 0} at hx
  change Memℓp (fun n => blockGenerator n (x n)) 2
  apply (memℓp_zero ?_).of_exponent_ge (by norm_num)
  exact hx.subset fun n hn hzero => hn (by rw [hzero, map_zero])

theorem operator_dense : Dense (operator.domain : Set Space) := by
  exact (P1.HilbertSumSupportDensity.dense_finiteSupport Block).mono
    (fun _ hx => finiteSupport_mem_domain hx)

theorem real_ne_eigenvalue (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (r : ℂ) ≠ eigenvalue n := by
  intro h
  have := congrArg Complex.re h
  simp [eigenvalue] at this
  linarith

theorem real_blockPencil_lower (r : ℝ) (hr : 0 < r) (n : ℕ) (x : Block n) :
    r * ‖x‖ ≤ ‖blockPencil (r : ℂ) n x‖ := by
  have h := blockPencil_lower (r : ℂ) n x
  have hre : r + 1 ≤ ‖(r : ℂ) - eigenvalue n‖ := by
    have := Complex.re_le_norm ((r : ℂ) - eigenvalue n)
    simpa [eigenvalue, sub_neg_eq_add] using this
  nlinarith [norm_nonneg x]

/-- A resolvent estimate on the positive real axis, without any assumed
generation theorem or power estimates. -/
theorem real_resolvent_norm_le (r : ℝ) (hr : 0 < r)
    (R : Unbounded.ResolventInverse operator (r : ℂ)) : ‖R.inverse‖ ≤ r⁻¹ := by
  have hpoint (x : Space) (n : ℕ) : ‖R.inverse x n‖ ≤ r⁻¹ * ‖x n‖ := by
    have h := real_blockPencil_lower r hr n (R.inverse x n)
    have hR := congrArg (fun y : Space => y n) (R.right_inverse x)
    change blockPencil (r : ℂ) n (R.inverse x n) = x n at hR
    rw [hR] at h
    have hdiv : ‖R.inverse x n‖ ≤ ‖x n‖ / r :=
      (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using h)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  apply R.inverse.opNorm_le_bound (inv_nonneg.mpr hr.le)
  intro x
  calc
    _ ≤ ‖r⁻¹ • lp.toNorm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖R.inverse x n‖ ≤ ‖r⁻¹ * ‖x n‖‖
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpoint x n
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), lp.norm_toNorm]

theorem hilleYosida_estimates : HilleYosidaSpec.ResolventEstimates operator 1 0 := by
  have hrho (r : ℝ) (hr : 0 < r) :
      Nonempty (Unbounded.ResolventInverse operator (algebraMap ℝ ℂ r)) :=
    ⟨resolventInverse (r : ℂ) (real_ne_eigenvalue r hr)⟩
  refine ⟨fun r hr => hrho r hr, ?_⟩
  intro r hr n
  have hnorm : ‖Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ ℂ r) operator‖ ≤ r⁻¹ := by
    rw [Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left (hrho r hr)]
    exact real_resolvent_norm_le r hr _
  calc
    _ ≤ ‖Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ ℂ r) operator‖ ^ (n + 1) :=
      norm_pow_le _ _
    _ ≤ (r⁻¹) ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) hnorm _
    _ = _ := by simp [inv_pow]

/-- Generation on the exact weighted domain, with the contraction constants. -/
theorem exists_contraction_semigroup :
    ∃ T : C0Semigroup ℂ Space,
      C0SemigroupSpec.generatesValue operator T ∧
      C0SemigroupSpec.exponentialBoundValue T 1 0 := by
  obtain ⟨T, hT, hb⟩ := HilleYosida.sufficient operator 1 0 (by norm_num)
    operator_dense operator_closed hilleYosida_estimates
  exact ⟨T, hT.symm, hb⟩

/-- Multiplication by a pure imaginary exponential preserves norms. -/
def phase (ω s : ℝ) : ℂ := Complex.exp (-((ω : ℂ) * Complex.I) * (s : ℂ))

@[simp] theorem norm_phase (ω s : ℝ) : ‖phase ω s‖ = 1 := by
  simp [phase, Complex.norm_exp]

@[simp] theorem phase_zero (ω : ℝ) : phase ω 0 = 1 := by simp [phase]

theorem hasDerivAt_phase (ω s : ℝ) :
    HasDerivAt (phase ω) (phase ω s * (-((ω : ℂ) * Complex.I))) s := by
  convert! ((((hasDerivAt_id (s : ℂ)).const_mul (-((ω : ℂ) * Complex.I))).cexp).comp_ofReal) using 1
  simp [phase]

/-- The elementary approximate-imaginary-eigenvector estimate for a contraction
semigroup. Only an actual generator vector is used; no spectral assumption is made. -/
theorem norm_le_orbit_add_defect (T : C0Semigroup ℂ Space)
    (hb : C0SemigroupSpec.exponentialBoundValue T 1 0)
    (x : (generator T).domain) (ω : ℝ) (t : ℝ≥0) :
    ‖(x : Space)‖ ≤ ‖T.operators t x‖ +
      (t : ℝ) * ‖generator T x - ((ω : ℂ) * Complex.I) • (x : Space)‖ := by
  letI : NormedSpace ℝ Space := NormedSpace.restrictScalars ℝ ℂ Space
  letI : IsScalarTower ℝ ℂ Space := IsScalarTower.restrictScalars ℝ ℂ Space
  let d : Space := generator T x - ((ω : ℂ) * Complex.I) • (x : Space)
  let f : ℝ → Space := fun s => phase ω s • T.operators s.toNNReal x
  let f' : ℝ → Space := fun s => phase ω s • T.operators s.toNNReal d
  have hT (s : ℝ≥0) : ‖T.operators s‖ ≤ 1 := by simpa using hb.2 s
  have hd (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      HasDerivWithinAt f (f' s) (Set.Icc 0 (t : ℝ)) s := by
    have h := (hasDerivAt_phase ω s).hasDerivWithinAt.smul
      ((T.hasDerivWithinAt_orbit x s hs.1).mono
        (fun u (hu : u ∈ Set.Icc 0 (t : ℝ)) => hu.1))
    convert! h using 1
    dsimp [f', d]
    simp only [map_sub, map_smul]
    module
  have hbound (s : ℝ) (_hs : s ∈ Set.Ico 0 (t : ℝ)) : ‖f' s‖ ≤ ‖d‖ := by
    dsimp [f']
    rw [norm_smul, norm_phase, one_mul]
    exact ((T.operators s.toNNReal).le_opNorm d).trans
      (by simpa using mul_le_mul_of_nonneg_right (hT s.toNNReal) (norm_nonneg d))
  have hdiff := norm_image_sub_le_of_norm_deriv_le_segment' hd hbound
    (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  have hzero : f 0 = (x : Space) := by simp [f, T.at_zero]
  have hnorm : ‖f (t : ℝ)‖ = ‖T.operators t x‖ := by simp [f, norm_smul]
  rw [hzero, sub_zero] at hdiff
  calc
    _ = ‖f (t : ℝ) - (f (t : ℝ) - (x : Space))‖ := by rw [sub_sub_cancel]
    _ ≤ ‖f (t : ℝ)‖ + ‖f (t : ℝ) - (x : Space)‖ := norm_sub_le _ _
    _ ≤ ‖T.operators t x‖ + ‖d‖ * (t : ℝ) := by rw [hnorm]; exact add_le_add le_rfl hdiff
    _ = _ := by rw [mul_comm]

/-- Unnormalized constant vectors avoid an unnecessary division by a square root. -/
def flatVector (n : ℕ) : Block n := WithLp.toLp 2 (fun _ => (1 : ℂ))

theorem norm_flatVector_sq (n : ℕ) : ‖flatVector n‖ ^ 2 = (n + 1 : ℕ) := by
  simp [EuclideanSpace.norm_sq_eq, flatVector]

theorem shift_flatVector_sub (n : ℕ) :
    shift n (flatVector n) - flatVector n = -PiLp.single 2 0 (1 : ℂ) := by
  ext j
  by_cases hj : j = 0
  · subst j
    simp [flatVector]
  · have hpos : 0 < j.val := by
      by_contra h
      apply hj
      apply Fin.ext
      change j.val = 0
      omega
    simp [shift_apply, flatVector, hpos, PiLp.single_apply, hj]

theorem norm_shift_flatVector_sub (n : ℕ) :
    ‖shift n (flatVector n) - flatVector n‖ = 1 := by
  rw [shift_flatVector_sub, norm_neg, PiLp.norm_single, norm_one]

/-- The true block frequency is `i(n+1)`, and its residual on a constant
vector is precisely the single missing coordinate of the forward shift. -/
theorem blockGenerator_sub_frequency (n : ℕ) (x : Block n) :
    blockGenerator n x - (((n + 1 : ℕ) : ℂ) * Complex.I) • x = shift n x - x := by
  ext j
  change eigenvalue n * x j + shift n x j -
    (((n + 1 : ℕ) : ℂ) * Complex.I) * x j = shift n x j - x j
  simp only [eigenvalue]
  ring

def flatElement (n : ℕ) : operator.domain :=
  ⟨lp.single 2 n (flatVector n), single_mem_domain n _⟩

theorem norm_flatElement_sq (n : ℕ) : ‖(flatElement n : Space)‖ ^ 2 = (n + 1 : ℕ) := by
  change ‖lp.single 2 n (flatVector n)‖ ^ 2 = _
  rw [lp.norm_single (by norm_num), norm_flatVector_sq]

theorem norm_flatElement_defect (n : ℕ) :
    ‖operator (flatElement n) - (((n + 1 : ℕ) : ℂ) * Complex.I) • (flatElement n : Space)‖ = 1 := by
  have heq : operator (flatElement n) -
      (((n + 1 : ℕ) : ℂ) * Complex.I) • (flatElement n : Space) =
      lp.single 2 n (shift n (flatVector n) - flatVector n) := by
    apply lp.ext
    funext m
    change blockGenerator m (lp.single 2 n (flatVector n) m) -
      (((n + 1 : ℕ) : ℂ) * Complex.I) • (lp.single 2 n (flatVector n) m) = _
    by_cases hm : m = n
    · subst m
      rw [lp.single_apply_self, lp.single_apply_self, blockGenerator_sub_frequency]
    · rw [lp.single_apply_ne 2 n (flatVector n) hm, map_zero, smul_zero, sub_self,
        lp.single_apply_ne 2 n _ hm]
  rw [heq, lp.norm_single (by norm_num), norm_shift_flatVector_sub]

/-- Constant block vectors of increasing dimension force every contraction
semigroup with this exact generator to have norm one at every time. -/
theorem semigroup_norm_eq_one (T : C0Semigroup ℂ Space)
    (hg : C0SemigroupSpec.generatesValue operator T)
    (hb : C0SemigroupSpec.exponentialBoundValue T 1 0) (t : ℝ≥0) :
    ‖T.operators t‖ = 1 := by
  have hgen : generator T = operator := hg.symm
  have hle : ‖T.operators t‖ ≤ 1 := by simpa using hb.2 t
  apply le_antisymm hle
  by_contra hn
  have hgap : 0 < 1 - ‖T.operators t‖ := sub_pos.mpr (lt_of_not_ge hn)
  have hbound (n : ℕ) : ‖(flatElement n : Space)‖ ≤ (t : ℝ) / (1 - ‖T.operators t‖) := by
    let x : (generator T).domain := ⟨(flatElement n : Space), by
      rw [hgen]; exact (flatElement n).property⟩
    have h := norm_le_orbit_add_defect T hb x ((n + 1 : ℕ) : ℝ) t
    have hx : generator T x = operator (flatElement n) := by
      exact hgen.le.2 (show (x : Space) = (flatElement n : Space) from rfl)
    rw [hx] at h
    change ‖(flatElement n : Space)‖ ≤ ‖T.operators t (flatElement n)‖ +
      (t : ℝ) * ‖operator (flatElement n) -
        (((n + 1 : ℕ) : ℂ) * Complex.I) • (flatElement n : Space)‖ at h
    rw [norm_flatElement_defect, mul_one] at h
    have hop := (T.operators t).le_opNorm (flatElement n : Space)
    apply (le_div_iff₀ hgap).mpr
    nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (((t : ℝ) / (1 - ‖T.operators t‖)) ^ 2)
  have hsq := sq_le_sq₀ (norm_nonneg (flatElement n : Space))
    (div_nonneg t.coe_nonneg hgap.le) |>.mpr (hbound n)
  rw [norm_flatElement_sq] at hsq
  push_cast at hsq
  linarith

theorem exponential_rate_nonneg (T : C0Semigroup ℂ Space)
    (hnorm : ∀ t : ℝ≥0, ‖T.operators t‖ = 1) (M ω : ℝ)
    (hb : C0SemigroupSpec.exponentialBoundValue T M ω) : 0 ≤ ω := by
  by_contra hω
  have hω' : ω < 0 := lt_of_not_ge hω
  have hlim : Filter.Tendsto (fun u : ℝ => M * Real.exp (ω * u))
      Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (Filter.Tendsto.const_mul_atTop_of_neg hω' Filter.tendsto_id)).const_mul M
  have he : ∀ᶠ u : ℝ in Filter.atTop, M * Real.exp (ω * u) < 1 :=
    (tendsto_order.mp hlim).2 _ (by norm_num)
  obtain ⟨u, hu0, hu⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and he).exists
  have h := hb.2 u.toNNReal
  rw [hnorm, Real.coe_toNNReal _ hu0] at h
  linarith

theorem growthBound_eq_zero_of_norm (T : C0Semigroup ℂ Space)
    (hnorm : ∀ t : ℝ≥0, ‖T.operators t‖ = 1) :
    C0SemigroupSpec.growthBoundValue T = (0 : EReal) := by
  have hb : C0SemigroupSpec.exponentialBoundValue T 1 0 := by
    refine ⟨le_rfl, ?_⟩
    intro t
    simp [hnorm]
  change sInf {a : EReal | ∃ ω : ℝ, (ω : EReal) = a ∧
    ∃ M, C0SemigroupSpec.exponentialBoundValue T M ω} = 0
  apply le_antisymm
  · apply sInf_le
    exact ⟨0, by simp, 1, hb⟩
  · apply le_sInf
    rintro a ⟨ω, rfl, M, hM⟩
    exact_mod_cast exponential_rate_nonneg T hnorm M ω hM

theorem semigroup_conclusion : Spec.SemigroupConclusion := by
  obtain ⟨T, hg, hb⟩ := exists_contraction_semigroup
  have hn : ∀ t : ℝ≥0, ‖T.operators t‖ = 1 := semigroup_norm_eq_one T hg hb
  exact ⟨T, hg, hb, hn, growthBound_eq_zero_of_norm T hn⟩

/-- The complete counterexample, on the canonical Hilbert direct sum. -/
theorem counterexample : Spec.Counterexample :=
  ⟨domain_identification, spectrum_identification, spectral_bound, semigroup_conclusion⟩

end ExpandedFA.Semigroups.GrowthGap
