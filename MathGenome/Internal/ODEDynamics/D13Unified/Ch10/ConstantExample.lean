import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.ConstantExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.Oscillation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.EvolutionMatrix
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate Matrix
namespace D13Unified.Ch10.ConstantExample
open RegularProblem
abbrev problem := Specs.D13Unified.Ch10.ConstantExample.problemValue
abbrev eigenvalue := Specs.D13Unified.Ch10.ConstantExample.eigenvalueValue
abbrev eigenfunction := Specs.D13Unified.Ch10.ConstantExample.eigenfunctionValue

lemma frequency_pos {ell : ℝ} (hell : 0 < ell) (n : ℕ) :
    0 < ((n : ℝ) + 1) * Real.pi / ell := by positivity

lemma eigenfunction_contDiff (ell : ℝ) (n : ℕ) : ContDiff ℝ ⊤ (eigenfunction ell n) := by
  unfold eigenfunction Specs.D13Unified.Ch10.ConstantExample.eigenfunctionValue
  fun_prop

lemma eigenfunction_hasDerivAt (ell : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (eigenfunction ell n)
      (Real.sqrt (2 / ell) * (((n : ℝ) + 1) * Real.pi / ell) *
        Real.cos (((n : ℝ) + 1) * Real.pi * x / ell)) x := by
  unfold eigenfunction Specs.D13Unified.Ch10.ConstantExample.eigenfunctionValue
  convert (((hasDerivAt_id x).const_mul (((n : ℝ) + 1) * Real.pi)).div_const ell).sin.const_mul
    (Real.sqrt (2 / ell)) using 1 <;> simp only [id_eq, mul_one] <;> ring

lemma eigenfunction_deriv (ell : ℝ) (n : ℕ) :
    deriv (eigenfunction ell n) = fun x => Real.sqrt (2 / ell) *
      (((n : ℝ) + 1) * Real.pi / ell) * Real.cos (((n : ℝ) + 1) * Real.pi * x / ell) := by
  funext x
  exact (eigenfunction_hasDerivAt ell n x).deriv

lemma eigenfunction_second (ell : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (deriv (eigenfunction ell n))
      (-eigenvalue ell n * eigenfunction ell n x) x := by
  rw [eigenfunction_deriv]
  convert (((hasDerivAt_id x).const_mul (((n : ℝ) + 1) * Real.pi)).div_const ell).cos.const_mul
    (Real.sqrt (2 / ell) * (((n : ℝ) + 1) * Real.pi / ell)) using 1 <;>
    simp only [id_eq, mul_one] <;>
    simp only [eigenvalue, eigenfunction,
      Specs.D13Unified.Ch10.ConstantExample.eigenvalueValue,
      Specs.D13Unified.Ch10.ConstantExample.eigenfunctionValue] <;> ring

theorem endpoints : Specs.D13Unified.Ch10.ConstantExample.Endpoints := by
  intro ell hell n
  constructor
  · simp [eigenfunction, Specs.D13Unified.Ch10.ConstantExample.eigenfunctionValue]
  · have harg : ((n : ℝ) + 1) * Real.pi * ell / ell = (n + 1 : ℕ) * Real.pi := by
      push_cast
      field_simp [ne_of_gt hell]
    change Real.sqrt (2 / ell) * Real.sin (((n : ℝ) + 1) * Real.pi * ell / ell) = 0
    rw [harg, Real.sin_nat_mul_pi, mul_zero]

lemma eigenfunction_nonzero {ell : ℝ} (hell : 0 < ell) (n : ℕ) :
    ∃ x ∈ Icc 0 ell, eigenfunction ell n x ≠ 0 := by
  let x := ell / (2 * ((n : ℝ) + 1))
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hx : x ∈ Icc 0 ell := by
    dsimp [x]
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 2 * ((n : ℝ) + 1))).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨x, hx, ?_⟩
  have harg : ((n : ℝ) + 1) * Real.pi * x / ell = Real.pi / 2 := by
    dsimp [x]
    field_simp [ne_of_gt hell, ne_of_gt hn]
    <;> ring
  simp only [eigenfunction, Specs.D13Unified.Ch10.ConstantExample.eigenfunctionValue,
    harg, Real.sin_pi_div_two, mul_one]
  exact ne_of_gt (Real.sqrt_pos.2 (div_pos (by norm_num) hell))

theorem classical_modes : Specs.D13Unified.Ch10.ConstantExample.ClassicalModes := by
  intro ell hell n
  let P := problem ell hell
  let y : ℝ → ℂ := fun x => (eigenfunction ell n x : ℂ)
  let dy : ℝ → ℂ := fun x => ((deriv (eigenfunction ell n) x : ℝ) : ℂ)
  have hfirst (x : ℝ) : HasDerivAt y (dy x) x :=
    by simpa only [y, dy, (eigenfunction_hasDerivAt ell n x).deriv] using
      (eigenfunction_hasDerivAt ell n x).ofReal_comp
  have hsecond (x : ℝ) : HasDerivAt dy
      ((-eigenvalue ell n * eigenfunction ell n x : ℝ) : ℂ) x :=
    (eigenfunction_second ell n x).ofReal_comp
  have hdiff : UniqueDiffOn ℝ (interval P) := uniqueDiffOn_Icc hell
  have hd : EqOn (derivative P y) dy (interval P) := by
    intro x hx
    exact (hfirst x).hasDerivWithinAt.derivWithin (hdiff x hx)
  refine ⟨(Complex.ofRealCLM.contDiff.comp (eigenfunction_contDiff ell n)).of_le
    (by norm_num) |>.contDiffOn, ?_, ?_, ?_⟩
  · obtain ⟨x, hx, hn⟩ := eigenfunction_nonzero hell n
    exact ⟨x, hx, Complex.ofReal_ne_zero.mpr hn⟩
  · apply (dirichlet_boundary P y).mpr
    constructor
    · change (eigenfunction ell n 0 : ℂ) = 0
      exact Complex.ofReal_eq_zero.mpr (endpoints ell hell n).1
    · change (eigenfunction ell n ell : ℂ) = 0
      exact Complex.ofReal_eq_zero.mpr (endpoints ell hell n).2
  · intro x hx
    have hf : HasDerivWithinAt (fun t => (P.p t : ℂ) * derivative P y t)
        ((-eigenvalue ell n * eigenfunction ell n x : ℝ) : ℂ) (interval P) x := by
      apply (hsecond x).hasDerivWithinAt.congr_of_mem _ hx
      intro t ht
      change (1 : ℂ) * derivative P y t = dy t
      rw [one_mul, hd ht]
    change -derivWithin (fun t => (P.p t : ℂ) * derivative P y t) (interval P) x +
      (0 : ℂ) * y x = _
    rw [hf.derivWithin (hdiff x hx)]
    change -((-eigenvalue ell n * eigenfunction ell n x : ℝ) : ℂ) +
      (0 : ℂ) * (eigenfunction ell n x : ℂ) =
      (eigenvalue ell n : ℂ) * (1 : ℂ) * (eigenfunction ell n x : ℂ)
    push_cast
    ring

/-- The zero set is the finite grid k ell/(n+1), 1 ≤ k ≤ n. -/
lemma zero_set {ell : ℝ} (hell : 0 < ell) (n : ℕ) :
    {x ∈ Ioo 0 ell | eigenfunction ell n x = 0} =
      range (fun i : Fin n => ((i.val : ℝ) + 1) * ell / ((n : ℝ) + 1)) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hs : Real.sqrt (2 / ell) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  ext x
  constructor
  · rintro ⟨hx, hz⟩
    have hsin : Real.sin (((n : ℝ) + 1) * Real.pi * x / ell) = 0 :=
      (mul_eq_zero.mp hz).resolve_left hs
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
    have hfreq := frequency_pos hell n
    have hpos : (0 : ℝ) < k := by
      have harg : 0 < ((n : ℝ) + 1) * Real.pi * x / ell := div_pos (mul_pos (mul_pos hn Real.pi_pos) hx.1) hell
      rw [← hk] at harg
      exact (mul_pos_iff_of_pos_right Real.pi_pos).mp harg
    have hlt : (k : ℝ) < (n : ℝ) + 1 := by
      have harg : ((n : ℝ) + 1) * Real.pi * x / ell < ((n : ℝ) + 1) * Real.pi := by
        apply (div_lt_iff₀ hell).mpr
        exact mul_lt_mul_of_pos_left hx.2 (by positivity)
      rw [← hk] at harg
      exact (mul_lt_mul_iff_left₀ Real.pi_pos).mp harg
    have hk0 : (0 : ℤ) ≤ k := le_of_lt (by exact_mod_cast hpos : (0 : ℤ) < k)
    lift k to ℕ using hk0 with m
    have hm0 : 0 < m := by exact_mod_cast hpos
    have hmn : m < n + 1 := by exact_mod_cast hlt
    let i : Fin n := ⟨m - 1, by omega⟩
    refine ⟨i, ?_⟩
    have hi : i.val + 1 = m := Nat.sub_add_cancel hm0
    have hie : (i.val : ℝ) + 1 = m := by exact_mod_cast hi
    change ((i.val : ℝ) + 1) * ell / ((n : ℝ) + 1) = x
    rw [hie]
    have hk' : (m : ℝ) * Real.pi = ((n : ℝ) + 1) * Real.pi * x / ell := by
      simpa using hk
    apply (div_eq_iff (ne_of_gt hn)).mpr
    have := (eq_div_iff (ne_of_gt hell)).mp hk'
    nlinarith [Real.pi_pos]
  · rintro ⟨i, rfl⟩
    have hi0 : 0 < (i.val : ℝ) + 1 := by positivity
    have hin : (i.val : ℝ) + 1 < (n : ℝ) + 1 := by exact_mod_cast Nat.add_lt_add_right i.isLt 1
    refine ⟨⟨by positivity, ?_⟩, ?_⟩
    · apply (div_lt_iff₀ hn).mpr
      nlinarith
    · have harg : ((n : ℝ) + 1) * Real.pi *
          (((i.val : ℝ) + 1) * ell / ((n : ℝ) + 1)) / ell = (i.val + 1 : ℕ) * Real.pi := by
        push_cast
        field_simp [ne_of_gt hell, ne_of_gt hn]
        <;> ring
      change Real.sqrt (2 / ell) * Real.sin _ = 0
      rw [harg, Real.sin_nat_mul_pi, mul_zero]

theorem zeros : Specs.D13Unified.Ch10.ConstantExample.Zeros := by
  intro ell hell n
  rw [zero_set hell n]
  have hi : Function.Injective (fun i : Fin n => ((i.val : ℝ) + 1) * ell / ((n : ℝ) + 1)) := by
    intro i j he
    have h := (div_left_inj' (by positivity : (n : ℝ) + 1 ≠ 0)).mp he
    have h' := mul_right_cancel₀ (ne_of_gt hell) h
    apply Fin.ext
    exact_mod_cast (add_right_cancel h')
  exact ⟨finite_range _, by simpa using ncard_range_of_injective hi⟩

/-- The zero count fixes the index in any increasing exhaustive sequence. -/
lemma sequence_eq {ell : ℝ} (hell : 0 < ell) (lam : ℕ → ℝ)
    (hs : Specs.D13Unified.Ch10.Oscillation.IsDirichletSequence (problem ell hell) lam) :
    lam = eigenvalue ell := by
  funext n
  obtain ⟨i, hi⟩ := hs.2.2.2 (eigenvalue ell n)
    ⟨eigenfunction ell n, classical_modes ell hell n⟩
  have hc : Specs.D13Unified.Ch10.Oscillation.RealDirichletEigenfunction
      (problem ell hell) (lam ((i + 1) - 1)) (eigenfunction ell n) := by
    rw [Nat.add_sub_cancel, ← hi]
    exact classical_modes ell hell n
  have hz := Oscillation.oscillation_count (problem ell hell) lam hs (i + 1)
    (by omega) (eigenfunction ell n) hc
  have hni : n = i := by
    have h := (zeros ell hell n).2.symm.trans hz.2
    simpa using h
  subst i
  exact hi.symm

lemma sequence_of_expansion (P : Problem) (lam : ℕ → ℝ)
    (hm : StrictMono lam) (ht : Tendsto lam atTop atTop)
    (phi : ℕ → ℝ → ℝ)
    (he : ∀ n, IsClassicalEigenfunction P dirichlet (lam n : ℂ) (fun x => (phi n x : ℂ)))
    (hall : ∀ (z : ℂ) (y : ℝ → ℂ), IsClassicalEigenfunction P dirichlet z y →
      ∃ n, z = (lam n : ℂ)) :
    Specs.D13Unified.Ch10.Oscillation.IsDirichletSequence P lam := by
  refine ⟨hm, ht, fun n => ⟨phi n, he n⟩, ?_⟩
  rintro mu ⟨y, hy⟩
  obtain ⟨n, hn⟩ := hall (mu : ℂ) (fun x => (y x : ℂ)) hy
  exact ⟨n, Complex.ofReal_injective hn⟩

theorem discrete_sequence : Specs.D13Unified.Ch10.ConstantExample.DiscreteSequence := by
  intro ell hell
  obtain ⟨lam, hs⟩ := Oscillation.sequence_exists (problem ell hell)
  rw [sequence_eq hell lam hs] at hs
  exact ⟨hs.1, hs.2.1⟩

theorem all_eigenvalues : Specs.D13Unified.Ch10.ConstantExample.AllEigenvalues := by
  intro ell hell z
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨lam, phi, hphi, B, hm, ht, he, hB, hall, hspan, hsum⟩ :=
      Spectrum.spectrum (problem ell hell)
    have hs := sequence_of_expansion _ lam hm ht phi he hall
    obtain ⟨n, hn⟩ := hall z y hy
    exact ⟨n, by simpa only [sequence_eq hell lam hs] using hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, classical_modes ell hell n⟩

lemma integral_square {ell : ℝ} (hell : 0 < ell) (n : ℕ) :
    ∫ x in 0..ell, eigenfunction ell n x ^ 2 = 1 := by
  let k := ((n : ℝ) + 1) * Real.pi / ell
  have hk : k ≠ 0 := ne_of_gt (frequency_pos hell n)
  have harg (x : ℝ) : ((n : ℝ) + 1) * Real.pi * x / ell = k * x := by dsimp [k]; ring
  have hbound : k * ell = (n + 1 : ℕ) * Real.pi := by
    dsimp [k]
    push_cast
    field_simp [ne_of_gt hell]
  simp only [eigenfunction, Specs.D13Unified.Ch10.ConstantExample.eigenfunctionValue,
    harg, mul_pow]
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2 / ell), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hk,
    mul_zero, hbound, integral_sin_sq, Real.sin_zero, Real.sin_nat_mul_pi]
  simp only [zero_mul, sub_zero, zero_add, smul_eq_mul]
  dsimp [k]
  push_cast
  field_simp [ne_of_gt hell]
  <;> ring

lemma mode_memLp (ell : ℝ) (hell : 0 < ell) (n : ℕ) :
    MemLp (fun x => (eigenfunction ell n x : ℂ)) 2 (weightedMeasure (problem ell hell)) :=
  continuous_memLp _ _ (classical_modes ell hell n).1.continuousOn

lemma mode_norm (ell : ℝ) (hell : 0 < ell) (n : ℕ) :
    ‖toHilbert (problem ell hell) (fun x => (eigenfunction ell n x : ℂ))
      (mode_memLp ell hell n)‖ = 1 := by
  let P := problem ell hell
  let v := toHilbert P (fun x => (eigenfunction ell n x : ℂ)) (mode_memLp ell hell n)
  have hinner : paperInner P v v = (1 : ℂ) := by
    rw [inner_representatives]
    change (∫ x in Icc 0 ell, (eigenfunction ell n x : ℂ) *
      conj (eigenfunction ell n x : ℂ) * (1 : ℂ)) = 1
    simp only [Complex.conj_ofReal, mul_one, ← Complex.ofReal_mul, ← sq, ← Complex.ofReal_pow]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hell.le,
      intervalIntegral.integral_ofReal, integral_square hell n]
    rfl
  have hs : ‖v‖ ^ 2 = 1 := by
    have h := (inner_norm P v).symm.trans hinner
    exact_mod_cast h
  have hn : 0 ≤ ‖v‖ := norm_nonneg v
  change ‖v‖ = 1
  nlinarith

theorem complete_orthonormal : Specs.D13Unified.Ch10.ConstantExample.CompleteOrthonormal := by
  classical
  intro ell hell
  let P := problem ell hell
  let hm := mode_memLp ell hell
  let v : ℕ → Hilbert P := fun n => toHilbert P (fun x => (eigenfunction ell n x : ℂ)) (hm n)
  obtain ⟨lam, phi, hphi, B, hmono, ht, he, hB, hall, hspan, hsum⟩ := Spectrum.spectrum P
  have hseq := sequence_of_expansion P lam hmono ht phi he hall
  have hlam : lam = eigenvalue ell := sequence_eq hell lam hseq
  have hv : Orthonormal ℂ v := by
    refine ⟨mode_norm ell hell, ?_⟩
    intro i j hij
    change paperInner P (v j) (v i) = 0
    apply Lagrange.eigenfunctions_orthogonal P dirichlet
      (eigenvalue ell j : ℂ) (eigenvalue ell i : ℂ)
      (fun x => (eigenfunction ell j x : ℂ)) (fun x => (eigenfunction ell i x : ℂ))
      (classical_modes ell hell j) (classical_modes ell hell i) _ (hm j) (hm i)
    intro heq
    exact hij ((discrete_sequence ell hell).1.injective (Complex.ofReal_injective heq)).symm
  have hle : Submodule.span ℂ (range B) ≤ Submodule.span ℂ (range v) := by
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    have hmem : v n ∈ (ℂ ∙ B n : Submodule ℂ (Hilbert P)) := by
      have hc : v n ∈ Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge.classicalEigenspace P (lam n : ℂ) := by
        right
        refine ⟨_, hm n, ?_, rfl⟩
        rw [hlam]
        exact classical_modes ell hell n
      rw [(hspan n).1] at hc
      exact hc
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c ≠ 0 := by
      intro hc0
      have hz : v n = 0 := by simpa [hc0] using hc.symm
      have hnorm := mode_norm ell hell n
      change ‖v n‖ = 1 at hnorm
      rw [hz, norm_zero] at hnorm
      exact zero_ne_one hnorm
    apply (Submodule.smul_mem_iff _ hc0).mp
    rw [hc]
    exact Submodule.subset_span ⟨n, rfl⟩
  have hd : (Submodule.span ℂ (range v)).topologicalClosure = ⊤ := by
    apply top_unique
    rw [← B.dense_span]
    exact Submodule.topologicalClosure_mono hle
  let C := HilbertBasis.mk hv hd.ge
  refine ⟨hm, C, ?_, Spectrum.hilbert_sums P C⟩
  intro n
  exact congrFun (HilbertBasis.coe_mk hv hd.ge) n

/-- First-order reconstruction covers positive, zero and negative parameters
uniformly and provides a global classical scalar solution. -/
theorem initial_value : Specs.D13Unified.Ch10.ConstantExample.InitialValue := by
  intro lam s A B
  let I : TimeInterval := ⟨univ, ⟨s, mem_univ s⟩, ordConnected_univ⟩
  let M : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun _ => !![0, 1; -lam, 0]
  obtain ⟨Y, hc, hi, hd, hr, hu⟩ := Ch07.LinearSystemExistence.vector_existence
    ℝ 2 I M s ![A, B] (mem_univ s) continuousOn_const
  have h0 (t : ℝ) : HasDerivAt (fun t => Y t 0) (Y t 1) t := by
    have h := hasDerivWithinAt_univ.mp (hd t (mem_univ t))
    simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using (hasDerivAt_pi.mp h 0)
  have h1 (t : ℝ) : HasDerivAt (fun t => Y t 1) (-lam * Y t 0) t := by
    have h := hasDerivWithinAt_univ.mp (hd t (mem_univ t))
    simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using (hasDerivAt_pi.mp h 1)
  have heq : deriv (fun t => Y t 0) = fun t => Y t 1 := funext fun t => (h0 t).deriv
  have hreg : ContDiff ℝ 2 (fun t => Y t 0) := by
    apply (contDiff_succ_iff_deriv (n := 1)).mpr
    refine ⟨fun t => (h0 t).differentiableAt, by simp, ?_⟩
    rw [heq]
    exact contDiff_pi.mp (contDiffOn_univ.mp hr) 1
  refine ⟨fun t => Y t 0, ⟨hreg, congrFun hi 0, ?_, ?_⟩, ?_⟩
  · rw [heq]
    exact congrFun hi 1
  · intro t
    rw [heq, (h1 t).deriv]
    ring
  · rintro y ⟨hyr, hya, hyb, hye⟩
    let Z : ℝ → Fin 2 → ℝ := fun t => ![y t, deriv y t]
    have hzreg : ContDiff ℝ 1 Z := by
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact hyr.of_le (by norm_num)
      · exact (contDiff_succ_iff_deriv (n := 1)).mp hyr |>.2.2
    have hzi : Z s = ![A, B] := by simp [Z, hya, hyb]
    have hzd (t : ℝ) (_ht : t ∈ I.carrier) :
        HasDerivWithinAt Z (M t *ᵥ Z t) I.carrier t := by
      apply HasDerivAt.hasDerivWithinAt
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · simpa [Z, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
          (hyr.differentiable (by norm_num) t).hasDerivAt
      · have hsecond := (hyr.differentiable_deriv_two t).hasDerivAt
        have he : deriv (deriv y) t = -lam * y t := by linarith [hye t]
        rw [he] at hsecond
        simpa [Z, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hsecond
    have huniq := hu Z hzreg.continuous.continuousOn hzi hzd
    funext t
    exact congrFun (huniq (mem_univ t)) 0

end D13Unified.Ch10.ConstantExample
