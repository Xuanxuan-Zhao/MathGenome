import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.FlipNormalForm
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.PeriodicMultipliers
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The explicit supercritical flip example, paper.tex `d13:16:flip-normal-form`. -/
noncomputable section
open Filter Module
open scoped Topology Matrix.Norms.Operator
namespace D13Unified.Ch16.FlipNormalForm
open D13Unified.Ch15.DiscreteDefinitions
open D13Unified.Ch15.PeriodicMultipliers
open D13Unified.Ch08.MatrixPowerCriteria

abbrev flip : Specs.D13Unified.Ch16.FlipNormalForm.flipType :=
  Specs.D13Unified.Ch16.FlipNormalForm.flip

lemma flip_zero (μ : ℝ) : flip μ 0 = 0 := by simp [flip, Specs.D13Unified.Ch16.FlipNormalForm.flip]

lemma flip_neg (μ x : ℝ) : flip μ (-x) = -flip μ x := by
  dsimp [flip, Specs.D13Unified.Ch16.FlipNormalForm.flip]
  ring

lemma flip_hasDerivAt (μ x : ℝ) : HasDerivAt (flip μ) (-(1 + μ) + 3 * x ^ 2) x := by
  convert ((hasDerivAt_id x).const_mul (-(1 + μ))).add ((hasDerivAt_id x).pow 3) using 1
  · funext y
    dsimp [flip, Specs.D13Unified.Ch16.FlipNormalForm.flip]
  · simp

lemma flip_contDiff (μ : ℝ) : ContDiff ℝ ⊤ (flip μ) := by
  exact (contDiff_const.mul contDiff_id).add (contDiff_id.pow 3)

/-- In real dimension one, complexification of the derivative is the scalar matrix. -/
lemma derivative_matrix {G : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt G a x) :
    complexify (LinearMap.toMatrix (Basis.singleton (Fin 1) ℝ) (Basis.singleton (Fin 1) ℝ)
      (fderiv ℝ G x).toLinearMap) = Matrix.diagonal (fun _ : Fin 1 => (a : ℂ)) := by
  ext i j
  simp [complexify, LinearMap.toMatrix_apply, Basis.singleton_apply, Basis.singleton_repr, h.deriv,
    Subsingleton.elim i j]

lemma scalar_spectral_lt {G : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt G a x) (ha : |a| < 1) :
    spectralRadius ℂ (complexify (LinearMap.toMatrix
      (Basis.singleton (Fin 1) ℝ) (Basis.singleton (Fin 1) ℝ)
      (fderiv ℝ G x).toLinearMap)) < 1 := by
  rw [derivative_matrix h]
  apply (spectralRadius_le_nnnorm (𝕜 := ℂ) _).trans_lt
  have hn : ‖Matrix.diagonal (fun _ : Fin 1 => (a : ℂ))‖ = |a| := by
    rw [Matrix.linfty_opNorm_diagonal]
    simp [pi_norm_const]
  have he : (‖Matrix.diagonal (fun _ : Fin 1 => (a : ℂ))‖₊ : ENNReal) < 1 := by
    exact_mod_cast (show ‖Matrix.diagonal (fun _ : Fin 1 => (a : ℂ))‖ < 1 by rwa [hn])
  exact he

lemma flip_sqrt {μ : ℝ} (hμ : 0 ≤ μ) : flip μ (Real.sqrt μ) = -Real.sqrt μ := by
  have hs := Real.sq_sqrt hμ
  dsimp [flip, Specs.D13Unified.Ch16.FlipNormalForm.flip]
  rw [pow_succ, hs]
  ring

lemma flip_neg_sqrt {μ : ℝ} (hμ : 0 ≤ μ) : flip μ (-Real.sqrt μ) = Real.sqrt μ := by
  rw [flip_neg, flip_sqrt hμ, neg_neg]

lemma sqrt_distinct {μ : ℝ} (hμ : 0 < μ) : Real.sqrt μ ≠ -Real.sqrt μ := by
  have := Real.sqrt_pos.mpr hμ
  linarith

lemma two_cycle_period {F : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hFa : F a = b) (hFb : F b = a) : HasLeastPeriod F a 2 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · change F (F a) = a
    rw [hFa, hFb]
  · intro m hm hm2
    have : m = 1 := by omega
    subst m
    change F a ≠ a
    rw [hFa]
    exact hab.symm

lemma flip_deriv_sqrt {μ : ℝ} (hμ : 0 ≤ μ) :
    HasDerivAt (flip μ) (-1 + 2 * μ) (Real.sqrt μ) := by
  convert flip_hasDerivAt μ (Real.sqrt μ) using 1
  rw [Real.sq_sqrt hμ]
  ring

lemma flip_deriv_neg_sqrt {μ : ℝ} (hμ : 0 ≤ μ) :
    HasDerivAt (flip μ) (-1 + 2 * μ) (-Real.sqrt μ) := by
  convert flip_hasDerivAt μ (-Real.sqrt μ) using 1
  rw [neg_sq, Real.sq_sqrt hμ]
  ring

lemma return_deriv_sqrt {μ : ℝ} (hμ : 0 ≤ μ) :
    HasDerivAt ((flip μ)^[2]) ((-1 + 2 * μ) ^ 2) (Real.sqrt μ) := by
  have ho : HasDerivAt (flip μ) (-1 + 2 * μ) (flip μ (Real.sqrt μ)) := by
    rw [flip_sqrt hμ]
    exact flip_deriv_neg_sqrt hμ
  have h := ho.comp (Real.sqrt μ) (flip_deriv_sqrt hμ)
  simpa [Function.iterate_succ, pow_two, Function.comp_def] using h

lemma return_deriv_neg_sqrt {μ : ℝ} (hμ : 0 ≤ μ) :
    HasDerivAt ((flip μ)^[2]) ((-1 + 2 * μ) ^ 2) (-Real.sqrt μ) := by
  have ho : HasDerivAt (flip μ) (-1 + 2 * μ) (flip μ (-Real.sqrt μ)) := by
    rw [flip_neg_sqrt hμ]
    exact flip_deriv_sqrt hμ
  have h := ho.comp (-Real.sqrt μ) (flip_deriv_neg_sqrt hμ)
  simpa [Function.iterate_succ, pow_two, Function.comp_def] using h

theorem cycleData : Specs.D13Unified.Ch16.FlipNormalForm.cycleData := by
  intro μ hμ hμ1
  exact ⟨sqrt_distinct hμ, flip_sqrt hμ.le, flip_neg_sqrt hμ.le,
    two_cycle_period (sqrt_distinct hμ) (flip_sqrt hμ.le) (flip_neg_sqrt hμ.le),
    two_cycle_period (sqrt_distinct hμ).symm (flip_neg_sqrt hμ.le) (flip_sqrt hμ.le),
    (return_deriv_sqrt hμ.le).deriv, (return_deriv_neg_sqrt hμ.le).deriv⟩

lemma finiteOrbit_two {μ : ℝ} (hμ : 0 ≤ μ) :
    finiteOrbit (flip μ) (Real.sqrt μ) 2 = {Real.sqrt μ, -Real.sqrt μ} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [flip_sqrt hμ]
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨0, rfl⟩
    · have hx := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨1, by simpa using flip_sqrt hμ⟩

theorem cycleAttraction : Specs.D13Unified.Ch16.FlipNormalForm.cycleAttraction := by
  intro μ hμ hμ1
  have hperiod := two_cycle_period (sqrt_distinct hμ) (flip_sqrt hμ.le) (flip_neg_sqrt hμ.le)
  have hspec := scalar_spectral_lt (return_deriv_sqrt hμ.le) (show |(-1 + 2 * μ) ^ 2| < 1 by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith)
  have h := periodicAttraction (Basis.singleton (Fin 1) ℝ) (flip μ) (Real.sqrt μ) 2
    hperiod (fun z _ => (flip_contDiff μ).contDiffAt.of_le (by norm_num)) hspec
  rwa [finiteOrbit_two hμ.le] at h

theorem zeroAttraction : Specs.D13Unified.Ch16.FlipNormalForm.zeroAttraction := by
  intro μ hμ hμ0
  have hd : HasDerivAt (flip μ) (-(1 + μ)) 0 := by simpa using flip_hasDerivAt μ 0
  have hspec := scalar_spectral_lt hd (show |-(1 + μ)| < 1 by
    rw [abs_neg, abs_of_pos (by linarith : 0 < 1 + μ)]
    linarith)
  have h := D13Unified.Ch15.LinearizedStability.linearizedAttraction
    (Basis.singleton (Fin 1) ℝ) (flip μ) Set.univ 0 isOpen_univ (Set.mem_univ _)
    ((flip_contDiff μ).of_le (by norm_num)).contDiffOn (flip_zero μ) hspec
  exact ⟨flip_zero μ, h.2.1, h.2.2.2⟩

lemma scalar_eigenvalue {G : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt G a x) :
    Module.End.HasEigenvalue (complexify (LinearMap.toMatrix
      (Basis.singleton (Fin 1) ℝ) (Basis.singleton (Fin 1) ℝ)
      (fderiv ℝ G x).toLinearMap)).toLin' (a : ℂ) := by
  rw [derivative_matrix h]
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := fun _ : Fin 1 => (1 : ℂ))
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · intro hz
    have := congrFun hz 0
    norm_num at this

theorem zeroInstability : Specs.D13Unified.Ch16.FlipNormalForm.zeroInstability := by
  intro μ hμ
  refine ⟨flip_zero μ, ?_⟩
  have hd : HasDerivAt (flip μ) (-(1 + μ)) 0 := by simpa using flip_hasDerivAt μ 0
  have heig := scalar_eigenvalue hd
  have hnorm : 1 < ‖((-(1 + μ) : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith : 0 < 1 + μ)]
    linarith
  obtain ⟨ε, hε, _, hescape⟩ :=
    D13Unified.Ch15.LinearizedInstability.linearizedInstability
      (Basis.singleton (Fin 1) ℝ) (flip μ) Set.univ 0 (fderiv ℝ (flip μ) 0)
      isOpen_univ (Set.mem_univ _) (flip_zero μ)
      ((flip_contDiff μ).contDiffAt.of_le (by norm_num))
      hd.differentiableAt.hasFDerivAt ⟨_, heig, hnorm⟩
  intro hstable
  obtain ⟨δ, hδ, hstay⟩ := hstable ε hε
  obtain ⟨x, _, hx, N, _, hleave, _⟩ := hescape δ hδ
  have hnear : dist x (0 : ℝ) < δ := by simpa [dist_eq_norm] using hx
  have hfar := hstay x hnear N
  rw [dist_eq_norm] at hfar
  exact (not_lt_of_ge hleave) hfar

theorem amplitudeLimit : Specs.D13Unified.Ch16.FlipNormalForm.amplitudeLimit := by
  constructor
  · intro μ hμ
    simp [abs_of_nonneg (Real.sqrt_nonneg μ)]
  · simpa using (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      nhdsWithin_le_nhds

end D13Unified.Ch16.FlipNormalForm
