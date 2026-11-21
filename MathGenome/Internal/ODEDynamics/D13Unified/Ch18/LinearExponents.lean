import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.LinearExponents
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.JordanSolutions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.NormIndependence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace D13Unified.Ch18.LinearExponents

/-- In zero dimension the operator norm is zero, including for the identity. -/
theorem zero_dimensional :
    Specs.D13Unified.Ch18.LinearExponents.zeroDimensionalStatement.{u,v} := by
  intro 𝕂 _ n _ _ _ E _ _ _ b A
  have hsub : Subsingleton E := b.equivFun.toEquiv.subsingleton
  letI := hsub
  have hz (t : ℝ) : Ch07.matrixOperatorNorm b
      (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue A t) = 0 := by
    unfold Ch07.matrixOperatorNorm
    rw [Subsingleton.elim (Ch07.matrixOperatorEquiv b
      (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue A t)) 0, norm_zero]
  have hr (t : ℝ) : Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate t
      (Ch07.matrixOperatorNorm b
        (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue A t)) = ⊥ := by
    simp [hz, Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate]
  exact ⟨hr, by simpa only [hr] using (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (⊥ : EReal)) atTop (𝓝 ⊥))⟩

/-- Polynomial logarithmic corrections vanish after division by time. -/
theorem tendsto_log_one_add_div :
    Tendsto (fun t : ℝ => Real.log (1 + t) / t) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
    tendsto_atTop_mono (fun t => by dsimp; linarith) tendsto_id
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp ht
  simpa [Function.comp_def, add_comm, add_left_comm, add_assoc] using h

/-- The logarithm of an exponential times a polynomial has its expected rate. -/
theorem tendsto_log_exp_polynomial (c α : ℝ) (hc : 0 < c) (m : ℕ) :
    Tendsto (fun t : ℝ => Real.log (c * Real.exp (α * t) * (1 + t) ^ m) / t)
      atTop (𝓝 α) := by
  have h₀ : Tendsto (fun t : ℝ =>
      Real.log c / t + α + (m : ℝ) * (Real.log (1 + t) / t)) atTop (𝓝 α) := by
    simpa using ((tendsto_const_nhds.div_atTop tendsto_id).add_const α).add
      (tendsto_log_one_add_div.const_mul (m : ℝ))
  apply h₀.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.log_mul (mul_ne_zero hc.ne' (Real.exp_ne_zero _))
    (pow_ne_zero _ (by linarith)), Real.log_mul hc.ne' (Real.exp_ne_zero _),
    Real.log_exp, Real.log_pow]
  field_simp

/-- Two-sided exponential/polynomial bounds imply the actual logarithmic limit.
The lower bound is needed: an upper estimate alone would only control limsup. -/
theorem exponential_polynomial_squeeze (r : ℝ → ℝ) (α c C : ℝ) (m : ℕ)
    (hc : 0 < c) (hC : 0 < C)
    (hl : ∀ᶠ t in atTop, c * Real.exp (α * t) / (1 + t) ^ m ≤ r t)
    (hu : ∀ᶠ t in atTop, r t ≤ C * Real.exp (α * t) * (1 + t) ^ m) :
    Tendsto (fun t : ℝ => Real.log (r t) / t) atTop (𝓝 α) := by
  have hlow : Tendsto (fun t : ℝ =>
      Real.log (c * Real.exp (α * t) / (1 + t) ^ m) / t) atTop (𝓝 α) := by
    have h₀ : Tendsto (fun t : ℝ =>
        Real.log c / t + α - (m : ℝ) * (Real.log (1 + t) / t)) atTop (𝓝 α) := by
      simpa using ((tendsto_const_nhds.div_atTop tendsto_id).add_const α).sub
        (tendsto_log_one_add_div.const_mul (m : ℝ))
    apply h₀.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.log_div (mul_ne_zero hc.ne' (Real.exp_ne_zero _))
      (pow_ne_zero _ (by linarith)), Real.log_mul hc.ne' (Real.exp_ne_zero _),
      Real.log_exp, Real.log_pow]
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow
    (tendsto_log_exp_polynomial C α hC m)
  · filter_upwards [hl, eventually_gt_atTop (0 : ℝ)] with t ht hpos
    have hp : 0 < c * Real.exp (α * t) / (1 + t) ^ m := by positivity
    exact div_le_div_of_nonneg_right (Real.log_le_log hp ht) hpos.le
  · filter_upwards [hl, hu, eventually_gt_atTop (0 : ℝ)] with t ht₁ ht₂ hpos
    have hp : 0 < r t := lt_of_lt_of_le (by positivity) ht₁
    exact div_le_div_of_nonneg_right (Real.log_le_log hp ht₂) hpos.le

/-- Generalized eigenspaces give an actual finite decomposition of every vector. -/
theorem exists_spectral_decomposition {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) :
    ∃ f : ℂ →₀ (n → ℂ), IsSpectralDecomposition A v f := by
  let T : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' A
  obtain ⟨f, hf, heq⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun μ => T.maxGenEigenspace μ) v).mp
      ((Module.End.iSup_maxGenEigenspace_eq_top T).symm ▸ Submodule.mem_top)
  exact ⟨f, hf, heq⟩

/-- The maximum defining α(v) exists for every nonzero vector. -/
theorem exists_vector_abscissa {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) (hv : v ≠ 0) :
    ∃ α : ℝ, VectorAbscissa A v α := by
  classical
  obtain ⟨f, hf⟩ := exists_spectral_decomposition A v
  have hne : ({μ | f μ ≠ 0} : Set ℂ).Nonempty := by
    by_contra h
    have hfzero : f = 0 := by
      apply Finsupp.ext
      intro μ
      exact not_ne_iff.mp (fun hm => h ⟨μ, hm⟩)
    apply hv
    rw [← hf.2, hfzero]
    simp
  have hs : f.support.Nonempty := by
    obtain ⟨μ, hμ⟩ := hne
    exact ⟨μ, Finsupp.mem_support_iff.mpr hμ⟩
  obtain ⟨μ, hμ, hm⟩ := Finset.exists_max_image f.support Complex.re hs
  refine ⟨μ.re, f, hf, ⟨⟨μ, Finsupp.mem_support_iff.mp hμ, rfl⟩, ?_⟩⟩
  rintro r ⟨ν, hν, rfl⟩
  exact hm ν (Finsupp.mem_support_iff.mpr hν)

/-- All coefficients of a truncated exponential are polynomially bounded. -/
theorem exp_coefficient_le (t : ℝ) {j m : ℕ} (hj : j ≤ m) :
    |t ^ j / (Nat.factorial j : ℝ)| ≤ (1 + |t|) ^ m := by
  have hf : (1 : ℝ) ≤ (Nat.factorial j : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j)
  calc
    |t ^ j / (Nat.factorial j : ℝ)| = |t| ^ j / (Nat.factorial j : ℝ) := by
      rw [abs_div, abs_pow, abs_of_nonneg (show 0 ≤ (Nat.factorial j : ℝ) by linarith)]
    _ ≤ |t| ^ j := div_le_self (pow_nonneg (abs_nonneg _) _) hf
    _ ≤ (1 + |t|) ^ j := pow_le_pow_left₀ (abs_nonneg _) (by linarith) _
    _ ≤ (1 + |t|) ^ m := pow_le_pow_right₀ (by linarith [abs_nonneg t]) hj

/-- A truncated exponential acting on a vector admits a uniform polynomial bound. -/
theorem truncated_exp_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (w : ℕ → E) (m : ℕ) (t : ℝ) :
    ‖∑ j ∈ Finset.range m, (t ^ j / (Nat.factorial j : ℝ)) • w j‖ ≤
      (∑ j ∈ Finset.range m, ‖w j‖) * (1 + |t|) ^ m := by
  calc
    _ ≤ ∑ j ∈ Finset.range m, ‖(t ^ j / (Nat.factorial j : ℝ)) • w j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range m, (1 + |t|) ^ m * ‖w j‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (exp_coefficient_le t (Nat.le_of_lt (Finset.mem_range.mp hj))) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

open scoped Matrix.Norms.Operator

/-- On a generalized eigenspace the orbit has an exponential/polynomial upper bound. -/
theorem generalized_orbit_upper {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) (w : n → ℂ) (m : ℕ)
    (hw : ((A - μ • 1) ^ m).mulVec w = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(Ch07.matrixExp A t).mulVec w‖ ≤ C * Real.exp (μ.re * t) * (1 + |t|) ^ m := by
  let N := A - μ • (1 : Matrix n n ℂ)
  let C := (∑ j ∈ Finset.range m, ‖(N ^ j).mulVec w‖) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun t => ?_⟩
  have hA : A = μ • (1 : Matrix n n ℂ) + N := by dsimp [N]; abel
  rw [hA, Ch07.matrixExp_scalar_add, Matrix.smul_mulVec,
    norm_smul, Complex.norm_exp]
  have he : (μ * (t : ℂ)).re = μ.re * t := by simp
  rw [he, Ch07.matrixExp_mulVec_of_annihilated N w m hw]
  calc
    _ ≤ Real.exp (μ.re * t) *
        ((∑ j ∈ Finset.range m, ‖(N ^ j).mulVec w‖) * (1 + |t|) ^ m) :=
      mul_le_mul_of_nonneg_left (truncated_exp_norm_le (fun j => (N ^ j).mulVec w) m t)
        (Real.exp_pos _).le
    _ ≤ C * Real.exp (μ.re * t) * (1 + |t|) ^ m := by
      dsimp [C]
      nlinarith [Real.exp_pos (μ.re * t), pow_nonneg (by positivity : 0 ≤ 1 + |t|) m]

/-- The inverse nilpotent exponential has polynomial size even when nilpotence
holds only on the chosen vector, rather than on the entire ambient space. -/
theorem annihilated_orbit_lower {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) (w : n → ℂ) (m : ℕ)
    (hw : (N ^ m).mulVec w = 0) (hw0 : w ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c / (1 + |t|) ^ m ≤ ‖(Ch07.matrixExp N t).mulVec w‖ := by
  let D := (∑ j ∈ Finset.range m, ‖N ^ j‖) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨‖w‖ / D, div_pos (norm_pos_iff.mpr hw0) hD, fun t => ?_⟩
  let y := (Ch07.matrixExp N t).mulVec w
  have hcomm : Commute (N ^ m) (Ch07.matrixExp N t) :=
    (((Commute.refl N).pow_left m).smul_right t).exp_right
  have hy : (N ^ m).mulVec y = 0 := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  let P := ∑ j ∈ Finset.range m, ((-t) ^ j / (Nat.factorial j : ℝ)) • N ^ j
  have hPy : P.mulVec y = w := by
    dsimp [P]
    rw [Matrix.sum_mulVec]
    simp_rw [Matrix.smul_mulVec]
    rw [← Ch07.matrixExp_mulVec_of_annihilated N y m hy (-t)]
    dsimp [y]
    rw [Matrix.mulVec_mulVec, ← Ch07.matrixExp_add_time, neg_add_cancel,
      Ch07.matrixExp_zero, Matrix.one_mulVec]
  have hP : ‖P‖ ≤ D * (1 + |t|) ^ m := by
    have h := truncated_exp_norm_le (fun j => N ^ j) m (-t)
    simp only [abs_neg] at h
    apply h.trans
    dsimp [D]
    nlinarith [pow_nonneg (by positivity : 0 ≤ 1 + |t|) m]
  have hprod : ‖w‖ ≤ D * (1 + |t|) ^ m * ‖y‖ := by
    rw [← hPy]
    exact (Matrix.linfty_opNorm_mulVec P y).trans
      (mul_le_mul_of_nonneg_right hP (norm_nonneg y))
  have hp : 0 < (1 + |t|) ^ m := by positivity
  apply (div_le_iff₀ hp).mpr
  apply (div_le_iff₀ hD).mpr
  nlinarith

/-- A nonzero generalized-eigenspace vector has both required bounds. -/
theorem generalized_orbit_bounds {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) (w : n → ℂ) (m : ℕ)
    (hw : ((A - μ • 1) ^ m).mulVec w = 0) (hw0 : w ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ,
      c * Real.exp (μ.re * t) / (1 + |t|) ^ m ≤ ‖(Ch07.matrixExp A t).mulVec w‖ ∧
      ‖(Ch07.matrixExp A t).mulVec w‖ ≤ C * Real.exp (μ.re * t) * (1 + |t|) ^ m := by
  obtain ⟨C, hC, hu⟩ := generalized_orbit_upper A μ w m hw
  let N := A - μ • (1 : Matrix n n ℂ)
  obtain ⟨c, hc, hl⟩ := annihilated_orbit_lower N w m hw hw0
  refine ⟨c, C, hc, hC, fun t => ⟨?_, hu t⟩⟩
  have hA : A = μ • (1 : Matrix n n ℂ) + N := by dsimp [N]; abel
  rw [hA, Ch07.matrixExp_scalar_add, Matrix.smul_mulVec, norm_smul, Complex.norm_exp]
  have he : (μ * (t : ℂ)).re = μ.re * t := by simp
  rw [he]
  convert mul_le_mul_of_nonneg_left (hl t) (Real.exp_pos (μ.re * t)).le using 1 <;> ring

/-- In particular, nontrivial nilpotent parts do not affect the exponent of a
nonzero generalized eigenvector. -/
theorem generalized_orbit_limit {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) (w : n → ℂ) (m : ℕ)
    (hw : ((A - μ • 1) ^ m).mulVec w = 0) (hw0 : w ≠ 0) :
    Tendsto (fun t : ℝ => Real.log ‖(Ch07.matrixExp A t).mulVec w‖ / t)
      atTop (𝓝 μ.re) := by
  obtain ⟨c, C, hc, hC, hb⟩ := generalized_orbit_bounds A μ w m hw hw0
  apply exponential_polynomial_squeeze _ μ.re c C m hc hC
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa only [abs_of_nonneg ht] using (hb t).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa only [abs_of_nonneg ht] using (hb t).2

/-- Translate the library's generalized eigenspace into the matrix annihilator. -/
theorem annihilator_of_mem {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) (w : n → ℂ)
    (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' A) μ) :
    ∃ m : ℕ, ((A - μ • 1) ^ m).mulVec w = 0 := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace
    (Matrix.toLinAlgEquiv' A) μ w).mp hw
  refine ⟨m, ?_⟩
  simpa only [← Matrix.toLinAlgEquiv'_apply, map_pow, map_sub, map_smul, map_one] using hm

/-- A bounded projection onto any one generalized eigenspace. -/
theorem exists_spectral_projection {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) :
    ∃ P : (n → ℂ) →L[ℂ] (n → ℂ), ∀ (ν : ℂ) (w : n → ℂ),
      w ∈ Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' A) ν →
      P w = if ν = μ then w else 0 := by
  classical
  let T : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' A
  let p := T.maxGenEigenspace μ
  let q := ⨆ (ν : ℂ) (_ : ν ≠ μ), T.maxGenEigenspace ν
  have hc : IsCompl p q := by
    refine ⟨T.independent_maxGenEigenspace μ, ?_⟩
    rw [codisjoint_iff]
    exact (iSup_split_single T.maxGenEigenspace μ).symm.trans
      (Module.End.iSup_maxGenEigenspace_eq_top T)
  let P := (p.projection q hc).toContinuousLinearMap
  refine ⟨P, fun ν w hw => ?_⟩
  by_cases h : ν = μ
  · subst ν
    simpa [P] using Submodule.projection_apply_of_mem_left hc hw
  · have hle : T.maxGenEigenspace ν ≤ q := by
      dsimp [q]
      exact le_iSup₂ (f := fun ν (_ : ν ≠ μ) => T.maxGenEigenspace ν) ν h
    have hq : w ∈ q := hle hw
    simp only [ite_eq_right h]
    change p.projection q hc w = 0
    exact (Submodule.projection_apply_eq_zero_iff hc).mpr hq

/-- The flow preserves every generalized eigenspace. -/
theorem orbit_mem_generalized {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) (w : n → ℂ)
    (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' A) μ) (t : ℝ) :
    (Ch07.matrixExp A t).mulVec w ∈
      Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' A) μ := by
  have hc : Commute A (Ch07.matrixExp A t) :=
    ((Commute.refl A).smul_right t).exp_right
  have hc' : Commute (Matrix.toLinAlgEquiv' A)
      (Matrix.toLinAlgEquiv' (Ch07.matrixExp A t)) := hc.map Matrix.toLinAlgEquiv'
  exact Module.End.mapsTo_maxGenEigenspace_of_comm hc' μ hw

/-- Projection extracts precisely one moving spectral component; there is no
cancellation between distinct generalized eigenspaces in the lower estimate. -/
theorem project_orbit {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) (f : ℂ →₀ (n → ℂ))
    (hf : IsSpectralDecomposition A v f) (μ : ℂ)
    (P : (n → ℂ) →L[ℂ] (n → ℂ))
    (hP : ∀ (ν : ℂ) (w : n → ℂ),
      w ∈ Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' A) ν →
      P w = if ν = μ then w else 0) (t : ℝ) :
    P ((Ch07.matrixExp A t).mulVec v) = (Ch07.matrixExp A t).mulVec (f μ) := by
  classical
  rw [← hf.2]
  change P ((Ch07.matrixExp A t).mulVec (∑ ν ∈ f.support, f ν)) = _
  rw [Matrix.mulVec_sum, map_sum]
  simp_rw [hP _ _ (orbit_mem_generalized A _ _ (hf.1 _) t)]
  by_cases hμ : μ ∈ f.support
  · simp [hμ]
  · simp [hμ, Finsupp.notMem_support_iff.mp hμ]

/-- The finite decomposition used in the specification is the unique generalized
spectral decomposition, rather than a choice of a possibly different splitting. -/
theorem spectral_decomposition_unique {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) (f g : ℂ →₀ (n → ℂ))
    (hf : IsSpectralDecomposition A v f) (hg : IsSpectralDecomposition A v g) : f = g := by
  apply Finsupp.ext
  intro μ
  obtain ⟨P, hP⟩ := exists_spectral_projection A μ
  have heqf : P v = f μ := by
    simpa only [Ch07.matrixExp_zero, Matrix.one_mulVec] using project_orbit A v f hf μ P hP 0
  have heqg : P v = g μ := by
    simpa only [Ch07.matrixExp_zero, Matrix.one_mulVec] using project_orbit A v g hg μ P hP 0
  exact heqf.symm.trans heqg

/-- Thus the relational specification of α(v) determines a unique real value. -/
theorem vector_abscissa_unique {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) {α β : ℝ}
    (hα : VectorAbscissa A v α) (hβ : VectorAbscissa A v β) : α = β := by
  obtain ⟨f, hf, hfa⟩ := hα
  obtain ⟨g, hg, hgb⟩ := hβ
  have heq := spectral_decomposition_unique A v f g hf hg
  subst g
  exact le_antisymm (hgb.2 hfa.1) (hfa.2 hgb.1)

/-- Summing the finitely many spectral components gives the correct upper
rate, including all nilpotent degrees. -/
theorem spectral_orbit_upper {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) (f : ℂ →₀ (n → ℂ))
    (hf : IsSpectralDecomposition A v f) (α : ℝ)
    (hα : ∀ μ, f μ ≠ 0 → μ.re ≤ α) :
    ∃ C : ℝ, ∃ m : ℕ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖(Ch07.matrixExp A t).mulVec v‖ ≤ C * Real.exp (α * t) * (1 + t) ^ m := by
  classical
  have hex (μ : ℂ) : ∃ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(Ch07.matrixExp A t).mulVec (f μ)‖ ≤
        C * Real.exp (μ.re * t) * (1 + |t|) ^ m := by
    obtain ⟨m, hm⟩ := annihilator_of_mem A μ (f μ) (hf.1 μ)
    obtain ⟨C, hC, hb⟩ := generalized_orbit_upper A μ (f μ) m hm
    exact ⟨m, C, hC, hb⟩
  choose m C hC hb using hex
  let M := f.support.sup m
  let D := (∑ μ ∈ f.support, C μ) + 1
  have hsum : 0 ≤ ∑ μ ∈ f.support, C μ := Finset.sum_nonneg (fun μ _ => (hC μ).le)
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, M, hD, fun t ht => ?_⟩
  rw [← hf.2]
  change ‖(Ch07.matrixExp A t).mulVec (∑ μ ∈ f.support, f μ)‖ ≤ _
  rw [Matrix.mulVec_sum]
  calc
    _ ≤ ∑ μ ∈ f.support, ‖(Ch07.matrixExp A t).mulVec (f μ)‖ := norm_sum_le _ _
    _ ≤ ∑ μ ∈ f.support, C μ * Real.exp (α * t) * (1 + t) ^ M := by
      apply Finset.sum_le_sum
      intro μ hμ
      have he : Real.exp (μ.re * t) ≤ Real.exp (α * t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (hα μ (Finsupp.mem_support_iff.mp hμ)) ht)
      have hp : (1 + |t|) ^ m μ ≤ (1 + t) ^ M := by
        rw [abs_of_nonneg ht]
        exact pow_le_pow_right₀ (by linarith) (Finset.le_sup hμ)
      exact (hb μ t).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left he (hC μ).le) hp (by positivity)
          (mul_nonneg (hC μ).le (Real.exp_pos _).le))
    _ = (∑ μ ∈ f.support, C μ) * Real.exp (α * t) * (1 + t) ^ M := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ D * Real.exp (α * t) * (1 + t) ^ M := by
      dsimp [D]
      nlinarith [Real.exp_pos (α * t), pow_nonneg (by linarith : 0 ≤ 1 + t) M]

/-- A maximizing spectral component supplies the lower bound for the whole
orbit through a bounded spectral projection. -/
theorem spectral_orbit_lower {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) (α : ℝ) (ha : VectorAbscissa A v α) :
    ∃ c : ℝ, ∃ m : ℕ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      c * Real.exp (α * t) / (1 + t) ^ m ≤ ‖(Ch07.matrixExp A t).mulVec v‖ := by
  obtain ⟨f, hf, hα⟩ := ha
  obtain ⟨μ, hμ, heq⟩ := hα.1
  obtain ⟨m, hm⟩ := annihilator_of_mem A μ (f μ) (hf.1 μ)
  obtain ⟨c, C, hc, _, hb⟩ := generalized_orbit_bounds A μ (f μ) m hm hμ
  obtain ⟨P, hP⟩ := exists_spectral_projection A μ
  let K := ‖P‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨c / K, m, div_pos hc hK, fun t ht => ?_⟩
  have hproj : ‖(Ch07.matrixExp A t).mulVec (f μ)‖ ≤
      K * ‖(Ch07.matrixExp A t).mulVec v‖ := by
    rw [← project_orbit A v f hf μ P hP t]
    exact (P.le_opNorm _).trans (by
      dsimp [K]
      nlinarith [norm_nonneg ((Ch07.matrixExp A t).mulVec v)])
  have hlow := (hb t).1
  rw [heq, abs_of_nonneg ht] at hlow
  have hp : 0 < (1 + t) ^ m := by positivity
  apply (div_le_iff₀ hp).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hK).mpr
  have hlow' := (div_le_iff₀ hp).mp (hlow.trans hproj)
  nlinarith

/-- The full coordinate-vector theorem, with arbitrary Jordan blocks. -/
theorem coordinate_directional_limit {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) (α : ℝ) (ha : VectorAbscissa A v α) :
    Tendsto (fun t : ℝ => Real.log ‖(Ch07.matrixExp A t).mulVec v‖ / t)
      atTop (𝓝 α) := by
  obtain ⟨f, hf, hα⟩ := ha
  obtain ⟨C, m, hC, hu⟩ := spectral_orbit_upper A v f hf α
    (fun μ hμ => hα.2 ⟨μ, hμ, rfl⟩)
  obtain ⟨c, k, hc, hl⟩ := spectral_orbit_lower A v α ⟨f, hf, hα⟩
  let M := max m k
  apply exponential_polynomial_squeeze _ α c C M hc hC
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (div_le_div_of_nonneg_left (by positivity)
      (by positivity : 0 < (1 + t) ^ k)
      (pow_le_pow_right₀ (by linarith) (le_max_right m k))).trans (hl t ht)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hu t ht).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith) (le_max_left m k)) (by positivity))

/-- Nonzero generalized-eigenspace components correspond to genuine eigenvalues. -/
theorem eigenvalue_of_mem_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) (w : n → ℂ)
    (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' A) μ) (hw0 : w ≠ 0) :
    Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' A) μ := by
  let T : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' A
  apply Module.End.hasEigenvalue_of_hasGenEigenvalue (k := Module.finrank ℂ (n → ℂ))
  change T.genEigenspace μ _ ≠ ⊥
  rw [← T.maxGenEigenspace_eq_genEigenspace_finrank]
  intro hz
  apply hw0
  exact (Submodule.mem_bot ℂ).mp (hz ▸ hw)

/-- The operator abscissa exists precisely where the positive-dimensional
statement needs it. -/
theorem exists_operator_abscissa {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) : ∃ α : ℝ, OperatorAbscissa A α := by
  classical
  let T : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' A
  obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue T
  let s := (Module.End.finite_hasEigenvalue T).toFinset
  have hs : s.Nonempty := ⟨μ₀, by simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hμ₀⟩
  obtain ⟨μ, hμ, hm⟩ := Finset.exists_max_image s Complex.re hs
  refine ⟨μ.re, ⟨μ, ?_, rfl⟩, ?_⟩
  · simpa only [s, Set.Finite.mem_toFinset] using hμ
  · rintro r ⟨ν, hν, rfl⟩
    exact hm ν (by simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hν)

/-- The induced infinity matrix norm is bounded by the sum of column norms. -/
theorem matrix_norm_le_sum_columns {𝕂 n : Type*} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (M : Matrix n n 𝕂) : ‖M‖ ≤ ∑ j : n, ‖M.mulVec (Pi.single j 1)‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h : Finset.univ.sup (fun i : n => ∑ j : n, ‖M i j‖₊) ≤
      ∑ j : n, ‖M.mulVec (Pi.single j 1)‖₊ := by
    apply Finset.sup_le
    intro i _
    apply Finset.sum_le_sum
    intro j _
    rw [Matrix.mulVec_single_one]
    exact nnnorm_le_pi_nnnorm (M.col j) i
  simpa only [NNReal.coe_sum, coe_nnnorm] using (NNReal.coe_le_coe.mpr h)

/-- Uniform upper bound for the operator, from finitely many coordinate vectors. -/
theorem coordinate_operator_upper {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (α : ℝ) (ha : OperatorAbscissa A α) :
    ∃ C : ℝ, ∃ m : ℕ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖Ch07.matrixExp A t‖ ≤ C * Real.exp (α * t) * (1 + t) ^ m := by
  classical
  have hcol (i : n) : ∃ C : ℝ, ∃ m : ℕ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖(Ch07.matrixExp A t).mulVec (Pi.single i 1)‖ ≤
        C * Real.exp (α * t) * (1 + t) ^ m := by
    obtain ⟨f, hf⟩ := exists_spectral_decomposition A (Pi.single i 1)
    exact spectral_orbit_upper A _ f hf α (fun μ hμ =>
      ha.2 ⟨μ, eigenvalue_of_mem_ne_zero A μ (f μ) (hf.1 μ) hμ, rfl⟩)
  choose C m hC hb using hcol
  let D := (∑ i : n, C i) + 1
  let M := Finset.univ.sup m
  have hsum : 0 ≤ ∑ i : n, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, M, hD, fun t ht => ?_⟩
  calc
    _ ≤ ∑ i : n, ‖(Ch07.matrixExp A t).mulVec (Pi.single i 1)‖ := matrix_norm_le_sum_columns _
    _ ≤ ∑ i : n, C i * Real.exp (α * t) * (1 + t) ^ M := by
      apply Finset.sum_le_sum
      intro i _
      exact (hb i t ht).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith) (Finset.le_sup (Finset.mem_univ i)))
        (mul_nonneg (hC i).le (Real.exp_pos _).le))
    _ = (∑ i : n, C i) * Real.exp (α * t) * (1 + t) ^ M := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ D * Real.exp (α * t) * (1 + t) ^ M := by
      dsimp [D]
      nlinarith [Real.exp_pos (α * t), pow_nonneg (by linarith : 0 ≤ 1 + t) M]

/-- An exponential cannot annihilate a nonzero initial vector. -/
theorem matrixExp_mulVec_ne_zero {𝕂 n : Type*} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) (v : n → 𝕂) (hv : v ≠ 0) (t : ℝ) :
    (Ch07.matrixExp A t).mulVec v ≠ 0 := by
  intro hz
  have h := congrArg (fun w => (Ch07.matrixExp A (-t)).mulVec w) hz
  rw [Matrix.mulVec_mulVec, ← Ch07.matrixExp_add_time, neg_add_cancel,
    Ch07.matrixExp_zero, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact hv h

/-- A fixed comparison of positive magnitudes preserves the real logarithmic
limit. This uses the already proved extended-real norm comparison upstream. -/
theorem log_limit_of_comparable (r s : ℝ → ℝ) (α K : ℝ)
    (hr : ∀ t, 0 < r t) (hs : ∀ t, 0 < s t) (hK : 0 < K)
    (hrs : ∀ t, s t ≤ K * r t) (hsr : ∀ t, r t ≤ K * s t)
    (hl : Tendsto (fun t => Real.log (r t) / t) atTop (𝓝 α)) :
    Tendsto (fun t => Real.log (s t) / t) atTop (𝓝 α) := by
  have hr' : Tendsto (fun t => GrowthDefinitions.logarithmicRate t (r t))
      atTop (𝓝 (α : EReal)) := by
    simpa only [GrowthDefinitions.logarithmicRate_nonzero _ _ (hr _).ne'] using
      (EReal.tendsto_coe.mpr hl)
  have hs' := (NormIndependence.comparison_tendsto
    (fun t => (hr t).le) (fun t => (hs t).le) hK
    (fun t => by simp [(hr t).ne', (hs t).ne']) hrs hsr tendsto_id (α : EReal)).mp hr'
  have hs'' : Tendsto (fun t => ((Real.log (s t) / t : ℝ) : EReal))
      atTop (𝓝 (α : EReal)) := by
    simpa only [GrowthDefinitions.logarithmicRate_nonzero _ _ (hs _).ne', id_eq] using hs'
  exact EReal.tendsto_coe.mp hs''

/-- A change of coordinates transports this actual real limit in either scalar field. -/
theorem norm_equiv_log_limit {𝕂 E F : Type*} [RCLike 𝕂]
    [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    [NormedAddCommGroup F] [NormedSpace 𝕂 F]
    (e : E ≃L[𝕂] F) (x : ℝ → E) (hx : ∀ t, x t ≠ 0) (α : ℝ)
    (hl : Tendsto (fun t => Real.log ‖e (x t)‖ / t) atTop (𝓝 α)) :
    Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 α) := by
  let K := max ‖e.toContinuousLinearMap‖ ‖e.symm.toContinuousLinearMap‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have h₁ : ‖e.toContinuousLinearMap‖ ≤ K := by
    dsimp [K]
    linarith [le_max_left ‖e.toContinuousLinearMap‖ ‖e.symm.toContinuousLinearMap‖]
  have h₂ : ‖e.symm.toContinuousLinearMap‖ ≤ K := by
    dsimp [K]
    linarith [le_max_right ‖e.toContinuousLinearMap‖ ‖e.symm.toContinuousLinearMap‖]
  apply log_limit_of_comparable (fun t => ‖e (x t)‖) (fun t => ‖x t‖) α K
    (fun t => norm_pos_iff.mpr (by simpa using hx t))
    (fun t => norm_pos_iff.mpr (hx t)) hK _ _ hl
  · intro t
    have h := (e.symm.toContinuousLinearMap.le_opNorm (e (x t))).trans
      (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _))
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using h
  · intro t
    exact (e.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _))

/-- The complex directional result for an arbitrary fixed norm. -/
theorem complex_directional :
    Specs.D13Unified.Ch18.LinearExponents.complexDirectionalStatement.{u,v} := by
  intro n _ _ E _ _ _ b A v hv
  have hcoords : b.equivFun v ≠ 0 := by simpa using hv
  refine ⟨exists_vector_abscissa A (b.equivFun v) hcoords, fun α hα => ?_⟩
  let e := b.equivFun.toContinuousLinearEquiv
  refine norm_equiv_log_limit e
    (fun t => Ch07.matrixOperatorEquiv b
      (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue A t) v) ?_ α ?_
  · intro t h
    have h' := congrArg b.equivFun h
    rw [map_zero, Ch07.matrixOperator_action] at h'
    exact matrixExp_mulVec_ne_zero A _ hcoords t h'
  · change Tendsto (fun t : ℝ => Real.log ‖b.equivFun
      (Ch07.matrixOperatorEquiv b (Ch07.matrixExp A t) v)‖ / t) atTop (𝓝 α)
    simp_rw [Ch07.matrixOperator_action]
    exact coordinate_directional_limit A (b.equivFun v) α hα

/-- An eigenvector with maximal real part gives the operator lower bound. -/
theorem coordinate_operator_lower {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (α : ℝ) (ha : OperatorAbscissa A α) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      c * Real.exp (α * t) / (1 + t) ≤ ‖Ch07.matrixExp A t‖ := by
  obtain ⟨μ, hμ, heq⟩ := ha.1
  obtain ⟨w, hw⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
  have hw' : ((A - μ • 1) ^ 1).mulVec w = 0 := by
    have he := (Module.End.mem_eigenspace_iff.mp hw.1)
    rw [pow_one]
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, Matrix.toLinAlgEquiv'_apply]
      using he
  obtain ⟨c, C, hc, _, hb⟩ := generalized_orbit_bounds A μ w 1 hw' hw.2
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw.2
  refine ⟨c / ‖w‖, div_pos hc hwpos, fun t ht => ?_⟩
  have hlow := (hb t).1
  rw [heq, abs_of_nonneg ht, pow_one] at hlow
  have hnorm := Matrix.linfty_opNorm_mulVec (Ch07.matrixExp A t) w
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hwpos).mpr
  have hlow' := (div_le_iff₀ (by linarith : 0 < 1 + t)).mp (hlow.trans hnorm)
  nlinarith

/-- The coordinate operator logarithmic limit. -/
theorem coordinate_operator_limit {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (α : ℝ) (ha : OperatorAbscissa A α) :
    Tendsto (fun t : ℝ => Real.log ‖Ch07.matrixExp A t‖ / t) atTop (𝓝 α) := by
  obtain ⟨C, m, hC, hu⟩ := coordinate_operator_upper A α ha
  obtain ⟨c, hc, hl⟩ := coordinate_operator_lower A α ha
  let M := max m 1
  apply exponential_polynomial_squeeze _ α c C M hc hC
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (div_le_div_of_nonneg_left (by positivity) (by linarith : 0 < 1 + t)
      (by simpa only [pow_one] using
        (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + t) (le_max_right m 1)))).trans (hl t ht)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hu t ht).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith) (le_max_left m 1)) (by positivity))

/-- Relating the auxiliary coordinate matrix norm to the induced operator norm
in any chosen normed realization, with constants independent of the matrix. -/
theorem operator_norm_comparison {𝕂 n E : Type*} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] [FiniteDimensional 𝕂 E]
    (b : Module.Basis n 𝕂 E) :
    ∃ K : ℝ, 0 < K ∧ ∀ M : Matrix n n 𝕂,
      Ch07.matrixOperatorNorm b M ≤ K * ‖M‖ ∧
      ‖M‖ ≤ K * Ch07.matrixOperatorNorm b M := by
  let e := b.equivFun.toContinuousLinearEquiv
  let K := (‖e.toContinuousLinearMap‖ + 1) * (‖e.symm.toContinuousLinearMap‖ + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hkk : ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ K := by
    dsimp [K]
    nlinarith [norm_nonneg e.toContinuousLinearMap, norm_nonneg e.symm.toContinuousLinearMap]
  refine ⟨K, hK, fun M => ⟨?_, ?_⟩⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK.le (norm_nonneg M))
    intro x
    have hcoord := Ch07.matrixOperator_action b M x
    have h₁ := e.symm.toContinuousLinearMap.le_opNorm (e (Ch07.matrixOperatorEquiv b M x))
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h₁
    have h₂ : ‖e (Ch07.matrixOperatorEquiv b M x)‖ ≤ ‖M‖ * ‖e x‖ := by
      change ‖b.equivFun (Ch07.matrixOperatorEquiv b M x)‖ ≤ _
      rw [hcoord]
      exact Matrix.linfty_opNorm_mulVec M _
    have h₃ := e.toContinuousLinearMap.le_opNorm x
    calc
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖M‖ * (‖e.toContinuousLinearMap‖ * ‖x‖)) :=
        h₁.trans (mul_le_mul_of_nonneg_left
          (h₂.trans (mul_le_mul_of_nonneg_left h₃ (norm_nonneg M))) (norm_nonneg _))
      _ ≤ K * ‖M‖ * ‖x‖ := by
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hkk (norm_nonneg M)) (norm_nonneg x) using 1 <;> ring
  · rw [Matrix.linfty_opNorm_eq_opNorm]
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hK.le (norm_nonneg (Ch07.matrixOperatorEquiv b M)))
    intro w
    have he : M.mulVec w = e (Ch07.matrixOperatorEquiv b M (e.symm w)) := by
      rw [show e (Ch07.matrixOperatorEquiv b M (e.symm w)) =
        M.mulVec (e (e.symm w)) from Ch07.matrixOperator_action b M (e.symm w)]
      simp
    change ‖M.mulVec w‖ ≤ _
    rw [he]
    have h₁ := e.toContinuousLinearMap.le_opNorm (Ch07.matrixOperatorEquiv b M (e.symm w))
    have h₂ := (Ch07.matrixOperatorEquiv b M).le_opNorm (e.symm w)
    have h₃ := e.symm.toContinuousLinearMap.le_opNorm w
    calc
      _ ≤ ‖e.toContinuousLinearMap‖ *
          (Ch07.matrixOperatorNorm b M * (‖e.symm.toContinuousLinearMap‖ * ‖w‖)) :=
        h₁.trans (mul_le_mul_of_nonneg_left
          (h₂.trans (mul_le_mul_of_nonneg_left h₃ (norm_nonneg _))) (norm_nonneg _))
      _ ≤ K * Ch07.matrixOperatorNorm b M * ‖w‖ := by
        dsimp only [Ch07.matrixOperatorNorm]
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hkk (norm_nonneg (Ch07.matrixOperatorEquiv b M)))
          (norm_nonneg w) using 1 <;> ring

theorem matrixExp_ne_zero {𝕂 n : Type*} [RCLike 𝕂] [Fintype n]
    [DecidableEq n] [Nonempty n] (A : Matrix n n 𝕂) (t : ℝ) : Ch07.matrixExp A t ≠ 0 := by
  intro hz
  have h := Ch07.matrixExp_add_time A t (-t)
  rw [add_neg_cancel, Ch07.matrixExp_zero, hz, zero_mul] at h
  exact one_ne_zero h

/-- Convert the operator limit to any fixed state norm, with its actual induced norm. -/
theorem operator_log_limit_of_coordinate {𝕂 n E : Type*} [RCLike 𝕂] [Fintype n]
    [DecidableEq n] [NormedAddCommGroup E] [NormedSpace 𝕂 E] [FiniteDimensional 𝕂 E]
    (b : Module.Basis n 𝕂 E) (M : ℝ → Matrix n n 𝕂) (hM : ∀ t, M t ≠ 0) (α : ℝ)
    (hl : Tendsto (fun t => Real.log ‖M t‖ / t) atTop (𝓝 α)) :
    Tendsto (fun t => Real.log (Ch07.matrixOperatorNorm b (M t)) / t) atTop (𝓝 α) := by
  obtain ⟨K, hK, hb⟩ := operator_norm_comparison b
  refine log_limit_of_comparable (fun t => ‖M t‖)
    (fun t => Ch07.matrixOperatorNorm b (M t)) α K
    (fun t => norm_pos_iff.mpr (hM t)) ?_ hK (fun t => (hb _).1) (fun t => (hb _).2) hl
  intro t
  apply norm_pos_iff.mpr
  intro hz
  apply hM t
  exact (Ch07.matrixOperatorEquiv b).injective (hz.trans (map_zero _).symm)

/-- Positive-dimensional complex operator theorem. -/
theorem complex_operator :
    Specs.D13Unified.Ch18.LinearExponents.complexOperatorStatement.{u,v} := by
  intro n _ _ _ E _ _ _ b A
  refine ⟨exists_operator_abscissa A, fun α hα => ?_⟩
  exact operator_log_limit_of_coordinate b (Ch07.matrixExp A) (matrixExp_ne_zero A)
    α (coordinate_operator_limit A α hα)

/-- Real exponential and coordinatewise complexification commute. -/
theorem matrixExp_complexify {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (t : ℝ) :
    (Ch07.matrixExp A t).map Complex.ofReal = Ch07.matrixExp (A.map Complex.ofReal) t := by
  let f : Matrix n n ℝ →+* Matrix n n ℂ := Complex.ofRealHom.mapMatrix
  have hf : Continuous f := by
    change Continuous (fun A : Matrix n n ℝ => A.map Complex.ofReal)
    fun_prop
  have hs : f (t • A) = t • f A := by ext i j; simp [f]
  change f (NormedSpace.exp (t • A)) = NormedSpace.exp (t • f A)
  rw [NormedSpace.map_exp f hf, hs]

/-- Complexification preserves the coordinate vector norm exactly. -/
theorem norm_complexify {n : Type*} [Fintype n] (w : n → ℝ) :
    ‖fun k => (w k : ℂ)‖ = ‖w‖ := by
  simp only [Pi.norm_def, Complex.nnnorm_real]

/-- It also preserves the induced infinity matrix norm for a real matrix. -/
theorem matrix_norm_complexify {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    ‖M.map Complex.ofReal‖ = ‖M‖ := by
  simp only [Matrix.linfty_opNorm_def, Matrix.map_apply, Complex.nnnorm_real]

/-- The real and complexified orbits agree as actual vectors. -/
theorem complexify_orbit {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (w : n → ℝ) (t : ℝ) :
    (Ch07.matrixExp (A.map Complex.ofReal) t).mulVec (fun k => (w k : ℂ)) =
      fun k => ((Ch07.matrixExp A t).mulVec w k : ℂ) := by
  rw [← matrixExp_complexify]
  ext k
  exact (Complex.ofRealHom.map_mulVec _ _ k).symm

/-- The real directional limit in coordinate norm. -/
theorem real_coordinate_directional_limit {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : n → ℝ) (α : ℝ)
    (ha : VectorAbscissa (A.map Complex.ofReal) (fun k => (v k : ℂ)) α) :
    Tendsto (fun t => Real.log ‖(Ch07.matrixExp A t).mulVec v‖ / t) atTop (𝓝 α) := by
  have hl := coordinate_directional_limit (A.map Complex.ofReal) (fun k => (v k : ℂ)) α ha
  simpa only [complexify_orbit, norm_complexify] using hl

/-- The real directional theorem for any fixed state norm. -/
theorem real_directional :
    Specs.D13Unified.Ch18.LinearExponents.realDirectionalStatement.{u,v} := by
  intro n _ _ E _ _ _ b A v hv
  have hcoords : b.equivFun v ≠ 0 := by simpa using hv
  have hcomplex : (fun k => (b.equivFun v k : ℂ)) ≠ 0 := by
    intro hz
    apply hcoords
    ext k
    exact Complex.ofReal_injective (congrFun hz k)
  refine ⟨exists_vector_abscissa (A.map Complex.ofReal) _ hcomplex, fun α hα => ?_⟩
  let e := b.equivFun.toContinuousLinearEquiv
  refine norm_equiv_log_limit e
    (fun t => Ch07.matrixOperatorEquiv b
      (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue A t) v) ?_ α ?_
  · intro t h
    have h' := congrArg b.equivFun h
    rw [map_zero, Ch07.matrixOperator_action] at h'
    exact matrixExp_mulVec_ne_zero A _ hcoords t h'
  · change Tendsto (fun t : ℝ => Real.log ‖b.equivFun
      (Ch07.matrixOperatorEquiv b (Ch07.matrixExp A t) v)‖ / t) atTop (𝓝 α)
    simp_rw [Ch07.matrixOperator_action]
    exact real_coordinate_directional_limit A (b.equivFun v) α hα

/-- Positive-dimensional real operator theorem, with its spectrum taken over ℂ. -/
theorem real_operator :
    Specs.D13Unified.Ch18.LinearExponents.realOperatorStatement.{u,v} := by
  intro n _ _ _ E _ _ _ b A
  refine ⟨exists_operator_abscissa (A.map Complex.ofReal), fun α hα => ?_⟩
  apply operator_log_limit_of_coordinate b (Ch07.matrixExp A) (matrixExp_ne_zero A) α
  have hl := coordinate_operator_limit (A.map Complex.ofReal) α hα
  simpa only [← matrixExp_complexify, matrix_norm_complexify] using hl

end D13Unified.Ch18.LinearExponents
