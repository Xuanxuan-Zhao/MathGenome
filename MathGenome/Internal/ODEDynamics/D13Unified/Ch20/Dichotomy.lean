import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.Dichotomy
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.HyperbolicSplitting
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.JordanSolutions
import Mathlib.Tactic.Positivity

noncomputable section
open scoped Matrix.Norms.Operator Topology
open Filter Finset
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch20

/-- Exponential decay in forward real time, including the endpoint zero. -/
def ExponentialDecay {V : Type*} [NormedAddCommGroup V] (f : ℝ → V) : Prop :=
  ∃ C α : ℝ, 0 ≤ C ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (-α * t)

namespace ExponentialDecay
variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]

lemma zero : ExponentialDecay (fun _ : ℝ => (0 : V)) :=
  ⟨0, 1, le_rfl, zero_lt_one, by simp⟩

lemma add {f g : ℝ → V} (hf : ExponentialDecay f) (hg : ExponentialDecay g) :
    ExponentialDecay (fun t => f t + g t) := by
  obtain ⟨C, a, hC, ha, hf⟩ := hf
  obtain ⟨D, b, hD, hb, hg⟩ := hg
  refine ⟨C + D, min a b, add_nonneg hC hD, lt_min ha hb, ?_⟩
  intro t ht
  have h₁ : Real.exp (-a * t) ≤ Real.exp (-(min a b) * t) := by
    apply Real.exp_le_exp.mpr; nlinarith [min_le_left a b]
  have h₂ : Real.exp (-b * t) ≤ Real.exp (-(min a b) * t) := by
    apply Real.exp_le_exp.mpr; nlinarith [min_le_right a b]
  calc
    ‖f t + g t‖ ≤ ‖f t‖ + ‖g t‖ := norm_add_le _ _
    _ ≤ C * Real.exp (-a * t) + D * Real.exp (-b * t) := add_le_add (hf t ht) (hg t ht)
    _ ≤ C * Real.exp (-(min a b) * t) + D * Real.exp (-(min a b) * t) :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ hC) (mul_le_mul_of_nonneg_left h₂ hD)
    _ = _ := by ring

lemma sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → V}
    (hf : ∀ i ∈ s, ExponentialDecay (f i)) :
    ExponentialDecay (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (V := V))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

lemma map [NormedSpace ℝ V] [NormedSpace ℝ W]
    {f : ℝ → V} (hf : ExponentialDecay f) (L : V →L[ℝ] W) :
    ExponentialDecay (fun t => L (f t)) := by
  obtain ⟨C, a, hC, ha, hf⟩ := hf
  refine ⟨‖L‖ * C, a, mul_nonneg (norm_nonneg _) hC, ha, fun t ht => ?_⟩
  calc
    ‖L (f t)‖ ≤ ‖L‖ * ‖f t‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (C * Real.exp (-a * t)) := mul_le_mul_of_nonneg_left (hf t ht) (norm_nonneg _)
    _ = _ := by ring

lemma of_norm_le {f : ℝ → V} {g : ℝ → W} (hg : ExponentialDecay g)
    (h : ∀ t, 0 ≤ t → ‖f t‖ ≤ ‖g t‖) : ExponentialDecay f := by
  obtain ⟨C, a, hC, ha, hg⟩ := hg
  exact ⟨C, a, hC, ha, fun t ht => (h t ht).trans (hg t ht)⟩

lemma pi {ι : Type*} [Fintype ι] {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {f : ℝ → ∀ i, V i} (hf : ∀ i, ExponentialDecay (fun t => f t i)) :
    ExponentialDecay f := by
  classical
  have h := sum (Finset.univ : Finset ι) (fun i _ =>
    (hf i).map (ContinuousLinearMap.single ℝ V i))
  simpa only [Finset.sum_apply, ContinuousLinearMap.single_apply, Finset.univ_sum_single]
    using h

end ExponentialDecay

/-- A direct exponential-series bound absorbs every monomial. -/
lemma pow_le_exp_mul (j : ℕ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ j ≤ ((Nat.factorial j : ℝ) / δ ^ j) * Real.exp (δ * t) := by
  have h := Real.pow_div_factorial_le_exp (δ * t) (mul_nonneg hδ.le ht) j
  have hj : (0 : ℝ) < Nat.factorial j := by positivity
  rw [div_le_iff₀ hj, mul_pow] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hδ j)).mpr
  simpa only [mul_comm] using h

lemma polynomial_exp_bound (p : Polynomial ℂ) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖p.eval ((c * t : ℝ) : ℂ)‖ ≤ C * Real.exp (δ * t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨C, hC, hp⟩ := hp
    obtain ⟨D, hD, hq⟩ := hq
    refine ⟨C + D, add_nonneg hC hD, fun t ht => ?_⟩
    rw [Polynomial.eval_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hp t ht) (hq t ht))
  | monomial j z =>
    refine ⟨‖z‖ * |c| ^ j * ((Nat.factorial j : ℝ) / δ ^ j), by positivity,
      fun t ht => ?_⟩
    simp only [Polynomial.eval_monomial, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, mul_pow]
    calc
      ‖z‖ * (|c| ^ j * t ^ j) = (‖z‖ * |c| ^ j) * t ^ j := by ring
      _ ≤ (‖z‖ * |c| ^ j) *
          (((Nat.factorial j : ℝ) / δ ^ j) * Real.exp (δ * t)) :=
        mul_le_mul_of_nonneg_left (pow_le_exp_mul j hδ ht) (by positivity)
      _ = _ := by ring

lemma exponential_polynomial_decay (p : Polynomial ℂ) (μ : ℂ) (c : ℝ)
    (hμ : c * μ.re < 0) :
    ExponentialDecay (fun t => p.eval ((c * t : ℝ) : ℂ) *
      Complex.exp (μ * ((c * t : ℝ) : ℂ))) := by
  let a := -(c * μ.re) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  obtain ⟨C, hC, hp⟩ := polynomial_exp_bound p c ha
  refine ⟨C, a, hC, ha, fun t ht => ?_⟩
  rw [norm_mul, Complex.norm_exp]
  have hre : (μ * ((c * t : ℝ) : ℂ)).re = μ.re * (c * t) := by simp
  rw [hre]
  calc
    ‖p.eval (↑(c * t))‖ * Real.exp (μ.re * (c * t)) ≤
        (C * Real.exp (a * t)) * Real.exp (μ.re * (c * t)) :=
      mul_le_mul_of_nonneg_right (hp t ht) (Real.exp_pos _).le
    _ = C * Real.exp (-a * t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [a]; ring

open D13Unified.Ch07
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma generalized_orbit_decay (A : Matrix n n ℂ) (μ : ℂ) (c : ℝ)
    (hμ : c * μ.re < 0) (v : n → ℂ)
    (hv : v ∈ Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' A) μ) :
    ExponentialDecay (fun t => (matrixExp A (c * t)).mulVec v) := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hv
  have hm' : ((A - μ • (1 : Matrix n n ℂ)) ^ m).mulVec v = 0 := by
    simpa only [← Matrix.toLinAlgEquiv'_apply, map_pow, map_sub, map_smul, map_one]
      using hm
  obtain ⟨p, hp⟩ := matrixExp_generalized_eigenvector A μ v m hm'
  apply ExponentialDecay.pi
  intro i
  simpa only [hp] using exponential_polynomial_decay (p i) μ c hμ

lemma spectral_orbit_decay (A : Matrix n n ℝ) (stable : Bool) (c : ℝ)
    (hc : ∀ μ : ℂ, (if stable then μ.re < 0 else 0 < μ.re) → c * μ.re < 0)
    (v : n → ℂ) (hv : v ∈ complexSpectralSpace A stable) :
    ExponentialDecay (fun t => (matrixExp (A.map Complex.ofReal) (c * t)).mulVec v) := by
  unfold complexSpectralSpace at hv
  refine Submodule.iSup_induction _ (motive := fun v =>
    ExponentialDecay (fun t => (matrixExp (A.map Complex.ofReal) (c * t)).mulVec v))
    hv ?_ ?_ ?_
  · intro μ v hv
    exact generalized_orbit_decay _ μ.val c (hc _ μ.property) v hv
  · simpa using (ExponentialDecay.zero (V := n → ℂ))
  · intro x y hx hy
    simpa only [Matrix.mulVec_add] using hx.add hy

/-- The real exponential agrees with its complexification. -/
lemma matrixExp_complexification (A : Matrix n n ℝ) (t : ℝ) :
    (matrixExp A t).map Complex.ofReal = matrixExp (A.map Complex.ofReal) t := by
  let F : Matrix n n ℝ →ₐ[ℝ] Matrix n n ℂ :=
    AlgHom.mapMatrix (Algebra.ofId ℝ ℂ)
  have hF : Continuous F := F.toLinearMap.continuous_of_finiteDimensional
  simpa [matrixExp, F, AlgHom.mapMatrix_apply, Algebra.ofId, Complex.coe_algebraMap] using NormedSpace.map_exp F hF (t • A)

lemma real_spectral_orbit_decay (A : Matrix n n ℝ) (stable : Bool) (c : ℝ)
    (hc : ∀ μ : ℂ, (if stable then μ.re < 0 else 0 < μ.re) → c * μ.re < 0)
    (v : n → ℝ) (hv : v ∈ realSpectralSpace A stable) :
    ExponentialDecay (fun t => (matrixExp A (c * t)).mulVec v) := by
  let R : (n → ℂ) →L[ℝ] (n → ℝ) := ContinuousLinearMap.pi
    (fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i))
  have h := (spectral_orbit_decay A stable c hc (realEmbedding v) hv).map R
  have heq (t : ℝ) : R ((matrixExp (A.map Complex.ofReal) (c * t)).mulVec
      (realEmbedding v)) = (matrixExp A (c * t)).mulVec v := by
    rw [← matrixExp_complexification]
    ext i
    change (((matrixExp A (c * t)).map Complex.ofReal).mulVec
      (fun i => (v i : ℂ)) i).re = _
    exact congrArg Complex.re (Complex.ofRealHom.map_mulVec (matrixExp A (c * t)) v i).symm
  simpa only [heq] using h

lemma projectionMatrix_mulVec (A : Matrix n n ℝ) (stable : Bool) (v : n → ℝ) :
    (Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A stable).mulVec v =
      Specs.D13Unified.Ch20.HyperbolicSplitting.projectionValue A stable v := by
  simpa only [Specs.D13Unified.Ch20.Dichotomy.projectionMatrix, Matrix.toLinAlgEquiv'_apply] using
    congrArg (fun f : Module.End ℝ (n → ℝ) => f v)
      (Matrix.toLinAlgEquiv'.apply_symm_apply
        (Specs.D13Unified.Ch20.HyperbolicSplitting.projectionValue A stable))

/-- A spectral projection has decaying columns, hence a decaying matrix in
any induced operator norm. The conversion is a continuous linear map from
ordinary coordinate arrays, so no equality of unrelated norms is presumed. -/
lemma projected_operator_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) (stable : Bool) (c : ℝ)
    (hc : ∀ μ : ℂ, (if stable then μ.re < 0 else 0 < μ.re) → c * μ.re < 0) :
    ExponentialDecay (fun t => matrixOperatorEquiv b
      (matrixExp A (c * t) * Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A stable)) := by
  let P := Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A stable
  have hcol (j : n) : ExponentialDecay (fun t =>
      (matrixExp A (c * t)).mulVec (fun i => P i j)) := by
    apply real_spectral_orbit_decay A stable c hc
    have hcomp : IsCompl (realSpectralSpace A stable) (realSpectralSpace A (!stable)) := by
      cases stable
      · exact (hyperbolic_splitting A hA).symm
      · exact hyperbolic_splitting A hA
    have hmem := Submodule.projection_apply_mem hcomp (Pi.single j 1)
    rw [← projection_eq A hA stable] at hmem
    have hPv : (fun i => P i j) =
        Specs.D13Unified.Ch20.HyperbolicSplitting.projectionValue A stable (Pi.single j 1) := by
      rw [← projectionMatrix_mulVec]
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, P]
    rw [hPv]
    exact hmem
  have hentry (j i : n) : ExponentialDecay (fun t =>
      (matrixExp A (c * t) * P) i j) := by
    have h := (hcol j).map (ContinuousLinearMap.proj i)
    change ExponentialDecay (fun t => (matrixExp A (c * t)).mulVec (fun i => P i j) i) at h
    exact h
  have harray : ExponentialDecay (fun t => fun i j =>
      (matrixExp A (c * t) * P) i j) :=
    ExponentialDecay.pi (fun i => ExponentialDecay.pi (fun j => hentry j i))
  let L : (n → n → ℝ) →ₗ[ℝ] (E →L[ℝ] E) :=
    (matrixOperatorEquiv b).toLinearMap.comp (Matrix.ofLinearEquiv ℝ).toLinearMap
  exact harray.map L.toContinuousLinearMap

/-- Exponential dichotomy for the canonical generalized spectral projections. -/
theorem exponential_dichotomy : Specs.D13Unified.Ch20.Dichotomy.dichotomyType := by
  intro n _ _ E _ _ _ b A hA
  have hs := projected_operator_decay b A hA true 1 (by intro μ hμ; simpa using hμ)
  have hu := projected_operator_decay b A hA false (-1) (by
    intro μ hμ; simp only [Bool.false_eq_true, ↓reduceIte] at hμ; linarith)
  obtain ⟨C, a, hC, ha, hs⟩ := hs
  obtain ⟨D, d, hD, hd, hu⟩ := hu
  refine ⟨max 1 (max C D), min a d, le_max_left _ _, lt_min ha hd, fun t ht => ?_⟩
  have hbound (X r : ℝ) (hX : 0 ≤ X) (hXK : X ≤ max 1 (max C D))
      (hr : min a d ≤ r) :
      X * Real.exp (-r * t) ≤ max 1 (max C D) * Real.exp (-(min a d) * t) := by
    apply mul_le_mul hXK _ (Real.exp_pos _).le (le_trans hX hXK)
    apply Real.exp_le_exp.mpr
    nlinarith
  constructor
  · have hs' := hs t ht
    simp only [one_mul] at hs'
    exact hs'.trans
      (hbound C a hC ((le_max_left C D).trans (le_max_right 1 (max C D))) (min_le_left a d))
  · have hu' := hu t ht
    simp only [neg_one_mul] at hu'
    exact hu'.trans
      (hbound D d hD ((le_max_right C D).trans (le_max_right 1 (max C D))) (min_le_right a d))

lemma whole_line_solution_formula (A : Matrix n n ℝ) (z : ℝ → n → ℝ)
    (hz : ∀ t, HasDerivAt z (A.mulVec (z t)) t) (s t : ℝ) :
    z t = (matrixExp A (t - s)).mulVec (z s) := by
  have hzcont : Continuous z := continuous_iff_continuousAt.mpr (fun t => (hz t).continuousAt)
  have hderiv : deriv z = fun t => A.mulVec (z t) := funext (fun t => (hz t).deriv)
  have hC1 : ContDiff ℝ 1 z := contDiff_one_iff_deriv.mpr
    ⟨fun t => (hz t).differentiableAt, by rw [hderiv]; fun_prop⟩
  have hsol : D13Unified.IsClassicalSolutionOn (matrixODE A) D13Unified.OpenTimeInterval.whole z := by
    refine ⟨hC1.contDiffOn, fun _ _ => Set.mem_univ _, ?_⟩
    intro t _
    simpa [matrixODE, D13Unified.ODE.eval] using hz t
  exact matrix_solution_formula A D13Unified.OpenTimeInterval.whole z hsol s
    (Set.mem_univ _) t (Set.mem_univ _)

lemma pi_matrixOperator_action (M : Matrix n n ℝ) (x : n → ℝ) :
    matrixOperatorEquiv (Pi.basisFun ℝ n) M x = M.mulVec x := by
  simpa using matrixOperator_action (Pi.basisFun ℝ n) M x

lemma bounded_solution_projection_zero (A : Matrix n n ℝ) (hA : IsHyperbolic A)
    (z : ℝ → n → ℝ) (hz : ∀ t, HasDerivAt z (A.mulVec (z t)) t)
    (hbounded : ∃ M : ℝ, ∀ t, ‖z t‖ ≤ M)
    (stable : Bool) (c : ℝ)
    (hc : ∀ μ : ℂ, (if stable then μ.re < 0 else 0 < μ.re) → c * μ.re < 0)
    (s : ℝ) : Specs.D13Unified.Ch20.HyperbolicSplitting.projectionValue A stable (z s) = 0 := by
  let P := Specs.D13Unified.Ch20.HyperbolicSplitting.projectionValue A stable
  let Q := Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A stable
  let F := fun t => matrixOperatorEquiv (Pi.basisFun ℝ n) (matrixExp A (c * t) * Q)
  obtain ⟨C, a, hC, ha, hdecay⟩ :=
    projected_operator_decay (Pi.basisFun ℝ n) A hA stable c hc
  obtain ⟨M, hM⟩ := hbounded
  have hM0 : 0 ≤ M := (norm_nonneg (z 0)).trans (hM 0)
  have heq (t : ℝ) : P (z s) = F t (z (s - c * t)) := by
    have hformula := whole_line_solution_formula A z hz (s - c * t) s
    have ht : s - (s - c * t) = c * t := by ring
    rw [ht] at hformula
    have hcomm := ((spectral_projections_commute A hA stable).2 (c * t)).eq
    have happ := congrArg (fun L : Module.End ℝ (n → ℝ) => L (z (s - c * t))) hcomm
    change P ((matrixExp A (c * t)).mulVec (z (s - c * t))) =
      (matrixExp A (c * t)).mulVec (P (z (s - c * t))) at happ
    rw [hformula]
    rw [happ]
    rw [pi_matrixOperator_action, ← Matrix.mulVec_mulVec]
    rw [projectionMatrix_mulVec]
  have hbound : ∀ t : ℝ, 0 ≤ t → ‖P (z s)‖ ≤ (C * Real.exp (-a * t)) * M := by
    intro t ht
    rw [heq t]
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply mul_le_mul (hdecay t ht) (hM (s - c * t)) (norm_nonneg _) _
    exact mul_nonneg hC (Real.exp_pos _).le
  have hlim : Tendsto (fun t : ℝ => (C * Real.exp (-a * t)) * M) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop ha)
    simpa using (tendsto_const_nhds.mul he).mul_const M
  apply norm_eq_zero.mp
  exact le_antisymm (ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, hbound⟩)) (norm_nonneg _)

lemma bounded_coordinate_solution_zero (A : Matrix n n ℝ) (hA : IsHyperbolic A)
    (z : ℝ → n → ℝ) (hz : ∀ t, HasDerivAt z (A.mulVec (z t)) t)
    (hbounded : ∃ M : ℝ, ∀ t, ‖z t‖ ≤ M) : ∀ t, z t = 0 := by
  intro t
  have hs := bounded_solution_projection_zero A hA z hz hbounded true 1
    (by intro μ hμ; simpa using hμ) t
  have hu := bounded_solution_projection_zero A hA z hz hbounded false (-1)
    (by intro μ hμ; simp only [Bool.false_eq_true, ↓reduceIte] at hμ; linarith) t
  have hsum := congrArg (fun P : Module.End ℝ (n → ℝ) => P (z t))
    (spectral_projection_laws A hA).1
  simpa only [LinearMap.add_apply, Module.End.one_apply, hs, hu, add_zero] using hsum.symm

/-- Every bounded whole-line solution of a hyperbolic constant equation vanishes,
in any fixed finite-dimensional norm. -/
theorem bounded_homogeneous_solution_zero : Specs.D13Unified.Ch20.Dichotomy.boundedSolutionType := by
  intro n _ _ E _ _ _ b A hA z hz hbounded t
  let e := b.equivFunL
  have hy : ∀ s, HasDerivAt (fun r => e (z r)) (A.mulVec (e (z s))) s := by
    intro s
    have h := e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hz s)
    simpa only [Function.comp_def] using
      (matrixOperator_action b A (z s)) ▸ h
  have hybound : ∃ M : ℝ, ∀ s, ‖e (z s)‖ ≤ M := by
    obtain ⟨M, hM⟩ := hbounded
    refine ⟨‖e.toContinuousLinearMap‖ * M, fun s => ?_⟩
    exact (e.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hM s) (norm_nonneg _))
  apply e.injective
  simpa only [map_zero] using bounded_coordinate_solution_zero A hA (fun r => e (z r)) hy hybound t

end D13Unified.Ch20
