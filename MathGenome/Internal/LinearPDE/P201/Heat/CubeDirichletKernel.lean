import MathGenome.Internal.LinearPDE.P201Specs.Heat.CubeDirichletKernel
import MathGenome.Internal.LinearPDE.P201.Heat.StrongMaximum
import MathGenome.Internal.LinearPDE.P201.Heat.ClassicalMaximum
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import MathGenome.Internal.FourierSobolev.P102.U3.PoissonSummation
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory Function
open scoped Topology ContDiff
namespace P201.Heat.Cube
open P201Specs.Heat.Cube (Mode KernelPoint)

abbrev cube : P201Specs.Heat.Cube.cubeType := @P201Specs.Heat.Cube.cube
abbrev closedCube : P201Specs.Heat.Cube.cubeType := @P201Specs.Heat.Cube.closedCube
abbrev innerCube : P201Specs.Heat.Cube.innerCubeType := @P201Specs.Heat.Cube.innerCube
abbrev sineMode : P201Specs.Heat.Cube.sineModeType := @P201Specs.Heat.Cube.sineMode
abbrev eigenvalue : P201Specs.Heat.Cube.eigenvalueType := @P201Specs.Heat.Cube.eigenvalue
abbrev kernelTerm : P201Specs.Heat.Cube.kernelTermType := @P201Specs.Heat.Cube.kernelTerm
abbrev cubeKernel : P201Specs.Heat.Cube.cubeKernelType := @P201Specs.Heat.Cube.cubeKernel
abbrev kernelSolution : P201Specs.Heat.Cube.kernelSolutionType :=
  @P201Specs.Heat.Cube.kernelSolution

/-- A finite product of independent nonnegative summable sequences is summable
on the full frequency lattice. -/
lemma summable_mode_product (n : ℕ) (f : ℕ → ℝ) (hf : Summable f)
    (hpos : ∀ j, 0 ≤ f j) : Summable (fun m : Mode n => ∏ j, f (m j)) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).summable_iff]
    simpa [Fin.prod_univ_succ, Fin.consEquiv, Function.comp_def] using
      hf.mul_of_nonneg ih hpos (fun m => Finset.prod_nonneg (fun j _ => hpos (m j)))

lemma abs_sineMode_le_one {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n)
    (m : Mode n) (x : P201Specs.Space n) : |sineMode ℓ a m x| ≤ 1 := by
  unfold sineMode P201Specs.Heat.Cube.sineMode
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => Real.abs_sin_le_one _)

lemma eigenvalue_nonneg {n : ℕ} (ℓ : ℝ) (m : Mode n) : 0 ≤ eigenvalue ℓ m := by
  unfold eigenvalue P201Specs.Heat.Cube.eigenvalue
  positivity

/-- The Gaussian lattice weight is bounded by a product of geometric weights. -/
lemma exp_eigenvalue_le_product {n : ℕ} {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (m : Mode n) :
    Real.exp (-eigenvalue ℓ m * s) ≤
      ∏ j, Real.exp (-(Real.pi ^ 2 / ℓ ^ 2 * s)) ^ (m j + 1) := by
  have hc : 0 ≤ Real.pi ^ 2 / ℓ ^ 2 * s := by positivity
  have hm : (∑ j, ((m j : ℝ) + 1)) ≤ ∑ j, ((m j : ℝ) + 1) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    have : 0 ≤ (m j : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc
    Real.exp (-eigenvalue ℓ m * s) ≤
        Real.exp (∑ j, (-(Real.pi ^ 2 / ℓ ^ 2 * s)) * ((m j : ℝ) + 1)) := by
      apply Real.exp_le_exp.mpr
      simp only [eigenvalue, P201Specs.Heat.Cube.eigenvalue,
        ← Finset.mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left hm hc]
    _ = _ := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro j _
      rw [show (m j : ℝ) + 1 = ((m j + 1 : ℕ) : ℝ) by simp]
      rw [mul_comm (-(Real.pi ^ 2 / ℓ ^ 2 * s))]
      exact Real.exp_nat_mul _ _

lemma summable_exp_eigenvalue {n : ℕ} {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) :
    Summable (fun m : Mode n => Real.exp (-eigenvalue ℓ m * s)) := by
  let q := Real.exp (-(Real.pi ^ 2 / ℓ ^ 2 * s))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  have hgeom : Summable (fun k : ℕ => q ^ (k + 1)) := by
    simpa only [pow_succ] using (summable_geometric_of_lt_one hq0.le hq1).mul_right q
  exact (summable_mode_product n _ hgeom (fun k => by positivity)).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le) (exp_eigenvalue_le_product hℓ hs)

lemma norm_kernelTerm_le {n : ℕ} {ℓ s τ : ℝ} (hℓ : 0 < ℓ) (hsτ : s ≤ τ)
    (a : P201Specs.Space n) (m : Mode n) (x y : P201Specs.Space n) :
    ‖kernelTerm ℓ a m (x, y, τ)‖ ≤
      (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * s) := by
  have hC : 0 ≤ (2 / ℓ) ^ n := by positivity
  have he : 0 ≤ Real.exp (-eigenvalue ℓ m * τ) := (Real.exp_pos _).le
  have he_le : Real.exp (-eigenvalue ℓ m * τ) ≤ Real.exp (-eigenvalue ℓ m * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [eigenvalue_nonneg ℓ m]
  simp only [kernelTerm, P201Specs.Heat.Cube.kernelTerm, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg hC, abs_of_pos (Real.exp_pos _)]
  calc
    (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * τ) * |sineMode ℓ a m x| *
        |sineMode ℓ a m y| ≤ (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * τ) * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (abs_sineMode_le_one ℓ a m x)
        (mul_nonneg hC he)) (abs_sineMode_le_one ℓ a m y) (abs_nonneg _) (by positivity)
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left he_le hC

/-- Absolute convergence at every positive time, for all ambient spatial points. -/
lemma kernel_summable {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x y : P201Specs.Space n) : Summable (fun m : Mode n => kernelTerm ℓ a m (x,y,τ)) := by
  apply Summable.of_norm
  exact ((summable_exp_eigenvalue hℓ hτ).mul_left ((2 / ℓ) ^ n)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun m => norm_kernelTerm_le hℓ le_rfl a m x y)

/-- Uniform convergence on the entire spatial space when time is bounded below. -/
lemma kernel_uniform {n : ℕ} {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (a : P201Specs.Space n) :
    TendstoUniformlyOn
      (fun F : Finset (Mode n) => fun z : KernelPoint n => ∑ m ∈ F, kernelTerm ℓ a m z)
      (fun z => cubeKernel ℓ a z.2.2 z.1 z.2.1) atTop {z | s ≤ z.2.2} := by
  apply tendstoUniformlyOn_tsum ((summable_exp_eigenvalue hℓ hs).mul_left ((2 / ℓ) ^ n))
  intro m z hz
  exact norm_kernelTerm_le hℓ hz a m z.1 z.2.1

lemma continuous_kernelTerm {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) (m : Mode n) :
    Continuous (kernelTerm ℓ a m) := by
  change Continuous (fun z : KernelPoint n => (2 / ℓ) ^ n *
    Real.exp (-eigenvalue ℓ m * z.2.2) * sineMode ℓ a m z.1 * sineMode ℓ a m z.2.1)
  simp only [sineMode, P201Specs.Heat.Cube.sineMode]
  fun_prop

lemma kernel_continuousOn_slab {n : ℕ} {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (a : P201Specs.Space n) :
    ContinuousOn (fun z : KernelPoint n => cubeKernel ℓ a z.2.2 z.1 z.2.1)
      {z | s ≤ z.2.2} := by
  exact continuousOn_tsum (fun m => (continuous_kernelTerm ℓ a m).continuousOn)
    ((summable_exp_eigenvalue hℓ hs).mul_left ((2 / ℓ) ^ n))
    (fun m z hz => norm_kernelTerm_le hℓ hz a m z.1 z.2.1)

lemma kernel_continuousAt {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a : P201Specs.Space n)
    {z : KernelPoint n} (hz : 0 < z.2.2) :
    ContinuousAt (fun w : KernelPoint n => cubeKernel ℓ a w.2.2 w.1 w.2.1) z := by
  apply (kernel_continuousOn_slab hℓ (half_pos hz) a z (by dsimp; linarith)).continuousAt
  have hmem : {w : KernelPoint n | z.2.2 / 2 < w.2.2} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by dsimp; linarith)
  exact Filter.mem_of_superset hmem (fun w hw => (show z.2.2 / 2 < w.2.2 from hw).le)

lemma sineMode_zero_of_face {n : ℕ} {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (a : P201Specs.Space n) (m : Mode n) (x : P201Specs.Space n)
    (j : Fin n) (hx : x j = a j ∨ x j = a j + ℓ) : sineMode ℓ a m x = 0 := by
  unfold sineMode P201Specs.Heat.Cube.sineMode
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rcases hx with hx | hx
  · simp [hx]
  · rw [hx]
    have heq : ((m j : ℝ) + 1) * Real.pi * (a j + ℓ - a j) / ℓ =
        ((m j + 1 : ℕ) : ℝ) * Real.pi := by push_cast; field_simp; ring
    rw [heq, Real.sin_nat_mul_pi]

lemma sineMode_zero_of_boundary {n : ℕ} {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (a : P201Specs.Space n) (m : Mode n) (x : P201Specs.Space n)
    (hx : x ∈ closedCube ℓ a \ cube ℓ a) : sineMode ℓ a m x = 0 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp hx.2
  have hface : x j = a j ∨ x j = a j + ℓ := by
    have hc := hx.1 j
    by_cases hleft : a j < x j
    · exact Or.inr (le_antisymm hc.2 (le_of_not_gt (fun hright => hj ⟨hleft, hright⟩)))
    · exact Or.inl (le_antisymm (le_of_not_gt hleft) hc.1)
  exact sineMode_zero_of_face hℓ a m x j hface

lemma kernel_symm {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) (τ : ℝ)
    (x y : P201Specs.Space n) : cubeKernel ℓ a τ x y = cubeKernel ℓ a τ y x := by
  unfold cubeKernel P201Specs.Heat.Cube.cubeKernel
  apply tsum_congr
  intro m
  simp only [P201Specs.Heat.Cube.kernelTerm]
  ring

/-- Vanishing on every lateral face, in either spatial variable. -/
theorem kernelBoundary : P201Specs.Heat.Cube.kernelBoundaryStatement := by
  intro n _ ℓ hℓ a τ _ x y hxy
  simp only [P201Specs.Heat.Cube.cubeKernel]
  suffices hz : ∀ m : Mode n, P201Specs.Heat.Cube.kernelTerm ℓ a m (x,y,τ) = 0 by
    simp only [hz, tsum_zero]
  intro m
  rcases hxy with hx | hy
  · have hzero := sineMode_zero_of_boundary hℓ.ne' a m x hx
    simp only [P201Specs.Heat.Cube.kernelTerm, hzero, mul_zero, zero_mul]
  · have hzero := sineMode_zero_of_boundary hℓ.ne' a m y hy
    simp only [P201Specs.Heat.Cube.kernelTerm, hzero, mul_zero]

/-- Coordinatewise closed cubes are compact for the canonical Euclidean norm. -/
lemma closedCube_isCompact {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) :
    IsCompact (closedCube ℓ a) := by
  have hc := isCompact_univ_pi (fun j : Fin n =>
    (isCompact_Icc : IsCompact (Icc (a j) (a j + ℓ))))
  have he := (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr hc
  convert he using 1
  ext x
  simp only [closedCube, P201Specs.Heat.Cube.closedCube, mem_ofPred_eq, mem_preimage,
    Set.mem_pi, Set.mem_univ, forall_const, mem_Icc]
  rfl

lemma cube_subset_closedCube {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) :
    cube ℓ a ⊆ closedCube ℓ a := by
  intro x hx j
  exact ⟨(hx j).1.le, (hx j).2.le⟩

lemma cube_isOpen {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) : IsOpen (cube ℓ a) := by
  change IsOpen {x : P201Specs.Space n | ∀ j, a j < x j ∧ x j < a j + ℓ}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  have hev : Continuous (fun x : P201Specs.Space n => x j) := by fun_prop
  exact (isOpen_lt (continuous_const : Continuous (fun _ : P201Specs.Space n => a j)) hev).inter
    (isOpen_lt hev (continuous_const : Continuous (fun _ : P201Specs.Space n => a j + ℓ)))

lemma kernel_continuous_fixed_time {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a : P201Specs.Space n) :
    Continuous (fun p : P201Specs.Space n × P201Specs.Space n => cubeKernel ℓ a τ p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hm : Continuous (fun q : P201Specs.Space n × P201Specs.Space n =>
      (q.1, q.2, τ)) := by fun_prop
  exact (kernel_continuousAt hℓ a (z := (p.1,p.2,τ)) hτ).comp (f := fun q : P201Specs.Space n × P201Specs.Space n => (q.1,q.2,τ)) hm.continuousAt

/-- The displayed integral is genuinely integrable, including for continuous
initial data that do not vanish at the boundary. -/
theorem kernelIntegral : P201Specs.Heat.Cube.kernelIntegralStatement := by
  intro n _ ℓ hℓ a g hg τ hτ x
  have hc := (kernel_continuous_fixed_time hℓ hτ a).comp
    (show Continuous (fun y : P201Specs.Space n => (x,y)) by fun_prop)
  have hi : IntegrableOn (fun y => cubeKernel ℓ a τ x y * g y)
      (closedCube ℓ a) (P201Specs.spatialMeasure n) :=
    @ContinuousOn.integrableOn_compact (P201Specs.Space n) ℝ _ _ _
      (P201Specs.spatialMeasure n) _ (closedCube ℓ a)
      (fun y => cubeKernel ℓ a τ x y * g y) _ _ (closedCube_isCompact ℓ a)
      (hc.continuousOn.mul hg)
  exact hi.mono_set (cube_subset_closedCube ℓ a)

/-- Every first sine mode is positive throughout the open cube. -/
lemma first_sineMode_pos {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a x : P201Specs.Space n)
    (hx : x ∈ cube ℓ a) : 0 < sineMode ℓ a (fun _ => 0) x := by
  unfold sineMode P201Specs.Heat.Cube.sineMode
  apply Finset.prod_pos
  intro j _
  simp only [Nat.cast_zero, zero_add, one_mul]
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr (hx j).1)) hℓ
  · apply (div_lt_iff₀ hℓ).mpr
    nlinarith [(hx j).2, Real.pi_pos]

/-- Polynomial factors from time differentiation can be absorbed by losing
half the Gaussian exponential decay. -/
lemma pow_mul_exp_le {u s : ℝ} (hu : 0 ≤ u) (hs : 0 < s) (k : ℕ) :
    u ^ k * Real.exp (-u * s) ≤
      ((k.factorial : ℝ) / (s / 2) ^ k) * Real.exp (-u * (s / 2)) := by
  have hr : 0 < (s / 2) ^ k := pow_pos (half_pos hs) k
  have hb := Real.pow_div_factorial_le_exp (u * (s / 2)) (mul_nonneg hu (half_pos hs).le) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hb' : u ^ k ≤ ((k.factorial : ℝ) / (s / 2) ^ k) * Real.exp (u * (s / 2)) := by
    have hp : (u * (s / 2)) ^ k ≤ Real.exp (u * (s / 2)) * k.factorial :=
      (div_le_iff₀ hfac).mp hb
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).mpr
    simpa only [mul_pow, mul_comm] using hp
  calc
    u ^ k * Real.exp (-u * s) ≤
        (((k.factorial : ℝ) / (s / 2) ^ k) * Real.exp (u * (s / 2))) *
          Real.exp (-u * s) := mul_le_mul_of_nonneg_right hb' (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

lemma summable_eigenvalue_pow_exp {n : ℕ} {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (k : ℕ) : Summable (fun m : Mode n => eigenvalue ℓ m ^ k *
      Real.exp (-eigenvalue ℓ m * s)) := by
  exact ((summable_exp_eigenvalue hℓ (half_pos hs)).mul_left
    ((k.factorial : ℝ) / (s / 2) ^ k)).of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (eigenvalue_nonneg ℓ m) k) (Real.exp_pos _).le)
      (fun m => pow_mul_exp_le (eigenvalue_nonneg ℓ m) hs k)

lemma contDiff_kernelTerm {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) (m : Mode n) :
    ContDiff ℝ ∞ (kernelTerm ℓ a m) := by
  change ContDiff ℝ ∞ (fun z : KernelPoint n => (2 / ℓ) ^ n *
    Real.exp (-eigenvalue ℓ m * z.2.2) * sineMode ℓ a m z.1 * sineMode ℓ a m z.2.1)
  simp only [sineMode, P201Specs.Heat.Cube.sineMode]
  fun_prop

lemma closure_cube {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a : P201Specs.Space n) :
    closure (cube ℓ a) = closedCube ℓ a := by
  let h := PiLp.homeomorph 2 (fun _ : Fin n => ℝ)
  have hr : cube ℓ a = h ⁻¹' (univ.pi (fun j => Ioo (a j) (a j + ℓ))) := by
    ext x
    simp only [cube, P201Specs.Heat.Cube.cube, mem_ofPred_eq, mem_preimage,
      Set.mem_pi, mem_univ, forall_const, mem_Ioo]
    rfl
  rw [hr, ← h.preimage_closure, closure_pi_set]
  have hc : ∀ j : Fin n, closure (Ioo (a j) (a j + ℓ)) = Icc (a j) (a j + ℓ) :=
    fun j => closure_Ioo (by linarith)
  simp_rw [hc]
  ext x
  simp only [closedCube, P201Specs.Heat.Cube.closedCube, mem_ofPred_eq, mem_preimage,
    Set.mem_pi, mem_univ, forall_const, mem_Icc]
  rfl

lemma frontier_cube {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a : P201Specs.Space n) :
    frontier (cube ℓ a) = closedCube ℓ a \ cube ℓ a := by
  rw [frontier, closure_cube hℓ, (cube_isOpen ℓ a).interior_eq]

lemma cube_convex {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) : Convex ℝ (cube ℓ a) := by
  intro x hx y hy u v hu hv huv j
  have hj := (convex_Ioo (a j) (a j + ℓ) : Convex ℝ (Ioo (a j) (a j + ℓ)))
    (hx j) (hy j) hu hv huv
  simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mem_Ioo] using hj

lemma iteratedDeriv_kernelTerm_time {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n)
    (m : Mode n) (x y : P201Specs.Space n) (τ : ℝ) (k : ℕ) :
    iteratedDeriv k (fun t => kernelTerm ℓ a m (x,y,t)) τ =
      (-eigenvalue ℓ m) ^ k * kernelTerm ℓ a m (x,y,τ) := by
  simp only [kernelTerm, P201Specs.Heat.Cube.kernelTerm]
  rw [iteratedDeriv_mul_const_field, iteratedDeriv_mul_const_field,
    iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  ring

lemma norm_iteratedDeriv_kernelTerm_time_le {n : ℕ} {ℓ s τ : ℝ} (hℓ : 0 < ℓ)
    (hsτ : s ≤ τ) (a : P201Specs.Space n) (m : Mode n)
    (x y : P201Specs.Space n) (k : ℕ) :
    ‖iteratedDeriv k (fun t => kernelTerm ℓ a m (x,y,t)) τ‖ ≤
      (2 / ℓ) ^ n * (eigenvalue ℓ m ^ k * Real.exp (-eigenvalue ℓ m * s)) := by
  rw [iteratedDeriv_kernelTerm_time, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg (eigenvalue_nonneg ℓ m)]
  have hb := mul_le_mul_of_nonneg_left (norm_kernelTerm_le hℓ hsτ a m x y)
    (pow_nonneg (eigenvalue_nonneg ℓ m) k)
  convert hb using 1; ring

/-- Every time-differentiated series converges uniformly away from time zero. -/
lemma kernel_time_derivatives_uniform {n : ℕ} {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (a : P201Specs.Space n) (k : ℕ) :
    TendstoUniformlyOn
      (fun F : Finset (Mode n) => fun z : KernelPoint n =>
        ∑ m ∈ F, iteratedDeriv k (fun t => kernelTerm ℓ a m (z.1,z.2.1,t)) z.2.2)
      (fun z => ∑' m : Mode n,
        iteratedDeriv k (fun t => kernelTerm ℓ a m (z.1,z.2.1,t)) z.2.2)
      atTop {z | s ≤ z.2.2} := by
  apply tendstoUniformlyOn_tsum
    ((summable_eigenvalue_pow_exp hℓ hs k).mul_left ((2 / ℓ) ^ n))
  intro m z hz
  exact norm_iteratedDeriv_kernelTerm_time_le hℓ hz a m z.1 z.2.1 k

lemma innerCube_isCompact {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) (δ : ℝ) :
    IsCompact (innerCube ℓ a δ) := by
  have hc := isCompact_univ_pi (fun j : Fin n =>
    (isCompact_Icc : IsCompact (Icc (a j + δ) (a j + ℓ - δ))))
  have he := (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr hc
  convert he using 1
  ext x
  simp only [innerCube, P201Specs.Heat.Cube.innerCube, mem_ofPred_eq, mem_preimage,
    Set.mem_pi, Set.mem_univ, forall_const, mem_Icc]
  rfl

lemma innerCube_subset_cube {n : ℕ} {ℓ δ : ℝ} (hδ : 0 < δ) (a : P201Specs.Space n) :
    innerCube ℓ a δ ⊆ cube ℓ a := by
  intro x hx j
  have hj := hx j
  constructor <;> linarith

lemma innerCube_nonempty {n : ℕ} {ℓ δ : ℝ} (hδ : 2 * δ ≤ ℓ)
    (a : P201Specs.Space n) : (innerCube ℓ a δ).Nonempty := by
  let x : P201Specs.Space n := WithLp.toLp 2 (fun j => a j + ℓ / 2)
  refine ⟨x, ?_⟩
  intro j
  change a j + δ ≤ a j + ℓ / 2 ∧ a j + ℓ / 2 ≤ a j + ℓ - δ
  constructor <;> linarith

/-- Compactness stage of the source argument. This implication alone is not a
proof of positivity: its premise is an outstanding, separately specified theorem. -/
lemma kernelLowerBound_of_positive (hpos : P201Specs.Heat.Cube.kernelPositiveStatement) :
    P201Specs.Heat.Cube.kernelLowerBoundStatement := by
  intro n hn ℓ hℓ a Kx Ky hKx hKxQ hKy hKyQ s t hs hst
  classical
  by_cases hnx : Kx.Nonempty
  · by_cases hny : Ky.Nonempty
    · let K : Set (KernelPoint n) := Kx ×ˢ Ky ×ˢ Icc s t
      have hK : IsCompact K := hKx.prod (hKy.prod isCompact_Icc)
      have hne : K.Nonempty := hnx.prod (hny.prod (nonempty_Icc.mpr hst))
      have hc : ContinuousOn
          (fun z : KernelPoint n => cubeKernel ℓ a z.2.2 z.1 z.2.1) K := by
        intro z hz
        exact (kernel_continuousAt hℓ a (hs.trans_le hz.2.2.1)).continuousWithinAt
      obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hc
      refine ⟨cubeKernel ℓ a z.2.2 z.1 z.2.1, ?_, ?_⟩
      · exact hpos n hn ℓ hℓ a z.2.2 (hs.trans_le hz.2.2.1) z.1
          (hKxQ hz.1) z.2.1 (hKyQ hz.2.1)
      · intro τ hτ x hx y hy
        exact hmin (a := (x,y,τ)) ⟨hx, hy, hτ⟩
    · refine ⟨1, one_pos, ?_⟩
      intro τ hτ x hx y hy
      exact (hny ⟨y,hy⟩).elim
  · refine ⟨1, one_pos, ?_⟩
    intro τ hτ x hx y hy
    exact (hnx ⟨x,hx⟩).elim

theorem kernelSummable : P201Specs.Heat.Cube.kernelSummableStatement := by
  intro n _ ℓ hℓ a τ hτ x y
  exact kernel_summable hℓ hτ a x y

theorem kernelUniform : P201Specs.Heat.Cube.kernelUniformStatement := by
  intro n _ ℓ hℓ a s t hs _
  exact (kernel_uniform hℓ hs a).mono (fun _ hz => hz.2.2.1)

theorem kernelContinuous : P201Specs.Heat.Cube.kernelContinuousStatement := by
  intro n _ ℓ hℓ a z hz
  exact (kernel_continuousAt hℓ a hz).continuousWithinAt

theorem kernelTimeSeries : P201Specs.Heat.Cube.kernelTimeSeriesStatement := by
  intro n _ ℓ hℓ a s t hs _ k
  exact (kernel_time_derivatives_uniform hℓ hs a k).mono (fun _ hz => hz.2.2.1)

/-- Leibniz estimates preserve exponential bounds in derivative order. -/
lemma norm_iteratedFDeriv_mul_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : E) (k : ℕ) {C D R S : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f x‖ ≤ C * R ^ j)
    (hc : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g x‖ ≤ D * S ^ j) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤ C * D * (R + S) ^ k := by
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (C * R ^ j) * (D * S ^ (k - j)) := by
      apply (norm_iteratedFDeriv_mul_le hf hg x (by simp)).trans
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Finset.mem_range_succ_iff.mp hj
      gcongr
      · exact hb j hjk
      · exact hc (k-j) (Nat.sub_le _ _)
    _ = C * D * (R + S) ^ k := by
      rw [add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Composing a translated sine with a linear functional gives the expected
frequency power in every mixed derivative. -/
lemma norm_iteratedFDeriv_sin_affine_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) (c : ℝ) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => Real.sin (L y - c)) x‖ ≤ ‖L‖ ^ k := by
  have hs : ContDiff ℝ ∞ (fun r : ℝ => Real.sin (r-c)) := by fun_prop
  change ‖iteratedFDeriv ℝ k ((fun r : ℝ => Real.sin (r-c)) ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hs x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hb : ‖iteratedFDeriv ℝ k (fun r : ℝ => Real.sin (r-c)) (L x)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_comp_sub_const]
    exact Real.abs_iteratedDeriv_sin_le_one k _
  simpa using mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg L) k)

lemma norm_iteratedFDeriv_exp_linear_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => Real.exp (L y)) x‖ ≤ Real.exp (L x) * ‖L‖ ^ k := by
  change ‖iteratedFDeriv ℝ k (Real.exp ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (Real.contDiff_exp : ContDiff ℝ ∞ Real.exp) x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he : ‖iteratedFDeriv ℝ k Real.exp (L x)‖ = Real.exp (L x) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have h := iteratedDeriv_exp_const_mul k 1
    simp only [one_mul, one_pow] at h
    rw [h]
    exact Real.norm_of_nonneg (Real.exp_pos _).le
  rw [he]

/-- A product of oscillatory factors has derivative growth controlled by the
sum of the individual frequencies. -/
lemma norm_iteratedFDeriv_prod_bound {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq ι] (u : Finset ι) (f : ι → E → ℝ)
    (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x : E) (k : ℕ)
    (hb : ∀ i ∈ u, ∀ j ≤ k, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ R i ^ j) :
    ‖iteratedFDeriv ℝ k (fun y => ∏ i ∈ u, f i y) x‖ ≤ (∑ i ∈ u, R i) ^ k := by
  induction u using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp [norm_iteratedFDeriv_zero]
    | succ k => simp [iteratedFDeriv_succ_const]
  | @insert i u hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    have hh := norm_iteratedFDeriv_mul_bound (hf i)
      (f := f i) (g := fun y => ∏ l ∈ u, f l y) (by fun_prop) x k
      (C := 1) (D := 1) (R := R i) (S := ∑ l ∈ u, R l)
      zero_le_one zero_le_one (hR i) (Finset.sum_nonneg (fun j _ => hR j))
      (fun j hj => by simpa using hb i (Finset.mem_insert_self _ _) j hj)
      (by
        intro j hj
        simpa using (ih j (fun l hl r hr => hb l (Finset.mem_insert_of_mem hl) r (hr.trans hj))))
    simpa using hh

lemma frequency_sq_le_eigenvalue {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (m : Mode n) (j : Fin n) :
    (((m j : ℝ) + 1) * Real.pi / ℓ) ^ 2 ≤ eigenvalue ℓ m := by
  have hs : ((m j : ℝ) + 1)^2 ≤ ∑ i, ((m i : ℝ) + 1)^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ((m i : ℝ) + 1)) (Finset.mem_univ j)
  have hc : 0 ≤ Real.pi^2 / ℓ^2 := by positivity
  have hb := mul_le_mul_of_nonneg_left hs hc
  change _ ≤ Real.pi^2 / ℓ^2 * ∑ i, ((m i : ℝ)+1)^2
  convert hb using 1 <;> ring

lemma frequency_le_one_add_eigenvalue {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (m : Mode n) (j : Fin n) :
    ((m j : ℝ) + 1) * Real.pi / ℓ ≤ 1 + eigenvalue ℓ m := by
  nlinarith [frequency_sq_le_eigenvalue hℓ m j,
    sq_nonneg (((m j : ℝ) + 1) * Real.pi / ℓ - 1/2)]

/-- Sine factors in either spatial variable have all derivative orders
controlled uniformly over the ambient spatial space. -/
lemma norm_iteratedFDeriv_sineFactor_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (m : Mode n) (j : Fin n)
    (P : KernelPoint n →L[ℝ] P201Specs.Space n)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (z : KernelPoint n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w =>
      Real.sin (((m j : ℝ) + 1) * Real.pi * (P w j - a j) / ℓ)) z‖ ≤
      (1 + eigenvalue ℓ m) ^ k := by
  let q : ℝ := ((m j : ℝ) + 1) * Real.pi / ℓ
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let L : KernelPoint n →L[ℝ] ℝ := q • ((PiLp.proj 2 (fun _ : Fin n => ℝ) j).comp P)
  have heq : (fun w => Real.sin (((m j : ℝ) + 1) * Real.pi * (P w j - a j) / ℓ)) =
      (fun w => Real.sin (L w - q * a j)) := by
    ext w
    congr 1
    change _ = q * P w j - q * a j
    dsimp [q]
    ring
  rw [heq]
  apply (norm_iteratedFDeriv_sin_affine_le L (q * a j) z k).trans
  apply pow_le_pow_left₀ (norm_nonneg L)
  apply le_trans (L.opNorm_le_bound hq ?_) (frequency_le_one_add_eigenvalue hℓ m j)
  intro w
  change ‖q * P w j‖ ≤ q * ‖w‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hq]
  exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (P w) j).trans (hP w)) hq

lemma norm_iteratedFDeriv_sineMode_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (m : Mode n)
    (P : KernelPoint n →L[ℝ] P201Specs.Space n)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (z : KernelPoint n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w => sineMode ℓ a m (P w)) z‖ ≤
      ((n : ℝ) * (1 + eigenvalue ℓ m)) ^ k := by
  unfold sineMode P201Specs.Heat.Cube.sineMode
  have hb := norm_iteratedFDeriv_prod_bound Finset.univ
    (fun j w => Real.sin (((m j : ℝ) + 1) * Real.pi * (P w j - a j) / ℓ))
    (fun _ => 1 + eigenvalue ℓ m) (fun _ => by linarith [eigenvalue_nonneg ℓ m])
    (fun _ => by fun_prop) z k
    (fun j _ r _ => norm_iteratedFDeriv_sineFactor_le hℓ a m j P hP z r)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hb

lemma norm_iteratedFDeriv_kernelTerm_le {n : ℕ} {ℓ s : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (m : Mode n) (z : KernelPoint n)
    (hz : s ≤ z.2.2) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (kernelTerm ℓ a m) z‖ ≤
      (2 / ℓ)^n * Real.exp (-eigenvalue ℓ m * s) *
        (((1 + 2 * n : ℝ) * (1 + eigenvalue ℓ m)) ^ k) := by
  let Px : KernelPoint n →L[ℝ] P201Specs.Space n := ContinuousLinearMap.fst ℝ _ _
  let Py : KernelPoint n →L[ℝ] P201Specs.Space n :=
    (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  let Pt : KernelPoint n →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  have hPx : ∀ w, ‖Px w‖ ≤ ‖w‖ := fun w => norm_fst_le w
  have hPy : ∀ w, ‖Py w‖ ≤ ‖w‖ := fun w => (norm_fst_le w.2).trans (norm_snd_le w)
  have hPt : ∀ w, ‖Pt w‖ ≤ ‖w‖ := fun w => (norm_snd_le w.2).trans (norm_snd_le w)
  let L := (-eigenvalue ℓ m) • Pt
  have hL : ‖L‖ ≤ eigenvalue ℓ m := by
    apply L.opNorm_le_bound (eigenvalue_nonneg ℓ m)
    intro w
    change ‖(-eigenvalue ℓ m) * Pt w‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (eigenvalue_nonneg ℓ m)]
    exact mul_le_mul_of_nonneg_left (hPt w) (eigenvalue_nonneg ℓ m)
  have hE (r : ℕ) : ‖iteratedFDeriv ℝ r (fun w => Real.exp (L w)) z‖ ≤
      Real.exp (-eigenvalue ℓ m * z.2.2) * (1 + eigenvalue ℓ m)^r := by
    apply (norm_iteratedFDeriv_exp_linear_le L z r).trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact pow_le_pow_left₀ (norm_nonneg L) (hL.trans (by linarith)) r
  have hR : 0 ≤ 1 + eigenvalue ℓ m := by linarith [eigenvalue_nonneg ℓ m]
  have hxy (r : ℕ) :
      ‖iteratedFDeriv ℝ r (fun w => sineMode ℓ a m (Px w) * sineMode ℓ a m (Py w)) z‖ ≤
        (2 * (n : ℝ) * (1 + eigenvalue ℓ m)) ^ r := by
    have h := norm_iteratedFDeriv_mul_bound
      (f := fun w => sineMode ℓ a m (Px w)) (g := fun w => sineMode ℓ a m (Py w))
      (R := (n : ℝ) * (1 + eigenvalue ℓ m)) (S := (n : ℝ) * (1 + eigenvalue ℓ m))
      (by unfold sineMode P201Specs.Heat.Cube.sineMode; fun_prop)
      (by unfold sineMode P201Specs.Heat.Cube.sineMode; fun_prop) z r
      (C := 1) (D := 1) (hC := zero_le_one) (hD := zero_le_one)
      (hR := by positivity) (hS := by positivity)
      (fun i _ => by simpa using norm_iteratedFDeriv_sineMode_le hℓ a m Px hPx z i)
      (fun i _ => by simpa using norm_iteratedFDeriv_sineMode_le hℓ a m Py hPy z i)
    convert h using 1 <;> ring
  have hb := norm_iteratedFDeriv_mul_bound
    (f := fun w => Real.exp (L w))
    (g := fun w => sineMode ℓ a m (Px w) * sineMode ℓ a m (Py w))
    (R := 1 + eigenvalue ℓ m) (S := 2 * (n : ℝ) * (1 + eigenvalue ℓ m)) (by fun_prop)
    (by unfold sineMode P201Specs.Heat.Cube.sineMode; fun_prop) z k
    (C := Real.exp (-eigenvalue ℓ m * z.2.2)) (D := 1)
    (hC := (Real.exp_pos _).le) (hD := zero_le_one) (hR := by positivity)
    (hS := by positivity) (fun i _ => hE i) (fun i _ => by simpa using hxy i)
  have hid : kernelTerm ℓ a m = fun w => (2/ℓ)^n •
      (Real.exp (L w) * (sineMode ℓ a m (Px w) * sineMode ℓ a m (Py w))) := by
    ext w
    change (2/ℓ)^n * Real.exp (-eigenvalue ℓ m * w.2.2) * sineMode ℓ a m w.1 * sineMode ℓ a m w.2.1 =
      (2/ℓ)^n * (Real.exp (-eigenvalue ℓ m * w.2.2) * (sineMode ℓ a m w.1 * sineMode ℓ a m w.2.1))
    ring
  rw [hid, iteratedFDeriv_const_smul_apply' (by unfold sineMode P201Specs.Heat.Cube.sineMode; fun_prop), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (2/ℓ)^n by positivity)]
  have he : Real.exp (-eigenvalue ℓ m * z.2.2) ≤ Real.exp (-eigenvalue ℓ m * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [eigenvalue_nonneg ℓ m]
  have hb' : ‖iteratedFDeriv ℝ k
      (fun w => Real.exp (L w) * (sineMode ℓ a m (Px w) * sineMode ℓ a m (Py w))) z‖ ≤
      Real.exp (-eigenvalue ℓ m * s) * (((1 + 2 * n : ℝ) * (1 + eigenvalue ℓ m)) ^ k) := by
    apply hb.trans
    convert mul_le_mul_of_nonneg_right he (pow_nonneg
      (show 0 ≤ (1 + 2 * n : ℝ) * (1 + eigenvalue ℓ m) by positivity) k) using 1 <;> ring
  convert mul_le_mul_of_nonneg_left hb' (show 0 ≤ (2/ℓ)^n by positivity) using 1 <;> ring

/-- Every fixed polynomial in the eigenvalue is summable against positive
heat decay. -/
lemma summable_one_add_eigenvalue_pow_exp {n : ℕ} {ℓ s : ℝ}
    (hℓ : 0 < ℓ) (hs : 0 < s) (k : ℕ) :
    Summable (fun m : Mode n => (1 + eigenvalue ℓ m)^k *
      Real.exp (-eigenvalue ℓ m * s)) := by
  have h := summable_sum (s := Finset.range (k + 1))
    (fun j _ => (summable_eigenvalue_pow_exp (n := n) hℓ hs j).mul_left (k.choose j : ℝ))
  convert h using 1
  ext m
  rw [add_comm 1 (eigenvalue ℓ m), add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_pow, mul_one]
  ring

lemma summable_kernelTerm_derivative_bound {n : ℕ} {ℓ s : ℝ}
    (hℓ : 0 < ℓ) (hs : 0 < s) (k : ℕ) :
    Summable (fun m : Mode n =>
      (2 / ℓ)^n * Real.exp (-eigenvalue ℓ m * s) *
        (((1 + 2 * n : ℝ) * (1 + eigenvalue ℓ m)) ^ k)) := by
  convert (summable_one_add_eigenvalue_pow_exp hℓ hs k).mul_left
    ((2 / ℓ)^n * (1 + 2 * n : ℝ)^k) using 1
  ext m
  rw [mul_pow]
  ring

lemma kernel_mixed_derivatives_summable {n : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (a : P201Specs.Space n) (z : KernelPoint n)
    (hz : 0 < z.2.2) (k : ℕ) :
    Summable (fun m : Mode n => iteratedFDeriv ℝ k (kernelTerm ℓ a m) z) := by
  haveI : CompleteSpace (KernelPoint n [×k]→L[ℝ] ℝ) :=
    ContinuousMultilinearMap.instCompleteSpace
  exact (summable_kernelTerm_derivative_bound hℓ hz k).of_norm_bounded
    (fun m => norm_iteratedFDeriv_kernelTerm_le hℓ a m z le_rfl k)

/-- All mixed derivative series converge uniformly even when only a positive
lower bound on time is imposed. -/
lemma kernel_mixed_derivatives_uniform {n : ℕ} {ℓ s : ℝ}
    (hℓ : 0 < ℓ) (hs : 0 < s) (a : P201Specs.Space n) (k : ℕ) :
    TendstoUniformlyOn
      (fun F : Finset (Mode n) => fun z : KernelPoint n =>
        ∑ m ∈ F, iteratedFDeriv ℝ k (kernelTerm ℓ a m) z)
      (fun z => ∑' m : Mode n, iteratedFDeriv ℝ k (kernelTerm ℓ a m) z)
      atTop {z | s ≤ z.2.2} := by
  haveI : CompleteSpace (KernelPoint n [×k]→L[ℝ] ℝ) :=
    ContinuousMultilinearMap.instCompleteSpace
  exact tendstoUniformlyOn_tsum (summable_kernelTerm_derivative_bound hℓ hs k)
    (fun m z hz => norm_iteratedFDeriv_kernelTerm_le hℓ a m z hz k)

theorem kernelSeries : P201Specs.Heat.Cube.kernelSeriesStatement := by
  intro n _ ℓ hℓ a s t hs _ k
  constructor
  · intro z hz
    exact kernel_mixed_derivatives_summable hℓ a z (hs.trans_le hz.2.2.1) k
  · exact (kernel_mixed_derivatives_uniform hℓ hs a k).mono (fun _ hz => hz.2.2.1)

lemma hasFDerivAt_tsum_on_open {α E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : α → E → F} {s : Set E} {u : α → ℝ} (hs : IsOpen s)
    (hu : Summable u) (hf : ∀ i, Differentiable ℝ (f i))
    (hb : ∀ i x, x ∈ s → ‖fderiv ℝ (f i) x‖ ≤ u i)
    (h0 : ∀ x ∈ s, Summable (fun i => f i x)) {x : E} (hx : x ∈ s) :
    HasFDerivAt (fun y => ∑' i, f i y) (∑' i, fderiv ℝ (f i) x) x := by
  classical
  apply hasFDerivAt_of_tendstoUniformlyOn hs (tendstoUniformlyOn_tsum hu hb)
    (fun t y _ => HasFDerivAt.fun_sum (fun i _ => (hf i y).hasFDerivAt))
    (fun y hy => (h0 y hy).hasSum) hx

lemma iteratedFDeriv_tsum_on_open {α E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : α → E → F} {s : Set E} {v : ℕ → α → ℝ} (hs : IsOpen s)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k i x, x ∈ s → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i)
    (k : ℕ) {x : E} (hx : x ∈ s) :
    iteratedFDeriv ℝ k (fun y => ∑' i, f i y) x =
      ∑' i, iteratedFDeriv ℝ k (f i) x := by
  have hsum (r : ℕ) (y : E) (hy : y ∈ s) :
      Summable (fun i => iteratedFDeriv ℝ r (f i) y) :=
    .of_norm_bounded (hv r) (fun i => hb r i y hy)
  induction k generalizing x with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k ih =>
    have heq : iteratedFDeriv ℝ k (fun y => ∑' i, f i y) =ᶠ[𝓝 x]
        (fun y => ∑' i, iteratedFDeriv ℝ k (f i) y) :=
      Filter.eventually_of_mem (hs.mem_nhds hx) (fun y hy => ih hy)
    have hd := hasFDerivAt_tsum_on_open hs (hv (k+1))
      (fun i => (hf i).differentiable_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top k)))
      (fun i y hy => by rw [norm_fderiv_iteratedFDeriv]; exact hb (k+1) i y hy)
      (hsum k) hx
    rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, heq.fderiv_eq, hd.fderiv]
    simp_rw [iteratedFDeriv_succ_eq_comp_left, comp_apply]
    exact (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (k+1) => E) F).symm.toContinuousLinearEquiv.map_tsum

lemma contDiffOn_tsum_on_open {α E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : α → E → F} {s : Set E} {v : ℕ → α → ℝ} (hs : IsOpen s)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k i x, x ∈ s → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i) :
    ContDiffOn ℝ ∞ (fun x => ∑' i, f i x) s := by
  have heq (k : ℕ) : EqOn (iteratedFDerivWithin ℝ k (fun x => ∑' i, f i x) s)
      (fun x => ∑' i, iteratedFDeriv ℝ k (f i) x) s := by
    intro x hx
    rw [iteratedFDerivWithin_of_isOpen k hs hx]
    exact iteratedFDeriv_tsum_on_open hs hf hv hb k hx
  rw [contDiffOn_iff_continuousOn_differentiableOn hs.uniqueDiffOn]
  constructor
  · intro k _
    exact (continuousOn_tsum
      (fun i => ((hf i).continuous_iteratedFDeriv (by simp)).continuousOn)
      (hv k) (hb k)).congr (heq k)
  · intro k _ x hx
    have hsum (y : E) (hy : y ∈ s) :
        Summable (fun i => iteratedFDeriv ℝ k (f i) y) :=
      .of_norm_bounded (hv k) (fun i => hb k i y hy)
    have hd := hasFDerivAt_tsum_on_open hs (hv (k+1))
      (fun i => (hf i).differentiable_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top k)))
      (fun i y hy => by rw [norm_fderiv_iteratedFDeriv]; exact hb (k+1) i y hy)
      hsum hx
    exact hd.differentiableAt.differentiableWithinAt.congr
      (fun y hy => heq k hy) (heq k hx)



/-- Smoothness follows locally from the complete mixed derivative estimates.
Only a positive-time neighborhood is used, with no assertion about negative time. -/
lemma kernel_contDiffOn_halfspace {n : ℕ} {ℓ s : ℝ} (hℓ : 0 < ℓ)
    (hs : 0 < s) (a : P201Specs.Space n) :
    ContDiffOn ℝ ∞ (fun z : KernelPoint n => cubeKernel ℓ a z.2.2 z.1 z.2.1)
      {z | s < z.2.2} := by
  exact contDiffOn_tsum_on_open
    (isOpen_lt continuous_const (by fun_prop)) (contDiff_kernelTerm ℓ a)
    (fun k => summable_kernelTerm_derivative_bound hℓ hs k)
    (fun k m z hz => norm_iteratedFDeriv_kernelTerm_le hℓ a m z hz.le k)

lemma kernel_contDiffAt {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a : P201Specs.Space n)
    {z : KernelPoint n} (hz : 0 < z.2.2) :
    ContDiffAt ℝ ∞ (fun w : KernelPoint n => cubeKernel ℓ a w.2.2 w.1 w.2.1) z := by
  exact (kernel_contDiffOn_halfspace hℓ (half_pos hz) a).contDiffAt
    ((isOpen_lt continuous_const (by fun_prop)).mem_nhds (by dsimp; linarith))

theorem kernelSmooth : P201Specs.Heat.Cube.kernelSmoothStatement := by
  intro n _ ℓ hℓ a z hz
  exact (kernel_contDiffAt hℓ a hz).contDiffWithinAt

theorem kernelDerivative : P201Specs.Heat.Cube.kernelDerivativeStatement := by
  intro n _ ℓ hℓ a k z hz
  exact iteratedFDeriv_tsum_on_open (s := {w : KernelPoint n | z.2.2 / 2 < w.2.2})
    (isOpen_lt continuous_const (by fun_prop)) (contDiff_kernelTerm ℓ a)
    (fun r => summable_kernelTerm_derivative_bound hℓ (half_pos hz) r)
    (fun r m w (hw : z.2.2 / 2 < w.2.2) =>
      norm_iteratedFDeriv_kernelTerm_le hℓ a m w hw.le r)
    k (by dsimp; linarith)

lemma norm_iteratedFDeriv_comp_affine_le {E G F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (L : G →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    (c : E) (x : G) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f (L y + c)) x‖ ≤
      ‖iteratedFDeriv ℝ k f (L x + c)‖ := by
  change ‖iteratedFDeriv ℝ k ((fun y => f (y+c)) ∘ L) x‖ ≤ _
  have hfshift : ContDiff ℝ ∞ (fun y => f (y+c)) := hf.comp (by fun_prop)
  rw [L.iteratedFDeriv_comp_right hfshift x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  rw [iteratedFDeriv_comp_add_right]
  have hp : ∏ i : Fin k, ‖L‖ ≤ 1 := Finset.prod_le_one₀
    (fun _ _ => norm_nonneg L) (fun _ _ => hL)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (norm_nonneg (iteratedFDeriv ℝ k f (L x+c)))

lemma norm_iteratedFDeriv_kernelTerm_space_le {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (m : Mode n) (x y : P201Specs.Space n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w => kernelTerm ℓ a m (w,y,τ)) x‖ ≤
      (2 / ℓ)^n * Real.exp (-eigenvalue ℓ m * τ) *
        (((1 + 2 * n : ℝ) * (1 + eigenvalue ℓ m)) ^ k) := by
  let L : P201Specs.Space n →L[ℝ] KernelPoint n := ContinuousLinearMap.inl ℝ _ _
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro w
    simp [L]
  have hb := norm_iteratedFDeriv_comp_affine_le (contDiff_kernelTerm ℓ a m)
    L hL (0,y,τ) x k
  have heq : (fun w => kernelTerm ℓ a m (L w + (0,y,τ))) =
      (fun w => kernelTerm ℓ a m (w,y,τ)) := by
    ext w
    simp [L, Prod.add_def]
  rw [heq] at hb
  apply hb.trans
  simpa [L, Prod.add_def] using norm_iteratedFDeriv_kernelTerm_le hℓ a m (x,y,τ) le_rfl k

lemma kernel_time_hasDerivAt {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x y : P201Specs.Space n) :
    HasDerivAt (fun t => cubeKernel ℓ a t x y)
      (∑' m : Mode n, -eigenvalue ℓ m * kernelTerm ℓ a m (x,y,τ)) τ := by
  have hd (m : Mode n) (t : ℝ) : DifferentiableAt ℝ
      (fun t => kernelTerm ℓ a m (x,y,t)) t := by
    unfold kernelTerm P201Specs.Heat.Cube.kernelTerm
    simp only [Prod.fst, Prod.snd]
    fun_prop
  have h := hasDerivAt_tsum_of_isPreconnected
    ((summable_eigenvalue_pow_exp (n := n) hℓ (half_pos hτ) 1).mul_left ((2 / ℓ)^n))
    isOpen_Ioi (convex_Ioi (τ/2)).isPreconnected
    (fun m t _ => (hd m t).hasDerivAt)
    (fun m t ht => by simpa only [iteratedDeriv_one, pow_one] using
      norm_iteratedDeriv_kernelTerm_time_le hℓ (le_of_lt ht) a m x y 1)
    (show τ ∈ Ioi (τ/2) by change τ/2 < τ; linarith)
    (kernel_summable hℓ hτ a x y) (show τ ∈ Ioi (τ/2) by change τ/2 < τ; linarith)
  change HasDerivAt (fun t => ∑' m : Mode n, kernelTerm ℓ a m (x,y,t)) _ τ
  convert h using 1
  apply tsum_congr
  intro m
  simpa only [iteratedDeriv_one, pow_one] using
    (iteratedDeriv_kernelTerm_time ℓ a m x y τ 1).symm

lemma summable_mode_product_norm (n : ℕ) (f : Fin n → ℕ → ℝ)
    (hf : ∀ j, Summable (fun k => ‖f j k‖)) :
    Summable (fun m : Mode n => ‖∏ j, f j (m j)‖) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).summable_iff]
    simpa [Fin.prod_univ_succ, Fin.consEquiv, Function.comp_def] using
      (hf 0).mul_norm (ih (fun j => f j.succ) (fun j => hf j.succ))

lemma tsum_mode_product (n : ℕ) (f : Fin n → ℕ → ℝ)
    (hf : ∀ j, Summable (fun k => ‖f j k‖)) :
    (∑' m : Mode n, ∏ j, f j (m j)) = ∏ j, ∑' k, f j k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).tsum_eq]
    simp only [Function.comp_def, Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [← tsum_mul_tsum_of_summable_norm (hf 0)
      (summable_mode_product_norm n (fun j => f j.succ) (fun j => hf j.succ))]
    rw [ih (fun j => f j.succ) (fun j => hf j.succ)]

lemma kernel_diagonal_nonneg {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x : P201Specs.Space n) : 0 ≤ cubeKernel ℓ a τ x x := by
  apply tsum_nonneg
  intro m
  change 0 ≤ (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * τ) *
    sineMode ℓ a m x * sineMode ℓ a m x
  nlinarith [mul_nonneg (by positivity : 0 ≤ (2 / ℓ) ^ n)
    (Real.exp_pos (-eigenvalue ℓ m * τ)).le, sq_nonneg (sineMode ℓ a m x)]

lemma kernel_diagonal_pos {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x : P201Specs.Space n) (hx : x ∈ cube ℓ a) :
    0 < cubeKernel ℓ a τ x x := by
  have hterm : ∀ m : Mode n, 0 ≤ kernelTerm ℓ a m (x,x,τ) := by
    intro m
    change 0 ≤ (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * τ) *
      sineMode ℓ a m x * sineMode ℓ a m x
    convert mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2 / ℓ) ^ n)
      (Real.exp_pos (-eigenvalue ℓ m * τ)).le) (sq_nonneg (sineMode ℓ a m x)) using 1 <;> ring
  have hfirst : 0 < kernelTerm ℓ a (fun _ => 0) (x,x,τ) := by
    change 0 < (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ (fun _ => 0) * τ) *
      sineMode ℓ a (fun _ => 0) x * sineMode ℓ a (fun _ => 0) x
    exact mul_pos (mul_pos (mul_pos (by positivity) (Real.exp_pos _))
      (first_sineMode_pos hℓ a x hx)) (first_sineMode_pos hℓ a x hx)
  exact (kernel_summable hℓ hτ a x x).tsum_pos hterm (fun _ => 0) hfirst

lemma interval_weight_summable_norm {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (u v : ℝ) : Summable (fun k : ℕ => ‖Real.exp
      (-(Real.pi ^ 2 / ℓ ^ 2) * ((k : ℝ) + 1) ^ 2 * τ) *
      Real.sin (((k : ℝ) + 1) * Real.pi * u / ℓ) *
      Real.sin (((k : ℝ) + 1) * Real.pi * v / ℓ)‖) := by
  have hsum : Summable (fun k : ℕ => Real.exp
      (-(Real.pi ^ 2 / ℓ ^ 2) * ((k : ℝ) + 1) ^ 2 * τ)) := by
    have hh := (Equiv.funUnique (Fin 1) ℕ).symm.summable_iff.mpr
      (summable_exp_eigenvalue (n := 1) hℓ hτ)
    simpa [Function.comp_def, eigenvalue, P201Specs.Heat.Cube.eigenvalue,
      Equiv.funUnique, Equiv.piUnique, neg_mul] using hh
  apply hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(Real.pi ^ 2 / ℓ ^ 2) * ((k : ℝ) + 1) ^ 2 * τ) * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.exp_pos _).le)
        (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma kernel_tensor_product {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x y : P201Specs.Space n) :
    cubeKernel ℓ a τ x y = ∏ j : Fin n, ((2 / ℓ) * ∑' k : ℕ,
      Real.exp (-(Real.pi ^ 2 / ℓ ^ 2) * ((k : ℝ) + 1) ^ 2 * τ) *
      Real.sin (((k : ℝ) + 1) * Real.pi * (x j - a j) / ℓ) *
      Real.sin (((k : ℝ) + 1) * Real.pi * (y j - a j) / ℓ)) := by
  let f : Fin n → ℕ → ℝ := fun j k =>
      Real.exp (-(Real.pi ^ 2 / ℓ ^ 2) * ((k : ℝ) + 1) ^ 2 * τ) *
      Real.sin (((k : ℝ) + 1) * Real.pi * (x j - a j) / ℓ) *
      Real.sin (((k : ℝ) + 1) * Real.pi * (y j - a j) / ℓ)
  have hf : ∀ j, Summable (fun k => ‖f j k‖) :=
    fun j => interval_weight_summable_norm hℓ hτ _ _
  have hterm : ∀ m : Mode n,
      kernelTerm ℓ a m (x,y,τ) = (2 / ℓ) ^ n * ∏ j, f j (m j) := by
    intro m
    change (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * τ) *
      sineMode ℓ a m x * sineMode ℓ a m y = _
    dsimp [f]
    simp only [Finset.prod_mul_distrib]
    have hexp : Real.exp (-eigenvalue ℓ m * τ) =
        ∏ j : Fin n, Real.exp (-(Real.pi ^ 2 / ℓ ^ 2) * ((m j : ℝ) + 1) ^ 2 * τ) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [eigenvalue, P201Specs.Heat.Cube.eigenvalue,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    rw [hexp]
    simp only [sineMode, P201Specs.Heat.Cube.sineMode, mul_assoc]
  change (∑' m : Mode n, kernelTerm ℓ a m (x,y,τ)) = _
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_mode_product n f hf, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- Integer cosine modes integrate to zero unless the frequency is zero. -/
lemma interval_cos_frequency {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℤ) :
    (∫ u in (0 : ℝ)..ℓ, Real.cos ((k : ℝ) * Real.pi * u / ℓ)) =
      if k = 0 then ℓ else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hfreq : (k : ℝ) * Real.pi / ℓ ≠ 0 := by
      exact div_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hk) Real.pi_ne_zero) hℓ.ne'
    have heq : (fun u : ℝ => Real.cos ((k : ℝ) * Real.pi * u / ℓ)) =
        (fun u : ℝ => Real.cos (((k : ℝ) * Real.pi / ℓ) * u)) := by
      funext u
      congr 1
      ring
    rw [heq, intervalIntegral.integral_comp_mul_left _ hfreq, integral_cos]
    have hend : (k : ℝ) * Real.pi / ℓ * ℓ = (k : ℝ) * Real.pi := by
      field_simp
    simp [hk, hend, Real.sin_int_mul_pi]

/-- The real sine basis on an interval has the source's normalization. -/
lemma interval_sine_orthogonality {ℓ : ℝ} (hℓ : 0 < ℓ) (p q : ℕ) :
    (∫ u in (0 : ℝ)..ℓ,
      Real.sin (((p : ℝ) + 1) * Real.pi * u / ℓ) *
      Real.sin (((q : ℝ) + 1) * Real.pi * u / ℓ)) =
      if p = q then ℓ / 2 else 0 := by
  have htrig : (fun u : ℝ =>
      Real.sin (((p : ℝ) + 1) * Real.pi * u / ℓ) *
      Real.sin (((q : ℝ) + 1) * Real.pi * u / ℓ)) =
      (fun u : ℝ => (Real.cos ((((p : ℤ) - (q : ℤ) : ℤ) : ℝ) * Real.pi * u / ℓ) -
        Real.cos ((((p : ℤ) + (q : ℤ) + 2 : ℤ) : ℝ) * Real.pi * u / ℓ)) / 2) := by
    funext u
    have hsub : (((p : ℤ) - (q : ℤ) : ℤ) : ℝ) * Real.pi * u / ℓ =
        (((p : ℝ) + 1) * Real.pi * u / ℓ) - (((q : ℝ) + 1) * Real.pi * u / ℓ) := by
      push_cast; ring
    have hadd : (((p : ℤ) + (q : ℤ) + 2 : ℤ) : ℝ) * Real.pi * u / ℓ =
        (((p : ℝ) + 1) * Real.pi * u / ℓ) + (((q : ℝ) + 1) * Real.pi * u / ℓ) := by
      push_cast; ring
    rw [hsub, hadd, Real.cos_sub, Real.cos_add]
    ring
  rw [htrig, intervalIntegral.integral_div,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    interval_cos_frequency hℓ, interval_cos_frequency hℓ]
  have hsum : (p : ℤ) + (q : ℤ) + 2 ≠ 0 := by omega
  have hdiff : (p : ℤ) - (q : ℤ) = 0 ↔ p = q := by omega
  simp only [hsum, ↓reduceIte, sub_zero, hdiff]
  split_ifs <;> simp

/-- Product integration on the Euclidean cube, with the canonical spatial measure. -/
lemma integral_cube_product {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a : P201Specs.Space n)
    (f : Fin n → ℝ → ℝ) :
    (∫ x in cube ℓ a, ∏ j, f j (x j - a j) ∂P201Specs.spatialMeasure n) =
      ∏ j, ∫ u in (0 : ℝ)..ℓ, f j u := by
  have hc : (WithLp.toLp 2) ⁻¹' (cube ℓ a) =
      Set.univ.pi (fun j : Fin n => Ioo (a j) (a j + ℓ)) := by
    ext x
    simp [cube, P201Specs.Heat.Cube.cube]
  have hm := (PiLp.volume_preserving_toLp (Fin n)).restrict_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding (cube ℓ a)
  rw [← hm.integral_comp (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
  rw [hc]
  change (∫ x : Fin n → ℝ in Set.univ.pi (fun j => Ioo (a j) (a j + ℓ)),
      ∏ j, f j (x j - a j) ∂Measure.pi (fun _ => volume)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod (fun j u => f j (u - a j))]
  apply Finset.prod_congr rfl
  intro j _
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : a j ≤ a j + ℓ),
    intervalIntegral.integral_comp_sub_right]
  simp

/-- Orthogonality of the full tensor sine basis on the translated cube. -/
lemma sineMode_orthogonality {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (p q : Mode n) :
    (∫ x in cube ℓ a, sineMode ℓ a p x * sineMode ℓ a q x
      ∂P201Specs.spatialMeasure n) = if p = q then (ℓ / 2) ^ n else 0 := by
  classical
  have hh : (fun x : P201Specs.Space n => sineMode ℓ a p x * sineMode ℓ a q x) =
      (fun x => ∏ j : Fin n,
        (Real.sin (((p j : ℝ) + 1) * Real.pi * (x j - a j) / ℓ) *
          Real.sin (((q j : ℝ) + 1) * Real.pi * (x j - a j) / ℓ))) := by
    ext x
    simp [sineMode, P201Specs.Heat.Cube.sineMode, Finset.prod_mul_distrib]
  rw [hh, integral_cube_product hℓ a (fun j u =>
    Real.sin (((p j : ℝ) + 1) * Real.pi * u / ℓ) *
      Real.sin (((q j : ℝ) + 1) * Real.pi * u / ℓ))]
  simp_rw [interval_sine_orthogonality hℓ]
  by_cases hpq : p = q
  · subst q
    simp [div_pow]
  · have hj : ∃ j, p j ≠ q j := Function.ne_iff.mp hpq
    obtain ⟨j, hj⟩ := hj
    rw [if_neg hpq]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

/-- The spectral coefficient of a single heat-kernel term. -/
lemma integral_kernelTerm_sineMode {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a y : P201Specs.Space n) (τ : ℝ) (m p : Mode n) :
    (∫ x in cube ℓ a, kernelTerm ℓ a m (y,x,τ) * sineMode ℓ a p x
      ∂P201Specs.spatialMeasure n) =
    if m = p then Real.exp (-eigenvalue ℓ p * τ) * sineMode ℓ a p y else 0 := by
  have heq : (fun x => kernelTerm ℓ a m (y,x,τ) * sineMode ℓ a p x) =
      (fun x => ((2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * τ) * sineMode ℓ a m y) *
        (sineMode ℓ a m x * sineMode ℓ a p x)) := by
    funext x
    simp only [kernelTerm, P201Specs.Heat.Cube.kernelTerm]
    ring
  rw [heq, integral_const_mul, sineMode_orthogonality hℓ]
  by_cases hmp : m = p
  · subst m
    simp only [↓reduceIte]
    have hC : (2 / ℓ) ^ n * (ℓ / 2) ^ n = 1 := by
      rw [← mul_pow]
      have : (2 / ℓ) * (ℓ / 2) = 1 := by field_simp
      rw [this, one_pow]
    calc
      (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ p * τ) * sineMode ℓ a p y * (ℓ / 2) ^ n =
          ((2 / ℓ) ^ n * (ℓ / 2) ^ n) *
            (Real.exp (-eigenvalue ℓ p * τ) * sineMode ℓ a p y) := by ring
      _ = _ := by rw [hC, one_mul]
  · simp [hmp]

/-- Each eigenmode is reproduced with its heat multiplier. -/
lemma kernelSolution_sineMode {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x : P201Specs.Space n) (p : Mode n) :
    kernelSolution ℓ a (sineMode ℓ a p) τ x =
      Real.exp (-eigenvalue ℓ p * τ) * sineMode ℓ a p x := by
  classical
  let μ := (P201Specs.spatialMeasure n).restrict (cube ℓ a)
  haveI : IsFiniteMeasure μ := by
    constructor
    change (P201Specs.spatialMeasure n).restrict (cube ℓ a) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (cube_subset_closedCube ℓ a)).trans_lt
      ((closedCube_isCompact ℓ a).measure_lt_top)
  have hcont : ∀ m : Mode n,
      Continuous (fun y : P201Specs.Space n => kernelTerm ℓ a m (x,y,τ) * sineMode ℓ a p y) := by
    intro m
    apply ((continuous_kernelTerm ℓ a m).comp (by fun_prop)).mul
    unfold sineMode P201Specs.Heat.Cube.sineMode
    fun_prop
  have hsum : HasSum (fun m : Mode n => ∫ y, kernelTerm ℓ a m (x,y,τ) * sineMode ℓ a p y ∂μ)
      (kernelSolution ℓ a (sineMode ℓ a p) τ x) := by
    apply hasSum_integral_of_dominated_convergence
      (fun m (_ : P201Specs.Space n) => (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * τ))
    · intro m
      exact (hcont m).aestronglyMeasurable
    · intro m
      exact ae_of_all _ (fun y => by
        rw [norm_mul, Real.norm_eq_abs]
        calc
          _ ≤ ((2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * τ)) * 1 :=
            mul_le_mul (norm_kernelTerm_le hℓ le_rfl a m x y) (abs_sineMode_le_one ℓ a p y)
              (abs_nonneg _) (by positivity)
          _ = _ := by ring)
    · exact ae_of_all _ fun _ => (summable_exp_eigenvalue hℓ hτ).mul_left ((2 / ℓ) ^ n)
    · simp only [tsum_mul_left]
      exact integrable_const _
    · exact ae_of_all _ fun y => (kernel_summable hℓ hτ a x y).hasSum.mul_right _
  have hterm : (fun m : Mode n => ∫ y, kernelTerm ℓ a m (x,y,τ) * sineMode ℓ a p y ∂μ) =
      (fun m : Mode n => if m = p then
        Real.exp (-eigenvalue ℓ p * τ) * sineMode ℓ a p x else 0) := by
    funext m
    exact integral_kernelTerm_sineMode hℓ a x τ m p
  rw [hterm] at hsum
  exact hsum.tsum_eq.symm.trans (by simp)


open P201Specs
lemma coordinate_apply_aux {n : ℕ} (i j : Fin n) : coordinate n i j = if j = i then 1 else 0 := by
  simp [coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]

lemma product_coordinate_derivative {n : ℕ} (s : Finset (Fin n))
    (f f' : Fin n → ℝ → ℝ) (hf : ∀ j, ∀ t, HasDerivAt (f j) (f' j t) t)
    (x : Space n) (i : Fin n) :
    fderiv ℝ (fun y : Space n => ∏ j ∈ s, f j (y j)) x (coordinate n i) =
      if i ∈ s then (∏ j ∈ s.erase i, f j (x j)) * f' i (x i) else 0 := by
  have hd (j : Fin n) : HasFDerivAt (fun y : Space n => f j (y j))
      ((f' j (x j)) • (PiLp.proj 2 (fun _ : Fin n => ℝ) j)) x :=
    (hf j (x j)).comp_hasFDerivAt x (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).hasFDerivAt
  rw [(HasFDerivAt.finsetProd (fun j (_ : j ∈ s) => hd j)).fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    PiLp.proj_apply, coordinate_apply_aux]
  simp [Finset.sum_ite_eq', mul_assoc]

lemma sineMode_coordinate_deriv {n : ℕ} (ℓ : ℝ) (a : Space n) (m : Mode n)
    (x : Space n) (i : Fin n) :
    fderiv ℝ (sineMode ℓ a m) x (coordinate n i) =
      (∏ j ∈ Finset.univ.erase i, Real.sin (((m j : ℝ) + 1) * Real.pi * (x j - a j) / ℓ)) *
        (Real.cos (((m i : ℝ) + 1) * Real.pi * (x i - a i) / ℓ) *
          (((m i : ℝ) + 1) * Real.pi / ℓ)) := by
  unfold sineMode P201Specs.Heat.Cube.sineMode
  have hf (j : Fin n) (t : ℝ) : HasDerivAt (fun t => Real.sin (((m j : ℝ) + 1) * Real.pi * (t - a j) / ℓ))
      (Real.cos (((m j : ℝ) + 1) * Real.pi * (t - a j) / ℓ) * (((m j : ℝ) + 1) * Real.pi / ℓ)) t := by
    convert (((hasDerivAt_id t).sub_const (a j)).const_mul (((m j : ℝ) + 1) * Real.pi)).div_const ℓ |>.sin using 1 <;> simp [mul_div_assoc]
  simpa using product_coordinate_derivative Finset.univ _ _ hf x i

lemma sineMode_coordinate_second_deriv {n : ℕ} (ℓ : ℝ) (a : Space n) (m : Mode n)
    (x : Space n) (i : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ (sineMode ℓ a m) y (coordinate n i)) x
      (coordinate n i) =
        -((((m i : ℝ) + 1) * Real.pi / ℓ) ^ 2) * sineMode ℓ a m x := by
  simp_rw [sineMode_coordinate_deriv]
  let c : Fin n → ℝ := fun j => ((m j : ℝ) + 1) * Real.pi / ℓ
  let f : Fin n → ℝ → ℝ := fun j t => Real.sin (((m j : ℝ) + 1) * Real.pi * (t - a j) / ℓ)
  let f' : Fin n → ℝ → ℝ := fun j t => Real.cos (((m j : ℝ) + 1) * Real.pi * (t - a j) / ℓ) * c j
  have hf (j : Fin n) (t : ℝ) : HasDerivAt (f j) (f' j t) t := by
    dsimp [f, f', c]
    convert (((hasDerivAt_id t).sub_const (a j)).const_mul (((m j : ℝ) + 1) * Real.pi)).div_const ℓ |>.sin using 1 <;> simp [mul_div_assoc]
  have hp : DifferentiableAt ℝ (fun y : Space n => ∏ j ∈ Finset.univ.erase i, f j (y j)) x := by
    exact (HasFDerivAt.finsetProd (fun j (_ : j ∈ Finset.univ.erase i) =>
      (hf j (x j)).comp_hasFDerivAt x (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).hasFDerivAt)).differentiableAt
  have hc : HasDerivAt (fun t : ℝ => Real.cos (((m i : ℝ) + 1) * Real.pi * (t - a i) / ℓ) * c i)
      (-(f i (x i)) * c i * c i) (x i) := by
    dsimp [f, c]
    convert (((((hasDerivAt_id (x i)).sub_const (a i)).const_mul (((m i : ℝ) + 1) * Real.pi)).div_const ℓ).cos.mul_const (((m i : ℝ) + 1) * Real.pi / ℓ)) using 1 <;> simp [mul_div_assoc]
  have hcFull := hc.comp_hasFDerivAt x (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).hasFDerivAt
  simp only [Function.comp_def, PiLp.proj_apply] at hcFull
  change fderiv ℝ (fun y : Space n => (∏ j ∈ Finset.univ.erase i, f j (y j)) *
    (Real.cos (((m i : ℝ) + 1) * Real.pi * (y i - a i) / ℓ) * c i)) x (coordinate n i) = _
  rw [fderiv_fun_mul hp hcFull.differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [product_coordinate_derivative _ f f' hf]
  simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte, mul_zero, zero_add]
  rw [hcFull.fderiv]
  simp only [smul_apply, smul_eq_mul, PiLp.proj_apply, coordinate_apply_aux, ↓reduceIte, mul_one]
  have hs : sineMode ℓ a m x = (∏ j ∈ Finset.univ.erase i, f j (x j)) * f i (x i) := by
    exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  rw [hs]
  dsimp only [c]
  ring

lemma sineMode_laplacian {n : ℕ} (ℓ : ℝ) (a : Space n) (m : Mode n) (x : Space n) :
    laplacian (sineMode ℓ a m) x = -eigenvalue ℓ m * sineMode ℓ a m x := by
  change (∑ i : Fin n, multiPartial (sineMode ℓ a m) ({i, i} : MultiIndex n) x) = _
  have hpartial (i : Fin n) : multiPartial (sineMode ℓ a m) ({i, i} : MultiIndex n) x =
      -((((m i : ℝ) + 1) * Real.pi / ℓ) ^ 2) * sineMode ℓ a m x := by
    change P102.U4.partialWord (sineMode ℓ a m) (({i, i} : Multiset (Fin n)).sort (· ≤ ·)) x = _
    have hs : ({i, i} : Multiset (Fin n)).sort (· ≤ ·) = [i, i] := by
      rw [Multiset.insert_eq_cons, Multiset.sort_cons (r := (· ≤ ·)) (a := i) (s := {i}) (by simp), Multiset.sort_singleton]
    rw [hs]
    exact sineMode_coordinate_second_deriv ℓ a m x i
  simp_rw [hpartial]
  rw [← Finset.sum_mul]
  congr 1
  calc
    (∑ i, -((((m i : ℝ) + 1) * Real.pi / ℓ) ^ 2)) =
        ∑ i : Fin n, -(Real.pi ^ 2 / ℓ ^ 2) * ((m i : ℝ) + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by simp [← Finset.mul_sum, eigenvalue, P201Specs.Heat.Cube.eigenvalue]

lemma sineMode_contDiff_aux {n : ℕ} (ℓ : ℝ) (a : Space n) (m : Mode n) :
    ContDiff ℝ ∞ (sineMode ℓ a m) := by
  unfold sineMode P201Specs.Heat.Cube.sineMode
  fun_prop

lemma kernelTerm_coordinate_second_deriv {n : ℕ} (ℓ : ℝ) (a : Space n) (m : Mode n)
    (x y : Space n) (τ : ℝ) (i : Fin n) :
    fderiv ℝ (fun u => fderiv ℝ (fun v => kernelTerm ℓ a m (v,y,τ)) u (coordinate n i)) x
      (coordinate n i) =
        -((((m i : ℝ) + 1) * Real.pi / ℓ) ^ 2) * kernelTerm ℓ a m (x,y,τ) := by
  let C : ℝ := (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * τ) * sineMode ℓ a m y
  have heq : (fun u : Space n => kernelTerm ℓ a m (u,y,τ)) = fun u => C * sineMode ℓ a m u := by
    ext u
    dsimp [C, kernelTerm, P201Specs.Heat.Cube.kernelTerm]
    ring
  rw [heq]
  have hd (u : Space n) := (sineMode_contDiff_aux ℓ a m).differentiable (by simp) u
  simp_rw [fderiv_const_mul (hd _) C, smul_apply, smul_eq_mul]
  have hd2 : DifferentiableAt ℝ (fun u => fderiv ℝ (sineMode ℓ a m) u (coordinate n i)) x := by
    simp_rw [sineMode_coordinate_deriv]
    fun_prop
  rw [fderiv_const_mul hd2 C]
  simp only [smul_apply, smul_eq_mul]
  rw [sineMode_coordinate_second_deriv]
  rw [show kernelTerm ℓ a m (x,y,τ) = C * sineMode ℓ a m x from congrFun heq x]
  ring

lemma kernelTerm_laplacian {n : ℕ} (ℓ : ℝ) (a : Space n) (m : Mode n)
    (x y : Space n) (τ : ℝ) :
    laplacian (fun u => kernelTerm ℓ a m (u,y,τ)) x =
      -eigenvalue ℓ m * kernelTerm ℓ a m (x,y,τ) := by
  change (∑ i : Fin n, multiPartial (fun u => kernelTerm ℓ a m (u,y,τ)) ({i, i} : MultiIndex n) x) = _
  have hpartial (i : Fin n) : multiPartial (fun u => kernelTerm ℓ a m (u,y,τ)) ({i, i} : MultiIndex n) x =
      -((((m i : ℝ) + 1) * Real.pi / ℓ) ^ 2) * kernelTerm ℓ a m (x,y,τ) := by
    change P102.U4.partialWord (fun u => kernelTerm ℓ a m (u,y,τ)) (({i, i} : Multiset (Fin n)).sort (· ≤ ·)) x = _
    have hs : ({i, i} : Multiset (Fin n)).sort (· ≤ ·) = [i, i] := by
      rw [Multiset.insert_eq_cons, Multiset.sort_cons (r := (· ≤ ·)) (a := i) (s := {i}) (by simp), Multiset.sort_singleton]
    rw [hs]
    exact kernelTerm_coordinate_second_deriv ℓ a m x y τ i
  simp_rw [hpartial]
  rw [← Finset.sum_mul]
  congr 1
  calc
    (∑ i, -((((m i : ℝ) + 1) * Real.pi / ℓ) ^ 2)) =
        ∑ i : Fin n, -(Real.pi ^ 2 / ℓ ^ 2) * ((m i : ℝ) + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by simp [← Finset.mul_sum, eigenvalue, P201Specs.Heat.Cube.eigenvalue]

lemma kernelTerm_heat_equation {n : ℕ} (ℓ : ℝ) (a : Space n) (m : Mode n)
    (x y : Space n) (τ : ℝ) :
    deriv (fun t => kernelTerm ℓ a m (x,y,t)) τ =
      laplacian (fun u => kernelTerm ℓ a m (u,y,τ)) x := by
  rw [kernelTerm_laplacian]
  simpa only [iteratedDeriv_one, pow_one] using iteratedDeriv_kernelTerm_time ℓ a m x y τ 1

lemma partial_fderiv_fst_field {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E × ℝ → F} {z : E × ℝ} (hu : ContDiffAt ℝ ∞ u z) :
    ContDiffAt ℝ ∞ (fun w : E × ℝ => fderiv ℝ (fun x => u (x,w.2)) w.1) z := by
  have hh : ContDiffAt ℝ ∞
      (Function.uncurry (fun w : E × ℝ => fun x : E => u (x,w.2))) (z,z.1) := by
    exact hu.comp (z,z.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact hh.fderiv contDiffAt_fst (by simp)

lemma partial_deriv_snd_field {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : E × ℝ → ℝ} {z : E × ℝ}
    (hu : ContDiffAt ℝ ∞ u z) :
    ContDiffAt ℝ ∞ (fun w : E × ℝ => deriv (fun t => u (w.1,t)) w.2) z := by
  have hh : ContDiffAt ℝ ∞
      (Function.uncurry (fun w : E × ℝ => fun t : ℝ => u (w.1,t))) (z,z.2) := by
    exact hu.comp (z,z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  simpa only [fderiv_apply_one_eq_deriv] using
    (hh.fderiv contDiffAt_snd (by simp)).clm_apply (contDiffAt_const (c := (1:ℝ)))

lemma classicalCaloricOn_of_contDiffOn {n : ℕ} {u : P201Specs.Heat.SpaceTime n → ℝ}
    {S : Set (P201Specs.Heat.SpaceTime n)} (hS : IsOpen S)
    (hu : ContDiffOn ℝ ∞ u S)
    (hpde : ∀ z ∈ S,
      deriv (fun t => u (z.1,t)) z.2 = P201Specs.laplacian (fun x => u (x,z.2)) z.1) :
    P201Specs.Heat.IsClassicalCaloricOn u S := by
  have hAt (z) (hz : z ∈ S) : ContDiffAt ℝ ∞ u z :=
    (hu z hz).contDiffAt (hS.mem_nhds hz)
  refine ⟨hu.continuousOn, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (partial_deriv_snd_field (hAt z hz)).continuousAt.continuousWithinAt
  · intro z hz
    exact (partial_fderiv_fst_field (hAt z hz)).continuousAt.continuousWithinAt
  · intro z hz
    exact (partial_fderiv_fst_field (partial_fderiv_fst_field (hAt z hz))).continuousAt.continuousWithinAt
  · intro z hz
    have ht : ContDiffAt ℝ ∞ (fun t => u (z.1,t)) z.2 :=
      (hAt z hz).comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
    have hx : ContDiffAt ℝ ∞ (fun x => u (x,z.2)) z.1 :=
      (hAt z hz).comp z.1 (contDiffAt_id.prodMk contDiffAt_const)
    exact ⟨ht.differentiableAt (by simp), hx.of_le (by simp), hpde z hz⟩

lemma kernelCaloric_of_smooth_and_heat
    (hsmooth : P201Specs.Heat.Cube.kernelSmoothStatement)
    (hheat : ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ →
      ∀ a y x : P201Specs.Space n, ∀ τ : ℝ, 0 < τ →
        deriv (fun t => cubeKernel ℓ a t x y) τ =
          P201Specs.laplacian (fun w => cubeKernel ℓ a τ w y) x) :
    P201Specs.Heat.Cube.kernelCaloricStatement := by
  intro n hn ℓ hℓ a y
  apply classicalCaloricOn_of_contDiffOn ((cube_isOpen ℓ a).prod isOpen_Ioi)
  · intro z hz
    have hh : ContDiffAt ℝ ∞
        (fun w : P201Specs.Heat.Cube.KernelPoint n => cubeKernel ℓ a w.2.2 w.1 w.2.1)
        (z.1,y,z.2) :=
      (hsmooth n hn ℓ hℓ a (z.1,y,z.2) hz.2).contDiffAt
        ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hz.2)
    exact (hh.comp z (contDiffAt_fst.prodMk (contDiffAt_const.prodMk contDiffAt_snd))).contDiffWithinAt
  · intro z hz
    exact hheat n hn ℓ hℓ a y z.1 z.2 hz.2


lemma laplacian_eq_sum_iteratedFDeriv {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) :
    laplacian f x = ∑ i : Fin n, iteratedFDeriv ℝ 2 f x (fun _ => coordinate n i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change (∑ i : Fin n, multiPartial f ({i,i} : MultiIndex n) x) = _
  apply Finset.sum_congr rfl
  intro i hi
  change P102.U4.partialWord f (({i,i} : Multiset (Fin n)).sort (· ≤ ·)) x = _
  have hs : ({i,i} : Multiset (Fin n)).sort (· ≤ ·) = [i,i] := by
    rw [Multiset.insert_eq_cons, Multiset.sort_cons (r := (· ≤ ·)) (a := i) (s := {i}) (by simp), Multiset.sort_singleton]
  rw [hs]
  change fderiv ℝ (fun y => fderiv ℝ f y (coordinate n i)) x (coordinate n i) = _
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

lemma laplacian_tsum_of_uniform_derivative_bounds {α : Type*} {n : ℕ}
    {f : α → Space n → ℝ} {v : ℕ → α → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k i x, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i)
    (x : Space n) :
    laplacian (fun y => ∑' i, f i y) x = ∑' i, laplacian (f i) x := by
  let L : (Space n [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin n, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space n) ℝ
      (fun _ => coordinate n i)
  have hL (g : Space n → ℝ) (hg : ContDiffAt ℝ 2 g x) :
      laplacian g x = L (iteratedFDeriv ℝ 2 g x) := by
    simpa [L, sum_apply] using laplacian_eq_sum_iteratedFDeriv hg
  have hS : ContDiff ℝ ∞ (fun y => ∑' i, f i y) := by
    rw [← contDiffOn_univ]
    exact contDiffOn_tsum_on_open isOpen_univ hf hv (fun k i x _ => hb k i x)
  have hsum2 : Summable (fun i => iteratedFDeriv ℝ 2 (f i) x) :=
    .of_norm_bounded (hv 2) (fun i => hb 2 i x)
  calc
    laplacian (fun y => ∑' i, f i y) x = L (iteratedFDeriv ℝ 2 (fun y => ∑' i, f i y) x) :=
      hL _ (hS.of_le (by simp)).contDiffAt
    _ = L (∑' i, iteratedFDeriv ℝ 2 (f i) x) := by
      rw [iteratedFDeriv_tsum_on_open isOpen_univ hf hv (fun k i x _ => hb k i x) 2 (mem_univ x)]
    _ = ∑' i, L (iteratedFDeriv ℝ 2 (f i) x) := L.map_tsum hsum2
    _ = ∑' i, laplacian (f i) x := by
      apply tsum_congr
      intro i
      exact (hL _ ((hf i).of_le (by simp)).contDiffAt).symm

lemma kernel_spatial_laplacian_series {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x y : Space n) :
    laplacian (fun u => cubeKernel ℓ a τ u y) x =
      ∑' m : P201Specs.Heat.Cube.Mode n, -eigenvalue ℓ m * kernelTerm ℓ a m (x,y,τ) := by
  change laplacian (fun u => ∑' m : P201Specs.Heat.Cube.Mode n, kernelTerm ℓ a m (u,y,τ)) x = _
  have hf (m : P201Specs.Heat.Cube.Mode n) : ContDiff ℝ ∞ (fun u => kernelTerm ℓ a m (u,y,τ)) := by
    exact (contDiff_kernelTerm ℓ a m).comp (by fun_prop)
  exact (laplacian_tsum_of_uniform_derivative_bounds hf
    (fun k => summable_kernelTerm_derivative_bound hℓ hτ k)
    (fun k m u => norm_iteratedFDeriv_kernelTerm_space_le hℓ a m u y k) x).trans
    (tsum_congr (fun m => kernelTerm_laplacian ℓ a m x y τ))

lemma kernel_heat_equation {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x y : P201Specs.Space n) :
    deriv (fun t => cubeKernel ℓ a t x y) τ =
      P201Specs.laplacian (fun w => cubeKernel ℓ a τ w y) x := by
  exact (kernel_time_hasDerivAt hℓ hτ a x y).deriv.trans
    (kernel_spatial_laplacian_series hℓ hτ a x y).symm

theorem kernelCaloric : P201Specs.Heat.Cube.kernelCaloricStatement :=
  kernelCaloric_of_smooth_and_heat kernelSmooth
    (fun _ _ _ hℓ a y x _ hτ => kernel_heat_equation hℓ hτ a x y)


open P201Specs.Heat (SpaceTime heatCylinder openHeatCylinder)
lemma kernelPositive_of_nonnegative
    (hnonneg : P201Specs.Heat.Cube.kernelNonnegativeStatement)
    :
    P201Specs.Heat.Cube.kernelPositiveStatement := by
  intro n hn ℓ hℓ a τ hτ x hx y hy
  have hnon : 0 ≤ cubeKernel ℓ a τ x y :=
    hnonneg n hn ℓ hℓ a τ hτ x (cube_subset_closedCube ℓ a hx)
      y (cube_subset_closedCube ℓ a hy)
  by_contra hpos
  have hzero : cubeKernel ℓ a τ x y = 0 := le_antisymm (not_lt.mp hpos) hnon
  have hconn : IsConnected (cube ℓ a) := (cube_convex ℓ a).isConnected ⟨x,hx⟩
  let u : SpaceTime n → ℝ := fun z => cubeKernel ℓ a z.2 z.1 y
  have hu : P201Specs.Heat.IsClassicalCaloricOn u (cube ℓ a ×ˢ Ioi 0) :=
    kernelCaloric n hn ℓ hℓ a y
  have huc : ContinuousOn u (heatCylinder (cube ℓ a) τ) :=
    hu.1.mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hu' : P201Specs.Heat.IsClassicalCaloricOn u (openHeatCylinder (cube ℓ a) τ) :=
    P201.Heat.IsClassicalCaloricOn.mono hu (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hb : ∀ z ∈ heatCylinder (cube ℓ a) τ, 0 ≤ u z := by
    intro z hz
    exact hnonneg n hn ℓ hℓ a z.2 hz.2.1 z.1 (cube_subset_closedCube ℓ a hz.1)
      y (cube_subset_closedCube ℓ a hy)
  have hh := P201.Heat.strongMinimum n hn (cube ℓ a) (cube_isOpen ℓ a) hconn τ hτ u
    huc hu' 0 hb x hx τ hτ le_rfl hzero y hy (τ/2) (half_pos hτ) (by linarith)
  have hd := kernel_diagonal_pos hℓ (half_pos hτ) a y hy
  change cubeKernel ℓ a (τ/2) y y = 0 at hh
  rw [hh] at hd
  exact lt_irrefl 0 hd


lemma kernelSolution_series {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x : P201Specs.Space n) {g : P201Specs.Space n → ℝ}
    (hg : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n)) :
    kernelSolution ℓ a g τ x = ∑' m : Mode n,
      (2/ℓ)^n * Real.exp (-eigenvalue ℓ m * τ) * sineMode ℓ a m x *
        ∫ y in cube ℓ a, sineMode ℓ a m y * g y ∂P201Specs.spatialMeasure n := by
  let μ := (P201Specs.spatialMeasure n).restrict (cube ℓ a)
  have hsum : HasSum (fun m : Mode n => ∫ y, kernelTerm ℓ a m (x,y,τ) * g y ∂μ)
      (kernelSolution ℓ a g τ x) := by
    apply hasSum_integral_of_dominated_convergence
      (fun m y => ((2 / ℓ)^n * Real.exp (-eigenvalue ℓ m * τ)) * ‖g y‖)
    · intro m
      exact (((continuous_kernelTerm ℓ a m).comp (by fun_prop)).aestronglyMeasurable).mul
        hg.aestronglyMeasurable
    · intro m
      exact ae_of_all _ (fun y => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_kernelTerm_le hℓ le_rfl a m x y) (norm_nonneg _))
    · exact ae_of_all _ (fun y => ((summable_exp_eigenvalue hℓ hτ).mul_left ((2 / ℓ)^n)).mul_right ‖g y‖)
    · simp only [tsum_mul_right, tsum_mul_left]
      exact hg.norm.const_mul _
    · exact ae_of_all _ (fun y => (kernel_summable hℓ hτ a x y).hasSum.mul_right _)
  rw [← hsum.tsum_eq]
  apply tsum_congr
  intro m
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    change (2/ℓ)^n * Real.exp (-eigenvalue ℓ m*τ) * sineMode ℓ a m x * sineMode ℓ a m y * g y = _
    ring)

lemma kernel_coefficient_norm_le {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n)
    (m : Mode n) {g : P201Specs.Space n → ℝ}
    (hg : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n)) :
    ‖∫ y in cube ℓ a, sineMode ℓ a m y * g y ∂P201Specs.spatialMeasure n‖ ≤
      ∫ y in cube ℓ a, ‖g y‖ ∂P201Specs.spatialMeasure n := by
  apply norm_integral_le_of_norm_le hg.norm
  exact ae_of_all _ (fun y => by
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (abs_sineMode_le_one ℓ a m y) (norm_nonneg (g y)))

def modePeak {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) (m : Mode n) : P201Specs.Space n :=
  WithLp.toLp 2 (fun j => a j + ℓ / (2 * ((m j : ℝ)+1)))

lemma sineMode_modePeak {n : ℕ} {ℓ : ℝ} (hℓ : ℓ ≠ 0) (a : P201Specs.Space n)
    (m : Mode n) : sineMode ℓ a m (modePeak ℓ a m) = 1 := by
  unfold sineMode P201Specs.Heat.Cube.sineMode
  apply Finset.prod_eq_one
  intro j _
  have hj : (m j : ℝ) + 1 ≠ 0 := by positivity
  have harg : ((m j : ℝ) + 1) * Real.pi * (modePeak ℓ a m j - a j) / ℓ = Real.pi / 2 := by
    change ((m j : ℝ) + 1) * Real.pi * (a j + ℓ / (2 * ((m j : ℝ)+1)) - a j) / ℓ = _
    field_simp
    <;> ring
  rw [harg, Real.sin_pi_div_two]


def solutionTerm {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (m : Mode n) (z : P201Specs.Heat.SpaceTime n) : ℝ :=
  (∫ y in cube ℓ a, sineMode ℓ a m y * g y ∂P201Specs.spatialMeasure n) *
    kernelTerm ℓ a m (z.1, modePeak ℓ a m, z.2)

lemma kernelSolution_eq_tsum_solutionTerm {n : ℕ} {ℓ τ : ℝ}
    (hℓ : 0 < ℓ) (hτ : 0 < τ) (a x : P201Specs.Space n)
    {g : P201Specs.Space n → ℝ}
    (hg : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n)) :
    kernelSolution ℓ a g τ x = ∑' m : Mode n, solutionTerm ℓ a g m (x,τ) := by
  rw [kernelSolution_series hℓ hτ a x hg]
  apply tsum_congr
  intro m
  simp only [solutionTerm, kernelTerm, P201Specs.Heat.Cube.kernelTerm,
    sineMode_modePeak hℓ.ne', mul_one]
  ring

lemma contDiff_solutionTerm {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n)
    (g : P201Specs.Space n → ℝ) (m : Mode n) : ContDiff ℝ ∞ (solutionTerm ℓ a g m) := by
  unfold solutionTerm
  exact contDiff_const.mul ((contDiff_kernelTerm ℓ a m).comp
    (show ContDiff ℝ ∞ (fun w : P201Specs.Heat.SpaceTime n => (w.1,modePeak ℓ a m,w.2)) by fun_prop))

lemma norm_iteratedFDeriv_solutionTerm_le {n : ℕ} {ℓ s : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) {g : P201Specs.Space n → ℝ}
    (hg : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n))
    (m : Mode n) (z : P201Specs.Heat.SpaceTime n) (hz : s ≤ z.2) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (solutionTerm ℓ a g m) z‖ ≤
      (∫ y in cube ℓ a, ‖g y‖ ∂P201Specs.spatialMeasure n) *
        ((2/ℓ)^n * Real.exp (-eigenvalue ℓ m * s) *
          (((1 + 2 * n : ℝ) * (1 + eigenvalue ℓ m)) ^ k)) := by
  let L : P201Specs.Heat.SpaceTime n →L[ℝ] KernelPoint n :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      ((0 : P201Specs.Heat.SpaceTime n →L[ℝ] P201Specs.Space n).prod
        (ContinuousLinearMap.snd ℝ _ _))
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro w
    simp [L, Prod.norm_def]
  have hb := (norm_iteratedFDeriv_comp_affine_le (contDiff_kernelTerm ℓ a m)
    L hL (0,modePeak ℓ a m,0) z k).trans
      (norm_iteratedFDeriv_kernelTerm_le hℓ a m (L z+(0,modePeak ℓ a m,0)) (by simpa [L, Prod.add_def] using hz) k)
  have heq : (fun w => kernelTerm ℓ a m (L w+(0,modePeak ℓ a m,0))) =
      (fun w : P201Specs.Heat.SpaceTime n => kernelTerm ℓ a m (w.1,modePeak ℓ a m,w.2)) := by
    ext w
    simp [L, Prod.add_def]
  rw [heq] at hb
  change ‖iteratedFDeriv ℝ k (fun w : P201Specs.Heat.SpaceTime n =>
    (∫ y in cube ℓ a, sineMode ℓ a m y * g y ∂P201Specs.spatialMeasure n) •
      kernelTerm ℓ a m (w.1,modePeak ℓ a m,w.2)) z‖ ≤ _
  have hfspace : ContDiff ℝ ∞ (fun w : P201Specs.Heat.SpaceTime n =>
      kernelTerm ℓ a m (w.1,modePeak ℓ a m,w.2)) :=
    (contDiff_kernelTerm ℓ a m).comp (by fun_prop)
  rw [iteratedFDeriv_const_smul_apply' (hfspace.contDiffAt.of_le (by simp)), norm_smul]
  exact mul_le_mul (kernel_coefficient_norm_le ℓ a m hg) hb (norm_nonneg _) (by positivity)

lemma kernelSolution_contDiffOn {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) {g : P201Specs.Space n → ℝ}
    (hg : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n)) :
    ContDiffOn ℝ ∞ (fun z : P201Specs.Heat.SpaceTime n => kernelSolution ℓ a g z.2 z.1)
      {z | 0 < z.2} := by
  intro z hz
  have hseries : ContDiffOn ℝ ∞
      (fun z : P201Specs.Heat.SpaceTime n => ∑' m : Mode n, solutionTerm ℓ a g m z)
      {w | z.2/2 < w.2} := by
    apply contDiffOn_tsum_on_open (isOpen_lt continuous_const (by fun_prop))
      (contDiff_solutionTerm ℓ a g)
      (fun k => (summable_kernelTerm_derivative_bound hℓ (half_pos hz) k).mul_left
        (∫ y in cube ℓ a, ‖g y‖ ∂P201Specs.spatialMeasure n))
    intro k m w hw
    exact norm_iteratedFDeriv_solutionTerm_le hℓ a hg m w hw.le k
  have heq : (fun w : P201Specs.Heat.SpaceTime n => kernelSolution ℓ a g w.2 w.1) =ᶠ[𝓝 z]
      (fun w => ∑' m : Mode n, solutionTerm ℓ a g m w) := by
    filter_upwards [(isOpen_lt continuous_const (by fun_prop)).mem_nhds hz] with w hw
    exact kernelSolution_eq_tsum_solutionTerm hℓ hw a w.1 hg
  exact ((hseries.contDiffAt ((isOpen_lt continuous_const (by fun_prop)).mem_nhds
    (by change z.2/2 < z.2; change 0 < z.2 at hz; linarith))).congr_of_eventuallyEq heq).contDiffWithinAt


lemma laplacian_const_mul {n : ℕ} {f : P201Specs.Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : P201Specs.Space n) :
    P201Specs.laplacian (fun y => c * f y) x = c * P201Specs.laplacian f x := by
  change laplacian (fun y => c * f y) x = c * laplacian f x
  rw [laplacian_eq_sum_iteratedFDeriv ((contDiff_const.mul hf).of_le (by simp)).contDiffAt,
    laplacian_eq_sum_iteratedFDeriv (hf.of_le (by simp)).contDiffAt, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (iteratedFDeriv ℝ 2 (fun y => c • f y) x) _ = _
  rw [iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by simp))]
  rfl

lemma solutionTerm_heat_equation {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n)
    (g : P201Specs.Space n → ℝ) (m : Mode n) (x : P201Specs.Space n) (τ : ℝ) :
    deriv (fun t => solutionTerm ℓ a g m (x,t)) τ =
      P201Specs.laplacian (fun w => solutionTerm ℓ a g m (w,τ)) x := by
  unfold solutionTerm
  simp only [Prod.fst, Prod.snd]
  have hf : ContDiff ℝ ∞ (fun w : P201Specs.Space n => kernelTerm ℓ a m (w,modePeak ℓ a m,τ)) :=
    (contDiff_kernelTerm ℓ a m).comp (by fun_prop)
  rw [deriv_const_mul_field, laplacian_const_mul hf]
  congr 1
  exact kernelTerm_heat_equation ℓ a m x (modePeak ℓ a m) τ

lemma norm_iteratedFDeriv_solutionTerm_space_le {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) {g : P201Specs.Space n → ℝ}
    (hg : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n))
    (m : Mode n) (x : P201Specs.Space n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w => solutionTerm ℓ a g m (w,τ)) x‖ ≤
      (∫ y in cube ℓ a, ‖g y‖ ∂P201Specs.spatialMeasure n) *
        ((2/ℓ)^n * Real.exp (-eigenvalue ℓ m * τ) *
          (((1 + 2 * n : ℝ) * (1 + eigenvalue ℓ m)) ^ k)) := by
  let L : P201Specs.Space n →L[ℝ] P201Specs.Heat.SpaceTime n := ContinuousLinearMap.inl ℝ _ _
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro w
    simp [L]
  have hb := norm_iteratedFDeriv_comp_affine_le (contDiff_solutionTerm ℓ a g m) L hL (0,τ) x k
  have heq : (fun w => solutionTerm ℓ a g m (L w+(0,τ))) =
      (fun w => solutionTerm ℓ a g m (w,τ)) := by
    ext w
    simp [L, Prod.add_def]
  rw [heq] at hb
  apply hb.trans
  simpa [L, Prod.add_def] using norm_iteratedFDeriv_solutionTerm_le hℓ a hg m (x,τ) le_rfl k

lemma norm_deriv_solutionTerm_time_le {n : ℕ} {ℓ s τ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) {g : P201Specs.Space n → ℝ}
    (hg : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n))
    (m : Mode n) (x : P201Specs.Space n) (hτ : s ≤ τ) :
    ‖deriv (fun t => solutionTerm ℓ a g m (x,t)) τ‖ ≤
      (∫ y in cube ℓ a, ‖g y‖ ∂P201Specs.spatialMeasure n) *
        ((2/ℓ)^n * Real.exp (-eigenvalue ℓ m * s) *
          (((1 + 2 * n : ℝ) * (1 + eigenvalue ℓ m)) ^ 1)) := by
  let L : ℝ →L[ℝ] P201Specs.Heat.SpaceTime n := ContinuousLinearMap.inr ℝ _ _
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro w
    simp [L]
  have hb := norm_iteratedFDeriv_comp_affine_le (contDiff_solutionTerm ℓ a g m) L hL (x,0) τ 1
  have heq : (fun t => solutionTerm ℓ a g m (L t+(x,0))) =
      (fun t => solutionTerm ℓ a g m (x,t)) := by
    ext t
    simp [L, Prod.add_def]
  rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] at hb
  apply hb.trans
  simpa [L, Prod.add_def] using norm_iteratedFDeriv_solutionTerm_le hℓ a hg m (x,τ) hτ 1

lemma kernelSolution_heat_equation {n : ℕ} {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    (a x : P201Specs.Space n) {g : P201Specs.Space n → ℝ}
    (hg : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n)) :
    deriv (fun t => kernelSolution ℓ a g t x) τ =
      P201Specs.laplacian (fun w => kernelSolution ℓ a g τ w) x := by
  have hsummable (t : ℝ) (ht : 0 < t) : Summable (fun m : Mode n => solutionTerm ℓ a g m (x,t)) := by
    exact (summable_kernelTerm_derivative_bound hℓ ht 0 |>.mul_left
      (∫ y in cube ℓ a, ‖g y‖ ∂P201Specs.spatialMeasure n)).of_norm_bounded
      (fun m => by simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_solutionTerm_le hℓ a hg m (x,t) le_rfl 0)
  have htime := hasDerivAt_tsum_of_isPreconnected
    ((summable_kernelTerm_derivative_bound hℓ (half_pos hτ) 1).mul_left
      (∫ y in cube ℓ a, ‖g y‖ ∂P201Specs.spatialMeasure n))
    isOpen_Ioi (convex_Ioi (τ/2)).isPreconnected
    (fun m t _ => (((contDiff_solutionTerm ℓ a g m).comp
      (show ContDiff ℝ ∞ (fun t : ℝ => (x,t)) by fun_prop)).differentiable (by simp) t).hasDerivAt)
    (fun m t ht => norm_deriv_solutionTerm_time_le hℓ a hg m x ht.le)
    (show τ ∈ Ioi (τ/2) by change τ/2 < τ; linarith) (hsummable τ hτ)
    (show τ ∈ Ioi (τ/2) by change τ/2 < τ; linarith)
  have heq : (fun t => kernelSolution ℓ a g t x) =ᶠ[𝓝 τ]
      (fun t => ∑' m : Mode n, solutionTerm ℓ a g m (x,t)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with t ht
    exact kernelSolution_eq_tsum_solutionTerm hℓ ht a x hg
  simp only [Function.comp_def] at htime
  rw [heq.deriv_eq, htime.deriv]
  have hx : (fun w => kernelSolution ℓ a g τ w) =
      (fun w => ∑' m : Mode n, solutionTerm ℓ a g m (w,τ)) := by
    funext w
    exact kernelSolution_eq_tsum_solutionTerm hℓ hτ a w hg
  rw [hx]
  exact (tsum_congr (fun m => solutionTerm_heat_equation ℓ a g m x τ)).trans
    (laplacian_tsum_of_uniform_derivative_bounds
      (fun m => (contDiff_solutionTerm ℓ a g m).comp
        (show ContDiff ℝ ∞ (fun w : P201Specs.Space n => (w,τ)) by fun_prop))
      (fun k => (summable_kernelTerm_derivative_bound hℓ hτ k).mul_left
        (∫ y in cube ℓ a, ‖g y‖ ∂P201Specs.spatialMeasure n))
      (fun k m w => norm_iteratedFDeriv_solutionTerm_space_le hℓ a hg m w k) x).symm

lemma kernelSolution_caloric {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a : P201Specs.Space n)
    {g : P201Specs.Space n → ℝ}
    (hg : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n)) :
    P201Specs.Heat.IsClassicalCaloricOn
      (fun z : P201Specs.Heat.SpaceTime n => kernelSolution ℓ a g z.2 z.1)
      {z | 0 < z.2} :=
  classicalCaloricOn_of_contDiffOn (isOpen_lt continuous_const (by fun_prop))
    (kernelSolution_contDiffOn hℓ a hg)
    (fun z hz => kernelSolution_heat_equation hℓ hz a z.1 hg)


lemma nonnegative_of_integral_mul_test_nonnegative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : Continuous f)
    (htest : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ U → (∀ w, 0 ≤ g w) → 0 ≤ ∫ w in U, f w * g w ∂μ) :
    ∀ x ∈ U, 0 ≤ f x := by
  intro x hx
  by_contra hnon
  have hfx : f x < 0 := lt_of_not_ge hnon
  obtain ⟨g,hgs,hgc,hgd,hgr,hgx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (inter_mem (hU.mem_nhds hx) ((isOpen_lt hf continuous_const).mem_nhds hfx))
  have hg0 : ∀ w, 0 ≤ g w := fun w => (hgr (mem_range_self w)).1
  have hgsU : tsupport g ⊆ U := fun w hw => (hgs hw).1
  have hqnon : 0 ≤ (fun w => -f w * g w) := by
    intro w
    by_cases hw : g w = 0
    · simp [hw]
    · exact mul_nonneg (neg_nonneg.mpr (hgs (subset_tsupport g (mem_support.mpr hw))).2.le) (hg0 w)
  have hpos : 0 < ∫ w, -f w * g w ∂μ :=
    (hf.neg.mul hgd.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := x) (HasCompactSupport.mul_left hgc) hqnon
      (by change -f x * g x ≠ 0; rw [hgx, mul_one]; exact neg_ne_zero.mpr hfx.ne)
  have hint := htest g hgd hgc hgsU hg0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hint
  · simp only [neg_mul, integral_neg] at hpos
    linarith
  · intro w hw
    have hgzero : g w = 0 := notMem_support.mp (fun h => hw (hgsU (subset_tsupport g h)))
    simp [hgzero]

lemma kernelNonnegative_of_solution_nonnegative
    (hsolution : ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : P201Specs.Space n,
      ∀ (g : P201Specs.Space n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
        tsupport g ⊆ cube ℓ a → (∀ w, 0 ≤ g w) →
        ∀ τ : ℝ, 0 < τ → ∀ x ∈ closedCube ℓ a, 0 ≤ kernelSolution ℓ a g τ x) :
    P201Specs.Heat.Cube.kernelNonnegativeStatement := by
  intro n hn ℓ hℓ a τ hτ x hx y hy
  by_cases hyi : y ∈ cube ℓ a
  · have hcont :=
      (kernel_continuous_fixed_time hℓ hτ a).comp
        (show Continuous (fun w : P201Specs.Space n => (x,w)) by fun_prop)
    apply nonnegative_of_integral_mul_test_nonnegative (P201Specs.spatialMeasure n)
      (cube_isOpen ℓ a) hcont _ y hyi
    intro g hgd hgc hgs hg0
    exact hsolution n hn ℓ hℓ a g hgd hgc hgs hg0 τ hτ x hx
  · rw [kernelBoundary n hn ℓ hℓ a τ hτ x y (Or.inr ⟨hy,hyi⟩)]


section
open P201Specs.Heat (SpaceTime)
open P201Specs.HeatMaximum

def heatCoefficients (n : ℕ) : Coefficients n where
  a := fun _ => 1
  b := fun _ _ => 0
  c := fun _ => 0

lemma heat_operator_neg_time_shift {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : P201Specs.Heat.IsClassicalCaloricOn u {z | 0 < z.2})
    {ε T : ℝ} {z : SpaceTime n} (hz : 0 < z.2 + ε) (hzT : z.2 ≤ T) :
    operator (heatCoefficients n) T (fun w => -u (w.1,w.2+ε)) z = 0 := by
  have h := hu.2.2.2.2 (z.1,z.2+ε) hz
  have hd : DifferentiableAt ℝ (fun t => -u (z.1,t+ε)) z.2 :=
    (h.1.comp z.2 ((differentiableAt_id).add_const ε)).neg
  have htime : timeDerivative T (fun w => -u (w.1,w.2+ε)) z =
      -deriv (fun t => u (z.1,t)) (z.2+ε) := by
    unfold timeDerivative
    rw [hd.derivWithin (uniqueDiffOn_Iic T z.2 hzT)]
    rw [show (fun t => -u (z.1,t+ε)) = -(fun t => u (z.1,t+ε)) by funext t; rfl]
    rw [deriv.neg]
    exact congrArg Neg.neg (deriv_comp_add_const (fun t => u (z.1,t)) ε z.2)

  have hfirst : spatialFirst (fun w => -u (w.1,w.2+ε)) =
      fun w => -fderiv ℝ (fun x => u (x,w.2+ε)) w.1 := by
    funext w
    exact fderiv_neg
  have hsecond : spatialSecond (fun w => -u (w.1,w.2+ε)) z =
      -fderiv ℝ (fderiv ℝ (fun x => u (x,z.2+ε))) z.1 := by
    unfold spatialSecond
    rw [hfirst]
    exact fderiv_neg
  have hpde := h.2.2
  rw [P201.Heat.laplacian_eq_sum_fderiv h.2.1] at hpde
  unfold operator
  rw [htime,hsecond]
  simp only [heatCoefficients, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ContinuousLinearMap.neg_apply,
    Finset.sum_neg_distrib, sub_neg_eq_add, Finset.sum_const_zero, sub_zero]
  linarith

lemma nonnegative_of_caloric_uniform_initial {n : ℕ} (Ω : P201Specs.Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (P201Specs.Space n)))
    (hne : (Ω : Set (P201Specs.Space n)).Nonempty)
    {u : SpaceTime n → ℝ} {g : P201Specs.Space n → ℝ}
    (hu : P201Specs.Heat.IsClassicalCaloricOn u {z | 0 < z.2})
    (hinit : TendstoUniformlyOn (fun t x => u (x,t)) g (𝓝[>] (0:ℝ))
      (closure (Ω : Set (P201Specs.Space n))))
    (hg0 : ∀ x ∈ closure (Ω : Set (P201Specs.Space n)), 0 ≤ g x)
    (hboundary : ∀ x ∈ frontier (Ω : Set (P201Specs.Space n)), ∀ t : ℝ, 0 < t → u (x,t) = 0) :
    ∀ τ : ℝ, 0 < τ → ∀ x ∈ closure (Ω : Set (P201Specs.Space n)), 0 ≤ u (x,τ) := by
  intro τ hτ x hx
  have hupp : -u (x,τ) ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hevent := Metric.tendstoUniformlyOn_iff.mp hinit δ hδ
    have hevent' : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
        0 < ε ∧ ε < τ ∧ ∀ y ∈ closure (Ω : Set (P201Specs.Space n)),
          dist (g y) (u (y,ε)) < δ := by
      filter_upwards [hevent, self_mem_nhdsWithin,
        (eventually_lt_nhds hτ).filter_mono nhdsWithin_le_nhds] with ε he hε hετ
      exact ⟨hε,hετ,he⟩
    obtain ⟨ε,hε,hετ,hclose⟩ := hevent'.exists
    have hT : 0 < τ - ε := sub_pos.mpr hετ
    let w : SpaceTime n → ℝ := fun z => -u (z.1,z.2+ε)
    have hshift : Continuous (fun z : SpaceTime n => (z.1,z.2+ε)) := by fun_prop
    have hwc : ContinuousOn w (closedCylinder Ω (τ-ε)) := by
      have hc := hu.1.comp hshift.continuousOn
        (show MapsTo (fun z : SpaceTime n => (z.1,z.2+ε))
          (closedCylinder Ω (τ-ε)) {z | 0 < z.2} from
          fun z hz => by change 0 < z.2 + ε; linarith [hz.2.1])
      exact hc.neg
    have hsp : ∀ s ∈ Ioc 0 (τ-ε), ContDiffOn ℝ 2 (fun y => w (y,s)) Ω := by
      intro s hs y hy
      have hsy : 0 < s+ε := by linarith [hs.1]
      exact ((hu.2.2.2.2 (y,s+ε) hsy).2.1.neg).contDiffWithinAt
    have htem : ∀ z ∈ activeCylinder Ω (τ-ε),
        DifferentiableWithinAt ℝ (fun s => w (z.1,s)) (Iic (τ-ε)) z.2 := by
      intro z hz
      have hzt : 0 < z.2+ε := by linarith [hz.2.1]
      have hd := (hu.2.2.2.2 (z.1,z.2+ε) hzt).1
      exact ((hd.comp z.2 (differentiableAt_id.add_const ε)).neg).differentiableWithinAt
    have hL : ∀ z ∈ activeCylinder Ω (τ-ε),
        operator (heatCoefficients n) (τ-ε) w z ≤ 0 := by
      intro z hz
      exact (heat_operator_neg_time_shift hu (by linarith [hz.2.1]) hz.2.2).le
    have hb : ∀ z ∈ P201Specs.HeatMaximum.parabolicBoundary Ω (τ-ε), w z ≤ δ := by
      intro z hz
      rcases hz with hz | hz
      · have hz0 : z.2 = 0 := hz.2
        change -u (z.1,z.2+ε) ≤ δ
        rw [hz0,zero_add]
        have hh := hclose z.1 hz.1
        rw [Real.dist_eq] at hh
        linarith [(abs_lt.mp hh).2, hg0 z.1 hz.1]
      · change -u (z.1,z.2+ε) ≤ δ
        rw [hboundary z.1 hz.1 (z.2+ε) (by linarith [hz.2.1])]
        linarith
    have hbound := P201.Heat.bound_of_boundary_bound hΩ hne hT
      (C := heatCoefficients n) (fun _ _ => Matrix.PosSemidef.one)
      (fun _ _ => le_rfl) hwc hsp htem hL δ (fun _ _ => by simp [heatCoefficients]) hb
    have hh := hbound (x,τ-ε) ⟨hx,le_of_lt hT,le_rfl⟩
    change -u (x,(τ-ε)+ε) ≤ δ at hh
    simpa only [sub_add_cancel,zero_add] using hh
  linarith

lemma kernelSolution_boundary {n : ℕ} (hn : 1 ≤ n) {ℓ τ : ℝ}
    (hℓ : 0 < ℓ) (hτ : 0 < τ) (a : P201Specs.Space n)
    (g : P201Specs.Space n → ℝ) (x : P201Specs.Space n)
    (hx : x ∈ closedCube ℓ a \ cube ℓ a) : kernelSolution ℓ a g τ x = 0 := by
  change (∫ y in cube ℓ a, cubeKernel ℓ a τ x y * g y ∂P201Specs.spatialMeasure n) = 0
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun y => by
    change cubeKernel ℓ a τ x y * g y = 0
    have hz : cubeKernel ℓ a τ x y = 0 := kernelBoundary n hn ℓ hℓ a τ hτ x y (Or.inl hx)
    rw [hz,zero_mul])

lemma kernelSolution_nonnegative_of_initial
    (hinit : P201Specs.Heat.Cube.kernelInitialStatement) :
    ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : P201Specs.Space n,
      ∀ (g : P201Specs.Space n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
        tsupport g ⊆ cube ℓ a → (∀ w, 0 ≤ g w) →
        ∀ τ : ℝ, 0 < τ → ∀ x ∈ closedCube ℓ a, 0 ≤ kernelSolution ℓ a g τ x := by
  intro n hn ℓ hℓ a g hgd hgc hgs hg0 τ hτ x hx
  let Ω : P201Specs.Domain n := ⟨cube ℓ a, cube_isOpen ℓ a⟩
  have hΩ : Bornology.IsBounded (Ω : Set (P201Specs.Space n)) :=
    (closedCube_isCompact ℓ a).isBounded.subset (cube_subset_closedCube ℓ a)
  have hne : (Ω : Set (P201Specs.Space n)).Nonempty := by
    refine ⟨WithLp.toLp 2 (fun j : Fin n => a j + ℓ/2), ?_⟩
    intro j
    change a j < a j + ℓ/2 ∧ a j + ℓ/2 < a j + ℓ
    constructor <;> linarith
  have hgint : IntegrableOn g (cube ℓ a) (P201Specs.spatialMeasure n) :=
    (hgd.continuous.integrable_of_hasCompactSupport hgc).integrableOn
  have hu := kernelSolution_caloric hℓ a hgint
  have hi : TendstoUniformlyOn (fun t y => kernelSolution ℓ a g t y) g
      (𝓝[>] (0:ℝ)) (closure (Ω : Set (P201Specs.Space n))) := by
    simpa only [Ω, TopologicalSpace.Opens.coe_mk, closure_cube hℓ a] using
      hinit n hn ℓ hℓ a g hgd hgc hgs
  have hb : ∀ y ∈ frontier (Ω : Set (P201Specs.Space n)),
      ∀ t : ℝ, 0 < t → kernelSolution ℓ a g t y = 0 := by
    intro y hy t ht
    change y ∈ frontier (cube ℓ a) at hy
    rw [frontier_cube hℓ a] at hy
    exact kernelSolution_boundary hn hℓ ht a g y hy
  have hh := nonnegative_of_caloric_uniform_initial Ω hΩ hne hu hi
    (fun y _ => hg0 y) hb τ hτ x
  apply hh
  simpa only [Ω,TopologicalSpace.Opens.coe_mk,closure_cube hℓ a] using hx

lemma kernelNonnegative_of_initial
    (hinit : P201Specs.Heat.Cube.kernelInitialStatement) :
    P201Specs.Heat.Cube.kernelNonnegativeStatement :=
  kernelNonnegative_of_solution_nonnegative (kernelSolution_nonnegative_of_initial hinit)


end
section


/-- Coordinate reflections, with `false` denoting the positive coordinate. -/
def signReflection {n : ℕ} (s : Fin n → Bool) : P201Specs.Space n ≃ₗ[ℝ] P201Specs.Space n where
  toFun x := WithLp.toLp 2 (fun j => if s j then -x j else x j)
  invFun x := WithLp.toLp 2 (fun j => if s j then -x j else x j)
  left_inv x := by ext j; change (if s j then -(if s j then -x j else x j) else
    (if s j then -x j else x j)) = x j; split <;> simp_all
  right_inv x := by ext j; change (if s j then -(if s j then -x j else x j) else
    (if s j then -x j else x j)) = x j; split <;> simp_all
  map_add' x y := by ext j; change (if s j then -(x j + y j) else x j + y j) =
    (if s j then -x j else x j) + (if s j then -y j else y j); split <;> simp_all [add_comm]
  map_smul' c x := by ext j; change (if s j then -(c * x j) else c * x j) =
    c * (if s j then -x j else x j); split <;> simp_all

@[simp] lemma signReflection_apply {n : ℕ} (s : Fin n → Bool) (x : P201Specs.Space n)
    (j : Fin n) : signReflection s x j = if s j then -x j else x j := rfl

@[simp] lemma signReflection_false {n : ℕ} (x : P201Specs.Space n) :
    signReflection (fun _ : Fin n => false) x = x := by ext j; simp

def reflectionSign {n : ℕ} (s : Fin n → Bool) : ℝ := ∏ j, if s j then -1 else 1

/-- Finite odd reflection of the translated initial datum, centered at the origin. -/
def oddReflection {n : ℕ} (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (x : P201Specs.Space n) : ℝ :=
  ∑ s : Fin n → Bool, reflectionSign s * g (a + signReflection s x)

lemma oddReflection_contDiff {n : ℕ} (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (oddReflection a g) := by
  unfold oddReflection
  apply ContDiff.sum
  intro s _
  exact contDiff_const.mul (hg.comp (contDiff_const.add (signReflection s).toContinuousLinearEquiv.contDiff))

lemma oddReflection_hasCompactSupport {n : ℕ} (a : P201Specs.Space n)
    (g : P201Specs.Space n → ℝ) (hg : HasCompactSupport g) :
    HasCompactSupport (oddReflection a g) := by
  have hs : ∀ s : Fin n → Bool, HasCompactSupport
      (fun x : P201Specs.Space n => reflectionSign s * g (a + signReflection s x)) := by
    intro s
    have hc := hg.comp_homeomorph
      ((signReflection s).toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addLeft a))
    exact hc.comp_left (by simp : reflectionSign s * (0 : ℝ) = 0)
  convert (HasCompactSupport.finset_sum (s := Finset.univ) (fun s _ => hs s)) using 1
  ext x
  simp [oddReflection]

/-- The finite reflection is a Schwartz function without an extension certificate. -/
def oddReflectionSchwartz {n : ℕ} (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    SchwartzMap (P201Specs.Space n) ℂ :=
  ((oddReflection_hasCompactSupport a g hgc).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (oddReflection_contDiff a g hg))

@[simp] lemma oddReflectionSchwartz_apply {n : ℕ} (a : P201Specs.Space n)
    (g : P201Specs.Space n → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : P201Specs.Space n) : oddReflectionSchwartz a g hg hgc x = (oddReflection a g x : ℂ) := rfl

lemma oddReflection_eq_on_closedCube {n : ℕ} {ℓ : ℝ} (a : P201Specs.Space n)
    (g : P201Specs.Space n → ℝ) (hgs : tsupport g ⊆ P201Specs.Heat.Cube.cube ℓ a)
    (x : P201Specs.Space n) (hx : x ∈ P201Specs.Heat.Cube.closedCube ℓ 0) :
    oddReflection a g x = g (a + x) := by
  classical
  unfold oddReflection
  rw [Finset.sum_eq_single (fun _ : Fin n => false)]
  · simp [reflectionSign]
  · intro s _ hs
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hs
    have hsj : s j = true := by cases h : s j <;> simp_all
    have hzero : g (a + signReflection s x) = 0 := by
      by_contra hne
      have hmem := hgs (subset_tsupport g (show (a + signReflection s x) ∈ Function.support g from hne)) j
      have hxj := (hx j).1
      simp only [PiLp.add_apply, signReflection_apply, hsj, ↓reduceIte, PiLp.zero_apply] at hmem hxj
      linarith [hmem.1]
    simp [hzero]
  · simp

/-- Noncentral lattice translates cannot meet the support of a reflected datum. -/
lemma oddReflection_lattice_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hgs : tsupport g ⊆ P201Specs.Heat.Cube.cube ℓ a)
    (x : P201Specs.Space n) (hx : x ∈ P201Specs.Heat.Cube.closedCube ℓ 0)
    (k : Fin n → ℤ) (hk : k ≠ 0) :
    oddReflection a g (x + (2 * ℓ) • P102.U3.PoissonSummation.latticePoint k) = 0 := by
  classical
  unfold oddReflection
  apply Finset.sum_eq_zero
  intro s _
  suffices hgzero : g (a + signReflection s
      (x + (2 * ℓ) • P102.U3.PoissonSummation.latticePoint k)) = 0 by rw [hgzero, mul_zero]
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
  have hj0 : k j ≠ 0 := by simpa using hj
  have hmem := hgs (subset_tsupport g (show (a + signReflection s
      (x + (2 * ℓ) • P102.U3.PoissonSummation.latticePoint k)) ∈ Function.support g from hne)) j
  have hxj := hx j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, signReflection_apply,
    P102.U3.PoissonSummation.latticePoint, WithLp.ofLp_toLp, PiLp.zero_apply,
    zero_add] at hmem hxj
  by_cases hjpos : 0 < k j
  · have hj1 : (1 : ℝ) ≤ (k j : ℝ) := by exact_mod_cast hjpos
    have hbound : ℓ < x j + 2 * ℓ * (k j : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hj1 (by positivity : 0 ≤ 2 * ℓ)]
    split at hmem <;> linarith [hmem.1, hmem.2]
  · have hjneg : k j ≤ -1 := by omega
    have hj1 : (k j : ℝ) ≤ -1 := by exact_mod_cast hjneg
    have hbound : x j + 2 * ℓ * (k j : ℝ) ≤ -ℓ := by
      nlinarith [mul_le_mul_of_nonneg_left hj1 (by positivity : 0 ≤ 2 * ℓ)]
    split at hmem <;> linarith [hmem.1, hmem.2]

/-- On the closed original cube the periodization is exactly the initial datum. -/
lemma oddReflection_periodization {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ P201Specs.Heat.Cube.cube ℓ a)
    (x : P201Specs.Space n) (hx : x ∈ P201Specs.Heat.Cube.closedCube ℓ 0) :
    (∑' k : Fin n → ℤ, P102.U3.PoissonSummation.spatialTerm (2 * ℓ)
      (oddReflectionSchwartz a g hg hgc) k x) = (g (a + x) : ℂ) := by
  rw [tsum_eq_single (0 : Fin n → ℤ)]
  · simp only [P102.U3.PoissonSummation.spatialTerm, oddReflectionSchwartz_apply]
    have hk : P102.U3.PoissonSummation.latticePoint (0 : Fin n → ℤ) = 0 := by
      ext j
      simp [P102.U3.PoissonSummation.latticePoint]
    rw [hk, smul_zero, add_zero, oddReflection_eq_on_closedCube a g hgs x hx]
  · intro k hk
    simp only [P102.U3.PoissonSummation.spatialTerm, oddReflectionSchwartz_apply]
    rw [oddReflection_lattice_zero hℓ a g hgs x hx k hk, Complex.ofReal_zero]

/-- Poisson summation provides an absolutely convergent Fourier representation
of the reflected smooth datum without a periodic-extension certificate. -/
lemma oddReflection_fourier_identity {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ P201Specs.Heat.Cube.cube ℓ a)
    (x : P201Specs.Space n) (hx : x ∈ P201Specs.Heat.Cube.closedCube ℓ 0) :
    (g (a + x) : ℂ) = (((2 * ℓ) ^ n)⁻¹ : ℝ) •
      (∑' m : Fin n → ℤ, P102.U3.PoissonSummation.fourierTerm (2 * ℓ)
        (oddReflectionSchwartz a g hg hgc) m x) := by
  rw [← oddReflection_periodization hℓ a g hg hgc hgs x hx]
  exact P102.U3.PoissonSummation.poisson_identity (2 * ℓ) (by positivity) _ x



open scoped BigOperators

lemma sum_bool_signed_exp (θ : ℝ) :
    (∑ b : Bool, (if b then (-1 : ℂ) else 1) *
      Complex.exp ((if b then (-1 : ℂ) else 1) * (θ : ℂ) * Complex.I)) =
      (2 * Complex.I) * (Real.sin θ : ℂ) := by
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul, neg_one_mul]
  rw [show -((θ : ℂ) * Complex.I) = (-θ : ℝ) * Complex.I by simp,
    Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

lemma sum_sign_exponential_product {n : ℕ} (θ : Fin n → ℝ) :
    (∑ s : Fin n → Bool, ∏ j,
      (if s j then (-1 : ℂ) else 1) *
        Complex.exp ((if s j then (-1 : ℂ) else 1) * (θ j : ℂ) * Complex.I)) =
      (2 * Complex.I) ^ n * ∏ j, (Real.sin (θ j) : ℂ) := by
  calc
    _ = ∏ j, ∑ b : Bool, (if b then (-1 : ℂ) else 1) *
        Complex.exp ((if b then (-1 : ℂ) else 1) * (θ j : ℂ) * Complex.I) :=
      (Fintype.prod_sum _).symm
    _ = _ := by
      simp_rw [sum_bool_signed_exp]
      rw [Finset.prod_mul_distrib]
      simp


abbrev SignedMode (n : ℕ) := (Fin n → ℕ) × (Fin n → Bool)
def signedModeInteger {n : ℕ} (p : SignedMode n) : Fin n → ℤ :=
  fun j => if p.2 j then -((p.1 j : ℤ) + 1) else (p.1 j : ℤ) + 1

lemma signedModeInteger_injective {n : ℕ} : Function.Injective (@signedModeInteger n) := by
  intro p q hpq
  apply Prod.ext
  · funext j
    have hj := congrFun hpq j
    dsimp [signedModeInteger] at hj
    cases hp : p.2 j <;> cases hq : q.2 j <;> simp [hp,hq] at hj <;> omega
  · funext j
    have hj := congrFun hpq j
    dsimp [signedModeInteger] at hj
    cases hp : p.2 j <;> cases hq : q.2 j <;> simp [hp,hq] at hj ⊢ <;> omega

lemma signedInteger_exists (z : ℤ) (hz : z ≠ 0) :
    ∃ p : ℕ × Bool, (if p.2 then -((p.1 : ℤ) + 1) else (p.1 : ℤ) + 1) = z := by
  cases z with
  | ofNat k =>
    cases k with
    | zero => exact (hz rfl).elim
    | succ k => exact ⟨(k,false), by simp⟩
  | negSucc k => exact ⟨(k,true), by simp [Int.negSucc_eq]⟩

lemma tsum_integer_modes_eq_signed_modes {n : ℕ} {F : (Fin n → ℤ) → ℂ}
    (hF : Summable F) (hzero : ∀ z (j : Fin n), z j = 0 → F z = 0) :
    (∑' z, F z) = ∑' m : Fin n → ℕ, ∑ s : Fin n → Bool, F (signedModeInteger (m,s)) := by
  have hs : Function.support F ⊆ Set.range (@signedModeInteger n) := by
    intro z hz
    have hcoord (j : Fin n) : z j ≠ 0 := by
      intro hj
      exact hz (hzero z j hj)
    choose p hp using fun j => signedInteger_exists (z j) (hcoord j)
    refine ⟨(fun j => (p j).1, fun j => (p j).2), ?_⟩
    exact funext hp
  calc
    (∑' z, F z) = ∑' p : SignedMode n, F (signedModeInteger p) :=
      (signedModeInteger_injective.tsum_eq hs).symm
    _ = ∑' m : Fin n → ℕ, ∑' s : Fin n → Bool, F (signedModeInteger (m,s)) :=
      (hF.comp_injective signedModeInteger_injective).tsum_prod
    _ = _ := by simp only [tsum_fintype]


open P102.U3.PoissonSummation
lemma signedMode_phase_product {n : ℕ} (ℓ : ℝ) (m : Fin n → ℕ) (s : Fin n → Bool)
    (x : P102.Specs.U3.Euclidean n) :
    Complex.exp (((2 * Real.pi * inner ℝ (latticePoint (signedModeInteger (m,s))) x / (2 * ℓ) : ℝ) : ℂ) * Complex.I) =
      ∏ j, Complex.exp ((if s j then (-1 : ℂ) else 1) *
        ((((m j : ℝ) + 1) * Real.pi * x j / ℓ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, latticePoint, WithLp.ofLp_toLp,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [signedModeInteger]
  by_cases hs : s j = true <;> simp [hs] <;> push_cast <;> ring


lemma signReflection_integral_comp {n : ℕ} (s : Fin n → Bool)
    (f : P201Specs.Space n → ℂ) :
    (∫ x, f (signReflection s x)) = ∫ x, f x := by
  let e : P201Specs.Space n ≃ₗᵢ[ℝ] P201Specs.Space n :=
    LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
      if s j then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have he : (e : P201Specs.Space n → P201Specs.Space n) = signReflection s := by
    funext x
    ext j
    simp only [e, LinearIsometryEquiv.piLpCongrRight_apply, signReflection_apply]
    by_cases hs : s j = true <;> simp [hs]
  rw [← he]
  exact e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding f


open P102.Specs.U3
open scoped FourierTransform
lemma sum_reflection_negative_phase {n : ℕ} (v ξ : P201Specs.Space n) :
    (∑ s : Fin n → Bool, (reflectionSign s : ℂ) *
      Complex.exp (((-2 * Real.pi * inner ℝ (signReflection s v) ξ : ℝ) : ℂ) * Complex.I)) =
      (-2 * Complex.I)^n * ∏ j, (Real.sin (2 * Real.pi * v j * ξ j) : ℂ) := by
  have hphase (s : Fin n → Bool) :
      (reflectionSign s : ℂ) *
        Complex.exp (((-2 * Real.pi * inner ℝ (signReflection s v) ξ : ℝ) : ℂ) * Complex.I) =
      ∏ j : Fin n, (if s j then (-1 : ℂ) else 1) *
        Complex.exp ((if s j then (-1 : ℂ) else 1) *
          ((-(2 * Real.pi * v j * ξ j) : ℝ) : ℂ) * Complex.I) := by
    rw [Finset.prod_mul_distrib]
    have hsign : (reflectionSign s : ℂ) = ∏ j : Fin n, if s j then (-1 : ℂ) else 1 := by
      simp [reflectionSign, apply_ite]
    rw [hsign]
    congr 1
    rw [← Complex.exp_sum]
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, signReflection_apply,
      ← Finset.mul_sum]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hs : s j = true <;> simp [hs] <;> push_cast <;> ring
  simp_rw [hphase]
  rw [sum_sign_exponential_product]
  simp only [Real.sin_neg, Complex.ofReal_neg, Finset.prod_neg, Finset.card_univ,
    Fintype.card_fin]
  rw [← mul_assoc, ← mul_pow]
  congr 2
  ring

lemma fourier_oddReflection {n : ℕ} (a : P201Specs.Space n)
    (g : P201Specs.Space n → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (ξ : P201Specs.Space n) :
    fourierValue n (oddReflectionSchwartz a g hg hgc) ξ =
      (-2 * Complex.I)^n * ∫ v : P201Specs.Space n,
        (g (a+v) : ℂ) * ∏ j, (Real.sin (2 * Real.pi * v j * ξ j) : ℂ) := by
  change FourierTransform.fourier (oddReflectionSchwartz a g hg hgc) ξ = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [oddReflectionSchwartz_apply, oddReflection, Complex.ofReal_sum,
    Complex.ofReal_mul, smul_eq_mul, Finset.mul_sum]
  have hi (s : Fin n → Bool) : Integrable (fun v : P201Specs.Space n =>
      Complex.exp (((-2 * Real.pi * inner ℝ v ξ : ℝ) : ℂ) * Complex.I) *
        ((reflectionSign s : ℂ) * (g (a+signReflection s v) : ℂ))) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (by fun_prop : Continuous (fun v : P201Specs.Space n =>
        Complex.exp (((-2 * Real.pi * inner ℝ v ξ : ℝ) : ℂ) * Complex.I))).mul
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (hg.continuous.comp (continuous_const.add (signReflection s).toContinuousLinearEquiv.continuous))))
    · apply HasCompactSupport.mul_left
      have hc := hgc.comp_homeomorph ((signReflection s).toContinuousLinearEquiv.toHomeomorph.trans
        (Homeomorph.addLeft a))
      have hc' : HasCompactSupport (fun v : P201Specs.Space n => (g (a+signReflection s v) : ℂ)) :=
        hc.comp_left Complex.ofReal_zero
      exact hc'.comp_left (mul_zero (reflectionSign s : ℂ))
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat] at hi
  push_cast
  rw [integral_finsetSum _ (fun s _ => hi s)]
  have hreflect (s : Fin n → Bool) :
      (∫ v : P201Specs.Space n, Complex.exp (((-2 * Real.pi * inner ℝ v ξ : ℝ) : ℂ) * Complex.I) *
        ((reflectionSign s : ℂ) * (g (a+signReflection s v) : ℂ))) =
      ∫ v : P201Specs.Space n, (g (a+v) : ℂ) * ((reflectionSign s : ℂ) *
        Complex.exp (((-2 * Real.pi * inner ℝ (signReflection s v) ξ : ℝ) : ℂ) * Complex.I)) := by
    rw [← signReflection_integral_comp s (fun v : P201Specs.Space n =>
      Complex.exp (((-2 * Real.pi * inner ℝ v ξ : ℝ) : ℂ) * Complex.I) *
        ((reflectionSign s : ℂ) * (g (a+signReflection s v) : ℂ)))]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      have hss : signReflection s (signReflection s v) = v := (signReflection s).left_inv v
      dsimp only
      rw [hss]
      ring)
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat] at hreflect
  simp_rw [hreflect]
  rw [← integral_finsetSum]
  · simp_rw [← Finset.mul_sum]
    have hphase := sum_reflection_negative_phase (n := n)
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat] at hphase
    push_cast at hphase
    simp_rw [hphase]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by ring)
  · intro s _
    apply Continuous.integrable_of_hasCompactSupport
    · have hr : Continuous (fun v => signReflection s v) := (signReflection s).toContinuousLinearEquiv.continuous
      exact (Complex.continuous_ofReal.comp (hg.continuous.comp
        (continuous_const.add continuous_id))).mul
        (continuous_const.mul (by fun_prop))
    · have hc : HasCompactSupport (fun v : P201Specs.Space n => (g (a+v) : ℂ)) :=
        (hgc.comp_homeomorph (Homeomorph.addLeft a)).comp_left Complex.ofReal_zero
      exact hc.mul_right



end
section
lemma heat_multiplier_series_initial {ι X E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ι → X → E) (lam u : ι → ℝ)
    (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i) (hlam : ∀ i, 0 ≤ lam i)
    (hf : ∀ i x, ‖f i x‖ ≤ u i) :
    TendstoUniformly (fun τ : ℝ => fun x : X => ∑' i, Real.exp (-lam i * τ) • f i x)
      (fun x => ∑' i, f i x) (𝓝[>] (0 : ℝ)) := by
  have he0 : ∀ (τ : ℝ), 0 < τ → ∀ i, |Real.exp (-lam i * τ) - 1| ≤ 1 := by
    intro τ hτ i
    have he1 : Real.exp (-lam i * τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hlam i])
    rw [abs_of_nonpos (sub_nonpos.mpr he1)]
    linarith [Real.exp_pos (-lam i * τ)]
  have ht : Tendsto (fun τ : ℝ => ∑' i, |Real.exp (-lam i * τ) - 1| * u i)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hh := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ)) (f := fun τ : ℝ =>
      fun i => |Real.exp (-lam i * τ) - 1| * u i) (g := fun _ : ι => (0 : ℝ)) hu
      (fun i => ?_) ?_
    · simpa using hh
    · have hc : Continuous (fun τ : ℝ => |Real.exp (-lam i * τ) - 1| * u i) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with τ hτ i
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hu0 i))]
      simpa using mul_le_mul_of_nonneg_right (he0 τ hτ i) (hu0 i)
  have hbase : ∀ x, Summable (fun i => f i x) := fun x =>
    Summable.of_norm (hu.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hf i x))
  have hbound : ∀ (τ : ℝ), 0 < τ → ∀ i x,
      ‖f i x - Real.exp (-lam i * τ) • f i x‖ ≤ |Real.exp (-lam i * τ) - 1| * u i := by
    intro τ _ i x
    have heq : f i x - Real.exp (-lam i * τ) • f i x =
        (1 - Real.exp (-lam i * τ)) • f i x := by rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (hf i x) (abs_nonneg _)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp ht) ε hε,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with τ hτ hτpos x
  have hscalar : Summable (fun i => |Real.exp (-lam i * τ) - 1| * u i) :=
    hu.of_nonneg_of_le (fun i => mul_nonneg (abs_nonneg _) (hu0 i))
      (fun i => by simpa using mul_le_mul_of_nonneg_right (he0 τ hτpos i) (hu0 i))
  have hnorm : Summable (fun i => ‖f i x - Real.exp (-lam i * τ) • f i x‖) :=
    hscalar.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hbound τ hτpos i x)
  have hsum : Summable (fun i => Real.exp (-lam i * τ) • f i x) := by
    have he1 : ∀ i, Real.exp (-lam i * τ) ≤ 1 := fun i =>
      Real.exp_le_one_iff.mpr (by nlinarith [hlam i, show 0 < τ from hτpos])
    apply Summable.of_norm
    apply hu.of_nonneg_of_le (fun i => norm_nonneg _)
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hf i x) (Real.exp_pos _).le).trans
      (by simpa using mul_le_mul_of_nonneg_right (he1 i) (hu0 i))
  calc
    dist (∑' i, f i x) (∑' i, Real.exp (-lam i * τ) • f i x) =
        ‖∑' i, (f i x - Real.exp (-lam i * τ) • f i x)‖ := by
      rw [dist_eq_norm, (hbase x).tsum_sub hsum]
    _ ≤ ∑' i, ‖f i x - Real.exp (-lam i * τ) • f i x‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, |Real.exp (-lam i * τ) - 1| * u i :=
      hnorm.tsum_le_tsum (fun i => hbound τ hτpos i x) hscalar
    _ < ε := by simpa [Real.dist_eq, abs_of_nonneg (tsum_nonneg
      (fun i => mul_nonneg (abs_nonneg _) (hu0 i)))] using hτ


open P102.U3.PoissonSummation

/-- The spatial heat eigenvalue on the complete integer frequency lattice. -/
def integerEigenvalue {n : ℕ} (ℓ : ℝ) (z : Fin n → ℤ) : ℝ :=
  Real.pi ^ 2 / ℓ ^ 2 * ∑ j, (z j : ℝ) ^ 2

lemma integerEigenvalue_nonneg {n : ℕ} (ℓ : ℝ) (z : Fin n → ℤ) :
    0 ≤ integerEigenvalue ℓ z := by unfold integerEigenvalue; positivity

/-- Fourier heat evolution of the explicitly reflected Schwartz datum. -/
def reflectedHeatSeries {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n)
    (g : P201Specs.Space n → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (τ : ℝ) (x : P201Specs.Space n) : ℂ :=
  (((2 * ℓ) ^ n)⁻¹ : ℝ) • ∑' z : Fin n → ℤ,
    Real.exp (-integerEigenvalue ℓ z * τ) •
      fourierTerm (2 * ℓ) (oddReflectionSchwartz a g hg hgc) z (x - a)

/-- The reflected Fourier heat series converges uniformly to the genuine
initial function on every face of the translated closed cube. -/
lemma reflectedHeatSeries_initial {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ P201Specs.Heat.Cube.cube ℓ a) :
    TendstoUniformlyOn (reflectedHeatSeries ℓ a g hg hgc)
      (fun x => (g x : ℂ)) (𝓝[>] (0 : ℝ)) (P201Specs.Heat.Cube.closedCube ℓ a) := by
  let C : ℝ := ((2 * ℓ) ^ n)⁻¹
  let φ := oddReflectionSchwartz a g hg hgc
  let u : (Fin n → ℤ) → ℝ := fun z => C *
    ‖P102.Specs.U3.fourierValue n φ ((2 * ℓ)⁻¹ • latticePoint z)‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hu : Summable u := (fourier_samples_absolute (2 * ℓ) (by positivity) φ).mul_left C
  have hu0 : ∀ z, 0 ≤ u z := fun z => mul_nonneg hC (norm_nonneg _)
  have hf : ∀ z (x : P201Specs.Space n),
      ‖C • fourierTerm (2 * ℓ) φ z (x - a)‖ ≤ u z := by
    intro z x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, norm_fourierTerm]
  have hlim := heat_multiplier_series_initial
    (fun z (x : P201Specs.Space n) => C • fourierTerm (2 * ℓ) φ z (x - a))
    (integerEigenvalue ℓ) u hu hu0 (integerEigenvalue_nonneg ℓ) hf
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hlim) ε hε] with τ hτ x hx
  have hxa : x - a ∈ P201Specs.Heat.Cube.closedCube ℓ 0 := by
    intro j
    have hj := hx j
    change 0 ≤ x j - a j ∧ x j - a j ≤ 0 + ℓ
    constructor <;> linarith [hj.1, hj.2]
  have hid : (∑' z, C • fourierTerm (2 * ℓ) φ z (x - a)) = (g x : ℂ) := by
    rw [tsum_const_smul'']
    have hh := (oddReflection_fourier_identity hℓ a g hg hgc hgs (x - a) hxa).symm
    simpa only [φ, C, add_sub_cancel] using hh
  have hexact : (∑' z, Real.exp (-integerEigenvalue ℓ z * τ) •
      C • fourierTerm (2 * ℓ) φ z (x - a)) = reflectedHeatSeries ℓ a g hg hgc τ x := by
    unfold reflectedHeatSeries
    rw [← tsum_const_smul'']
    apply tsum_congr
    intro z
    exact smul_comm _ _ _
  simpa only [hid, hexact] using hτ x



open P201Specs.Heat.Cube (Mode)
open P102.U3.PoissonSummation

def integerSineMode {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) (m : Fin n → ℤ)
    (x : P201Specs.Space n) : ℝ := ∏ j, Real.sin ((m j : ℝ) * Real.pi * (x j - a j) / ℓ)

lemma integerSineMode_signed {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n) (m : Mode n)
    (s : Fin n → Bool) (x : P201Specs.Space n) :
    integerSineMode ℓ a (signedModeInteger (m,s)) x = reflectionSign s * P201Specs.Heat.Cube.sineMode ℓ a m x := by
  unfold integerSineMode reflectionSign P201Specs.Heat.Cube.sineMode
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  dsimp [signedModeInteger]
  by_cases hs : s j = true
  · simp only [hs, ↓reduceIte, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      neg_mul, neg_div, Real.sin_neg, neg_one_mul, one_mul]
  · simp [hs]

lemma integerSineMode_zero_of_coordinate {n : ℕ} (ℓ : ℝ) (a : P201Specs.Space n)
    (m : Fin n → ℤ) (j : Fin n) (hj : m j = 0) (x : P201Specs.Space n) :
    integerSineMode ℓ a m x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hj]

lemma sum_sign_lattice_phase {n : ℕ} (ℓ : ℝ) (m : Mode n) (x : P201Specs.Space n) :
    (∑ s : Fin n → Bool, (reflectionSign s : ℂ) *
      Complex.exp (((2 * Real.pi * inner ℝ (latticePoint (signedModeInteger (m,s))) x / (2 * ℓ) : ℝ) : ℂ) * Complex.I)) =
      (2 * Complex.I)^n * (P201Specs.Heat.Cube.sineMode ℓ 0 m x : ℂ) := by
  simp_rw [signedMode_phase_product]
  simpa only [reflectionSign, Complex.ofReal_prod, Complex.ofReal_one, Complex.ofReal_neg,
    apply_ite Complex.ofReal, Finset.prod_mul_distrib, P201Specs.Heat.Cube.sineMode, PiLp.zero_apply, sub_zero] using
    sum_sign_exponential_product (fun j => ((m j : ℝ) + 1) * Real.pi * x j / ℓ)


open P201Specs.Heat.Cube (Mode)
open P102.U3.PoissonSummation

lemma positive_fourier_samples_summable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (φ : P102.Specs.U3.Test n) (c : Mode n → ℂ)
    (hc : ∀ m, P102.Specs.U3.fourierValue n φ
      ((2 * ℓ)⁻¹ • latticePoint (signedModeInteger (m, fun _ => false))) = c m) :
    Summable c := by
  have hfull : Summable (fun z : Fin n → ℤ => P102.Specs.U3.fourierValue n φ
      ((2 * ℓ)⁻¹ • latticePoint z)) :=
    .of_norm (fourier_samples_absolute (2 * ℓ) (by positivity) φ)
  have hinj : Function.Injective (fun m : Mode n => signedModeInteger (m, fun _ => false)) := by
    intro m p hmp
    exact congrArg Prod.fst (signedModeInteger_injective hmp)
  simpa only [Function.comp_def, hc] using hfull.comp_injective hinj

lemma fourier_lattice_sine_synthesis {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (φ : P102.Specs.U3.Test n) (c : Mode n → ℂ)
    (hc : ∀ m s, P102.Specs.U3.fourierValue n φ
      ((2 * ℓ)⁻¹ • latticePoint (signedModeInteger (m,s))) = (reflectionSign s : ℂ) * c m)
    (hzero : ∀ (z : Fin n → ℤ) (j : Fin n), z j = 0 →
      P102.Specs.U3.fourierValue n φ ((2 * ℓ)⁻¹ • latticePoint z) = 0)
    (x : P201Specs.Space n) :
    (∑' z : Fin n → ℤ, fourierTerm (2 * ℓ) φ z x) =
      (2 * Complex.I)^n * ∑' m : Mode n, c m * (P201Specs.Heat.Cube.sineMode ℓ 0 m x : ℂ) := by
  have hfull : Summable (fun z : Fin n → ℤ => fourierTerm (2 * ℓ) φ z x) :=
    .of_norm (fourier_absolute (2 * ℓ) (by positivity) φ x)
  rw [tsum_integer_modes_eq_signed_modes hfull (fun z j hj => by
    simp only [fourierTerm, hzero z j hj, zero_mul])]
  calc
    _ = ∑' m : Mode n, c m *
        ∑ s : Fin n → Bool, (reflectionSign s : ℂ) *
          Complex.exp (((2 * Real.pi * inner ℝ (latticePoint (signedModeInteger (m,s))) x / (2 * ℓ) : ℝ) : ℂ) * Complex.I) := by
      apply tsum_congr
      intro m
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [fourierTerm, hc]
      ring
    _ = _ := by
      simp_rw [sum_sign_lattice_phase]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      ring


open P201Specs.Heat.Cube (Mode)
open P102.U3.PoissonSummation
lemma lattice_sine_synthesis {n : ℕ} (ℓ : ℝ) (C : (Fin n → ℤ) → ℂ)
    (hC : Summable C) (c : Mode n → ℂ)
    (hc : ∀ m s, C (signedModeInteger (m,s)) = (reflectionSign s : ℂ) * c m)
    (hzero : ∀ (z : Fin n → ℤ) (j : Fin n), z j = 0 → C z = 0)
    (x : P201Specs.Space n) :
    (∑' z : Fin n → ℤ, C z *
      Complex.exp (((2 * Real.pi * inner ℝ (latticePoint z) x / (2 * ℓ) : ℝ) : ℂ) * Complex.I)) =
      (2 * Complex.I)^n * ∑' m : Mode n, c m * (P201Specs.Heat.Cube.sineMode ℓ 0 m x : ℂ) := by
  let F (z : Fin n → ℤ) := C z *
    Complex.exp (((2 * Real.pi * inner ℝ (latticePoint z) x / (2 * ℓ) : ℝ) : ℂ) * Complex.I)
  have hfull : Summable F := by
    apply Summable.of_norm
    simpa only [F, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using hC.norm
  change (∑' z, F z) = _
  rw [tsum_integer_modes_eq_signed_modes hfull (fun z j hj => by
    simp only [F, hzero z j hj, zero_mul])]
  calc
    _ = ∑' m : Mode n, c m *
        ∑ s : Fin n → Bool, (reflectionSign s : ℂ) *
          Complex.exp (((2 * Real.pi * inner ℝ (latticePoint (signedModeInteger (m,s))) x / (2 * ℓ) : ℝ) : ℂ) * Complex.I) := by
      apply tsum_congr
      intro m
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [F, hc]
      ring
    _ = _ := by
      simp_rw [sum_sign_lattice_phase]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      ring



lemma integerEigenvalue_signed {n : ℕ} (ℓ : ℝ) (m : P201Specs.Heat.Cube.Mode n)
    (s : Fin n → Bool) :
    integerEigenvalue ℓ (signedModeInteger (m,s)) = P201Specs.Heat.Cube.eigenvalue ℓ m := by
  unfold integerEigenvalue P201Specs.Heat.Cube.eigenvalue
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [signedModeInteger]
  by_cases hs : s j = true <;> simp [hs] <;> ring


end
section

open P102.Specs.U3 P102.U3.PoissonSummation Function

lemma fourier_oddReflection_lattice {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ cube ℓ a) (m : Fin n → ℤ) :
    fourierValue n (oddReflectionSchwartz a g hg hgc) ((2 * ℓ)⁻¹ • latticePoint m) =
      (-2 * Complex.I)^n * ∫ y in cube ℓ a,
        (g y : ℂ) * ∏ j, (Real.sin ((m j : ℝ) * Real.pi * (y j - a j) / ℓ) : ℂ) := by
  rw [fourier_oddReflection]
  congr 1
  have hphase (v : P201Specs.Space n) (j : Fin n) :
      2 * Real.pi * v j * (((2 * ℓ)⁻¹ • latticePoint m) j) =
        (m j : ℝ) * Real.pi * v j / ℓ := by
    simp only [PiLp.smul_apply, smul_eq_mul, latticePoint, WithLp.ofLp_toLp]
    field_simp
  simp_rw [hphase]
  let F : P201Specs.Space n → ℂ := fun y =>
    (g y : ℂ) * ∏ j, (Real.sin ((m j : ℝ) * Real.pi * (y j - a j) / ℓ) : ℂ)
  have hshift : (∫ v : P201Specs.Space n, (g (a+v) : ℂ) *
      ∏ j, (Real.sin ((m j : ℝ) * Real.pi * v j / ℓ) : ℂ)) = ∫ y, F y := by
    calc
      _ = ∫ v : P201Specs.Space n, F (a+v) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun v => by simp [F, PiLp.add_apply])
      _ = _ := integral_add_left_eq_self F a
  rw [hshift]
  apply Eq.symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hgy : g y = 0 := notMem_support.mp (fun h => hy (hgs (subset_tsupport g h)))
  simp [F,hgy]

lemma fourier_oddReflection_lattice_real {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ cube ℓ a) (m : Fin n → ℤ) :
    fourierValue n (oddReflectionSchwartz a g hg hgc) ((2 * ℓ)⁻¹ • latticePoint m) =
      (-2 * Complex.I)^n * ((∫ y in cube ℓ a,
        (∏ j, Real.sin ((m j : ℝ) * Real.pi * (y j - a j) / ℓ)) * g y
          ∂P201Specs.spatialMeasure n : ℝ) : ℂ) := by
  rw [fourier_oddReflection_lattice hℓ a g hg hgc hgs m]
  congr 1
  calc
    _ = ∫ y in cube ℓ a, ((
        (∏ j, Real.sin ((m j : ℝ) * Real.pi * (y j - a j) / ℓ)) * g y : ℝ) : ℂ) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        simp only [Complex.ofReal_mul, Complex.ofReal_prod]
        ring)
    _ = _ := integral_complex_ofReal



end
section

open P201Specs.Heat.Cube (Mode)
open P102.U3.PoissonSummation
lemma reflectedHeatSeries_eq_sineSeries_of_coeff {n : ℕ} {ℓ τ : ℝ}
    (hℓ : 0 < ℓ) (hτ : 0 ≤ τ) (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hcoeff : ∀ z : Fin n → ℤ,
      P102.Specs.U3.fourierValue n (oddReflectionSchwartz a g hg hgc)
        ((2 * ℓ)⁻¹ • latticePoint z) =
      (-2 * Complex.I)^n * ((∫ y in P201Specs.Heat.Cube.cube ℓ a,
        integerSineMode ℓ a z y * g y ∂P201Specs.spatialMeasure n : ℝ) : ℂ))
    (x : P201Specs.Space n) :
    reflectedHeatSeries ℓ a g hg hgc τ x =
      ((∑' m : Mode n, (2 / ℓ)^n * Real.exp (-P201Specs.Heat.Cube.eigenvalue ℓ m * τ) *
        (∫ y in P201Specs.Heat.Cube.cube ℓ a, P201Specs.Heat.Cube.sineMode ℓ a m y * g y
          ∂P201Specs.spatialMeasure n) * P201Specs.Heat.Cube.sineMode ℓ a m x : ℝ) : ℂ) := by
  let φ := oddReflectionSchwartz a g hg hgc
  let B (m : Mode n) : ℝ := ∫ y in P201Specs.Heat.Cube.cube ℓ a,
    P201Specs.Heat.Cube.sineMode ℓ a m y * g y ∂P201Specs.spatialMeasure n
  let A (z : Fin n → ℤ) : ℂ := P102.Specs.U3.fourierValue n φ
    ((2 * ℓ)⁻¹ • latticePoint z)
  let C (z : Fin n → ℤ) : ℂ := (Real.exp (-integerEigenvalue ℓ z * τ) : ℂ) * A z
  let c (m : Mode n) : ℂ := (Real.exp (-P201Specs.Heat.Cube.eigenvalue ℓ m * τ) : ℂ) *
    (-2 * Complex.I)^n * (B m : ℂ)
  have hC : Summable C := by
    apply Summable.of_norm
    refine (fourier_samples_absolute (2 * ℓ) (by positivity) φ).of_nonneg_of_le
      (fun z => norm_nonneg _) ?_
    intro z
    dsimp [C, A]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
      nlinarith [integerEigenvalue_nonneg ℓ z]))
  have hc : ∀ m s, C (signedModeInteger (m,s)) = (reflectionSign s : ℂ) * c m := by
    intro m s
    dsimp [C, A, φ, c, B]
    rw [integerEigenvalue_signed, hcoeff]
    simp_rw [integerSineMode_signed, mul_assoc]
    rw [integral_const_mul]
    push_cast
    ring
  have hzero : ∀ (z : Fin n → ℤ) (j : Fin n), z j = 0 → C z = 0 := by
    intro z j hj
    dsimp [C, A, φ]
    rw [hcoeff]
    simp_rw [integerSineMode_zero_of_coordinate ℓ a z j hj, zero_mul]
    simp
  have hsyn := lattice_sine_synthesis ℓ C hC c hc hzero (x-a)
  have hmode (m : Mode n) : P201Specs.Heat.Cube.sineMode ℓ 0 m (x-a) =
      P201Specs.Heat.Cube.sineMode ℓ a m x := by
    simp [P201Specs.Heat.Cube.sineMode]
  have hnormal : ((((2 * ℓ)^n)⁻¹ : ℝ) : ℂ) * (2 * Complex.I)^n * (-2 * Complex.I)^n =
      (((2 / ℓ)^n : ℝ) : ℂ) := by
    push_cast
    rw [← inv_pow, ← mul_pow, ← mul_pow]
    congr 1
    field_simp
    simp [Complex.I_sq, one_div]
    ring
  unfold reflectedHeatSeries
  simp only [Complex.real_smul, fourierTerm]
  simp_rw [← mul_assoc]
  change ((((2 * ℓ)^n)⁻¹ : ℝ) : ℂ) *
    (∑' z, C z * Complex.exp (((2 * Real.pi * inner ℝ (latticePoint z) (x-a) / (2 * ℓ) : ℝ) : ℂ) * Complex.I)) = _
  rw [hsyn, Complex.ofReal_tsum]
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [hmode]
  dsimp only [c]
  simp only [Complex.ofReal_mul]
  calc
    _ = (((((2 * ℓ)^n)⁻¹ : ℝ) : ℂ) * (2 * Complex.I)^n * (-2 * Complex.I)^n) *
        ((Real.exp (-P201Specs.Heat.Cube.eigenvalue ℓ m * τ) : ℂ) *
          (B m : ℂ) * (P201Specs.Heat.Cube.sineMode ℓ a m x : ℂ)) := by ring
    _ = _ := by rw [hnormal]; dsimp only [B]; ring


lemma reflectedHeatSeries_eq_kernelSolution {n : ℕ} {ℓ τ : ℝ}
    (hℓ : 0 < ℓ) (hτ : 0 < τ) (a : P201Specs.Space n) (g : P201Specs.Space n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ cube ℓ a) (x : P201Specs.Space n) :
    reflectedHeatSeries ℓ a g hg hgc τ x = (kernelSolution ℓ a g τ x : ℂ) := by
  have hcoeff (z : Fin n → ℤ) := fourier_oddReflection_lattice_real hℓ a g hg hgc hgs z
  have h := reflectedHeatSeries_eq_sineSeries_of_coeff hℓ hτ.le a g hg hgc
    (fun z => by simpa only [integerSineMode] using hcoeff z) x
  rw [h, kernelSolution_series hℓ hτ a x
    (hg.continuous.integrable_of_hasCompactSupport hgc).integrableOn]
  congr 1
  apply tsum_congr
  intro m
  ring

theorem kernelInitial : P201Specs.Heat.Cube.kernelInitialStatement := by
  intro n _ ℓ hℓ a g hg hgc hgs
  have hi := reflectedHeatSeries_initial hℓ a g hg hgc hgs
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hi) ε hε,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with τ hτ hτpos x hx
  have hh := hτ x hx
  rw [reflectedHeatSeries_eq_kernelSolution hℓ hτpos a g hg hgc hgs x] at hh
  simpa only [Complex.isometry_ofReal.dist_eq] using hh

theorem kernelNonnegative : P201Specs.Heat.Cube.kernelNonnegativeStatement :=
  kernelNonnegative_of_initial kernelInitial

theorem kernelPositive : P201Specs.Heat.Cube.kernelPositiveStatement :=
  kernelPositive_of_nonnegative kernelNonnegative

theorem kernelLowerBound : P201Specs.Heat.Cube.kernelLowerBoundStatement :=
  kernelLowerBound_of_positive kernelPositive

end
end P201.Heat.Cube
