import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Evolution.Definitions
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.OrbitError
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Ring

noncomputable section

namespace NumAnalysis206.Evolution

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-- Split one nonnegative exact mesh step using the semigroup law. -/
theorem semigroup_mesh_succ (T : StronglyContinuousSemigroup 𝕜 X)
    {h : ℝ} (hh : 0 ≤ h) (j : ℕ) :
    T (((j + 1 : ℕ) : ℝ) * h) = T h * T ((j : ℝ) * h) := by
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
  exact T.map_add h ((j : ℝ) * h) hh (mul_nonneg (Nat.cast_nonneg _) hh)

theorem orbitTelescoping : Specs.NumAnalysis206.Evolution.orbitTelescoping := by
  intro 𝕜 _ X _ _ _ C T x h hh n
  let f : ℕ → X := fun j => (C h ^ (n - j)) (T ((j : ℝ) * h) x)
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      (C h ^ (n - 1 - j)) ((C h - T h) (T ((j : ℝ) * h) x)) =
        f j - f (j + 1) := by
    have hjn : j < n := Finset.mem_range.mp hj
    have he : n - j = (n - 1 - j) + 1 := by omega
    have he' : n - (j + 1) = n - 1 - j := by omega
    dsimp only [f]
    rw [he, he', pow_succ, semigroup_mesh_succ T hh.le]
    simp only [mul_apply_eq_comp, sub_apply, map_sub]
  calc
    (C h ^ n) x - T ((n : ℝ) * h) x = f 0 - f n := by
      simp [f, T.map_zero]
    _ = ∑ j ∈ Finset.range n, (f j - f (j + 1)) := by
      symm
      exact Finset.sum_range_sub' f n
    _ = _ := Finset.sum_congr rfl (fun j hj => (hterm j hj).symm)

/-- The finite orbit maximum bounds every completed one-step defect. -/
theorem norm_orbit_step_le (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (T₀ : ℝ) {h : ℝ} (hh : 0 < h)
    (x : X) {j : ℕ} (hj : ((j : ℝ) + 1) * h ≤ T₀) :
    ‖(C h - T h) (T ((j : ℝ) * h) x)‖ ≤ h * orbitDefect C T T₀ h x := by
  have hmem := (mem_orbitIndices_iff hh j).mpr hj
  have hsup := Finset.le_sup (f := fun j : ℕ => ‖(C h - T h) (T ((j : ℝ) * h) x)‖₊) hmem
  calc
    ‖(C h - T h) (T ((j : ℝ) * h) x)‖ ≤
        (((orbitIndices T₀ h).sup
          (fun j => ‖(C h - T h) (T ((j : ℝ) * h) x)‖₊) : NNReal) : ℝ) := hsup
    _ = h * orbitDefect C T T₀ h x := by
      unfold orbitDefect
      rw [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

theorem orbitDefect_nonneg (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (T₀ : ℝ) {h : ℝ} (hh : 0 < h)
    (x : X) : 0 ≤ orbitDefect C T T₀ h x :=
  mul_nonneg (inv_nonneg.mpr hh.le) (NNReal.coe_nonneg _)

/-- Bound the error at one mesh time by summing propagated orbit defects. -/
theorem mesh_time_error_le [CompleteSpace X] (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) {T₀ h M : ℝ} (hh : 0 < h)
    (hM : 0 ≤ M) (hstable : ∀ k : ℕ, (k : ℝ) * h ≤ T₀ → ‖C h ^ k‖ ≤ M)
    (x : X) (n : ℕ) (hn : (n : ℝ) * h ≤ T₀) :
    ‖(C h ^ n) x - T ((n : ℝ) * h) x‖ ≤ M * T₀ * orbitDefect C T T₀ h x := by
  rw [orbitTelescoping C T x h hh n]
  calc
    ‖∑ j ∈ Finset.range n,
        (C h ^ (n - 1 - j)) ((C h - T h) (T ((j : ℝ) * h) x))‖ ≤
        ∑ j ∈ Finset.range n,
          ‖(C h ^ (n - 1 - j)) ((C h - T h) (T ((j : ℝ) * h) x))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n, M * h * orbitDefect C T T₀ h x := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have hk : ((n - 1 - j : ℕ) : ℝ) * h ≤ T₀ := by
        have hk' : ((n - 1 - j : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (show n - 1 - j ≤ n by omega)
        exact (mul_le_mul_of_nonneg_right hk' hh.le).trans hn
      have hj' : ((j : ℝ) + 1) * h ≤ T₀ := by
        have hjn' : (j : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast (show j + 1 ≤ n by omega)
        exact (mul_le_mul_of_nonneg_right hjn' hh.le).trans hn
      calc
        ‖(C h ^ (n - 1 - j)) ((C h - T h) (T ((j : ℝ) * h) x))‖ ≤
            ‖C h ^ (n - 1 - j)‖ * ‖(C h - T h) (T ((j : ℝ) * h) x)‖ :=
          (C h ^ (n - 1 - j)).le_opNorm _
        _ ≤ M * (h * orbitDefect C T T₀ h x) :=
          mul_le_mul (hstable _ hk) (norm_orbit_step_le C T T₀ hh x hj')
            (norm_nonneg _) hM
        _ = M * h * orbitDefect C T T₀ h x := by ring
    _ = (n : ℝ) * (M * h * orbitDefect C T T₀ h x) := by simp
    _ = M * ((n : ℝ) * h) * orbitDefect C T T₀ h x := by ring
    _ ≤ M * T₀ * orbitDefect C T T₀ h x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hM)
        (orbitDefect_nonneg C T T₀ hh x)

/-- W19's quantitative bound, uniformly over all mesh times. -/
theorem stabilityOrbitErrorBound :
    Specs.NumAnalysis206.Evolution.stabilityOrbitErrorBound := by
  intro 𝕜 _ X _ _ _ C T T₀ h₀ M hT₀ _h₀ hstable x h hh hhh₀
  have hM : 0 ≤ M := (norm_nonneg (C h ^ 0)).trans
    (hstable h hh hhh₀ 0 (by simpa using hT₀.le))
  have hbound : 0 ≤ M * T₀ * orbitDefect C T T₀ h x :=
    mul_nonneg (mul_nonneg hM hT₀.le) (orbitDefect_nonneg C T T₀ hh x)
  change (((meshIndices T₀ h).sup
    (fun n => ‖(C h ^ n) x - T ((n : ℝ) * h) x‖₊) : NNReal) : ℝ) ≤ _
  change (meshIndices T₀ h).sup
    (fun n => ‖(C h ^ n) x - T ((n : ℝ) * h) x‖₊) ≤
    (⟨M * T₀ * orbitDefect C T T₀ h x, hbound⟩ : NNReal)
  apply Finset.sup_le
  intro n hn
  exact mesh_time_error_le C T hh hM (hstable h hh hhh₀) x n
    ((mem_meshIndices_iff hh n).mp hn)

/-- A step exceeding the horizon has zero mesh error and empty orbit defect. -/
theorem meshErrorBeyondHorizon :
    Specs.NumAnalysis206.Evolution.meshErrorBeyondHorizon := by
  intro 𝕜 _ X _ _ _ C T T₀ h x hh hTh
  have horbit : orbitIndices T₀ h = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hj' := (mem_orbitIndices_iff hh j).mp hj
    have hnonneg : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    nlinarith
  have hmesh : (meshIndices T₀ h).sup
      (fun n => ‖(C h ^ n) x - T ((n : ℝ) * h) x‖₊) = 0 := by
    apply (Finset.sup_eq_bot_iff _ _).mpr
    intro n hn
    have hn' := (mem_meshIndices_iff hh n).mp hn
    have hnzero : n = 0 := by
      by_contra hnzero
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnzero)
      have := mul_le_mul_of_nonneg_right hn1 hh.le
      linarith
    subst n
    simp [T.map_zero]
  constructor
  · unfold meshError
    rw [hmesh]
    rfl
  · simp [orbitDefect, horbit]

end NumAnalysis206.Evolution
