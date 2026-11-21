import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.GreenKernel
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.EvolutionMatrix
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator ContDiff

namespace D13Unified.Ch10.GreenKernel

lemma continuousOn_Q (P : Problem) (c : ℝ) : ContinuousOn (Q P c) (interval P) :=
  P.q_continuous.add (continuousOn_const.mul P.w_continuous)

/-- Compactness bounds (1−q)/w above, and w is strictly positive everywhere
on the closed interval. No global coefficient bounds are assumed. -/
theorem shift_exists : Specs.D13Unified.Ch10.GreenKernel.ShiftExists := by
  intro P
  have h : ContinuousOn (fun x => (1 - P.q x) / P.w x) (interval P) :=
    (continuousOn_const.sub P.q_continuous).div P.w_continuous
      (fun x hx => ne_of_gt (P.w_positive x hx))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  have hb : (1 - P.q x) / P.w x ≤ max 1 M :=
    (le_abs_self _).trans ((hM x hx).trans (le_max_right _ _))
  have hm := (div_le_iff₀ (P.w_positive x hx)).mp hb
  dsimp [Q]
  linarith

lemma continuousOn_systemMatrix (P : Problem) (c : ℝ) :
    ContinuousOn (systemMatrix P c) (interval P) := by
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  fin_cases i <;> fin_cases j
  · exact continuousOn_const
  · exact P.p_regular.continuousOn.inv₀ (fun x hx => ne_of_gt (P.p_positive x hx))
  · exact continuousOn_Q P c
  · exact continuousOn_const

/-- Coordinate extraction is continuous for the matrix operator norm used by
EvolutionMatrix. This avoids confusing that norm with the iterated Pi norm. -/
private def matrixEntry (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun M => M i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

lemma column_regularity (P : Problem) (c s : ℝ) (hs : s ∈ interval P) (i j : Fin 2) :
    ContDiffOn ℝ 1 (fun x => Ch07.EvolutionMatrix.U (timeInterval P)
      (systemMatrix P c) x s i j) (interval P) := by
  exact (matrixEntry i j).contDiff.comp_contDiffOn
    (Ch07.EvolutionMatrix.contDiffOn_U (timeInterval P) (systemMatrix P c) s hs
      (continuousOn_systemMatrix P c))

lemma column_derivative (P : Problem) (c s x : ℝ) (hs : s ∈ interval P)
    (hx : x ∈ interval P) (i j : Fin 2) :
    HasDerivWithinAt (fun t => Ch07.EvolutionMatrix.U (timeInterval P)
      (systemMatrix P c) t s i j)
      ((systemMatrix P c x * Ch07.EvolutionMatrix.U (timeInterval P)
        (systemMatrix P c) x s) i j) (interval P) x := by
  exact (matrixEntry i j).hasFDerivAt.comp_hasDerivWithinAt x
    (Ch07.EvolutionMatrix.hasDerivWithinAt_U (timeInterval P) (systemMatrix P c) s hs
      (continuousOn_systemMatrix P c) x hx)

lemma left_mode_c1 (P : Problem) (c : ℝ) :
    ContDiffOn ℝ 1 (leftMode P c) (interval P) :=
  column_regularity P c P.a (left_mem_Icc.mpr P.a_lt_b.le) 0 1

lemma left_flux_c1 (P : Problem) (c : ℝ) :
    ContDiffOn ℝ 1 (leftFlux P c) (interval P) :=
  column_regularity P c P.a (left_mem_Icc.mpr P.a_lt_b.le) 1 1

lemma right_mode_c1 (P : Problem) (c : ℝ) :
    ContDiffOn ℝ 1 (rightMode P c) (interval P) :=
  (column_regularity P c P.b (right_mem_Icc.mpr P.a_lt_b.le) 0 1).neg

lemma right_flux_c1 (P : Problem) (c : ℝ) :
    ContDiffOn ℝ 1 (rightFlux P c) (interval P) :=
  (column_regularity P c P.b (right_mem_Icc.mpr P.a_lt_b.le) 1 1).neg

lemma left_mode_derivative (P : Problem) (c x : ℝ) (hx : x ∈ interval P) :
    HasDerivWithinAt (leftMode P c) (leftFlux P c x / P.p x) (interval P) x := by
  convert! column_derivative P c P.a x (left_mem_Icc.mpr P.a_lt_b.le) hx 0 1 using 1;
    simp [leftFlux, systemMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      div_eq_mul_inv, mul_comm]

lemma left_flux_derivative (P : Problem) (c x : ℝ) (hx : x ∈ interval P) :
    HasDerivWithinAt (leftFlux P c) (Q P c x * leftMode P c x) (interval P) x := by
  convert! column_derivative P c P.a x (left_mem_Icc.mpr P.a_lt_b.le) hx 1 1 using 1;
    simp [leftMode, systemMatrix, Matrix.mul_apply, Fin.sum_univ_two]

lemma right_mode_derivative (P : Problem) (c x : ℝ) (hx : x ∈ interval P) :
    HasDerivWithinAt (rightMode P c) (rightFlux P c x / P.p x) (interval P) x := by
  convert! (column_derivative P c P.b x (right_mem_Icc.mpr P.a_lt_b.le) hx 0 1).neg using 1;
    simp [rightFlux, systemMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      div_eq_mul_inv, mul_comm]

lemma right_flux_derivative (P : Problem) (c x : ℝ) (hx : x ∈ interval P) :
    HasDerivWithinAt (rightFlux P c) (Q P c x * rightMode P c x) (interval P) x := by
  convert! (column_derivative P c P.b x (right_mem_Icc.mpr P.a_lt_b.le) hx 1 1).neg using 1;
    simp [rightMode, systemMatrix, Matrix.mul_apply, Fin.sum_univ_two]

lemma left_initial (P : Problem) (c : ℝ) :
    leftMode P c P.a = 0 ∧ leftFlux P c P.a = 1 := by
  have hi := Ch07.EvolutionMatrix.U_self (timeInterval P) (systemMatrix P c) P.a
    (left_mem_Icc.mpr P.a_lt_b.le) (continuousOn_systemMatrix P c)
  simp [leftMode, leftFlux, hi]

lemma right_initial (P : Problem) (c : ℝ) :
    rightMode P c P.b = 0 ∧ rightFlux P c P.b = -1 := by
  have hi := Ch07.EvolutionMatrix.U_self (timeInterval P) (systemMatrix P c) P.b
    (right_mem_Icc.mpr P.a_lt_b.le) (continuousOn_systemMatrix P c)
  simp [rightMode, rightFlux, hi]

lemma left_flux_eq (P : Problem) (c x : ℝ) (hx : x ∈ interval P) :
    P.p x * derivWithin (leftMode P c) (interval P) x = leftFlux P c x := by
  rw [(left_mode_derivative P c x hx).derivWithin (uniqueDiffOn_Icc P.a_lt_b x hx)]
  field_simp [ne_of_gt (P.p_positive x hx)]

lemma right_flux_eq (P : Problem) (c x : ℝ) (hx : x ∈ interval P) :
    P.p x * derivWithin (rightMode P c) (interval P) x = rightFlux P c x := by
  rw [(right_mode_derivative P c x hx).derivWithin (uniqueDiffOn_Icc P.a_lt_b x hx)]
  field_simp [ne_of_gt (P.p_positive x hx)]

lemma left_mode_c2 (P : Problem) (c : ℝ) :
    ContDiffOn ℝ 2 (leftMode P c) (interval P) := by
  apply (contDiffOn_succ_iff_derivWithin (f := leftMode P c) (n := 1)
    (uniqueDiffOn_Icc P.a_lt_b)).mpr
  refine ⟨fun x hx => (left_mode_derivative P c x hx).differentiableWithinAt,
    by simp, ?_⟩
  apply ((left_flux_c1 P c).div P.p_regular
    (fun x hx => ne_of_gt (P.p_positive x hx))).congr
  intro x hx
  exact (left_mode_derivative P c x hx).derivWithin (uniqueDiffOn_Icc P.a_lt_b x hx)

lemma right_mode_c2 (P : Problem) (c : ℝ) :
    ContDiffOn ℝ 2 (rightMode P c) (interval P) := by
  apply (contDiffOn_succ_iff_derivWithin (f := rightMode P c) (n := 1)
    (uniqueDiffOn_Icc P.a_lt_b)).mpr
  refine ⟨fun x hx => (right_mode_derivative P c x hx).differentiableWithinAt,
    by simp, ?_⟩
  apply ((right_flux_c1 P c).div P.p_regular
    (fun x hx => ne_of_gt (P.p_positive x hx))).congr
  intro x hx
  exact (right_mode_derivative P c x hx).derivWithin (uniqueDiffOn_Icc P.a_lt_b x hx)

/-- Normalized classical homogeneous solutions, including both endpoints. -/
theorem modes : Specs.D13Unified.Ch10.GreenKernel.Modes := by
  intro P c
  refine ⟨left_mode_c2 P c, right_mode_c2 P c,
    (left_initial P c).1, (right_initial P c).1, ?_, ?_, ?_, ?_⟩
  · rw [left_flux_eq P c P.a (left_mem_Icc.mpr P.a_lt_b.le), (left_initial P c).2]
  · rw [right_flux_eq P c P.b (right_mem_Icc.mpr P.a_lt_b.le), (right_initial P c).2]
  · intro x hx
    have hd := (left_flux_derivative P c x hx).congr_of_mem
      (fun t ht => left_flux_eq P c t ht) hx
    rw [hd.derivWithin (uniqueDiffOn_Icc P.a_lt_b x hx)]
    ring
  · intro x hx
    have hd := (right_flux_derivative P c x hx).congr_of_mem
      (fun t ht => right_flux_eq P c t ht) hx
    rw [hd.derivWithin (uniqueDiffOn_Icc P.a_lt_b x hx)]
    ring

/-- Invertibility excludes a zero state in a normalized evolution column. -/
lemma column_nonzero (P : Problem) (c s x : ℝ) (hs : s ∈ interval P)
    (hx : x ∈ interval P) :
    Ch07.EvolutionMatrix.U (timeInterval P) (systemMatrix P c) x s 0 1 ≠ 0 ∨
    Ch07.EvolutionMatrix.U (timeInterval P) (systemMatrix P c) x s 1 1 ≠ 0 := by
  by_contra! h
  have hi := Ch07.EvolutionMatrix.composition ℝ 2 (timeInterval P) (systemMatrix P c)
    (continuousOn_systemMatrix P c) x hx s hs s hs
  rw [Ch07.EvolutionMatrix.U_self (timeInterval P) (systemMatrix P c) s hs
    (continuousOn_systemMatrix P c)] at hi
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hi
  simp [Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2] at he

/-- A useful positivity proof which does not presuppose the sign of the mode:
(y·py′)′ = (py′)²/p + Qy² is strictly positive for a nonzero state. -/
lemma energy_increasing (P : Problem) (c : ℝ) (f g : ℝ → ℝ)
    (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x)
    (hf : ContinuousOn f (interval P)) (hg : ContinuousOn g (interval P))
    (hfd : ∀ x ∈ interval P, HasDerivWithinAt f (g x / P.p x) (interval P) x)
    (hgd : ∀ x ∈ interval P, HasDerivWithinAt g (Q P c x * f x) (interval P) x)
    (hn : ∀ x ∈ interval P, f x ≠ 0 ∨ g x ≠ 0) :
    StrictMonoOn (fun x => f x * g x) (interval P) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fun x =>
    g x / P.p x * g x + f x * (Q P c x * f x)) (convex_Icc _ _) (hf.mul hg)
  · intro x hx
    exact ((hfd x (interior_subset hx)).mul (hgd x (interior_subset hx))).mono interior_subset
  · intro x hx
    have hxI := interior_subset hx
    have hp := P.p_positive x hxI
    have hq : 0 < Q P c x := lt_of_lt_of_le zero_lt_one (hQ x hxI)
    have he : g x / P.p x * g x + f x * (Q P c x * f x) =
        g x ^ 2 / P.p x + Q P c x * f x ^ 2 := by ring
    rw [he]
    rcases hn x hxI with h | h
    · exact add_pos_of_nonneg_of_pos (div_nonneg (sq_nonneg _) hp.le)
        (mul_pos hq (sq_pos_of_ne_zero h))
    · exact add_pos_of_pos_of_nonneg (div_pos (sq_pos_of_ne_zero h) hp)
        (mul_nonneg hq.le (sq_nonneg _))

lemma left_mode_positive (P : Problem) (c : ℝ)
    (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x) :
    ∀ x ∈ Ioc P.a P.b, 0 < leftMode P c x := by
  have hmono := energy_increasing P c (leftMode P c) (leftFlux P c) hQ
    (left_mode_c1 P c).continuousOn (left_flux_c1 P c).continuousOn
    (left_mode_derivative P c) (left_flux_derivative P c)
    (fun x hx => column_nonzero P c P.a x (left_mem_Icc.mpr P.a_lt_b.le) hx)
  have hpos : ∀ x ∈ Ioc P.a P.b, 0 < leftMode P c x * leftFlux P c x := by
    intro x hx
    simpa only [(left_initial P c).1, zero_mul] using
      hmono (left_mem_Icc.mpr P.a_lt_b.le) ⟨hx.1.le, hx.2⟩ hx.1
  intro x hx
  have hg : 0 < leftFlux P c x := by
    by_contra! h
    obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' hx.1.le
      ((left_flux_c1 P c).continuousOn.mono (Icc_subset_Icc_right hx.2))
      (show 0 ∈ Icc (leftFlux P c x) (leftFlux P c P.a) by
        rw [(left_initial P c).2]; exact ⟨h, zero_le_one⟩)
    have hza : P.a < z := lt_of_le_of_ne hz.1 (by
      intro he; rw [← he, (left_initial P c).2] at hzero; norm_num at hzero)
    have hp := hpos z ⟨hza, hz.2.trans hx.2⟩
    rw [hzero, mul_zero] at hp
    exact (lt_irrefl 0) hp
  exact pos_of_mul_pos_left (hpos x hx) hg.le

lemma right_mode_positive (P : Problem) (c : ℝ)
    (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x) :
    ∀ x ∈ Ico P.a P.b, 0 < rightMode P c x := by
  have hn : ∀ x ∈ interval P, rightMode P c x ≠ 0 ∨ rightFlux P c x ≠ 0 := by
    intro x hx
    simpa only [rightMode, rightFlux, neg_ne_zero] using
      column_nonzero P c P.b x (right_mem_Icc.mpr P.a_lt_b.le) hx
  have hmono := energy_increasing P c (rightMode P c) (rightFlux P c) hQ
    (right_mode_c1 P c).continuousOn (right_flux_c1 P c).continuousOn
    (right_mode_derivative P c) (right_flux_derivative P c) hn
  have hneg : ∀ x ∈ Ico P.a P.b, rightMode P c x * rightFlux P c x < 0 := by
    intro x hx
    simpa only [(right_initial P c).1, zero_mul] using
      hmono ⟨hx.1, hx.2.le⟩ (right_mem_Icc.mpr P.a_lt_b.le) hx.2
  intro x hx
  have hg : rightFlux P c x < 0 := by
    by_contra! h
    obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' hx.2.le
      ((right_flux_c1 P c).continuousOn.mono (Icc_subset_Icc_left hx.1))
      (show 0 ∈ Icc (rightFlux P c P.b) (rightFlux P c x) by
        rw [(right_initial P c).2]; exact ⟨by norm_num, h⟩)
    have hzb : z < P.b := lt_of_le_of_ne hz.2 (by
      intro he; rw [he, (right_initial P c).2] at hzero; norm_num at hzero)
    have hp := hneg z ⟨hx.1.trans hz.1, hzb⟩
    rw [hzero, mul_zero] at hp
    exact (lt_irrefl 0) hp
  nlinarith [hneg x hx]

/-- Constancy of the Wronskian, without any sign assumption on Q. -/
lemma wronskian_constant (P : Problem) (c x : ℝ) (hx : x ∈ interval P) :
    wronskian P c x = denominator P c := by
  let W := fun t => leftFlux P c t * rightMode P c t - leftMode P c t * rightFlux P c t
  have hc : ContinuousOn W (interval P) :=
    ((left_flux_c1 P c).continuousOn.mul (right_mode_c1 P c).continuousOn).sub
      ((left_mode_c1 P c).continuousOn.mul (right_flux_c1 P c).continuousOn)
  have hd : ∀ t ∈ interval P, HasDerivWithinAt W 0 (interval P) t := by
    intro t ht
    convert! ((left_flux_derivative P c t ht).mul (right_mode_derivative P c t ht)).sub
      ((left_mode_derivative P c t ht).mul (right_flux_derivative P c t ht)) using 1; ring
  have hint := integral_eq_sub_on_interval ordConnected_Icc hc continuousOn_const hd
    (left_mem_Icc.mpr P.a_lt_b.le) hx
  have hWa : W P.a = denominator P c := by
    simp [W, (left_initial P c).1, (left_initial P c).2, denominator]
  have hconst : W x = denominator P c := by
    simpa only [intervalIntegral.integral_zero, hWa, sub_eq_zero] using hint.symm
  calc
    wronskian P c x =
        (P.p x * derivWithin (leftMode P c) (interval P) x) * rightMode P c x -
        leftMode P c x * (P.p x * derivWithin (rightMode P c) (interval P) x) := by
      dsimp [wronskian]; ring
    _ = W x := by rw [left_flux_eq P c x hx, right_flux_eq P c x hx]
    _ = denominator P c := hconst

theorem positive_modes : Specs.D13Unified.Ch10.GreenKernel.PositiveModes := by
  intro P c _ hQ
  exact ⟨left_mode_positive P c hQ, right_mode_positive P c hQ,
    right_mode_positive P c hQ P.a ⟨le_rfl, P.a_lt_b⟩,
    fun x hx => wronskian_constant P c x hx⟩

theorem kernel_symmetry : Specs.D13Unified.Ch10.GreenKernel.KernelSymmetry := by
  intro P c x t
  simp only [kernel, min_comm x t, max_comm x t]

theorem kernel_boundary : Specs.D13Unified.Ch10.GreenKernel.KernelBoundary := by
  intro P c t ht
  constructor
  · simp [kernel, min_eq_left ht.1, max_eq_right ht.1, (left_initial P c).1]
  · simp [kernel, min_eq_right ht.2, max_eq_left ht.2, (right_initial P c).1]

theorem kernel_continuity : Specs.D13Unified.Ch10.GreenKernel.KernelContinuity := by
  intro P c
  apply ContinuousOn.div_const
  apply ContinuousOn.mul
  · exact (left_mode_c1 P c).continuousOn.comp
      (continuous_fst.min continuous_snd).continuousOn
      (fun z hz => ⟨le_min hz.1.1 hz.2.1, (min_le_left _ _).trans hz.1.2⟩)
  · exact (right_mode_c1 P c).continuousOn.comp
      (continuous_fst.max continuous_snd).continuousOn
      (fun z hz => ⟨hz.1.1.trans (le_max_left _ _), max_le hz.1.2 hz.2.2⟩)

theorem kernel_positivity : Specs.D13Unified.Ch10.GreenKernel.KernelPositivity := by
  intro P c hc hQ x hx t ht
  obtain ⟨hu, hv, hD, _⟩ := positive_modes P c hc hQ
  exact div_pos (mul_pos (hu _ ⟨lt_min hx.1 ht.1, (min_le_left _ _).trans hx.2.le⟩)
    (hv _ ⟨hx.1.le.trans (le_max_left _ _), max_lt hx.2 ht.2⟩)) hD

theorem kernel_jump : Specs.D13Unified.Ch10.GreenKernel.KernelJump := by
  intro P c hc hQ t ht
  have htI : t ∈ interval P := ⟨ht.1.le, ht.2.le⟩
  have hD := (positive_modes P c hc hQ).2.2.1.ne'
  have hld := (left_mode_derivative P c t htI).derivWithin (uniqueDiffOn_Icc P.a_lt_b t htI)
  have hrd := (right_mode_derivative P c t htI).derivWithin (uniqueDiffOn_Icc P.a_lt_b t htI)
  refine ⟨?_, ?_, ?_⟩
  · rw [hld]
    apply (((left_mode_derivative P c t htI).mul_const (rightMode P c t)).div_const
      (denominator P c)).congr_mono _ _ (Icc_subset_Icc_right ht.2.le)
    · intro x hx
      simp [kernel, min_eq_left hx.2, max_eq_right hx.2]
    · simp [kernel]
  · rw [hrd]
    apply (((right_mode_derivative P c t htI).const_mul (leftMode P c t)).div_const
      (denominator P c)).congr_mono _ _ (Icc_subset_Icc_left ht.1.le)
    · intro x hx
      simp [kernel, min_eq_right hx.1, max_eq_left hx.1]
    · simp [kernel]
  · have hw := wronskian_constant P c t htI
    dsimp [wronskian] at hw
    field_simp [hD]
    nlinarith only [hw]


private lemma cast_derivative {𝕂 : Type} [RCLike 𝕂] {f : ℝ → ℝ} {d x : ℝ}
    {S : Set ℝ} (hf : HasDerivWithinAt f d S x) :
    HasDerivWithinAt (fun t => (f t : 𝕂)) (d : 𝕂) S x := by
  exact (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂).hasFDerivAt.comp_hasDerivWithinAt x hf

private lemma cast_continuous {𝕂 : Type} [RCLike 𝕂] {f : ℝ → ℝ} {S : Set ℝ}
    (hf : ContinuousOn f S) : ContinuousOn (fun t => (f t : 𝕂)) S :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂).continuous.comp_continuousOn hf

private lemma kernel_integral_split {𝕂 : Type} [RCLike 𝕂] (P : Problem) (c : ℝ)
    (f : ℝ → 𝕂) (hf : ContinuousOn f (interval P)) (x : ℝ) (hx : x ∈ interval P) :
    applyKernel P c f x =
      ((rightMode P c x : 𝕂) * (∫ t in P.a..x, (leftMode P c t : 𝕂) * f t * (P.w t : 𝕂)) +
       (leftMode P c x : 𝕂) * (∫ t in x..P.b, (rightMode P c t : 𝕂) * f t * (P.w t : 𝕂))) /
        (denominator P c : 𝕂) := by
  have hk : ContinuousOn (fun t => (kernel P c x t : 𝕂) * f t * (P.w t : 𝕂))
      (interval P) :=
    ((cast_continuous ((kernel_continuity P c).comp (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => ⟨hx, ht⟩))).mul hf).mul (cast_continuous P.w_continuous)
  have ha := (hk.mono (show uIcc P.a x ⊆ interval P by
    rw [uIcc_of_le hx.1]; exact Icc_subset_Icc_right hx.2)).intervalIntegrable (μ := volume)
  have hb := (hk.mono (show uIcc x P.b ⊆ interval P by
    rw [uIcc_of_le hx.2]; exact Icc_subset_Icc_left hx.1)).intervalIntegrable (μ := volume)
  unfold applyKernel
  rw [← intervalIntegral.integral_add_adjacent_intervals ha hb]
  have hleft : (∫ t in P.a..x, (kernel P c x t : 𝕂) * f t * (P.w t : 𝕂)) =
      ((rightMode P c x : 𝕂) / (denominator P c : 𝕂)) *
        (∫ t in P.a..x, (leftMode P c t : 𝕂) * f t * (P.w t : 𝕂)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    simp only [kernel, min_eq_right ht.2, max_eq_left ht.2,
      RCLike.ofReal_div, RCLike.ofReal_mul]
    ring
  have hright : (∫ t in x..P.b, (kernel P c x t : 𝕂) * f t * (P.w t : 𝕂)) =
      ((leftMode P c x : 𝕂) / (denominator P c : 𝕂)) *
        (∫ t in x..P.b, (rightMode P c t : 𝕂) * f t * (P.w t : 𝕂)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.2] at ht
    simp only [kernel, min_eq_left ht.1, max_eq_right ht.1,
      RCLike.ofReal_div, RCLike.ofReal_mul]
    ring
  rw [hleft, hright]
  ring

theorem inverse_continuous : Specs.D13Unified.Ch10.GreenKernel.InverseContinuous := by
  intro 𝕂 _ P c hc hQ f hf
  let U : ℝ → 𝕂 := fun x => (leftMode P c x : 𝕂)
  let V : ℝ → 𝕂 := fun x => (rightMode P c x : 𝕂)
  let UF : ℝ → 𝕂 := fun x => (leftFlux P c x : 𝕂)
  let VF : ℝ → 𝕂 := fun x => (rightFlux P c x : 𝕂)
  let pp : ℝ → 𝕂 := fun x => (P.p x : 𝕂)
  let qq : ℝ → 𝕂 := fun x => (Q P c x : 𝕂)
  let F : ℝ → 𝕂 := fun x => f x * (P.w x : 𝕂)
  let d : 𝕂 := (denominator P c : 𝕂)
  let A : ℝ → 𝕂 := fun x => ∫ t in P.a..x, U t * F t
  let B : ℝ → 𝕂 := fun x => ∫ t in x..P.b, V t * F t
  let Y : ℝ → 𝕂 := fun x => (V x * A x + U x * B x) / d
  let Z : ℝ → 𝕂 := fun x => (VF x * A x + UF x * B x) / d
  have ha : P.a ∈ interval P := left_mem_Icc.mpr P.a_lt_b.le
  have hb : P.b ∈ interval P := right_mem_Icc.mpr P.a_lt_b.le
  have ud := uniqueDiffOn_Icc P.a_lt_b
  have hpc : ContinuousOn pp (interval P) := cast_continuous P.p_regular.continuousOn
  have hqc : ContinuousOn qq (interval P) := cast_continuous (continuousOn_Q P c)
  have hFc : ContinuousOn F (interval P) := hf.mul (cast_continuous P.w_continuous)
  have hUc : ContinuousOn U (interval P) := cast_continuous (left_mode_c1 P c).continuousOn
  have hVc : ContinuousOn V (interval P) := cast_continuous (right_mode_c1 P c).continuousOn
  have hUFc : ContinuousOn UF (interval P) := cast_continuous (left_flux_c1 P c).continuousOn
  have hVFc : ContinuousOn VF (interval P) := cast_continuous (right_flux_c1 P c).continuousOn
  have hp0 : ∀ x ∈ interval P, pp x ≠ 0 := fun x hx =>
    RCLike.ofReal_ne_zero.mpr (P.p_positive x hx).ne'
  have hd0 : d ≠ 0 := RCLike.ofReal_ne_zero.mpr (positive_modes P c hc hQ).2.2.1.ne'
  have hUd : ∀ x ∈ interval P, HasDerivWithinAt U (UF x / pp x) (interval P) x := by
    intro x hx
    convert! cast_derivative (𝕂 := 𝕂) (left_mode_derivative P c x hx) using 1
    simp [UF, pp]
  have hVd : ∀ x ∈ interval P, HasDerivWithinAt V (VF x / pp x) (interval P) x := by
    intro x hx
    convert! cast_derivative (𝕂 := 𝕂) (right_mode_derivative P c x hx) using 1
    simp [VF, pp]
  have hUFd : ∀ x ∈ interval P, HasDerivWithinAt UF (qq x * U x) (interval P) x := by
    intro x hx
    convert! cast_derivative (𝕂 := 𝕂) (left_flux_derivative P c x hx) using 1
    simp [qq, U]
  have hVFd : ∀ x ∈ interval P, HasDerivWithinAt VF (qq x * V x) (interval P) x := by
    intro x hx
    convert! cast_derivative (𝕂 := 𝕂) (right_flux_derivative P c x hx) using 1
    simp [qq, V]
  have hAd : ∀ x ∈ interval P, HasDerivWithinAt A (U x * F x) (interval P) x :=
    fun x hx => hasDerivWithinAt_integral_on_interval ordConnected_Icc (hUc.mul hFc) ha hx
  have hBd : ∀ x ∈ interval P, HasDerivWithinAt B (-V x * F x) (interval P) x := by
    intro x hx
    convert! (hasDerivWithinAt_integral_on_interval ordConnected_Icc (hVc.mul hFc) hb hx).neg using 1
    · exact funext fun z => intervalIntegral.integral_symm P.b z
    · simp only [Pi.mul_apply, neg_mul]
  have hAc : ContinuousOn A (interval P) := fun x hx => (hAd x hx).continuousWithinAt
  have hBc : ContinuousOn B (interval P) := fun x hx => (hBd x hx).continuousWithinAt
  have hYc : ContinuousOn Y (interval P) := ((hVc.mul hAc).add (hUc.mul hBc)).div_const d
  have hZc : ContinuousOn Z (interval P) := ((hVFc.mul hAc).add (hUFc.mul hBc)).div_const d
  have hW : ∀ x ∈ interval P, UF x * V x - U x * VF x = d := by
    intro x hx
    have hw := wronskian_constant P c x hx
    have hreal : leftFlux P c x * rightMode P c x - leftMode P c x * rightFlux P c x =
        denominator P c := by
      rw [← hw]
      dsimp [wronskian]
      rw [← left_flux_eq P c x hx, ← right_flux_eq P c x hx]
      ring
    dsimp [UF, V, U, VF, d]
    simpa only [RCLike.ofReal_sub, RCLike.ofReal_mul] using congrArg (fun z : ℝ => (z : 𝕂)) hreal
  have hYd : ∀ x ∈ interval P, HasDerivWithinAt Y (Z x / pp x) (interval P) x := by
    intro x hx
    convert! (((hVd x hx).mul (hAd x hx)).add ((hUd x hx).mul (hBd x hx))).div_const d using 1
    dsimp [Z]
    ring
  have hZd : ∀ x ∈ interval P, HasDerivWithinAt Z (qq x * Y x - F x) (interval P) x := by
    intro x hx
    convert! (((hVFd x hx).mul (hAd x hx)).add ((hUFd x hx).mul (hBd x hx))).div_const d using 1
    dsimp [Y]
    field_simp [hd0]
    linear_combination (F x) * hW x hx
  have hZreg : ContDiffOn ℝ 1 Z (interval P) :=
    Ch07.LinearSystemExistence.regularity ((hqc.mul hYc).sub hFc) hZd
  have hYreg : ContDiffOn ℝ 2 Y (interval P) := by
    apply (contDiffOn_succ_iff_derivWithin (f := Y) (n := 1) ud).mpr
    refine ⟨fun x hx => (hYd x hx).differentiableWithinAt, by simp, ?_⟩
    have hpr : ContDiffOn ℝ 1 pp (interval P) :=
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂).contDiff.comp_contDiffOn P.p_regular
    apply (hZreg.mul (hpr.inv hp0)).congr
    intro x hx
    convert! (hYd x hx).derivWithin (ud x hx) using 1; simp [div_eq_mul_inv]
  have hYa : Y P.a = 0 := by
    simp [Y, A, U, (left_initial P c).1]
  have hYb : Y P.b = 0 := by
    simp [Y, B, V, (right_initial P c).1]
  have hflux : ∀ x ∈ interval P, pp x * derivWithin Y (interval P) x = Z x := by
    intro x hx
    rw [(hYd x hx).derivWithin (ud x hx)]
    field_simp [hp0 x hx]
  have hYsol : IsDirichletSolution P c f Y := by
    refine ⟨hYreg, hYa, hYb, ?_⟩
    intro x hx
    have hd := (hZd x hx).congr_of_mem hflux hx
    rw [hd.derivWithin (ud x hx)]
    dsimp [F]
    ring
  have hsplit : EqOn (applyKernel P c f) Y (interval P) := by
    intro x hx
    convert! kernel_integral_split P c f hf x hx using 1;
      simp only [Y, A, B, U, V, F, d, mul_assoc]
  refine ⟨?_, ?_⟩
  · refine ⟨hYreg.congr hsplit, ?_, ?_, ?_⟩
    · rw [hsplit ha]; exact hYa
    · rw [hsplit hb]; exact hYb
    · intro x hx
      have heq : EqOn (derivWithin (applyKernel P c f) (interval P))
          (derivWithin Y (interval P)) (interval P) := by
        intro t ht
        exact (derivWithin_congr hsplit (hsplit ht))
      have heq2 : EqOn
          (fun t => (P.p t : 𝕂) * derivWithin (applyKernel P c f) (interval P) t)
          (fun t => (P.p t : 𝕂) * derivWithin Y (interval P) t) (interval P) :=
        fun t ht => congrArg (fun z => (P.p t : 𝕂) * z) (heq ht)
      rw [derivWithin_congr heq2 (heq2 hx), hsplit hx]
      exact hYsol.2.2.2 x hx
  · intro y hy x hx
    let z : ℝ → 𝕂 := fun t => pp t * derivWithin y (interval P) t
    have hyc := hy.1.continuousOn
    have hpr : ContDiffOn ℝ 1 pp (interval P) :=
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂).contDiff.comp_contDiffOn P.p_regular
    have hzreg : ContDiffOn ℝ 1 z (interval P) :=
      hpr.mul (hy.1.derivWithin ud (by norm_num))
    have hzc := hzreg.continuousOn
    have hyd : ∀ t ∈ interval P, HasDerivWithinAt y (z t / pp t) (interval P) t := by
      intro t ht
      have hd := (hy.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt
      convert! hd using 1
      dsimp [z]
      field_simp [hp0 t ht]
    have hzd : ∀ t ∈ interval P, HasDerivWithinAt z (qq t * y t - F t) (interval P) t := by
      intro t ht
      have heq := hy.2.2.2 t ht
      change -derivWithin z (interval P) t + qq t * y t = (P.w t : 𝕂) * f t at heq
      have he : qq t * y t - F t = derivWithin z (interval P) t := by
        dsimp [F]
        linear_combination heq
      rw [he]
      exact (hzreg.differentiableOn (by norm_num) t ht).hasDerivWithinAt
    let LA : ℝ → 𝕂 := fun t => UF t * y t - U t * z t
    let LB : ℝ → 𝕂 := fun t => V t * z t - VF t * y t
    have hLAc : ContinuousOn LA (interval P) := (hUFc.mul hyc).sub (hUc.mul hzc)
    have hLBc : ContinuousOn LB (interval P) := (hVc.mul hzc).sub (hVFc.mul hyc)
    have hLAd : ∀ t ∈ interval P, HasDerivWithinAt LA (U t * F t) (interval P) t := by
      intro t ht
      convert! ((hUFd t ht).mul (hyd t ht)).sub ((hUd t ht).mul (hzd t ht)) using 1
      ring
    have hLBd : ∀ t ∈ interval P, HasDerivWithinAt LB (-V t * F t) (interval P) t := by
      intro t ht
      convert! ((hVd t ht).mul (hzd t ht)).sub ((hVFd t ht).mul (hyd t ht)) using 1
      ring
    have hLAa : LA P.a = 0 := by simp [LA, hy.2.1, U, (left_initial P c).1]
    have hLBb : LB P.b = 0 := by simp [LB, hy.2.2.1, V, (right_initial P c).1]
    have heA : LA x = A x := by
      have hi := integral_eq_sub_on_interval ordConnected_Icc hLAc (hUc.mul hFc) hLAd ha hx
      convert! hi.symm using 1; simp only [hLAa, sub_zero]
    have heB : LB x = B x := by
      have hi := integral_eq_sub_on_interval ordConnected_Icc hLBc
        ((hVc.mul hFc).neg) (fun t ht => by
          convert! hLBd t ht using 1; simp only [Pi.mul_apply, Pi.neg_apply, neg_mul]) hx hb
      have hne : -B x = -LB x := by
        convert! hi using 1 <;>
          simp only [B, Pi.neg_apply, Pi.mul_apply, intervalIntegral.integral_neg, hLBb, zero_sub]
      exact (neg_inj.mp hne).symm
    rw [hsplit hx]
    change y x = (V x * A x + U x * B x) / d
    apply (eq_div_iff hd0).mpr
    rw [← heA, ← heB, ← hW x hx]
    dsimp [LA, LB]
    ring

end D13Unified.Ch10.GreenKernel
