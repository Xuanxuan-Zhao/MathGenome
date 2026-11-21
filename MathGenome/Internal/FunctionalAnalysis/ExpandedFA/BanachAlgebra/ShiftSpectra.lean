import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.ShiftSpectra
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Conventions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.NeumannResolvent
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The unilateral forward and backward shifts on every finite scalar ℓᵖ. -/
noncomputable section
open Filter
open scoped ENNReal Topology
namespace ExpandedFA.BanachAlgebra.ShiftSpectra

abbrev forwardShift : Spec.ShiftType := Spec.ForwardValue
abbrev backwardShift : Spec.ShiftType := Spec.BackwardValue

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)

@[simp] theorem forward_zero (x : Space p) : forwardShift p hp x 0 = 0 := rfl
@[simp] theorem forward_succ (x : Space p) (n : ℕ) :
    forwardShift p hp x (n + 1) = x n := rfl
@[simp] theorem backward_apply (x : Space p) (n : ℕ) :
    backwardShift p hp x n = x (n + 1) := rfl

theorem shift_coordinates : Spec.Coordinates := by
  intro p _ hp x
  exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem forward_norm (x : Space p) : ‖forwardShift p hp x‖ = ‖x‖ :=
  (forwardIsometry p hp).norm_map x

theorem backward_norm_le (x : Space p) : ‖backwardShift p hp x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (exponent_pos p hp) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (exponent_pos p hp)]
  change (∑' n, ‖x (n + 1)‖ ^ p.toReal) ≤ _
  rw [((lp.memℓp x).summable (exponent_pos p hp)).tsum_eq_zero_add]
  exact le_add_of_nonneg_left (by positivity)

@[simp] theorem backward_forward (x : Space p) :
    backwardShift p hp (forwardShift p hp x) = x := by
  apply lp.ext; rfl

theorem forward_norm_one : ‖forwardShift p hp‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x; simpa using (forward_norm p hp x).le
  · have h := (forwardShift p hp).le_opNorm (lp.single p 0 (1 : ℂ))
    rw [forward_norm] at h
    simpa [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))] using h

theorem backward_norm_one : ‖backwardShift p hp‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x; simpa using backward_norm_le p hp x
  · have h := (backwardShift p hp).le_opNorm
      (forwardShift p hp (lp.single p 0 (1 : ℂ)))
    rw [backward_forward, forward_norm] at h
    simpa [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))] using h

theorem shift_norms : Spec.Norms := fun p _ hp =>
  ⟨forward_norm_one p hp, backward_norm_one p hp⟩

theorem forward_eigenvector_zero (z : ℂ) (x : Space p)
    (h : forwardShift p hp x = z • x) : x = 0 := by
  have hc (n : ℕ) := congrArg (fun y : Space p => y n) h
  have hx : ∀ n, x n = 0 := by
    by_cases hz : z = 0
    · intro n
      have hh := hc (n + 1)
      change x n = z * x (n + 1) at hh
      simpa [hz] using hh
    · intro n
      induction n with
      | zero =>
        have hh := hc 0
        change 0 = z * x 0 at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left hz
      | succ n ih =>
        have hh := hc (n + 1)
        change x n = z * x (n + 1) at hh
        rw [ih] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left hz
  exact lp.ext (funext hx)

theorem forward_point_spectrum : Spec.ForwardPointSpectrum := by
  intro p _ hp
  ext z
  change (∃ x : Space p, x ≠ 0 ∧ forwardShift p hp x = z • x) ↔ False
  exact ⟨fun ⟨x, hx, he⟩ => hx (forward_eigenvector_zero p hp z x he), False.elim⟩

/-- The equation at e₀ is impossible throughout the closed disk. -/
theorem forward_not_surjective (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ¬ Function.Surjective (fun x : Space p => z • x - forwardShift p hp x) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (lp.single p 0 (1 : ℂ))
  have h0 : z * x 0 = 1 := by
    have h := congrArg (fun y : Space p => y 0) hx
    change z * x 0 - 0 = 1 at h
    simpa using h
  have hs (n : ℕ) : z * x (n + 1) = x n := by
    have h := congrArg (fun y : Space p => y (n + 1)) hx
    have hn : n + 1 ≠ (0 : ℕ) := Nat.succ_ne_zero n
    change z * x (n + 1) - x n = _ at h
    rw [lp.single_apply_ne (E := fun _ : ℕ => ℂ) p 0 1 hn] at h
    exact sub_eq_zero.mp h
  have hle (n : ℕ) : ‖x 0‖ ≤ ‖x n‖ := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      apply ih.trans
      rw [← hs n, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hz
  have hlim := (ExpandedFA.P1.C01SequenceSpaces.lp_coordinates_tendsto_zero ℂ p hp x).norm
  have hx0 : ‖x 0‖ ≤ 0 := ge_of_tendsto (by simpa using hlim) (Eventually.of_forall hle)
  have : x 0 = 0 := norm_eq_zero.mp (le_antisymm hx0 (norm_nonneg _))
  simp [this] at h0

theorem forward_spectrum : Spec.ForwardSpectrum := by
  intro p _ hp
  ext z
  change z ∈ spectrum ℂ (forwardShift p hp) ↔ ‖z‖ ≤ 1
  constructor
  · intro hz
    simpa [forward_norm_one p hp] using spectrum.norm_le_norm_of_mem hz
  · intro hz hres
    obtain ⟨U, _, hright⟩ :=
      (ExpandedFA.BanachAlgebra.operator_resolvent_iff_bounded_inverse
        ℂ (Space p) (forwardShift p hp) z).mp hres
    exact forward_not_surjective p hp z hz (fun y => ⟨U y, hright y⟩)

include hp in
/-- Geometric sequences belong to every finite ℓᵖ in the open disk. -/
theorem geometric_mem (z : ℂ) (hz : ‖z‖ < 1) : Memℓp (fun n : ℕ => z ^ n) p := by
  apply memℓp_gen
  have hs := summable_geometric_of_lt_one
    (Real.rpow_nonneg (norm_nonneg z) p.toReal)
    (Real.rpow_lt_one (norm_nonneg z) hz (exponent_pos p hp))
  simpa only [norm_pow, Real.rpow_pow_comm (norm_nonneg z)] using hs

def geometricVector (z : ℂ) (hz : ‖z‖ < 1) : Space p :=
  ⟨fun n => z ^ n, geometric_mem p hp z hz⟩

@[simp] theorem geometric_apply (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) :
    geometricVector p hp z hz n = z ^ n := rfl

theorem geometric_nonzero (z : ℂ) (hz : ‖z‖ < 1) : geometricVector p hp z hz ≠ 0 := by
  intro h
  have := congrArg (fun y : Space p => y 0) h
  simp at this

theorem backward_geometric (z : ℂ) (hz : ‖z‖ < 1) :
    backwardShift p hp (geometricVector p hp z hz) = z • geometricVector p hp z hz := by
  apply lp.ext; funext n
  change z ^ (n + 1) = z * z ^ n
  exact pow_succ' z n

theorem backward_eigenvalue_lt_one (z : ℂ) (x : Space p) (hx : x ≠ 0)
    (he : backwardShift p hp x = z • x) : ‖z‖ < 1 := by
  have hs (n : ℕ) : x (n + 1) = z * x n :=
    congrArg (fun y : Space p => y n) he
  have hc (n : ℕ) : x n = z ^ n * x 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [hs, ih, pow_succ']; ring
  have hx0 : x 0 ≠ 0 := by
    intro h0
    apply hx; apply lp.ext; funext n
    change x n = 0
    rw [hc n, h0, mul_zero]
  by_contra hz
  have hz' : 1 ≤ ‖z‖ := le_of_not_gt hz
  have hle (n : ℕ) : ‖x 0‖ ≤ ‖x n‖ := by
    rw [hc n, norm_mul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hz')
  have hlim := (ExpandedFA.P1.C01SequenceSpaces.lp_coordinates_tendsto_zero ℂ p hp x).norm
  have h0 : ‖x 0‖ ≤ 0 := ge_of_tendsto (by simpa using hlim) (Eventually.of_forall hle)
  exact hx0 (norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _)))

theorem backward_point_spectrum : Spec.BackwardPointSpectrum := by
  intro p _ hp
  ext z
  change (∃ x : Space p, x ≠ 0 ∧ backwardShift p hp x = z • x) ↔ ‖z‖ < 1
  constructor
  · rintro ⟨x, hx, he⟩
    exact backward_eigenvalue_lt_one p hp z x hx he
  · intro hz
    exact ⟨geometricVector p hp z hz, geometric_nonzero p hp z hz,
      backward_geometric p hp z hz⟩

/-- The finite initial segment of a unimodular geometric sequence. -/
def truncatedVector (z : ℂ) (N : ℕ) : Space p :=
  ∑ n ∈ Finset.range N, lp.single p n ((z⁻¹) ^ n)

theorem truncated_apply (z : ℂ) (N n : ℕ) :
    truncatedVector p z N n = if n < N then (z⁻¹) ^ n else 0 := by
  simp only [truncatedVector, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  rw [Finset.sum_pi_single]
  simp

include hp in
theorem truncated_norm_power (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) :
    ‖truncatedVector p z N‖ ^ p.toReal = N := by
  rw [truncatedVector, lp.norm_sum_single (exponent_pos p hp)]
  simp [norm_pow, norm_inv, hz]

include hp in
theorem exists_truncated_norm_gt (z : ℂ) (hz : ‖z‖ = 1) (C : ℝ) :
    ∃ N : ℕ, C < ‖truncatedVector p z (N + 1)‖ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((max C 0) ^ p.toReal)
  refine ⟨N, ?_⟩
  by_contra h
  have hC : ‖truncatedVector p z (N + 1)‖ ≤ max C 0 :=
    (le_of_not_gt h).trans (le_max_left _ _)
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hC (exponent_pos p hp).le
  rw [truncated_norm_power p hp z hz] at hpow
  push_cast at hpow
  linarith

/-- The residual consists of precisely the two endpoint coordinates. -/
theorem truncated_residual (z : ℂ) (hz : z ≠ 0) (N : ℕ) :
    forwardShift p hp (truncatedVector p z (N + 1)) - z • truncatedVector p z (N + 1) =
      lp.single p (N + 1) ((z⁻¹) ^ N) - lp.single p 0 z := by
  apply lp.ext; funext n
  change forwardShift p hp (truncatedVector p z (N + 1)) n -
    z * truncatedVector p z (N + 1) n = _
  cases n with
  | zero =>
    simp [truncated_apply]
  | succ n =>
    rw [forward_succ, truncated_apply, truncated_apply]
    change (if n < N + 1 then (z⁻¹) ^ n else 0) -
      z * (if n + 1 < N + 1 then (z⁻¹) ^ (n + 1) else 0) =
        lp.single (E := fun _ : ℕ => ℂ) p (N + 1) ((z⁻¹) ^ N) (n + 1) - lp.single (E := fun _ : ℕ => ℂ) p 0 z (n + 1)
    rw [lp.single_apply_ne (E := fun _ : ℕ => ℂ) p 0 z (Nat.succ_ne_zero n)]
    by_cases hn : n < N
    · have hne : n + 1 ≠ N + 1 := by omega
      rw [lp.single_apply_ne (E := fun _ : ℕ => ℂ) p (N + 1) _ hne]
      simp only [show n < N + 1 by omega, show n + 1 < N + 1 by omega, ↓reduceIte,
        sub_zero, pow_succ]
      field_simp
      simp
    · by_cases he : n = N
      · subst n
        simp
      · have hn' : ¬ n < N + 1 := by omega
        have hn'' : ¬ n + 1 < N + 1 := by omega
        have hne : n + 1 ≠ N + 1 := by omega
        rw [lp.single_apply_ne (E := fun _ : ℕ => ℂ) p (N + 1) _ hne]
        simp [hn', hn'']

theorem truncated_residual_norm_le (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) :
    ‖forwardShift p hp (truncatedVector p z (N + 1)) -
      z • truncatedVector p z (N + 1)‖ ≤ 2 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [truncated_residual p hp z hz0]
  apply (norm_sub_le _ _).trans
  norm_num [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)), norm_pow, norm_inv, hz]

/-- Normalization of the finite initial segments gives actual unit vectors. -/
theorem forward_endpoint_vectors (z : ℂ) (hz : ‖z‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Space p, ‖x‖ = 1 ∧ ‖forwardShift p hp x - z • x‖ < ε := by
  obtain ⟨N, hN⟩ := exists_truncated_norm_gt p hp z hz (2 / ε)
  let v := truncatedVector p z (N + 1)
  have hv : 0 < ‖v‖ := (div_pos (by norm_num) hε).trans hN
  let c : ℂ := (‖v‖ : ℂ)⁻¹
  have hc : ‖c‖ = ‖v‖⁻¹ := by simp [c, Complex.norm_real]
  refine ⟨c • v, ?_, ?_⟩
  · rw [norm_smul, hc, inv_mul_cancel₀ hv.ne']
  · rw [map_smul, smul_comm z c, ← smul_sub, norm_smul, hc]
    apply (mul_le_mul_of_nonneg_left (truncated_residual_norm_le p hp z hz N)
      (inv_nonneg.mpr hv.le)).trans_lt
    rw [inv_mul_eq_div, div_lt_iff₀ hv]
    have : 2 < ε * ‖v‖ := by
      have hh := (div_lt_iff₀ hε).mp hN
      nlinarith
    exact this

/-- The isometry estimate excludes every scalar off the unit circle. -/
theorem forward_approximate_spectrum : Spec.ForwardApproximateSpectrum := by
  intro p _ hp
  ext z
  change (∀ ε : ℝ, 0 < ε → ∃ x : Space p,
    ‖x‖ = 1 ∧ ‖forwardShift p hp x - z • x‖ < ε) ↔ ‖z‖ = 1
  constructor
  · intro h
    by_contra hz
    have he : 0 < |1 - ‖z‖| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hz))
    obtain ⟨x, hx, hres⟩ := h _ he
    have hh := abs_norm_sub_norm_le (forwardShift p hp x) (z • x)
    rw [forward_norm p hp, norm_smul, hx, mul_one] at hh
    linarith
  · intro hz
    exact forward_endpoint_vectors p hp z hz

/-- Apply the contractive backward shift to a forward residual at z⁻¹. -/
theorem backward_endpoint_vectors : Spec.BackwardEndpoints := by
  intro p _ hp z hz ε hε
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  obtain ⟨x, hx, hres⟩ := forward_endpoint_vectors p hp z⁻¹ (by simp [norm_inv, hz]) ε hε
  refine ⟨x, hx, ?_⟩
  have heq : backwardShift p hp (forwardShift p hp x - z⁻¹ • x) =
      (-z⁻¹) • (backwardShift p hp x - z • x) := by
    rw [map_sub, backward_forward, map_smul, smul_sub, smul_smul]
    simp [hz0, neg_smul, sub_eq_add_neg, add_comm]
  have hh := backward_norm_le p hp (forwardShift p hp x - z⁻¹ • x)
  rw [heq, norm_smul] at hh
  simpa only [norm_neg, norm_inv, hz, inv_one, one_mul] using hh.trans_lt hres

/-- Eigenvalues fill the open disk; closedness supplies its boundary. -/
theorem backward_spectrum : Spec.BackwardSpectrum := by
  intro p _ hp
  have hinterior : Metric.ball (0 : ℂ) 1 ⊆ spectrum ℂ (backwardShift p hp) := by
    intro z hz hres
    have hz' : ‖z‖ < 1 := by simpa using hz
    let x := geometricVector p hp z hz'
    have hx : x ≠ 0 := geometric_nonzero p hp z hz'
    have he : backwardShift p hp x = z • x := backward_geometric p hp z hz'
    obtain ⟨U, hleft, _⟩ :=
      (ExpandedFA.BanachAlgebra.operator_resolvent_iff_bounded_inverse
        ℂ (Space p) (backwardShift p hp) z).mp hres
    have hh := hleft x
    rw [he, sub_self, map_zero] at hh
    exact hx hh.symm
  apply Set.Subset.antisymm
  · intro z hz
    simpa [backward_norm_one p hp] using spectrum.norm_le_norm_of_mem hz
  · intro z hz
    have hz' : z ∈ closure (Metric.ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      simpa using hz
    exact closure_minimal hinterior (spectrum.isClosed _) hz'

end ExpandedFA.BanachAlgebra.ShiftSpectra
