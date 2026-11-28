import MathGenome.Internal.LieTheoryDeepening.LieNotes.Virasoro.VirasoroCocycle
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.WittCohomology

/-! Central Lie 2-cocycles of the Witt algebra and their cohomology classes. -/

noncomputable section

open LieModule.Cohomology

namespace LieNotes.Virasoro

open WittCohomologySpec (coboundary H2)
open scoped WittCohomologySpec

local notation "W" => Witt.W
local notation "L" => Witt.L
local notation "κ" => VirasoroSpec.centralCoefficient

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
  [LieRingModule W Z] [LieModule ℂ W Z] [LieModule.IsTrivial W Z]

local notation "Cocycle" => (twoCocycle ℂ W Z : Type _)

omit [LieModule.IsTrivial W Z] in
/-- Two cocycles agreeing on all pairs of Witt modes agree everywhere. -/
private theorem cocycle_ext {c d : Cocycle}
    (h : ∀ m n : ℤ, c.val (L m) (L n) = d.val (L m) (L n)) : c = d := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext_basis Witt.basis Witt.basis
  intro m n
  change c.val (Witt.basis m) (Witt.basis n) = d.val (Witt.basis m) (Witt.basis n)
  simpa only [Witt.basis_apply] using h m n

private theorem lie_opposite (m : ℤ) :
    ⁅L m, L (-m)⁆ = (2 * (m : ℂ)) • L 0 := by
  rw [Witt.lie_L, add_neg_cancel, Int.cast_neg, sub_neg_eq_add, two_mul]

private theorem coboundary_opposite (φ : W →ₗ[ℂ] Z) (m : ℤ) :
    (coboundary Z φ).val (L m) (L (-m)) = -((2 * (m : ℂ)) • φ (L 0)) := by
  change d₁₂ ℂ W Z φ (L m) (L (-m)) = _
  rw [coboundary_apply_trivial, lie_opposite, map_smul]

/-- One cochain adjusts both the pairs `(L₀, Lⱼ)` and the pair `(L₁, L₋₁)`. -/
private def normalizingCochain (c : Cocycle) : W →ₗ[ℂ] Z :=
  Witt.basis.constr ℂ fun j : ℤ =>
    if j = 0 then (2 : ℂ)⁻¹ • c.val (L 1) (L (-1))
    else -((j : ℂ)⁻¹) • c.val (L 0) (L j)

omit [LieModule.IsTrivial W Z] in
private theorem normalizingCochain_apply (c : Cocycle) (j : ℤ) :
    normalizingCochain c (L j) =
      if j = 0 then (2 : ℂ)⁻¹ • c.val (L 1) (L (-1))
      else -((j : ℂ)⁻¹) • c.val (L 0) (L j) := by
  rw [← Witt.basis_apply j, normalizingCochain, Module.Basis.constr_basis,
    Witt.basis_apply]

private def normalize (c : Cocycle) : Cocycle :=
  c + coboundary Z (normalizingCochain c)

private theorem normalize_zero (c : Cocycle) (j : ℤ) :
    (normalize c).val (L 0) (L j) = 0 := by
  by_cases hj : j = 0
  · subst j
    exact twoCochain_alt (normalize c).val (L 0)
  change c.val (L 0) (L j) + d₁₂ ℂ W Z (normalizingCochain c) (L 0) (L j) = 0
  rw [coboundary_apply_trivial, Witt.lie_L, Int.cast_zero, zero_sub, zero_add,
    map_smul, normalizingCochain_apply, ite_eq_right hj, smul_smul, neg_mul_neg,
    mul_inv_cancel₀ (Int.cast_ne_zero.mpr hj), one_smul, add_neg_cancel]

private theorem normalize_one (c : Cocycle) :
    (normalize c).val (L 1) (L (-1)) = 0 := by
  change c.val (L 1) (L (-1)) +
    (coboundary Z (normalizingCochain c)).val (L 1) (L (-1)) = 0
  rw [coboundary_opposite, Int.cast_one, mul_one, normalizingCochain_apply, ite_eq_left rfl,
    smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul, add_neg_cancel]

private theorem cocycle_identity (c : Cocycle) (x y u : W) :
    c.val x ⁅y, u⁆ = c.val ⁅x, y⁆ u + c.val y ⁅x, u⁆ :=
  (mem_twoCocycle_iff_of_trivial ℂ W Z c.val).mp c.property x y u

private theorem off_diagonal (c : Cocycle) (h₀ : ∀ j : ℤ, c.val (L 0) (L j) = 0)
    (m n : ℤ) (hmn : m + n ≠ 0) : c.val (L m) (L n) = 0 := by
  have h := cocycle_identity c (L 0) (L m) (L n)
  simp only [Witt.lie_L, Int.cast_zero, zero_sub, zero_add, map_smul,
    LinearMap.smul_apply, h₀, smul_zero] at h
  rw [← add_smul, ← neg_add, ← Int.cast_add, neg_smul, zero_eq_neg] at h
  exact (smul_eq_zero.mp h).resolve_left (Int.cast_ne_zero.mpr hmn)

private theorem diagonal_recurrence (c : Cocycle) (h₁ : c.val (L 1) (L (-1)) = 0)
    (m : ℤ) :
    ((m : ℂ) - 1) • c.val (L (m + 1)) (L (-(m + 1))) =
      ((m : ℂ) + 2) • c.val (L m) (L (-m)) := by
  have h := cocycle_identity c (L m) (L 1) (L (-(m + 1)))
  have hleft : 1 + -(m + 1) = -m := by omega
  have hright : m + -(m + 1) = -1 := by omega
  simp only [Witt.lie_L, map_smul, LinearMap.smul_apply, hleft, hright, Int.cast_one,
    h₁, smul_zero, add_zero] at h
  have hscalar : (1 : ℂ) - (↑(-(m + 1)) : ℂ) = (m : ℂ) + 2 := by
    push_cast
    ring
  rw [hscalar] at h
  exact h.symm

private theorem eq_zero_of_normalized (c : Cocycle)
    (h₀ : ∀ j : ℤ, c.val (L 0) (L j) = 0) (h₁ : c.val (L 1) (L (-1)) = 0)
    (h₂ : c.val (L 2) (L (-2)) = 0) : c = 0 := by
  have hnat (k : ℕ) : c.val (L ((k : ℤ) + 2)) (L (-((k : ℤ) + 2))) = 0 := by
    induction k with
    | zero => simpa using h₂
    | succ k ih =>
      have h := diagonal_recurrence c h₁ ((k : ℤ) + 2)
      rw [ih, smul_zero] at h
      have hn : ((↑((k : ℤ) + 2) : ℂ) - 1) ≠ 0 := by
        intro hz
        have hc : (↑((k : ℤ) + 2) : ℂ) = ((1 : ℤ) : ℂ) := by
          simpa only [Int.cast_one] using sub_eq_zero.mp hz
        have he := Int.cast_injective (α := ℂ) hc
        omega
      have hs := (smul_eq_zero.mp h).resolve_left hn
      have hk : (k : ℤ) + 2 + 1 = ((k + 1 : ℕ) : ℤ) + 2 := by omega
      rwa [hk] at hs
  have hnonneg (m : ℤ) (hm : 0 ≤ m) : c.val (L m) (L (-m)) = 0 := by
    by_cases hm₀ : m = 0
    · subst m
      exact h₀ _
    by_cases hm₁ : m = 1
    · subst m
      exact h₁
    have hk : m = ((m - 2).toNat : ℤ) + 2 := by omega
    simpa only [← hk] using hnat (m - 2).toNat
  apply cocycle_ext
  intro m n
  change c.val (L m) (L n) = 0
  by_cases hmn : m + n = 0
  · have hn : n = -m := by omega
    subst n
    by_cases hm : 0 ≤ m
    · exact hnonneg m hm
    have h := hnonneg (-m) (by omega)
    rw [neg_neg, ← twoCochain_skew c.val (L m) (L (-m)), neg_eq_zero] at h
    exact h
  · exact off_diagonal c h₀ m n hmn

private theorem omega_zero (z : Z) (j : ℤ) : (omega z).val (L 0) (L j) = 0 := by
  simp [VirasoroSpec.centralCoefficient]

private theorem omega_one (z : Z) : (omega z).val (L 1) (L (-1)) = 0 := by
  norm_num [VirasoroSpec.centralCoefficient]

private theorem omega_two (z : Z) : (omega z).val (L 2) (L (-2)) = (2 : ℂ)⁻¹ • z := by
  rw [omega_modes, show κ 2 (-2) = (2 : ℂ)⁻¹ by norm_num [VirasoroSpec.centralCoefficient]]

private theorem normalize_eq_omega (c : Cocycle) :
    normalize c = omega ((2 : ℂ) • (normalize c).val (L 2) (L (-2))) := by
  let z := (2 : ℂ) • (normalize c).val (L 2) (L (-2))
  change normalize c = omega z
  apply sub_eq_zero.mp
  apply eq_zero_of_normalized
  · intro j
    change (normalize c).val (L 0) (L j) - (omega z).val (L 0) (L j) = 0
    rw [normalize_zero, omega_zero, sub_zero]
  · change (normalize c).val (L 1) (L (-1)) - (omega z).val (L 1) (L (-1)) = 0
    rw [normalize_one, omega_one, sub_zero]
  · change (normalize c).val (L 2) (L (-2)) - (omega z).val (L 2) (L (-2)) = 0
    rw [omega_two]
    dsimp only [z]
    rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul, sub_self]

private theorem omega_parameter_eq {z z' : Z} {φ : W →ₗ[ℂ] Z}
    (h : omega z - omega z' = coboundary Z φ) : z = z' := by
  have h₁ := congrArg (fun c : Cocycle => c.val (L 1) (L (-1))) h
  change (omega z).val (L 1) (L (-1)) - (omega z').val (L 1) (L (-1)) =
    (coboundary Z φ).val (L 1) (L (-1)) at h₁
  rw [omega_one, omega_one, sub_self, coboundary_opposite, Int.cast_one, mul_one,
    zero_eq_neg] at h₁
  have hφ : φ (L 0) = 0 :=
    (smul_eq_zero.mp h₁).resolve_left (by norm_num)
  have h₂ := congrArg (fun c : Cocycle => c.val (L 2) (L (-2))) h
  change (omega z).val (L 2) (L (-2)) - (omega z').val (L 2) (L (-2)) =
    (coboundary Z φ).val (L 2) (L (-2)) at h₂
  rw [omega_two, omega_two, coboundary_opposite, hφ, smul_zero, neg_zero] at h₂
  exact smul_right_injective Z (by norm_num : (2 : ℂ)⁻¹ ≠ 0) (sub_eq_zero.mp h₂)

/-- Classification in the cocycle submodule, with Mathlib's coboundary sign. -/
theorem existsUnique_omega_add_coboundary (c : Cocycle) :
    ∃! z : Z, ∃ φ : W →ₗ[ℂ] Z, c + coboundary Z φ = omega z := by
  refine ⟨_, ⟨normalizingCochain c, normalize_eq_omega c⟩, ?_⟩
  rintro z ⟨φ, hφ⟩
  apply omega_parameter_eq (φ := φ - normalizingCochain c)
  rw [← hφ, ← normalize_eq_omega c, normalize, map_sub]
  abel

theorem witt_cocycle_classification : WittCohomologySpec.Classification := by
  intro Z _ _ _ _ _ c
  refine (existsUnique_congr fun z => ?_).mp (existsUnique_omega_add_coboundary c)
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, fun x y => congrArg (fun a : twoCocycle ℂ W Z => a.val x y) hφ⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, cocycle_ext fun m n => hφ (L m) (L n)⟩

/-- The linear family of Virasoro cocycles with trivial coefficients. -/
private def omegaLinear : Z →ₗ[ℂ] Cocycle where
  toFun := omega
  map_add' z z' := by
    apply cocycle_ext
    intro m n
    change (omega (z + z')).val (L m) (L n) =
      (omega z).val (L m) (L n) + (omega z').val (L m) (L n)
    simp only [omega_modes, smul_add]
  map_smul' a z := by
    apply cocycle_ext
    intro m n
    change (omega (a • z)).val (L m) (L n) = a • (omega z).val (L m) (L n)
    simp only [omega_modes, smul_comm (κ m n) a z]

private def omegaClass : Z →ₗ[ℂ] H2 Z :=
  (LinearMap.range (coboundary Z)).mkQ.comp omegaLinear

private theorem omegaClass_bijective : Function.Bijective (omegaClass (Z := Z)) := by
  constructor
  · intro z z' h
    change (Submodule.Quotient.mk (omega z) : H2 Z) = Submodule.Quotient.mk (omega z') at h
    obtain ⟨φ, hφ⟩ := (Submodule.Quotient.eq _).mp h
    exact omega_parameter_eq hφ.symm
  · intro q
    obtain ⟨c, rfl⟩ := (LinearMap.range (coboundary Z)).mkQ_surjective q
    obtain ⟨z, ⟨φ, hφ⟩, _⟩ := existsUnique_omega_add_coboundary c
    refine ⟨z, (Submodule.Quotient.eq _).mpr ?_⟩
    refine ⟨φ, ?_⟩
    change coboundary Z φ = omega z - c
    rw [← hφ]
    abel

/-- The canonical isomorphism sending a central coefficient to its cohomology class. -/
def wittCohomologyEquiv : Z ≃ₗ[ℂ] H2 Z :=
  LinearEquiv.ofBijective omegaClass omegaClass_bijective

theorem witt_cohomology_equivalence : WittCohomologySpec.CohomologyEquivalence := by
  intro Z _ _ _ _ _
  refine ⟨wittCohomologyEquiv, fun z c hc => ?_⟩
  have h : omega z = c := Subtype.ext (Subtype.ext hc.symm)
  change Submodule.Quotient.mk (omega z) = Submodule.Quotient.mk c
  rw [h]

theorem witt_scalar_cohomology_dimension : WittCohomologySpec.ScalarCohomologyDimension := by
  change Module.finrank ℂ (H2 (TrivialLieModule ℂ W ℂ)) = 1
  rw [← (wittCohomologyEquiv (Z := TrivialLieModule ℂ W ℂ)).finrank_eq]
  exact CommSemiring.finrank_self ℂ

end LieNotes.Virasoro
