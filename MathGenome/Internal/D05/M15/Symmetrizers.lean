import MathGenome.Internal.D05.M15.PermutationActions
import MathGenome.Internal.D05.Foundations.PermutationSign
import MathGenome.Internal.Specs.D05.M15.Symmetrizers
import Mathlib.Tactic.Module

/-! Averaging the ordinary and sign-twisted permutation representations.
All tensor powers here are the upstream algebraic finite tensor products. -/

noncomputable section
namespace D05.M15.Symmetrizers

open D05.Foundations D05.M15.PermutationActions
open Specs.D05.M15.Symmetrizers

noncomputable abbrev symmetricProjector :=
  @Specs.D05.M15.Symmetrizers.symmetricProjector
noncomputable abbrev alternatingProjector :=
  @Specs.D05.M15.Symmetrizers.alternatingProjector
noncomputable abbrev symmetricPart := @Specs.D05.M15.Symmetrizers.symmetricPart
noncomputable abbrev alternatingPart := @Specs.D05.M15.Symmetrizers.alternatingPart

section Averaging
variable {K E G : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Group G] [Fintype G]

/-- The normalized finite-group average. -/
def groupAverage (ρ : G → E →ₗ[K] E) : E →ₗ[K] E :=
  (Fintype.card G : K)⁻¹ • ∑ g : G, ρ g

/-- Left translation permutes the summands; no characteristic condition is
needed for this identity alone. -/
theorem groupAverage_invariant (ρ : G → E →ₗ[K] E)
    (hmul : ∀ g h, (ρ g).comp (ρ h) = ρ (g * h)) (g : G) (x : E) :
    ρ g (groupAverage ρ x) = groupAverage ρ x := by
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  calc
    ∑ h : G, ρ g (ρ h x) = ∑ h : G, ρ (g * h) x := by
      apply Finset.sum_congr rfl
      intro h _
      exact congrArg (fun f : E →ₗ[K] E => f x) (hmul g h)
    _ = ∑ h : G, ρ h x :=
      Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ (fun _ => rfl)

omit [Group G] in
/-- Normalization makes averaging act as identity on fixed vectors. -/
theorem groupAverage_fixed (ρ : G → E →ₗ[K] E)
    (hc : (Fintype.card G : K) ≠ 0) (x : E) (hx : ∀ g, ρ g x = x) :
    groupAverage ρ x = x := by
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, hx,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hc, one_smul]
end Averaging

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The paper's inversion-parity sign is involutive after mapping to K. -/
theorem scalarSign_square (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    (permutationSign σ : K) * (permutationSign σ : K) = 1 := by
  rw [D05.Foundations.PermutationSign.signIdentification]
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

def signedOperator (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    TensorPower K V p →ₗ[K] TensorPower K V p :=
  (permutationSign σ : K) • permutationOperator p σ

theorem signedOperator_mul (p : ℕ) (σ τ : Equiv.Perm (Fin p)) :
    (signedOperator (K := K) (V := V) p σ).comp (signedOperator p τ) =
      signedOperator p (σ * τ) := by
  apply LinearMap.ext
  intro x
  simp only [signedOperator, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
    smul_smul]
  rw [← LinearMap.comp_apply, operator_mul,
    D05.Foundations.PermutationSign.signMultiplicative, Int.cast_mul]
  rw [mul_comm]

private theorem perm_card (p : ℕ) : Fintype.card (Equiv.Perm (Fin p)) = p.factorial := by
  simp [Fintype.card_perm]

private theorem average_symmetric (p : ℕ) (hp : (p.factorial : K) ≠ 0) :
    groupAverage (permutationOperator (K := K) (V := V) p) = Specs.D05.M15.Symmetrizers.symmetricProjector p hp := by
  simp only [groupAverage, perm_card,
    Specs.D05.M15.Symmetrizers.symmetricProjector]

private theorem average_alternating (p : ℕ) (hp : (p.factorial : K) ≠ 0) :
    groupAverage (signedOperator (K := K) (V := V) p) = Specs.D05.M15.Symmetrizers.alternatingProjector p hp := by
  simp only [groupAverage, perm_card, signedOperator,
    Specs.D05.M15.Symmetrizers.alternatingProjector]

private theorem signed_fixed_iff (p : ℕ) (t : TensorPower K V p) :
    (∀ σ, signedOperator p σ t = t) ↔ IsSignInvariant p t := by
  constructor
  · intro h σ
    have hh := congrArg (fun x => (permutationSign σ : K) • x) (h σ)
    simpa only [signedOperator, LinearMap.smul_apply, smul_smul,
      scalarSign_square, one_smul] using hh
  · intro h σ
    simp only [signedOperator, LinearMap.smul_apply, h σ, smul_smul,
      scalarSign_square, one_smul]

theorem symmetrizer_invariant : Specs.D05.M15.Symmetrizers.symmetrizer_invariant := by
  intro K V _ _ _ p hp τ
  apply LinearMap.ext
  intro t
  rw [LinearMap.comp_apply, ← average_symmetric p hp]
  exact groupAverage_invariant _ (operator_mul p) τ t

theorem antisymmetrizer_covariant : Specs.D05.M15.Symmetrizers.antisymmetrizer_covariant := by
  intro K V _ _ _ p hp τ
  have h := groupAverage_invariant (signedOperator (K := K) (V := V) p)
    (signedOperator_mul p) τ
  apply LinearMap.ext
  intro t
  have hh := congrArg (fun x => (permutationSign τ : K) • x) (h t)
  rw [average_alternating p hp] at hh
  simpa only [signedOperator, LinearMap.smul_apply, LinearMap.comp_apply,
    smul_smul, scalarSign_square, one_smul] using hh

theorem symmetrizer_fixed : Specs.D05.M15.Symmetrizers.symmetrizer_fixed := by
  intro K V _ _ _ p hp t ht
  rw [← average_symmetric p hp]
  exact groupAverage_fixed _ (by simpa only [perm_card] using hp) t ht

theorem antisymmetrizer_fixed : Specs.D05.M15.Symmetrizers.antisymmetrizer_fixed := by
  intro K V _ _ _ p hp t ht
  rw [← average_alternating p hp]
  exact groupAverage_fixed _ (by simpa only [perm_card] using hp) t
    ((signed_fixed_iff p t).mpr ht)

theorem projectors_idempotent : Specs.D05.M15.Symmetrizers.projectors_idempotent := by
  intro K V _ _ _ p hp
  constructor
  · apply LinearMap.ext
    intro t
    apply symmetrizer_fixed p hp
    intro σ
    exact congrArg (fun f : TensorPower K V p →ₗ[K] TensorPower K V p => f t)
      (symmetrizer_invariant p hp σ)
  · apply LinearMap.ext
    intro t
    apply antisymmetrizer_fixed p hp
    intro σ
    exact congrArg (fun f : TensorPower K V p →ₗ[K] TensorPower K V p => f t)
      (antisymmetrizer_covariant p hp σ)

theorem projector_images : Specs.D05.M15.Symmetrizers.projector_images := by
  intro K V _ _ _ p hp t
  constructor
  · constructor
    · rintro ⟨x, rfl⟩ σ
      exact congrArg (fun f : TensorPower K V p →ₗ[K] TensorPower K V p => f x)
        (symmetrizer_invariant p hp σ)
    · intro ht
      exact ⟨t, symmetrizer_fixed p hp t ht⟩
  · constructor
    · rintro ⟨x, rfl⟩ σ
      exact congrArg (fun f : TensorPower K V p →ₗ[K] TensorPower K V p => f x)
        (antisymmetrizer_covariant p hp σ)
    · intro ht
      exact ⟨t, antisymmetrizer_fixed p hp t ht⟩

theorem low_degrees : Specs.D05.M15.Symmetrizers.low_degrees := by
  intro K V _ _ _ p h hp
  have hsub : Subsingleton (Fin p) := by
    apply Fin.subsingleton_iff_le_one.mpr h
  have hσ (σ : Equiv.Perm (Fin p)) : σ = 1 := Subsingleton.elim _ _
  have hs (σ : Equiv.Perm (Fin p)) : permutationSign σ = 1 := by
    rw [hσ σ, D05.Foundations.PermutationSign.signIdentification]
    simp
  constructor
  · apply LinearMap.ext
    intro t
    apply symmetrizer_fixed p hp
    intro σ
    change permutationOperator p σ t = t
    rw [hσ σ, operator_one]
    rfl
  · apply LinearMap.ext
    intro t
    apply antisymmetrizer_fixed p hp
    intro σ
    change permutationOperator p σ t = (permutationSign σ : K) • t
    rw [hσ σ, operator_one, hs 1]
    simp

theorem vanishing_factorial : Specs.D05.M15.Symmetrizers.vanishing_factorial := by
  intro K _ p hp
  rw [hp]
  exact not_isUnit_zero

/-- Alternation implies the swap sign rule without dividing by two. -/
theorem alternating_skew {W : Type*} [AddCommGroup W] [Module K W]
    (b : V →ₗ[K] V →ₗ[K] W) (hb : IsAlternating b) (u v : V) :
    b u v = -b v u := by
  apply eq_neg_iff_add_eq_zero.mpr
  have h := hb (u + v)
  simpa only [map_add, LinearMap.add_apply, hb u, hb v, zero_add, add_zero, add_comm] using h

theorem bilinear_parts : Specs.D05.M15.Symmetrizers.bilinear_parts := by
  intro K V W _ _ _ _ _ h2 b
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    simp only [Specs.D05.M15.Symmetrizers.symmetricPart, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.flip_apply]
    rw [add_comm]
  · intro v
    simp [Specs.D05.M15.Symmetrizers.alternatingPart, LinearMap.flip_apply]
  · change (2 : K)⁻¹ • (b + b.flip) + (2 : K)⁻¹ • (b - b.flip) = b
    calc
      _ = (2 : K)⁻¹ • ((2 : K) • b) := by module
      _ = b := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem bilinear_intersection_zero :
    Specs.D05.M15.Symmetrizers.bilinear_intersection_zero := by
  intro K V W _ _ _ _ _ h2 b hs ha
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  change b u v = 0
  have h : b u v = -b u v := (hs u v).trans (alternating_skew b ha v u)
  have hz : (2 : K) • b u v = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp hz).resolve_left h2

theorem bilinear_decomposition_unique :
    Specs.D05.M15.Symmetrizers.bilinear_decomposition_unique := by
  intro K V W _ _ _ _ _ h2 b s a hs ha hsum
  have hparts := bilinear_parts h2 b
  have hzero : s - Specs.D05.M15.Symmetrizers.symmetricPart h2 b = 0 := by
    apply bilinear_intersection_zero h2
    · intro u v
      change s u v - _ = s v u - _
      rw [hs u v, hparts.1 u v]
    · intro v
      have heq : s - Specs.D05.M15.Symmetrizers.symmetricPart h2 b =
          Specs.D05.M15.Symmetrizers.alternatingPart h2 b - a := by
        apply sub_eq_sub_iff_add_eq_add.mpr
        exact hsum.trans (by simpa only [add_comm] using hparts.2.2.symm)
      rw [heq]
      change _ - a v v = 0
      rw [hparts.2.1 v, ha v, sub_self]
  have heq := sub_eq_zero.mp hzero
  refine ⟨heq, ?_⟩
  have ht := hparts.2.2
  rw [heq] at hsum
  exact add_left_cancel (hsum.trans ht.symm)

theorem tensor_intersection_zero : Specs.D05.M15.Symmetrizers.tensor_intersection_zero := by
  intro K V _ _ _ p hp h2 t hs ha
  let i : Fin p := ⟨0, by omega⟩
  let j : Fin p := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have hv := congrArg Fin.val h; simp [i, j] at hv
  have hsign : (permutationSign (Equiv.swap i j) : K) = -1 := by
    rw [D05.Foundations.PermutationSign.signTransposition p i j hij]
    simp
  have hh : t = -t := by
    calc
      t = Specs.D05.M15.PermutationActions.permutationOperator p (Equiv.swap i j) t :=
        (hs _).symm
      _ = (permutationSign (Equiv.swap i j) : K) • t := ha _
      _ = -t := by rw [hsign, neg_one_smul]
  have hz : (2 : K) • t = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hh
  exact (smul_eq_zero.mp hz).resolve_left h2

end D05.M15.Symmetrizers
