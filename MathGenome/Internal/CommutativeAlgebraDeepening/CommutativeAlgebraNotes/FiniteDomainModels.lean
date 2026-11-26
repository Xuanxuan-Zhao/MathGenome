import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Integral

namespace CommutativeAlgebraNotes

open Polynomial

/-- A finite extension of the fraction field of a domain has a finite domain model
inside the extension. -/
theorem exists_finite_domain_model (S K M : Type*)
    [CommRing S] [IsDomain S] [Field K] [Field M]
    [Algebra S K] [IsFractionRing S K] [Algebra K M] [Module.Finite K M]
    [Algebra S M] [IsScalarTower S K M] :
    ∃ B : Subalgebra S M, IsDomain B ∧ Module.Finite S B ∧ IsFractionRing B M := by
  classical
  have : Algebra.IsAlgebraic S M := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic K M)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := K) (M := M)
  obtain ⟨d, hd, hInt⟩ := Algebra.IsAlgebraic.exists_integral_multiples S t
  let B : Subalgebra S M := Algebra.adjoin S ((fun x : M => d • x) '' (t : Set M))
  refine ⟨B, inferInstance, Algebra.finite_adjoin_of_finite_of_isIntegral
    (t.finite_toSet.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hInt x hx), ?_⟩
  apply IsFractionRing.of_field
  have hclear : ∀ x : M, ∃ s : S, s ≠ 0 ∧ algebraMap S M s * x ∈ B := by
    intro x
    have hx : x ∈ Submodule.span K (t : Set M) := ht.symm ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine ⟨d, hd, ?_⟩
      rw [← Algebra.smul_def]
      exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [map_mul, mul_add]
      have h₁ := B.mul_mem (B.algebraMap_mem b) hax
      have h₂ := B.mul_mem (B.algebraMap_mem a) hby
      simpa only [mul_left_comm, mul_assoc] using B.add_mem h₁ h₂
    | smul k x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective S k
      have hcK := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) hc
      have hkc : algebraMap S K c * k = algebraMap S K b :=
        (mul_comm _ _).trans ((eq_div_iff_mul_eq hcK).mp hbc.symm)
      have hkcM : algebraMap S M c * algebraMap K M k = algebraMap S M b := by
        simpa only [map_mul, ← IsScalarTower.algebraMap_apply S K M] using
          congrArg (algebraMap K M) hkc
      refine ⟨a * c, mul_ne_zero ha (mem_nonZeroDivisors_iff_ne_zero.mp hc), ?_⟩
      rw [map_mul, Algebra.smul_def, mul_assoc, ← mul_assoc (algebraMap S M c), hkcM]
      simpa only [mul_left_comm] using B.mul_mem (B.algebraMap_mem b) hax
  intro x
  obtain ⟨s, hs, hx⟩ := hclear x
  have hmap : Function.Injective (algebraMap S M) := by
    rw [IsScalarTower.algebraMap_eq S K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective S K)
  refine ⟨⟨_, hx⟩, algebraMap S B s, ?_⟩
  change x = (algebraMap S M s * x) / algebraMap S M s
  rw [mul_comm, mul_div_cancel_right₀ _ ((map_ne_zero_iff _ hmap).mpr hs)]

/-- A fraction can be cleared with any prescribed positive power of a denominator. -/
theorem exists_pow_mul_mem {S M : Type*} [CommRing S] [Field M] [Algebra S M]
    (B : Subalgebra S M) [IsFractionRing B M] (f : M) (p : ℕ) (hp : 0 < p) :
    ∃ b : B, b ≠ 0 ∧ (algebraMap B M b) ^ p * f ∈ B := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors B) f
  refine ⟨b, mem_nonZeroDivisors_iff_ne_zero.mp b.prop, ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [pow_succ, mul_assoc, mul_comm (algebraMap B M b.val), hab]
  exact B.mul_mem (B.pow_mem b.val.prop _) a.prop

/-- Scaling the radicand by the p-th power of a nonzero scalar maps the new root
to that scalar times the old root. -/
theorem exists_scaled_adjoin_root_equiv (M : Type*) [Field M] (p : ℕ) (f c : M)
    (hc : c ≠ 0) :
    ∃ e : AdjoinRoot (X ^ p - C (c ^ p * f)) ≃ₐ[M] AdjoinRoot (X ^ p - C f),
      e (AdjoinRoot.root (X ^ p - C (c ^ p * f))) =
        algebraMap M _ c * AdjoinRoot.root (X ^ p - C f) := by
  let P : M[X] := X ^ p - C f
  let Q : M[X] := X ^ p - C (c ^ p * f)
  have rootPow (a : M) :
      AdjoinRoot.root (X ^ p - C a) ^ p = algebraMap M _ a := by
    have h := AdjoinRoot.eval₂_root (X ^ p - C a)
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
    exact sub_eq_zero.mp h
  have hP : AdjoinRoot.root P ^ p = algebraMap M (AdjoinRoot P) f := rootPow f
  have hQ : AdjoinRoot.root Q ^ p = algebraMap M (AdjoinRoot Q) (c ^ p * f) :=
    rootPow (c ^ p * f)
  have hφ : Q.eval₂ (Algebra.ofId M (AdjoinRoot P)).toRingHom
      (algebraMap M _ c * AdjoinRoot.root P) = 0 := by
    change (X ^ p - C (c ^ p * f)).eval₂ (algebraMap M (AdjoinRoot P)) _ = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, mul_pow, hP, map_mul, map_pow, sub_self]
  have hψ : P.eval₂ (Algebra.ofId M (AdjoinRoot Q)).toRingHom
      (algebraMap M _ c⁻¹ * AdjoinRoot.root Q) = 0 := by
    change (X ^ p - C f).eval₂ (algebraMap M (AdjoinRoot Q)) _ = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, mul_pow, hQ, ← map_pow,
      ← map_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, one_mul, sub_self]
  let φ : AdjoinRoot Q →ₐ[M] AdjoinRoot P :=
    AdjoinRoot.liftAlgHom Q (Algebra.ofId M _) _ hφ
  let ψ : AdjoinRoot P →ₐ[M] AdjoinRoot Q :=
    AdjoinRoot.liftAlgHom P (Algebra.ofId M _) _ hψ
  have hφroot : φ (AdjoinRoot.root Q) = algebraMap M _ c * AdjoinRoot.root P :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  have hψroot : ψ (AdjoinRoot.root P) = algebraMap M _ c⁻¹ * AdjoinRoot.root Q :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  have hleft : ψ.comp φ = AlgHom.id M (AdjoinRoot Q) := by
    apply AdjoinRoot.algHom_ext
    change ψ (φ (AdjoinRoot.root Q)) = AdjoinRoot.root Q
    rw [hφroot, map_mul, AlgHom.commutes, hψroot]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  have hright : φ.comp ψ = AlgHom.id M (AdjoinRoot P) := by
    apply AdjoinRoot.algHom_ext
    change φ (ψ (AdjoinRoot.root P)) = AdjoinRoot.root P
    rw [hψroot, map_mul, AlgHom.commutes, hφroot]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  refine ⟨AlgEquiv.ofAlgHom φ ψ hright hleft, ?_⟩
  exact hφroot

end CommutativeAlgebraNotes
