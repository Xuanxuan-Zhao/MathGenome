import MathGenome.Internal.Specs.D07.Ch15.CyclotomicGalois
import MathGenome.Internal.D07.Ch15.CyclotomicPolynomials
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
Rational cyclotomic Galois groups for a primitive root in a specified field.
The cyclotomic-extension certificate is proved for the actual intermediate
field. Rational irreducibility gives its degree and the exponent isomorphism.
The library isomorphism uses a chosen primitive root; expressing the source's
root as a power of that root proves the required action on the source's root.
-/

namespace D07.Ch15.CyclotomicGalois

open Specs.D07.Ch15.CyclotomicGalois

universe u

theorem primitive_adjoin_isCyclotomic (Ω : Type u) [Field Ω] [CharZero Ω]
    (n : ℕ) (hn : 0 < n) (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) :
    IsCyclotomicExtension {n} ℚ (IntermediateField.adjoin ℚ {ζ}) := by
  have : NeZero n := ⟨hn.ne'⟩
  exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
    n ℚ Ω (IntermediateField.adjoin ℚ {ζ}) hζ).mpr rfl

theorem cyclotomic_degree : CyclotomicDegree.{u} := by
  intro Ω _ _ n hn ζ hζ
  have : NeZero n := ⟨hn.ne'⟩
  have := primitive_adjoin_isCyclotomic Ω n hn ζ hζ
  exact ⟨IsCyclotomicExtension.finiteDimensional {n} ℚ _,
    IsCyclotomicExtension.finrank _ (CyclotomicPolynomials.rational_irreducibility n hn)⟩

theorem cyclotomic_splitting_galois : CyclotomicSplittingGalois.{u} := by
  intro Ω _ _ n hn ζ hζ
  have : NeZero n := ⟨hn.ne'⟩
  have := primitive_adjoin_isCyclotomic Ω n hn ζ hζ
  exact ⟨IsCyclotomicExtension.isSplittingField_X_pow_sub_one n ℚ _,
    Polynomial.X_pow_sub_one_separable_iff.mpr (Nat.cast_ne_zero.mpr hn.ne'),
    IsCyclotomicExtension.isGalois {n} ℚ _⟩

theorem cyclotomic_galois_equivalence : CyclotomicGaloisEquivalence.{u} := by
  intro Ω _ _ n hn ζ hζ
  have : NeZero n := ⟨hn.ne'⟩
  let E := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  let root : E := ⟨ζ, IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ)⟩
  have := primitive_adjoin_isCyclotomic Ω n hn ζ hζ
  let e : (E ≃ₐ[ℚ] E) ≃* (ZMod n)ˣ :=
    IsCyclotomicExtension.autEquivPow E (CyclotomicPolynomials.rational_irreducibility n hn)
  have hroot : IsPrimitiveRoot root n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  let ε := IsCyclotomicExtension.zeta n ℚ E
  have hε : IsPrimitiveRoot ε n := IsCyclotomicExtension.zeta_spec n ℚ E
  obtain ⟨k, _, hk⟩ := hε.eq_pow_of_pow_eq_one hroot.pow_eq_one
  have action (σ : E ≃ₐ[ℚ] E) : (σ root : Ω) = ζ ^ (e σ : ZMod n).val := by
    have hεaction : ε ^ (e σ : ZMod n).val = σ ε := hε.autToPow_spec ℚ σ
    have h : σ root = root ^ (e σ : ZMod n).val := by
      calc
        σ root = σ (ε ^ k) := congrArg σ hk.symm
        _ = (σ ε) ^ k := map_pow σ ε k
        _ = (ε ^ (e σ : ZMod n).val) ^ k := by rw [hεaction]
        _ = (ε ^ k) ^ (e σ : ZMod n).val := by rw [← pow_mul, Nat.mul_comm, pow_mul]
        _ = root ^ (e σ : ZMod n).val := by rw [hk]
    exact congrArg (fun x : E => (x : Ω)) h
  exact ⟨e, action, fun a => by simpa only [e.apply_symm_apply] using action (e.symm a)⟩

theorem cyclotomic_galois_order : CyclotomicGaloisOrder.{u} := by
  intro Ω _ _ n hn ζ hζ
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨e, _⟩ := cyclotomic_galois_equivalence Ω n hn ζ hζ
  exact ⟨Finite.of_equiv (ZMod n)ˣ e.symm.toEquiv,
    (Nat.card_congr e.toEquiv).trans (by simp [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient])⟩

theorem cyclotomic_galois_abelian : CyclotomicGaloisAbelian.{u} := by
  intro Ω _ _ n hn ζ hζ
  obtain ⟨e, _⟩ := cyclotomic_galois_equivalence Ω n hn ζ hζ
  dsimp only
  intro σ τ
  apply e.injective
  simp only [map_mul, mul_comm]

theorem cyclotomic_small_cases : CyclotomicSmallCases.{u} := by
  intro Ω _ _ n hn ζ hζ
  have hpos : 0 < n := by rcases hn with rfl | rfl <;> decide
  obtain ⟨e, _⟩ := cyclotomic_galois_equivalence Ω n hpos ζ hζ
  have hu : Subsingleton (ZMod n)ˣ := by
    rcases hn with rfl | rfl <;> infer_instance
  have := hu
  exact ⟨e.injective.subsingleton, hu⟩

end D07.Ch15.CyclotomicGalois
