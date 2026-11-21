import MathGenome.Internal.Specs.D07.Ch15.KummerForward
import MathGenome.Internal.D07.Ch15.RootsUnity
import MathGenome.Internal.D07.Ch14.DegreeIndex
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.Coset.Card

/-! K07.15.kummer_forward: no irreducibility assumption on the binomial. -/

namespace D07.Ch15.KummerForward

open Polynomial IntermediateField

universe u v

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

/-- A base field containing every root in a closed overfield contains a
primitive root. This is derived, not added as a hypothesis. -/
lemma primitive_root_in_base [IsAlgClosed Ω] {n : ℕ} (hn : 0 < n)
    (hchar : (n : K) ≠ 0)
    (hroots : ∀ ζ : Ω, ζ ^ n = 1 → ∃ c : K, algebraMap K Ω c = ζ) :
    ∃ ζ : K, IsPrimitiveRoot ζ n := by
  obtain ⟨ζ, hζ⟩ := RootsUnity.primitive_root_exists K Ω n hn hchar
  obtain ⟨c, hc⟩ := hroots ζ hζ.pow_eq_one
  refine ⟨c, ?_⟩
  rw [← hc] at hζ
  exact hζ.of_map_of_injective (algebraMap K Ω).injective

/-- Adjoining one root already supplies the whole splitting field. -/
lemma radical_step_splitting {n : ℕ} (hn : 0 < n)
    (hroots : ∀ ζ : Ω, ζ ^ n = 1 → ∃ c : K, algebraMap K Ω c = ζ)
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (a : Kˣ) {u : Ω}
    (hu : u ^ n = algebraMap K Ω (a : K)) :
    IsSplittingField K (adjoin K {u}) (X ^ n - C (a : K)) := by
  let E := adjoin K {u}
  let r : E := ⟨u, mem_adjoin_simple_self K u⟩
  have hr : r ^ n = algebraMap K E (a : K) := by
    apply Subtype.val_injective
    exact hu
  have ha : algebraMap K Ω (a : K) ≠ 0 :=
    (_root_.map_ne_zero (algebraMap K Ω)).mpr a.ne_zero
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hu
    exact ha hu.symm
  apply IntermediateField.isSplittingField_iff.mpr
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hζ.map_of_injective (algebraMap K E).injective) hr
  · apply le_antisymm
    · apply adjoin_le_iff.mpr
      rintro x rfl
      apply subset_adjoin
      exact mem_rootSet.mpr ⟨X_pow_sub_C_ne_zero hn _, by simp [hu]⟩
    · apply adjoin_le_iff.mpr
      intro x hx
      have hxpow : x ^ n = algebraMap K Ω (a : K) := by
        simpa only [map_sub, aeval_X_pow, aeval_C, sub_eq_zero] using
          (mem_rootSet.mp hx).2
      have hratio : (x / u) ^ n = 1 := by
        rw [div_pow, hxpow, hu, div_self ha]
      obtain ⟨c, hc⟩ := hroots (x / u) hratio
      have hx : x = algebraMap K Ω c * u := by rw [hc, div_mul_cancel₀ _ hu0]
      rw [hx]
      exact mul_mem (IntermediateField.algebraMap_mem E c) (mem_adjoin_simple_self K u)

/-- The full radical-step theorem, including finiteness and degree divisibility. -/
theorem kummer_forward : Specs.D07.Ch15.KummerForward.RadicalStepCyclicGalois.{u, v} := by
  intro K Ω _ _ _ _ n hn hchar hroots a u hu
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := primitive_root_in_base hn hchar hroots
  let E := adjoin K {u}
  let r : E := ⟨u, mem_adjoin_simple_self K u⟩
  have hr : r ^ n = algebraMap K E (a : K) := by
    apply Subtype.val_injective
    exact hu
  have ha : algebraMap K E (a : K) ≠ 0 := (_root_.map_ne_zero (algebraMap K E)).mpr a.ne_zero
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hr
    exact ha hr.symm
  let : IsSplittingField K E (X ^ n - C (a : K)) :=
    radical_step_splitting hn hroots hζ a hu
  let : FiniteDimensional K E := IsSplittingField.finiteDimensional E (X ^ n - C (a : K))
  let : IsGalois K E := IsGalois.of_separable_splitting_field
    (separable_X_pow_sub_C (a : K) hchar a.ne_zero)
  have ratio_pow (σ : E ≃ₐ[K] E) : (σ r / r) ^ n = 1 := by
    rw [div_pow, ← map_pow, hr, σ.commutes, div_self ha]
  have root_is_scalar (x : E) (hx : x ^ n = 1) :
      ∃ c : K, algebraMap K E c = x := by
    have hxΩ : (x : Ω) ^ n = 1 := congrArg Subtype.val hx
    obtain ⟨c, hc⟩ := hroots x hxΩ
    exact ⟨c, Subtype.val_injective hc⟩
  let χ : (E ≃ₐ[K] E) →* rootsOfUnity n E :=
    { toFun := fun σ => rootsOfUnity.mkOfPowEq (σ r / r) (ratio_pow σ)
      map_one' := by
        apply rootsOfUnity.coe_injective
        change r / r = 1
        exact div_self hr0
      map_mul' := by
        intro σ τ
        apply rootsOfUnity.coe_injective
        change (σ * τ) r / r = (σ r / r) * (τ r / r)
        obtain ⟨c, hc⟩ := root_is_scalar (τ r / r) (ratio_pow τ)
        have hfix : σ (τ r / r) = τ r / r := by rw [← hc, σ.commutes]
        have hτ : τ r = (τ r / r) * r := (div_mul_cancel₀ _ hr0).symm
        rw [AlgEquiv.mul_apply, hτ, map_mul, hfix]
        field_simp }
  have hχ : Function.Injective χ := by
    intro σ τ heq
    have heq' : σ r / r = τ r / r :=
      congrArg (fun q : rootsOfUnity n E => ((q : Eˣ) : E)) heq
    have hgen : σ r = τ r := (div_left_inj' hr0).mp heq'
    apply AlgEquiv.coe_toAlgHom_injective
    apply adjoin_algHom_ext K
    rintro x rfl
    exact hgen
  have hcyc : IsCyclic (E ≃ₐ[K] E) := isCyclic_of_injective χ hχ
  have hdegree : Module.finrank K E = Nat.card (E ≃ₐ[K] E) :=
    (Ch14.DegreeIndex.degree_index K E (⊥ : Subgroup (E ≃ₐ[K] E))).2.2
  refine ⟨inferInstance, inferInstance, hcyc, ?_⟩
  rw [hdegree, ← (hζ.map_of_injective (algebraMap K E).injective).card_rootsOfUnity]
  exact Subgroup.card_dvd_of_injective χ hχ

end D07.Ch15.KummerForward
