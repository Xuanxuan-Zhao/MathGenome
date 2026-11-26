import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientIntersectionAfterExtension
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DerivationsOfNonPowers
import Mathlib.Algebra.Polynomial.Derivation
import Batteries.Tactic.OpenPrivate

namespace CommutativeAlgebraNotes

noncomputable section

open Polynomial
open scoped IntermediateField

open private integral_of_powers_mem binomial_aeval from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.PBases

private theorem minpoly_eq_binomial
    {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {E : Subfield F} (hE : frobeniusSubfield F p ≤ E) {x : F} (hx : x ∉ E) :
    minpoly E x = X ^ p - C (⟨x ^ p, hE ⟨x, rfl⟩⟩ : E) := by
  let a : E := ⟨x ^ p, hE ⟨x, rfl⟩⟩
  have hp : p.Prime := Fact.out
  have hi : Irreducible (X ^ p - C a) := by
    apply X_pow_sub_C_irreducible_of_prime hp
    intro b hb
    have he : (b : F) ^ p = x ^ p := congrArg Subtype.val hb
    exact hx (frobenius_inj F p he ▸ b.property)
  exact (minpoly.eq_of_irreducible_of_monic hi (binomial_aeval hE x)
    (monic_X_pow_sub_C a hp.ne_zero)).symm

/-- A maximal subfield containing the base and avoiding the chosen element
makes the ambient field a simple purely inseparable extension. -/
private theorem exists_simple_adjoin_of_nonmem
    {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {H : Subfield F} (hH : frobeniusSubfield F p ≤ H) {x : F} (hx : x ∉ H) :
    ∃ E : Subfield F, H ≤ E ∧ x ∉ E ∧ E⟮x⟯ = ⊤ := by
  classical
  let U : Set (Subfield F) := {E | x ∉ E}
  obtain ⟨E, hHE, hm⟩ := zorn_le_nonempty₀ U (fun c hc chain A hAc => by
    refine ⟨sSup c, ?_, fun _ h => le_sSup h⟩
    exact fun h => by
      obtain ⟨V, hV, hxV⟩ := (Subfield.mem_sSup_of_directedOn ⟨A, hAc⟩ chain.directedOn).mp h
      exact hc hV hxV) H hx
  have hxE : x ∉ E := hm.1
  have hE := hH.trans hHE
  have hdeg {z : F} (hz : z ∉ E) : Module.finrank E E⟮z⟯ = p := by
    rw [IntermediateField.adjoin.finrank (integral_of_powers_mem hE z),
      minpoly_eq_binomial hE hz, natDegree_X_pow_sub_C]
  refine ⟨E, hHE, hxE, top_unique ?_⟩
  intro y _
  by_cases hy : y ∈ E
  · exact (E⟮x⟯).algebraMap_mem (⟨y, hy⟩ : E)
  have hx' : x ∈ E⟮y⟯ := by
    by_contra hn
    exact hy (hm.2 hn (fun z hz => (E⟮y⟯).algebraMap_mem (⟨z, hz⟩ : E))
      (IntermediateField.mem_adjoin_simple_self E y))
  let := IntermediateField.adjoin.finiteDimensional (integral_of_powers_mem hE y)
  have he : E⟮x⟯ = E⟮y⟯ := IntermediateField.eq_of_le_of_finrank_eq
    (IntermediateField.adjoin_simple_le_iff.mpr hx') ((hdeg hxE).trans (hdeg hy).symm)
  rw [he]
  exact IntermediateField.mem_adjoin_simple_self E y

/-- Differentiate the polynomial presentation over a field of constants
containing the prescribed base. -/
private theorem exists_derivation_of_nonmem
    {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {H : Subfield F} (hH : frobeniusSubfield F p ≤ H) {x : F} (hx : x ∉ H) :
    ∃ D : Derivation ℤ F F, D x = 1 ∧ ∀ c ∈ H, D c = 0 := by
  obtain ⟨E, hHE, hxE, hgen⟩ := exists_simple_adjoin_of_nonmem hH hx
  have hE := hH.trans hHE
  have hsurj : Function.Surjective (aeval (R := E) x) := by
    have htop := (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (integral_of_powers_mem hE x).isAlgebraic).mp hgen
    rw [Algebra.adjoin_singleton_eq_range_aeval] at htop
    intro y
    apply (aeval (R := E) x).mem_range.mp
    rw [htop]
    trivial
  have hderiv : derivative (minpoly E x) = 0 := by
    rw [minpoly_eq_binomial hE hxE]
    simp [derivative_X_pow]
  have hker (q : E[X]) (hq : aeval x q = 0) :
      aeval (R := E) x (derivative' q) = 0 := by
    obtain ⟨g, rfl⟩ := minpoly.dvd_iff.mpr hq
    simp [hderiv, minpoly.aeval]
  let D : Derivation E F F := Derivation.liftOfSurjective hsurj hker
  refine ⟨D.restrictScalars ℤ, ?_, fun c hc => D.map_algebraMap (⟨c, hHE hc⟩ : E)⟩
  change D x = 1
  simpa only [aeval_X, derivative'_apply, derivative_X, map_one] using
    Derivation.liftOfSurjective_apply hsurj hker (X : E[X])

/-- Clear the denominators of a field derivation on a finite algebra generating set. -/
private theorem exists_derivation_after_clearing_denominators
    {A B F : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field F]
    [Algebra A B] [Algebra.FiniteType A B] [Algebra B F] [IsFractionRing B F]
    (D : Derivation ℤ F F)
    (hD : ∀ a : A, D (algebraMap B F (algebraMap A B a)) = 0)
    (f : B) (hf : D (algebraMap B F f) ≠ 0) :
    ∃ d : Derivation ℤ B B, d f ≠ 0 := by
  classical
  let i := algebraMap B F
  have hi : Function.Injective i := IsFractionRing.injective B F
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  have clear (t : Finset B) :
      ∃ b : B, b ≠ 0 ∧ ∀ x ∈ t, i b * D (i x) ∈ i.range := by
    induction t using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | @insert x t hxt ih =>
      obtain ⟨b, hb, hbt⟩ := ih
      obtain ⟨n, c, hc, hfrac⟩ := IsFractionRing.div_surjective B (D (i x))
      change i n / i c = D (i x) at hfrac
      have hc0 := nonZeroDivisors.ne_zero hc
      have hic : i c ≠ 0 := fun h => hc0 (hi (h.trans (map_zero i).symm))
      have hcx : i c * D (i x) = i n := by
        rw [← hfrac, mul_comm, div_mul_cancel₀ _ hic]
      refine ⟨b * c, mul_ne_zero hb hc0, fun y hy => ?_⟩
      rw [map_mul]
      rcases Finset.mem_insert.mp hy with rfl | hyt
      · rw [mul_assoc, hcx, ← map_mul]
        exact ⟨b * n, rfl⟩
      · rw [mul_comm (i b) (i c), mul_assoc]
        exact i.range.mul_mem ⟨c, rfl⟩ (hbt y hyt)
  obtain ⟨b, hb, hbs⟩ := clear s
  have hpres (x : B) : i b * D (i x) ∈ i.range := by
    have hx : x ∈ Algebra.adjoin A (s : Set B) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact hbs y hy
    | algebraMap a =>
      rw [hD, mul_zero]
      exact i.range.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add, map_add, mul_add]
      exact i.range.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, mul_add,
        mul_left_comm (i b) (i x), mul_left_comm (i b) (i y)]
      exact i.range.add_mem (i.range.mul_mem ⟨x, rfl⟩ hy) (i.range.mul_mem ⟨y, rfl⟩ hx)
  let δ : B → B := fun x => (hpres x).choose
  have hδ (x : B) : i (δ x) = i b * D (i x) := (hpres x).choose_spec
  let δadd : B →+ B :=
    { toFun := δ
      map_zero' := hi (by simp [hδ])
      map_add' := fun x y => hi (by simp [hδ, mul_add]) }
  let d : Derivation ℤ B B := Derivation.mk' δadd.toIntLinearMap fun x y => hi (by
    change i (δ (x * y)) = i (x * δ y + y * δ x)
    simp only [map_add, map_mul, hδ, D.leibniz, smul_eq_mul, mul_add]
    rw [mul_left_comm (i b) (i x), mul_left_comm (i b) (i y)])
  refine ⟨d, fun h => ?_⟩
  change δ f = 0 at h
  have hib : i b ≠ 0 := fun h => hb (hi (h.trans (map_zero i).symm))
  exact (mul_ne_zero hib hf) ((hδ f).symm.trans (by rw [h, map_zero]))

/-- Lemma 5.5. A non-power in the fraction field is detected by a derivation
taking values in the original finite-type domain. -/
theorem exists_derivation_ne_zero_of_not_pth_power :
    Specs.CommutativeAlgebraNotes.DerivationsOfNonPowers.DerivationsDetectNonPowers := by
  classical
  intro k _ p _ _ r s S B _ _ _ _ hSB F _ _ _ _ f hf
  let K := FractionRing S
  let : Algebra K F := (IsFractionRing.lift (K := K)
    (g := (algebraMap B F).comp (algebraMap S B))
    ((IsFractionRing.injective B F).comp hSB)).toAlgebra
  let : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  obtain ⟨E, _, hfinite, _, _, hinter⟩ := finiteCoefficientApproximations k p r s
  let T (J : Finset E) : Subring S :=
    finiteCoefficientSubring (p := p) (fun x : E => (x : k)) J r s
  let H (J : Finset E) : Subfield F :=
    frobeniusSubfield F p ⊔ (fractionSubfieldOfSubring (T J)).map (algebraMap K F)
  let x := algebraMap B F f
  have hxf : x ∉ frobeniusSubfield F p := fun h => hf (mem_frobeniusSubfield.mp h)
  have hi : (⨅ J, H J) = frobeniusSubfield F p := hinter F
  obtain ⟨J, hJ⟩ : ∃ J, x ∉ H J := by
    by_contra! h
    exact hxf (hi ▸ Subfield.mem_iInf.mpr h)
  obtain ⟨D, hDx, hD⟩ := exists_derivation_of_nonmem (H := H J) le_sup_left hJ
  let : Module.Finite (T J) S := (hfinite J).1
  let : Algebra (T J) B := ((algebraMap S B).comp (T J).subtype).toAlgebra
  let : IsScalarTower (T J) S B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FiniteType (T J) B := Algebra.FiniteType.trans
    (R := T J) (S := S) (A := B) inferInstance inferInstance
  refine exists_derivation_after_clearing_denominators (A := T J) D ?_ f ?_
  · intro a
    have ha : algebraMap K F (algebraMap S K a.val) = algebraMap B F (algebraMap (T J) B a) :=
      IsFractionRing.lift_algebraMap (K := K)
        (g := (algebraMap B F).comp (algebraMap S B))
        ((IsFractionRing.injective B F).comp hSB) a.val
    rw [← ha]
    have hle : (fractionSubfieldOfSubring (T J)).map (algebraMap K F) ≤ H J := le_sup_right
    exact hD _ (hle (Subfield.mem_map.mpr
      ⟨_, algebraMap_mem_fractionSubfieldOfSubring a.property, rfl⟩))
  · exact hDx.trans_ne one_ne_zero

end

end CommutativeAlgebraNotes
