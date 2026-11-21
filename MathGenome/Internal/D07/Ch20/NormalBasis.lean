import MathGenome.Internal.Specs.D07.Ch20.NormalBasis
import MathGenome.Internal.D07.Ch20.NormalBasisFiniteBaseNormalBasis
import MathGenome.Internal.D07.Ch20.NormalBasisInfiniteBaseNormalBasis
import MathGenome.Internal.D07.Ch13.GaloisGroup
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.FieldTheory.Finite.Trace

/-!
K07.20.normal_basis. Combine the two upstream branches. Over a finite
base, finite degree makes the extension field finite. The ordered
Frobenius basis is transported along the bijective enumeration of the
relative automorphisms by Frobenius powers. Over an infinite base, use
the upstream determinant construction. Both branches allow degree one
and neither divides by the extension degree.
-/

noncomputable section
universe u v
namespace D07.Ch20.NormalBasis

open Specs.D07.Ch20.NormalBasis

theorem finite_field_normal_basis : FiniteFieldNormalBasis.{u, v} := by
  intro K L _ _ _ _ _ q n hq hn
  let : Finite L := Module.finite_of_finite K
  obtain ⟨_, _, _, _, a, B, _, _, hB⟩ :=
    NormalBasisFiniteBaseNormalBasis.finite_base_normal_basis K L q n hq hn
  exact ⟨a, B, hB⟩

theorem normal_basis_exists : NormalBasisExists.{u, v} := by
  intro K L _ _ _ _ _
  classical
  cases finite_or_infinite K with
  | inl hK =>
    let := hK
    let : Finite L := Module.finite_of_finite K
    obtain ⟨a, B, hB⟩ := finite_field_normal_basis K L (Nat.card K)
      (Module.finrank K L) rfl rfl
    obtain ⟨_, _, _, _, _, _, _, Φ, hΦ, _, _, hbij⟩ :=
      Ch13.GaloisGroup.finite_extension_galois_group K L (Nat.card K)
        (Module.finrank K L) rfl rfl
    let e : Fin (Module.finrank K L) ≃ (L ≃ₐ[K] L) := Equiv.ofBijective _ hbij
    have hpow (j : ℕ) : (Φ ^ j) a = a ^ (Nat.card K ^ j) := by
      rw [AlgEquiv.coe_pow, show (Φ : L → L) = (fun x => x ^ Nat.card K) from funext hΦ,
        pow_iterate]
    refine ⟨a, B.reindex e, ?_⟩
    intro σ
    obtain ⟨j, rfl⟩ := e.surjective σ
    rw [Module.Basis.reindex_apply, e.symm_apply_apply, hB]
    exact (hpow j.val).symm
  | inr hK =>
    let := hK
    exact NormalBasisInfiniteBaseNormalBasis.normal_basis_exists K L

theorem embedded_normal_basis : EmbeddedNormalBasis.{u, v} := by
  intro K Ω _ _ _ _ _ _ q n hq hn
  obtain ⟨_, _, hdim, hdegree, _, _, _⟩ :=
    Ch13.Existence.embedded_existence K Ω q n hq hn
  let := hdim
  exact finite_field_normal_basis K _ q n hq hdegree

/-- Degree one already provides the first counterexample: 1 in F_3. -/
theorem normal_not_primitive : NormalNotPrimitive := by
  classical
  refine ⟨1, ?_, ?_⟩
  · let : Unique (ZMod 3 ≃ₐ[ZMod 3] ZMod 3) :=
      { default := 1
        uniq := fun σ => by ext x; simpa using σ.commutes x }
    exact ⟨Module.Basis.singleton _ _, fun σ => by simp⟩
  · simp only [orderOf_one, Nat.card_eq_fintype_card]
    decide

/-- For a normal element a in F_8, the element a+a² is nonzero and has
trace zero. It is different from 1 since the degree is odd. All nonidentity
units of F_8 have order 7, so this gives a primitive element which is not normal. -/
theorem primitive_not_normal : PrimitiveNotNormal := by
  classical
  let K := ZMod 2
  let L := GaloisField 2 3
  have hdegree : Module.finrank K L = 3 := GaloisField.finrank 2 (by decide)
  have hcard : Nat.card L = 8 := GaloisField.card 2 3 (by decide)
  have hunitcard : Nat.card Lˣ = 7 := by rw [Nat.card_units, hcard]
  obtain ⟨a, B, hB⟩ := finite_field_normal_basis K L 2 3 (by simp [K]) hdegree
  let x : L := a + a ^ 2
  have hx0 : x ≠ 0 := by
    intro h
    have ha : a = a ^ 2 := CharTwo.add_eq_zero.mp h
    have hb : B (0 : Fin 3) = B 1 := by simpa [hB] using ha
    have : (0 : Fin 3) = 1 := B.injective hb
    exact (by decide : (0 : Fin 3) ≠ 1) this
  let : Fintype L := Fintype.ofFinite L
  have hax : a ^ 8 = a := by
    have h := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have hs2 : x ^ 2 = a ^ 2 + a ^ 4 := by
    dsimp [x]
    rw [CharTwo.add_sq, ← pow_mul]
  have hs4 : x ^ 4 = a ^ 4 + a ^ 8 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hs2, CharTwo.add_sq]
    simp only [← pow_mul]
  have hxsum : x + x ^ 2 + x ^ 4 = 0 := by
    rw [hs2, hs4, hax]
    dsimp [x]
    calc
      _ = (a + a) + (a ^ 2 + a ^ 2) + (a ^ 4 + a ^ 4) := by ac_rfl
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
  have hx1 : x ≠ 1 := by
    intro h
    simp [h, CharTwo.add_self_eq_zero] at hxsum
  let u : Lˣ := Units.mk0 x hx0
  have hu1 : u ≠ 1 := by
    intro h
    exact hx1 (congrArg (fun z : Lˣ => (z : L)) h)
  have horder : orderOf u = 7 := by
    have hd : orderOf u ∣ 7 := hunitcard ▸ orderOf_dvd_natCard u
    rcases (by decide : Nat.Prime 7).eq_one_or_self_of_dvd _ hd with h | h
    · exact False.elim (hu1 (orderOf_eq_one_iff.mp h))
    · exact h
  refine ⟨u, horder.trans hunitcard.symm, ?_⟩
  rintro ⟨C, hC⟩
  have hxtrace : Algebra.trace K L x = 0 := by
    apply (algebraMap K L).injective
    rw [map_zero, FiniteField.algebraMap_trace_eq_sum_pow, hdegree]
    simpa [Finset.sum_range_succ, K] using hxsum
  have hsum : ∑ σ : L ≃ₐ[K] L, σ x = 0 := by
    rw [← trace_eq_sum_automorphisms, hxtrace, map_zero]
  have hz : ∀ σ : L ≃ₐ[K] L, (1 : K) = 0 :=
    Fintype.linearIndependent_iff.mp C.linearIndependent (fun _ => 1)
      (by simpa only [one_smul, hC, u, Units.val_mk0] using hsum)
  exact one_ne_zero (hz 1)

end D07.Ch20.NormalBasis
