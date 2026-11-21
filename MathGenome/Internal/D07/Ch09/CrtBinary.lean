import MathGenome.Internal.Specs.D07.Ch09.CrtBinary
import MathGenome.Internal.D07.Ch09.FirstIsomorphism
import MathGenome.Internal.D07.Ch09.ProductIntersection
import Mathlib.Tactic.NormNum

/-! K07.09.crt_binary: the natural binary CRT and its explicit inverse. -/

universe u

namespace D07.Ch09.CrtBinary

open Specs.D07.Ch09.CrtBinary

def reductionMap {R : Type u} [CommRing R] (I J : Ideal R) :
    R →+* (R ⧸ I) × (R ⧸ J) :=
  (Ideal.Quotient.mk I).prod (Ideal.Quotient.mk J)

theorem kernelIsIntersection : KernelIsIntersection.{u} := by
  intro R _ I J
  ext r
  simp [RingHom.mem_ker, reductionMapValue, Prod.ext_iff,
    Ideal.Quotient.eq_zero_iff_mem]

theorem explicitPreimage : ExplicitPreimage.{u} := by
  intro R _ I J i j hi hj hij a b
  have hi0 : Ideal.Quotient.mk I i = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have hj0 : Ideal.Quotient.mk J j = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hj
  have hj1 : Ideal.Quotient.mk I j = 1 := by
    have h := congrArg (Ideal.Quotient.mk I) hij
    simpa [map_add, hi0] using h
  have hi1 : Ideal.Quotient.mk J i = 1 := by
    have h := congrArg (Ideal.Quotient.mk J) hij
    simpa [map_add, hj0] using h
  apply Prod.ext <;>
    simp [reductionMapValue, map_add, map_mul, hi0, hj0, hj1, hi1]

theorem reductionSurjective : ReductionSurjective.{u} := by
  intro R _ I J h
  obtain ⟨i, hi, j, hj, hij⟩ :=
    (D07.Ch09.Comaximal.witnessCharacterization R I J).mp h
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨a * j + b * i, explicitPreimage R I J i j hi hj hij a b⟩

theorem binaryCRT : BinaryCRT.{u} := by
  intro R _ I J h
  let f := reductionMapValue I J
  have hker : I * J = RingHom.ker f := by
    rw [D07.Ch09.ProductIntersection.binaryProductIntersection R I J h]
    exact (kernelIsIntersection R I J).symm
  obtain ⟨e₀, he₀⟩ :=
    D07.Ch09.FirstIsomorphism.first_isomorphism_of_surjective
      R ((R ⧸ I) × (R ⧸ J)) f (reductionSurjective R I J h)
  let e := (Ideal.quotEquivOfEq hker).trans e₀
  have he : ∀ r : R, e (Ideal.Quotient.mk (I * J) r) = f r := by
    intro r
    simpa [e] using he₀ r
  refine ⟨e, he, ?_⟩
  intro i j hi hj hij a b
  apply e.injective
  rw [e.apply_symm_apply, he]
  exact (explicitPreimage R I J i j hi hj hij a b).symm

theorem integerCounterexample : IntegerCounterexample := by
  let I : Ideal ℤ := Ideal.span {2}
  have htwo : (1 : ℤ) ∉ I := by
    change (1 : ℤ) ∉ Ideal.span {(2 : ℤ)}
    rw [Ideal.mem_span_singleton]
    norm_num
  have h01 : (0 : ℤ ⧸ I) ≠ 1 := by
    intro h
    apply htwo
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa using h.symm
  have hdiag : ∀ x y : ℤ ⧸ I,
      (x, y) ∈ (reductionMapValue I I).range ↔ x = y := by
    intro x y
    constructor
    · rintro ⟨r, hr⟩
      exact (congrArg Prod.fst hr).symm.trans (congrArg Prod.snd hr)
    · rintro rfl
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨r, rfl⟩
  refine ⟨?_, hdiag, ?_⟩
  · intro h
    apply htwo
    change I ⊔ I = ⊤ at h
    rw [sup_idem] at h
    exact (Ideal.eq_top_iff_one I).mp h
  · intro h
    obtain ⟨r, hr⟩ := h (0, 1)
    exact h01 ((hdiag 0 1).mp ⟨r, hr⟩)

end D07.Ch09.CrtBinary
