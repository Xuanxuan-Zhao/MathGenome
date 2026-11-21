import MathGenome.Internal.Specs.D07.Ch23.CentralizersFiniteDivisionCoordinates

/-! Finite left coordinates over division subrings, without a commutativity
assumption or use of Wedderburn's theorem. -/

universe u v

namespace D07.Ch23.CentralizersFiniteDivisionCoordinates

open Specs.D07.Ch23.CentralizersFiniteDivisionCoordinates

theorem leftBasisAndCounting : LeftBasisAndCounting.{u} := by
  intro D _ _ E
  classical
  let b := Module.finBasis E D
  refine ⟨Module.finrank E D, b, rfl, Module.finrank_pos, ?_,
    Module.natCard_eq_pow_finrank⟩
  intro x
  refine ⟨b.equivFun x, ?_, ?_⟩
  · exact (b.sum_equivFun x).symm
  · intro a ha
    apply b.equivFun.symm.injective
    simpa only [Module.Basis.equivFun_symm_apply, LinearEquiv.symm_apply_apply,
      Subfield.smul_def, smul_eq_mul] using ha.symm

theorem centralDimensions :
    ∀ (F : Type v) [Field F] [Finite F]
      (D : Type u) [DivisionRing D] [Finite D] [Algebra F D]
      (E : Subfield D) (hF : ∀ a : F, algebraMap F D a ∈ E),
      letI := centralSubfieldAlgebra F D E hF
      let q := Nat.card F
      let d := Module.finrank F E
      let n := Module.finrank F D
      let r := Module.finrank E D
      1 < q ∧ 0 < d ∧ 0 < n ∧ 0 < r ∧
        Nat.card E = q ^ d ∧ Nat.card D = q ^ n ∧
        n = d * r ∧ d ∣ n ∧ (E ≠ ⊤ → d < n) := by
  intro F _ _ D _ _ _ E hF
  let := centralSubfieldAlgebra F D E hF
  let : IsScalarTower F E D := ⟨fun a b x => by
    change (algebraMap F D a * (b : D)) * x = a • ((b : D) * x)
    rw [Algebra.smul_def, mul_assoc]⟩
  dsimp only
  have hq : 1 < Nat.card F := by
    let := Fintype.ofFinite F
    simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := F))
  refine ⟨hq, Module.finrank_pos, Module.finrank_pos, Module.finrank_pos,
    Module.natCard_eq_pow_finrank, Module.natCard_eq_pow_finrank,
    (Module.finrank_mul_finrank F E D).symm,
    Module.finrank_dvd_finrank_right F E D, ?_⟩
  intro hE
  have hcard : Nat.card E < Nat.card D := by
    let := Fintype.ofFinite E
    let := Fintype.ofFinite D
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_injective_not_surjective ((↑) : E → D) Subtype.val_injective
    intro hsurj
    apply hE
    apply SetLike.ext
    intro x
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨y, rfl⟩ := hsurj x
      exact y.property
  rw [Module.natCard_eq_pow_finrank (K := F) (V := E),
    Module.natCard_eq_pow_finrank (K := F) (V := D)] at hcard
  exact (Nat.pow_lt_pow_iff_right hq).mp hcard

end D07.Ch23.CentralizersFiniteDivisionCoordinates
