import MathGenome.Internal.Specs.D07.Ch16.IntegerPresentationCokernel
import MathGenome.Internal.D07.Ch16.Smith

namespace D07.Ch16.IntegerPresentationCokernel
open scoped DirectSum

theorem unitFactorZero : Specs.D07.Ch16.IntegerPresentationCokernel.UnitFactorZero := by
  intro d
  rw [← (Int.quotientSpanNatEquivZMod d).toEquiv.subsingleton_congr]
  rw [D07.Ch16.Smith.unitQuotient]
  exact Int.isUnit_iff_natAbs_eq.trans (by simp)

theorem unitFactorDeletion : Specs.D07.Ch16.IntegerPresentationCokernel.UnitFactorDeletion := by
  intro s d
  classical
  let p : (∀ i : Fin s, ZMod (d i)) →ₗ[ℤ]
      (∀ i : {i : Fin s // d i ≠ 1}, ZMod (d i.val)) :=
    LinearMap.pi fun i => LinearMap.proj i.val
  have hp : Function.Bijective p := by
    constructor
    · intro x y hxy
      ext i
      by_cases h : d i = 1
      · have := (unitFactorZero (d i)).mpr h
        exact Subsingleton.elim _ _
      · exact congrArg (fun z => z ⟨i, h⟩) hxy
    · intro y
      refine ⟨fun i => if h : d i = 1 then 0 else y ⟨i, h⟩, ?_⟩
      ext i
      simp [p, i.property]
  exact ⟨LinearEquiv.ofBijective p hp, fun _ _ => rfl⟩

/-- With no free coordinates the cardinality is the product of the moduli. -/
theorem finiteProductCard {s : ℕ} (d : Fin s → ℕ) (hd : ∀ i, 0 < d i) :
    Finite ((Fin 0 → ℤ) × (∀ i, ZMod (d i))) ∧
    Nat.card ((Fin 0 → ℤ) × (∀ i, ZMod (d i))) = ∏ i, d i := by
  let : ∀ i, NeZero (d i) := fun i => ⟨(hd i).ne'⟩
  constructor
  · infer_instance
  · simp

/-- A free coordinate provides an injection of the integers. -/
theorem infiniteFreeProduct {s t : ℕ} (d : Fin s → ℕ) (ht : 0 < t) :
    Infinite ((Fin t → ℤ) × (∀ i, ZMod (d i))) := by
  apply Infinite.of_injective (fun z : ℤ => ((fun _ : Fin t => z), 0))
  intro x y h
  exact congrArg (fun p => p.1 ⟨0, ht⟩) h

theorem cokernelDecomposition :
    Specs.D07.Ch16.IntegerPresentationCokernel.CokernelDecomposition := by
  intro m n A
  classical
  obtain ⟨s, k, t, b, e, a, hsm, hsn, hne, hchain, _hb, _he, ⟨Q⟩, _⟩ :=
    D07.Ch16.Smith.smithDecomposition ℤ m n A.mulVecLin
  let d : Fin s → ℕ := fun i => (a i).natAbs
  have hd : ∀ i, 0 < d i := fun i => Int.natAbs_pos.mpr (hne i)
  have hdc : ∀ i j, i ≤ j → d i ∣ d j := fun i j hij =>
    Int.natAbs_dvd_natAbs.mpr (hchain i j hij)
  have ht : t = n - s := by omega
  subst t
  let Z : (∀ i : Fin s, ℤ ⧸ Ideal.span {a i}) ≃ₗ[ℤ]
      (∀ i : Fin s, ZMod (d i)) :=
    (AddEquiv.piCongrRight fun i => (Int.quotientSpanEquivZMod (a i)).toAddEquiv).toIntLinearEquiv
  let E := Q.trans ((LinearEquiv.refl ℤ (Fin (n - s) → ℤ)).prodCongr Z)
  obtain ⟨U, _hU⟩ := unitFactorDeletion s d
  refine ⟨s, d, ?_, ?_, hd, hdc, ⟨E⟩, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact ⟨E.trans ((LinearEquiv.refl ℤ _).prodCongr
      (DirectSum.linearEquivFunOnFintype ℤ (Fin s) (fun i => ZMod (d i))).symm)⟩
  · exact ⟨E.trans ((LinearEquiv.refl ℤ _).prodCongr U)⟩
  · intro h
    have hfin := finiteProductCard d hd
    have hz : n - s = 0 := by omega
    have : Finite ((Fin (n - s) → ℤ) × (∀ i, ZMod (d i))) := by
      simpa only [hz] using hfin.1
    constructor
    · exact Finite.of_equiv _ E.symm.toEquiv
    · rw [Nat.card_congr E.toEquiv]
      simpa only [hz] using hfin.2
  · intro h
    have := infiniteFreeProduct d (Nat.sub_pos_of_lt h)
    exact Infinite.of_injective E.symm E.symm.injective

end D07.Ch16.IntegerPresentationCokernel
