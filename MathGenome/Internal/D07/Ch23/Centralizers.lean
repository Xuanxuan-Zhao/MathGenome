import MathGenome.Internal.Specs.D07.Ch23.Centralizers
import MathGenome.Internal.D07.Ch23.CentralizersFiniteDivisionCoordinates

/-! Centers and centralizers in arbitrary division rings, and unital subrings
of finite division rings. The finite inverse argument uses injective left
multiplication on the subring; it assumes no commutativity. -/

universe u v

namespace D07.Ch23.Centralizers

open Specs.D07.Ch23.Centralizers

theorem centerCarrier : CenterCarrier.{u} := by
  intro D _
  ext a
  change a ∈ Subring.center D ↔ ∀ x : D, a * x = x * a
  rw [Subring.mem_center_iff]
  exact forall_congr' fun x => eq_comm

theorem centralizerCarrier : CentralizerCarrier.{u} := by
  intro D _ x
  ext a
  change a ∈ Subring.centralizer ({x} : Set D) ↔ a * x = x * a
  rw [Subring.mem_centralizer_iff]
  constructor
  · intro h
    exact (h x (Set.mem_singleton x)).symm
  · intro h y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact h.symm

theorem commutingInverse : CommutingInverse.{u} := by
  intro D _ a x h
  exact (show Commute a x from h).inv_left₀

theorem centerDivisionSubring : CenterDivisionSubring.{u} := by
  intro D _
  refine ⟨(Subring.center D).toSubfield ?_, rfl⟩
  intro a ha
  apply Subring.mem_center_iff.mpr
  intro x
  exact (commutingInverse D a x ((Subring.mem_center_iff.mp ha x).symm)).symm

theorem centralizerDivisionSubring : CentralizerDivisionSubring.{u} := by
  intro D _ x
  refine ⟨(Subring.centralizer ({x} : Set D)).toSubfield ?_, rfl⟩
  intro a ha
  apply Subring.mem_centralizer_iff.mpr
  intro y hy
  exact (commutingInverse D a y ((Subring.mem_centralizer_iff.mp ha y hy).symm)).symm

theorem centerCommutative : CenterCommutative.{u} := by
  intro D _ a b
  exact mul_comm a b

theorem centerField : CenterField.{u} := by
  intro D _
  exact ⟨inferInstance, rfl⟩

theorem finiteSubringInverseClosed : FiniteSubringInverseClosed.{u} := by
  intro D _ _ S a ha
  classical
  by_cases h0 : a = 0
  · simpa only [h0, inv_zero] using S.zero_mem
  let f : S → S := fun b => ⟨a * b, S.mul_mem ha b.property⟩
  have hf : Function.Injective f := by
    intro b c h
    apply Subtype.ext
    exact mul_left_cancel₀ h0 (congrArg Subtype.val h)
  obtain ⟨b, hb⟩ := (Finite.surjective_of_injective hf) (1 : S)
  have hab : a * (b : D) = 1 := congrArg Subtype.val hb
  have hb_inv : (b : D) = a⁻¹ := by
    calc
      (b : D) = a⁻¹ * (a * (b : D)) := by rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
      _ = a⁻¹ := by rw [hab, mul_one]
  exact hb_inv ▸ b.property

theorem finiteSubringDivisionSubring : FiniteSubringDivisionSubring.{u} := by
  intro D _ _ S
  exact ⟨S.toSubfield (finiteSubringInverseClosed D S), rfl⟩

theorem finiteSubringDivisionRing : FiniteSubringDivisionRing.{u} := by
  intro D _ _ S
  let E : Subfield D := S.toSubfield (finiteSubringInverseClosed D S)
  exact ⟨E.toDivisionRing, rfl⟩

theorem leftBasisAndCounting : LeftBasisAndCounting.{u} :=
  CentralizersFiniteDivisionCoordinates.leftBasisAndCounting

theorem centralDimensions : CentralDimensions.{u, v} :=
  CentralizersFiniteDivisionCoordinates.centralDimensions

end D07.Ch23.Centralizers
