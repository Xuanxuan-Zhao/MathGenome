import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.MinorRank
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.RepresentationMinors
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace FiniteCombinatorics.Matroid
open Set Submodule
open scoped _root_.Matroid
universe u v w
variable {α : Type u} {K : Type v} [Field K]
variable {V : Type w} [AddCommGroup V] [Module K V]

/-- Killing U identifies the spans of W and U + W. -/
theorem quotient_span_image (U : Submodule K V) (v : α → V) (A : Set α) :
    span K ((fun e => U.mkQ (v e)) '' A) = (U ⊔ span K (v '' A)).map U.mkQ := by
  rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq,
    Submodule.map_span, Set.image_image]

/-- The quotient identification is the first isomorphism theorem for the
quotient map restricted to the finite span; it does not quotient all of V again. -/
theorem quotient_span_equiv (U : Submodule K V) (v : α → V) (A : Set α) :
    let S := U ⊔ span K (v '' A)
    ∃ e : (S ⧸ U.comap S.subtype) ≃ₗ[K]
        span K ((fun e => U.mkQ (v e)) '' A),
      ∀ x : S, (e (Submodule.Quotient.mk x) : V ⧸ U) = U.mkQ (x : V) := by
  let S := U ⊔ span K (v '' A)
  let f := U.mkQ.domRestrict S
  have hk : LinearMap.ker f = U.comap S.subtype := by
    simp [f, LinearMap.ker_domRestrict]
  have hr : LinearMap.range f = span K ((fun e => U.mkQ (v e)) '' A) := by
    rw [LinearMap.range_domRestrict]
    exact (quotient_span_image U v A).symm
  let e := (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))
  refine ⟨e, ?_⟩
  intro x
  change ((LinearEquiv.ofEq _ _ hr)
    (f.quotKerEquivRange (Submodule.Quotient.mk x)) : V ⧸ U) = _
  rw [LinearEquiv.coe_ofEq_apply, LinearMap.quotKerEquivRange_apply_mk]
  rfl

/-- Rank-nullity in U+W, where finiteness is available even if V is infinite. -/
theorem quotient_span_finrank (v : α → V) (C A : Set α)
    (hC : C.Finite) (hA : A.Finite) :
    (Module.finrank K (span K ((fun e => (span K (v '' C)).mkQ (v e)) '' A)) : ℤ) =
      (Module.finrank K (span K (v '' (A ∪ C))) : ℤ) -
      (Module.finrank K (span K (v '' C)) : ℤ) := by
  let U := span K (v '' C)
  let S := U ⊔ span K (v '' A)
  have hs : S = span K (v '' (A ∪ C)) := by
    simp [S, U, image_union, span_union, sup_comm]
  let : Module.Finite K S := by
    rw [hs]
    exact Module.Finite.span_of_finite K ((hA.union hC).image v)
  let f := U.mkQ.domRestrict S
  have hk : LinearMap.ker f = U.comap S.subtype := by
    simp [f, LinearMap.ker_domRestrict]
  have hr : LinearMap.range f = span K ((fun e => U.mkQ (v e)) '' A) := by
    rw [LinearMap.range_domRestrict]
    exact (quotient_span_image U v A).symm
  have hd := f.finrank_range_add_finrank_ker
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe (show U ≤ S from le_sup_left)).finrank_eq,
    hs] at hd
  have hdz :
      (Module.finrank K (span K ((fun e => U.mkQ (v e)) '' A)) : ℤ) +
        (Module.finrank K U : ℤ) =
        (Module.finrank K (span K (v '' (A ∪ C))) : ℤ) := by
    exact_mod_cast hd
  linarith

theorem deletionRepresents : Expected.deletionRepresents := by
  intro α K _ V _ _ M _ v hv C _ I
  rw [_root_.Matroid.delete_indep_iff, hv I]
  simp only [_root_.Matroid.delete_ground, subset_sdiff]
  tauto

theorem contractionQuotientSpan : Expected.contractionQuotientSpan := by
  intro α K _ V _ _ M _ v _ C _ A _
  exact quotient_span_image (span K (v '' C)) v A

theorem contractionQuotientEquiv : Expected.contractionQuotientEquiv := by
  intro α K _ V _ _ M _ v _ C _ A _
  exact quotient_span_equiv (span K (v '' C)) v A

theorem contractionQuotientDimension : Expected.contractionQuotientDimension := by
  intro α K _ V _ _ M _ v hv C hC A hA
  dsimp only
  rw [representsRank K M v hv (A ∪ C) (union_subset (hA.trans sdiff_subset) hC),
    representsRank K M v hv C hC]
  exact quotient_span_finrank v C A (M.ground_finite.subset hC)
    (M.ground_finite.subset (hA.trans sdiff_subset))

/-- The rank tests agree on the retained ground. No basis of C or independence
assumption on C is required. -/
theorem contractionRepresents : Expected.contractionRepresents := by
  intro α K _ V _ _ M _ v hv C hC
  let qv := fun e => (span K (v '' C)).mkQ (v e)
  let N := vectorMatroid K (M.E \ C) M.ground_finite.sdiff qv
  intro I
  by_cases hI : I ⊆ (M ／ C).E
  · have hN : rank N I = (Module.finrank K (span K (qv '' I)) : ℤ) :=
      vectorRank K (M.E \ C) M.ground_finite.sdiff qv I hI
    have hr : rank (M ／ C) I = rank N I := by
      rw [contractionRank M C I hC hI, hN]
      exact (contractionQuotientDimension K M v hv C hC I hI).symm
    have hi : (M ／ C).Indep I ↔ N.Indep I := by
      rw [← rankRecovery (M ／ C) I, ← rankRecovery N I]
      change (I ⊆ (M ／ C).E ∧ rank (M ／ C) I = _) ↔
        (I ⊆ N.E ∧ rank N I = _)
      rw [hr]
      rfl
    exact hi.trans (vectorIndep K (M.E \ C) M.ground_finite.sdiff qv I)
  · constructor
    · intro hi
      exact (hI hi.subset_ground).elim
    · intro hi
      exact (hI hi.1).elim

end FiniteCombinatorics.Matroid
