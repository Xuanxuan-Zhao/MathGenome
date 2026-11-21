import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ForwardPresentations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.TutteDefinition

namespace FiniteCombinatorics.Matroid
open Set
universe u v w

/-- The nonnegative rank deficit in the x exponent. -/
noncomputable def rankDeficit {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (A : Set α) : ℕ :=
  (M.eRk M.E).toNat - (M.eRk A).toNat

/-- The nonnegative cardinality deficit in the y exponent, on subsets of E. -/
noncomputable def rankNullity {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (A : Set α) : ℕ :=
  A.ncard - (M.eRk A).toNat

/-- Sum over exactly all subsets of the finite ground, including ∅. -/
noncomputable def tutte {α : Type u} (M : _root_.Matroid α) [M.Finite] :
    TuttePolynomial := by
  classical
  exact ∑ A ∈ M.ground_finite.toFinset.powerset,
    (MvPolynomial.X 0 - 1) ^ rankDeficit M (A : Set α) *
    (MvPolynomial.X 1 - 1) ^ rankNullity M (A : Set α)

/-- Simultaneous substitution, also into other commutative rings (e.g. ℤ[t]). -/
noncomputable def tutteSubstitute {R : Type w} [CommRing R]
    (P : TuttePolynomial) (x y : R) : R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => if i = 0 then x else y) P

/-- Integer evaluation of the Tutte polynomial. -/
noncomputable def tutteEvaluate {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (x y : ℤ) : ℤ := tutteSubstitute (tutte M) x y

/-- The canonical Mathlib direct sum, with two disjoint indexed ground sets. -/
def directSum {α : Type u} {β : Type v} (M : _root_.Matroid α)
    (N : _root_.Matroid β) : _root_.Matroid (α ⊕ β) := M.sum N

instance directSumFinite {α : Type u} {β : Type v}
    (M : _root_.Matroid α) (N : _root_.Matroid β) [M.Finite] [N.Finite] :
    (directSum M N).Finite := by
  constructor
  rw [directSum, _root_.Matroid.sum_ground]
  exact (M.ground_finite.image Sum.inl).union (N.ground_finite.image Sum.inr)

/-- The natural exponent represents actual subtraction in the shared integer rank. -/
theorem rankDeficitCast {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (A : Set α) (hA : A ⊆ M.E) :
    (rankDeficit M A : ℤ) = rank M M.E - rank M A := by
  have h : (M.eRk A).toNat ≤ (M.eRk M.E).toNat := by
    have hi := rankMonotone M A M.E hA Subset.rfl
    unfold rank at hi
    exact_mod_cast hi
  simp only [rankDeficit, Nat.cast_sub h, rank]

theorem rankNullityCast {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (A : Set α) (hA : A ⊆ M.E) :
    (rankNullity M A : ℤ) = (A.ncard : ℤ) - rank M A := by
  have h : (M.eRk A).toNat ≤ A.ncard := by
    have hi := (rankBounds M A hA).2
    unfold rank at hi
    exact_mod_cast hi
  simp only [rankNullity, Nat.cast_sub h, rank]

theorem tutteEmpty {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (hE : M.E = ∅) : tutte M = 1 := by
  classical
  simp [tutte, rankDeficit, rankNullity, hE]

theorem tutteSubstituteVariables {R : Type w} [CommRing R] (x y : R) :
    tutteSubstitute (MvPolynomial.X 0) x y = x ∧
    tutteSubstitute (MvPolynomial.X 1) x y = y := by
  simp [tutteSubstitute]

theorem tutteSubstituteSum {α : Type u} {R : Type w} [CommRing R]
    (M : _root_.Matroid α) [M.Finite] (x y : R) :
    tutteSubstitute (tutte M) x y =
      ∑ A ∈ M.ground_finite.toFinset.powerset,
        (x - 1) ^ rankDeficit M (A : Set α) * (y - 1) ^ rankNullity M (A : Set α) := by
  classical
  simp [tutteSubstitute, tutte, map_sum, map_mul, map_pow, map_sub]

theorem directSumGround {α : Type u} {β : Type v}
    (M : _root_.Matroid α) (N : _root_.Matroid β) :
    (directSum M N).E = Sum.inl '' M.E ∪ Sum.inr '' N.E :=
  _root_.Matroid.sum_ground M N

theorem directSumGroundDisjoint {α : Type u} {β : Type v}
    (M : _root_.Matroid α) (N : _root_.Matroid β) :
    Disjoint (Sum.inl '' M.E : Set (α ⊕ β)) (Sum.inr '' N.E) :=
  Set.disjoint_image_inl_image_inr

theorem directSumIndep {α : Type u} {β : Type v}
    (M : _root_.Matroid α) (N : _root_.Matroid β) (I : Set (α ⊕ β)) :
    (directSum M N).Indep I ↔ M.Indep (Sum.inl ⁻¹' I) ∧ N.Indep (Sum.inr ⁻¹' I) :=
  _root_.Matroid.sum_indep_iff M N

/-- Split a basis into its two components; its size and hence rank add. -/
theorem directSumRank {α : Type u} {β : Type v}
    (M : _root_.Matroid α) (N : _root_.Matroid β) [M.Finite] [N.Finite]
    (A : Set (α ⊕ β)) (hA : A ⊆ (directSum M N).E) :
    rank (directSum M N) A = rank M (Sum.inl ⁻¹' A) + rank N (Sum.inr ⁻¹' A) := by
  obtain ⟨B, hB⟩ := (directSum M N).exists_isBasis A hA
  have hb := _root_.Matroid.sum_isBasis_iff.mp hB
  have hl := hb.1.indep.finite
  have hr := hb.2.indep.finite
  have hc : B.ncard = (Sum.inl ⁻¹' B).ncard + (Sum.inr ⁻¹' B).ncard := by
    calc B.ncard = (Sum.inl '' (Sum.inl ⁻¹' B) ∪ Sum.inr '' (Sum.inr ⁻¹' B)).ncard :=
          congrArg Set.ncard (Set.image_preimage_inl_union_image_preimage_inr B).symm
         _ = (Sum.inl '' (Sum.inl ⁻¹' B)).ncard + (Sum.inr '' (Sum.inr ⁻¹' B)).ncard :=
          Set.ncard_union_eq Set.disjoint_image_inl_image_inr (hl.image _) (hr.image _)
         _ = _ := by rw [Set.ncard_image_of_injective _ Sum.inl_injective,
                        Set.ncard_image_of_injective _ Sum.inr_injective]
  rw [← basisCardinality _ B A hB, ← basisCardinality _ _ _ hb.1,
    ← basisCardinality _ _ _ hb.2, hc, Nat.cast_add]

end FiniteCombinatorics.Matroid
