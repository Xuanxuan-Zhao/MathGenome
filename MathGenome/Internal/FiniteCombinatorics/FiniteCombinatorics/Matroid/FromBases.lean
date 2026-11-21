import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Foundation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.FromBases

/-! W64(2), from bases. Mathlib's finite basis constructor proves maximality
from exchange, using the equicardinality theorem for exchange families. We use
that constructor to establish augmentation, then use the shared canonical
construction `ofAugmentation` for the final matroid. No nonempty-ground
assumption is made. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u}

private theorem basisExchange {E : Set α} {B : Set (Set α)}
    (hB : BasisPresentation E B) : _root_.Matroid.ExchangeProperty (· ∈ B) :=
  fun D F hD hF e he => hB.2.2 D hD F hF e he

private def basisModel {E : Set α} (hE : E.Finite) {B : Set (Set α)}
    (hB : BasisPresentation E B) : _root_.Matroid α :=
  _root_.Matroid.ofIsBaseOfFinite hE (· ∈ B) hB.1 (basisExchange hB) hB.2.1

private theorem basisModel_indep {E : Set α} (hE : E.Finite) {B : Set (Set α)}
    (hB : BasisPresentation E B) (I : Set α) :
    (basisModel hE hB).Indep I ↔ BasisIndependent E B I := by
  change (∃ D ∈ B, I ⊆ D) ↔ I ⊆ E ∧ ∃ D ∈ B, I ⊆ D
  exact ⟨fun h => ⟨by obtain ⟨D, hD, hID⟩ := h; exact hID.trans (hB.2.1 D hD), h⟩,
    fun h => h.2⟩

/-- Equal cardinality follows from exchange; it is not an input hypothesis. -/
theorem basisPresentationEquicardinal (E : Set α) (hE : E.Finite)
    (B : Set (Set α)) (hB : BasisPresentation E B) :
    ∀ D ∈ B, ∀ F ∈ B, D.ncard = F.ncard := by
  intro D hD F hF
  have he := (basisExchange hB).encard_isBase_eq hD hF
  have hDfin := hE.subset (hB.2.1 D hD)
  have hFfin := hE.subset (hB.2.1 F hF)
  rw [← hDfin.cast_ncard_eq, ← hFfin.cast_ncard_eq] at he
  exact_mod_cast he

/-- The subsets of designated bases satisfy finite augmentation. -/
theorem basisPresentationAugmentation (E : Set α) (hE : E.Finite)
    (B : Set (Set α)) (hB : BasisPresentation E B)
    (I J : Set α) (hI : BasisIndependent E B I) (hJ : BasisIndependent E B J)
    (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J \ I, BasisIndependent E B (insert e I) := by
  have hi := (basisModel_indep hE hB I).2 hI
  have hj := (basisModel_indep hE hB J).2 hJ
  have henc : I.encard < J.encard := by
    rw [← (hE.subset hI.1).cast_ncard_eq, ← (hE.subset hJ.1).cast_ncard_eq]
    exact_mod_cast hcard
  obtain ⟨e, he, hie⟩ := hi.exists_insert_of_encard_lt hj henc
  exact ⟨e, he, (basisModel_indep hE hB _).1 hie⟩

private def basisSystem {E : Set α} (hE : E.Finite) {B : Set (Set α)}
    (hB : BasisPresentation E B) : IndependenceSystem E where
  finite_ground := hE
  Indep := BasisIndependent E B
  empty_indep := ⟨empty_subset E, by
    obtain ⟨D, hD⟩ := hB.1
    exact ⟨D, hD, empty_subset D⟩⟩
  hereditary := fun {_ _} hJ hIJ => ⟨hIJ.trans hJ.1, by
    obtain ⟨D, hD, hJD⟩ := hJ.2
    exact ⟨D, hD, hIJ.trans hJD⟩⟩
  subset_ground := fun {_} hI => hI.1

/-- Construct a finite matroid on the original ground, recovering precisely the
independent sets and the designated bases, including when the ground is empty. -/
theorem existsMatroidOfBases (E : Set α) (hE : E.Finite)
    (B : Set (Set α)) (hB : BasisPresentation E B) :
    ∃ M : _root_.Matroid α,
      M.E = E ∧ M.Finite ∧
      (∀ I, M.Indep I ↔ BasisIndependent E B I) ∧
      (∀ D, M.IsBase D ↔ D ∈ B) := by
  let S := basisSystem hE hB
  have haug : Augmentation S := fun {I J} hI hJ hc =>
    basisPresentationAugmentation E hE B hB I J hI hJ hc
  let M := ofAugmentation S haug
  have heq : M = basisModel hE hB := by
    apply _root_.Matroid.ext_indep (by rfl)
    intro I _
    exact (indepPreserved E S haug I).trans (basisModel_indep hE hB I).symm
  refine ⟨M, groundPreserved E S haug, finiteConstruction E S haug, ?_, ?_⟩
  · intro I
    exact indepPreserved E S haug I
  · intro D
    rw [heq]
    rfl

end FiniteCombinatorics.Matroid
