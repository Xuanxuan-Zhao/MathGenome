import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.Presentation
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanFreeness
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWOrdered
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Module

/-!
The tensor-word representation detects the Cartan space and the negative
free Lie algebra. The presentation's interchange gives the positive side.
-/

namespace LieNotes.Contragredient.Presentation

open Module
open scoped Classical

noncomputable section

universe u v w

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H]

private abbrev WordSpace (I : Type u) := MonoidAlgebra ℂ (FreeMonoid I)

private def wordBasis : Basis (List I) ℂ (WordSpace I) :=
  (MonoidAlgebra.basis (FreeMonoid I) ℂ).reindex FreeMonoid.toList

private abbrev word (w : List I) : WordSpace I := wordBasis w

private def prepend (i : I) : Module.End ℂ (WordSpace I) :=
  Algebra.lmul ℂ (WordSpace I) (MonoidAlgebra.of ℂ (FreeMonoid I) (FreeMonoid.of i))

@[simp] private theorem prefix_word (i : I) (w : List I) :
    prepend i (word w) = word (i :: w) := by
  simp [prepend, word, wordBasis, MonoidAlgebra.of_apply, FreeMonoid.ofList_cons]

private theorem word_nil : word ([] : List I) = 1 := by
  simp [word, wordBasis, MonoidAlgebra.one_def]

variable [Finite I]

private def wordWeight (R : Realization A H) : List I → Module.Dual ℂ H
  | [] => 0
  | i :: w => R.α i + wordWeight R w

private def diagonal (R : Realization A H) (μ : Module.Dual ℂ H) :
    H →ₗ[ℂ] Module.End ℂ (WordSpace I) where
  toFun h := wordBasis.constr ℂ (fun w => (μ - wordWeight R w) h • word w)
  map_add' h k := by
    apply wordBasis.ext
    intro w
    simp only [Basis.constr_basis, LinearMap.add_apply, map_add, add_smul]
  map_smul' c h := by
    apply wordBasis.ext
    intro w
    simp [Basis.constr_basis, mul_smul]

@[simp] private theorem diagonal_word (R : Realization A H) (μ : Module.Dual ℂ H)
    (h : H) (w : List I) :
    diagonal R μ h (word w) = (μ - wordWeight R w) h • word w :=
  wordBasis.constr_basis ℂ _ _

/-- The raising operator kills the vacuum and acts recursively on a prefixed word. -/
private def raiseWord (R : Realization A H) (μ : Module.Dual ℂ H) (i : I) :
    List I → WordSpace I
  | [] => 0
  | j :: w => prepend j (raiseWord R μ i w) +
      if i = j then diagonal R μ (R.h i) (word w) else 0

private def raise (R : Realization A H) (μ : Module.Dual ℂ H) (i : I) :
    Module.End ℂ (WordSpace I) :=
  wordBasis.constr ℂ (raiseWord R μ i)

@[simp] private theorem raise_word (R : Realization A H) (μ : Module.Dual ℂ H)
    (i : I) (w : List I) :
    raise R μ i (word w) = raiseWord R μ i w :=
  wordBasis.constr_basis ℂ _ _

private theorem diagonal_prefix (R : Realization A H) (μ : Module.Dual ℂ H) (h : H) (i : I) :
    diagonal R μ h * prepend i = prepend i * diagonal R μ h - R.α i h • prepend i := by
  apply wordBasis.ext
  intro w
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, prefix_word,
    diagonal_word, map_smul, wordWeight, LinearMap.sub_apply, LinearMap.add_apply]
  module

/-- Every term of the raised word has weight shifted by the same simple root. -/
private theorem diagonal_raiseWord (R : Realization A H) (μ : Module.Dual ℂ H)
    (h : H) (i : I) (w : List I) :
    diagonal R μ h (raiseWord R μ i w) =
      ((μ - wordWeight R w) h + R.α i h) • raiseWord R μ i w := by
  induction w with
  | nil => simp [raiseWord]
  | cons j w ih =>
    have shift (x : WordSpace I) :
        diagonal R μ h (prepend j x) =
          prepend j (diagonal R μ h x) - R.α j h • prepend j x :=
      LinearMap.congr_fun (diagonal_prefix R μ h j) x
    simp only [raiseWord, map_add, shift, ih, map_smul, wordWeight, LinearMap.sub_apply,
      LinearMap.add_apply]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, diagonal_word, map_smul, smul_add, LinearMap.sub_apply]
      module
    · simp only [ite_eq_right hij, map_zero, add_zero]
      module

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem wordRelations (R : Realization A H) (μ : Module.Dual ℂ H) :
    Relations R (diagonal R μ) (raise R μ) prepend := by
  constructor
  · intro h k
    change diagonal R μ h * diagonal R μ k - diagonal R μ k * diagonal R μ h = 0
    apply wordBasis.ext
    intro w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply,
      diagonal_word, map_smul, smul_smul, mul_comm, sub_self]
  · intro h i
    change diagonal R μ h * raise R μ i - raise R μ i * diagonal R μ h = _
    apply wordBasis.ext
    intro w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, raise_word,
      diagonal_word, map_smul, diagonal_raiseWord]
    module
  · intro h i
    change diagonal R μ h * prepend i - prepend i * diagonal R μ h = _
    rw [diagonal_prefix]
    abel
  · intro i j
    change raise R μ i * prepend j - prepend j * raise R μ i = _
    apply wordBasis.ext
    intro w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, prefix_word, raise_word, raiseWord]
    split <;> simp_all

private def wordAction (R : Realization A H) (μ : Module.Dual ℂ H) :
    Algebra R →ₗ⁅ℂ⁆ Module.End ℂ (WordSpace I) :=
  lift R (diagonal R μ) (raise R μ) prepend (wordRelations R μ)

/-- The given map from the full Cartan space to the presented algebra is injective. -/
theorem cartan_injective (R : Realization A H) : Function.Injective (cartan R) := by
  refine (injective_iff_map_eq_zero (cartan R)).mpr ?_
  intro h hh
  apply (Module.forall_dual_apply_eq_zero_iff ℂ h).mp
  intro μ
  have hμ := congrArg (fun x => wordAction R μ x (word [])) hh
  change lift R (diagonal R μ) (raise R μ) prepend _ (cartan R h) (word []) =
    wordAction R μ 0 (word []) at hμ
  rw [lift_cartan, diagonal_word, wordWeight, sub_zero, word_nil, map_zero,
    LinearMap.zero_apply] at hμ
  exact (smul_eq_zero.mp hμ).resolve_right one_ne_zero

private def freeLieToAssociative : FreeLieAlgebra ℂ I →ₗ⁅ℂ⁆ FreeAlgebra ℂ I :=
  FreeLieAlgebra.lift ℂ (FreeAlgebra.ι ℂ)

omit [Finite I] in
private theorem freeLieToAssociative_injective :
    Function.Injective (freeLieToAssociative (I := I)) := by
  let : LinearOrder (Basis.ofVectorSpaceIndex ℂ (FreeLieAlgebra ℂ I)) :=
    IsWellOrder.linearOrder WellOrderingRel
  have hPBW := Shared.Lie.PBW.inclusionInjective_spec ℂ (FreeLieAlgebra ℂ I)
    (Basis.ofVectorSpaceIndex ℂ (FreeLieAlgebra ℂ I))
    (Basis.ofVectorSpace ℂ (FreeLieAlgebra ℂ I))
  intro x y hxy
  apply hPBW
  apply (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℂ I).injective
  simpa [FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra, freeLieToAssociative,
    Shared.Lie.inclusion, Shared.Lie.canonicalLieMap] using hxy

private theorem negativeLift_injective (R : Realization A H) :
    Function.Injective (FreeLieAlgebra.lift ℂ (f R)) := by
  -- The negative generators act by left multiplication on words.
  let assocAction : FreeAlgebra ℂ I →ₐ[ℂ] Module.End ℂ (WordSpace I) :=
    (Algebra.lmul ℂ (WordSpace I)).comp FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom
  have hAction :
      (wordAction R 0).comp (FreeLieAlgebra.lift ℂ (f R)) =
        assocAction.toLieHom.comp freeLieToAssociative := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp [wordAction, assocAction, freeLieToAssociative, prepend,
      FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  have hinj : Function.Injective (assocAction.toLieHom.comp freeLieToAssociative) :=
    (Algebra.lmul_injective.comp
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective).comp freeLieToAssociative_injective
  intro x y hxy
  apply hinj
  rw [← hAction, LieHom.comp_apply, LieHom.comp_apply, hxy]

private theorem positiveLift_injective (R : Realization A H) :
    Function.Injective (FreeLieAlgebra.lift ℂ (e R)) := by
  have h : (involution R).toLieHom.comp (FreeLieAlgebra.lift ℂ (e R)) =
      FreeLieAlgebra.lift ℂ (f R) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp
  intro x y hxy
  apply negativeLift_injective R
  rw [← h, LieHom.comp_apply, LieHom.comp_apply, hxy]

private def freeSideLift {L : Type w} [LieRing L] [LieAlgebra ℂ L] (g : I → L) :
    FreeLieAlgebra ℂ I →ₗ⁅ℂ⁆ LieSubalgebra.lieSpan ℂ L (Set.range g) :=
  FreeLieAlgebra.lift ℂ (fun i => ⟨g i, LieSubalgebra.subset_lieSpan (Set.mem_range_self i)⟩)

private def freeSideEquiv {L : Type w} [LieRing L] [LieAlgebra ℂ L] (g : I → L)
    (hg : Function.Injective (FreeLieAlgebra.lift ℂ g)) :
    FreeLieAlgebra ℂ I ≃ₗ⁅ℂ⁆ LieSubalgebra.lieSpan ℂ L (Set.range g) := by
  let S := LieSubalgebra.lieSpan ℂ L (Set.range g)
  have hcomp : S.incl.comp (freeSideLift g) = FreeLieAlgebra.lift ℂ g := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp [freeSideLift]
  refine LieEquiv.ofBijective (freeSideLift g) ⟨?_, ?_⟩
  · intro x y hxy
    apply hg
    rw [← hcomp, LieHom.comp_apply, LieHom.comp_apply, hxy]
  · have hle : S ≤ (FreeLieAlgebra.lift ℂ g).range := by
      apply LieSubalgebra.lieSpan_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨FreeLieAlgebra.of ℂ i, FreeLieAlgebra.lift_of_apply g i⟩
    intro x
    obtain ⟨y, hy⟩ := hle x.property
    refine ⟨y, Subtype.ext ?_⟩
    exact (LieHom.congr_fun hcomp y).trans hy

/-- The canonical identification of the free Lie algebra with the negative side. -/
def negativeFree (R : Realization A H) : FreeLieAlgebra ℂ I ≃ₗ⁅ℂ⁆ negative R :=
  freeSideEquiv (f R) (negativeLift_injective R)

/-- The canonical identification of the free Lie algebra with the positive side. -/
def positiveFree (R : Realization A H) : FreeLieAlgebra ℂ I ≃ₗ⁅ℂ⁆ positive R :=
  freeSideEquiv (e R) (positiveLift_injective R)

@[simp] theorem negativeFree_of (R : Realization A H) (i : I) :
    (negativeFree R (FreeLieAlgebra.of ℂ i) : Algebra R) = f R i := by
  change ((freeSideLift (f R) (FreeLieAlgebra.of ℂ i)) : Algebra R) = f R i
  simp [freeSideLift]

@[simp] theorem positiveFree_of (R : Realization A H) (i : I) :
    (positiveFree R (FreeLieAlgebra.of ℂ i) : Algebra R) = e R i := by
  change ((freeSideLift (e R) (FreeLieAlgebra.of ℂ i)) : Algebra R) = e R i
  simp [freeSideLift]

theorem negative_isFree (R : Realization A H) :
    ∃ ψ : FreeLieAlgebra ℂ I ≃ₗ⁅ℂ⁆ negative R,
      ∀ i, (ψ (FreeLieAlgebra.of ℂ i) : Algebra R) = f R i :=
  ⟨negativeFree R, negativeFree_of R⟩

theorem positive_isFree (R : Realization A H) :
    ∃ ψ : FreeLieAlgebra ℂ I ≃ₗ⁅ℂ⁆ positive R,
      ∀ i, (ψ (FreeLieAlgebra.of ℂ i) : Algebra R) = e R i :=
  ⟨positiveFree R, positiveFree_of R⟩

end

end LieNotes.Contragredient.Presentation
