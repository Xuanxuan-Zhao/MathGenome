import Specs.LinearAlgebraicGroups.Reductive.CocharacterDynamics
import LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.DiagonalizableGroups (IntegerCharacters diagonalGroup)
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private conjugationAction isFixedBy_conjugation_iff
  from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private group_geometricallyIrreducible
  from LinearAlgebraicGroups.Reductive.CocharacterOpenCell

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private instance : Group.FG Specs.DiagonalizableGroups.IntegerCharacters.{u} :=
  let e : Multiplicative ℤ ≃* Specs.DiagonalizableGroups.IntegerCharacters.{u} := MulEquiv.ulift.symm
  Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

theorem smoothCocharacterCentralizer :
    Specs.CocharacterDynamics.SmoothCocharacterCentralizer.{u} := by
  intro k _ G _ cochar C hC
  let := G.property.1
  refine DiagonalizableFixedLocus.affineFixedLocusSmooth
    (M := Specs.DiagonalizableGroups.IntegerCharacters)
    G.val.X (conjugationAction cochar) C.group.X C.inclusion.hom.hom C.isClosedImmersion ?_
  intro S g
  exact (isFixedBy_conjugation_iff cochar g).trans (hC S g)

theorem centralizerLieInvariants : Specs.CocharacterDynamics.CentralizerLieInvariants.{u} := by
  intro k _ G H i C hC
  let := mono_over C.inclusion.hom.hom C.isClosedImmersion
  ext v
  change (∃ w, mapPointKernel C.inclusion w = v) ↔
    IsFixedBy (conjugationAction i).smul v.toMul.val
  rw [isFixedBy_conjugation_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact (hC _ _).mpr ⟨w.toMul.val, rfl⟩
  · intro hv
    obtain ⟨w, hw⟩ := (hC _ _).mp hv
    have hw1 : reduceTangentPoints C.group w = 1 := by
      apply (cancel_mono C.inclusion.hom.hom).mp
      change (((testSpec k).map (dualReduction k).op ≫ w) ≫ C.inclusion.hom.hom) =
        (1 : Points C.group.X (CommAlgCat.of k k)) ≫ C.inclusion.hom.hom
      rw [Category.assoc, hw, MonObj.one_comp]
      exact v.toMul.property
    refine ⟨⟨w, hw1⟩, ?_⟩
    exact Subtype.ext hw

theorem torusCentralizer : Specs.CocharacterDynamics.TorusCentralizer.{u} := by
  intro k _ G _ _ S hS
  obtain ⟨C, hC, hs, hg⟩ := connectedTorusCentralizer G S hS
  exact ⟨C, hC, hs, hg, centralizerLieInvariants S.inclusion C hC⟩

/-- Centralization can be tested after precomposing with a faithfully flat cover. -/
private theorem centralizes_comp_iff {A B G : GroupScheme k} (p : A ⟶ B) (i : B ⟶ G)
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left] {T : SchemeOver k} (g : T ⟶ G.X) :
    Centralizes (p ≫ i) g ↔ Centralizes i g := by
  let q : A.X ⊗ T ⟶ B.X ⊗ T := lift (fst A.X T ≫ p.hom.hom) (snd A.X T)
  have hfst : q ≫ fst B.X T = fst A.X T ≫ p.hom.hom := lift_fst _ _
  have hsnd : q ≫ snd B.X T = snd A.X T := lift_snd _ _
  have square : IsPullback (fst A.X T) q p.hom.hom (fst B.X T) := by
    apply IsPullback.mk' hfst.symm
    · intro W m n hmn₁ hmn₂
      apply CartesianMonoidalCategory.hom_ext
      · exact hmn₁
      · simpa only [Category.assoc, hsnd] using congrArg (· ≫ snd B.X T) hmn₂
    · intro W a b h
      refine ⟨lift a (b ≫ snd B.X T), lift_fst _ _, ?_⟩
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, hfst, ← Category.assoc, lift_fst, h]
      · rw [Category.assoc, hsnd, lift_snd]
  have underlying := square.map (Over.forget (Spec (CommRingCat.of k)))
  have : Flat q.left := MorphismProperty.of_isPullback underlying (inferInstance : Flat p.hom.hom.left)
  have : Surjective q.left :=
    MorphismProperty.of_isPullback underlying (inferInstance : Surjective p.hom.hom.left)
  have hEpi : Epi q.left := Flat.epi_of_flat_of_surjective _
  have : Epi q := (Over.forget (Spec (CommRingCat.of k))).epi_of_epi_map (f := q) hEpi
  have hconj : q ≫ conjugateFamily i g = conjugateFamily (p ≫ i) g := by
    change q ≫ ((snd B.X T ≫ g) * (fst B.X T ≫ i.hom.hom) * (snd B.X T ≫ g)⁻¹) =
      (snd A.X T ≫ g) * (fst A.X T ≫ p.hom.hom ≫ i.hom.hom) * (snd A.X T ≫ g)⁻¹
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hfst, hsnd]
  have hproj : q ≫ fst B.X T ≫ i.hom.hom = fst A.X T ≫ (p ≫ i).hom.hom := by
    rw [← Category.assoc, hfst, Category.assoc]
    rfl
  unfold Centralizes
  rw [← hconj, ← hproj, cancel_epi]

theorem cocharacterDynamics : Specs.CocharacterDynamics.Dynamics.{u} := by
  intro k _ G _ _ cochar
  obtain ⟨D⟩ := existsLimitDecomposition G cochar
  obtain ⟨Dneg⟩ := existsLimitDecomposition G (oppositeCocharacter cochar)
  obtain ⟨hPs, hUs, hZs⟩ := limitSubgroupsSmooth G cochar D
  obtain ⟨hPc, hUc, hZc⟩ := geometricallyConnectedLimitSubgroups G cochar D
  have hUnc := (geometricallyConnectedLimitSubgroups G (oppositeCocharacter cochar) Dneg).2.1
  let m := bigCellMap D Dneg
  have hOpen : IsOpenImmersion m.left := bigCell G cochar D Dneg
  have hCell : GeometricallyConnected
      (Dneg.contracting.group.X ⊗ (D.centralizer.group.X ⊗ D.contracting.group.X)).hom := by
    have := group_geometricallyIrreducible G
    let e := lift (η[Dneg.contracting.group.X])
      (lift (η[D.centralizer.group.X]) (η[D.contracting.group.X]))
    have : Surjective (m.left ≫ G.val.X.hom) :=
      ⟨fun _ ↦ ⟨e.left (IsLocalRing.closedPoint k), Subsingleton.elim _ _⟩⟩
    rw [← Over.w m]
    have hi : GeometricallyIrreducible (m.left ≫ G.val.X.hom) := inferInstance
    refine ⟨fun K _ z T a b square ↦ ?_⟩
    have := hi.geometrically_irreducibleSpace z a b square
    infer_instance
  refine ⟨D, Dneg, hPs, hUs, hZs, hPc, hUc, hZc, hUnc, contractingSubgroupUnipotent G cochar D,
    ⟨identityLieStructure G⟩, fun s ↦ lieWeights G cochar D s, hOpen, hCell, ?_⟩
  obtain ⟨I, p, i, hfactor, himage, _⟩ :=
    schemeImageFactorization (diagonalGroup k IntegerCharacters) G cochar
  let : Flat p.hom.hom.left := hfactor.2.1
  let : Surjective p.hom.hom.left := hfactor.2.2.1
  refine ⟨I, p, i, hfactor, himage, fun T g ↦ ?_⟩
  change Centralizes i g ↔ _
  rw [← centralizes_comp_iff p i g, hfactor.1]
  exact D.centralizer_points T g

end
end LinearAlgebraicGroups.CocharacterDynamics
