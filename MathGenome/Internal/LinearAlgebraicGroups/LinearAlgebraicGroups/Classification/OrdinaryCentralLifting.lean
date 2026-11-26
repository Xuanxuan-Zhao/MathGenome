import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.OrdinaryCentralLifting
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.TransportedRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CellHomomorphism
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Classification.OrdinaryCentralLifting

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CellHomomorphism (pullbackCharacters)
open Specs.CharacterDescent (Character compositionPairing)
open Specs.CharacterPairing (pairing)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.Pinning (AttachedDatum IsSimple PinnedGroup SplitBorelPair)
open Specs.RankTwoLifting (Compatible)
open Specs.RootGroups (AdditiveLine)

open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private integerHomEquiv specIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private split_character_presentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre

variable {k : Type u} [Field k] {A : AdditiveLine k}

private theorem torusMapOfCharacters {T S : GroupScheme k}
    (hT : IsSplitTorus T) (hS : IsSplitTorus S) (h : Character S →* Character T) :
    ∃ τ : T ⟶ S, pullbackCharacters τ = h ∧ (Function.Bijective h → IsIso τ) := by
  obtain ⟨_, e, he⟩ := split_character_presentation hT
  obtain ⟨_, g, hg⟩ := split_character_presentation hS
  let j := specGroupMap (groupAlgebraMap k h)
  refine ⟨e.inv ≫ j ≫ g.hom, ?_, ?_⟩
  · apply MonoidHom.ext
    intro χ
    change (e.inv ≫ j ≫ g.hom) ≫ χ = h χ
    apply (cancel_epi e.hom).mp
    have hc : h.comp (integerHomEquiv (Character S) χ) =
        integerHomEquiv (Character T) (h χ) := by
      apply MonoidHom.ext
      intro z
      exact map_zpow h χ z.down.toAdd
    have hm : groupAlgebraMap k (integerHomEquiv (Character S) χ) ≫ groupAlgebraMap k h =
        groupAlgebraMap k (integerHomEquiv (Character T) (h χ)) := by
      apply CommHopfAlgCat.hom_ext
      change (MonoidAlgebra.mapDomainBialgHom k h).comp
        (MonoidAlgebra.mapDomainBialgHom k (integerHomEquiv (Character S) χ)) = _
      rw [← MonoidAlgebra.mapDomainBialgHom_comp, hc]
      rfl
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hg χ, he (h χ), j]
    rw [← specGroupMap_comp, hm]
  · intro hb
    let b : Character S ≃* Character T := MulEquiv.ofBijective h hb
    let i : specGroup (groupAlgebra k (Character T)) ≅
        specGroup (groupAlgebra k (Character S)) :=
      specIso (MonoidAlgebra.domCongrBialgEquiv k k b)
    have hi : i.hom = j := rfl
    simpa only [Iso.trans_hom, Iso.symm_hom, hi, Category.assoc] using
      (e.symm ≪≫ i ≪≫ g).isIso_hom

private theorem basePos_iff_borelRoots {P : SplitBorelPair k} (D : AttachedDatum P) :
    letI := D.comm
    ∀ α, D.base.IsPos α ↔ α ∈ subgroupRoots P.T P.B := by
  let _ := D.comm
  let _ := D.datum.finiteRoots
  let _ := D.datum.freeCharacters
  let _ := D.datum.finiteCharacters
  let _ := D.datum.reduced
  obtain ⟨c, _, hregular, _, hc⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  let l := Specs.SimpleRoots.evaluate D.datum c
  have hval (α : Root P.T) : l (D.datum.rootDatum.root α) = pairing P.T.group α.val c := by
    change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root α) (Additive.ofMul c) = _
    rw [D.datum.root_eq, D.datum.pairing_eq]
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor D.datum.rootDatum l
    (fun α => hval α ▸ hregular α)
  have hroots : Specs.SimpleRoots.positive D.datum.rootDatum l = subgroupRoots P.T P.B := by
    rw [hc]
    ext α
    change 0 < l (D.datum.rootDatum.root α) ↔ 0 < pairing P.T.group α.val c
    rw [hval]
  -- Both bases have as support the indecomposable positive roots of the Borel.
  have hsupport : b.support = D.base.support := by
    ext α
    rw [hb.simple_iff, D.simple_iff, hroots]
    simp only [D.datum.root_eq, IsSimple]
    rfl
  have equalOfSupport (b₁ b₂ : D.datum.rootDatum.Base) (h : b₁.support = b₂.support) : b₁ = b₂ := by
    cases b₁
    cases b₂
    cases h
    rfl
  intro α
  rw [← equalOfSupport b D.base hsupport, hb.positive_iff, hroots]

private theorem positiveOfBaseComparison {P Q : SplitBorelPair k}
    (D : AttachedDatum P) (E : AttachedDatum Q) (d : Root P.T ≃ Root Q.T) :
    letI := D.comm
    letI := E.comm
    (∀ α, α ∈ D.base.support → d α ∈ E.base.support) →
    (∀ α β j, D.datum.rootDatum.root j = D.datum.rootDatum.root α + D.datum.rootDatum.root β →
      E.datum.rootDatum.root (d j) = E.datum.rootDatum.root (d α) + E.datum.rootDatum.root (d β)) →
    ∀ α, D.base.IsPos α → E.base.IsPos (d α) := by
  let _ := D.comm
  let _ := E.comm
  let _ := D.datum.finiteRoots
  let _ := E.datum.finiteRoots
  intro hbase hsum α hα
  refine hα.induction_on_add (p := fun β => E.base.IsPos (d β)) ?_ ?_
  · exact fun β hβ => E.base.isPos_of_mem_support (hbase β hβ)
  · exact fun β j i he hβ hj =>
      hβ.add (E.base.isPos_of_mem_support (hbase j hj)) (hsum β j i he)

private theorem positiveComparison {P Q : PinnedGroup A}
    {D : AttachedDatum P.pair} {E : AttachedDatum Q.pair} {d : Root P.pair.T ≃ Root Q.pair.T}
    {τ : P.pair.T.group ⟶ Q.pair.T.group} (h : Compatible P Q D E d τ) :
    letI := D.comm
    letI := E.comm
    ∀ α, D.base.IsPos α ↔ E.base.IsPos (d α) := by
  let _ := D.comm
  let _ := E.comm
  let l := (pullbackCharacters τ).toAdditive.toIntLinearMap
  have hinj : Function.Injective l := h.injective
  have hr (α : Root P.pair.T) : l (E.datum.rootDatum.root (d α)) = D.datum.rootDatum.root α := by
    rw [D.datum.root_eq, E.datum.root_eq]
    exact congrArg Additive.ofMul (h.root α)
  have hs (β : Root Q.pair.T) : l (E.datum.rootDatum.root β) =
      D.datum.rootDatum.root (d.symm β) := by
    simpa only [Equiv.apply_symm_apply] using hr (d.symm β)
  intro α
  constructor
  · apply positiveOfBaseComparison D E d (fun β hβ => (h.simple β).mp hβ) _ α
    intro β j i he
    apply hinj
    simpa only [map_add, hr] using he
  · intro hα
    have hb (β : Root Q.pair.T) (hβ : β ∈ E.base.support) : d.symm β ∈ D.base.support :=
      (h.simple (d.symm β)).mpr (by simpa only [Equiv.apply_symm_apply] using hβ)
    have hr' (β j i : Root Q.pair.T)
        (he : E.datum.rootDatum.root i = E.datum.rootDatum.root β + E.datum.rootDatum.root j) :
        D.datum.rootDatum.root (d.symm i) =
          D.datum.rootDatum.root (d.symm β) + D.datum.rootDatum.root (d.symm j) := by
      simpa only [map_add, hs] using congrArg l he
    simpa only [Equiv.symm_apply_apply] using
      positiveOfBaseComparison E D d.symm hb hr' (d α) hα

/-- The transported coordinate comparison supplies the signed root relations
for the cell extension. The common-kernel premise is retained in the ordered
conditional interface. -/
theorem ordinaryCentralLifting_conditional
    (_commonKernelSubtorus : Specs.TransportedRootCoordinates.CommonKernelSubtorus.{u})
    (transportedRootCoordinates : Specs.TransportedRootCoordinates.Statement.{u}) :
    Specs.OrdinaryCentralLifting.Statement.{u} := by
  intro k _ A P Q D E
  let _ := D.comm
  let _ := E.comm
  dsimp only
  intro d h hinj hindex hroot hdual hsimple
  obtain ⟨τ, hτ, hIsoτ⟩ := torusMapOfCharacters P.pair.split Q.pair.split h
  have hcompat : Compatible P Q D E d τ := by
    refine ⟨hτ.symm ▸ hinj, hτ.symm ▸ hindex, ?_, ?_, hsimple⟩
    · intro α
      change pullbackCharacters τ (d α).val = α.val
      rw [hτ]
      exact hroot α
    · intro α
      -- The perfect pairing detects the image of each coroot under the torus map.
      apply Additive.ofMul.injective
      apply E.datum.rootDatum.flip.toPerfPair.injective
      ext y
      let χ := Additive.toMul y
      change E.datum.rootDatum.toLinearMap (Additive.ofMul χ)
          (Additive.ofMul (Additive.toMul (D.datum.rootDatum.coroot α) ≫ τ)) =
        E.datum.rootDatum.toLinearMap (Additive.ofMul χ)
          (Additive.ofMul (Additive.toMul (E.datum.rootDatum.coroot (d α))))
      rw [E.datum.pairing_eq, E.datum.pairing_eq, ← hdual α χ, ← hτ]
      unfold pairing compositionPairing
      rw [Category.assoc]
      rfl
  obtain ⟨_, e, _, _, _, _, _, X, Y, hcoordinates, hpinP, hpinQ, hsigned⟩ :=
    transportedRootCoordinates P Q D E d τ hcompat
  obtain ⟨f, ⟨hf, hfinite, hflat, hsurj, hkernel, _, hfIso⟩, _⟩ :=
    CellHomomorphism.cellHomomorphism
      P.pair.G Q.pair.G P.pair.reductive Q.pair.reductive P.pair.T Q.pair.T
      P.pair.split Q.pair.split P.pair.maximal Q.pair.maximal
      P.pair.B Q.pair.B P.pair.borel Q.pair.borel P.pair.containsTorus Q.pair.containsTorus
      D.comm E.comm D.datum E.datum D.base E.base (basePos_iff_borelRoots D)
      (basePos_iff_borelRoots E) A X Y d τ hcompat.injective hcompat.finiteIndex hcompat.root
      hcompat.coroot (positiveComparison hcompat) hcompat.simple hsigned
  refine ⟨τ, f, hτ, ⟨hf.1, ?_⟩, hfinite, hflat, hsurj, hkernel,
    fun hs => hfIso (hIsoτ ⟨hinj, hs⟩), ?_⟩
  · intro α β hab
    simpa only [hab, hpinP α, hpinQ β] using hf.2 α.val
  · intro α
    obtain ⟨x, hx, hy⟩ := hcoordinates α
    have he : x.hom ≫ ((P.roots α).val.inclusion ≫ f) =
        x.hom ≫ ((e α).hom ≫ (Q.roots (d α)).val.inclusion) := by
      simpa only [hx, hy, Iso.trans_hom, Category.assoc] using hf.2 α
    exact ⟨e α, (cancel_epi x.hom).mp he⟩

end LinearAlgebraicGroups.Classification.OrdinaryCentralLifting

universe v8_closure_55bdefd962fffa9c_u0
theorem _root_.«LinearAlgebraicGroups».«Classification».«OrdinaryCentralLifting».«ordinaryCentralLifting» : _root_.«LinearAlgebraicGroups».«Specs».«OrdinaryCentralLifting».«Statement».{v8_closure_55bdefd962fffa9c_u0} :=
  @_root_.«LinearAlgebraicGroups».«Classification».«OrdinaryCentralLifting».«ordinaryCentralLifting_conditional».{v8_closure_55bdefd962fffa9c_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«TransportedRootCoordinates».«commonKernelSubtorus».{v8_closure_55bdefd962fffa9c_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«TransportedRootCoordinates».«transportedRootCoordinates».{v8_closure_55bdefd962fffa9c_u0})
