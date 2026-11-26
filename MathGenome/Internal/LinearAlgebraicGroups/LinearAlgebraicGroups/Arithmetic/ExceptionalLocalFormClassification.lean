import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalFormClassification
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndices
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedOuterExceptionalForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import Batteries.Tactic.OpenPrivate

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalLocalFormClassification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj TensorProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalLocalFormClassification
open Specs.Pinning (AttachedDatum BasedIso PinnedGroup PinnedIso SplitBorelPair)
open Specs.CharacterDescent (Cocharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.ExceptionalAffineRootSystems (exceptionalCartan)
open Specs.ExceptionalAffineBruhat (ExceptionalNumbering)
open Specs.GeometricRadicals (IsSemisimple IsSplitReductive)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open Specs.AutomorphismSequence (relativePoints restrictIso)
open Specs.RelativeFormComparison (IsInduced fieldTest transportedAut)
open Specs.RationalRealization (Realization)

open private pinnedLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private realization_corootSpan of_fullCorootLattice latticeCriterion_pair
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private multiplicativeBaseChange multiplicativeBaseChange_unit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private additiveLine_eq exceptionalCartan_eq
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves

noncomputable section

private def simpleEquiv {D E : Pinning.BasedRootDatum.{u}} (e : BasedIso D E) :
    D.base.support ≃ E.base.support :=
  (e.val.indexEquiv.image _).trans (Set.equivOfEq e.property)

private theorem pinnedCocharacterComparison {k : Type u} [Field k] {A : AdditiveLine k}
    {P Q : PinnedGroup A} {D : AttachedDatum P.pair} {E : AttachedDatum Q.pair}
    (f : PinnedIso P Q) (e : BasedIso D.toBased E.toBased)
    (he : Classification.Pinning.inducedBasedIso f D E = e) (y : E.toBased.Y) :
    Additive.toMul (e.val.coweightEquiv y) ≫ f.torus.hom = Additive.toMul y := by
  rw [← he]
  change (Additive.toMul y ≫ f.torus.inv) ≫ f.torus.hom = Additive.toMul y
  rw [Category.assoc, f.torus.inv_hom_id, Category.comp_id]
  rfl

private theorem numberedReference {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    {P : SplitBorelPair (SeparableClosure F)} (D : AttachedDatum P) {n : ℕ}
    (b : Fin n ≃ D.toBased.base.support)
    (g : P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj G.val)
    (hD : corootLattice D = ⊤)
    (hb : ∀ i j, D.toBased.datum.pairing (b i) (b j) = exceptionalCartan n i j) :
    Nonempty (SplitReference G D b g) := by
  classical
  let S := SeparableClosure F
  let C := groupBaseChange F S
  obtain ⟨A₀, A, R₀, R, f, t, a, q, ht, hq, _, hc⟩ :=
    QuasiSplitOrbitLevis.integralSplitComparison (F := F) (K := S) D.toBased
  obtain ⟨U, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist A P
  let P' : PinnedGroup A := ⟨P, U, pin⟩
  obtain ⟨v, hv⟩ := pinnedLift P' R.pinned D R.attached R.datumIso
  have h₀ : corootLattice R₀.attached = ⊤ := realization_corootSpan R₀ hD
  have hs : IsSemisimple R₀.pinned.pair.G := of_fullCorootLattice _ _ h₀
  have hsc : GeometricallySimplyConnected R₀.pinned.pair.G :=
    (latticeCriterion_pair Classification.IntegralRealization.integralRealization _ _ hs).mpr h₀
  obtain ⟨l, Q, ⟨E⟩⟩ := RamifiedExceptionalMarkedAdjoint.splitSequenceForAttachedDatum R₀.attached
  let d := R₀.datumIso
  let z := b.trans (simpleEquiv d)
  have hz (i : Fin n) : d.val.indexEquiv (b i).val = (z i).val := rfl
  have hnum : ExceptionalNumbering R₀.attached.toBased n z := by
    constructor
    · let := R₀.attached.toBased.freeX
      let B := R₀.attached.toBased.base.flip.toWeightBasisInt.map (LinearEquiv.ofTop _ h₀)
      rw [Module.finrank_eq_nat_card_basis B]
      exact (Nat.card_congr z.symm).trans (Nat.card_fin n)
    · intro i j
      rw [← hz, ← hz, RootPairing.Hom.pairing]
      exact hb i j
  let geom := v.group ≪≫ f
  obtain ⟨c, hIso⟩ :=
    Descent.RelativeFormComparison.schemeIsomorphismComparison (S := S) R₀.pinned.pair.G.val G.val
  let i : relativePoints R₀.pinned.pair.G.val (fieldTest F S) ≅
      relativePoints G.val (fieldTest F S) := c (geom.symm ≪≫ g)
  let m : MultiplicativeComparison F S := multiplicativeBaseChange F S
  have hm : PreservesUnits m := multiplicativeBaseChange_unit S
  refine ⟨⟨A₀, R₀.pinned, R₀.attached, d, z, hnum, hz, h₀, hs, hsc, geom,
    v.torus ≪≫ t, v.borel ≪≫ q, ?_, ?_, m, hm, ?_, l, Q, E, i,
    (hIso _ _).mpr rfl⟩⟩
  · change (P'.pair.T.inclusion ≫ (v.group.hom ≫ f.hom)) = _
    rw [← Category.assoc, v.torus_comm, Category.assoc, ht]
    rfl
  · change (P'.pair.B.inclusion ≫ (v.group.hom ≫ f.hom)) = _
    rw [← Category.assoc, v.borel_comm, Category.assoc, hq]
    rfl
  · intro y
    have hv' := pinnedCocharacterComparison v R.datumIso hv
      (R.datumIso.val.coweightEquiv.symm (d.val.coweightEquiv y))
    rw [LinearEquiv.apply_symm_apply] at hv'
    rw [Iso.trans_hom, ← Category.assoc, hv']
    have hc' := hc m hm (d.val.coweightEquiv y)
    change _ = m.hom ≫ C.map (Additive.toMul (d.val.coweightEquiv.symm
      (d.val.coweightEquiv y))) at hc'
    rw [LinearEquiv.symm_apply_apply] at hc'
    exact hc'

section ReferenceForms

open Specs.AutomorphismSequence (ExactSequence)
open Specs.ExceptionalFormsOverUnramifiedFields (HasTypeE)
open Specs.QuasiSplitInnerForms (AreInnerForms outerHom)
open Descent.QuasiSplitInnerForms (splitKernel differenceOfTrivializations)
open RootData (integralCartan)
open RootData.AbsoluteDynkinTypes (cartanDeterminesBasedDatum)
open private innerComparison from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
open private groundIso restrict_ground from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
open private simpleRootEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalUnramifiedCocycleSupport

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
  {P : SplitBorelPair (SeparableClosure F)} {D : AttachedDatum P} {n : ℕ}
  {b : Fin n ≃ D.toBased.base.support}
  {g : P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj G.val}

private theorem referenceType (R : SplitReference G D b g)
    (hn : n = 6 ∨ n = 7 ∨ n = 8) : HasTypeE R.attached n := by
  refine ⟨R.numbering.trans (simpleRootEquiv R.attached).symm, ?_⟩
  intro i j
  exact (R.numbered.2 i j).trans (congrFun (congrFun (exceptionalCartan_eq n hn) i) j)

private theorem innerCriteria (R : SplitReference G D b g)
    {A : AdditiveLine F} (Q : PinnedGroup A) (E : AttachedDatum Q.pair)
    (e : R.pinned.pair.G.val ≅ Q.pair.G.val) :
    IsInner R ↔ AreInnerForms (S := SeparableClosure F) Q.pair.G G := by
  let S := SeparableClosure F
  let i := groundIso (S := S) e
  have hi (σ : Gal(S/F)) : outerHom (S := S) R.sequence (transportedAut F S i σ) = 1 := by
    unfold transportedAut
    rw [show restrictIso (RelativeFormComparison.fieldMap F S σ) i = i from restrict_ground e σ,
      Iso.self_symm_id]
    exact map_one (outerHom (S := S) R.sequence)
  constructor
  · intro hr
    obtain ⟨l, q, ⟨E'⟩⟩ := RamifiedExceptionalMarkedAdjoint.splitSequenceForAttachedDatum E
    exact ⟨q, E'.inner, E'.onLift, E'.innerInjective, i.symm ≪≫ R.trivialization,
      (innerComparison R.sequence q E'.inner E'.onLift E'.innerInjective i R.trivialization).mpr
        (fun σ => (hr σ).trans (hi σ).symm)⟩
  · rintro ⟨q, inn, hql, hinj, r, hr⟩
    let j := i ≪≫ r
    have hj : i.symm ≪≫ j = r := by simp [j]
    have h := (innerComparison R.sequence q inn hql hinj i j).mp (hj.symm ▸ hr)
    -- Compare the original trivialization with the inner-valued one.
    let f := Aut.of (R.trivialization ≪≫ j.symm)
    have hf : f.asIso ≪≫ j = R.trivialization := by simp [f]
    intro σ
    rw [← hf, Descent.QuasiSplitInnerForms.changeOfTrivialization, map_mul, map_mul, map_inv, h σ,
      hi, mul_one, (Descent.QuasiSplitInnerForms.splitCoefficientMaps (S := S) R.sequence).1]
    exact inv_mul_cancel _

private theorem referenceAgreesWithInnerForms (R : SplitReference G D b g)
    (hn : n = 6 ∨ n = 7 ∨ n = 8) : AgreesWithInnerForms R := by
  refine ⟨innerCriteria R R.pinned R.attached (Iso.refl _), ?_⟩
  intro A' P' D' hD' htype
  obtain ⟨z, hz⟩ := htype
  let z' := z.trans (simpleRootEquiv D')
  let f := R.numbering.symm.trans z'
  have hf (i : Fin n) : f (R.numbering i) = z' i := by simp [f]
  obtain ⟨e, _⟩ :=
    ((cartanDeterminesBasedDatum R.attached.toBased D'.toBased R.coroots hD' f).mp
      (by
        intro i j
        obtain ⟨i, rfl⟩ := R.numbering.surjective i
        obtain ⟨j, rfl⟩ := R.numbering.surjective j
        rw [hf, hf]
        change R.attached.toBased.datum.pairing _ _ = D'.toBased.datum.pairing _ _
        exact ((R.numbered.2 j i).trans
          (congrFun (congrFun (exceptionalCartan_eq n hn) j) i)).trans (hz j i).symm)).exists
  have hA := additiveLine_eq A' R.line
  subst A'
  obtain ⟨v, hv⟩ := pinnedLift R.pinned P' R.attached D' e
  exact ⟨e, v.group, v.torus, v.borel, v.torus_comm, v.borel_comm,
    pinnedCocharacterComparison v e hv, innerCriteria R P' D' v.group⟩

end ReferenceForms

section Diagram

open Specs.QuasiSplitInnerForms (basedAutTopology fieldGalTopology relativeAutTopology relativeAutDiscrete
  trivialOuterAction outerHom mapCocycle)
open Specs.ExceptionalFormsOverUnramifiedFields (HasTypeE)
open Specs.SteinbergPinnedDescent (e6Involution)
open Specs.QuasiSplitOrbitLevis (simplePermutation)
open Descent.Forms (SchemeModels)
open Descent.NonabelianCohomology (Cocycle restriction)
open Descent.QuasiSplitInnerForms (splitCoefficientMaps)
open RootData (integralCartan)
open RootData.AbsoluteDynkinTypes (cartanDeterminesBasedDatum)
open private e7e8DiagramTrivial from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields

attribute [local instance] basedAutTopology fieldGalTopology relativeAutTopology relativeAutDiscrete

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
  {P : SplitBorelPair (SeparableClosure F)} {D : AttachedDatum P} {n : ℕ}
  {b : Fin n ≃ D.toBased.base.support}
  {g : P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj G.val}

private abbrev referenceForm (R : SplitReference G D b g) :
    SchemeModels (SeparableClosure F) R.pinned.pair.G :=
  ⟨G, ⟨R.geometric.symm ≪≫ g⟩⟩

private theorem existsDiagramCocycle (R : SplitReference G D b g) :
    ∃ ω : Cocycle (trivialOuterAction (k := F) (S := SeparableClosure F) R.attached.toBased),
      ∀ σ, ω σ = outerHom R.sequence (transportedAut F (SeparableClosure F) R.trivialization σ) := by
  obtain ⟨C⟩ := Descent.RelativeFormComparison.relativeFormClassification
    (S := SeparableClosure F) R.pinned.pair.G
  obtain ⟨a, ha, _⟩ := C.computes (referenceForm R) R.trivialization
  let ω := mapCocycle (outerHom R.sequence) continuous_of_discreteTopology
    (splitCoefficientMaps (S := SeparableClosure F) R.sequence).1 a
  exact ⟨ω, fun σ => congrArg (outerHom R.sequence) (ha σ)⟩

private def labelledDiagram (R : SplitReference G D b g) :
    Aut R.attached.toBased →* Equiv.Perm (Fin n) :=
  R.numbering.symm.permCongrHom.toMonoidHom.comp (simplePermutation R.attached)

private theorem labelledDiagram_apply (R : SplitReference G D b g) (d : Aut R.attached.toBased)
    (i : Fin n) :
    (R.numbering (labelledDiagram R d i)).val = d.asIso.hom.val.indexEquiv (R.numbering i).val := by
  change (R.numbering (R.numbering.symm (simplePermutation R.attached d (R.numbering i)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem labelledDiagram_injective (R : SplitReference G D b g) :
    Function.Injective (labelledDiagram R) := by
  intro d d' h
  let E := R.attached.toBased
  have he (i : E.base.support) :
      d'.asIso.hom.val.indexEquiv i.val = (simpleEquiv d.asIso.hom i).val := by
    obtain ⟨j, rfl⟩ := R.numbering.surjective i
    rw [← labelledDiagram_apply R d', ← h, labelledDiagram_apply]
    rfl
  have hp : AbsoluteDynkinTypes.PreservesCartan (integralCartan E.datum E.base)
      (integralCartan E.datum E.base) (simpleEquiv d.asIso.hom) := by
    intro i j
    change E.datum.pairing j.val i.val = E.datum.pairing
      (d.asIso.hom.val.indexEquiv j.val) (d.asIso.hom.val.indexEquiv i.val)
    exact d.asIso.hom.val.toHom.pairing.symm
  obtain ⟨a, ha, huniq⟩ := (cartanDeterminesBasedDatum E E R.coroots R.coroots _).mp hp
  apply Aut.ext
  apply Iso.ext
  exact (huniq d.asIso.hom (fun _ => rfl)).trans (huniq d'.asIso.hom he).symm

private theorem labelledDiagram_cartan (R : SplitReference G D b g)
    (hn : n = 6 ∨ n = 7 ∨ n = 8) (d : Aut R.attached.toBased) :
    ∀ i j, CartanMatrix.E n (labelledDiagram R d i) (labelledDiagram R d j) =
      CartanMatrix.E n i j := by
  intro i j
  rw [← exceptionalCartan_eq n hn, ← R.numbered.2, ← R.numbered.2 i j,
    labelledDiagram_apply, labelledDiagram_apply]
  exact d.asIso.hom.val.toHom.pairing

private theorem innerOfTypeE7E8 (R : SplitReference G D b g) (hn : n = 7 ∨ n = 8) :
    IsInner R := by
  intro σ
  let d := outerHom R.sequence (transportedAut F (SeparableClosure F) R.trivialization σ)
  apply labelledDiagram_injective R
  rw [map_one]
  exact e7e8DiagramTrivial hn _ (labelledDiagram_cartan R (.inr hn) d)

private theorem e6DiagramAlternatives (R : SplitReference G D b g) (h : n = 6)
    (d : Aut R.attached.toBased) :
    labelledDiagram R d = 1 ∨
      labelledDiagram R d = ((finCongr h).trans e6Involution).trans (finCongr h).symm := by
  subst n
  exact Arithmetic.SteinbergPinnedDescent.e6Diagram.1 _ (labelledDiagram_cartan R (.inl rfl) d)

private theorem quadraticDiagramField (R : SplitReference G D b g) (h : n = 6)
    (ω : Cocycle (trivialOuterAction (k := F) (S := SeparableClosure F) R.attached.toBased))
    (hω : ∃ σ, ω σ ≠ 1) :
    ∃ (L : FiniteGaloisIntermediateField F (SeparableClosure F))
      (θ : Gal(L/F) →* Aut R.attached.toBased), Module.finrank F L = 2 ∧ Function.Injective θ ∧
        ∀ σ, θ (restriction L σ) = ω σ := by
  classical
  let S := SeparableClosure F
  let : DiscreteTopology (Aut R.attached.toBased) := ⟨rfl⟩
  let θS : Gal(S/F) →* Aut R.attached.toBased :=
    { toFun := ω
      map_one' := by
        have hh := ω.property.2 1 1
        rw [one_mul] at hh
        change ω 1 = ω 1 * ω 1 at hh
        exact mul_left_cancel (hh.symm.trans (mul_one (ω 1)).symm)
      map_mul' := fun σ τ => ω.property.2 σ τ }
  have hcont : Continuous θS := ω.property.1
  have hopen : IsOpen (θS.ker : Set Gal(S/F)) :=
    (isOpen_discrete ({1} : Set (Aut R.attached.toBased))).preimage hcont
  have hclosed : IsClosed (θS.ker : Set Gal(S/F)) := isClosed_singleton.preimage hcont
  let N : _root_.ClosedSubgroup Gal(S/F) := ⟨θS.ker, hclosed⟩
  let J := IntermediateField.fixedField θS.ker
  have hfix : J.fixingSubgroup = θS.ker := InfiniteGalois.fixingSubgroup_fixedField N
  have hfin := (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois J).mp (by
    rw [hfix]
    exact ⟨hopen, inferInstance⟩)
  let L : FiniteGaloisIntermediateField F S :=
    { toIntermediateField := J, finiteDimensional := hfin.1, isGalois := hfin.2 }
  let e : Gal(L/F) ≃* θS.range :=
    (InfiniteGalois.normalAutEquivQuotient N).symm.trans (QuotientGroup.quotientKerEquivRange θS)
  let θ : Gal(L/F) →* Aut R.attached.toBased := θS.range.subtype.comp e.toMonoidHom
  have he (σ : Gal(S/F)) : θ (restriction L σ) = θS σ := by
    change (e (restriction L σ)).val = θS σ
    have hh : (InfiniteGalois.normalAutEquivQuotient N) (QuotientGroup.mk σ) = restriction L σ := rfl
    rw [← hh]
    change (QuotientGroup.quotientKerEquivRange θS
      ((InfiniteGalois.normalAutEquivQuotient N).symm
        ((InfiniteGalois.normalAutEquivQuotient N) (QuotientGroup.mk σ)))).val = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨τ, hτ⟩ := hω
  have hrange : (θS.range : Set (Aut R.attached.toBased)) = {1, θS τ} := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      rcases e6DiagramAlternatives R h (θS σ) with hs | hs
      · left
        exact labelledDiagram_injective R (hs.trans (map_one _).symm)
      · right
        apply labelledDiagram_injective R
        rcases e6DiagramAlternatives R h (θS τ) with ht | ht
        · exact (hτ (labelledDiagram_injective R (ht.trans (map_one _).symm))).elim
        · exact hs.trans ht.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact θS.range.one_mem
      · exact ⟨τ, rfl⟩
  have hcard : Nat.card θS.range = 2 :=
    Set.ncard_eq_two.mpr ⟨1, θS τ, Ne.symm hτ, hrange⟩
  refine ⟨L, θ, ?_, Subtype.val_injective.comp e.injective, he⟩
  let : FiniteDimensional F (L : Type u) := L.finiteDimensional
  let : IsGalois F (L : Type u) := L.isGalois
  exact (IsGalois.card_aut_eq_finrank F L).symm.trans ((Nat.card_congr e.toEquiv).trans hcard)

end Diagram

section LocalForms

open Specs.AdjointRepresentation (GroupPoints)
open Specs.AutomorphismSequence (AdjointQuotient groupSections automorphisms)
open Specs.ExceptionalAffineBruhat (IsUnramifiedLocalExtension)
open Specs.ExceptionalLocalRootCoordinates (ramificationIndex normalizedValuation normalizedValueGroupMap)
open Specs.ExceptionalFormsOverUnramifiedFields (HasTypeE)
open Specs.ExceptionalTwistedTraceComparison (PointCocycle Twist InnerMap ActsByConjugation
  adjointAction extendPoint)
open Specs.GeometricBorelConjugacy (IsQuasiSplit)
open Specs.GeometricRadicals (IsReductive)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction outerHom pinnedSection AreInnerForms
  mapCocycle mapH1 fieldGalTopology basedAutTopology relativeAutTopology relativeAutDiscrete)
open Specs.RelativeFormComparison (fieldMap)
open Specs.SteinbergPinnedDescent (comparisonOnPoints coefficientAction e6Involution)
open Descent.Forms (SchemeModels)
open Descent.NonabelianCohomology (Cocycle pointAction pointMap restriction classOf)
open Descent.QuasiSplitInnerForms (splitKernel splitCoefficientMaps liftInnerCocycle
  differenceOfTrivializations changeOfTrivialization)
open MaximalUnramifiedBrauer (IsUnramified)
open RamifiedOuterExceptionalForms (existsPinnedInnerReference ramifiedOuterQuasiSplit)
open private modelOfRelativeIso pinnedClass quasiSplitUniqueness
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
open private comparison_transports_action reductive_of_relative_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison
open private normalizedValueGroupMap_exp normalizedValuation_algebraMap_exp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private normalized_unramified
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves

attribute [local instance] fieldGalTopology basedAutTopology relativeAutTopology relativeAutDiscrete

private theorem relativeIso_fixed_of_trivial {F S : Type u} [Field F] [Field S] [Algebra F S]
    {G H : GroupScheme F}
    (i : relativePoints G (fieldTest F S) ≅ relativePoints H (fieldTest F S))
    (σ : Gal(S/F)) (h : transportedAut F S i σ = 1) :
    restrictIso (fieldMap F S σ) i = i := by
  have hh := congrArg Aut.asIso h
  change restrictIso (fieldMap F S σ) i ≪≫ i.symm = Iso.refl _ at hh
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans] using
    congrArg (fun j => j ≪≫ i) hh

private theorem liftFormCocycle {F S : Type u} [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    {G H : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    (inn : InnerMap Q) (hinj : Function.Injective (inn.app (op (fieldTest F S))))
    (i : relativePoints G.val (fieldTest F S) ≅ relativePoints H.val (fieldTest F S))
    (hi : ∀ σ, transportedAut F S i σ ∈ (inn.app (op (fieldTest F S))).hom.range) :
    ∃ a : PointCocycle (S := S) Q.quotient.val,
      ∀ σ, transportedAut F S i σ = inn.app (op (fieldTest F S)) ⟨a.val σ⟩ := by
  obtain ⟨C⟩ := Descent.RelativeFormComparison.relativeFormClassification (S := S) G
  obtain ⟨a, ha, _⟩ := C.computes (modelOfRelativeIso G H i) i
  obtain ⟨d, hd, _⟩ := liftInnerCocycle G.val Q.quotient.val inn hinj a (fun σ => ha σ ▸ hi σ)
  exact ⟨d, fun σ => (ha σ).symm.trans (hd σ).symm⟩

private def twistOfComparison {F S : Type u} [Field F] [Field S] [Algebra F S] [IsGalois F S]
    {G H : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    (hH : IsReductive H) (inn : InnerMap Q)
    (hLift : ActsByConjugation inn) (hinj : ∀ U, Function.Injective (inn.app U))
    (i : relativePoints G.val (fieldTest F S) ≅ relativePoints H.val (fieldTest F S))
    (a : PointCocycle (S := S) Q.quotient.val)
    (hi : ∀ σ, transportedAut F S i σ = inn.app (op (fieldTest F S)) ⟨a.val σ⟩) :
    Twist a where
  group := H
  reductive := hH
  trivialization := i
  inner := inn
  onLift := hLift
  innerInjective := hinj
  cocycle_eq := hi
  fixed := by
    intro x σ
    let y := (comparisonOnPoints i).symm (extendPoint (S := S) x)
    have hy := (comparisonOnPoints i).apply_symm_apply (extendPoint (S := S) x)
    have hx : coefficientAction S H.val σ (extendPoint x) = extendPoint x :=
      (Arithmetic.SteinbergPinnedDescent.rationalPoints H (extendPoint x)).mpr ⟨x, rfl⟩ σ
    have h := comparison_transports_action i σ y
    rw [hi σ] at h
    change comparisonOnPoints i (adjointAction inn (a.val σ) (coefficientAction S G.val σ y)) =
      coefficientAction S H.val σ (comparisonOnPoints i y) at h
    rw [hy, hx] at h
    exact (comparisonOnPoints i).injective (h.trans hy.symm)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {G : AffineAlgebraicGroup F}
  {P : SplitBorelPair (SeparableClosure F)} {D : AttachedDatum P} {n : ℕ}
  {b : Fin n ≃ D.toBased.base.support}
  {g : P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj G.val}

private theorem ramificationCases (L : Type u) [Field L] [Algebra F L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L] :
    IsUnramifiedLocalExtension F L ∨ 1 < ramificationIndex F L := by
  have hm : StrictMono (normalizedValueGroupMap F L) :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).strictMono.comp
      (ValuativeExtension.mapValueGroupWithZero_strictMono.comp
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).symm.strictMono)
  have hpos := hm (WithZero.exp_lt_exp.mpr (show (0 : ℤ) < 1 by decide))
  rw [normalizedValueGroupMap_exp, normalizedValueGroupMap_exp, mul_zero, mul_one,
    WithZero.exp_lt_exp] at hpos
  by_cases he : ramificationIndex F L = 1
  · left
    intro z
    by_cases hz : z = 0
    · simp [hz]
    rw [normalizedValuation_algebraMap_exp F L hz, he, one_mul, WithZero.exp_log]
    exact (map_ne_zero _).mpr hz
  · right
    omega

private theorem unramifiedOfNormalized (L : Type u) [Field L] [Algebra F L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (hu : IsUnramifiedLocalExtension F L) :
    IsUnramified F L := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro v
  let eF := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  let eL := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (eF.symm (eL v))
  refine ⟨x, eL.injective ?_⟩
  change normalizedValuation L (algebraMap F L x) = _
  rw [hu x]
  change eF (ValuativeRel.valuation F x) = eL v
  rw [hx, eF.apply_symm_apply]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem quasiSplitReferenceIso (R : SplitReference G D b g)
    {ω : Cocycle (trivialOuterAction (k := F) (S := SeparableClosure F) R.attached.toBased)}
    (V : PinnedRepresentative R.sequence ω) (hq : IsQuasiSplit G)
    (hω : ∀ σ, outerHom R.sequence (transportedAut F (SeparableClosure F) R.trivialization σ) = ω σ) :
    Nonempty (V.model.val.val ≅ G.val) := by
  let S := SeparableClosure F
  obtain ⟨C⟩ := Descent.RelativeFormComparison.relativeFormClassification (S := S) R.pinned.pair.G
  obtain ⟨a, ha, hc⟩ := C.computes (referenceForm R) R.trivialization
  let h := splitCoefficientMaps (S := S) R.sequence
  have hp : mapH1 (outerHom (S := S) R.sequence) continuous_of_discreteTopology h.1
      (C.equiv (Quotient.mk _ (referenceForm R))) = classOf ω := by
    rw [hc]
    apply congrArg classOf
    apply Subtype.ext
    funext σ
    exact (congrArg (outerHom R.sequence) (ha σ)).trans (hω σ)
  have hw := pinnedClass R.sequence C h ω V
  have hq' := quasiSplitUniqueness Descent.RelativeFormComparison.relativeFormClassification
    Descent.BorelInnerAlignment.borelInnerAlignment R.sequence C h ω V (referenceForm R) hq hp
  exact Quotient.exact (C.equiv.injective (hw.trans hq'.symm))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem referenceFormReductive (R : SplitReference G D b g) : IsReductive G :=
  reductive_of_relative_iso R.trivialization R.pinned.pair.reductive

private theorem outerCase (R : SplitReference G D b g) (h₆ : n = 6)
    (hG : IsReductive G) (ho : ¬ IsInner R) : HasOuterRepresentative R h₆ := by
  subst n
  let S := SeparableClosure F
  obtain ⟨δ, hδ⟩ := existsDiagramCocycle R
  have hnontriv : ∃ σ, δ σ ≠ 1 := by
    by_contra! h
    exact ho (fun σ => (hδ σ).symm.trans (h σ))
  obtain ⟨L, θ, hdeg, hinj, hθ⟩ := quadraticDiagramField R rfl δ hnontriv
  obtain ⟨vL, tL, heL, hL, _, _, _⟩ := finiteExtension_localField (K := F) (L := L)
  let := vL
  let := tL
  let := heL
  let := hL
  have hne : θ ≠ 1 := by
    rintro he
    obtain ⟨σ, hσ⟩ := hnontriv
    exact hσ ((hθ σ).symm.trans (congrFun (congrArg DFunLike.coe he) (restriction L σ)))
  have hlabel (σ : Gal(L/F)) (hσ : σ ≠ 1) (i : Fin 6) :
      (θ σ).asIso.hom.val.indexEquiv (R.numbering i).val = (R.numbering (e6Involution i)).val := by
    rcases e6DiagramAlternatives R rfl (θ σ) with hh | hh
    · exact (hσ (hinj ((labelledDiagram_injective R
        (hh.trans (map_one _).symm)).trans (map_one θ).symm))).elim
    · rw [← labelledDiagram_apply, hh]
      rfl
  have hram := ramificationCases (F := F) L
  have houter (σ : Gal(S/F)) :
      outerHom R.sequence (transportedAut F S R.trivialization σ) = θ (restriction L σ) :=
    (hδ σ).symm.trans (hθ σ).symm
  obtain ⟨ω, V, hω, hi⟩ :=
    existsPinnedInnerReference R.sequence L θ (referenceForm R) R.trivialization houter
  have hω' (σ : Gal(S/F)) : outerHom R.sequence (transportedAut F S R.trivialization σ) = ω σ :=
    (houter σ).trans (hω σ).symm
  refine ⟨L, vL, tL, hL, heL, θ, hdeg, hne, hram, hlabel, ω, V, ?_⟩
  rcases hram with hu | hram
  · obtain ⟨Q, inn, hLift, hin, i, hInner⟩ := hi
    obtain ⟨a, ha⟩ := liftFormCocycle inn (hin _) i hInner
    let T := twistOfComparison hG inn hLift hin i a ha
    obtain ⟨K, _, _, _, _, _, _, M, A, aK, N, _, _, _, _, _, _, hres⟩ :=
      ExceptionalStableAlcoves.exceptionalAlcoveNormalForm F V 6 (.inl rfl)
        (referenceType R (.inl rfl)) R.semisimple R.simplyConnected (.inl rfl)
        L (unramifiedOfNormalized L hu) ⟨θ, fun σ => (hω σ).symm⟩ Q a
    have hn : ¬ ∀ σ, ω σ = 1 := fun h => ho fun σ => (hω' σ).trans (h σ)
    obtain ⟨⟨e⟩, hQ⟩ := (hres T).1 hn
    exact ⟨e.symm, hQ, fun σ => ⟨hω' σ, hω σ⟩⟩
  · have hq := ramifiedOuterQuasiSplit F S R.sequence R.semisimple R.simplyConnected
      (referenceType R (.inl rfl)) L hdeg hram θ hne (referenceForm R) R.trivialization houter
    obtain ⟨e⟩ := quasiSplitReferenceIso R V hq hω'
    exact ⟨e, hq, fun σ => ⟨hω' σ, hω σ⟩⟩

end LocalForms

section InnerLevel

open Specs.AutomorphismSequence (AdjointQuotient)
open Specs.IntegralSemisimpleModel (Model Integers fibre integerAlgebra forgetFibrePoint)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalAffineBruhat (SplitLevel FieldPoints IsUnramifiedLocalExtension scalarPoints)
open Specs.ExceptionalStableAlcoves (MarkedExceptionalCover MarkedUnramifiedLevel)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Specs.AdjointRepresentation (GroupPoints)
open Descent.NonabelianCohomology (pointAction Points)
open private fibreTowerComparison from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent
open private forgetFibrePointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private forgetFibrePoint_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private quotientIsoOfKernel centralizesIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private projection_eq_one_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private levelCoefficientComparison markedAdjointQuotient groundReferenceMarking
  markedExceptionalCoverExists from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves

attribute [local instance] integerAlgebra

private theorem numberedCover {D : Pinning.BasedRootDatum.{u}} {n : ℕ}
    (b : Fin n ≃ D.base.support) (hs : D.datum.corootSpan ℤ = ⊤)
    (hb : ∀ i j, D.datum.pairing (b i) (b j) = exceptionalCartan n i j) :
    ∃ M : MarkedExceptionalCover D n, ∀ i, M.datum.val.indexEquiv (b i).val = (M.scNumbering i).val := by
  obtain ⟨M⟩ := markedExceptionalCoverExists D n b hs hb
  let c := b.trans (simpleEquiv M.datum)
  have hc (i j : Fin n) : M.scDatum.datum.pairing (c i).val (c j).val = exceptionalCartan n i j :=
    M.datum.val.toHom.pairing.trans (hb i j)
  let e := c.trans M.scNumbering.symm
  have hce (i : Fin n) : M.scNumbering (e i) = c i := Equiv.apply_symm_apply M.scNumbering (c i)
  let a := e.trans M.adNumbering
  have he (i j : Fin n) : exceptionalCartan n (e i) (e j) = exceptionalCartan n i j := by
    rw [← M.scNumbering_eq.2, hce, hce]
    exact hc i j
  refine ⟨{ M with
    scNumbering := c
    adNumbering := a
    scNumbering_eq := ⟨M.scNumbering_eq.1, hc⟩
    adNumbering_eq := ⟨M.adNumbering_eq.1, fun i j => (M.adNumbering_eq.2 (e i) (e j)).trans (he i j)⟩
    numbering_comm := fun i => (congrArg (fun z : M.scDatum.base.support =>
      M.cover.rootEquiv z.val) (hce i).symm).trans (M.numbering_comm (e i)) }, fun _ => rfl⟩

private theorem adjointQuotientComparison {F : Type u} [Field F] {G H : AffineAlgebraicGroup F}
    (Q : AdjointQuotient G) (Q' : AdjointQuotient H) (i : G.val ≅ H.val) :
    ∃ j : Q.quotient.val ≅ Q'.quotient.val, Q.projection ≫ j.hom = i.hom ≫ Q'.projection := by
  refine quotientIsoOfKernel Q.projection Q'.projection i Q.fppf Q'.fppf ?_
  intro U x
  rw [projection_eq_one_iff Q, projection_eq_one_iff Q']
  exact (Descent.AutomorphismSequence.innerAut_eq_one_iff x).trans
    ((centralizesIso i x).trans (Descent.AutomorphismSequence.innerAut_eq_one_iff _).symm)

private theorem groundReferenceGroupIso {F : Type u} [Field F] {B : Pinning.BasedRootDatum.{u}}
    {M : Model B} (C : MarkedFibre M F) {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (d : BasedIso D.toBased B) :
    Nonempty (P.pair.G.val ≅ C.realization.pinned.pair.G.val) := by
  have hA := additiveLine_eq A C.line
  subst A
  obtain ⟨j, _, _, _⟩ := groundReferenceMarking C d
  exact ⟨j.group.symm⟩

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem markedLevelForSplitReference {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    (hu : IsUnramifiedLocalExtension F K) {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {n : ℕ} (Q : AdjointQuotient P.pair.G)
    (M : MarkedExceptionalCover D.toBased n) (hn : n = 6 ∨ n = 7 ∨ n = 8) :
    ∃ (L : MarkedUnramifiedLevel (K := K) M Q)
      (iG : P.pair.G.val ≅ (fibre F).obj M.scModel.group)
      (iQ : Q.quotient.val ≅ (fibre F).obj M.adModel.group),
      Q.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map M.cover.map ∧ L.diagram = 1 ∧
      ∀ x : Descent.NonabelianCohomology.Points F K Q.quotient.val.X,
        L.adjointPoint x = forgetFibrePoint M.adModel.group (CommAlgCat.of F K)
          (x ≫ iQ.hom.hom.hom) := by
  obtain ⟨p, p', e, X, BX, he, hp, hlevels⟩ :=
    ExceptionalStableAlcoveRepresentatives.markedAlcoveCoefficientComparison F M.cover n
      M.scNumbering M.adNumbering hn M.scNumbering_eq M.adNumbering_eq M.corootSpan M.rootSpan
  obtain ⟨Y, BY, hs, ht, ho, hcoef, hout⟩ := hlevels K hu
  let C := X.sc_fibre
  let C' := X.ad_fibre
  obtain ⟨j⟩ := groundReferenceGroupIso C M.datum
  obtain ⟨q, m, hm⟩ := markedAdjointQuotient M.cover C C' M.rootSpan
  obtain ⟨d, hd⟩ := adjointQuotientComparison Q q j
  let iG := j ≪≫ C.groupIso.symm
  let iQ := (d ≪≫ m) ≪≫ C'.groupIso.symm
  have hQ : Q.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map M.cover.map := by
    simp only [iQ, iG, Iso.trans_hom, Iso.symm_hom, Category.assoc, reassoc_of% hd,
      reassoc_of% hm, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨l, _, ⟨E⟩⟩ := RamifiedExceptionalMarkedAdjoint.splitSequenceForAttachedDatum C.realization.attached
  obtain ⟨l', _, ⟨E'⟩⟩ := RamifiedExceptionalMarkedAdjoint.splitSequenceForAttachedDatum C'.realization.attached
  obtain ⟨ρ, a, β, hmarked, haff, htype, haction⟩ := levelCoefficientComparison Y
    M.scNumbering M.adNumbering M.adNumbering_eq M.rootSpan M.numbering_comm C C' E E' 1 1
    (.inr rfl) (by intro σ i; simp only [MonoidHom.one_apply, map_one]; rfl)
    hcoef (fun h => hout h C C' l l' _ _)
  obtain ⟨s, hproj⟩ := fibreTowerComparison (F := F) (K := K)
  let B := groupBaseChange F K
  let ref := B.mapIso iG ≪≫ (s.app M.scModel.group).symm
  let adj := B.mapIso iQ ≪≫ (s.app M.adModel.group).symm
  have hcomm : B.map Q.projection ≫ adj.hom = ref.hom ≫ (fibre K).map M.cover.map := by
    have hs' := s.inv.naturality M.cover.map
    change B.map ((fibre F).map M.cover.map) ≫ (s.app M.adModel.group).inv =
      (s.app M.scModel.group).inv ≫ (fibre K).map M.cover.map at hs'
    change B.map Q.projection ≫ (B.map iQ.hom ≫ (s.app M.adModel.group).inv) =
      (B.map iG.hom ≫ (s.app M.scModel.group).inv) ≫ (fibre K).map M.cover.map
    rw [← Category.assoc, ← B.map_comp, hQ, B.map_comp, Category.assoc, hs', ← Category.assoc]
  let R := CommAlgCat.of F K
  let z := (((groupPointsFunctor F).mapIso iQ).app R).groupIsoToMulEquiv.trans
    (forgetFibrePointEquiv M.adModel.group R)
  have hz (x : Descent.NonabelianCohomology.Points F K Q.quotient.val.X) :
      z x = forgetFibrePoint M.adModel.group R (x ≫ iQ.hom.hom.hom) := rfl
  have hzk (x : GroupPoints ((groupBaseChange F K).obj Q.quotient.val) (CommAlgCat.of K K)) :
      z (baseChangePoint F K Q.quotient.val.X (CommAlgCat.of K K) x) =
        forgetFibrePoint M.adModel.group (CommAlgCat.of K K) (x ≫ adj.hom.hom.hom) := by
    apply Over.OverMorphism.ext
    rw [hz]
    let f := pullback.fst ((fibre F).obj M.adModel.group).X.hom (fieldSpecMap F K)
    let pF := pullback.fst M.adModel.group.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} F)))
    let pK := pullback.fst M.adModel.group.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} K)))
    change ((x.left ≫ pullback.fst Q.quotient.val.X.hom (fieldSpecMap F K)) ≫
      iQ.hom.hom.hom.left) ≫ pF = (x.left ≫ adj.hom.hom.hom.left) ≫ pK
    have hpK : (s.app M.adModel.group).hom.hom.hom.left ≫ f ≫ pF = pK :=
      hproj M.adModel.group
    have hp' : (s.app M.adModel.group).inv.hom.hom.left ≫ pK = f ≫ pF := by
      rw [← hpK]
      simp only [← Category.assoc]
      rw [show (s.app M.adModel.group).inv.hom.hom.left ≫
        (s.app M.adModel.group).hom.hom.hom.left = 𝟙 _ from
          congrArg (fun x => x.hom.hom.left) (s.app M.adModel.group).inv_hom_id]
      rw [Category.id_comp]
    have hf' : (B.map iQ.hom).hom.hom.left ≫ f =
        pullback.fst Q.quotient.val.X.hom (fieldSpecMap F K) ≫ iQ.hom.hom.hom.left := by
      change ((baseChange F K).map iQ.hom.hom.hom).left ≫ _ = _
      exact pullback.lift_fst _ _ _
    change _ = (x.left ≫ ((B.map iQ.hom).hom.hom.left ≫
      (s.app M.adModel.group).inv.hom.hom.left)) ≫ pK
    simp only [Category.assoc, hp', reassoc_of% hf']
  have hρ (σ : Gal(K/F)) (v : FieldPoints M.adModel K) :
      ρ σ v = scalarPoints M.adModel σ.toRingHom v := by
    obtain ⟨f, hf⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C'
    obtain ⟨w, rfl⟩ := (f.app R).groupIsoToMulEquiv.surjective v
    have ha := hmarked.1 σ w
    rw [← hf] at ha
    change ρ σ ((f.hom.app R).hom w) =
      scalarPoints M.adModel σ.toRingHom ((f.hom.app R).hom w)
    rw [ha, MonoidHom.one_apply, map_one]
    change ExceptionalMarkedRootDescent.markedFibrePoint C' R
      (mapPoints (CommAlgCat.ofHom σ.toAlgHom) w) =
      scalarPoints M.adModel σ.toRingHom ((f.hom.app R).hom w)
    rw [hf R w]
    unfold ExceptionalMarkedRootDescent.markedFibrePoint
    let a : R ⟶ R := CommAlgCat.ofHom σ.toAlgHom
    have hw : mapPoints a w ≫ C'.groupIso.inv.hom.hom =
        mapPoints a (w ≫ C'.groupIso.inv.hom.hom) := Category.assoc _ _ _
    rw [hw]
    exact forgetFibrePoint_natural _ a _
  have hzρ (σ : Gal(K/F)) (x : Descent.NonabelianCohomology.Points F K Q.quotient.val.X) :
      z (pointAction F K Q.quotient.val.X σ x) = ρ σ (z x) := by
    rw [hz, hρ, hz]
    change forgetFibrePoint _ R (mapPoints (CommAlgCat.ofHom σ.toAlgHom)
      (x ≫ iQ.hom.hom.hom)) = _
    exact forgetFibrePoint_natural _ _ _
  refine ⟨⟨p, p', e, he, hp, X, BX, Y, BY, hs, ht, ref, adj, hcomm, z, hzk, C', l',
    1, ρ, a, β, hmarked, hzρ, haff, htype, haction, ho⟩, iG, iQ, hQ, rfl, hz⟩

end InnerLevel

section InnerForms

open Specs.AdjointRepresentation (GroupPoints)
open Specs.AutomorphismSequence (AdjointQuotient RelativeAut restrictAut)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalAffineBruhat (IsUnramifiedLocalExtension)
open Specs.ExceptionalAffineBuilding (lengthZeroNormalizer typeChange)
open Specs.ExceptionalInnerIndices (e6Black e7Black)
open Specs.ExceptionalStableAlcoves (changeCoordinates MarkedUnramifiedLevel AlcoveNormalForm)
open Specs.ExceptionalTwistedTraceComparison (PointCocycle Twist InnerMap ActsByConjugation)
open Specs.GeometricBorelConjugacy (IsQuasiSplit)
open Specs.GeometricRadicals (IsReductive)
open Specs.IntegralSemisimpleModel (fibre forgetFibrePoint integerAlgebra)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction
  fieldGalTopology basedAutTopology relativeAutTopology relativeAutDiscrete)
open Specs.RelativeFormComparison (automorphismAction fieldMap)
open Descent.NonabelianCohomology (Cocycle Points pointAction pointMap restriction)
open Descent.QuasiSplitInnerForms (splitKernel changeOfTrivialization)
open ExceptionalStableAlcoveRepresentatives (cocycle_trivial_of_generator)
open MaximalUnramifiedBrauer (IsUnramified)
open private pinnedRepresentatives from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
open private groundIso induced_iff schemeIsoEquiv schemeIsoEquiv_ground
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
open private adjointQuotientOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalUnramifiedCocycleSupport
open private normalized_unramified enlargeCocycleSupport alcoveNormalFormAtLevel inflateNormalForm
  representative_trivial_of_type fixedRelativeIsoDescends
  relativeIsoAtLevel coefficientInclusion coefficientInclusion_comm
  restrictRelativeIso_injective restrictRelativeIso_comp restrictRelativeIso_trans
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private maximalTransport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence

attribute [local instance] integerAlgebra basedAutTopology fieldGalTopology relativeAutTopology relativeAutDiscrete

private def innerAt {F S : Type u} [Field F] [Field S] [Algebra F S]
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G} (inn : InnerMap Q) :
    Descent.NonabelianCohomology.Points F S Q.quotient.val.X →* RelativeAut G.val (fieldTest F S) :=
  (inn.app (op (fieldTest F S))).hom.comp
    { toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ => rfl }

private theorem innerAt_equivariant {F S : Type u} [Field F] [Field S] [Algebra F S]
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G} (inn : InnerMap Q)
    (σ : Gal(S/F)) (x : Descent.NonabelianCohomology.Points F S Q.quotient.val.X) :
    innerAt inn (pointAction F S Q.quotient.val.X σ x) =
      automorphismAction F S G.val σ (innerAt inn x) :=
  ConcreteCategory.congr_hom (inn.naturality (fieldMap F S σ).op) (ULift.up x)

private theorem innerAt_restrict {F : Type u} [Field F]
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G} (inn : InnerMap Q)
    (K : FiniteGaloisIntermediateField F (SeparableClosure F))
    (x : Descent.NonabelianCohomology.Points F K Q.quotient.val.X) :
    restrictAut (coefficientInclusion (F := F) (K := K) (S := SeparableClosure F)) (innerAt inn x) =
      innerAt inn (pointMap F K Q.quotient.val.X K.toIntermediateField.val x) :=
  (ConcreteCategory.congr_hom (inn.naturality
    (coefficientInclusion (F := F) (K := K) (S := SeparableClosure F)).op) (ULift.up x)).symm

set_option maxHeartbeats 1700000 in
set_option backward.isDefEq.respectTransparency false in
private theorem comparisonAtFiniteLevel {F : Type u} [Field F]
    {G H : AffineAlgebraicGroup F} {Q : AdjointQuotient G} (inn : InnerMap Q)
    (K : FiniteGaloisIntermediateField F (SeparableClosure F))
    (i : relativePoints G.val (fieldTest F (SeparableClosure F)) ≅
      relativePoints H.val (fieldTest F (SeparableClosure F)))
    (a : Gal(K/F) → Descent.NonabelianCohomology.Points F K Q.quotient.val.X)
    (ha₁ : a 1 = 1)
    (ha : ∀ σ, transportedAut F (SeparableClosure F) i σ =
      innerAt inn (pointMap F K Q.quotient.val.X K.toIntermediateField.val (a (restriction K σ)))) :
    ∃ j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val,
      let r := schemeIsoEquiv K G.val H.val j
      restrictIso (coefficientInclusion (F := F) (K := K) (S := SeparableClosure F)) r = i ∧
      ∀ σ, transportedAut F K r σ = innerAt inn (a σ) := by
  let S := SeparableClosure F
  let e := coefficientInclusion (F := F) (K := K) (S := S)
  have hfixed (τ : Gal(S/K)) : restrictIso (fieldMap F S (τ.restrictScalars F)) i = i := by
    apply relativeIso_fixed_of_trivial
    have h : restriction K (τ.restrictScalars F) = 1 := by
      apply AlgEquiv.ext
      intro x
      apply K.toIntermediateField.val.injective
      exact (AlgEquiv.restrictNormalHom_apply K.toIntermediateField (τ.restrictScalars F) x).trans
        (τ.commutes x)
    rw [ha, h, ha₁, map_one, map_one]
  obtain ⟨j, hj⟩ := relativeIsoAtLevel (K := K) G H i hfixed
  let r := schemeIsoEquiv K G.val H.val j
  refine ⟨j, hj, ?_⟩
  intro σ
  obtain ⟨τ, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective S :
    Function.Surjective (restriction K)) σ
  have hflat : Flat e.left := inferInstanceAs (Flat (fieldSpecMap K S))
  have hsurj : Surjective e.left := by
    change Surjective (fieldSpecMap K S)
    exact ⟨fun _ => ⟨IsLocalRing.closedPoint S, Subsingleton.elim _ _⟩⟩
  apply Aut.ext
  apply restrictRelativeIso_injective e hflat hsurj
  change restrictIso e (restrictIso (fieldMap F K (restriction K τ)) r ≪≫ r.symm) =
    (restrictAut e (innerAt inn (a (restriction K τ)))).asIso
  rw [innerAt_restrict, restrictRelativeIso_trans, restrictRelativeIso_comp,
    coefficientInclusion_comm, ← restrictRelativeIso_comp, hj]
  have hsymm : restrictIso e r.symm = i.symm := by rw [← hj]; rfl
  rw [hsymm]
  exact congrArg Aut.asIso (ha τ)

private theorem trivialUnramifiedLevel (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsUnramified F (⊥ : FiniteGaloisIntermediateField F (SeparableClosure F)) := by
  let K : FiniteGaloisIntermediateField F (SeparableClosure F) := ⊥
  obtain ⟨r, t, he, hL, _, _, _⟩ := finiteExtension_localField (K := F) (L := K)
  let := r
  let := t
  let := he
  let := hL
  refine ⟨K.finiteDimensional, inferInstance, r, t, hL, he, ?_⟩
  have hsurj : Function.Surjective (algebraMap F K) := by
    change Function.Surjective (algebraMap F (⊥ : IntermediateField F (SeparableClosure F)))
    rw [← show ⇑(IntermediateField.botEquiv F (SeparableClosure F)).symm = _ from
      funext (IntermediateField.botEquiv_symm (F := F) (E := SeparableClosure F))]
    exact (IntermediateField.botEquiv F (SeparableClosure F)).symm.surjective
  exact ValuativeRel.valuation_surjective.comp hsurj

private theorem positiveAtLevel {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    {D : Pinning.BasedRootDatum.{u}} {n : ℕ} {M : Specs.ExceptionalStableAlcoves.MarkedExceptionalCover D n}
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G} (L : MarkedUnramifiedLevel (K := K) M Q) :
    let A := ApartmentRoots.split M.adDatum.datum ℚ
    ∀ i, M.adDatum.base.IsPos i → 0 < A.root i L.p' ∧ A.root i L.p' < 1 := by
  intro A i hi
  have hp := (L.level.ad.chart.signs.positive_iff i 0).mpr (.inr ⟨rfl, ⟨i, L.level.ad_points.2.2.1 ▸ rfl, hi⟩⟩)
  change 0 < A.root i L.p' + (0 : ℤ) at hp
  have hn : ¬ A.positive L.p' (i, -1) := by
    rw [L.level.ad.chart.signs.positive_iff]
    simp
  change ¬ 0 < A.root i L.p' + ((-1 : ℤ) : ℚ) at hn
  have hne : A.root i L.p' ≠ 1 := fun h => L.level.ad.geometry.regular i ⟨1, by simpa using h.symm⟩
  push Not at hn
  exact ⟨by simpa using hp, lt_of_le_of_ne (by simpa using hn) hne⟩

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {G : AffineAlgebraicGroup F}
  {P : SplitBorelPair (SeparableClosure F)} {D : AttachedDatum P} {n : ℕ}
  {b : Fin n ≃ D.toBased.base.support}
  {g : P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj G.val}

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem innerCase (R : SplitReference G D b g) (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (hi : IsInner R) :
    (IsSplitReductive G ∧ Nonempty (R.pinned.pair.G.val ≅ G.val)) ∨
      (¬ IsSplitReductive G ∧
        ((∃ h : n = 6, HasMarkedInnerIndex R 2 (Fin.cast h ⁻¹' e6Black)) ∨
         (∃ h : n = 7, HasMarkedInnerIndex R 4 (Fin.cast h ⁻¹' e7Black)))) := by
  let S := SeparableClosure F
  let K₀ : FiniteGaloisIntermediateField F S := ⊥
  let ω : Cocycle (trivialOuterAction (k := F) (S := S) R.attached.toBased) :=
    ⟨fun _ => 1, continuous_const, fun _ _ => by simp⟩
  obtain ⟨V⟩ := pinnedRepresentatives R.sequence ω
  obtain ⟨v, hv⟩ := fixedRelativeIsoDescends R.pinned.pair.G V.model.val V.trivialization
    (fun σ => relativeIso_fixed_of_trivial _ σ ((V.transport_eq σ).trans (map_one _)))
  by_cases hsplit : IsSplitReductive G
  · obtain ⟨P', rfl⟩ := Classification.PinnedEquivalence.pinnedEquivalence.2 F |>.1 G hsplit
    have hq : IsQuasiSplit P'.G := ⟨P'.reductive, P'.B, P'.borel⟩
    obtain ⟨f⟩ := quasiSplitReferenceIso R V hq hi
    exact .inl ⟨hsplit, ⟨v ≪≫ f⟩⟩
  let inn := R.sequence.toExactSequence.inner
  obtain ⟨a₀, ha₀⟩ := liftFormCocycle inn (R.sequence.innerInjective _) R.trivialization
    (fun σ => (splitKernel R.sequence _).mp (hi σ))
  let Q₀ := adjointQuotientOfIso v R.adjoint
  have htype := referenceType R hn
  have href : Specs.ExceptionalFormsOverUnramifiedFields.IsExceptionalReference R.attached :=
    ⟨R.semisimple, R.simplyConnected, by rcases hn with h | h | h <;> subst n <;> tauto⟩
  obtain ⟨d₀, hd₀⟩ := ExceptionalUnramifiedCocycleSupport.exceptionalCocycleSupport V href Q₀ K₀
    (trivialUnramifiedLevel F) ⟨1, fun _ => rfl⟩ a₀
  obtain ⟨K, vK, tK, lK, eK, _, hK, hd, hfrob, aK₀, haK₀, had₀⟩ := enlargeCocycleSupport hd₀
  let := vK
  let := tK
  let := lK
  let := eK
  obtain ⟨M, hM⟩ := numberedCover R.numbering R.coroots R.numbered.2
  obtain ⟨L, iG, iQ, hQ, hL, hpoint⟩ := markedLevelForSplitReference hK R.adjoint M hn
  let aK : Gal(K/F) → Descent.NonabelianCohomology.Points F K R.adjoint.quotient.val.X := aK₀
  have haK (σ τ : Gal(K/F)) :
      aK (σ * τ) = aK σ * pointAction F K R.adjoint.quotient.val.X σ (aK τ) := haK₀ σ τ
  have had (σ : Gal(S/F)) :
      pointMap F K R.adjoint.quotient.val.X K.toIntermediateField.val (aK (restriction K σ)) =
        changeCoordinates (pointAction F S R.adjoint.quotient.val.X) a₀.val d₀ σ := had₀ σ
  have hcoc (σ τ : Gal(K/F)) :
      L.adjointPoint (aK (σ * τ)) = L.adjointPoint (aK σ) * L.coefficient σ (L.adjointPoint (aK τ)) := by
    rw [haK, map_mul, L.coefficient_eq]
  obtain ⟨N⟩ := alcoveNormalFormAtLevel L hK hfrob.choose hfrob.choose_spec hn (.inr hL) hd
    (fun σ => L.adjointPoint (aK σ)) hcoc
  let : TopologicalSpace (GroupPoints R.adjoint.quotient.val (CommAlgCat.of F K)) := ⊥
  let a : PointCocycle (S := K) R.adjoint.quotient.val :=
    ⟨fun σ => L.adjointPoint.symm (N.representative σ),
      continuous_of_discreteTopology, fun σ τ => by
        change L.adjointPoint.symm (N.representative (σ * τ)) =
          L.adjointPoint.symm (N.representative σ) *
            pointAction F K R.adjoint.quotient.val.X σ (L.adjointPoint.symm (N.representative τ))
        apply L.adjointPoint.injective
        rw [map_mul, L.coefficient_eq, L.adjointPoint.apply_symm_apply,
          L.adjointPoint.apply_symm_apply, L.adjointPoint.apply_symm_apply, N.representative_cocycle]⟩
  obtain ⟨c, hc⟩ := inflateNormalForm a₀ aK N d₀ had
  let i := (innerAt inn c).asIso ≪≫ R.trivialization
  have hci (σ : Gal(S/F)) :
      transportedAut F S i σ =
        innerAt inn (pointMap F K R.adjoint.quotient.val.X K.toIntermediateField.val
          (a.val (restriction K σ))) := by
    dsimp only [i]
    rw [changeOfTrivialization, ha₀, hc]
    change (innerAt inn c)⁻¹ * innerAt inn (a₀.val σ) *
      automorphismAction F S R.pinned.pair.G.val σ (innerAt inn c) = _
    rw [← innerAt_equivariant, changeCoordinates, map_mul, map_mul, map_inv]
  have splitOfTrivial (ht : ∀ σ, N.representative σ = 1) : IsSplitReductive G := by
    have hf (σ : Gal(S/F)) : restrictIso (fieldMap F S σ) i = i := by
      apply relativeIso_fixed_of_trivial
      rw [hci]
      change innerAt inn (pointMap F K R.adjoint.quotient.val.X K.toIntermediateField.val
        (L.adjointPoint.symm (N.representative (restriction K σ)))) = _
      rw [ht, map_one, map_one, map_one]
    obtain ⟨f, hf⟩ := fixedRelativeIsoDescends R.pinned.pair.G G i hf
    exact ⟨referenceFormReductive R, transportSubgroup f R.pinned.pair.T,
      R.pinned.pair.split, maximalTransport f R.pinned.pair.T R.pinned.pair.maximal⟩
  have h₈ : n ≠ 8 := fun h => hsplit (splitOfTrivial (representative_trivial_of_type N hL (.inl h)))
  have hφ : typeChange L.level.typeQuotient (N.representative N.frobenius) ≠ 1 := by
    intro ht
    obtain ⟨_, _, _, _, t, _, _, _, _, _, _, htriv, ht'⟩ := N.inner_correction hL
    have heq : typeChange L.base.typeQuotient t = 1 :=
      (L.scalar_types.1 (t : Specs.ExceptionalAffineBruhat.FieldPoints M.adModel F)).symm.trans (ht' ▸ ht)
    have hrep : N.representative N.frobenius = 1 := by
      rw [ht', htriv heq, map_one]
    exact hsplit (splitOfTrivial (cocycle_trivial_of_generator L.coefficient N.representative
      N.representative_cocycle N.frobenius N.arithmetic.1 hrep))
  have h₁ : a.val 1 = 1 := by simp
  obtain ⟨j, hj, hja⟩ := comparisonAtFiniteLevel inn K i a.val h₁ hci
  -- The adjusted trivialization presents the given group as the finite-level twist.
  let T := twistOfComparison (referenceFormReductive R) inn R.sequence.onLift R.sequence.innerInjective
    (schemeIsoEquiv K R.pinned.pair.G.val G.val j) a hja
  let t := forgetFibrePoint M.adModel.group (CommAlgCat.of F K) (a.val N.frobenius ≫ iQ.hom.hom.hom)
  have ht : t = N.representative N.frobenius :=
    (hpoint (a.val N.frobenius)).symm.trans (L.adjointPoint.apply_symm_apply _)
  have hmem : t ∈ lengthZeroNormalizer L.level.ad := ht.symm ▸ N.representative_mem N.frobenius
  have htype : typeChange L.level.typeQuotient t ≠ 1 := ht.symm ▸ hφ
  have hcomp : IsInduced F S ((groupBaseChange F S).mapIso (Iso.refl G.val))
      ((restrictIso (coefficientInclusion (F := F) (K := K) (S := S)) T.trivialization).symm ≪≫ i) := by
    change IsInduced F S _ ((restrictIso _ (schemeIsoEquiv K R.pinned.pair.G.val G.val j)).symm ≪≫ i)
    rw [hj, Iso.symm_self_id]
    apply (induced_iff _ _).mpr
    rw [schemeIsoEquiv_ground]
    exact Functor.mapIso_refl _ _
  let indices := ExceptionalInnerIndices.exceptionalInnerTitsIndices
  have h67 : n = 6 ∨ n = 7 := hn.imp_right (fun h => h.resolve_right h₈)
  rcases h67 with h₆ | h₇
  · subst n
    obtain ⟨_, j', f, hj', hf, hindex⟩ := indices.2.2.1 F K hK M.cover M.scNumbering
      M.adNumbering M.scNumbering_eq M.adNumbering_eq M.corootSpan M.rootSpan L.level L.building
      (positiveAtLevel L) R.pinned.pair.G R.adjoint iG iQ hQ a T N.frobenius N.arithmetic hmem htype
    refine .inr ⟨hsplit, .inl ⟨rfl, K, vK, tK, lK, eK, hK, M, L.p, L.p', L.apartments,
      L.level, L.building, iG, iQ, hM, hQ, a₀, a, T, N.frobenius, Iso.refl _, ha₀, ⟨c, hc, hcomp⟩,
      N.arithmetic, ⟨hmem, htype⟩, j', f, hj', hf, ?_⟩⟩
    simpa only [Functor.mapIso_refl, Iso.trans_refl, Fin.cast_refl, Set.preimage_id, Set.preimage_id'] using hindex
  · subst n
    obtain ⟨_, j', f, hj', hf, hindex⟩ := indices.2.2.2 F K hK M.cover M.scNumbering
      M.adNumbering M.scNumbering_eq M.adNumbering_eq M.corootSpan M.rootSpan L.level L.building
      (positiveAtLevel L) R.pinned.pair.G R.adjoint iG iQ hQ a T N.frobenius N.arithmetic hmem htype
    refine .inr ⟨hsplit, .inr ⟨rfl, K, vK, tK, lK, eK, hK, M, L.p, L.p', L.apartments,
      L.level, L.building, iG, iQ, hM, hQ, a₀, a, T, N.frobenius, Iso.refl _, ha₀, ⟨c, hc, hcomp⟩,
      N.arithmetic, ⟨hmem, htype⟩, j', f, hj', hf, ?_⟩⟩
    simpa only [Functor.mapIso_refl, Iso.trans_refl, Fin.cast_refl, Set.preimage_id, Set.preimage_id'] using hindex

end InnerForms

end

/-- The local form comparison with the marked Tits indices and the outer
pinned representative on the specified exceptional group. -/
theorem exceptionalLocalFormClassification :
    Specs.ExceptionalLocalFormClassification.Classification.{u} := by
  intro F _ _ _ _ G hG hsc n hn P D b g hb
  have hD : corootLattice D = ⊤ :=
    QuasiSplitPinnedPairModel.corootLatticeAfterSplitting G hG.1 hsc P D ⟨g.symm⟩
  obtain ⟨R⟩ := numberedReference D b g hD hb
  refine ⟨hD, R, referenceAgreesWithInnerForms R hn, ?_⟩
  by_cases hi : IsInner R
  · rcases innerCase R hn hi with h | h
    · exact .inl ⟨hi, h⟩
    · exact .inr (.inl ⟨hi, h⟩)
  · have h₆ : n = 6 := hn.resolve_right (fun h => hi (innerOfTypeE7E8 R h))
    exact .inr (.inr ⟨h₆, hi, outerCase R h₆ (referenceFormReductive R) hi⟩)

end LinearAlgebraicGroups.Arithmetic.ExceptionalLocalFormClassification
