import Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
import LinearAlgebraicGroups.Arithmetic.OddFixedVectorDensity
import LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import LinearAlgebraicGroups.Arithmetic.QuasiSplitComponentDescent
import LinearAlgebraicGroups.Arithmetic.QuasiSplitRadicalGeneration
import LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
import LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
import LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertApplication
import LinearAlgebraicGroups.Arithmetic.TrialitarianCliffordInvariants
import LinearAlgebraicGroups.Arithmetic.TrialitarianLeviDescent
import LinearAlgebraicGroups.Relative.Parabolics
import LinearAlgebraicGroups.Relative.RationalDensity
import LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.Index
import LinearAlgebraicGroups.Descent.RelativeRank
import LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

/-! The diagram action and local forms of trialitarian groups. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.TrialitarianLocalForms
open Specs.Arithmetic.NontrialitarianSpinModels (HasFixedVectorVertex)
open Specs.AbsoluteDynkinTypes (D4Cartan D4Outer PreservesCartan)
open QuasiSplitInnerForms (outerHom)
open RelativeFormComparison (transportedAut)

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

/-- The permutation of the four marked vertices attached to a based automorphism. -/
private def simplePermutation (D : D4Diagram G) (a : Aut D.datum.toBased) :
    Equiv.Perm (Fin 4) :=
  D.simple.trans
    ((a.asIso.hom.val.indexEquiv.subtypeEquiv (fun i => by
      change i ∈ D.datum.toBased.base.support ↔
        a.asIso.hom.val.indexEquiv i ∈ D.datum.toBased.base.support
      let e := a.asIso.hom.val.indexEquiv
      let I : Set D.datum.toBased.I := D.datum.toBased.base.support
      have he : e '' I = I := a.asIso.hom.property
      change i ∈ I ↔ e i ∈ I
      have hm : e i ∈ e '' I ↔ e i ∈ I := by rw [he]
      exact e.injective.mem_set_image.symm.trans hm)).trans D.simple.symm)

private theorem simplePermutation_apply (D : D4Diagram G) (a : Aut D.datum.toBased)
    (i : Fin 4) :
    (D.simple (simplePermutation D a i)).val =
      a.asIso.hom.val.indexEquiv (D.simple i).val := by
  simp [simplePermutation]

private def simplePermutationHom (D : D4Diagram G) :
    Aut D.datum.toBased →* Equiv.Perm (Fin 4) where
  toFun := simplePermutation D
  map_one' := by
    apply Equiv.ext
    intro i
    apply D.simple.injective
    apply Subtype.ext
    rw [simplePermutation_apply]
    rfl
  map_mul' a b := by
    apply Equiv.ext
    intro i
    apply D.simple.injective
    apply Subtype.ext
    change (D.simple (simplePermutation D (a * b) i)).val =
      (D.simple (simplePermutation D a (simplePermutation D b i))).val
    rw [simplePermutation_apply, simplePermutation_apply, simplePermutation_apply]
    rfl

private theorem simplePermutation_preservesCartan (D : D4Diagram G)
    (a : Aut D.datum.toBased) :
    PreservesCartan D4Cartan D4Cartan (simplePermutation D a) := by
  change ∀ i j : Fin 4, D4Cartan i j = D4Cartan (simplePermutation D a i) (simplePermutation D a j)
  intro i j
  calc
    D4Cartan i j = D.datum.toBased.datum.pairing (D.simple j).val (D.simple i).val :=
      (D.cartan i j).symm
    _ = D.datum.toBased.datum.pairing
        (D.simple (simplePermutation D a j)).val (D.simple (simplePermutation D a i)).val := by
      rw [simplePermutation_apply, simplePermutation_apply]
      exact a.asIso.hom.val.toHom.pairing.symm
    _ = _ := D.cartan _ _

open LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle)
open RelativeFormComparison (fieldTest)

local instance galTopology : TopologicalSpace (Gal(SeparableClosure F/F)) :=
  krullTopology F (SeparableClosure F)

local instance basedAutTopology (B : Pinning.BasedRootDatum.{u}) : TopologicalSpace (Aut B) := ⊥
local instance basedAutDiscrete (B : Pinning.BasedRootDatum.{u}) : DiscreteTopology (Aut B) := ⟨rfl⟩

local instance relativeAutTopology (H : GroupScheme F) :
    TopologicalSpace (AutomorphismSequence.RelativeAut H (fieldTest F (SeparableClosure F))) := ⊥

local instance relativeAutDiscrete (H : GroupScheme F) :
    DiscreteTopology (AutomorphismSequence.RelativeAut H (fieldTest F (SeparableClosure F))) := ⟨rfl⟩

private def formClassification (D : D4Diagram G) :
    RelativeFormComparison.RelativeClassification F (SeparableClosure F) D.pinned.pair.G :=
  (LinearAlgebraicGroups.Descent.RelativeFormComparison.relativeFormClassification
    (k := F) (S := SeparableClosure F) D.pinned.pair.G).some

private def formModel (D : D4Diagram G) :
    LinearAlgebraicGroups.Descent.Forms.SchemeModels (SeparableClosure F) D.pinned.pair.G :=
  ⟨G, ⟨D.splitIso⟩⟩

private def outerCocycle (D : D4Diagram G) :
    Cocycle (QuasiSplitInnerForms.trivialOuterAction
      (k := F) (S := SeparableClosure F) D.datum.toBased) :=
  QuasiSplitInnerForms.mapCocycle (outerHom D.sequence) continuous_of_discreteTopology
    (LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.splitCoefficientMaps
      (S := SeparableClosure F) D.sequence).1
    ((formClassification D).computes (formModel D) D.relativeIso).choose

private theorem outerCocycle_apply (D : D4Diagram G) (σ : Gal(SeparableClosure F/F)) :
    outerCocycle D σ = outerHom D.sequence (transportedAut F (SeparableClosure F) D.relativeIso σ) :=
  congrArg (outerHom D.sequence)
    (((formClassification D).computes (formModel D) D.relativeIso).choose_spec.1 σ)

/-- The diagram representation on all four marked vertices. -/
private def diagramAction (D : D4Diagram G) : Gal(SeparableClosure F/F) →* Equiv.Perm (Fin 4) :=
  (simplePermutationHom D).comp
    { toFun := outerCocycle D
      map_one' := by
        have h := (outerCocycle D).property.2 1 1
        simp only [mul_one, MonoidHom.one_apply, MulAut.one_apply] at h
        exact mul_left_cancel (show outerCocycle D 1 * outerCocycle D 1 =
          outerCocycle D 1 * 1 by simpa only [mul_one] using h.symm)
      map_mul' := fun σ τ => (outerCocycle D).property.2 σ τ }

private theorem diagramAction_apply (D : D4Diagram G) (σ : Gal(SeparableClosure F/F))
    (i : Fin 4) :
    (D.simple (diagramAction D σ i)).val =
      (outerHom D.sequence (transportedAut F (SeparableClosure F) D.relativeIso σ)).asIso.hom.val.indexEquiv
        (D.simple i).val :=
  (simplePermutation_apply D (outerCocycle D σ) i).trans
    (congrArg (fun a : Aut D.datum.toBased => a.asIso.hom.val.indexEquiv (D.simple i).val)
      (outerCocycle_apply D σ))

private theorem diagramAction_preservesCartan (D : D4Diagram G) (σ : Gal(SeparableClosure F/F)) :
    PreservesCartan D4Cartan D4Cartan (diagramAction D σ) :=
  simplePermutation_preservesCartan D _

private theorem isTransitive_iff (D : D4Diagram G) :
    D.IsTransitive ↔ ∀ i j : D4Outer, ∃ σ : Gal(SeparableClosure F/F),
      diagramAction D σ i.val = j.val := by
  unfold D4Diagram.IsTransitive
  constructor
  · intro h i j
    obtain ⟨σ, hσ⟩ := h i j
    refine ⟨σ, D.simple.injective (Subtype.ext ?_)⟩
    rw [diagramAction_apply, hσ]
  · intro h i j
    obtain ⟨σ, hσ⟩ := h i j
    exact ⟨σ, (diagramAction_apply D σ i.val).symm.trans
      (congrArg (fun t => (D.simple t).val) hσ)⟩

private theorem fixedVectorVertex (D : D4Diagram G) (h : ¬ D.IsTransitive) :
    HasFixedVectorVertex G 4 := by
  let H := (diagramAction D).range
  have hH : ∀ a ∈ H, PreservesCartan D4Cartan D4Cartan a := by
    rintro a ⟨σ, rfl⟩
    exact diagramAction_preservesCartan D σ
  have hn : ¬ ∀ i j : D4Outer, ∃ a ∈ H, a i.val = j.val := by
    intro h'
    apply h
    apply (isTransitive_iff D).mpr
    intro i j
    obtain ⟨_, ⟨σ, rfl⟩, hij⟩ := h' i j
    exact ⟨σ, hij⟩
  obtain ⟨i, hi⟩ := (RootData.AbsoluteDynkinTypes.d4ActionDichotomy H hH).mpr hn
  refine ⟨D.additive, D.pinned, D.datum, D.lifts, D.adjoint, D.sequence, D.splitIso,
    D.relativeIso, D.simple, i.val, D.induced, D.cartan, ?_, ?_⟩
  · change i.val.val ≠ 1
    exact fun hi => i.property (Fin.ext hi)
  · intro σ
    rw [← diagramAction_apply, hi (diagramAction D σ) ⟨σ, rfl⟩]


@[instance_reducible] private def outerVertexAction (D : D4Diagram G) : MulAction (Gal(SeparableClosure F/F)) D4Outer where
  smul σ i := ⟨diagramAction D σ i.val, fun h =>
    i.property ((diagramAction D σ).injective
      (h.trans (((RootData.AbsoluteDynkinTypes.d4Permutations _).mp
        (diagramAction_preservesCartan D σ)).symm)))⟩
  one_smul i := Subtype.ext (by change diagramAction D 1 i.val = i.val; rw [map_one]; rfl)
  mul_smul σ τ i := Subtype.ext (by
    change diagramAction D (σ * τ) i.val = diagramAction D σ (diagramAction D τ i.val)
    rw [map_mul]
    rfl)


/-- The diagram field of a transitive action and the equivariant identification
of its embeddings with the actual marked outer vertices. -/
private theorem cubicOrbitField (D : D4Diagram G) (h : D.IsTransitive) :
    let := outerVertexAction D
    ∃ (E : IntermediateField F (SeparableClosure F))
      (numbering : (E →ₐ[F] SeparableClosure F) ≃ D4Outer),
      Module.finrank F E = 3 ∧
      ∀ (σ : Gal(SeparableClosure F/F)) e, numbering (σ.toAlgHom.comp e) = σ • numbering e := by
  classical
  let S := SeparableClosure F
  let := outerVertexAction D
  let vertex : D4Outer := ⟨0, by decide⟩
  let H := MulAction.stabilizer Gal(S/F) vertex
  have hH : IsClosed (H : Set Gal(S/F)) := by
    let : TopologicalSpace (Fin 4) := ⊥
    let : DiscreteTopology (Fin 4) := ⟨rfl⟩
    have hfun : Continuous (fun a : Aut D.datum.toBased => simplePermutation D a vertex.val) :=
      continuous_of_discreteTopology
    have hc : Continuous (fun σ : Gal(S/F) => simplePermutation D (outerCocycle D σ) vertex.val) :=
      hfun.comp (outerCocycle D).property.1
    have hpre : (H : Set Gal(S/F)) =
        (fun σ : Gal(S/F) => simplePermutation D (outerCocycle D σ) vertex.val) ⁻¹' {vertex.val} :=
      Set.ext fun σ => ⟨fun hσ => congrArg Subtype.val hσ, fun hσ => Subtype.ext hσ⟩
    rw [hpre]
    exact isClosed_singleton.preimage hc
  let E := IntermediateField.fixedField H
  have hfix : E.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hH⟩
  let : MulAction.IsPretransitive Gal(S/F) D4Outer :=
    ⟨fun i j => by
      obtain ⟨σ, hσ⟩ := (isTransitive_iff D).mp h i j
      exact ⟨σ, Subtype.ext hσ⟩⟩
  let : Fintype D4Outer := inferInstanceAs (Fintype {i : Fin 4 // i ≠ 1})
  have hcard : Nat.card D4Outer = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hdegree : Module.finrank F E = 3 := by
    rw [E.finrank_eq_fixingSubgroup_index, hfix,
      MulAction.index_stabilizer_of_transitive, hcard]
  have hemb : Function.Surjective (fun σ : Gal(S/F) => σ.toAlgHom.comp E.val) := by
    intro e
    let T := e.liftNormal S
    let σ : Gal(S/F) := AlgEquiv.ofBijective T (AlgHom.normal_bijective F S S T)
    exact ⟨σ, AlgHom.ext fun x => e.liftNormal_commutes S x⟩
  have heq (σ τ : Gal(S/F)) :
      σ.toAlgHom.comp E.val = τ.toAlgHom.comp E.val ↔ σ • vertex = τ • vertex := by
    have key : τ⁻¹ * σ ∈ E.fixingSubgroup ↔
        σ.toAlgHom.comp E.val = τ.toAlgHom.comp E.val := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      constructor
      · intro hk
        apply AlgHom.ext
        intro x
        change σ x.val = τ x.val
        exact (AlgEquiv.symm_apply_eq τ).mp (hk x.val x.property)
      · intro hk x hx
        exact (AlgEquiv.symm_apply_eq τ).mpr (DFunLike.congr_fun hk ⟨x, hx⟩)
    rw [← key, hfix, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
  let number (e : E →ₐ[F] S) : D4Outer := (hemb e).choose • vertex
  have hnumber (σ : Gal(S/F)) : number (σ.toAlgHom.comp E.val) = σ • vertex :=
    (heq _ _).mp (hemb _).choose_spec
  refine ⟨E, Equiv.ofBijective number ⟨?_, ?_⟩, hdegree, ?_⟩
  · intro e f
    obtain ⟨σ, rfl⟩ := hemb e
    obtain ⟨τ, rfl⟩ := hemb f
    intro h'
    apply (heq σ τ).mpr
    simpa only [hnumber] using h'
  · intro i
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq Gal(S/F) vertex i
    exact ⟨_, (hnumber σ).trans hσ⟩
  · intro σ e
    obtain ⟨τ, rfl⟩ := hemb e
    change number ((σ * τ).toAlgHom.comp E.val) = σ • number (τ.toAlgHom.comp E.val)
    rw [hnumber, hnumber, mul_smul]


open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple integralDiagram)
open private extendComparison semisimple_of_commonExtension simpleFormOfConnectedDiagram
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitComponentDescent
open private centralIsogeny_postIso
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private d4_entry from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

private theorem referenceSemisimple (D : D4Diagram G) (hG : IsSemisimple G) :
    IsSemisimple D.pinned.pair.G :=
  semisimple_of_commonExtension hG D.splitIso.symm

private theorem referenceSimplyConnected (D : D4Diagram G) (hG : GeometricallySimplyConnected G) :
    GeometricallySimplyConnected D.pinned.pair.G := by
  let S := SeparableClosure F
  let A := AlgebraicClosure F
  let e : (GeometricRadicals.GeometricGroup D.pinned.pair.G).val ≅
      (GeometricRadicals.GeometricGroup G).val := extendComparison (R := A) D.splitIso
  intro H hH f hf
  have := hG H hH (f ≫ e.hom) (centralIsogeny_postIso e hf)
  exact IsIso.of_isIso_comp_right f e.hom

private theorem connectedDiagram (D : D4Diagram G) :
    (integralDiagram (RootData.integralCartan D.datum.toBased.datum D.datum.toBased.base)).IsConnected := by
  classical
  refine ⟨⟨D.simple 1⟩, ?_⟩
  have edge (i : Fin 4) : Relation.EqvGen
      (fun x y => (integralDiagram (RootData.integralCartan
        D.datum.toBased.datum D.datum.toBased.base)).edges x y ≠ 0) (D.simple i) (D.simple 1) := by
    by_cases hi : i = 1
    · subst i
      exact Relation.EqvGen.refl _
    · apply Relation.EqvGen.rel
      have hne : D.simple i ≠ D.simple 1 := fun h => hi (D.simple.injective h)
      simp only [integralDiagram, RootData.integralCartan, ite_eq_right hne, D.cartan]
      change (CartanMatrix.D 4 i 1 * CartanMatrix.D 4 1 i).toNat ≠ 0
      rw [d4_entry i 1, d4_entry 1 i]
      simp [hi, Ne.symm hi]
  intro i j
  exact (by simpa only [Equiv.apply_symm_apply] using
    (Relation.EqvGen.trans _ _ _ (edge (D.simple.symm i)) ((edge (D.simple.symm j)).symm)))

private theorem referenceCorootSpan (D : D4Diagram G) (hG : IsSemisimple G)
    (hSC : GeometricallySimplyConnected G) : corootLattice D.datum = ⊤ := by
  let P := D.pinned.pair
  let := D.datum.comm
  exact (Classification.SimplyConnectedLattice.latticeCriterion P.G
    (referenceSemisimple D hG) P.T P.split P.maximal D.datum.datum).mp
      (referenceSimplyConnected D hSC)

private theorem absoluteAlmostSimple (D : D4Diagram G) (hG : IsSemisimple G)
    (hSC : GeometricallySimplyConnected G) : IsAbsolutelyAlmostSimple G :=
  (simpleFormOfConnectedDiagram (K := SeparableClosure F)
    D.datum (referenceCorootSpan D hG hSC) (connectedDiagram D) D.splitIso).1

private theorem absoluteAlmostSimpleForRadicals {H : AffineAlgebraicGroup F}
    (h : IsAbsolutelyAlmostSimple H) : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple H := by
  refine ⟨h.1, ?_, ?_⟩
  · rintro ⟨e⟩
    exact h.2.1 ((Grp.isZero_trivial _).of_iso e)
  · intro N hN
    rcases h.2.2 N hN with h0 | h1
    · left
      exact ⟨h0.iso (Grp.isZero_trivial _)⟩
    · exact Or.inr h1


open TrialitarianAlbertDescentSpecification (DiagramPresentation cartanD4)
open Specs.GeometricBorelConjugacy (IsQuasiSplit)
open Specs.Unipotent (baseChangedAlgebraicGroup)

private abbrev albertRelabelling : Equiv.Perm (Fin 4) := Equiv.swap 1 3

private def albertOuterVertices : Fin 3 ≃ D4Outer := by
  let f (i : Fin 3) : D4Outer := ⟨albertRelabelling i.castSucc, by
    intro hi
    have h : albertRelabelling i.castSucc = albertRelabelling 3 := by
      simpa [albertRelabelling] using hi
    exact Fin.castSucc_ne_last i (albertRelabelling.injective h)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j h
    exact Fin.castSucc_injective _ (albertRelabelling.injective (congrArg Subtype.val h))
  · intro i
    have h : albertRelabelling i.val ≠ Fin.last 3 := by
      intro hi
      have he : albertRelabelling i.val = albertRelabelling 1 := by
        simpa [albertRelabelling] using hi
      exact i.property (albertRelabelling.injective he)
    obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr h
    refine ⟨j, Subtype.ext ?_⟩
    change albertRelabelling j.castSucc = i.val
    rw [hj, Equiv.swap_apply_self]

private theorem albertOuterVertices_apply (i : Fin 3) :
    (albertOuterVertices i).val = albertRelabelling i.castSucc := rfl

/-- Use the same cubic diagram field and the same marking for the Albert
isotropy theorem and for descent of quasi-splitness. -/
private theorem quasiSplitOfTransitiveDiagram
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (D : D4Diagram G) (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (h : D.IsTransitive) : IsQuasiSplit G := by
  classical
  let := outerVertexAction D
  obtain ⟨E, number, hdegree, hnumber⟩ := cubicOrbitField D h
  let numbering := number.trans albertOuterVertices.symm
  have hvertices (e : E →ₐ[F] SeparableClosure F) :
      albertRelabelling (numbering e).castSucc = (number e).val := by
    rw [← albertOuterVertices_apply]
    exact congrArg Subtype.val (albertOuterVertices.apply_symm_apply (number e))
  let P : DiagramPresentation G E (SeparableClosure F) :=
    { additive := D.additive
      pinned := D.pinned
      datum := D.datum
      lifts := D.lifts
      adjoint := D.adjoint
      autSequence := D.sequence
      semisimple := referenceSemisimple D hG
      simplyConnected := referenceSimplyConnected D hSC
      roots := albertRelabelling.trans D.simple
      cartan := fun i j => (D.cartan _ _).trans (by
        change CartanMatrix.D 4 (albertRelabelling j) (albertRelabelling i) = cartanD4 i j
        fin_cases i <;> fin_cases j <;> decide)
      form := D.relativeIso
      numbering := numbering
      diagramAction := fun σ e => by
        change (outerHom D.sequence (transportedAut F (SeparableClosure F) D.relativeIso σ)).asIso.hom.val.indexEquiv
          (D.simple (albertRelabelling (numbering e).castSucc)).val =
            (D.simple (albertRelabelling (numbering (σ.toAlgHom.comp e)).castSucc)).val
        rw [hvertices, hvertices, ← diagramAction_apply, hnumber]
        rfl }
  let : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hdegree]; decide)
  obtain ⟨M, _, _, hq, _, _⟩ :=
    TrialitarianCliffordInvariants.trialitarianCubicSplitting
      F E (SeparableClosure F) hdegree G P
  obtain ⟨c, hc⟩ :=
    TrialitarianAlbertApplication.albertIsotropy F E (SeparableClosure F) hdegree G P hG hSC M
  change ¬ (∀ (X : SchemeOver F) (g : X ⟶ G.val.X), Centralizes c g) at hc
  obtain ⟨X, hX⟩ := not_forall.mp hc
  obtain ⟨g, hg⟩ := not_forall.mp hX
  exact TrialitarianLeviDescent.quasiSplitDescent F E (SeparableClosure F)
    hdegree G P D.splitIso D.induced hG hSC ⟨c, X, g, hg⟩ hq

theorem finiteQuasiSplit : FiniteQuasiSplit.{u} := by
  intro F _ _ _ _ G hG hSC htrial
  obtain ⟨D, hD⟩ := htrial
  exact quasiSplitOfTransitiveDiagram D hG hSC hD

open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (completionAlgebra)
open CocharacterDynamics (existsLimitDecomposition oppositeCocharacter)

/-- Density at the isotropic completions suffices for the global conclusion. -/
private theorem globalStrongApproximation_of_localGeneration
    (localDensity : LocalGeneration.{u, v}) : GlobalStrongApproximation.{u, v} := by
  intro K _ D G hG hSC htrial hpos i S hS
  obtain ⟨diagram, hdiagram⟩ := htrial
  have hsimple := absoluteAlmostSimpleForRadicals (absoluteAlmostSimple diagram hG hSC)
  obtain ⟨c, hc⟩ := hpos
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨Q⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  apply ((OppositeRadicals.approximation D G i hsimple c hc P Q).2.2.2.2 S hS).2
  intro w
  obtain ⟨e, _, hc', _⟩ := OppositeRadicals.localGeneration D G i hsimple c hc P Q w.1
  exact localDensity D G hG hSC ⟨diagram, hdiagram⟩ i w.1
    ⟨e.hom ≫ (groupBaseChange K (D.Completion w.1)).map c, hc'⟩

open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open private positive_rank_iff_cocharacter proper_parabolic_cocharacter
  from LinearAlgebraicGroups.Descent.RelativeRank
open private baseChangeSelfIso from LinearAlgebraicGroups.Reductive.NontrivialRationalTorus

private theorem positiveSplitRank_of_nonzeroCocharacter
    (hG : IsSemisimple G) (h : ∃ c : Cocharacter G.val, c ≠ 0) :
    HasPositiveSplitRank G := by
  have hP := (LinearAlgebraicGroups.Descent.RelativeRank.semisimpleParabolicCriterion G hG).mpr
    ((positive_rank_iff_cocharacter G).mpr h)
  obtain ⟨c, hc⟩ := proper_parabolic_cocharacter G hP
  exact ⟨c, by
    change ¬ (∀ (X : SchemeOver F) (g : X ⟶ G.val.X), Centralizes c g) at hc
    push Not at hc
    exact hc⟩

private theorem finiteIsotropy_of_fixedVectorVertex_odd
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (D : D4Diagram G) (hD : ¬ D.IsTransitive) (h₂ : (2 : F) ≠ 0) :
    HasPositiveSplitRank G := by
  obtain ⟨K, _, _, _, _, ρ, Q, _, horth, ⟨M⟩⟩ :=
    NontrialitarianSpinModels.nontrialitarianSpinModel F G 4 le_rfl
      (absoluteAlmostSimple D hG hSC) hSC (fixedVectorVertex D hD)
  obtain ⟨c, hc⟩ :=
    QuaternionSpinIsotropy.finiteSpinIsotropy G Q M (by simp) (horth h₂) F h₂
  let e := (baseChangeSelfIso F).app G.val
  apply positiveSplitRank_of_nonzeroCocharacter hG
  refine ⟨c ≫ e.hom, ?_⟩
  intro hz
  apply hc
  apply (cancel_mono e.hom).mp
  simpa only [zero_comp] using hz

private theorem finiteGeneration_of_fixedVectorVertex_charTwo
    [CharP F 2] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (D : D4Diagram G) (hD : ¬ D.IsTransitive) (i : MatrixRealization G) :
    Dense {g : PointsIn i F | ∃ p ∈ Specs.Arithmetic.RelativeRayGeneration.unipotentGenerated G,
      toUnit ((testSpec F).obj (Opposite.op (CommAlgCat.of F F))) ≫ p = g} :=
  QuaternionSpinCharacteristicTwo.nontrialitarianLocalGeneration
    F G 4 le_rfl (absoluteAlmostSimple D hG hSC) hSC (fixedVectorVertex D hD) i

open Topology
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (LocalPoints asMatrix)
open private baseChangeMatrixPoints from LinearAlgebraicGroups.Reductive.GeneralLinearStructure

/-- The matrix realization after extending scalars, with the same matrix entries. -/
private def completionRealization {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place) :
    MatrixRealization (baseChangedAlgebraicGroup (D.Completion w) G) where
  size := i.size
  ambient := baseChangedAlgebraicGroup (D.Completion w) i.ambient
  matrix := baseChangeMatrixPoints (D.Completion w) i.matrix
  embedding := (groupBaseChange K (D.Completion w)).map i.embedding
  closed := baseChangeClosedSubgroup K (D.Completion w) i.embedding i.closed

/-- The density statement on the scalar-extended group gives density
in the topology of the original group's local points. -/
private theorem densityFromCompletionModel
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place)
    (localDensity :
      let F := D.Completion w
      let H := baseChangedAlgebraicGroup F G
      Dense {g : PointsIn (completionRealization D i w) F |
        ∃ p ∈ Specs.Arithmetic.RelativeRayGeneration.unipotentGenerated H,
          toUnit ((testSpec F).obj (Opposite.op (CommAlgCat.of F F))) ≫ p = g}) :
    Dense (Specs.Arithmetic.OppositeRadicals.localPlus D i w) := by
  let F := D.Completion w
  let R := CommAlgCat.of F F
  let H := baseChangedAlgebraicGroup F G
  let j := completionRealization D i w
  let e : PointsIn j F ≃ LocalPoints D i w := (baseChangePointGroupEquiv F G.val R).toEquiv
  have hmat : (asMatrix j F : PointsIn j F → _) = asMatrix i F ∘ e := by
    funext g
    change i.matrix.hom.app ((restrictTestAlgebra K F).obj R)
      (baseChangePoint K F i.ambient.val.X R
        (g ≫ ((groupBaseChange K F).map i.embedding).hom.hom)) =
      i.matrix.hom.app ((restrictTestAlgebra K F).obj R)
        (baseChangePoint K F G.val.X R g ≫ i.embedding.hom.hom)
    exact congrArg (fun p => i.matrix.hom.app ((restrictTestAlgebra K F).obj R) p)
      (baseChangePointsSchemeNaturality K F i.embedding.hom.hom R
        (show Points ((groupBaseChange K F).obj G.val).X R from g))
  have he : IsInducing e := ⟨by
    change TopologicalSpace.induced (asMatrix j F) _ =
      TopologicalSpace.induced e (TopologicalSpace.induced (asMatrix i F) _)
    rw [hmat, induced_compose]
    rfl⟩
  let h := e.toHomeomorphOfIsInducing he
  apply (h.surjective.denseRange.dense_image h.continuous localDensity).mono
  rintro _ ⟨g, ⟨p, hp, rfl⟩, rfl⟩
  exact ⟨p, hp, rfl⟩

open private fibreTowerIso from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange

private def extendedSplitComparison (D : D4Diagram G)
    (E : Type u) [Field E] [Algebra F E] :
    (groupBaseChange F (SeparableClosure E)).obj D.pinned.pair.G.val ≅
      (groupBaseChange E (SeparableClosure E)).obj (baseChangedAlgebraicGroup E G).val := by
  let S := SeparableClosure E
  let incl : SeparableClosure F →ₐ[F] S := IsSepClosed.lift
  letI : Algebra (SeparableClosure F) S := incl.toRingHom.toAlgebra
  letI : IsScalarTower F (SeparableClosure F) S :=
    IsScalarTower.of_algebraMap_eq' incl.comp_algebraMap.symm
  exact extendComparison (R := S) D.splitIso ≪≫
    (groupBaseChangeTower (k := F) (K := E) S).app G.val

private theorem simplyConnectedAfterScalarExtension (D : D4Diagram G) (hG : IsSemisimple G)
    (hSC : GeometricallySimplyConnected G) (E : Type u) [Field E] [Algebra F E] :
    GeometricallySimplyConnected (baseChangedAlgebraicGroup E G) :=
  (simpleFormOfConnectedDiagram (K := SeparableClosure E)
    D.datum (referenceCorootSpan D hG hSC) (connectedDiagram D)
    (extendedSplitComparison D E)).2

/-- A marking of absolute type \(D_4\) exists on the actual scalar extension. -/
private theorem diagramAfterScalarExtension (D : D4Diagram G)
    (E : Type u) [Field E] [Algebra F E] :
    Nonempty (D4Diagram (baseChangedAlgebraicGroup E G)) := by
  let S := SeparableClosure E
  let H := baseChangedAlgebraicGroup E G
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.datum.toBased
  obtain ⟨A, P, eF, _⟩ := M.fieldFibre F
  obtain ⟨B, Q, eE, _⟩ := M.fieldFibre E
  obtain ⟨matching⟩ := ((Classification.PinnedEquivalence.pinnedEquivalence.2 F).2.1
    D.pinned.pair P.pinned.pair D.datum P.attached).mpr ⟨P.datumIso.val⟩
  let modelIso : (groupBaseChange F E).obj D.pinned.pair.G.val ≅ Q.pinned.pair.G.val :=
    (groupBaseChange F E).mapIso (matching ≪≫ eF.symm) ≪≫
      ((fibreTowerIso F E).app M.group).symm ≪≫ eE
  let tower := groupBaseChangeTower (k := F) (K := E) S
  let splitIso : (groupBaseChange E S).obj Q.pinned.pair.G.val ≅
      (groupBaseChange E S).obj H.val :=
    (groupBaseChange E S).mapIso modelIso.symm ≪≫
      (tower.app D.pinned.pair.G.val).symm ≪≫
      extendedSplitComparison D E
  obtain ⟨datum, lifts, adjoint, seq, _, _⟩ :=
    LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.automorphismSequences Q.pinned
  let basedIso : D.datum.toBased ⟶ datum.toBased :=
    Q.datumIso ≫ Classification.Pinning.inducedBasedIso (Pinning.PinnedIso.refl Q.pinned)
      Q.attached datum
  let simple := D.simple.trans (basedIso.val.indexEquiv.subtypeEquiv
    (fun a => by
      have h : basedIso.val.indexEquiv '' (D.datum.toBased.base.support : Set D.datum.toBased.I) =
          datum.toBased.base.support := basedIso.property
      exact basedIso.val.indexEquiv.injective.mem_set_image.symm.trans
        (show _ ↔ _ by rw [h])))
  obtain ⟨relative, hrelative⟩ :=
    LinearAlgebraicGroups.Descent.RelativeFormComparison.schemeIsomorphismComparison
      (k := E) (S := S) Q.pinned.pair.G.val H.val
  refine ⟨⟨B, Q.pinned, datum, lifts, adjoint, seq, splitIso, relative splitIso,
    (hrelative _ _).mpr rfl, simple, ?_⟩⟩
  intro i j
  exact basedIso.val.toHom.pairing.trans (D.cartan i j)

open Specs.RelativeRank (HasProperParabolic)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsTrivialSubgroup identitySubgroup)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.BorelProper (IsParabolic)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open private contracting_trivial_of_whole reductive_of_semisimple
  from LinearAlgebraicGroups.Descent.RelativeRank
open private asMatrix_isClosedEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private factors_through_closed_of_dense_rationalSections rationalSourceIso
  from LinearAlgebraicGroups.Relative.RationalDensity
open private trivial_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private subgroupIso_of_same from LinearAlgebraicGroups.RootData.RankOneFlag
open private trivialOfSubgroup from LinearAlgebraicGroups.Reductive.CentralDerived
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private kBorel_smooth_connected from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem positiveSplitRank_of_properParabolic (hP : HasProperParabolic G) :
    HasPositiveSplitRank G := by
  obtain ⟨c, hc⟩ := proper_parabolic_cocharacter G hP
  change ¬ (∀ (X : SchemeOver F) (g : X ⟶ G.val.X), Centralizes c g) at hc
  push Not at hc
  exact ⟨c, hc⟩

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem positiveSplitRank_of_quasiSplit (hG : IsAbsolutelyAlmostSimple G)
    (hq : IsQuasiSplit G) : HasPositiveSplitRank G := by
  obtain ⟨hred, B, hB⟩ := hq
  have hs := (kBorel_smooth_connected G B hB).1
  obtain ⟨hC, hCbor⟩ := hB
  let C := GeometricRadicals.baseChangedSubgroup (AlgebraicClosure F) B hC
  have hP : IsParabolic G B := ⟨hred, hs, hC, C, hCbor, ⟨𝟙 _, Category.id_comp _⟩⟩
  apply positiveSplitRank_of_properParabolic
  refine ⟨B, hP, ?_⟩
  intro hwhole
  have : IsIso B.inclusion := hwhole
  have : IsIso C.inclusion := (groupBaseChange F (AlgebraicClosure F)).map_isIso B.inclusion
  let I := (Grp.forget (SchemeOver (AlgebraicClosure F))).mapIso (asIso C.inclusion)
  have hnorm : IsNormalSubgroup C.inclusion := by
    refine ⟨subgroupConjugation C.inclusion ≫ I.inv, ?_⟩
    change (subgroupConjugation C.inclusion ≫ I.inv) ≫ I.hom = _
    simp
  have hrad := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  obtain ⟨e⟩ := trivialOfSubgroup
    (hrad.2.2 C ⟨hCbor.1.1, hCbor.1.2.1, hnorm⟩ hCbor.1.2.2) hG.1.2.2
  exact hG.2.1 (((Grp.isZero_trivial _).of_iso e).of_iso (asIso C.inclusion).symm)

private theorem unipotentGenerated_eq_bot_of_noProperParabolic (hG : IsReductive G)
    (hP : ¬ HasProperParabolic G) : unipotentGenerated G = ⊥ := by
  apply le_antisymm _ bot_le
  refine iSup_le fun P => iSup_le fun hp => iSup_le fun U => iSup_le fun hu => ?_
  have : IsIso P.inclusion :=
    Classical.byContradiction fun h => hP ⟨P, hp, h⟩
  obtain ⟨c, D, e, V, j, _, _, he, _, _, _, _, _, _, hv, _⟩ :=
    Relative.Parabolics.rationalParabolics.1 G P hp
  have : IsIso (e.hom ≫ D.parabolic.inclusion) := by
    rw [he]
    infer_instance
  have : IsIso D.parabolic.inclusion := IsIso.of_isIso_comp_left e.hom _
  obtain ⟨t⟩ := contracting_trivial_of_whole G hG c D
  obtain ⟨a⟩ := trivialOfSubgroup (hv.2.2 U hu.1 hu.2.1) ⟨j ≪≫ t⟩
  rintro p ⟨g, rfl⟩
  change 𝟙_ (SchemeOver F) ⟶ U.group.X at g
  change g ≫ (U.inclusion ≫ P.inclusion).hom.hom =
    (1 : 𝟙_ (SchemeOver F) ⟶ G.val.X)
  let b := (Grp.forget (SchemeOver F)).mapIso a
  have hg : g = 1 := (cancel_mono b.hom).mp (toUnit_unique _ _)
  exact (congrArg (fun x => x ≫ (U.inclusion ≫ P.inclusion).hom.hom) hg).trans
    (MonObj.one_comp (U.inclusion ≫ P.inclusion).hom.hom)

private theorem nontrivialFieldPoints [Infinite F] (hG : IsAbsolutelyAlmostSimple G)
    (hred : IsReductive G) (i : MatrixRealization G) : ∃ g : PointsIn i F, g ≠ 1 := by
  by_contra! h
  let I := identitySubgroup G
  have : Smooth G.val.X.hom := hred.1
  have : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  obtain ⟨j, hj⟩ := factors_through_closed_of_dense_rationalSections (𝟙 G.val) I id
    (Relative.RationalDensity.reductiveRationalPointsDense F G hred) (fun g => by
      have he : g = 1 := by
        apply (cancel_epi (rationalSourceIso F).inv).mp
        rw [MonObj.comp_one]
        exact h ((rationalSourceIso F).inv ≫ g)
      exact ⟨1, by simp [he, MonObj.one_comp]⟩)
  have := inclusion_mono I
  let e : G.val ≅ I.group := ⟨j, I.inclusion, hj, (cancel_mono I.inclusion).mp (by simp [hj])⟩
  obtain ⟨t⟩ := (trivial_baseChange_iff (K := AlgebraicClosure F) G.val).mpr ⟨e⟩
  exact hG.2.1 ((Grp.isZero_trivial _).of_iso t)

private theorem infiniteOfNonarchimedeanLocalField
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] : Infinite F := by
  have : Infinite (WithZero (Multiplicative ℤ)) :=
    Infinite.of_injective WithZero.exp WithZero.exp_injective
  exact Infinite.of_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F) ∘ ValuativeRel.valuation F)
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
      (ValuativeRel.valuation_surjective (K := F)))

private theorem positiveSplitRank_of_radicalDensity
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (hG : IsAbsolutelyAlmostSimple G) (i : MatrixRealization G)
    (h : Dense {g : PointsIn i F | ∃ p ∈ unipotentGenerated G,
      toUnit ((testSpec F).obj (Opposite.op (CommAlgCat.of F F))) ≫ p = g}) :
    HasPositiveSplitRank G := by
  by_contra hn
  have : Infinite F := infiniteOfNonarchimedeanLocalField
  have : T2Space (PointsIn i F) := (asMatrix_isClosedEmbedding i F).isEmbedding.t2Space
  have hred := reductive_of_semisimple G hG.1
  have hbot := unipotentGenerated_eq_bot_of_noProperParabolic hred
    (fun hp => hn (positiveSplitRank_of_properParabolic hp))
  have hd : Dense ({1} : Set (PointsIn i F)) := h.mono (by
    rintro _ ⟨p, hp, rfl⟩
    have he : p = 1 := by simpa [hbot] using hp
    rw [he, MonObj.comp_one]
    rfl)
  obtain ⟨g, hg⟩ := nontrivialFieldPoints hG hred i
  apply hg
  have hmem := hd g
  rw [isClosed_singleton.closure_eq] at hmem
  exact Set.mem_singleton_iff.mp hmem

private theorem finiteIsotropy_of_fixedVectorVertex_charTwo
    [CharP F 2] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (D : D4Diagram G) (hD : ¬ D.IsTransitive) :
    HasPositiveSplitRank G := by
  obtain ⟨n, L, ⟨m⟩, f, hf⟩ := LinearAlgebraicGroups.faithfulLinearization F G
  let i : MatrixRealization G := ⟨n, L, m, f, hf⟩
  exact positiveSplitRank_of_radicalDensity (absoluteAlmostSimple D hG hSC) i
    (finiteGeneration_of_fixedVectorVertex_charTwo hG hSC D hD i)

theorem finiteIsotropy : FiniteIsotropy.{u} := by
  intro F _ _ _ _ G hG
  obtain ⟨hss, hsc, ⟨D⟩⟩ := hG
  by_cases hD : D.IsTransitive
  · exact positiveSplitRank_of_quasiSplit (absoluteAlmostSimple D hss hsc)
      (finiteQuasiSplit F G hss hsc ⟨D, hD⟩)
  · by_cases h₂ : (2 : F) = 0
    · have : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h₂
      exact finiteIsotropy_of_fixedVectorVertex_charTwo hss hsc D hD
    · exact finiteIsotropy_of_fixedVectorVertex_odd hss hsc D hD h₂

private theorem not_transitive_of_smallAlgClosedExtension (D : D4Diagram G)
    (A : Type u) [Field A] [Algebra F A] [IsAlgClosed A] [Module.Finite F A]
    (hA : Module.finrank F A < 3) : ¬ D.IsTransitive := by
  intro h
  obtain ⟨E, _, hE, _⟩ := cubicOrbitField D h
  let : Module.IsTorsionFree F E := DivisionSemiring.to_moduleIsTorsionFree
  let : Module.IsTorsionFree F A := DivisionSemiring.to_moduleIsTorsionFree
  let e : E →ₐ[F] A := IsAlgClosed.lift
  have hle := e.toLinearMap.finrank_le_finrank_of_injective e.injective
  rw [hE] at hle
  omega

private theorem isAlgClosed_of_complexEquiv (r : F ≃+* ℂ) : IsAlgClosed F := by
  apply IsAlgClosed.of_exists_root
  intro p _ hp
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eval₂_eq_zero r.toRingHom p
    (Polynomial.degree_pos_of_irreducible hp).ne'
  refine ⟨r.symm z, r.injective ?_⟩
  change r.toRingHom (p.eval (r.symm z)) = r.toRingHom 0
  have he : r.toRingHom (r.symm z) = z := r.apply_symm_apply z
  rwa [map_zero, ← Polynomial.eval₂_hom r.toRingHom, he]

private theorem not_transitive_over_real (D : D4Diagram G) (r : F ≃+* ℝ) :
    ¬ D.IsTransitive := by
  let A := ULift.{u} ℂ
  let e : A ≃+* ℂ := ULift.ringEquiv
  let : Algebra F A :=
    (e.symm.toRingHom.comp (Complex.ofRealHom.comp r.toRingHom)).toAlgebra
  have : IsAlgClosed A := isAlgClosed_of_complexEquiv e
  have hc : (algebraMap ℝ ℂ).comp r.toRingHom = e.toRingHom.comp (algebraMap F A) := by
    apply RingHom.ext
    intro x
    exact (e.apply_symm_apply (Complex.ofReal (r x))).symm
  have hc' : e.symm.toRingHom.comp (algebraMap ℝ ℂ) =
      (algebraMap F A).comp r.symm.toRingHom := by
    apply RingHom.ext
    intro x
    change e.symm (Complex.ofReal x) = e.symm (Complex.ofReal (r (r.symm x)))
    rw [r.apply_symm_apply]
  have : Module.Finite F A := Module.Finite.of_equiv_equiv r.symm e.symm hc'.symm
  apply not_transitive_of_smallAlgClosedExtension D A
  rw [Algebra.finrank_eq_of_equiv_equiv r e hc, Complex.finrank_real_complex]
  decide

private theorem completionCases {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (w : D.Place) :
    let F := D.Completion w
    (∃ val : ValuativeRel F, @IsNonarchimedeanLocalField F _ val _) ∨
      (∃ r : F ≃+* ℝ, IsHomeomorph r) ∨ Nonempty (F ≃+* ℂ) := by
  rcases w with w | w
  · exact Or.inl ⟨inferInstanceAs (ValuativeRel (D.FiniteCompletion w)),
      inferInstanceAs (IsNonarchimedeanLocalField (D.FiniteCompletion w))⟩
  · cases D with
    | function F t => exact w.elim
    | number h =>
      change NumberField.InfinitePlace K at w
      rcases w.isReal_or_isComplex with hr | hc
      · obtain ⟨r, hi⟩ := numberRealCompletion w hr
        have he : IsHomeomorph (r : w.Completion → ℝ) :=
          (isHomeomorph_iff_isEmbedding_surjective).mpr ⟨hi.isEmbedding, r.surjective⟩
        exact Or.inr (Or.inl ⟨r, he⟩)
      · obtain ⟨r, _⟩ := numberComplexCompletion w hc
        exact Or.inr (Or.inr ⟨r⟩)

open Specs.QuasiSplitLocalGeneration (IsLocalField)
open Specs.QuasiSplitOrbitAmbientWords (groundPointIso)
open private isKBorel_iff_of_isAlgClosed from LinearAlgebraicGroups.RootData.BorelNormalizer
open private connected_of_geometricallyConnected
  from LinearAlgebraicGroups.RootData.BorelsAndChambers

private theorem quasiSplit_of_algClosed [IsAlgClosed F] (hG : IsReductive G) :
    IsQuasiSplit G := by
  obtain ⟨B, hB⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelExists G hG.1
    (connected_of_geometricallyConnected hG.2.1)
  exact ⟨hG, B, (isKBorel_iff_of_isAlgClosed G B).mpr hB⟩

private theorem radicalDensity_of_quasiSplit [TopologicalSpace F]
    (hF : IsLocalField F) (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (hq : IsQuasiSplit G) (i : MatrixRealization G) :
    Dense {g : PointsIn i F | ∃ p ∈ unipotentGenerated G,
      toUnit ((testSpec F).obj (Opposite.op (CommAlgCat.of F F))) ≫ p = g} := by
  have hgen := QuasiSplitRadicalGeneration.quasiSplitRadicalGeneration hF G hG hSC hq
  apply dense_univ.mono
  intro g _
  let X := (testSpec F).obj (Opposite.op (CommAlgCat.of F F))
  let e : 𝟙_ (SchemeOver F) ≅ X := groundPointIso F
  let x : X ⟶ G.val.X := g
  refine ⟨e.hom ≫ x, hgen.symm ▸ Subgroup.mem_top _, ?_⟩
  change toUnit X ≫ e.hom ≫ x = x
  have he : toUnit X = e.inv := toUnit_unique _ _
  exact (congrArg (fun f : X ⟶ 𝟙_ (SchemeOver F) => f ≫ e.hom ≫ x) he).trans
    (e.inv_hom_id_assoc x)

private theorem radicalDensity_of_nonarchimedean
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (D : D4Diagram G) (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (i : MatrixRealization G) :
    Dense {g : PointsIn i F | ∃ p ∈ unipotentGenerated G,
      toUnit ((testSpec F).obj (Opposite.op (CommAlgCat.of F F))) ≫ p = g} := by
  by_cases htransitive : D.IsTransitive
  · exact radicalDensity_of_quasiSplit
      (Or.inl ⟨inferInstance, inferInstance, inferInstance⟩) hG hSC
      (finiteQuasiSplit F G hG hSC ⟨D, htransitive⟩) i
  by_cases h₂ : (2 : F) = 0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h₂
    exact finiteGeneration_of_fixedVectorVertex_charTwo hG hSC D htransitive i
  · obtain ⟨c, hc⟩ := finiteIsotropy_of_fixedVectorVertex_odd hG hSC D htransitive h₂
    exact OddFixedVectorDensity.oddFixedVectorDensity h₂ (Or.inl ⟨inferInstance, inferInstance⟩)
      G (absoluteAlmostSimple D hG hSC) hSC (fixedVectorVertex D htransitive) c hc i

private theorem radicalDensity_of_real [TopologicalSpace F]
    (r : F ≃+* ℝ) (hr : IsHomeomorph r)
    (D : D4Diagram G) (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (hpos : HasPositiveSplitRank G) (i : MatrixRealization G) :
    Dense {g : PointsIn i F | ∃ p ∈ unipotentGenerated G,
      toUnit ((testSpec F).obj (Opposite.op (CommAlgCat.of F F))) ≫ p = g} := by
  have h₂ : (2 : F) ≠ 0 := by
    intro hz
    apply (two_ne_zero : (2 : ℝ) ≠ 0)
    simpa only [map_ofNat, map_zero] using congrArg r hz
  obtain ⟨c, hc⟩ := hpos
  exact OddFixedVectorDensity.oddFixedVectorDensity h₂ (Or.inr ⟨r, hr⟩)
    G (absoluteAlmostSimple D hG hSC) hSC (fixedVectorVertex D (not_transitive_over_real D r)) c hc i

set_option maxHeartbeats 500000 in
theorem localGeneration : LocalGeneration.{u, v} := by
  intro K _ D G hG hSC htrial i w hpos
  obtain ⟨diagram, _⟩ := htrial
  let F := D.Completion w
  let H := baseChangedAlgebraicGroup F G
  let j := completionRealization D i w
  have hH : IsSemisimple H :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G hG.1 hG.2.1).mpr hG
  have hSCH : GeometricallySimplyConnected H := simplyConnectedAfterScalarExtension diagram hG hSC F
  obtain ⟨completedDiagram⟩ := diagramAfterScalarExtension diagram F
  change HasPositiveSplitRank H at hpos
  apply densityFromCompletionModel D i w
  change Dense {g : PointsIn j F | ∃ p ∈ unipotentGenerated H,
    toUnit ((testSpec F).obj (Opposite.op (CommAlgCat.of F F))) ≫ p = g}
  rcases completionCases D w with ⟨valuation, hlocal⟩ | ⟨r, hr⟩ | hcomplex
  · let : ValuativeRel F := valuation
    let : IsNonarchimedeanLocalField F := hlocal
    exact radicalDensity_of_nonarchimedean (F := F) (G := H) completedDiagram hH hSCH j
  · exact radicalDensity_of_real (F := F) (G := H) r hr completedDiagram hH hSCH hpos j
  · obtain ⟨r⟩ := hcomplex
    let : IsAlgClosed F := isAlgClosed_of_complexEquiv r
    exact radicalDensity_of_quasiSplit (F := F) (G := H) (Or.inr (Or.inr ⟨r⟩)) hH hSCH
      (quasiSplit_of_algClosed (reductive_of_semisimple H hH)) j

theorem globalStrongApproximation : GlobalStrongApproximation.{u, v} :=
  globalStrongApproximation_of_localGeneration localGeneration

end

end LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
