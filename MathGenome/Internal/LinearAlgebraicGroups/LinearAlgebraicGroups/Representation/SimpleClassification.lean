import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedNonvanishing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.BaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import Batteries.Tactic.OpenPrivate

open CategoryTheory AlgebraicGeometry Opposite WithConv Coalgebra
open scoped CategoryTheory.MonObj TensorProduct

universe u

noncomputable section

set_option linter.style.haveILetI false

namespace LinearAlgebraicGroups.Representation.SimpleClassification

open LinearAlgebraicGroups.Specs
open Specs.SimpleClassification
open FlagLineBundle (OppositeBorelPair)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.RootWeightAction (Representation IsPrimitive fixedSpace weightSpace act extendVector
  mem_fixedSpace mem_weightSpace)
open Specs.PrimitiveLine (IsSimple IsEquivariant orbitCoefficient)
open Specs.CyclicHighestWeight (orbitSpan)
open Specs.InducedNonvanishing (Dominant)
open Specs.InducedSocle (IsSimpleSubmodule)
open RationalRepresentations (tensorCoordinate evaluate scalarExtension)
open private pointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle
open private fromCoaction toCoaction from_toCoaction evaluation act_contract contract contract_tmul
  contract_natural coords_injective orbit_le_iff orbit_properties stable_iff stable_map
  generates_of_simple inclusion_equivariant act_eq_scalar_iff coefficientMap
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
open private tensorCoordinate_tmul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

variable {k I J : Type u} [Field k] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {G : AffineAlgebraicGroup k} {A : HopfAlgebraCategory k}

private theorem coactionComparison : Specs.CyclicHighestWeight.CoactionComparison.{u} :=
  CyclicHighestWeight.cyclicHighestWeight.1

private theorem realizes_fromCoaction {V : Type u} [AddCommGroup V] [Module k V]
    (e : specGroup A ≅ G.val) (b : Module.Basis I k V) (δ : RightComodule k A V) :
    Realizes e b δ (fromCoaction (pointIso e) b δ) := by
  intro R g v i
  have h := evaluation (pointIso e) b δ R g (b.equivFun.symm v) i
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

omit [DecidableEq I] in
private theorem tensorCoordinate_basis_transport {V : Type u} [AddCommGroup V] [Module k V]
    (b : Module.Basis I k V) (i : I) (t : (I → k) ⊗[k] A) :
    tensorCoordinate b i ((b.equivFun.symm.toLinearMap.rTensor A) t) =
      tensorCoordinate (Pi.basisFun k I) i t := by
  induction t using TensorProduct.inductionOn with
  | tmul v a =>
    simp only [LinearMap.rTensor_tmul, tensorCoordinate_tmul]
    congr 1
    change b.equivFun (b.equivFun.symm v) i = v i
    rw [LinearEquiv.apply_symm_apply]
  | add t s ht hs => simp [ht, hs]

private theorem realizedCoaction_transport {V : Type u} [AddCommGroup V] [Module k V]
    (e : specGroup A ≅ G.val) (b : Module.Basis I k V)
    (δ : RightComodule k A V) (ρ : Representation G.val I) (h : Realizes e b δ ρ) :
    (b.equivFun.symm.toLinearMap.rTensor A).comp
      (toCoaction (pointIso e) (Pi.basisFun k I) ρ).coaction =
      δ.coaction.comp b.equivFun.symm.toLinearMap := by
  apply LinearMap.ext
  intro v
  apply coords_injective b (CommAlgCat.of k A)
  funext i
  simp only [LinearMap.comp_apply, tensorCoordinate_basis_transport]
  have hm := realizes_fromCoaction e (Pi.basisFun k I)
    (toCoaction (pointIso e) (Pi.basisFun k I) ρ)
    (CommAlgCat.of k A) (AlgHom.id k A) v i
  rw [from_toCoaction, RationalRepresentations.evaluate_id] at hm
  have hv := h (CommAlgCat.of k A) (AlgHom.id k A) v i
  rw [RationalRepresentations.evaluate_id] at hv
  exact (by simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, LinearEquiv.coe_coe] using hm.symm.trans hv)

private theorem realizes_unique {V : Type u} [AddCommGroup V] [Module k V]
    (e : specGroup A ≅ G.val) (b : Module.Basis I k V) (δ : RightComodule k A V)
    (ρ : Representation G.val I) (h : Realizes e b δ ρ) :
    ρ = fromCoaction (pointIso e) b δ := by
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro g
  apply Units.ext
  ext i j
  obtain ⟨a, rfl⟩ :=
    ((forget GrpCat).mapIso ((pointIso e).app R)).toEquiv.surjective g
  let v : I → k := Pi.single j 1
  have hv : extendVector R v = Pi.single j 1 := by
    funext l
    by_cases hl : l = j
    · subst l
      simp [v, extendVector]
    · simp [v, extendVector, Pi.single_eq_of_ne hl]
  have hh := (h R a.ofConv v i).trans
    (realizes_fromCoaction e b δ R a.ofConv v i).symm
  change act ρ R ((pointIso e).hom.app R a) (extendVector R v) i =
    act (fromCoaction (pointIso e) b δ) R ((pointIso e).hom.app R a)
      (extendVector R v) i at hh
  simpa [hv, act, Matrix.mulVec_single] using hh

private theorem action_scalar_forward {ρ : Representation G.val I} {σ : Representation G.val J}
    {f : (I → k) →ₗ[k] (J → k)} (hf : IsEquivariant ρ σ f)
    (R : TestAlgebra k) (g : AdjointRepresentation.GroupPoints G.val R) (c : R) (v : I → k)
    (h : act ρ R g (extendVector R v) = c • extendVector R v) :
    act σ R g (extendVector R (f v)) = c • extendVector R (f v) := by
  apply (act_eq_scalar_iff σ R g (f v) c).mpr
  intro ℓ
  rw [← hf, (act_eq_scalar_iff ρ R g v c).mp h ℓ, map_smul]

private theorem action_scalar_backward {ρ : Representation G.val I} {σ : Representation G.val J}
    {f : (I → k) →ₗ[k] (J → k)} (hf : IsEquivariant ρ σ f) (hi : Function.Injective f)
    (R : TestAlgebra k) (g : AdjointRepresentation.GroupPoints G.val R) (c : R) (v : I → k)
    (h : act σ R g (extendVector R (f v)) = c • extendVector R (f v)) :
    act ρ R g (extendVector R v) = c • extendVector R v := by
  apply (act_eq_scalar_iff ρ R g v c).mpr
  intro ℓ
  apply hi
  rw [hf, (act_eq_scalar_iff σ R g (f v) c).mp h ℓ, map_smul]

private theorem primitive_of_embedding {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    {ρ : Representation G.val I} {σ : Representation G.val J}
    {f : (I → k) →ₗ[k] (J → k)} (hf : IsEquivariant ρ σ f) (hi : Function.Injective f)
    {v : I → k} (h : IsPrimitive σ P.torus P.positive U χ (f v)) :
    IsPrimitive ρ P.torus P.positive U χ v := by
  refine ⟨fun hz ↦ h.1 (hz ▸ f.map_zero), mem_fixedSpace.mpr ?_, mem_weightSpace.mpr ?_⟩
  · intro R g
    simpa only [one_smul] using action_scalar_backward hf hi R _ 1 v
      (by simpa only [one_smul] using mem_fixedSpace.mp h.2.1 R g)
  · intro R t
    exact action_scalar_backward hf hi R _ _ v (mem_weightSpace.mp h.2.2 R t)

private theorem fixedSpace_eq_of_radical {P : OppositeBorelPair G}
    {U U' : ClosedSubgroup P.positive.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (hU' : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U')
    (ρ : Representation G.val I) :
    fixedSpace ρ (U.inclusion ≫ P.positive.inclusion) =
      fixedSpace ρ (U'.inclusion ≫ P.positive.inclusion) := by
  have forward (U₁ U₂ : ClosedSubgroup P.positive.group)
      (h : SchemeDerivedGroup.IsSubgroupOf U₁ U₂) :
      fixedSpace ρ (U₂.inclusion ≫ P.positive.inclusion) ≤
        fixedSpace ρ (U₁.inclusion ≫ P.positive.inclusion) := by
    obtain ⟨j, hj⟩ := h
    intro v hv
    apply mem_fixedSpace.mpr
    intro R g
    have hg := mem_fixedSpace.mp hv R (g ≫ j.hom.hom)
    have he := congrArg (fun f : U₁.group ⟶ P.positive.group ↦ f.hom.hom) hj
    change j.hom.hom ≫ U₂.inclusion.hom.hom = U₁.inclusion.hom.hom at he
    change act ρ R ((g ≫ j.hom.hom) ≫ U₂.inclusion.hom.hom ≫
      P.positive.inclusion.hom.hom) (extendVector R v) = extendVector R v at hg
    change act ρ R (g ≫ U₁.inclusion.hom.hom ≫ P.positive.inclusion.hom.hom)
      (extendVector R v) = extendVector R v
    have he' := (Category.assoc j.hom.hom U₂.inclusion.hom.hom
      P.positive.inclusion.hom.hom).symm.trans
        (congrArg (fun f ↦ f ≫ P.positive.inclusion.hom.hom) he)
    have hpt := (Category.assoc g j.hom.hom
      (U₂.inclusion.hom.hom ≫ P.positive.inclusion.hom.hom)).trans
        (congrArg (fun f ↦ g ≫ f) he')
    exact (congrArg (fun t ↦ act ρ R t (extendVector R v) = extendVector R v) hpt).mp hg
  exact le_antisymm (forward U' U (hU.2.2 U' hU'.1 hU'.2.1))
    (forward U U' (hU'.2.2 U hU.1 hU.2.1))

private theorem simple_of_embedding {ρ : Representation G.val I} {σ : Representation G.val J}
    {f : (I → k) →ₗ[k] (J → k)} (hf : IsEquivariant ρ σ f) (hi : Function.Injective f)
    {M : Submodule k (J → k)} (hr : LinearMap.range f = M)
    (hM : IsSimpleSubmodule σ M) : IsSimple ρ := by
  refine ⟨?_, ?_⟩
  · intro hbot
    apply hM.2.1
    rw [← hr, ← Submodule.map_top, hbot, Submodule.map_bot]
  · intro N hN
    have hle : N.map f ≤ M := by
      rw [← hr, ← Submodule.map_top]
      exact Submodule.map_mono le_top
    have h := hM.2.2 (N.map f) (stable_map hf N hN) hle
    apply h.imp
    · intro hb
      exact Submodule.map_injective_of_injective hi (hb.trans (Submodule.map_bot f).symm)
    · intro ht
      exact Submodule.map_injective_of_injective hi (ht.trans (hr.symm.trans (Submodule.map_top f).symm))

private theorem existsSocleModel (P : OppositeBorelPair G)
    (U : ClosedSubgroup P.positive.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (χ : Character P.torus.group) (hχ : Dominant P χ) :
    Nonempty (SocleModel P U χ) := by
  classical
  obtain ⟨p, Q, a, A, D, e, d, q, φ, c, L, E, ρ, ha, hq, hφ, hc, hfinite, hE, htrans,
    hsocle, hdom⟩ := InducedNonvanishing.nonvanishing k G P χ
  obtain ⟨I, hI, hdec, b, U', hU', comm, D₀, ey, base, hb, σ, hσ, hinj, hW⟩ := hsocle
  letI := hI
  letI := hdec
  obtain ⟨v, hv, hline, hwv, _, ⟨_, _, hunique⟩, _, hM, _⟩ := hW (hdom.mpr hχ)
  let M := orbitSpan σ (𝟙 G.val.X) v
  let x : M := ⟨v, (orbit_properties coactionComparison σ A (pointIso e) v).1⟩
  let δσ := toCoaction (pointIso e) (Pi.basisFun k I) σ
  have hs : δσ.IsSubcomodule M := (stable_iff coactionComparison σ A (pointIso e) M).mp hM.1
  obtain ⟨δ, hδ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction δσ M).mp hs
  let J := ULift.{u} (Fin (Module.finrank k M))
  let bM : Module.Basis J k M := (Module.finBasis k M).reindex Equiv.ulift.symm
  let τ := fromCoaction (pointIso e) bM δ
  let inc := M.subtype.comp bM.equivFun.symm.toLinearMap
  have hi : Function.Injective inc := Subtype.val_injective.comp bM.equivFun.symm.injective
  have hir : LinearMap.range inc = M := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have heqv : IsEquivariant τ σ inc := inclusion_equivariant (pointIso e) σ M bM δ hδ
  have hτ := simple_of_embedding heqv hi hir hM
  have hix : inc (bM.equivFun x) = v := by simp [inc, x]
  have hf := (fixedSpace_eq_of_radical hU hU' σ).trans hline
  have hvprim : IsPrimitive σ P.torus P.positive U χ v :=
    ⟨hv, hf.symm ▸ Submodule.subset_span (Set.mem_singleton v), hwv⟩
  have hprim := primitive_of_embedding heqv hi (hix.symm ▸ hvprim)
  obtain ⟨_, _, high⟩ := CyclicHighestWeight.cyclicHighestWeight.2 G P.reductive P.torus
    P.positive P.split P.maximal P.positiveBorel P.inPositive
  have hgen := generates_of_simple coactionComparison τ A (pointIso e) hτ hprim.1
  have htop := ((high U hU τ χ (bM.equivFun x) hprim).2 hgen).1
  have hcoact :
      let i := b.equivFun.symm.toLinearMap.comp M.subtype
      (i.rTensor A).comp δ.coaction = ρ.coaction.comp i := by
    dsimp only
    rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, hδ, ← LinearMap.comp_assoc,
      realizedCoaction_transport e b ρ σ hσ, LinearMap.comp_assoc]
  exact ⟨{
    projection := p
    A := A
    D := D
    groupIso := e
    borelIso := d
    restriction := q
    character := φ
    coordinate := c
    restriction_spec := hq
    character_spec := hφ
    coordinate_spec := hc
    inducedCoaction := ρ
    leftTranslation := htrans
    I := I
    inducedBasis := b
    inducedAction := σ
    inducedAction_spec := hσ
    socle := M
    socle_simple := hM
    socle_unique := fun N hN ↦ (hunique N hN).trans (hunique M hM).symm
    highestVector := x
    highest_primitive := hvprim
    inducedFixedLine := hf
    socleCoaction := δ
    socleCoaction_spec := hcoact
    J := J
    socleBasis := bM
    socleAction := τ
    socleAction_spec := realizes_fromCoaction e bM δ
    simple := hτ
    highestLine := htop
    primitive := hprim }⟩

private def coordinateIso (G : AffineAlgebraicGroup k) :
    specGroup (coordinateHopf ⟨G.val, G.property.1⟩) ≅ G.val :=
  (affineGroupInclusion k).mapIso (coordinateHopfSpecIso ⟨G.val, G.property.1⟩)

private theorem primitive_change_radical {P : OppositeBorelPair G}
    {U U' : ClosedSubgroup P.positive.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (hU' : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U')
    (ρ : Representation G.val I) (χ : Character P.torus.group) (v : I → k) :
    IsPrimitive ρ P.torus P.positive U χ v ↔
      IsPrimitive ρ P.torus P.positive U' χ v := by
  unfold IsPrimitive
  rw [fixedSpace_eq_of_radical hU hU' ρ]

theorem classification : Classification.{u} := by
  classical
  intro k _ G P U hU
  let A := coordinateHopf ⟨G.val, G.property.1⟩
  let e := pointIso (coordinateIso G)
  obtain ⟨comm, D, U', hU', high, existsPrimitive, uniqueSimple⟩ :=
    PrimitiveLine.primitiveLine G P.reductive P.torus P.positive P.split P.maximal
      P.positiveBorel P.inPositive
  letI := comm
  have dominant {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I)
      (hs : IsSimple ρ) (χ : Character P.torus.group) (h : HasHighestWeight P U ρ χ) :
      Dominant P χ := by
    obtain ⟨v, hv⟩ := h
    have hv' := (primitive_change_radical hU hU' ρ χ v).mp hv
    have hgen := generates_of_simple coactionComparison ρ A e hs hv.1
    have hd := (high ρ χ v hv' hgen).2.2.1
    exact (InducedNonvanishing.dominant_iff_datum
      LinearAlgebraicGroups.Classification.CentralIsogenies.centralIsogenyComparison P D χ).mpr hd
  refine ⟨?_, fun ρ hs χ h ↦ dominant ρ hs χ h, ?_⟩
  · intro I _ _ ρ hs
    obtain ⟨χ, v, hv, huniq⟩ := existsPrimitive ρ hs
    have hχ : HasHighestWeight P U ρ χ := ⟨v, (primitive_change_radical hU hU' ρ χ v).mpr hv⟩
    refine ⟨χ, ⟨dominant ρ hs χ hχ, hχ⟩, ?_⟩
    rintro mu ⟨_, w, hw⟩
    exact (huniq mu w ((primitive_change_radical hU hU' ρ mu w).mp hw)).1
  · intro χ hχ
    obtain ⟨S⟩ := existsSocleModel P U hU χ hχ
    refine ⟨S, ?_⟩
    intro I _ _ ρ hs
    constructor
    · rintro ⟨⟨f, hf⟩⟩
      let v := f.symm (S.socleBasis.equivFun S.highestVector)
      have h : IsPrimitive S.socleAction P.torus P.positive U χ (f v) := by
        dsimp only [v]
        rw [LinearEquiv.apply_symm_apply]
        exact S.primitive
      exact ⟨v, primitive_of_embedding hf f.injective h⟩
    · rintro ⟨v, hv⟩
      have hv' := (primitive_change_radical hU hU' ρ χ v).mp hv
      have hw := (primitive_change_radical hU hU' S.socleAction χ _).mp S.primitive
      obtain ⟨f, hf⟩ := uniqueSimple ρ S.socleAction hs S.simple χ v _ hv' hw
      exact ⟨⟨f, hf⟩⟩

theorem scalarEndomorphisms : ScalarEndomorphisms.{u} := by
  classical
  intro k I _ _ _ G P ρ hs f hf
  let A := coordinateHopf ⟨G.val, G.property.1⟩
  let e := pointIso (coordinateIso G)
  obtain ⟨_, _, U, _, high, existsPrimitive, _⟩ :=
    PrimitiveLine.primitiveLine G P.reductive P.torus P.positive P.split P.maximal
      P.positiveBorel P.inPositive
  obtain ⟨χ, v, hv, _⟩ := existsPrimitive ρ hs
  have hgen := generates_of_simple coactionComparison ρ A e hs hv.1
  have hline := (high ρ χ v hv hgen).1
  have hw : f v ∈ weightSpace ρ P.torus χ := mem_weightSpace.mpr fun R t ↦
    action_scalar_forward hf R _ _ _ (mem_weightSpace.mp hv.2.2 R t)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hline ▸ hw)
  have hker : orbitSpan ρ (𝟙 G.val.X) v ≤ LinearMap.ker (f - a • LinearMap.id) := by
    apply (orbit_le_iff ρ v _).mpr
    intro R g ℓ
    change f (orbitCoefficient ρ R g ℓ v) - a • orbitCoefficient ρ R g ℓ v = 0
    rw [hf, ← ha]
    change coefficientMap ρ R g ℓ (a • v) - a • coefficientMap ρ R g ℓ v = 0
    rw [map_smul, sub_self]
  rw [hgen, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at hker
  refine ⟨a, hker, ?_⟩
  intro b hb
  have h := LinearMap.congr_fun (hb.symm.trans hker) v
  change b • v = a • v at h
  exact (smul_left_injective k hv.1) h

section BaseChange

open Specs.FlagLineBundle (characterCoordinate)
open Specs.CharacterPairing (characterValue)
open Specs.Unipotent (HasInvariantVectors baseChangedAlgebraicGroup)
open RationalRepresentations (IsScalarExtension extendCoaction extendCoaction_isScalarExtension
  restrictCoaction restrictCoaction_coaction)
open TensorProduct.AlgebraTensorModule
open private affinePoint affinePoint_specGroupMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle
open private hopfPreimage specGroupMap_hopfPreimage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable {B : HopfAlgebraCategory k}

private theorem scalar_restriction_iff
    (e : specGroup A ≅ G.val) (b : Module.Basis I k V)
    (δ : RightComodule k A V) (ρ : Representation G.val I) (hρ : Realizes e b δ ρ)
    {H : GroupScheme k} (d : specGroup B ≅ H) (f : H ⟶ G.val) (q : A ⟶ B)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ f) (c : B) (x : V) :
    (q.hom.toAlgHom.toLinearMap.lTensor V) (δ.coaction x) = x ⊗ₜ[k] c ↔
      ∀ (R : TestAlgebra k) (a : B →ₐ[k] R),
        act ρ R (affinePoint R a ≫ d.hom.hom.hom ≫ f.hom.hom)
          (extendVector R (b.equivFun x)) = a c • extendVector R (b.equivFun x) := by
  have hpt (R : TestAlgebra k) (a : B →ₐ[k] R) :
      affinePoint R a ≫ d.hom.hom.hom ≫ f.hom.hom =
        affinePoint R (a.comp q.hom.toAlgHom) ≫ e.hom.hom.hom := by
    have hh := congrArg (fun p : specGroup B ⟶ G.val ↦ p.hom.hom) hq.symm
    change d.hom.hom.hom ≫ f.hom.hom = (specGroupMap q).hom.hom ≫ e.hom.hom.hom at hh
    rw [hh, ← Category.assoc, affinePoint_specGroupMap]
  have hval (R : TestAlgebra k) (a : B →ₐ[k] R) (i : I) :
      act ρ R (affinePoint R a ≫ d.hom.hom.hom ≫ f.hom.hom)
          (extendVector R (b.equivFun x)) i =
        tensorCoordinate b i (a.toLinearMap.lTensor V
          (q.hom.toAlgHom.toLinearMap.lTensor V (δ.coaction x))) := by
    rw [hpt]
    have h := hρ R (a.comp q.hom.toAlgHom) (b.equivFun x) i
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← LinearMap.lTensor_comp_apply]
    exact h
  have hpure (R : TestAlgebra k) (a : B →ₐ[k] R) (i : I) :
      tensorCoordinate b i (x ⊗ₜ[k] a c) = (a c • extendVector R (b.equivFun x)) i := by
    rw [tensorCoordinate_tmul, Algebra.smul_def]
    change algebraMap k R (b.equivFun x i) * a c = a c * algebraMap k R (b.equivFun x i)
    exact mul_comm _ _
  constructor
  · intro h R a
    funext i
    rw [hval, h, LinearMap.lTensor_tmul]
    exact hpure R a i
  · intro h
    let R := CommAlgCat.of k B
    let a : B →ₐ[k] R := AlgHom.id k B
    apply coords_injective b R
    funext i
    have hh := congrFun (h R a) i
    rw [hval, ← hpure R a i] at hh
    have hid : a.toLinearMap = LinearMap.id := rfl
    simpa only [hid, LinearMap.lTensor_id, LinearMap.id_apply, show a c = c from rfl] using hh

private theorem subgroupPoints_surjective {H : GroupScheme k} (d : specGroup B ≅ H)
    (R : TestAlgebra k) :
    Function.Surjective (fun a : B →ₐ[k] R ↦ affinePoint R a ≫ d.hom.hom.hom) := by
  intro g
  obtain ⟨a, rfl⟩ := ((forget GrpCat).mapIso ((pointIso d).app R)).toEquiv.surjective g
  exact ⟨a.ofConv, rfl⟩

private theorem characterValue_at_coordinate {H : GroupScheme k}
    (d : specGroup B ≅ H) (χ : Character H)
    (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ B)
    (hφ : specGroupMap φ = d.hom ≫ χ)
    (R : TestAlgebra k) (a : B →ₐ[k] R) :
    characterValue χ R (affinePoint R a ≫ d.hom.hom.hom) = a (characterCoordinate φ) := by
  have hp : (affinePoint R a ≫ d.hom.hom.hom) ≫ χ.hom.hom =
      affinePoint R (a.comp φ.hom.toAlgHom) := by
    rw [Category.assoc]
    change affinePoint R a ≫ (d.hom ≫ χ).hom.hom = _
    rw [← hφ, affinePoint_specGroupMap]
  unfold characterValue
  rw [hp]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((testSpec k).map (CommAlgCat.ofHom (a.comp φ.hom.toAlgHom)).op)).unop.hom
      (MonoidAlgebra.of k _ DiagonalizableGroups.integerGenerator) = _
  rw [Functor.FullyFaithful.preimage_map]
  rfl

private theorem restricted_eigenvector_map
    (δ : RightComodule k A V) (δ' : RightComodule k A W) (f : V →ₗ[k] W)
    (hf : (f.rTensor A).comp δ.coaction = δ'.coaction.comp f)
    (q : A ⟶ B) (c : B) (x : V) :
    (q.hom.toAlgHom.toLinearMap.lTensor W) (δ'.coaction (f x)) = f x ⊗ₜ[k] c ↔
      (f.rTensor B) ((q.hom.toAlgHom.toLinearMap.lTensor V) (δ.coaction x)) = f x ⊗ₜ[k] c := by
  have hh := LinearMap.congr_fun hf x
  change f.rTensor A (δ.coaction x) = δ'.coaction (f x) at hh
  rw [← hh, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]

private theorem fixedLine_in_socle {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) (C : HopfAlgebraCategory k) (d : specGroup C ≅ U.group)
    (q : S.A ⟶ C) (hq : specGroupMap q ≫ S.groupIso.hom =
      d.hom ≫ U.inclusion ≫ P.positive.inclusion) :
    ∀ x : S.socle, (q.hom.toAlgHom.toLinearMap.lTensor S.socle) (S.socleCoaction.coaction x) =
      x ⊗ₜ[k] (1 : C) ↔ x ∈ Submodule.span k {S.highestVector} := by
  let i := S.inducedBasis.equivFun.symm.toLinearMap.comp S.socle.subtype
  have inj : Function.Injective i := S.inducedBasis.equivFun.symm.injective.comp Subtype.val_injective
  intro x
  have h := restricted_eigenvector_map S.socleCoaction S.inducedCoaction i
    S.socleCoaction_spec q 1 x
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := C) i inj
  have h' : (q.hom.toAlgHom.toLinearMap.lTensor S.socle) (S.socleCoaction.coaction x) =
        x ⊗ₜ[k] (1 : C) ↔
      (q.hom.toAlgHom.toLinearMap.lTensor _) (S.inducedCoaction.coaction (i x)) =
        i x ⊗ₜ[k] (1 : C) := by
    rw [h, ← LinearMap.rTensor_tmul]
    exact hi.eq_iff.symm
  have hv : S.inducedBasis.equivFun (i x) = (x : S.I → k) :=
    S.inducedBasis.equivFun.apply_symm_apply _
  rw [h', scalar_restriction_iff S.groupIso S.inducedBasis S.inducedCoaction S.inducedAction
    S.inducedAction_spec d (U.inclusion ≫ P.positive.inclusion) q hq, hv]
  have eqv : (∀ (R : TestAlgebra k) (a : C →ₐ[k] R),
      act S.inducedAction R
        (affinePoint R a ≫ d.hom.hom.hom ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom)
        (extendVector R x.val) = a 1 • extendVector R x.val) ↔
      x.val ∈ fixedSpace S.inducedAction (U.inclusion ≫ P.positive.inclusion) := by
    rw [mem_fixedSpace]
    constructor
    · intro h₀ R z
      obtain ⟨a, rfl⟩ := subgroupPoints_surjective d R z
      simpa only [Category.assoc, map_one, one_smul] using h₀ R a
    · intro h₀ R a
      simpa only [Category.assoc, map_one, one_smul] using h₀ R (affinePoint R a ≫ d.hom.hom.hom)
  rw [eqv, S.inducedFixedLine, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Subtype.ext ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, congrArg Subtype.val ha⟩⟩

private theorem weightLine_in_socle {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) (E : HopfAlgebraCategory k) (d : specGroup E ≅ P.torus.group)
    (q : S.A ⟶ E) (hq : specGroupMap q ≫ S.groupIso.hom = d.hom ≫ P.torus.inclusion)
    (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ E)
    (hφ : specGroupMap φ = d.hom ≫ χ) :
    ∀ x : S.socle, (q.hom.toAlgHom.toLinearMap.lTensor S.socle) (S.socleCoaction.coaction x) =
      x ⊗ₜ[k] characterCoordinate φ ↔ x ∈ Submodule.span k {S.highestVector} := by
  intro x
  rw [scalar_restriction_iff S.groupIso S.socleBasis S.socleCoaction S.socleAction
    S.socleAction_spec d P.torus.inclusion q hq]
  have eqv : (∀ (R : TestAlgebra k) (a : E →ₐ[k] R),
      act S.socleAction R (affinePoint R a ≫ d.hom.hom.hom ≫ P.torus.inclusion.hom.hom)
        (extendVector R (S.socleBasis.equivFun x)) =
          a (characterCoordinate φ) • extendVector R (S.socleBasis.equivFun x)) ↔
      S.socleBasis.equivFun x ∈ weightSpace S.socleAction P.torus χ := by
    rw [mem_weightSpace]
    constructor
    · intro h₀ R z
      obtain ⟨a, rfl⟩ := subgroupPoints_surjective d R z
      simpa only [Category.assoc, characterValue_at_coordinate d χ φ hφ] using h₀ R a
    · intro h₀ R a
      simpa only [Category.assoc, characterValue_at_coordinate d χ φ hφ] using
        h₀ R (affinePoint R a ≫ d.hom.hom.hom)
  rw [eqv, S.highestLine, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, S.socleBasis.equivFun.injective ((map_smul _ _ _).trans ha)⟩,
    fun ⟨a, ha⟩ ↦ ⟨a, (map_smul _ _ _).symm.trans (congrArg S.socleBasis.equivFun ha)⟩⟩

variable {K : Type u} [Field K] [Algebra k K]

private theorem extendedHopfMap_linear (q : A ⟶ B) :
    (extendedHopfMap K q).hom.toAlgHom.toLinearMap = q.hom.toAlgHom.toLinearMap.baseChange K := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a b
  rfl

set_option maxSynthPendingDepth 4 in
private theorem scalarEquations_baseChange
    (δ : RightComodule k A V) (δK : RightComodule K (scalarExtension A K) (K ⊗[k] V))
    (hext : IsScalarExtension A δ δK) (q : A ⟶ B) (c : B) (v : V)
    (hline : ∀ x, (q.hom.toAlgHom.toLinearMap.lTensor V) (δ.coaction x) =
      x ⊗ₜ[k] c ↔ x ∈ Submodule.span k {v}) :
    {x | (q.hom.toAlgHom.toLinearMap.baseChange K).lTensor (K ⊗[k] V) (δK.coaction x) =
        x ⊗ₜ[K] ((1 : K) ⊗ₜ[k] c)} = (Submodule.span K {(1 : K) ⊗ₜ[k] v} : Set _) := by
  let f := (q.hom.toAlgHom.toLinearMap.lTensor V).comp δ.coaction -
    (TensorProduct.mk k V B).flip c
  let pK : (K ⊗[k] V) →ₗ[K] (K ⊗[k] V) ⊗[K] (K ⊗[k] B) :=
    ((q.hom.toAlgHom.toLinearMap.baseChange K).lTensor (K ⊗[k] V)).comp δK.coaction
  let wK : (K ⊗[k] V) →ₗ[K] (K ⊗[k] V) ⊗[K] (K ⊗[k] B) :=
    (TensorProduct.mk K (K ⊗[k] V) (K ⊗[k] B)).flip ((1 : K) ⊗ₜ[k] c)
  let fK := pK - wK
  have hker : f.ker = Submodule.span k {v} := by
    ext x
    simp only [LinearMap.mem_ker, f, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.flip_apply, TensorProduct.mk_apply, sub_eq_zero, hline]
  have hcomm (a : K) (t : V ⊗[k] A) :
      (q.hom.toAlgHom.toLinearMap.baseChange K).lTensor (K ⊗[k] V)
        (distribBaseChange k K V A (a ⊗ₜ[k] t)) =
      distribBaseChange k K V B (a ⊗ₜ[k] q.hom.toAlgHom.toLinearMap.lTensor V t) := by
    induction t using TensorProduct.inductionOn with
    | tmul x z => simp only [distribBaseChange_tmul, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul]
    | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
  have hfK : fK = (distribBaseChange k K V B).toLinearMap.comp (f.baseChange K) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change δK.coaction = _ at hext
    simp only [fK, pK, wK, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, LinearMap.baseChange_tmul, hext, LinearEquiv.coe_coe, hcomm, f,
      TensorProduct.tmul_sub, map_sub, distribBaseChange_tmul]
  have hkerK : fK.ker = Submodule.span K {(1 : K) ⊗ₜ[k] v} := by
    have hflat : (f.baseChange K).ker = f.ker.baseChange K := Module.Flat.ker_lTensor_eq K K f
    rw [hfK, LinearMap.ker_comp_of_ker_eq_bot _ (LinearEquiv.ker _),
      hflat, hker, Submodule.baseChange_span, Set.image_singleton]
    rfl
  ext x
  change _ ↔ x ∈ Submodule.span K {(1 : K) ⊗ₜ[k] v}
  rw [← hkerK]
  simp only [LinearMap.mem_ker, fK, pK, wK, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, sub_eq_zero]
  rfl

private theorem contracts_mem_subcomodule {δ : RightComodule k A V} {M : Submodule k V}
    (hM : δ.IsSubcomodule M) (x : V) (hx : x ∈ M) (ℓ : A →ₗ[k] k) :
    contract ℓ (δ.coaction x) ∈ M := by
  obtain ⟨t, ht⟩ := hM ⟨x, hx⟩
  change M.subtype.rTensor A t = δ.coaction x at ht
  rw [← ht, ← contract_natural]
  exact (contract ℓ t).property

private theorem contract_one_tmul_baseChange
    (δ : RightComodule k A V) (δK : RightComodule K (scalarExtension A K) (K ⊗[k] V))
    (hext : IsScalarExtension A δ δK) (v : V) (ℓ : A →ₗ[k] k) :
    let ℓK := (TensorProduct.AlgebraTensorModule.rid k K K).toLinearMap.comp (ℓ.baseChange K)
    contract ℓK (δK.coaction ((1 : K) ⊗ₜ[k] v)) =
      (1 : K) ⊗ₜ[k] contract ℓ (δ.coaction v) := by
  dsimp only
  change δK.coaction = _ at hext
  rw [hext, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe]
  generalize δ.coaction v = t
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
    simp only [distribBaseChange_tmul, contract_tmul, LinearMap.comp_apply,
      LinearMap.baseChange_tmul, LinearEquiv.coe_coe, rid_tmul]
    change (ℓ a • (1 : K)) • ((1 : K) ⊗ₜ[k] x) = (1 : K) ⊗ₜ[k] (ℓ a • x)
    rw [TensorProduct.smul_tmul' (R := k) (R' := K), smul_eq_mul, mul_one]
    exact TensorProduct.smul_tmul (R := k) (ℓ a) (1 : K) x
  | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]

private theorem socle_generator_baseChange {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group} (S : SocleModel P U χ)
    (δK : RightComodule K (scalarExtension S.A K) (K ⊗[k] S.socle))
    (hext : IsScalarExtension S.A S.socleCoaction δK) (M : Submodule K (K ⊗[k] S.socle))
    (hM : δK.IsSubcomodule M) (hv : (1 : K) ⊗ₜ[k] S.highestVector ∈ M) : M = ⊤ := by
  let v := S.highestVector
  let N : Submodule k S.socle := Submodule.span k
    (Set.range fun ℓ : S.A →ₗ[k] k ↦ contract ℓ (S.socleCoaction.coaction v))
  have hN : N = ⊤ := by
    let b := S.socleBasis
    let w := b.equivFun v
    let e := pointIso S.groupIso
    have hw : w ≠ 0 := S.primitive.1
    have hgen := generates_of_simple coactionComparison S.socleAction S.A e S.simple hw
    have hle : orbitSpan S.socleAction (𝟙 G.val.X) w ≤ N.map b.equivFun.toLinearMap := by
      apply (orbit_le_iff S.socleAction w _).mpr
      intro R g ℓ
      obtain ⟨a, rfl⟩ := ((forget GrpCat).mapIso (e.app R)).toEquiv.surjective g
      have h := act_contract e b S.socleCoaction R a.ofConv ℓ v
      rw [← realizes_unique S.groupIso b S.socleCoaction S.socleAction S.socleAction_spec] at h
      change orbitCoefficient S.socleAction R (e.hom.app R a) ℓ w = _ at h
      exact Submodule.mem_map.mpr
        ⟨_, Submodule.subset_span ⟨ℓ.comp a.ofConv.toLinearMap, rfl⟩, h.symm⟩
    rw [hgen, top_le_iff] at hle
    exact Submodule.map_injective_of_injective b.equivFun.injective
      (hle.trans (Submodule.map_top _ |>.trans (LinearEquiv.range b.equivFun)).symm)
  have hbase : N.baseChange K ≤ M := by
    rw [Submodule.baseChange_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨ℓ, rfl⟩, rfl⟩
    change (1 : K) ⊗ₜ[k] contract ℓ (S.socleCoaction.coaction v) ∈ M
    rw [← contract_one_tmul_baseChange S.socleCoaction δK hext v ℓ]
    exact contracts_mem_subcomodule hM _ hv _
  rw [hN, Submodule.baseChange_top] at hbase
  exact top_unique hbase

private theorem hopfPreimage_comp_iso {A B : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (f : specGroup B ⟶ G.val) :
    specGroupMap (hopfPreimage (f ≫ e.inv)) ≫ e.hom = f := by
  rw [specGroupMap_hopfPreimage, Category.assoc, e.inv_hom_id, Category.comp_id]

theorem absoluteSimplicity : AbsoluteSimplicity.{u} := by
  classical
  intro k _ G P U hU χ S
  let Ualg := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup P.positive) U
  obtain ⟨C, ⟨eU₀⟩, _⟩ := hU.2.1
  let eU : specGroup C ≅ U.group := eU₀
  let Talg := closedSubgroupAlgebraicGroup (G := G) P.torus
  let E := coordinateHopf ⟨Talg.val, Talg.property.1⟩
  let eT : specGroup E ≅ P.torus.group := coordinateIso Talg
  let qU := hopfPreimage ((eU.hom ≫ U.inclusion ≫ P.positive.inclusion) ≫ S.groupIso.inv)
  let qT := hopfPreimage ((eT.hom ≫ P.torus.inclusion) ≫ S.groupIso.inv)
  let φ := hopfPreimage (eT.hom ≫ χ)
  have hqU : specGroupMap qU ≫ S.groupIso.hom = eU.hom ≫ U.inclusion ≫ P.positive.inclusion :=
    hopfPreimage_comp_iso S.groupIso _
  have hqT : specGroupMap qT ≫ S.groupIso.hom = eT.hom ≫ P.torus.inclusion :=
    hopfPreimage_comp_iso S.groupIso _
  have hφ : specGroupMap φ = eT.hom ≫ χ := specGroupMap_hopfPreimage _
  refine ⟨C, E, eU, eT, qU, qT, φ, hqU, hqT, hφ, ?_⟩
  intro K _ _
  let δ := extendCoaction (K := K) S.A S.socleCoaction
  have hδ := extendCoaction_isScalarExtension (K := K) S.A S.socleCoaction
  let v := (1 : K) ⊗ₜ[k] S.highestVector
  have hv : v ≠ 0 := by
    intro hz
    have hinj := Module.Flat.tensorProduct_mk_injective k S.socle K
    have h0 := hinj (hz.trans ((TensorProduct.mk k K S.socle 1).map_zero).symm)
    exact S.primitive.1 (h0 ▸ S.socleBasis.equivFun.map_zero)
  have hu := scalarEquations_baseChange S.socleCoaction δ hδ qU 1 S.highestVector
    (fixedLine_in_socle S C eU qU hqU)
  have ht := scalarEquations_baseChange S.socleCoaction δ hδ qT (characterCoordinate φ)
    S.highestVector (weightLine_in_socle S E eT qT hqT φ hφ)
  refine ⟨δ, hδ, (Submodule.ne_bot_iff _).mpr ⟨v, Submodule.mem_top, hv⟩,
    ?_, hv, hu, ht⟩
  intro M hM
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨δM, hδM⟩ := (RightComodule.isSubcomodule_iff_exists_coaction δ M).mp hM
    haveI : Nontrivial M := by
      obtain ⟨x, hx, hne⟩ := (Submodule.ne_bot_iff _).mp hbot
      exact ⟨⟨⟨x, hx⟩, 0, fun hz ↦ hne (congrArg Subtype.val hz)⟩⟩
    let UalgK := baseChangedAlgebraicGroup K Ualg
    let isoUK : specGroup (scalarExtension C K) ≅ UalgK.val :=
      extendedGroupIso K C ≪≫ (groupBaseChange k K).mapIso eU
    have hCK : HasInvariantVectors (scalarExtension C K) :=
      (LinearAlgebraicGroups.Unipotent.unipotenceCriteria UalgK (scalarExtension C K) isoUK).1.mp
        ((LinearAlgebraicGroups.Unipotent.unipotenceFieldExtension (K := K) Ualg).mpr hU.2.1)
    let qUK : scalarExtension S.A K ⟶ scalarExtension C K := extendedHopfMap K qU
    let τ : RightComodule K (scalarExtension C K) M := restrictCoaction qUK δM
    obtain ⟨x, hx, hfix⟩ := hCK M τ
    have hτ : τ.coaction x = x ⊗ₜ[K] (1 : scalarExtension C K) := by
      have h0 := (RationalRepresentations.invariantKernel (scalarExtension C K) τ x).mpr hfix
        (CommAlgCat.of K (scalarExtension C K)) (AlgHom.id K (scalarExtension C K))
      rwa [RationalRepresentations.evaluate_id] at h0
    rw [show τ = restrictCoaction qUK δM from rfl, restrictCoaction_coaction, LinearMap.comp_apply] at hτ
    have h := (restricted_eigenvector_map δM δ M.subtype hδM qUK 1 x).mpr
      (by rw [hτ, LinearMap.rTensor_tmul])
    rw [show qUK.hom.toAlgHom.toLinearMap = qU.hom.toAlgHom.toLinearMap.baseChange K from
      extendedHopfMap_linear qU] at h
    have hxline : x.val ∈ Submodule.span K {v} := by
      change x.val ∈ (Submodule.span K {v} : Set _)
      rw [← hu]
      exact h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxline
    have ha0 : a ≠ 0 := by
      intro hz
      apply hx
      apply Subtype.ext
      exact ha.symm.trans (by rw [hz, zero_smul]; rfl)
    have hvM : v ∈ M := by
      have hh := M.smul_mem a⁻¹ x.property
      rwa [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul] at hh
    exact socle_generator_baseChange S δ hδ M hM hvM

end BaseChange

section WeightLattice

open Specs.SimplyConnectedLattice (corootLatticeOf corootLattice)
open private restrictCharacters_injective restrictCharacters_surjective corootDatum
  semisimple_iff_corootFullRank splitBorelPair corootLattice_splitBorelPair dualSurjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies

theorem simplyConnectedWeightLattice : SimplyConnectedWeightLattice.{u} := by
  intro k _ G hG T hs hm _ D
  letI := D.freeCharacters
  letI := D.finiteCharacters
  letI := D.freeCocharacters
  letI := D.finiteCocharacters
  let P := splitBorelPair G (reductive_of_semisimple G hG) T hs hm
  let E := LinearAlgebraicGroups.Classification.Pinning.attachedDatum P
  have hE := (semisimple_iff_corootFullRank P E).mp hG
  rw [corootLattice_splitBorelPair G (reductive_of_semisimple G hG) T hs hm D] at hE
  let C := corootLatticeOf D
  have finiteQuot : Finite (Additive (Cocharacter T.group) ⧸ C) :=
    (Submodule.finiteQuotient_iff C).mpr hE
  have hi : Function.Injective (weightLatticeMap D) :=
    restrictCharacters_injective D.rootDatum finiteQuot
  have hcrit := LinearAlgebraicGroups.Classification.SimplyConnectedLattice.latticeCriterion
    G hG T hs hm D
  refine ⟨hi, ?_⟩
  rw [hcrit]
  refine ⟨?_, restrictCharacters_surjective D.rootDatum⟩
  intro h
  let E' := corootDatum D.rootDatum hi
  have hc : Function.Surjective C.subtype :=
    dualSurjective D.rootDatum.toLinearMap.flip E'.toLinearMap.flip C.subtype (weightLatticeMap D)
      (fun _ _ ↦ rfl) ((Submodule.range_subtype C).symm ▸ finiteQuot) h
  simpa only [Submodule.range_subtype] using LinearMap.range_eq_top.mpr hc

end WeightLattice

end LinearAlgebraicGroups.Representation.SimpleClassification
