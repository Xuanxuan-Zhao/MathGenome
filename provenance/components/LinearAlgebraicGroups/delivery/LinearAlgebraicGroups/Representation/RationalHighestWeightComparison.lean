import Specs.LinearAlgebraicGroups.Representation.RationalHighestWeightComparison
import LinearAlgebraicGroups.Representation.SimpleClassification
import LinearAlgebraicGroups.Representation.LieStableSubspaces
import LinearAlgebraicGroups.RootData.OrderedRootProducts
import Mathlib.Algebra.Lie.Matrix
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.RationalHighestWeightComparison

open _root_.LinearAlgebraicGroups.Specs
open Specs.RationalHighestWeightComparison
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (adjointWeightVectors)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.OrderedRootProducts (RootSubgroupFamily product rootProduct Enumerates)
open Specs.RootWeightAction (Representation act extendVector IsPrimitive mem_weightSpace mem_fixedSpace)
open Specs.PrimitiveLine (IsSimple IsStable)
open Specs.SimpleClassification (Realizes)

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open private dualKernelIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private pointIso from LinearAlgebraicGroups.Representation.InducedSocle
open private fromCoaction toCoaction from_toCoaction stable_iff
  from LinearAlgebraicGroups.Representation.PrimitiveLine
open private realizes_fromCoaction realizedCoaction_transport
  from LinearAlgebraicGroups.Representation.SimpleClassification
open private tangent_evaluation lieTangentEquiv
  from LinearAlgebraicGroups.Representation.LieStableSubspaces
open private tensorCoordinate_tmul from LinearAlgebraicGroups.Affine.RationalRepresentations
open private matrixDifferentialLinear matrixDifferential_bracket
  from LinearAlgebraicGroups.Affine.LieBracket

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {I : Type u} [Fintype I] [DecidableEq I]
  {V : Type u} [AddCommGroup V] [Module k V]

private abbrev dualTest (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

private abbrev presentedTangent {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (x : Lie k G.val) :=
  tangentPointOfLie A (mapPointKernel e.inv x)

private theorem point_of_presentedTangent {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (x : Lie k G.val) :
    (testSpec k).map (CommAlgCat.ofHom (presentedTangent e x).val).op ≫ e.hom.hom.hom =
      x.toMul.val := by
  let d := dualKernelIso ((groupPointsFunctor k).mapIso e)
  let q := dualKernelIso (hopfSpecPointIso A)
  have h : q ((hopfKernelLifts A).symm (presentedTangent e x)) = d.symm x := by
    change q ((hopfKernelLifts A).symm (lieTangentEquiv A (d.symm x))) = d.symm x
    simp [lieTangentEquiv, q]
  have eq := congrArg (fun y : Lie k (specGroup A) => (d y).toMul.val) h
  rw [AddEquiv.apply_symm_apply] at eq
  exact eq

/-- The coefficient of the dual-number parameter in the orbit of a vector
is the coordinate of the differentiated coaction. -/
private theorem differentiated_coordinate {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (b : Module.Basis I k V) (δ : RightComodule k A V)
    {ρ : Representation G.val I} (hr : Realizes e b δ ρ) (x : Lie k G.val) (v : V) (i : I) :
    b.equivFun (differentiatedCoaction A δ (presentedTangent e x) v) i =
      (act ρ (dualTest k) x.toMul.val (extendVector (dualTest k) (b.equivFun v)) i).snd := by
  have h := hr (dualTest k) (presentedTangent e x).val (b.equivFun v) i
  rw [point_of_presentedTangent, LinearEquiv.symm_apply_apply, tangent_evaluation,
    map_add, tensorCoordinate_tmul, tensorCoordinate_tmul] at h
  have hs := congrArg TrivSqZeroExt.snd h
  simpa only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_one,
    smul_zero, zero_add, TrivSqZeroExt.snd_inr, smul_eq_mul, mul_one, mul_zero,
    Module.Basis.coord_apply, Module.Basis.equivFun_apply] using hs.symm

private theorem rootProduct_identity_point {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (R : TestAlgebra k) (l : List (Specs.AbstractPairing.Root T)) :
    ∃ p : Points (product (fun α => (U α).val.group.X) l) R, p ≫ rootProduct U l = 1 := by
  induction l with
  | nil => exact ⟨toUnit _, MonObj.comp_one _⟩
  | cons α l ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨lift 1 p, ?_⟩
    simp only [rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hp, mul_one,
      MonObj.one_comp]

private theorem rootProduct_contains {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (R : TestAlgebra k) {α : Specs.AbstractPairing.Root T} (y : GroupPoints (U α).val.group R)
    (l : List (Specs.AbstractPairing.Root T)) (hα : α ∈ l) :
    ∃ p : Points (product (fun β => (U β).val.group.X) l) R,
      p ≫ rootProduct U l = y ≫ (U α).val.inclusion.hom.hom := by
  induction l with
  | nil => simp at hα
  | cons β l ih =>
    rcases List.mem_cons.mp hα with rfl | hα
    · obtain ⟨p, hp⟩ := rootProduct_identity_point U R l
      refine ⟨lift y p, ?_⟩
      simp only [rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hp, mul_one]
    · obtain ⟨p, hp⟩ := ih hα
      refine ⟨lift 1 p, ?_⟩
      simp only [rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hp, MonObj.one_comp,
        one_mul]

/-- Choose the unipotent radical so that every positive root tangent is the
image of a point of the radical over the dual numbers. -/
private theorem positiveTangent_points (P : OppositeBorelPair G) :
    ∃ U : ClosedSubgroup P.positive.group,
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U ∧
      ∀ α ∈ subgroupRoots P.torus P.positive, ∀ x ∈ adjointWeightVectors P.torus α.val,
        ∃ p : GroupPoints U.group (dualTest k),
          p ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom = x.toMul.val := by
  classical
  obtain ⟨hfin, _, _⟩ := RootData.OrderedRootProducts.contractingProduct G P.reductive P.torus
    P.split P.maximal
  letI := hfin.fintype
  have hroot (α : Specs.AbstractPairing.Root P.torus) :
      ∃ H : {H : ClosedSubgroup G.val // Specs.RootGroups.IsRootSubgroup P.torus H α.val},
        Set.range (mapPointKernel H.val.inclusion) = adjointWeightVectors P.torus α.val := by
    obtain ⟨H, hH, _, heq, _, _⟩ :=
      ((RootData.RootGroups.rootSubgroups G P.reductive P.torus P.split P.maximal).2
        α.val α.property).2.2
    exact ⟨⟨H, hH⟩, heq⟩
  let roots : RootSubgroupFamily P.torus := fun α => (hroot α).choose
  obtain ⟨U, hU, hprod⟩ := RootData.OrderedRootProducts.borelRadicalProduct
    G P.reductive P.torus P.split P.maximal P.positive P.positiveBorel P.inPositive
  let S := subgroupRoots P.torus P.positive
  let l := (Set.toFinite S).toFinset.toList
  have hl : Enumerates l S := ⟨Finset.nodup_toList _, by intro α; simp only [l, Finset.mem_toList, Set.Finite.mem_toFinset]⟩
  obtain ⟨E, hE⟩ := hprod roots l hl
  refine ⟨U, hU, fun α hα x hx => ?_⟩
  have hx' : x ∈ Set.range (mapPointKernel (roots α).val.inclusion) :=
    (hroot α).choose_spec.symm ▸ hx
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨p, hp⟩ := rootProduct_contains roots (dualTest k) y.toMul.val l ((hl.2 α).mpr hα)
  refine ⟨p ≫ E.hom, ?_⟩
  change (p ≫ E.hom) ≫ U.inclusion.hom.hom ≫ P.positive.inclusion.hom.hom = _
  rw [Category.assoc, hE, hp]
  rfl

private theorem highest_of_primitive [LieRing (Lie k G.val)] [LieRingModule (Lie k G.val) V]
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val) (b : Module.Basis I k V)
    (δ : RightComodule k A V) {ρ : Representation G.val I} (hr : Realizes e b δ ρ)
    (ha : AgreesWithCoaction e δ) {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    (hU : ∀ α ∈ subgroupRoots P.torus P.positive, ∀ x ∈ adjointWeightVectors P.torus α.val,
      ∃ p : GroupPoints U.group (dualTest k),
        p ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom = x.toMul.val)
    {χ : Character P.torus.group} {v : V} (hv : IsPrimitive ρ P.torus P.positive U χ (b.equivFun v)) :
    IsHighestVector P χ v := by
  refine ⟨fun hz => hv.1 (by simp [hz]), ?_, ?_⟩
  · intro t
    apply b.equivFun.injective
    funext i
    rw [← ha, differentiated_coordinate e b δ hr]
    have ht := congrFun (mem_weightSpace.mp hv.2.2 (dualTest k) t.toMul.val) i
    change act ρ (dualTest k) (mapPointKernel P.torus.inclusion t).toMul.val
      (extendVector (dualTest k) (b.equivFun v)) i = _ at ht
    rw [ht]
    simp [extendVector, TrivSqZeroExt.snd_mul, smul_eq_mul, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  · intro α hα x hx
    obtain ⟨p, hp⟩ := hU α hα x hx
    apply b.equivFun.injective
    funext i
    rw [← ha, differentiated_coordinate e b δ hr, ← hp,
      mem_fixedSpace.mp hv.2.1 (dualTest k) p]
    simp [extendVector, TrivSqZeroExt.algebraMap_eq_inl]

section Simplicity

variable [CharZero k] [ConnectedSpace G.val.X.left]
  [LieRing (Lie k G.val)] [LieRingModule (Lie k G.val) V] [FiniteDimensional k V]

private theorem subcomodule_iff_lie {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (δ : RightComodule k A V) (ha : AgreesWithCoaction e δ)
    (W : Submodule k V) :
    δ.IsSubcomodule W ↔ ∀ (x : Lie k G.val) (v : W), ⁅x, (v : V)⁆ ∈ W := by
  have h := LinearAlgebraicGroups.lieStableSubspacesOfPresentation G e δ W
  constructor
  · intro hW x v
    rw [← ha x (v : V)]
    exact h.mp hW x v
  · intro hW
    apply h.mpr
    intro x v
    rw [ha x (v : V)]
    exact hW x v

private theorem simple_of_irreducible {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (b : Module.Basis I k V) (δ : RightComodule k A V)
    (ha : AgreesWithCoaction e δ) [LieModule.IsIrreducible k (Lie k G.val) V] :
    IsSimple (fromCoaction (pointIso e) b δ) := by
  let ρ := fromCoaction (pointIso e) b δ
  let τ := toCoaction (pointIso e) (Pi.basisFun k I) ρ
  let f := b.equivFun.symm
  letI : Nontrivial V := (LieSubmodule.nontrivial_iff k (Lie k G.val) V).mp inferInstance
  letI : Nontrivial (I → k) := b.equivFun.injective.nontrivial
  refine ⟨top_ne_bot, fun M hM => ?_⟩
  have hτ : τ.IsSubcomodule M :=
    (stable_iff CyclicHighestWeight.cyclicHighestWeight.1 ρ A (pointIso e) M).mp hM
  have hcomm := realizedCoaction_transport e b δ ρ (realizes_fromCoaction e b δ)
  let W := M.map f.toLinearMap
  have hW : δ.IsSubcomodule W := by
    intro v
    obtain ⟨w, hw, heq⟩ := Submodule.mem_map.mp v.property
    obtain ⟨z, hz⟩ := hτ ⟨w, hw⟩
    let j : M →ₗ[k] W := (f.toLinearMap.comp M.subtype).codRestrict W
      (fun w => Submodule.mem_map.mpr ⟨w, w.property, rfl⟩)
    have hj : W.subtype.comp j = f.toLinearMap.comp M.subtype := rfl
    refine ⟨j.rTensor A z, ?_⟩
    rw [← LinearMap.rTensor_comp_apply, hj, LinearMap.rTensor_comp_apply, hz]
    exact (LinearMap.congr_fun hcomm w).trans (congrArg δ.coaction heq)
  let N : LieSubmodule k (Lie k G.val) V :=
    { W with lie_mem := fun {x v} hv => (subcomodule_iff_lie e δ ha W).mp hW x ⟨v, hv⟩ }
  rcases IsSimpleOrder.eq_bot_or_eq_top N with h | h
  · left
    exact (Submodule.map_eq_bot_iff (e := f)).mp
      (congrArg (fun N : LieSubmodule k (Lie k G.val) V => N.toSubmodule) h)
  · right
    exact (Submodule.map_eq_top_iff (e := f)).mp
      (congrArg (fun N : LieSubmodule k (Lie k G.val) V => N.toSubmodule) h)

end Simplicity

section MatrixAction

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The tangent of a finite matrix representation is a Lie algebra map. -/
private def pointActionDifferential (s : IdentityLieStructure G.val)
    (ρ : Representation G.val I) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Lie k G.val →ₗ⁅k⁆ Matrix I I k := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let M := StandardGroups.generalLinearGroup k I
  let glIso := StandardGroups.generalLinearGroupPointsIso k I
  let E := groupHomEquiv G.val M.val G.property.1
  let f := E.symm (ρ ≫ glIso.inv)
  letI : IsAffine G.val.X.left := G.property.1
  let d := matrixDifferentialLinear f glIso
  refine
    { toFun := InfinitesimalCommutator.matrixDifferential f glIso
      map_add' := fun x y => ?_
      map_smul' := fun a x => ?_
      map_lie' := fun {x y} => matrixDifferential_bracket f glIso s.commutator_law x y }
  · have h := congrArg (fun law : AddGroup (PointKernel G.val) => law.toAdd.add x y) s.group_law
    exact (congrArg (InfinitesimalCommutator.matrixDifferential f glIso) h).trans (map_add d x y)
  · have h := congrFun (congrFun s.scalar_law a) x
    exact (congrArg (InfinitesimalCommutator.matrixDifferential f glIso) h).trans (map_smul d a x)

private theorem pointActionDifferential_apply (s : IdentityLieStructure G.val)
    (ρ : Representation G.val I) (x : Lie k G.val) (i j : I) :
    (pointActionDifferential s ρ) x i j = ((ρ.app (dualTest k) x.toMul.val).val i j).snd := by
  let M := StandardGroups.generalLinearGroup k I
  let glIso := StandardGroups.generalLinearGroupPointsIso k I
  let E := groupHomEquiv G.val M.val G.property.1
  let f := E.symm (ρ ≫ glIso.inv)
  have h : (groupPointsFunctor k).map f ≫ glIso.hom = ρ := by
    change E f ≫ glIso.hom = ρ
    rw [show E f = ρ ≫ glIso.inv from E.apply_symm_apply _, Category.assoc, glIso.inv_hom_id,
      Category.comp_id]
  exact congrArg (fun a : Representation G.val I => ((a.app (dualTest k) x.toMul.val).val i j).snd) h

private theorem differentiated_matrix {A : HopfAlgebraCategory k}
    (s : IdentityLieStructure G.val) (e : specGroup A ≅ G.val) (ρ : Representation G.val I)
    (δ : RightComodule k A (I → k)) (hr : Realizes e (Pi.basisFun k I) δ ρ)
    (x : Lie k G.val) (v : I → k) :
    differentiatedCoaction A δ (presentedTangent e x) v = (pointActionDifferential s ρ x).mulVec v := by
  funext i
  have h := differentiated_coordinate e (Pi.basisFun k I) δ hr x v i
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply] at h
  rw [h]
  simp only [act, Matrix.mulVec, dotProduct, pointActionDifferential_apply]
  change (TrivSqZeroExt.sndHom k k)
    (∑ j, (ρ.app (dualTest k) x.toMul.val).val i j * algebraMap k (DualNumber k) (v j)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [TrivSqZeroExt.snd_mul, smul_eq_mul, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]

private theorem realizes_toCoaction {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (ρ : Representation G.val I) :
    Realizes e (Pi.basisFun k I) (toCoaction (pointIso e) (Pi.basisFun k I) ρ) ρ := by
  simpa only [from_toCoaction] using realizes_fromCoaction e (Pi.basisFun k I)
    (toCoaction (pointIso e) (Pi.basisFun k I) ρ)

/-- Differentiation carries rational highest vectors to the corresponding Lie
highest vectors and realizes every dominant actual character. -/
theorem rationalHighestWeightComparison : Statement.{u} := by
  classical
  intro k _ _ G hG P s
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := hG.2.1
  letI : ConnectedSpace G.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton
    G.val.X.hom
  obtain ⟨U, hU, hroots⟩ := positiveTangent_points P
  have classification := SimpleClassification.classification G P U hU
  constructor
  · intro V _ _ _ _ _ hi A e δ ha
    letI := hi
    let b := (Module.finBasis k V).reindex
      (Equiv.ulift.symm : _ ≃ ULift.{u} (Fin (Module.finrank k V)))
    let ρ := fromCoaction (pointIso e) b δ
    obtain ⟨χ, ⟨_, v, hv⟩, _⟩ := classification.1 ρ (simple_of_irreducible e b δ ha)
    refine ⟨χ, b.equivFun.symm v, highest_of_primitive e b δ (realizes_fromCoaction e b δ) ha hroots ?_⟩
    simpa only [LinearEquiv.apply_symm_apply] using hv
  · intro χ hχ
    obtain ⟨S, _⟩ := classification.2.2 χ hχ
    let V := S.J → k
    let ρ := S.socleAction
    let e := S.groupIso
    let b := Pi.basisFun k S.J
    let δ := toCoaction (pointIso e) b ρ
    let d := pointActionDifferential s ρ
    letI : LieRingModule (Lie k G.val) V := LieRingModule.compLieHom V d
    letI : LieModule k (Lie k G.val) V := LieModule.compLieHom V d
    have hr : Realizes e b δ ρ := realizes_toCoaction e ρ
    have ha : AgreesWithCoaction e δ := fun x v => differentiated_matrix s e ρ δ hr x v
    haveI : Nontrivial V := (Submodule.nontrivial_iff k (M := V)).mp (nontrivial_of_ne _ _ S.simple.1)
    have hi : LieModule.IsIrreducible k (Lie k G.val) V := by
      apply LieModule.IsIrreducible.mk
      intro N hN
      have hδ : δ.IsSubcomodule N.toSubmodule :=
        (subcomodule_iff_lie e δ ha N.toSubmodule).mpr (fun x v => N.lie_mem (x := x) v.property)
      have hstable : IsStable ρ N.toSubmodule :=
        (stable_iff CyclicHighestWeight.cyclicHighestWeight.1 ρ S.A (pointIso e) N.toSubmodule).mpr hδ
      rcases S.simple.2 N.toSubmodule hstable with h | h
      · exact (hN (LieSubmodule.toSubmodule_injective h)).elim
      · exact LieSubmodule.toSubmodule_injective h
    refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      hi, S.A, e, δ, ha, b.equivFun.symm (S.socleBasis.equivFun S.highestVector), ?_⟩
    apply highest_of_primitive e b δ hr ha hroots
    simpa only [LinearEquiv.apply_symm_apply] using S.primitive

end MatrixAction

end

end LinearAlgebraicGroups.Representation.RationalHighestWeightComparison
