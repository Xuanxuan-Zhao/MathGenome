import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.CompleteReducibility
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FaithfulLinearization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.LieStableSubspaces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.BaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompleteReducibility
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
open AlgebraicGeometry CategoryTheory Opposite WithConv
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Representation.CompleteReducibility

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open LinearAlgebraicGroups.Specs
open Specs.CompleteReducibility (IsFaithful pointPresentation)
open LinearAlgebraicGroups.RationalRepresentations hiding restrictCoaction
open Specs.GeometricRadicals (IsReductive IsTrivialSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open Specs.DiagonalizableGroups (groupAlgebra)

section Differentiation

open InfinitesimalCommutator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

open private matrixDifferentialLinear matrixDifferential_bracket
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open private dualKernelIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

private def representationDifferential {G L : GroupScheme k}
    [IsAffine G.X.left] [IsAffine L.X.left]
    (s : IdentityLieStructure G) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (f : G ⟶ L)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Lie k G →ₗ⁅k⁆ Module.End k V := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let d := matrixDifferentialLinear f l
  let T : Matrix ι ι k ≃ₐ[k] Module.End k V := Matrix.toLinAlgEquiv b
  refine {
    toFun := fun x => T (matrixDifferential f l x)
    map_add' := ?_
    map_smul' := ?_
    map_lie' := ?_ }
  · intro x y
    have h := congrArg (fun g : AddGroup (PointKernel G) => g.toAdd.add x y) s.group_law
    exact (congrArg (fun z => T (matrixDifferential f l z)) h).trans
      ((congrArg T (d.map_add x y)).trans (T.map_add _ _))
  · intro c x
    have h := congrFun (congrFun s.scalar_law c) x
    exact (congrArg (fun z => T (matrixDifferential f l z)) h).trans
      ((congrArg T (d.map_smul c x)).trans (T.toLinearMap.map_smul c (d x)))
  · intro x y
    change T (matrixDifferential f l (s.lieRing.toBracket.bracket x y)) =
      T (d x) * T (d y) - T (d y) * T (d x)
    rw [matrixDifferential_bracket f l s.commutator_law, map_sub, map_mul, map_mul]
    rfl

private theorem tangent_point_presentation {G : GroupScheme k} {A : HopfAlgebraCategory k}
    (a : specGroup A ≅ G) (x : Lie k G) :
    (pointPresentation a).hom.app (CommAlgCat.of k (DualNumber k))
      (toConv (tangentPointOfLie A (mapPointKernel a.inv x)).val) = x.toMul.val := by
  let d := dualKernelIso ((groupPointsFunctor k).mapIso a)
  let dA := dualKernelIso (hopfSpecPointIso A)
  change (d (dA (dA.symm (d.symm x)))).toMul.val = x.toMul.val
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

private theorem representationDifferential_apply {G L : GroupScheme k}
    [IsAffine G.X.left] [IsAffine L.X.left]
    (s : IdentityLieStructure G) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (f : G ⟶ L)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι)
    {A : HopfAlgebraCategory k} (a : specGroup A ≅ G) (ρ : RightComodule k A V)
    (hc : coefficients A b ρ = universalMatrix A (⟨G, inferInstance⟩ : AffineGroupCategory k)
      L (pointPresentation a) l f) (x : Lie k G) :
    letI := s.lieRing
    letI := s.lieAlgebra
    (representationDifferential s b f l x : V →ₗ[k] V) =
      differentiatedCoaction A ρ (tangentPointOfLie A (mapPointKernel a.inv x)) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  apply b.ext
  intro j
  have h := evaluationComparison A b ⟨G, inferInstance⟩ L (pointPresentation a) l f ρ hc
    (CommAlgCat.of k (DualNumber k)) (tangentPointOfLie A (mapPointKernel a.inv x)).val j
  rw [tangent_point_presentation] at h
  change Matrix.toLinAlgEquiv b (matrixDifferential f l x) (b j) =
    (TensorProduct.rid k V) (((TrivSqZeroExt.sndHom k k).lTensor V)
      (evaluate A ρ (tangentPointOfLie A (mapPointKernel a.inv x)).val (b j)))
  rw [h, map_sum, map_sum, Matrix.toLinAlgEquiv_self]
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  rfl

private theorem semisimple_group_complement [CharZero k] [FiniteDimensional k V]
    (hLie : SemisimplyDifferentiated.LieSemisimple.{u}) (G : AffineAlgebraicGroup k)
    (hG : GeometricRadicals.IsSemisimple G) {A : HopfAlgebraCategory k}
    (a : specGroup A ≅ G.val) (ρ : RightComodule k A V) (U : Submodule k V)
    (hU : ρ.IsSubcomodule U) :
    ∃ C : Submodule k V, IsCompl U C ∧ ρ.IsSubcomodule C := by
  classical
  letI := G.property.1
  letI := hG.2.1
  letI : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  let b := (Module.finBasis k V).reindex
    (Equiv.ulift.symm : Fin (Module.finrank k V) ≃ ULift.{u} (Fin (Module.finrank k V)))
  let L := LinearAlgebraicGroups.StandardGroups.generalLinearGroup k
    (ULift.{u} (Fin (Module.finrank k V)))
  letI := L.property.1
  let l := LinearAlgebraicGroups.StandardGroups.generalLinearGroupPointsIso (k := k)
    (ι := ULift.{u} (Fin (Module.finrank k V)))
  obtain ⟨E, hE⟩ := representationCoactionComparison A b ⟨G.val, G.property.1⟩ L.val
    (pointPresentation a) l
  let f := E.symm ρ
  have hc : coefficients A b ρ = universalMatrix A ⟨G.val, G.property.1⟩ L.val
      (pointPresentation a) l f :=
    (congrArg (coefficients A b) (E.apply_symm_apply ρ)).symm.trans (hE f)
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨hfin, hs⟩ := hLie G hG s
  letI : FiniteDimensional k (Lie k G.val) := hfin
  let d := representationDifferential s b f l
  letI : LieRingModule (Lie k G.val) V := LieRingModule.compLieHom V d
  letI : LieModule k (Lie k G.val) V := LieModule.compLieHom V d
  have hd (x : Lie k G.val) (v : V) :
      ⁅x, v⁆ = differentiatedCoaction A ρ (tangentPointOfLie A (mapPointKernel a.inv x)) v :=
    DFunLike.congr_fun (representationDifferential_apply s b f l a ρ hc x) v
  let P : LieSubmodule k (Lie k G.val) V :=
    { U with lie_mem := fun {x v} hv => (hd x v).symm ▸
        (lieStableSubspacesOfPresentation G a ρ U).mp hU x ⟨v, hv⟩ }
  obtain ⟨C, hC⟩ :=
    LieAlgebrasAndRepresentations.CompleteReducibility.invariant_complement
      k (Lie k G.val) V hs P
  refine ⟨C.toSubmodule, ?_, (lieStableSubspacesOfPresentation G a ρ _).mpr ?_⟩
  · exact ⟨LieSubmodule.disjoint_toSubmodule.mpr hC.disjoint,
      LieSubmodule.codisjoint_toSubmodule.mpr hC.codisjoint⟩
  · intro x v
    rw [← hd]
    exact C.lie_mem v.property


end Differentiation

open scoped CategoryTheory.MonObj

open private restrictCoaction kernel_presentation faithfullyFlat_of_presentation
  kernelInvariants_isSubcomodule map_coaction_tensor
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.ExactOperations
open private tensorCoordinate_sum_basis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private trivial_baseChange_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private invariant_iff_coaction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
open private geometricallyConnected_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private diagonal_coefficients offBlock_zero commute_from_centre
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus
open private centralInclusion productAlgebraicGroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {k V W : Type u} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private theorem exists_faithful (G : AffineAlgebraicGroup k) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : RightComodule k A V), IsFaithful G ρ e := by
  classical
  obtain ⟨n, L, ⟨l⟩, f, hf⟩ := faithfulLinearization k G
  let I := ULift.{u} (Fin n)
  let b : Module.Basis I k (I → k) := Pi.basisFun k I
  obtain ⟨E, hE⟩ := representationCoactionComparison A b
    (⟨G.val, G.property.1⟩ : AffineGroupCategory k) L.val e l
  exact ⟨I → k, inferInstance, inferInstance, inferInstance, E f, n, b, L, l, f, hf, hE f⟩

private theorem projection_equivariant {A : HopfAlgebraCategory k} (ρ : RightComodule k A V)
    (U C : Submodule k V) (h : IsCompl U C) (τ : RightComodule k A U)
    (hU : IsEquivariant A τ ρ U.subtype) (hC : ρ.IsSubcomodule C) :
    IsEquivariant A ρ τ (U.projectionOnto C h) := by
  let r := U.projectionOnto C h
  have hrU : r.comp U.subtype = LinearMap.id := U.projectionOnto_comp_subtype h
  have hrC : r.comp C.subtype = 0 := LinearMap.ext (U.projectionOnto_apply_right h)
  have hpart (v : V) : ∃ (u : U) (c : C), (u : V) + c = v := by
    have hv : v ∈ U ⊔ C := by rw [h.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, he⟩ := Submodule.mem_sup.mp hv
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, he⟩
  change (r.rTensor A).comp ρ.coaction = τ.coaction.comp r
  apply LinearMap.ext
  intro v
  obtain ⟨x, y, rfl⟩ := hpart v
  have hx : ρ.coaction (x : V) = U.subtype.rTensor A (τ.coaction x) :=
    (DFunLike.congr_fun hU x).symm
  obtain ⟨z, hz⟩ := hC y
  have hrx : r (x : V) = x := DFunLike.congr_fun hrU x
  have hry : r (y : V) = 0 := DFunLike.congr_fun hrC y
  simp only [LinearMap.comp_apply, map_add, hrx, hry, map_zero, add_zero, hx, ← hz]
  simp [← LinearMap.rTensor_comp_apply, hrU, hrC]

private theorem kernel_isSubcomodule {A : HopfAlgebraCategory k}
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (r : V →ₗ[k] W) (hr : IsEquivariant A ρ σ r) : ρ.IsSubcomodule (LinearMap.ker r) := by
  intro x
  have hx : (r.rTensor A) (ρ.coaction (x : V)) = 0 := by
    simpa [LinearMap.mem_ker.mp x.property] using DFunLike.congr_fun hr x.val
  exact (Module.Flat.rTensor_exact A r.exact_subtype_ker_map _).mp hx

private def coordinateHom {G H : GroupScheme k} {A B : HopfAlgebraCategory k}
    (a : specGroup A ≅ G) (b : specGroup B ≅ H) (f : G ⟶ H) : B ⟶ A :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage (a.hom ≫ f ≫ b.inv)).unop

private theorem coordinateHom_spec {G H : GroupScheme k} {A B : HopfAlgebraCategory k}
    (a : specGroup A ≅ G) (b : specGroup B ≅ H) (f : G ⟶ H) :
    specGroupMap (coordinateHom a b f) ≫ b.hom = a.hom ≫ f := by
  have h : specGroupMap (coordinateHom a b f) = a.hom ≫ f ≫ b.inv :=
    (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  rw [h]
  simp

private theorem pointPresentation_map {G H : GroupScheme k} {A B : HopfAlgebraCategory k}
    (a : specGroup A ≅ G) (b : specGroup B ≅ H) (q : B ⟶ A) (f : G ⟶ H)
    (h : specGroupMap q ≫ b.hom = a.hom ≫ f) (R : TestAlgebra k) (g : A →ₐ[k] R) :
    (pointPresentation b).hom.app R (toConv (g.comp q.hom.toAlgHom)) =
      ((groupPointsFunctor k).map f).app R ((pointPresentation a).hom.app R (toConv g)) := by
  have h' := congrArg (Grp.forget (SchemeOver k)).map h
  change (specGroupMap q).hom.hom ≫ b.hom.hom.hom = a.hom.hom.hom ≫ f.hom.hom at h'
  change (Spec.mapMulEquiv (R := k) (S := B) (T := R) (toConv (g.comp q.hom.toAlgHom))) ≫
    b.hom.hom.hom = (Spec.mapMulEquiv (R := k) (S := A) (T := R) (toConv g)) ≫
      a.hom.hom.hom ≫ f.hom.hom
  rw [← h', ← Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  exact Spec.map_comp (CommRingCat.ofHom q.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom g.toRingHom)

private theorem trivial_of_zero_inclusion {G : GroupScheme k} (N : ClosedSubgroup G)
    (h : N.inclusion = 0) : IsTrivialSubgroup N := by
  letI := N.isClosedImmersion
  haveI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  haveI : Mono N.inclusion := (Grp.forget _).mono_of_mono_map ‹Mono N.inclusion.hom.hom›
  exact ⟨(IsZero.of_mono_eq_zero N.inclusion h).iso (Grp.isZero_trivial _)⟩

private theorem faithful_kernel_trivial {A B : HopfAlgebraCategory k} (G : AffineAlgebraicGroup k)
    (a : specGroup A ≅ G.val) (N : ClosedSubgroup G.val) (b : specGroup B ≅ N.group)
    (q : A ⟶ B) (hq : specGroupMap q ≫ a.hom = b.hom ≫ N.inclusion)
    (ρ : RightComodule k A V) (hρ : IsFaithful G ρ (pointPresentation a))
    (htriv : ∀ v : V, (restrictCoaction q ρ).coaction v = v ⊗ₜ[k] 1) :
    IsTrivialSubgroup N := by
  classical
  obtain ⟨n, basis, L, l, f, hf, hcoeff⟩ := hρ
  letI := hf
  haveI : Mono f.hom.hom := Over.mono_of_mono_left _
  haveI : Mono f := (Grp.forget _).mono_of_mono_map ‹Mono f.hom.hom›
  apply trivial_of_zero_inclusion N
  apply (cancel_mono f).mp
  rw [zero_comp]
  let R : TestAlgebra k := CommAlgCat.of k B
  let g : ((groupPointsFunctor k).obj N.group).obj R :=
    (pointPresentation b).hom.app R (toConv (AlgHom.id k B))
  let M := l.hom.app R (((groupPointsFunctor k).map f).app R
    (((groupPointsFunctor k).map N.inclusion).app R g))
  have hM : M = 1 := by
    apply Units.ext
    ext i j
    have he := evaluationComparison A basis
      (⟨G.val, G.property.1⟩ : AffineGroupCategory k) L.val
      (pointPresentation a) l f ρ hcoeff R q.hom.toAlgHom j
    have hpoint := pointPresentation_map b a q N.inclusion hq R (AlgHom.id k B)
    rw [AlgHom.id_comp] at hpoint
    rw [hpoint] at he
    have he' : basis j ⊗ₜ[k] (1 : B) = ∑ i, basis i ⊗ₜ[k] M.val i j :=
      (htriv (basis j)).symm.trans he
    have hc := congrArg (tensorCoordinate basis i) he'
    rw [tensorCoordinate_sum_basis] at hc
    simpa [tensorCoordinate, Module.Basis.repr_self_apply, Finsupp.single_apply,
      Matrix.one_apply, eq_comm] using hc.symm
  have hp : (((groupPointsFunctor k).map (N.inclusion ≫ f)).app R) g = 1 := by
    apply (ConcreteCategory.bijective_of_isIso (l.hom.app R)).injective
    change M = (l.hom.app R).hom 1
    rw [map_one, hM]
  have hg : (g : Points N.group.X R) = b.hom.hom.hom := by
    change Spec.mapMulEquiv (R := k) (S := B) (T := R) (toConv (AlgHom.id k B)) ≫
      b.hom.hom.hom = _
    have he : (Spec.mapMulEquiv (R := k) (S := B) (T := R) (toConv (AlgHom.id k B))) =
        𝟙 (specGroup B).X := by
      apply Over.OverMorphism.ext
      exact Spec.map_id _
    exact (congrArg (fun z : (specGroup B).X ⟶ (specGroup B).X => z ≫ b.hom.hom.hom) he).trans
      (Category.id_comp b.hom.hom.hom)
  apply Grp.hom_ext
  apply (cancel_epi b.hom.hom.hom).mp
  change (g : Points N.group.X R) ≫ (N.inclusion ≫ f).hom.hom = 1 at hp
  rw [hg] at hp
  change b.hom.hom.hom ≫ (N.inclusion ≫ f).hom.hom =
    b.hom.hom.hom ≫ (1 : N.group.X ⟶ L.val.X)
  exact hp.trans (MonObj.comp_one b.hom.hom.hom).symm


private theorem trivial_unipotent_normal_subgroup [FiniteDimensional k V]
    (G : AffineAlgebraicGroup k) {A : HopfAlgebraCategory k}
    (a : specGroup A ≅ G.val) (ρ : RightComodule k A V)
    (hf : IsFaithful G ρ (pointPresentation a)) (hs : IsSemisimple A ρ)
    (N : ClosedSubgroup G.val) (hN : IsNormalSubgroup N.inclusion)
    (hu : Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup N)) :
    IsTrivialSubgroup N := by
  obtain ⟨L, f, Q, p, i, _, hker, hfac, _, _⟩ := normalAffineQuotient G N hN
  obtain ⟨B, _, ⟨b⟩⟩ := groupPresentation Q
  let j := coordinateHom a b p
  have hj := coordinateHom_spec a b p
  letI := hopfKernelIdeal k j
  have hff := faithfullyFlat_of_presentation p j a b hj hfac.2.1 hfac.2.2.1
  let C := hopfQuotient A (kernelIdeal j)
  let q := hopfQuotientMap A (kernelIdeal j)
  let c : specGroup C ≅ N.group := kernel_presentation p N hker j a b hj
  let U := Specs.Unipotent.kernelInvariants j ρ
  have hU : ρ.IsSubcomodule U := kernelInvariants_isSubcomodule j hff ρ
  obtain ⟨τ, hτ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction ρ U).mp hU
  obtain ⟨r, hr, hri⟩ := hs U τ hτ
  have hC : ρ.IsSubcomodule (LinearMap.ker r) := kernel_isSubcomodule ρ τ r hr
  obtain ⟨σ, hσ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction ρ _).mp hC
  -- A nonzero complement would contain a vector fixed by the unipotent subgroup.
  have htop : U = ⊤ := by
    by_contra hne
    have hcompl : IsCompl U (LinearMap.ker r) := LinearMap.isCompl_of_proj
      (fun x => DFunLike.congr_fun hri x)
    have hne' : LinearMap.ker r ≠ ⊥ := by
      intro h
      apply hne
      simpa [h] using hcompl.sup_eq_top
    letI := Submodule.nontrivial_iff_ne_bot.mpr hne'
    have hInv := (Unipotent.unipotenceCriteria (closedSubgroupAlgebraicGroup N) C c).1.mp hu
    obtain ⟨v, hv, hvfix⟩ := hInv _ (restrictCoaction q σ)
    have hz : (v : V) ∈ U := by
      change _ ∈ Specs.Unipotent.kernelInvariants j ρ
      unfold Specs.Unipotent.kernelInvariants
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      simp only [LinearMap.comp_apply]
      have h := DFunLike.congr_fun hσ v
      change (LinearMap.ker r).subtype.rTensor A (σ.coaction v) = ρ.coaction (v : V) at h
      rw [← h, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]
      change (LinearMap.ker r).subtype.rTensor C ((restrictCoaction q σ).coaction v) = _
      have hvfix' : (restrictCoaction q σ).coaction v = v ⊗ₜ[k] (1 : C) :=
        (invariant_iff_coaction C (restrictCoaction q σ) v).mp hvfix
      rw [hvfix', LinearMap.rTensor_tmul]
      rfl
    exact hv (Subtype.ext ((Submodule.disjoint_def.mp hcompl.disjoint) (v : V) hz v.property))
  have htriv (v : V) : (restrictCoaction q ρ).coaction v = v ⊗ₜ[k] (1 : C) := by
    have hv : v ∈ U := htop ▸ Submodule.mem_top
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp hv)
  have hc : specGroupMap q ≫ a.hom = c.hom ≫ N.inclusion := by
    simp only [c, q, kernel_presentation, IsPullback.isoIsPullback_hom_fst]
  exact faithful_kernel_trivial G a N c q hc ρ hf htriv

private theorem reductive_of_faithful_semisimple [CharZero k] [FiniteDimensional k V]
    (G : AffineAlgebraicGroup k) [ConnectedSpace G.val.X.left] {A : HopfAlgebraCategory k}
    (a : specGroup A ≅ G.val) (ρ : RightComodule k A V)
    (hf : IsFaithful G ρ (pointPresentation a)) (hs : IsSemisimple A ρ) :
    IsReductive G := by
  have hsm := characteristicZeroSmoothness k G
  have hgc := geometricallyConnected_of_connected G
  refine ⟨hsm, hgc, ?_⟩
  obtain ⟨N, hN, e, _⟩ := Reductive.RadicalBaseChange.unipotentRadicalPerfectDescent G hsm hgc
  have htrivial := trivial_unipotent_normal_subgroup G a ρ hf hs N hN.1.2.2 hN.2.1
  obtain ⟨et⟩ := (trivial_baseChange_iff (K := AlgebraicClosure k) N.group).mpr htrivial
  exact ⟨e.symm ≪≫ et⟩


section WeightProjections

open scoped Classical
open WeightDecomposition (weightSpace mem_weightSpace)
open private weightProjection projection_of_mem projection_mem coaction_sum counit_character
  tensorCoefficients from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition

variable {X M : Type u} [CommGroup M]
  [AddCommGroup X] [Module k X]
variable {A B : HopfAlgebraCategory k}

private theorem equivariant_comp {ρ : RightComodule k A V} {σ : RightComodule k A W}
    {τ : RightComodule k A X} {f : V →ₗ[k] W} {g : W →ₗ[k] X}
    (hf : IsEquivariant A ρ σ f) (hg : IsEquivariant A σ τ g) :
    IsEquivariant A ρ τ (g.comp f) := by
  unfold IsEquivariant at *
  rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, hg,
    LinearMap.comp_assoc]

private theorem equivariant_restrict (q : A ⟶ B)
    {ρ : RightComodule k A V} {σ : RightComodule k A W} {f : V →ₗ[k] W}
    (h : IsEquivariant A ρ σ f) : IsEquivariant B (restrictCoaction q ρ) (restrictCoaction q σ) f := by
  unfold IsEquivariant at *
  change (f.rTensor B).comp ((q.hom.toLinearMap.lTensor V).comp ρ.coaction) =
    ((q.hom.toLinearMap.lTensor W).comp σ.coaction).comp f
  rw [← LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_assoc, h, ← LinearMap.comp_assoc]

private theorem central_weight_projection [FiniteDimensional k V]
    (q : A ⟶ groupAlgebra k M) (ρ : RightComodule k A V)
    (hc : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (c : MonoidAlgebra k M →ₐ[k] R),
      letI := convolutionGroup A R
      Commute (toConv a) (toConv (c.comp q.hom.toAlgHom))) (m : M) :
    IsEquivariant A ρ ρ (weightProjection (restrictCoaction q ρ) m) := by
  classical
  let τ := restrictCoaction q ρ
  let bs (m : M) := Module.Basis.ofVectorSpace k (weightSpace τ m)
  have hw := WeightDecomposition.weightDecomposition τ
  let b := hw.collectedBasis bs
  let J := Σ m : M, Module.Basis.ofVectorSpaceIndex k (weightSpace τ m)
  letI : Finite J := Module.Finite.finite_basis b
  letI : Fintype J := Fintype.ofFinite J
  let X := coefficients A b ρ
  have hdiag (i j : J) := diagonal_coefficients q ρ b Sigma.fst
    (fun j ↦ hw.collectedBasis_mem bs j) i j
  have hz (i j : J) (h : i.1 ≠ j.1) : X i j = 0 :=
    offBlock_zero q X (coefficients_isCoactionMatrix A b ρ) Sigma.fst hdiag hc i j h
  let P := weightProjection τ m
  have hp (i : J) : P (b i) = if i.1 = m then b i else 0 :=
    projection_of_mem (hw.collectedBasis_mem bs i) m
  apply b.ext
  intro j
  change (P.rTensor A) (ρ.coaction (b j)) = ρ.coaction (P (b j))
  calc
    _ = ∑ i : J, P (b i) ⊗ₜ[k] X i j := by
      rw [coaction_apply_basis A b ρ j, map_sum]
      exact Finset.sum_congr rfl (fun i _ => LinearMap.rTensor_tmul A P (X i j) (b i))
    _ = _ := by
      rw [hp j]
      by_cases hj : j.1 = m
      · rw [ite_eq_left hj, coaction_apply_basis A b ρ j]
        change _ = ∑ i : J, b i ⊗ₜ[k] X i j
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i.1 = m
        · rw [hp i, ite_eq_left hi]
        · rw [hp i, ite_eq_right hi, hz i j (fun h => hi (h.trans hj)),
            TensorProduct.zero_tmul, TensorProduct.tmul_zero]
      · rw [ite_eq_right hj, map_zero]
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : i.1 = m
        · rw [hz i j (fun h => hj (h.symm.trans hi)), TensorProduct.tmul_zero]
        · rw [hp i, ite_eq_right hi, TensorProduct.zero_tmul]

private theorem weight_projection_natural
    {ρ : RightComodule k (groupAlgebra k M) V} {σ : RightComodule k (groupAlgebra k M) W}
    (f : V →ₗ[k] W) (hf : IsEquivariant (groupAlgebra k M) ρ σ f) (m : M) (v : V) :
    weightProjection σ m (f v) = f (weightProjection ρ m v) := by
  classical
  have eq (t : V ⊗[k] MonoidAlgebra k M) :
      (tensorCoefficients ((f.rTensor (MonoidAlgebra k M)) t)) m =
        f (tensorCoefficients t m) := by
    induction t with
    | tmul v a =>
      simp only [tensorCoefficients, LinearMap.rTensor_tmul, LinearEquiv.trans_apply,
        LinearEquiv.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply, map_smul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  change tensorCoefficients (σ.coaction (f v)) m = f (tensorCoefficients (ρ.coaction v) m)
  have h := DFunLike.congr_fun hf v
  change f.rTensor (MonoidAlgebra k M) (ρ.coaction v) = σ.coaction (f v) at h
  rw [← h, eq]

private theorem weightProjection_sum [FiniteDimensional k V]
    (ρ : RightComodule k (groupAlgebra k M) V) :
    ∃ s : Finset M, ∀ v : V, (∑ m ∈ s, weightProjection ρ m v) = v := by
  classical
  let s := (WeightDecomposition.finiteWeights ρ).toFinset
  refine ⟨s, fun v => ?_⟩
  have hz (m : M) (h : m ∉ s) : weightProjection ρ m v = 0 := by
    have he : weightSpace ρ m = ⊥ := by
      by_contra hh
      exact h ((Set.Finite.mem_toFinset _).mpr hh)
    exact (Submodule.mem_bot (R := k)).mp (he ▸ projection_mem ρ m v)
  -- The pointwise finite support can be replaced by the finite set of nonzero weights.
  obtain ⟨l, hlco, hl⟩ := coaction_sum ρ v
  have ht' : (∑ m ∈ l, weightProjection ρ m v) = v := by
    have hh := ρ.counit v
    rw [hlco] at hh
    simpa only [map_sum, LinearMap.lTensor_tmul, counit_character, TensorProduct.rid_tmul,
      one_smul] using hh
  calc
    (∑ m ∈ s, weightProjection ρ m v) = ∑ m ∈ l ∪ s, weightProjection ρ m v :=
      Finset.sum_subset Finset.subset_union_right (fun m _ hm => hz m hm)
    _ = ∑ m ∈ l, weightProjection ρ m v :=
      (Finset.sum_subset Finset.subset_union_left (fun m _ hm => hl m hm)).symm
    _ = v := ht'

private theorem equivariant_of_weight_preserving [FiniteDimensional k V]
    {ρ : RightComodule k (groupAlgebra k M) V} {σ : RightComodule k (groupAlgebra k M) W}
    (f : V →ₗ[k] W) (hf : ∀ (m : M) (v : V), v ∈ weightSpace ρ m → f v ∈ weightSpace σ m) :
    IsEquivariant (groupAlgebra k M) ρ σ f := by
  classical
  let bs (m : M) := Module.Basis.ofVectorSpace k (weightSpace ρ m)
  have hi := WeightDecomposition.weightDecomposition ρ
  let b := hi.collectedBasis bs
  apply b.ext
  intro j
  have hj := hi.collectedBasis_mem bs j
  change (f.rTensor (MonoidAlgebra k M)) (ρ.coaction (b j)) = σ.coaction (f (b j))
  rw [mem_weightSpace.mp hj, LinearMap.rTensor_tmul, mem_weightSpace.mp (hf j.1 (b j) hj)]

/-- Project to each central weight before and after applying the derived-group
retraction. The weight projections themselves commute with the ambient coaction. -/
private theorem weighted_retraction [FiniteDimensional k V] [FiniteDimensional k W]
    (q : A ⟶ groupAlgebra k M) (d : A ⟶ B) (ρ : RightComodule k A V)
    (σ : RightComodule k A W) (i : W →ₗ[k] V) (hi : IsEquivariant A σ ρ i)
    (hc : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (c : MonoidAlgebra k M →ₐ[k] R),
      letI := convolutionGroup A R
      Commute (toConv a) (toConv (c.comp q.hom.toAlgHom)))
    (r : V →ₗ[k] W) (hr : IsEquivariant B (restrictCoaction d ρ) (restrictCoaction d σ) r)
    (hri : r.comp i = LinearMap.id) :
    ∃ p : V →ₗ[k] W, IsEquivariant B (restrictCoaction d ρ) (restrictCoaction d σ) p ∧
      IsEquivariant (groupAlgebra k M) (restrictCoaction q ρ) (restrictCoaction q σ) p ∧
      p.comp i = LinearMap.id := by
  classical
  let ρT := restrictCoaction q ρ
  let σT := restrictCoaction q σ
  obtain ⟨s, hs⟩ := weightProjection_sum σT
  let P := weightProjection ρT
  let Q := weightProjection σT
  let f (m : M) := (Q m).comp (r.comp (P m))
  let p := ∑ m ∈ s, f m
  refine ⟨p, ?_, ?_, ?_⟩
  · have he (m : M) : IsEquivariant B (restrictCoaction d ρ) (restrictCoaction d σ) (f m) :=
      equivariant_comp
        (equivariant_comp (equivariant_restrict d (central_weight_projection q ρ hc m)) hr)
        (equivariant_restrict d (central_weight_projection q σ hc m))
    unfold IsEquivariant at *
    ext v
    simp only [p, ← LinearMap.coe_rTensorHom, map_sum, LinearMap.comp_apply, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro m _
    exact DFunLike.congr_fun (he m) v
  · apply equivariant_of_weight_preserving
    intro m v hv
    change (∑ n ∈ s, f n) v ∈ weightSpace σT m
    rw [LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro n _
    change Q n (r (P n v)) ∈ weightSpace σT m
    change weightProjection σT n (r (weightProjection ρT n v)) ∈ weightSpace σT m
    rw [projection_of_mem hv]
    split
    · rename_i h
      subst n
      exact projection_mem σT m _
    · simp
  · ext w
    change (∑ m ∈ s, f m) (i w) = w
    rw [LinearMap.sum_apply]
    calc
      _ = ∑ m ∈ s, Q m w := by
        apply Finset.sum_congr rfl
        intro m _
        change weightProjection σT m (r (weightProjection ρT m (i w))) =
          weightProjection σT m w
        rw [weight_projection_natural i (equivariant_restrict q hi),
          show r (i (weightProjection σT m w)) = weightProjection σT m w from
            DFunLike.congr_fun hri _, projection_of_mem (projection_mem σT m w), ite_eq_left rfl]
      _ = w := hs w

end WeightProjections

section ProductCover

variable {A B : HopfAlgebraCategory k}

private theorem evaluate_restriction (q : A ⟶ B) (ρ : RightComodule k A V)
    {R : TestAlgebra k} (g : B →ₐ[k] R) :
    evaluate B (restrictCoaction q ρ) g = evaluate A ρ (g.comp q.hom.toAlgHom) := by
  change (g.toLinearMap.lTensor V).comp ((q.hom.toLinearMap.lTensor V).comp ρ.coaction) =
    ((g.toLinearMap.comp q.hom.toLinearMap).lTensor V).comp ρ.coaction
  rw [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp]

private def evaluateTensor {R : TestAlgebra k} (d : V →ₗ[k] V ⊗[k] R) :
    V ⊗[k] R →ₗ[k] V ⊗[k] R :=
  (LinearMap.mul' k R).lTensor V ∘ₗ
    (TensorProduct.assoc k V R R).toLinearMap ∘ₗ d.rTensor R

private theorem evaluateTensor_mul (ρ : RightComodule k A V)
    (f g : (convolutionPoints A).obj (CommAlgCat.of k B)) (v : V) :
    evaluateTensor (R := CommAlgCat.of k B) (evaluate A ρ f.ofConv) (evaluate A ρ g.ofConv v) =
      evaluate A ρ (f * g).ofConv v := by
  let R := CommAlgCat.of k B
  have h := map_coaction_tensor (B := B) (C := B) ρ.coaction
    f.ofConv.toLinearMap g.ofConv.toLinearMap (ρ.coaction v)
  rw [ρ.coassoc, ← LinearMap.lTensor_comp_apply] at h
  change (LinearMap.mul' k R).lTensor V (TensorProduct.assoc k V R R
    (((f.ofConv.toLinearMap.lTensor V).comp ρ.coaction).rTensor R
      ((g.ofConv.toLinearMap.lTensor V) (ρ.coaction v)))) = _
  rw [← h, ← LinearMap.lTensor_comp_apply]
  have he : (LinearMap.mul' k R).comp
      ((TensorProduct.map f.ofConv.toLinearMap g.ofConv.toLinearMap).comp (Coalgebra.comul (R := k))) =
      (f * g).ofConv.toLinearMap := by
    ext a
    change LinearMap.mul' k R (TensorProduct.map f.ofConv.toLinearMap g.ofConv.toLinearMap
      (Coalgebra.comul (R := k) a)) = (f * g).ofConv a
    rw [AlgHom.convMul_apply]
    induction (Coalgebra.comul (R := k) a) with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [he]
  rfl

private theorem evaluateTensor_preserves {R : TestAlgebra k} (d : V →ₗ[k] V ⊗[k] R)
    (U : Submodule k V) (h : ∀ u : U, d u ∈ LinearMap.range (U.subtype.rTensor R))
    (x : V ⊗[k] R) (hx : x ∈ LinearMap.range (U.subtype.rTensor R)) :
    evaluateTensor (R := R) d x ∈ LinearMap.range (U.subtype.rTensor R) := by
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.inductionOn with
  | tmul u r =>
    obtain ⟨y, hy⟩ := h u
    refine ⟨(LinearMap.mul' k R).lTensor U
      (TensorProduct.assoc k U R R (y ⊗ₜ[k] r)), ?_⟩
    change ((U.subtype.rTensor R) ((LinearMap.mul' k R).lTensor U
      (TensorProduct.assoc k U R R (y ⊗ₜ[k] r)))) =
      (LinearMap.mul' k R).lTensor V (TensorProduct.assoc k V R R
        ((d.rTensor R) (U.subtype.rTensor R (u ⊗ₜ[k] r))))
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    change _ = (LinearMap.mul' k R).lTensor V (TensorProduct.assoc k V R R (d (u : V) ⊗ₜ[k] r))
    rw [← hy]
    clear hy
    induction y with
    | tmul z s => rfl
    | add y z hy hz =>
      simp only [TensorProduct.add_tmul, map_add, hy, hz]
  | add x y hx hy =>
    simpa only [map_add] using (LinearMap.range (U.subtype.rTensor R)).add_mem hx hy

private theorem isSubcomodule_of_injective_restriction (q : A ⟶ B) (hq : Function.Injective q.hom)
    (ρ : RightComodule k A V) (U : Submodule k V) (h : (restrictCoaction q ρ).IsSubcomodule U) :
    ρ.IsSubcomodule U := by
  intro v
  apply (Module.Flat.rTensor_exact A (LinearMap.exact_subtype_mkQ U) (ρ.coaction v)).mp
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := V ⧸ U) q.hom.toLinearMap hq
  have hv := (Module.Flat.rTensor_exact B (LinearMap.exact_subtype_mkQ U)
    ((restrictCoaction q ρ).coaction v)).mpr (h v)
  change (q.hom.toLinearMap.lTensor (V ⧸ U)) ((U.mkQ.rTensor A) (ρ.coaction v)) =
    (q.hom.toLinearMap.lTensor (V ⧸ U)) 0
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.comp_apply, map_zero]
  exact hv

private theorem isSubcomodule_of_product_cover
    {G T D P : AffineAlgebraicGroup k}
    {A AT AD : HopfAlgebraCategory k}
    (a : specGroup A ≅ G.val) (aT : specGroup AT ≅ T.val) (aD : specGroup AD ≅ D.val)
    (iT : T.val ⟶ G.val) (iD : D.val ⟶ G.val)
    (pT : P.val ⟶ T.val) (pD : P.val ⟶ D.val)
    (m : P.val ⟶ G.val)
    (hm : m.hom.hom = (pT ≫ iT).hom.hom * (pD ≫ iD).hom.hom)
    (hflat : Flat m.hom.hom.left) (hsurj : Surjective m.hom.hom.left)
    (ρ : RightComodule k A V) (U : Submodule k V)
    (hT : (restrictCoaction (coordinateHom aT a iT) ρ).IsSubcomodule U)
    (hD : (restrictCoaction (coordinateHom aD a iD) ρ).IsSubcomodule U) :
    ρ.IsSubcomodule U := by
  obtain ⟨B, _, ⟨b⟩⟩ := groupPresentation P
  let q := coordinateHom b a m
  have hq := coordinateHom_spec b a m
  have hff := faithfullyFlat_of_presentation m q b a hq hflat hsurj
  apply isSubcomodule_of_injective_restriction q hff.injective ρ U
  -- In the coordinate algebra of the cover, its universal point maps to the
  -- product of the two projected points. Each factor preserves the subspace.
  let R := CommAlgCat.of k B
  let t := (coordinateHom b aT pT).hom.toAlgHom
  let d := (coordinateHom b aD pD).hom.toAlgHom
  let f : (convolutionPoints A).obj R := toConv (t.comp (coordinateHom aT a iT).hom.toAlgHom)
  let g : (convolutionPoints A).obj R := toConv (d.comp (coordinateHom aD a iD).hom.toAlgHom)
  have hprod : (toConv q.hom.toAlgHom : (convolutionPoints A).obj R) = f * g := by
    let e := (pointPresentation a).hom.app R
    let y := (pointPresentation b).hom.app R (toConv (AlgHom.id k B))
    apply (ConcreteCategory.bijective_of_isIso e).injective
    have hq' := pointPresentation_map b a q m hq R (AlgHom.id k B)
    have ht := pointPresentation_map b aT _ pT (coordinateHom_spec b aT pT)
      R (AlgHom.id k B)
    have hd := pointPresentation_map b aD _ pD (coordinateHom_spec b aD pD)
      R (AlgHom.id k B)
    rw [AlgHom.id_comp] at hq' ht hd
    change e (toConv q.hom.toAlgHom) = e.hom (f * g)
    rw [map_mul, hq']
    have hf := pointPresentation_map aT a _ iT (coordinateHom_spec aT a iT) R t
    have hg := pointPresentation_map aD a _ iD (coordinateHom_spec aD a iD) R d
    change e f = _ at hf
    change e g = _ at hg
    rw [hf, hg]
    change (pointPresentation aT).hom.app R (toConv t) = _ at ht
    change (pointPresentation aD).hom.app R (toConv d) = _ at hd
    rw [ht, hd]
    change (y : Points P.val.X R) ≫ m.hom.hom =
      ((y : Points P.val.X R) ≫ (pT ≫ iT).hom.hom) *
        ((y : Points P.val.X R) ≫ (pD ≫ iD).hom.hom)
    rw [hm, MonObj.comp_mul]
  have hfv (v : U) : evaluate A ρ f.ofConv v ∈ LinearMap.range (U.subtype.rTensor B) := by
    change evaluate A ρ (t.comp (coordinateHom aT a iT).hom.toAlgHom) v ∈ _
    rw [← evaluate_restriction (R := R) _ ρ _]
    exact (stableSubspaces AT _ U).mpr hT R t v
  have hgv (v : U) : evaluate A ρ g.ofConv v ∈ LinearMap.range (U.subtype.rTensor B) := by
    change evaluate A ρ (d.comp (coordinateHom aD a iD).hom.toAlgHom) v ∈ _
    rw [← evaluate_restriction (R := R) _ ρ _]
    exact (stableSubspaces AD _ U).mpr hD R d v
  intro v
  change evaluate A ρ (toConv q.hom.toAlgHom : (convolutionPoints A).obj R).ofConv v ∈ _
  rw [hprod, ← evaluateTensor_mul]
  exact evaluateTensor_preserves (R := R) (evaluate A ρ f.ofConv) U hfv _ (hgv v)

end ProductCover

private theorem central_coordinate {G T : GroupScheme k} {A B : HopfAlgebraCategory k}
    (a : specGroup A ≅ G) (b : specGroup B ≅ T) (i : T ⟶ G)
    (hi : Centralizes (𝟙 G) i.hom.hom)
    (R : TestAlgebra k) (x : A →ₐ[k] R) (y : B →ₐ[k] R) :
    letI := convolutionGroup A R
    Commute (toConv x) (toConv (y.comp (coordinateHom b a i).hom.toAlgHom)) := by
  letI := convolutionGroup A R
  let e := (pointPresentation a).hom.app R
  apply Commute.of_map (f := e.hom) (ConcreteCategory.bijective_of_isIso e).injective
  have hp := pointPresentation_map b a _ i (coordinateHom_spec b a i) R y
  change Commute (e (toConv x)) (e (toConv (y.comp (coordinateHom b a i).hom.toAlgHom)))
  change e (toConv (y.comp (coordinateHom b a i).hom.toAlgHom)) = _ at hp
  rw [hp]
  change Commute (e (toConv x) : Points G.X R)
    (((pointPresentation b).hom.app R (toConv y) : Points T.X R) ≫ i.hom.hom)
  exact (commute_from_centre hi
    ((pointPresentation b).hom.app R (toConv y) : Points T.X R)
    (e (toConv x) : Points G.X R)).symm

private theorem split_reductive_semisimple [CharZero k] [IsAlgClosed k] [FiniteDimensional k V]
    (hLie : SemisimplyDifferentiated.LieSemisimple.{u}) (G : AffineAlgebraicGroup k)
    (hG : GeometricRadicals.IsReductive G) {A : HopfAlgebraCategory k}
    (a : specGroup A ≅ G.val) (ρ : RightComodule k A V) : IsSemisimple A ρ := by
  classical
  intro U τ hU
  obtain ⟨Z, hZ, T, hT, _⟩ := Reductive.CentralDerived.centralTorusExists G hG
  obtain ⟨D, hD⟩ := SchemeDerivedGroup.derivedSubgroupExists G
  obtain ⟨m, hm, _⟩ := Reductive.CentralDerived.centralProductKernel G hG Z hZ T hT D hD
  obtain ⟨hmf, hms⟩ := Reductive.CentralDerived.centralProductFaithfullyFlat G hG Z hZ T hT D hD m hm
  let TG := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup Z) T
  let DG := closedSubgroupAlgebraicGroup D
  let iT : TG.val ⟶ G.val := T.inclusion ≫ Z.inclusion
  have hc : Centralizes (𝟙 G.val) iT.hom.hom := centralInclusion hZ T
  have hTs : GeometricRadicals.IsSplitTorus TG.val :=
    split_of_torus ((isTorus_iff_coordinates TG).mp hT.1)
  obtain ⟨r, ⟨e⟩⟩ := hTs
  obtain ⟨bT⟩ := CharacterDescent.standardSplitTorus (k := k) r
  let aT := bT ≪≫ e.symm
  let t := coordinateHom aT a iT
  obtain ⟨AD, _, ⟨aD⟩⟩ := groupPresentation DG
  let d := coordinateHom aD a D.inclusion
  have hDs := Reductive.CentralDerived.derivedSemisimple G hG D hD
  have hUD : (restrictCoaction d ρ).IsSubcomodule U :=
    (RightComodule.isSubcomodule_iff_exists_coaction _ U).mpr
      ⟨restrictCoaction d τ, equivariant_restrict d hU⟩
  obtain ⟨C, hUC, hCD⟩ := semisimple_group_complement hLie DG hDs aD (restrictCoaction d ρ) U hUD
  let p := U.projectionOnto C hUC
  have hp := projection_equivariant (restrictCoaction d ρ) U C hUC
    (restrictCoaction d τ) (equivariant_restrict d hU) hCD
  obtain ⟨q, hqD, hqT, hqi⟩ := weighted_retraction t d ρ τ U.subtype hU
    (central_coordinate a aT iT hc) p hp (U.projectionOnto_comp_subtype hUC)
  have hcompl : IsCompl U (LinearMap.ker q) := LinearMap.isCompl_of_proj
    (fun x => DFunLike.congr_fun hqi x)
  have hC : ρ.IsSubcomodule (LinearMap.ker q) :=
    isSubcomodule_of_product_cover (P := productAlgebraicGroup TG DG) a aT aD iT D.inclusion
      (Specs.CentralDerived.firstProjection T.group D.group)
      (Specs.CentralDerived.secondProjection T.group D.group) m hm hmf hms ρ _
      (kernel_isSubcomodule _ _ q hqT) (kernel_isSubcomodule _ _ q hqD)
  exact ⟨U.projectionOnto (LinearMap.ker q) hcompl,
    projection_equivariant ρ U _ hcompl τ hU hC, U.projectionOnto_comp_subtype hcompl⟩

private theorem reductive_semisimple [CharZero k] [FiniteDimensional k V]
    (hLie : SemisimplyDifferentiated.LieSemisimple.{u}) (G : AffineAlgebraicGroup k)
    (hG : GeometricRadicals.IsReductive G) {A : HopfAlgebraCategory k}
    (a : specGroup A ≅ G.val) (ρ : RightComodule k A V) : IsSemisimple A ρ := by
  let K := AlgebraicClosure k
  let aK := extendedGroupIso K A ≪≫ (groupBaseChange k K).mapIso a
  have hKG := (Reductive.RadicalBaseChange.reductiveFieldExtension
    (K := K) G hG.1 hG.2.1).mpr hG
  let ρK := extendCoaction (K := K) A ρ
  exact semisimplicityDescent A ρ ρK (extendCoaction_isScalarExtension A ρ)
    (split_reductive_semisimple hLie (baseChangedAlgebraicGroup K G) hKG aK ρK)

/-- Complete reducibility in characteristic zero, conditional on the Lie semisimplicity theorem. -/
theorem characteristicZeroCompleteReducibility_conditional
    (hLie : SemisimplyDifferentiated.LieSemisimple.{u}) :
    Specs.CompleteReducibility.CharacteristicZeroCompleteReducibility.{u} := by
  intro k _ _ G _ A a
  constructor
  · constructor
    · intro h V _ _ _ ρ
      exact reductive_semisimple hLie G h a ρ
    · intro h
      obtain ⟨V, _, _, _, ρ, hf⟩ := exists_faithful G A (pointPresentation a)
      exact reductive_of_faithful_semisimple G a ρ hf (h V ρ)
  · constructor
    · intro h
      obtain ⟨V, _, _, _, ρ, hf⟩ := exists_faithful G A (pointPresentation a)
      exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, hf, h V ρ⟩
    · rintro ⟨V, _, _, _, ρ, hf, hs⟩ W _ _ _ σ
      exact reductive_semisimple hLie G (reductive_of_faithful_semisimple G a ρ hf hs) a σ

end
end LinearAlgebraicGroups.Representation.CompleteReducibility

universe v8_closure_b4d732f2dab2717a_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«CompleteReducibility».«characteristicZeroCompleteReducibility» : _root_.«LinearAlgebraicGroups».«Specs».«CompleteReducibility».«CharacteristicZeroCompleteReducibility».{v8_closure_b4d732f2dab2717a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«CompleteReducibility».«characteristicZeroCompleteReducibility_conditional».{v8_closure_b4d732f2dab2717a_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«SemisimplyDifferentiated».«lieSemisimple».{v8_closure_b4d732f2dab2717a_u0})
