import Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitTorusProduct
import LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import LinearAlgebraicGroups.Relative.RationalCocharacter
import LinearAlgebraicGroups.RootData.CharacterPairing
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Coalgebra WithConv
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitTorusProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.QuasiSplitOrbitTorusProduct
open Specs.AdjointBorelCohomology (PermutedCharacterBasis)
open Specs.AdjointCocharacters (coordinateHopfMap coordinateHopfIso)
local notation "coordHopf" => Specs.AdjointCocharacters.coordinateHopf
open Specs.CharacterDescent (GeometricCharacters IsDiagonalizable StandardLattice Character Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open Specs.GeometricRadicals (IsSplitTorus IsTorus)
open Specs.SmoothnessAndIsogenies (pullbackCharacter)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open Descent (SemilinearAction)
open private extendedCoordinateIso extendedCoordinateIso_natural
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private splitPresentation latticeCoordinates charactersOfIso
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private groupLikeIso extendedHopfMap_equivariant
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private torus_of_iso from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_descends_from_algebraic_closure torus_after_algClosed_extension
  from LinearAlgebraicGroups.Reductive.MaximalToriExist
open private groupBaseChangeTowerIso twistMorphism twistedBaseChange twistedBaseChange_inv
  twistCocharacter multiplicativeBaseChange multiplicativeBaseChange_unit galoisCocharacterAction
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private torsionFree_of_diagonal_torus cocharacter_ext_units from LinearAlgebraicGroups.RootData.RankOneFlag

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 70000
set_option backward.isDefEq.respectTransparency false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem splitHopfPresentation (T : AffineAlgebraicGroup F)
    (h : IsSplitTorus ((groupBaseChange F K).obj T.val)) :
    ∃ n : ℕ, Nonempty (groupAlgebra K (StandardLattice.{u} n) ≅
      extendedHopf K (coordHopf T)) := by
  obtain ⟨n, ⟨e⟩⟩ := splitPresentation h
  let g := e ≪≫ (extendedCoordinateIso (K := K) T).symm
  exact ⟨n, ⟨((hopfSpec.fullyFaithful (R := CommRingCat.of K)).preimageIso g).unop.symm⟩⟩

private theorem torusBaseChange (T : AffineAlgebraicGroup F) (h : IsTorus T.val) :
    IsTorus ((groupBaseChange F K).obj T.val) := by
  let L := AlgebraicClosure K
  apply torus_descends_from_algebraic_closure (baseChangedAlgebraicGroup K T)
  exact torus_of_iso ((groupBaseChangeTowerIso (k := F) (K := K) (L := L)).app T.val).symm
    (torus_after_algClosed_extension L T h)

open private latticeEquivOfBasis from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies

private theorem subtorusCharacters {T : AffineAlgebraicGroup F} (S : ClosedSubgroup T.val)
    (hT : IsSplitTorus ((groupBaseChange F K).obj T.val)) (hS : IsTorus S.group) :
    let A := closedSubgroupAlgebraicGroup (G := T) S
    IsDiagonalizable (extendedHopf K (coordHopf A)) ∧
      Module.Finite ℤ (CharacterLattice K A) ∧ Module.Free ℤ (CharacterLattice K A) ∧
      Function.Surjective (characterRestriction K (S := A) (T := T) S.inclusion) ∧
      IsSplitTorus ((groupBaseChange F K).obj S.group) := by
  let A := closedSubgroupAlgebraicGroup (G := T) S
  let B := extendedHopf K (coordHopf A)
  obtain ⟨n, ⟨d⟩⟩ := splitHopfPresentation (K := K) T hT
  let M := StandardLattice.{u} n
  let right := extendedHopfMap K (coordinateHopfMap (G := A) (H := T) S.inclusion)
  let f := d.hom ≫ right
  have hf : Function.Surjective f.hom := by
    apply (hopfMapClosedImmersion K f).mp
    let e := extendedCoordinateIso (K := K) T
    let e' := extendedCoordinateIso (K := K) A
    let q := (groupBaseChange F K).map S.inclusion
    have h := extendedCoordinateIso_natural (K := K) (G := A) (H := T) S.inclusion
    have hr : specGroupMap right = e'.hom ≫ q ≫ e.inv := by
      rw [← Category.assoc, ← h, Category.assoc, e.hom_inv_id, Category.comp_id]
    change IsClosedImmersion (specGroupMap (d.hom ≫ right)).hom.hom.left
    rw [specGroupMap_comp]
    rw [hr]
    let forget := Grp.forget (SchemeOver K) ⋙ Over.forget _
    let ds := (hopfSpec (CommRingCat.of K)).mapIso d.op
    haveI : IsIso (forget.map e'.hom) := forget.map_isIso e'.hom
    haveI : IsIso (forget.map e.inv) := forget.map_isIso e.inv
    haveI : IsIso (forget.map ds.hom) := forget.map_isIso ds.hom
    haveI : IsClosedImmersion (forget.map q) :=
      baseChangeClosedSubgroup F K S.inclusion S.isClosedImmersion
    change IsClosedImmersion (((forget.map e'.hom ≫ forget.map q) ≫ forget.map e.inv) ≫
      forget.map ds.hom)
    infer_instance
  obtain ⟨N, ⟨v, hv⟩, _⟩ := (DiagonalizableGroups.hopfQuotientClassification K M f).mp hf
  let e : groupAlgebra K (M ⧸ N) ≅ B := CommHopfAlgCat.isoMk v
  let equivalence := (CharacterDescent.monomialCharacterEquiv K).trans (groupLikeIso e)
  let hTor : IsTorus (specGroup (groupAlgebra K (M ⧸ N))) :=
    torus_of_iso ((hopfSpec (CommRingCat.of K)).mapIso e.symm.op ≪≫
      extendedCoordinateIso (K := K) A).symm (torusBaseChange (K := K) A hS)
  letI : Module.IsTorsionFree ℤ (Additive (M ⧸ N)) := torsionFree_of_diagonal_torus _ hTor
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates n).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  letI : Module.Finite ℤ (Additive (M ⧸ N)) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let lin : Additive (M ⧸ N) ≃ₗ[ℤ] CharacterLattice K A :=
    equivalence.toAdditive.toIntLinearEquiv
  letI : Module.Finite ℤ (CharacterLattice K A) := Module.Finite.equiv lin
  obtain ⟨m, c⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ) (M := Additive (M ⧸ N))
  let w : groupAlgebra K (M ⧸ N) ≅ groupAlgebra K (StandardLattice.{u} m) :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv K K (latticeEquivOfBasis c))
  obtain ⟨t⟩ := CharacterDescent.standardSplitTorus (k := K) m
  have split : IsSplitTorus ((groupBaseChange F K).obj S.group) :=
    ⟨m, ⟨(extendedCoordinateIso (K := K) A).symm ≪≫
      (hopfSpec (CommRingCat.of K)).mapIso (w.symm ≪≫ e).op ≪≫ t⟩⟩
  refine ⟨⟨⟨CommGrpCat.of (M ⧸ N), inferInstance⟩, ⟨e⟩⟩, inferInstance,
    Module.Free.of_basis (c.map lin), ?_, split⟩
  intro x
  obtain ⟨z, hz⟩ := equivalence.surjective x.toMul
  obtain ⟨m', rfl⟩ := QuotientGroup.mk'_surjective N z
  let toAmbient :=  (CharacterDescent.monomialCharacterEquiv K).trans (groupLikeIso d)
  refine ⟨Additive.ofMul (toAmbient m'), ?_⟩
  apply Additive.toMul.injective
  apply GroupLike.val_injective
  have hv' := DFunLike.congr_fun hv (MonoidAlgebra.single m' 1)
  change right.hom (d.hom.hom (MonoidAlgebra.single m' 1)) = x.toMul.val
  rw [← hz]
  change f.hom (MonoidAlgebra.single m' 1) =
    v.toBialgHom (MonoidAlgebra.single (QuotientGroup.mk' N m') 1)
  simpa only [BialgHom.comp_apply, MonoidAlgebra.mapDomainBialgHom_single] using hv'.symm

/-- The orbit subtori can use the same splitting field as the ambient torus. -/
theorem splitClosedSubtorus : SplitClosedSubtorus.{u} := by
  intro F K _ _ _ T S hT hS
  exact (subtorusCharacters (K := K) S hT hS).2.2.2.2

private def dualCharacterBasis {I X : Type u} [Finite I]
    [AddCommGroup X] [Module ℤ X] [Module.IsReflexive ℤ X]
    (b : Module.Basis I ℤ (Module.Dual ℤ X)) : Module.Basis I ℤ X := by
  classical
  exact b.dualBasis.map (Module.evalEquiv ℤ X).symm

private theorem dualCharacterBasis_apply {I X : Type u} [Finite I]
    [AddCommGroup X] [Module ℤ X] [Module.IsReflexive ℤ X]
    (b : Module.Basis I ℤ (Module.Dual ℤ X)) (i l : I) :
    b l (dualCharacterBasis b i) = (by classical exact if i = l then 1 else 0) := by
  classical
  rw [dualCharacterBasis, Module.Basis.map_apply, Module.apply_evalEquiv_symm_apply,
    Module.Basis.dualBasis_apply_self]
  by_cases h : i = l
  · simp [h]
  · simp [h, Ne.symm h]

private theorem restriction_coordinates {I X Y : Type u} [Finite I]
    [AddCommGroup X] [Module ℤ X] [Module.IsReflexive ℤ X]
    [AddCommGroup Y] [Module ℤ Y] [Module.IsReflexive ℤ Y]
    (b : Module.Basis I ℤ (Module.Dual ℤ X))
    (j : X →ₗ[ℤ] Y) (hj : Function.Surjective j) (s : Set I)
    (hs : LinearMap.range j.dualMap = Submodule.span ℤ (b '' s)) :
    (∀ i, i ∉ s → j (dualCharacterBasis b i) = 0) ∧
      ∃ c : Module.Basis s ℤ Y, ∀ i : s, c i = j (dualCharacterBasis b i.1) := by
  classical
  let d := dualCharacterBasis b
  have coord (i : I) (v : Module.Dual ℤ X) : v (d i) = b.repr v i := by
    dsimp only [d, dualCharacterBasis, Module.Basis.map_apply]
    rw [Module.apply_evalEquiv_symm_apply, Module.Basis.dualBasis_apply]
  have hz (i : I) (hi : i ∉ s) : j (d i) = 0 := by
    apply (Module.evalEquiv ℤ Y).injective
    ext v
    change (j.dualMap v) (d i) = _
    rw [map_zero, coord]
    have hmem : j.dualMap v ∈ Submodule.span ℤ (b '' s) :=
      hs ▸ LinearMap.mem_range_self j.dualMap v
    obtain h := (b.mem_span_image.mp hmem)
    exact Finsupp.notMem_support_iff.mp (fun h' => hi (h h'))
  refine ⟨hz, ?_⟩
  letI := Fintype.ofFinite s
  let a : s → Y := fun i => j (d i.1)
  have tests (i : s) : b i.1 ∈ LinearMap.range j.dualMap := by
    rw [hs]
    exact Submodule.subset_span (Set.mem_image_of_mem b i.2)
  choose v hv using tests
  let e : Y →ₗ[ℤ] (s → ℤ) := LinearMap.pi v
  have he (i : s) : e (a i) = (Pi.basisFun ℤ s) i := by
    ext l
    change (j.dualMap (v l)) (d i.1) = _
    rw [hv, dualCharacterBasis_apply, Pi.basisFun_apply, Pi.single_apply]
    simp only [Subtype.ext_iff, eq_comm]
  have hli : LinearIndependent ℤ a := by
    apply LinearIndependent.of_comp e
    simpa only [Function.comp_def, he] using (Pi.basisFun ℤ s).linearIndependent
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range a) := by
    rw [← LinearMap.range_eq_top.mpr hj, ← Submodule.map_top, ← d.span_eq, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i ∈ s
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [hz i hi]
      exact Submodule.zero_mem _
  exact ⟨Module.Basis.mk hli hsp, Module.Basis.mk_apply hli hsp⟩

section Permutation

variable {I : Type u} [Fintype I] {T : AffineAlgebraicGroup F}
  {ρ : Gal(K/F) →* Equiv.Perm I}

private def permutedDualBasis [Module.IsReflexive ℤ (CharacterLattice K T)]
    (b : Module.Basis I ℤ (CocharacterLattice K T))
    (h : ∀ (σ : Gal(K/F)) (i : I) (χ ψ : CharacterLattice K T),
      (SemilinearAction.scalarExtension (K := K) (coordHopf T)).act σ χ.toMul.val =
        ψ.toMul.val → b (ρ σ i) ψ = b i χ) : PermutedCharacterBasis K I T ρ := by
  classical
  let d := dualCharacterBasis b
  refine ⟨d, fun σ i => ?_⟩
  let a := CharacterDescent.geometricAction K (coordHopf T) σ
  let x : CharacterLattice K T := Additive.ofMul (a.asHom (d i).toMul)
  have hx : x = d (ρ σ i) := by
    apply (Module.evalEquiv ℤ (CharacterLattice K T)).injective
    apply b.ext
    intro j
    obtain ⟨l, rfl⟩ := (ρ σ).surjective j
    change b (ρ σ l) x = b (ρ σ l) (d (ρ σ i))
    rw [h σ l (d i) x rfl, dualCharacterBasis_apply, dualCharacterBasis_apply,
      (ρ σ).injective.eq_iff]
  exact congrArg (fun v : CharacterLattice K T => v.toMul.val) hx

end Permutation

private def fixedEvaluation {Γ J M : Type u} [Group Γ] [MulAction Γ J] [MulAction Γ M] (i : J)
    (v : {v : J → M // ∀ (σ : Γ) l, v (σ • l) = σ • v l}) :
    {x : M // ∀ σ ∈ MulAction.stabilizer Γ i, σ • x = x} :=
  ⟨v.val i, fun σ hσ =>
    (v.property σ i).symm.trans (congrArg v.val (MulAction.mem_stabilizer_iff.mp hσ))⟩

private theorem fixedEvaluation_bijective {Γ J M : Type u} [Group Γ] [MulAction Γ J]
    [MulAction Γ M] (i : J) (h : ∀ l : J, ∃ σ : Γ, σ • i = l) :
    Function.Bijective (fixedEvaluation (Γ := Γ) (M := M) i) := by
  classical
  choose g hg using h
  constructor
  · intro v w hvw
    apply Subtype.ext
    funext l
    calc
      v.val l = g l • v.val i := (congrArg v.val (hg l).symm).trans (v.property (g l) i)
      _ = g l • w.val i := congrArg (g l • ·) (congrArg Subtype.val hvw)
      _ = w.val l := ((congrArg w.val (hg l).symm).trans (w.property (g l) i)).symm
  · intro x
    let v (l : J) := g l • x.val
    have eval (l : J) (σ : Γ) (hσ : σ • i = l) : v l = σ • x.val := by
      have hs : σ⁻¹ * g l ∈ MulAction.stabilizer Γ i := by
        apply MulAction.mem_stabilizer_iff.mpr
        rw [mul_smul, hg, ← hσ, inv_smul_smul]
      have hf := congrArg (σ • ·) (x.property _ hs)
      simpa only [mul_smul, smul_inv_smul] using hf
    refine ⟨⟨v, fun σ l => ?_⟩, Subtype.ext ?_⟩
    · rw [eval (σ • l) (σ * g l) (by rw [mul_smul, hg]), mul_smul]
    · exact (eval i 1 (one_smul Γ i)).trans (one_smul Γ x.val)

open private pointCharacters pointCharacters_equivariant pointCharacters_bijective
  extendCoordinatePoint extendCoordinatePoint_mul groupLikeEvaluation
  fixedFieldTensor fixedFieldTensorUnits fixedFieldTensor_injective fixedFieldTensor_natural
  tensorUnitAction from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

open private coordinatePresentationMap from LinearAlgebraicGroups.Descent.AdjointCocharacters
open private hopfPoint_map from LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
open WeilRestriction (extendedUnits tensorMap multiplicativeRestriction multiplicativeRestrictionUnits)

private def pointCoordinates (T : AffineAlgebraicGroup F) :
    convolutionPoints (coordHopf T) ≅ (groupPointsFunctor F).obj T.val :=
  hopfSpecPointIso _ ≪≫ (groupPointsFunctor F).mapIso (coordinateHopfIso T)

private theorem fromCoordinates_map {T S : AffineAlgebraicGroup F} (f : S.val ⟶ T.val)
    (R : TestAlgebra F) (x : WithConv (coordHopf S →ₐ[F] R)) :
    ((groupPointsFunctor F).map f).app R ((pointCoordinates S).hom.app R x) =
      (pointCoordinates T).hom.app R
        (toConv (x.ofConv.comp (coordinateHopfMap (G := S) (H := T) f).hom.toAlgHom)) := by
  let P := groupPointsFunctor F
  let a := coordinateHopfMap (G := S) (H := T) f
  have hf : (coordinateHopfIso S).hom ≫ f = specGroupMap a ≫ (coordinateHopfIso T).hom := by
    rw [coordinatePresentationMap]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := ConcreteCategory.congr_hom (congrArg (fun g => g.app R)
    (show P.map (coordinateHopfIso S).hom ≫ P.map f =
        P.map (specGroupMap a) ≫ P.map (coordinateHopfIso T).hom by
      rw [← P.map_comp, ← P.map_comp, hf]))
    ((hopfSpecPointIso (coordHopf S)).hom.app R x)
  change ((P.map f).app R) (((P.map (coordinateHopfIso S).hom).app R)
      ((hopfSpecPointIso (coordHopf S)).hom.app R x)) =
    ((P.map (coordinateHopfIso T).hom).app R)
      (((P.map (specGroupMap a)).app R) ((hopfSpecPointIso (coordHopf S)).hom.app R x)) at h
  rw [hopfPoint_map] at h
  exact h

private theorem pointCoordinates_cancel (A : AffineAlgebraicGroup F) (R : TestAlgebra F)
  (z : WithConv (coordHopf A →ₐ[F] R)) :
    ((algSpec.fullyFaithful (R := CommRingCat.of F)).preimage
      ((pointCoordinates A).hom.app R z ≫ (coordinateHopfIso A).inv.hom.hom)).unop.hom =
    z.ofConv := by
  change ((algSpec.fullyFaithful (R := CommRingCat.of F)).preimage
    (((hopfSpecPointIso (coordHopf A)).hom.app R z) ≫
      (coordinateHopfIso A).hom.hom.hom ≫ (coordinateHopfIso A).inv.hom.hom)).unop.hom = _
  have h := (Grp.forget (SchemeOver F)).congr_map (coordinateHopfIso A).hom_inv_id
  change (coordinateHopfIso A).hom.hom.hom ≫ (coordinateHopfIso A).inv.hom.hom = 𝟙 _ at h
  rw [h, Category.comp_id]
  change ((algSpec.fullyFaithful (R := CommRingCat.of F)).preimage
    ((testSpec F).map (CommAlgCat.ofHom z.ofConv).op)).unop.hom = _
  rw [Functor.FullyFaithful.preimage_map]
  rfl

private theorem evaluation_restriction {T S : AffineAlgebraicGroup F} (f : S.val ⟶ T.val)
    (R : TestAlgebra F) (x : ((groupPointsFunctor F).obj S.val).obj R)
    (χ : CharacterLattice K T) :
    evaluateCharacter T R (((groupPointsFunctor F).map f).app R x) χ =
      evaluateCharacter S R x (characterRestriction K (S := S) (T := T) f χ) := by
  let c := (pointCoordinates S).hom.app R
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso c).2 x
  rw [fromCoordinates_map]
  unfold evaluateCharacter
  dsimp only
  rw [pointCoordinates_cancel, pointCoordinates_cancel]
  apply Units.ext
  change (Algebra.TensorProduct.map (AlgHom.id K K)
      (y.ofConv.comp (coordinateHopfMap (G := S) (H := T) f).hom.toAlgHom)) χ.toMul.val =
    (Algebra.TensorProduct.map (AlgHom.id K K) y.ofConv)
      ((Algebra.TensorProduct.map (AlgHom.id K K)
        (coordinateHopfMap (G := S) (H := T) f).hom.toAlgHom) χ.toMul.val)
  exact AlgHom.congr_fun (by
    simpa only [AlgHom.id_comp] using
      (Algebra.TensorProduct.map_comp (AlgHom.id K K) (AlgHom.id K K)
        y.ofConv (coordinateHopfMap (G := S) (H := T) f).hom.toAlgHom)) χ.toMul.val

private theorem evaluateCharacter_coordinates (T : AffineAlgebraicGroup F)
    (R : TestAlgebra F) (x : ((groupPointsFunctor F).obj T.val).obj R)
    (χ : CharacterLattice K T) :
    evaluateCharacter T R x χ =
      groupLikeEvaluation (extendCoordinatePoint R ((pointCoordinates T).inv.app R x).ofConv)
        χ.toMul := by
  let f := (pointCoordinates T).hom.app R
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso f).2 x
  unfold evaluateCharacter
  rw [pointCoordinates_cancel]
  have h := ConcreteCategory.congr_hom (congrArg (fun g => g.app R)
    (pointCoordinates T).hom_inv_id) y
  change (pointCoordinates T).inv.app R ((pointCoordinates T).hom.app R y) = y at h
  rw [h]
  rfl

private def evaluationHom (T : AffineAlgebraicGroup F) (R : TestAlgebra F)
    (χ : CharacterLattice K T) :
    ((groupPointsFunctor F).obj T.val).obj R →* (K ⊗[F] R)ˣ := by
  have mul_eval (x y : ((groupPointsFunctor F).obj T.val).obj R) :
      evaluateCharacter T R (x * y) χ = evaluateCharacter T R x χ * evaluateCharacter T R y χ := by
    simp only [evaluateCharacter_coordinates]
    let m := ((pointCoordinates T).inv.app R).hom
    have hm : m (x * y) = m x * m y := map_mul m x y
    change groupLikeEvaluation (extendCoordinatePoint R (m (x * y)).ofConv) χ.toMul = _
    rw [hm, extendCoordinatePoint_mul]
    apply Units.ext
    let a : WithConv (extendedHopf K (coordHopf T) →ₐ[K] K ⊗[F] R) :=
      toConv (extendCoordinatePoint R (m x).ofConv)
    let b : WithConv (extendedHopf K (coordHopf T) →ₐ[K] K ⊗[F] R) :=
      toConv (extendCoordinatePoint R (m y).ofConv)
    change (a * b).ofConv χ.toMul.val = a.ofConv χ.toMul.val * b.ofConv χ.toMul.val
    rw [AlgHom.convMul_apply, χ.toMul.2.comul_eq_tmul_self, Algebra.TensorProduct.lift_tmul]
  exact { toFun := fun x => evaluateCharacter T R x χ
          map_one' := by
            have h := mul_eval 1 1
            rw [one_mul] at h
            exact mul_eq_left.mp h.symm
          map_mul' := mul_eval }

private theorem evaluateCharacter_natural (T : AffineAlgebraicGroup F)
    {R S : TestAlgebra F} (g : R ⟶ S)
    (x : ((groupPointsFunctor F).obj T.val).obj R) (χ : CharacterLattice K T) :
    evaluateCharacter T S (((groupPointsFunctor F).obj T.val).map g x) χ =
      Units.map (Algebra.TensorProduct.map (AlgHom.id K K) g.hom).toMonoidHom
        (evaluateCharacter T R x χ) := by
  simp only [evaluateCharacter_coordinates]
  have h := (pointCoordinates T).inv.naturality_apply g x
  let f := (pointCoordinates T).inv.app R x
  change (pointCoordinates T).inv.app S (((groupPointsFunctor F).obj T.val).map g x) =
    toConv (g.hom.comp f.ofConv) at h
  rw [h]
  apply Units.ext
  change (Algebra.TensorProduct.map (AlgHom.id K K) (g.hom.comp f.ofConv)) χ.toMul.val =
    (Algebra.TensorProduct.map (AlgHom.id K K) g.hom)
      ((Algebra.TensorProduct.map (AlgHom.id K K) f.ofConv) χ.toMul.val)
  exact AlgHom.congr_fun (by
    simpa only [AlgHom.id_comp] using
      (Algebra.TensorProduct.map_comp (AlgHom.id K K) (AlgHom.id K K) g.hom f.ofConv)) χ.toMul.val

section Profiles

variable {I : Type u} {T : AffineAlgebraicGroup F}
  {ρ : Gal(K/F) →* Equiv.Perm I}


private def characterProfile (d : PermutedCharacterBasis K I T ρ) (R : TestAlgebra F) :
    letI := MulAction.compHom I ρ
    letI := tensorUnitAction (K := K) R
    ((groupPointsFunctor F).obj T.val).obj R →
      {v : I → (K ⊗[F] R)ˣ // ∀ (σ : Gal(K/F)) i, v (σ • i) = σ • v i} := by
  letI := MulAction.compHom I ρ
  letI := tensorUnitAction (K := K) R
  intro x
  refine ⟨fun i => evaluateCharacter T R x (d.basis i), ?_⟩
  intro σ i
  change evaluateCharacter T R x (d.basis (ρ σ i)) =
    σ • evaluateCharacter T R x (d.basis i)
  rw [evaluateCharacter_coordinates, evaluateCharacter_coordinates]
  exact pointCharacters_equivariant R d ((pointCoordinates T).inv.app R x).ofConv σ i

private theorem characterProfile_bijective [IsGalois F K]
    (d : PermutedCharacterBasis K I T ρ) (hT : IsDiagonalizable (extendedHopf K (coordHopf T)))
    (R : TestAlgebra F) : Function.Bijective (characterProfile d R) := by
  letI := MulAction.compHom I ρ
  letI := tensorUnitAction (K := K) R
  let e := ((pointCoordinates T).app R).symm.groupIsoToMulEquiv
  have he : Function.Bijective (fun x => (e x).ofConv) := ofConv_bijective.comp e.bijective
  have h : characterProfile d R =
      (fun f => ⟨pointCharacters R d f, pointCharacters_equivariant R d f⟩) ∘
        (fun x => (e x).ofConv) := by
    funext x
    apply Subtype.ext
    funext i
    change evaluateCharacter T R x (d.basis i) =
      groupLikeEvaluation (extendCoordinatePoint R ((pointCoordinates T).inv.app R x).ofConv)
        (d.basis i).toMul
    exact evaluateCharacter_coordinates T R x (d.basis i)
  rw [h]
  exact (pointCharacters_bijective R d hT).comp he

private def weilCoordinate (d : PermutedCharacterBasis K I T ρ) (i : I) (R : TestAlgebra F)
    (x : ((groupPointsFunctor F).obj T.val).obj R) :
    letI := MulAction.compHom I ρ
    (R ⊗[F] IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i))ˣ := by
  letI := MulAction.compHom I ρ
  letI := tensorUnitAction (K := K) R
  exact (fixedFieldTensorUnits R (MulAction.stabilizer Gal(K/F) i)).symm
    (fixedEvaluation (Γ := Gal(K/F)) i (characterProfile d R x))

private theorem weilCoordinate_spec (d : PermutedCharacterBasis K I T ρ) (i : I)
    (R : TestAlgebra F) (x : ((groupPointsFunctor F).obj T.val).obj R) :
    letI := MulAction.compHom I ρ
    Units.map (orbitFieldInclusion R (MulAction.stabilizer Gal(K/F) i)).toMonoidHom
      (weilCoordinate d i R x) = evaluateCharacter T R x (d.basis i) := by
  letI := MulAction.compHom I ρ
  letI := tensorUnitAction (K := K) R
  let J := MulAction.stabilizer Gal(K/F) i
  let t := fixedEvaluation (Γ := Gal(K/F)) i (characterProfile d R x)
  have hh := congrArg Subtype.val ((fixedFieldTensorUnits R J).apply_symm_apply t)
  change Units.map (fixedFieldTensor R J).toMonoidHom ((fixedFieldTensorUnits R J).symm t) =
    t.val at hh
  change Units.map (fixedFieldTensor R J).toMonoidHom ((fixedFieldTensorUnits R J).symm t) =
    t.val
  exact hh

private def weilPointMap (d : PermutedCharacterBasis K I T ρ) (i : I) :
    letI := MulAction.compHom I ρ
    (groupPointsFunctor F).obj T.val ⟶
      extendedUnits F (IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)) := by
  letI := MulAction.compHom I ρ
  let J := MulAction.stabilizer Gal(K/F) i
  let E := IntermediateField.fixedField J
  have injective (R : TestAlgebra F) :
      Function.Injective (Units.map (orbitFieldInclusion R J).toMonoidHom) :=
    Units.map_injective (fixedFieldTensor_injective R J)
  refine
    { app := fun R => GrpCat.ofHom
        { toFun := weilCoordinate d i R
          map_one' := ?_
          map_mul' := ?_ }
      naturality := ?_ }
  · apply injective R
    rw [map_one, weilCoordinate_spec]
    simpa only [evaluationHom, MonoidHom.coe_mk, OneHom.coe_mk] using
      (evaluationHom T R (d.basis i)).map_one
  · intro x y
    apply injective R
    rw [map_mul, weilCoordinate_spec, weilCoordinate_spec, weilCoordinate_spec]
    simpa only [evaluationHom, MonoidHom.coe_mk, OneHom.coe_mk] using
      (evaluationHom T R (d.basis i)).map_mul x y
  · intro R S g
    apply GrpCat.ext
    intro x
    apply injective S
    change Units.map (orbitFieldInclusion S J).toMonoidHom
      (weilCoordinate d i S (((groupPointsFunctor F).obj T.val).map g x)) =
      Units.map (orbitFieldInclusion S J).toMonoidHom
        (Units.map (tensorMap F E g.hom).toMonoidHom (weilCoordinate d i R x))
    rw [weilCoordinate_spec, evaluateCharacter_natural, ← weilCoordinate_spec d i R x]
    apply Units.ext
    exact (fixedFieldTensor_natural g J (weilCoordinate d i R x).val).symm

end Profiles

@[instance_reducible] private def orbitAction {Γ I : Type u} [Group Γ] [MulAction Γ I]
    (o : MulAction.orbitRel.Quotient Γ I) :
    MulAction Γ {i : I // Quotient.mk (MulAction.orbitRel Γ I) i = o} where
  smul σ i := ⟨σ • i.val, (Quotient.sound (MulAction.orbitRel_apply.mpr
    (MulAction.mem_orbit_iff.mpr ⟨σ, rfl⟩))).trans i.property⟩
  one_smul i := Subtype.ext (one_smul Γ i.val)
  mul_smul σ τ i := Subtype.ext (mul_smul σ τ i.val)

section Factors

variable {I : Type u} {T : AffineAlgebraicGroup F}
  {ρ : Gal(K/F) →* Equiv.Perm I}

local notation "Orbit" => @MulAction.orbitRel.Quotient Gal(K/F) I _ (MulAction.compHom I ρ)
local notation "orbitOf" => Quotient.mk (@MulAction.orbitRel Gal(K/F) I _ (MulAction.compHom I ρ))
local notation "vertices" o => {i : I // orbitOf i = o}

private def restrictBasis {S : AffineAlgebraicGroup F} (f : S.val ⟶ T.val)
    (d : PermutedCharacterBasis K I T ρ) (o : Orbit)
    (c : Module.Basis (vertices o) ℤ (CharacterLattice K S))
    (hc : ∀ i, c i = characterRestriction K (S := S) (T := T) f (d.basis i.val)) :
    letI := MulAction.compHom I ρ
    letI := orbitAction o
    PermutedCharacterBasis K (vertices o) S (MulAction.toPermHom Gal(K/F) (vertices o)) := by
  letI := MulAction.compHom I ρ
  letI := orbitAction o
  refine ⟨c, fun σ i => ?_⟩
  rw [hc, hc]
  let g := coordinateHopfMap (G := S) (H := T) f
  change (SemilinearAction.scalarExtension (K := K) (coordHopf S)).act σ
      ((extendedHopfMap K g).hom (d.basis i.val).toMul.val) =
    (extendedHopfMap K g).hom (d.basis (ρ σ i.val)).toMul.val
  have hg := extendedHopfMap_equivariant K g σ (d.basis i.val).toMul.val
  change (extendedHopfMap K g).hom
      ((SemilinearAction.scalarExtension (K := K) (coordHopf T)).act σ
        (d.basis i.val).toMul.val) =
    (SemilinearAction.scalarExtension (K := K) (coordHopf S)).act σ
      ((extendedHopfMap K g).hom (d.basis i.val).toMul.val) at hg
  rw [← hg, d.permutation]

private theorem orbit_transitive (i : I) (l : vertices (orbitOf i)) :
    letI := MulAction.compHom I ρ
    letI := orbitAction (orbitOf i)
    ∃ σ : Gal(K/F), σ • (⟨i, rfl⟩ : vertices (orbitOf i)) = l := by
  letI := MulAction.compHom I ρ
  letI := orbitAction (orbitOf i)
  obtain ⟨σ, hσ⟩ :=
    MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact l.property))
  exact ⟨σ, Subtype.ext hσ⟩

private theorem factorWeilMap_bijective [IsGalois F K] {S : AffineAlgebraicGroup F}
    (f : S.val ⟶ T.val) (d : PermutedCharacterBasis K I T ρ) (i : I)
    (c : Module.Basis (vertices (orbitOf i)) ℤ (CharacterLattice K S))
    (hc : ∀ l, c l = characterRestriction K (S := S) (T := T) f (d.basis l.val))
    (hS : IsDiagonalizable (extendedHopf K (coordHopf S))) (R : TestAlgebra F) :
    Function.Bijective
      (fun x => weilCoordinate d i R (((groupPointsFunctor F).map f).app R x)) := by
  letI := MulAction.compHom I ρ
  let J := MulAction.stabilizer Gal(K/F) i
  let U := vertices (orbitOf i)
  letI := orbitAction (orbitOf i)
  letI := tensorUnitAction (K := K) R
  let u : U := ⟨i, rfl⟩
  let r := MulAction.toPermHom Gal(K/F) U
  let d' : PermutedCharacterBasis K U S r := restrictBasis f d (orbitOf i) c hc
  have hJ : MulAction.stabilizer Gal(K/F) u = J := by
    ext σ
    change σ • u = u ↔ ρ σ i = i
    exact Subtype.ext_iff
  let transport : {x : (K ⊗[F] R)ˣ // ∀ σ ∈ MulAction.stabilizer Gal(K/F) u, σ • x = x} ≃
      {x : (K ⊗[F] R)ˣ // ∀ σ ∈ J, σ • x = x} :=
    Equiv.subtypeEquivProp (by rw [hJ])
  let h := (fixedEvaluation_bijective (Γ := Gal(K/F)) (M := (K ⊗[F] R)ˣ)
    (J := U) u (orbit_transitive (ρ := ρ) i)).comp (characterProfile_bijective d' hS R)
  have hbij := (fixedFieldTensorUnits R J).symm.bijective.comp (transport.bijective.comp h)
  convert hbij using 1
  funext x
  apply (fixedFieldTensorUnits R J).injective
  apply Subtype.ext
  change Units.map (orbitFieldInclusion R J).toMonoidHom
    (weilCoordinate d i R (((groupPointsFunctor F).map f).app R x)) =
      ((fixedFieldTensorUnits R J) ((fixedFieldTensorUnits R J).symm
        (transport (fixedEvaluation (Γ := Gal(K/F)) u (characterProfile d' R x))))).val
  rw [weilCoordinate_spec, Equiv.apply_symm_apply, evaluation_restriction]
  change evaluateCharacter S R x (characterRestriction K (S := S) (T := T) f (d.basis i)) =
    evaluateCharacter S R x (c u)
  rw [hc]

private theorem affinePointEquivalence {G W : GroupScheme F}
    (hG : IsAffine G.X.left) (hW : IsAffine W.X.left)
    (e : (groupPointsFunctor F).obj G ≅ (groupPointsFunctor F).obj W) :
    ∃ a : G ≅ W, (groupPointsFunctor F).map a.hom = e.hom := by
  let P := groupPointsFunctor F
  obtain ⟨f, hf⟩ := (groupHomComparison F G W hG).2 e.hom
  obtain ⟨g, hg⟩ := (groupHomComparison F W G hW).2 e.inv
  change P.map f = e.hom at hf
  change P.map g = e.inv at hg
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (groupHomComparison F G G hG).1
    change P.map (f ≫ g) = P.map (𝟙 G)
    rw [P.map_comp, hf, hg, P.map_id, e.hom_inv_id]
  · apply (groupHomComparison F W W hW).1
    change P.map (g ≫ f) = P.map (𝟙 W)
    rw [P.map_comp, hg, hf, P.map_id, e.inv_hom_id]

private theorem factorWeilIso [Module.Finite F K] [IsGalois F K] {S : AffineAlgebraicGroup F}
    (f : S.val ⟶ T.val) (d : PermutedCharacterBasis K I T ρ) (i : I)
    (c : Module.Basis (vertices (orbitOf i)) ℤ (CharacterLattice K S))
    (hc : ∀ l, c l = characterRestriction K (S := S) (T := T) f (d.basis l.val))
    (hS : IsDiagonalizable (extendedHopf K (coordHopf S))) :
    letI := MulAction.compHom I ρ
    let E := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
    ∃ (W : AffineAlgebraicGroup F) (e : S.val ≅ W.val)
      (w : (groupPointsFunctor F).obj W.val ≅ extendedUnits F E),
      ∀ (R : TestAlgebra F) (x : ((groupPointsFunctor F).obj S.val).obj R),
        Units.map (orbitFieldInclusion R (MulAction.stabilizer Gal(K/F) i)).toMonoidHom
          (w.hom.app R (((groupPointsFunctor F).map e.hom).app R x)) =
        evaluateCharacter T R (((groupPointsFunctor F).map f).app R x) (d.basis i) := by
  letI := MulAction.compHom I ρ
  let J := MulAction.stabilizer Gal(K/F) i
  let E := IntermediateField.fixedField J
  let P := groupPointsFunctor F
  let m := P.map f ≫ weilPointMap d i
  haveI (R : TestAlgebra F) : IsIso (m.app R) := by
    let e : ((P.obj S.val).obj R) ≅ (extendedUnits F E).obj R :=
      (MulEquiv.ofBijective (m.app R).hom
        (factorWeilMap_bijective f d i c hc hS R)).toGrpIso
    exact e.isIso_hom
  haveI : IsIso m := NatIso.isIso_of_isIso_app m
  let W := multiplicativeRestriction F E
  let w := multiplicativeRestrictionUnits F E
  obtain ⟨a, ha⟩ := affinePointEquivalence S.property.1 W.property.1 (asIso m ≪≫ w.symm)
  refine ⟨W, a, w, fun R x => ?_⟩
  have hh : P.map a.hom ≫ w.hom = m := by
    rw [ha]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hh' := ConcreteCategory.congr_hom (congrArg (fun a => a.app R) hh) x
  change w.hom.app R ((P.map a.hom).app R x) = weilCoordinate d i R ((P.map f).app R x) at hh'
  rw [hh', weilCoordinate_spec]

end Factors

open private orbitPoint orbitPoint_spec orbitPoint_bijective
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

section Product

variable {I : Type u} [Fintype I] {T : AffineAlgebraicGroup F}
  {ρ : Gal(K/F) →* Equiv.Perm I}

local notation "Orbit" => @MulAction.orbitRel.Quotient Gal(K/F) I _ (MulAction.compHom I ρ)
local notation "orbitOf" => Quotient.mk (@MulAction.orbitRel Gal(K/F) I _ (MulAction.compHom I ρ))
local notation "vertices" o => {i : I // orbitOf i = o}

omit [Fintype I] in
private theorem orbitCoordinates_bijective [IsGalois F K]
    (d : PermutedCharacterBasis K I T ρ) (hT : IsDiagonalizable (extendedHopf K (coordHopf T)))
    (R : TestAlgebra F) :
    Function.Bijective (fun x => fun o : Orbit => weilCoordinate d o.out R x) := by
  letI := MulAction.compHom I ρ
  let e := ((pointCoordinates T).app R).symm.groupIsoToMulEquiv
  have he : Function.Bijective (fun x => (e x).ofConv) := ofConv_bijective.comp e.bijective
  have h : (fun x => fun o : Orbit => weilCoordinate d o.out R x) =
      orbitPoint R d ∘ (fun x => (e x).ofConv) := by
    funext x o
    let J := MulAction.stabilizer Gal(K/F) o.out
    apply Units.map_injective (fixedFieldTensor_injective R J)
    change Units.map (orbitFieldInclusion R J).toMonoidHom (weilCoordinate d o.out R x) =
      Units.map (fixedFieldTensor R J).toMonoidHom (orbitPoint R d (e x).ofConv o)
    rw [weilCoordinate_spec, orbitPoint_spec]
    change evaluateCharacter T R x (d.basis o.out) =
      groupLikeEvaluation (extendCoordinatePoint R ((pointCoordinates T).inv.app R x).ofConv)
        (d.basis o.out).toMul
    exact evaluateCharacter_coordinates T R x (d.basis o.out)
  rw [h]
  exact (orbitPoint_bijective R d hT).comp he

private theorem productPoints_bijective {O : Type u} [Finite O] {S : O → GroupScheme F}
    (P : Fan S) (hP : IsLimit P) (R : TestAlgebra F) :
    Function.Bijective (fun x => fun o => ((groupPointsFunctor F).map (P.proj o)).app R x) := by
  let U := Grp.forget (SchemeOver F)
  let h := (Fan.isLimitMapConeEquiv U S P) (isLimitOfPreserves U hP)
  constructor
  · intro x y eq
    exact Fan.IsLimit.hom_ext h _ _ (congrFun eq)
  · intro x
    exact ⟨Fan.IsLimit.lift h x, funext (fun o => Fan.IsLimit.fac h _ o)⟩

private theorem affineProduct {O : Type u} [Finite O] {S : O → GroupScheme F}
    (P : Fan S) (hP : IsLimit P) (hS : ∀ o, IsAffine (S o).X.left) :
    IsAffine P.pt.X.left := by
  let U := Grp.forget (SchemeOver F)
  let R := algSpec (CommRingCat.of F)
  letI := (algSpec.fullyFaithful (R := CommRingCat.of F)).full
  letI := (algSpec.fullyFaithful (R := CommRingCat.of F)).faithful
  letI : R.IsRightAdjoint := (algΓAlgSpecAdjunction (CommRingCat.of F)).isRightAdjoint
  apply essImage_algSpec.mp
  exact R.essImage.prop_of_isLimit (isLimitOfPreserves U hP)
    (fun o => essImage_algSpec.mpr (hS o.as))

private theorem evaluateCharacter_zero (T : AffineAlgebraicGroup F) (R : TestAlgebra F)
    (x : ((groupPointsFunctor F).obj T.val).obj R) :
    evaluateCharacter (K := K) T R x 0 = 1 := by
  rw [evaluateCharacter_coordinates]
  change groupLikeEvaluation (extendCoordinatePoint R ((pointCoordinates T).inv.app R x).ofConv)
    (1 : GeometricCharacters K (coordHopf T)) = 1
  exact map_one _

private theorem multiplicationIso [IsGalois F K] [IsCommMonObj T.val.X]
    (d : PermutedCharacterBasis K I T ρ)
    (hT : IsDiagonalizable (extendedHopf K (coordHopf T)))
    (A : Orbit → AffineAlgebraicGroup F) (f : ∀ o, (A o).val ⟶ T.val)
    (outside : ∀ o i, orbitOf i ≠ o → characterRestriction K (S := A o) (T := T) (f o)
      (d.basis i) = 0)
    (basis : ∀ o, Module.Basis (vertices o) ℤ (CharacterLattice K (A o)))
    (hbasis : ∀ o i, basis o i = characterRestriction K (S := A o) (T := T) (f o)
      (d.basis i.val))
    (hA : ∀ o, IsDiagonalizable (extendedHopf K (coordHopf (A o))))
    (P : Fan (fun o => (A o).val)) (hP : IsLimit P) :
    ∃ e : P.pt ≅ T.val, ∀ (R : TestAlgebra F)
      (x : ((groupPointsFunctor F).obj P.pt).obj R),
      letI : Fintype Orbit := Fintype.ofFinite _
      letI : CommGroup (((groupPointsFunctor F).obj T.val).obj R) := CategoryTheory.Hom.commGroup
      ((groupPointsFunctor F).map e.hom).app R x =
        ∏ o : Orbit, ((groupPointsFunctor F).map (P.proj o ≫ f o)).app R x := by
  classical
  letI := MulAction.compHom I ρ
  letI : Fintype Orbit := Fintype.ofFinite _
  let G := groupPointsFunctor F
  let M : P.pt ⟶ T.val := ∏ o : Orbit, P.proj o ≫ f o
  have mpoint (R : TestAlgebra F) (x : (G.obj P.pt).obj R) :
      letI : CommGroup ((G.obj T.val).obj R) := CategoryTheory.Hom.commGroup
      (G.map M).app R x = ∏ o : Orbit, (G.map (P.proj o ≫ f o)).app R x := by
    letI : CommGroup ((G.obj T.val).obj R) := CategoryTheory.Hom.commGroup
    let g : (P.pt ⟶ T.val) →* (G.obj T.val).obj R :=
      { toFun := fun v => (G.map v).app R x
        map_one' := MonObj.comp_one x
        map_mul' := fun _ _ => MonObj.comp_mul x _ _ }
    exact map_prod g (fun o => P.proj o ≫ f o) Finset.univ
  have bij (R : TestAlgebra F) : Function.Bijective ((G.map M).app R) := by
    letI : CommGroup ((G.obj T.val).obj R) := CategoryTheory.Hom.commGroup
    let C := fun x => fun o : Orbit => weilCoordinate d o.out R x
    let g := fun (x : (o : Orbit) → (G.obj (A o).val).obj R) (o : Orbit) =>
      weilCoordinate d o.out R ((G.map (f o)).app R (x o))
    have family (o : Orbit) (i : I) (hi : orbitOf i = o) :
        Function.Bijective (fun x => weilCoordinate d i R ((G.map (f o)).app R x)) := by
      subst o
      exact factorWeilMap_bijective (f _) d i (basis _) (hbasis _) (hA _) R
    have hg : Function.Bijective g :=
      (Equiv.piCongrRight fun o => Equiv.ofBijective _ (family o o.out (Quotient.out_eq o))).bijective
    have he : C ∘ ((G.map M).app R) =
        g ∘ (fun x => fun o => (G.map (P.proj o)).app R x) := by
      funext x o
      let i := o.out
      have hi : orbitOf i = o := Quotient.out_eq o
      let J := MulAction.stabilizer Gal(K/F) i
      apply Units.map_injective (fixedFieldTensor_injective R J)
      change Units.map (orbitFieldInclusion R J).toMonoidHom
        (weilCoordinate d i R ((G.map M).app R x)) =
        Units.map (orbitFieldInclusion R J).toMonoidHom
          (weilCoordinate d i R ((G.map (f o)).app R ((G.map (P.proj o)).app R x)))
      rw [weilCoordinate_spec, weilCoordinate_spec, mpoint]
      let ev := evaluationHom T R (d.basis i)
      change ev (∏ l : Orbit, (G.map (P.proj l ≫ f l)).app R x) =
        ev ((G.map (f o)).app R ((G.map (P.proj o)).app R x))
      rw [map_prod, Finset.prod_eq_single o]
      · rw [G.map_comp]
        rfl
      · intro l _ hl
        change evaluateCharacter T R ((G.map (P.proj l ≫ f l)).app R x) (d.basis i) = 1
        rw [G.map_comp]
        change evaluateCharacter T R ((G.map (f l)).app R ((G.map (P.proj l)).app R x))
          (d.basis i) = 1
        rw [evaluation_restriction, outside l i (hi.trans_ne hl.symm)]
        exact evaluateCharacter_zero _ _ _
      · simp
    have hcomp : Function.Bijective (C ∘ ((G.map M).app R)) :=
      he ▸ hg.comp (productPoints_bijective P hP R)
    exact ((orbitCoordinates_bijective d hT R).of_comp_iff' ((G.map M).app R)).mp hcomp
  haveI (R : TestAlgebra F) : IsIso ((G.map M).app R) :=
    (MulEquiv.ofBijective ((G.map M).app R).hom (bij R)).toGrpIso.isIso_hom
  haveI : IsIso (G.map M) := NatIso.isIso_of_isIso_app (G.map M)
  obtain ⟨e, he⟩ := affinePointEquivalence (affineProduct P hP (fun o => (A o).property.1))
    T.property.1 (asIso (G.map M))
  refine ⟨e, fun R x => ?_⟩
  change G.map e.hom = G.map M at he
  rw [he]
  exact mpoint R x

end Product

/-- Multiplication identifies the given orbit subtori with the original torus.
Each orbit factor represents the units over the fixed field of its vertex stabilizer. -/
theorem orbitTorusProduct : OrbitTorusProduct.{u} := by
  classical
  intro F K _ _ _ _ _ I _ ρ T hT b hb
  dsimp only
  intro S hS hspan
  letI := MulAction.compHom I ρ
  let O := MulAction.orbitRel.Quotient Gal(K/F) I
  let q : I → O := Quotient.mk (MulAction.orbitRel Gal(K/F) I)
  let A (o : O) := closedSubgroupAlgebraicGroup (G := T) (S o)
  obtain ⟨r, ⟨e⟩⟩ := splitHopfPresentation T hT
  let M := StandardLattice.{u} r
  let c : Additive M ≃ₗ[ℤ] CharacterLattice K T :=
    ((CharacterDescent.monomialCharacterEquiv K).trans (groupLikeIso e)).toAdditive.toIntLinearEquiv
  let l := (latticeCoordinates r).symm.trans c
  letI : Module.Finite ℤ (CharacterLattice K T) := Module.Finite.equiv l
  letI : Module.Free ℤ (CharacterLattice K T) := Module.Free.of_equiv l
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates r).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  have diag : IsDiagonalizable (extendedHopf K (coordHopf T)) :=
    ⟨⟨CommGrpCat.of M, inferInstance⟩, ⟨e⟩⟩
  let d := permutedDualBasis b hb
  have dual (i l : I) : b l (d.basis i) = if i = l then 1 else 0 :=
    dualCharacterBasis_apply b i l
  have charFactor (o : O) := subtorusCharacters (K := K) (S o) hT (hS o)
  have coords (o : O) :
      let j := characterRestriction K (S := A o) (T := T) (S o).inclusion
      (∀ i, q i ≠ o → j (d.basis i) = 0) ∧
        ∃ c' : Module.Basis {i : I // q i = o} ℤ (CharacterLattice K (A o)),
          ∀ i, c' i = j (d.basis i.val) := by
    obtain ⟨_, hfinite, hfree, hsurj, _⟩ := charFactor o
    letI := hfinite
    letI := hfree
    exact restriction_coordinates b _ hsurj {i | q i = o} (hspan o).2
  have outside (o : O) := (coords o).1
  choose basis hBasis using fun o => (coords o).2
  have diagFactor (o : O) : IsDiagonalizable (extendedHopf K (coordHopf (A o))) :=
    (charFactor o).1
  have hcomm : IsCommMonObj T.val.X :=
    CentralFrobeniusDescent.torus_commutative T
      ⟨K, inferInstance, inferInstance, inferInstance, hT⟩
  letI := hcomm
  unfold OrbitTorusDecomposition
  refine ⟨hcomm, d, dual, outside, fun o => ⟨basis o, hBasis o⟩, ?_, ?_⟩
  · intro P hP
    exact multiplicationIso d diag A (fun o => (S o).inclusion) outside basis hBasis
      diagFactor P hP
  · intro i
    exact factorWeilIso (S := A (q i)) (S (q i)).inclusion d i (basis (q i)) (hBasis (q i))
      (diagFactor (q i))

open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)
open Specs.CharacterPairing (pairing powerMorphism)
open CocharacterDynamics (unitPoint unitCoordinates)
open private extendedGroupIso extendedSpecIso extendedSpecIso_hom_fst
  baseChangeProjection_naturality specGroupMap_injective
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private integerHopfHomEquiv from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private integerExponent integerExponent_zpow
  from LinearAlgebraicGroups.RootData.CharacterPairing

private def scalarExtensionComparison (T : AffineAlgebraicGroup F) :
    ScalarExtensionComparison K T := by
  refine ⟨extendedCoordinateIso (K := K) T, ?_⟩
  change (extendedSpecIso K (coordHopf T)).hom.left ≫
    ((baseChange F K).map (coordinateHopfIso T).hom.hom.hom).left ≫
      pullback.fst T.val.X.hom (fieldSpecMap F K) = _
  rw [baseChangeProjection_naturality, ← Category.assoc, extendedSpecIso_hom_fst]

private theorem fieldConjugation_fst (T : GroupScheme F) (σ : Gal(K/F)) :
    fieldConjugation σ T ≫ pullback.fst T.X.hom (fieldSpecMap F K) =
      pullback.fst T.X.hom (fieldSpecMap F K) :=
  pullback.lift_fst _ _ _

private theorem fieldConjugation_snd (T : GroupScheme F) (σ : Gal(K/F)) :
    fieldConjugation σ T ≫ pullback.snd T.X.hom (fieldSpecMap F K) =
      pullback.snd T.X.hom (fieldSpecMap F K) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  pullback.lift_snd _ _ _

private def coefficientRingMap (σ : Gal(K/F)) (A : HopfAlgebraCategory F) :
    K ⊗[F] A →ₐ[F] K ⊗[F] A :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id F A)

private theorem coefficientRingMap_apply (σ : Gal(K/F)) (A : HopfAlgebraCategory F)
    (x : K ⊗[F] A) :
    coefficientRingMap σ A x = (SemilinearAction.scalarExtension (K := K) A).act σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem scalarExtensionComparison_coefficients {T : AffineAlgebraicGroup F}
    (a : ScalarExtensionComparison K T) (σ : Gal(K/F)) :
    a.val.hom.hom.hom.left ≫ fieldConjugation σ T.val =
      Spec.map (CommRingCat.ofHom (coefficientRingMap σ (coordHopf T)).toRingHom) ≫
        a.val.hom.hom.hom.left := by
  let G := T.val.X
  let s := fieldSpecMap F K
  let p := pullback.fst G.hom s
  let r := pullback.snd G.hom s
  let v := a.val.hom.hom.hom.left
  let c := Spec.map (CommRingCat.ofHom (coefficientRingMap σ (coordHopf T)).toRingHom)
  change v ≫ fieldConjugation σ T.val = c ≫ v
  apply pullback.hom_ext
  · change (v ≫ fieldConjugation σ T.val) ≫ p = (c ≫ v) ≫ p
    rw [Category.assoc, fieldConjugation_fst, Category.assoc, show v ≫ p = _ from a.property, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext x
    change (1 : K) ⊗ₜ[F] x = (σ 1 : K) ⊗ₜ[F] x
    rw [map_one]
  · change (v ≫ fieldConjugation σ T.val) ≫ r = (c ≫ v) ≫ r
    have hK : v ≫ r = Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[F] coordHopf T))) :=
      a.val.hom.hom.hom.w
    rw [Category.assoc, fieldConjugation_snd, ← Category.assoc, hK, Category.assoc, hK, ← Spec.map_comp,
      ← Spec.map_comp]
    congr 1

private theorem cocharacterPullback_transport {T : AffineAlgebraicGroup F}
    (a : ScalarExtensionComparison K T) {σ : Gal(K/F)}
    {y y' : Cocharacter ((groupBaseChange F K).obj T.val)}
    (h : CocharacterTransport T.val σ y y') (x : extendedHopf K (coordHopf T)) :
    (cocharacterPullback a y').hom ((SemilinearAction.scalarExtension (K := K)
      (coordHopf T)).act σ x) =
      (MonoidAlgebra.mapRingEquiv IntegerCharacters σ.toRingEquiv)
        ((cocharacterPullback a y).hom x) := by
  let v := a.val.hom.hom.hom.left
  let c := CommRingCat.ofHom (coefficientRingMap σ (coordHopf T)).toRingHom
  let d := CommRingCat.ofHom
    (MonoidAlgebra.mapRingEquiv IntegerCharacters σ.toRingEquiv).toRingHom
  let q (z : Cocharacter ((groupBaseChange F K).obj T.val)) :=
    CommRingCat.ofHom (cocharacterPullback a z).hom.toAlgHom.toRingHom
  have hq (z : Cocharacter ((groupBaseChange F K).obj T.val)) :
      Spec.map (q z) ≫ v = z.hom.hom.left := by
    let P := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
    have hz : specGroupMap (cocharacterPullback a z) = z ≫ a.val.inv :=
      (hopfSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage _
    change P.map (specGroupMap (cocharacterPullback a z)) ≫ P.map a.val.hom = P.map z
    rw [← P.map_comp, hz, Category.assoc, a.val.inv_hom_id, Category.comp_id]
  have hc : v ≫ fieldConjugation σ T.val = Spec.map c ≫ v :=
    scalarExtensionComparison_coefficients a σ
  haveI : IsIso v := (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso a.val.hom
  have hspec : Spec.map (q y') ≫ Spec.map c = Spec.map d ≫ Spec.map (q y) := by
    apply (cancel_mono v).mp
    calc
      (Spec.map (q y') ≫ Spec.map c) ≫ v =
          y'.hom.hom.left ≫ fieldConjugation σ T.val := by
        rw [Category.assoc, ← hc, ← Category.assoc, hq]
      _ = Spec.map d ≫ y.hom.hom.left := h
      _ = (Spec.map d ≫ Spec.map (q y)) ≫ v := by rw [Category.assoc, hq]
  have hr : c ≫ q y' = q y ≫ d := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact hspec
  have hx := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hr) x
  change (cocharacterPullback a y').hom (coefficientRingMap σ (coordHopf T) x) = _ at hx
  rwa [coefficientRingMap_apply] at hx

private abbrev multiplicativeGroup (F : Type u) [Field F] := specGroup (groupAlgebra F IntegerCharacters)

private def multiplicativeBaseChangeIso : multiplicativeGroup K ≅
    (groupBaseChange F K).obj (multiplicativeGroup F) :=
  let e : extendedHopf K (groupAlgebra F IntegerCharacters) ≅ groupAlgebra K IntegerCharacters :=
    CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange F K IntegerCharacters)
  (hopfSpec (CommRingCat.of K)).mapIso e.op ≪≫ extendedGroupIso K (groupAlgebra F IntegerCharacters)

private abbrev extendLaurent : MonoidAlgebra F IntegerCharacters →ₐ[F]
    MonoidAlgebra K IntegerCharacters :=
  MonoidAlgebra.mapAlgHom IntegerCharacters (Algebra.ofId F K)

private theorem multiplicativeBaseChangeIso_fst :
    (multiplicativeBaseChangeIso (F := F) (K := K)).hom.hom.hom.left ≫
      pullback.fst (multiplicativeGroup F).X.hom (fieldSpecMap F K) =
      Spec.map (CommRingCat.ofHom (extendLaurent (F := F) (K := K)).toRingHom) := by
  let B := groupAlgebra F IntegerCharacters
  let e := CharacterDescent.groupAlgebraBaseChange F K IntegerCharacters
  change (Spec.map (CommRingCat.ofHom e.toAlgEquiv.toAlgHom.toRingHom) ≫
    (extendedSpecIso K B).hom.left) ≫ pullback.fst (multiplicativeGroup F).X.hom (fieldSpecMap F K) = _
  rw [Category.assoc, extendedSpecIso_hom_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change MonoidAlgebra.scalarTensorEquiv F K ((1 : K) ⊗ₜ[F] a) = extendLaurent a
  rw [MonoidAlgebra.scalarTensorEquiv_tmul, one_smul]

private theorem multiplicativeBaseChangeIso_units (R : TestAlgebra K) (t : Rˣ) :
    baseChangePoint F K (multiplicativeGroup F).X R
      (unitPoint R t ≫ (multiplicativeBaseChangeIso (F := F) (K := K)).hom.hom.hom) =
      unitPoint ((restrictTestAlgebra F K).obj R) t := by
  apply Over.OverMorphism.ext
  change (Spec.map (CommRingCat.ofHom (unitCoordinates R t).toRingHom) ≫ _) ≫ _ =
    Spec.map (CommRingCat.ofHom (unitCoordinates ((restrictTestAlgebra F K).obj R) t).toRingHom)
  rw [Category.assoc, multiplicativeBaseChangeIso_fst, ← Spec.map_comp]
  congr 1
  letI : Algebra F R := ((algebraMap K R).comp (algebraMap F K)).toAlgebra
  letI : IsScalarTower F K R := IsScalarTower.of_algebraMap_eq' rfl
  let f := ((unitCoordinates R t).restrictScalars F).comp (extendLaurent (F := F) (K := K))
  apply CommRingCat.hom_ext
  change f.toRingHom = (unitCoordinates ((restrictTestAlgebra F K).obj R) t).toRingHom
  congr 1
  apply MonoidAlgebra.algHom_ext
  · intro m
    change (unitCoordinates R t) (MonoidAlgebra.mapAlgHom IntegerCharacters (Algebra.ofId F K)
      (MonoidAlgebra.single m 1)) =
      (unitCoordinates ((restrictTestAlgebra F K).obj R) t) (MonoidAlgebra.of F _ m)
    rw [MonoidAlgebra.mapAlgHom_single, map_one]
    change (unitCoordinates R t) (MonoidAlgebra.of K _ m) = _
    simp only [unitCoordinates, MonoidAlgebra.lift_of]
  · ext

private theorem multiplicativeBaseChangeIso_coefficients (σ : Gal(K/F)) :
    (multiplicativeBaseChangeIso (F := F) (K := K)).hom.hom.hom.left ≫
        fieldConjugation σ (multiplicativeGroup F) =
      multiplicativeFieldConjugation σ ≫
        (multiplicativeBaseChangeIso (F := F) (K := K)).hom.hom.hom.left := by
  let M := multiplicativeGroup F
  let p := pullback.fst M.X.hom (fieldSpecMap F K)
  let q := pullback.snd M.X.hom (fieldSpecMap F K)
  let e := multiplicativeBaseChangeIso (F := F) (K := K)
  let v := e.hom.hom.hom.left
  let d := MonoidAlgebra.mapRingEquiv IntegerCharacters σ.toRingEquiv
  let dF : MonoidAlgebra K IntegerCharacters →ₐ[F] MonoidAlgebra K IntegerCharacters :=
    { toRingHom := d.toRingHom
      commutes' := fun z => by
        change d (MonoidAlgebra.single 1 (algebraMap F K z)) =
          MonoidAlgebra.single 1 (algebraMap F K z)
        dsimp only [d]
        rw [MonoidAlgebra.mapRingEquiv_single]
        exact congrArg (MonoidAlgebra.single (1 : IntegerCharacters)) (σ.commutes z) }
  change v ≫ fieldConjugation σ M = Spec.map (CommRingCat.ofHom d.toRingHom) ≫ v
  apply pullback.hom_ext
  · change (v ≫ fieldConjugation σ M) ≫ p =
      (Spec.map (CommRingCat.ofHom d.toRingHom) ≫ v) ≫ p
    rw [Category.assoc, fieldConjugation_fst, Category.assoc, show v ≫ p = _ from
      multiplicativeBaseChangeIso_fst, ← Spec.map_comp]
    congr 1
    have h : dF.comp (extendLaurent (F := F) (K := K)) = extendLaurent := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        change d (MonoidAlgebra.mapAlgHom IntegerCharacters (Algebra.ofId F K)
          (MonoidAlgebra.single m 1)) =
          MonoidAlgebra.mapAlgHom IntegerCharacters (Algebra.ofId F K) (MonoidAlgebra.single m 1)
        rw [MonoidAlgebra.mapAlgHom_single, map_one]
        change (MonoidAlgebra.mapRingEquiv IntegerCharacters σ.toRingEquiv)
          (MonoidAlgebra.single m 1) = MonoidAlgebra.single m 1
        rw [MonoidAlgebra.mapRingEquiv_single, map_one]
      · ext
    exact congrArg (fun f : MonoidAlgebra F IntegerCharacters →ₐ[F]
      MonoidAlgebra K IntegerCharacters => CommRingCat.ofHom f.toRingHom) h.symm
  · change (v ≫ fieldConjugation σ M) ≫ q =
      (Spec.map (CommRingCat.ofHom d.toRingHom) ≫ v) ≫ q
    have hK : v ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K (MonoidAlgebra K IntegerCharacters))) :=
      e.hom.hom.hom.w
    rw [Category.assoc, fieldConjugation_snd, ← Category.assoc, hK, Category.assoc, hK,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change MonoidAlgebra.single (1 : IntegerCharacters) (σ a) =
      (MonoidAlgebra.mapRingEquiv IntegerCharacters σ.toRingEquiv) (MonoidAlgebra.single 1 a)
    rw [MonoidAlgebra.mapRingEquiv_single]
    rfl

private theorem cocharacterTransport_equiv (T : GroupScheme F) (σ : Gal(K/F))
    (y y' : Cocharacter ((groupBaseChange F K).obj T)) :
    CocharacterTransport T σ y y' ↔
      let e := multiplicativeBaseChangeIso (F := F) (K := K)
      fieldConjugation σ (multiplicativeGroup F) ≫ (e.inv ≫ y).hom.hom.left =
        (e.inv ≫ y').hom.hom.left ≫ fieldConjugation σ T := by
  let M := multiplicativeGroup F
  let e := multiplicativeBaseChangeIso (F := F) (K := K)
  let P := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  let v := P.map e.hom
  let w := P.map e.inv
  haveI : IsIso v := P.map_isIso e.hom
  have hvw : v ≫ w = 𝟙 _ := (P.map_comp _ _).symm.trans (by rw [e.hom_inv_id, P.map_id])
  have hc : v ≫ fieldConjugation σ M = multiplicativeFieldConjugation σ ≫ v :=
    multiplicativeBaseChangeIso_coefficients σ
  change y'.hom.hom.left ≫ fieldConjugation σ T = multiplicativeFieldConjugation σ ≫ y.hom.hom.left ↔
    fieldConjugation σ M ≫ (w ≫ y.hom.hom.left) = (w ≫ y'.hom.hom.left) ≫ fieldConjugation σ T
  rw [← cancel_epi v, ← Category.assoc v, hc, Category.assoc (multiplicativeFieldConjugation σ),
    ← Category.assoc v w, hvw, Category.id_comp, ← Category.assoc v, ← Category.assoc v w,
    hvw, Category.id_comp, eq_comm]

private theorem multiplicativeBaseChangeIso_eq :
    multiplicativeBaseChangeIso (F := F) (K := K) = multiplicativeBaseChange F K := by
  apply Iso.ext
  apply cocharacter_ext_units
  intro R t
  apply (baseChangePoints F K _ R).1
  exact (multiplicativeBaseChangeIso_units R t).trans (multiplicativeBaseChange_unit K R t).symm

private theorem cocharacterTransport_twist (T : GroupScheme F) (σ : Gal(K/F))
    (y z : Cocharacter ((groupBaseChange F K).obj T)) :
    CocharacterTransport T σ y z ↔ z = twistCocharacter σ⁻¹ y := by
  let e := multiplicativeBaseChangeIso (F := F) (K := K)
  let f := e.inv ≫ y
  let f' := twistMorphism σ⁻¹ f
  let y' := e.hom ≫ f'
  let P := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  let M := multiplicativeGroup F
  have h (G : GroupScheme F) : (twistedBaseChange σ⁻¹ G).inv.hom.hom.left =
      fieldConjugation σ G := by
    rw [twistedBaseChange_inv, inv_inv]
    rfl
  have hh : fieldConjugation σ M ≫ f.hom.hom.left =
      f'.hom.hom.left ≫ fieldConjugation σ T := by
    change fieldConjugation σ M ≫ f.hom.hom.left =
      ((twistedBaseChange σ⁻¹ M).inv.hom.hom.left ≫ f.hom.hom.left ≫
      (twistedBaseChange σ⁻¹ T).hom.hom.hom.left) ≫ fieldConjugation σ T
    rw [h M, Category.assoc, Category.assoc, ← h T]
    have hId := P.congr_map (twistedBaseChange σ⁻¹ T).hom_inv_id
    change (twistedBaseChange σ⁻¹ T).hom.hom.hom.left ≫
      (twistedBaseChange σ⁻¹ T).inv.hom.hom.left = 𝟙 _ at hId
    rw [hId]
    change fieldConjugation σ M ≫ f.hom.hom.left = fieldConjugation σ M ≫ f.hom.hom.left ≫
      𝟙 ((groupBaseChange F K).obj T).X.left
    rw [Category.comp_id]
  have hy' : CocharacterTransport T σ y y' := (cocharacterTransport_equiv T σ y y').mpr (by
    change fieldConjugation σ M ≫ f.hom.hom.left = (e.inv ≫ e.hom ≫ f').hom.hom.left ≫ _
    rw [e.inv_hom_id_assoc]
    exact hh)
  have heq : y' = twistCocharacter σ⁻¹ y := by
    change (multiplicativeBaseChangeIso (F := F) (K := K)).hom ≫ twistMorphism σ⁻¹
      ((multiplicativeBaseChangeIso (F := F) (K := K)).inv ≫ y) = _
    rw [multiplicativeBaseChangeIso_eq]
    rfl
  rw [← heq]
  refine ⟨fun hz => ?_, fun hz => hz ▸ hy'⟩
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  haveI : IsIso (fieldConjugation σ T) := by
    rw [← h T]
    exact P.map_isIso (twistedBaseChange σ⁻¹ T).inv
  exact (cancel_mono (fieldConjugation σ T)).mp (hz.trans hy'.symm)

private theorem coefficient_action (T : GroupScheme F)
    [IsCommMonObj ((groupBaseChange F K).obj T).X] :
    ∃ A : DistribMulAction Gal(K/F) (Additive (Cocharacter ((groupBaseChange F K).obj T))),
      ∀ (σ : Gal(K/F)) (y y' : Cocharacter ((groupBaseChange F K).obj T)),
        A.smul σ (Additive.ofMul y) = Additive.ofMul y' ↔ CocharacterTransport T σ y y' := by
  refine ⟨galoisCocharacterAction, fun σ y y' => ?_⟩
  change Additive.ofMul (twistCocharacter σ⁻¹ y) = Additive.ofMul y' ↔ _
  rw [Additive.ofMul.injective.eq_iff, cocharacterTransport_twist, eq_comm]


/-- The normalized Laurent comparison identifies the semilinear square with
Galois transport of the actual group-scheme morphisms. -/
theorem cocharacterCoefficientAction : CocharacterCoefficientAction.{u} := by
  intro F K _ _ _
  refine ⟨multiplicativeBaseChangeIso, multiplicativeBaseChangeIso_units,
    cocharacterTransport_equiv, coefficient_action⟩

private theorem characterOfCoordinate_unique (A : HopfAlgebraCategory K)
    (f g : groupAlgebra K IntegerCharacters ⟶ A)
    (h : f.hom (MonoidAlgebra.of K IntegerCharacters integerGenerator) =
      g.hom (MonoidAlgebra.of K IntegerCharacters integerGenerator)) : f = g := by
  apply (integerHopfHomEquiv A).symm.injective
  exact GroupLike.val_injective h

private theorem cocharacterPullback_exponent {T : AffineAlgebraicGroup F}
    (a : ScalarExtensionComparison K T) (y : Cocharacter ((groupBaseChange F K).obj T.val))
    (χ : groupAlgebra K IntegerCharacters ⟶ extendedHopf K (coordHopf T)) :
    (cocharacterPullback a y).hom (χ.hom (MonoidAlgebra.of K IntegerCharacters integerGenerator)) =
      MonoidAlgebra.of K IntegerCharacters
        (integerGenerator ^ pairing _ (a.val.inv ≫ specGroupMap χ) y) := by
  let h := cocharacterPullback a y
  let n := pairing _ (a.val.inv ≫ specGroupMap χ) y
  have hh : specGroupMap h = y ≫ a.val.inv :=
    (hopfSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage _
  have hc : y ≫ (a.val.inv ≫ specGroupMap χ) = powerMorphism n :=
    (RootData.CharacterPairing.characterPairingComposition _ _ _).1 n |>.mpr rfl
  have hp := (show powerMorphism n = specGroupMap (Specs.DiagonalizableGroups.groupAlgebraMap K
      ((zpowersHom IntegerCharacters (integerGenerator ^ n)).comp MulEquiv.ulift.toMonoidHom)) from rfl)
  rw [hp, ← Category.assoc, ← hh, ← specGroupMap_comp] at hc
  have he := DFunLike.congr_fun (congrArg CommHopfAlgCat.Hom.hom (specGroupMap_injective hc))
    (MonoidAlgebra.of K IntegerCharacters integerGenerator)
  change h.hom (χ.hom (MonoidAlgebra.single integerGenerator 1)) =
    MonoidAlgebra.mapDomainBialgHom K
      ((zpowersHom IntegerCharacters (integerGenerator ^ n)).comp MulEquiv.ulift.toMonoidHom)
      (MonoidAlgebra.single integerGenerator 1) at he
  rw [MonoidAlgebra.mapDomainBialgHom_single] at he
  change h.hom (χ.hom (MonoidAlgebra.single integerGenerator 1)) =
    MonoidAlgebra.single ((integerGenerator ^ n) ^ (1 : ℤ)) 1 at he
  rw [zpow_one] at he
  exact he

/-- Integral duality on the actual base change, with its pullback and coefficient actions. -/
theorem splitCocharacterDuality : SplitCocharacterDuality.{u} := by
  intro F K _ _ _
  classical
  let a (T : AffineAlgebraicGroup F) := scalarExtensionComparison (K := K) T
  obtain ⟨char, hnaturality, hcoordinate⟩ := CharacterDescent.characterInterpretation (k := K)
  have hp (T : AffineAlgebraicGroup F) (hT : IsSplitTorus ((groupBaseChange F K).obj T.val)) :
      ∃ hcomm : IsCommMonObj ((groupBaseChange F K).obj T.val).X,
      letI := hcomm
      ∃ p : Additive (Character ((groupBaseChange F K).obj T.val)) →ₗ[ℤ]
          Additive (Cocharacter ((groupBaseChange F K).obj T.val)) →ₗ[ℤ] ℤ,
        p.IsPerfPair ∧ ∀ χ y, p (Additive.ofMul χ) (Additive.ofMul y) = pairing _ χ y := by
    obtain ⟨h, _, _, _, _, hp⟩ := RootData.CharacterPairing.perfectCharacterPairing _ hT
    exact ⟨h, hp⟩
  choose hcomm hp using hp
  have hp' (T : AffineAlgebraicGroup F) (hT : IsSplitTorus ((groupBaseChange F K).obj T.val)) :
      letI := hcomm T hT
      ∃ p : Additive (Character ((groupBaseChange F K).obj T.val)) →ₗ[ℤ]
          Additive (Cocharacter ((groupBaseChange F K).obj T.val)) →ₗ[ℤ] ℤ,
        p.IsPerfPair ∧ ∀ χ y, p (Additive.ofMul χ) (Additive.ofMul y) = pairing _ χ y := hp T hT
  choose p hperf hpair using hp'
  let χ (T : AffineAlgebraicGroup F) : CharacterLattice K T ≃ₗ[ℤ]
      Additive (Character ((groupBaseChange F K).obj T.val)) :=
    ((char _).trans (charactersOfIso (a T).val)).toAdditive.toIntLinearEquiv
  let e (T : AffineAlgebraicGroup F) (hT : IsSplitTorus ((groupBaseChange F K).obj T.val)) :
      letI := hcomm T hT
      Additive (Cocharacter ((groupBaseChange F K).obj T.val)) ≃ₗ[ℤ] CocharacterLattice K T :=
    letI := hcomm T hT
    letI := hperf T hT
    (p T hT).flip.toPerfPair.trans (χ T).dualMap
  have eval (T : AffineAlgebraicGroup F) (hT : IsSplitTorus ((groupBaseChange F K).obj T.val))
      (y : Cocharacter ((groupBaseChange F K).obj T.val)) (x : CharacterLattice K T) :
      e T hT (Additive.ofMul y) x = pairing _ ((a T).val.inv ≫ char _ x.toMul) y := by
    change (p T hT) (Additive.ofMul ((a T).val.inv ≫ char _ x.toMul)) (Additive.ofMul y) = _
    exact hpair T hT _ y
  have eval' (T : AffineAlgebraicGroup F) (hT : IsSplitTorus ((groupBaseChange F K).obj T.val))
      (y : Cocharacter ((groupBaseChange F K).obj T.val)) (x : CharacterLattice K T)
      (f : groupAlgebra K IntegerCharacters ⟶ extendedHopf K (coordHopf T))
      (hf : f.hom (MonoidAlgebra.of K IntegerCharacters integerGenerator) = x.toMul.val) :
      e T hT (Additive.ofMul y) x = pairing _ ((a T).val.inv ≫ specGroupMap f) y := by
    obtain ⟨g, hg, hchar⟩ := hcoordinate _ x.toMul
    have heq : g = f := characterOfCoordinate_unique _ g f (hg.trans hf.symm)
    rw [eval, hchar, heq]
  refine ⟨a, hcomm, e, eval', ?_, ?_⟩
  · intro S T hS hT f y
    ext x
    change e T hT (Additive.ofMul (y ≫ (groupBaseChange F K).map f)) x =
      e S hS (Additive.ofMul y) (characterRestriction K (S := S) (T := T) f x)
    rw [eval, eval]
    let g := extendedHopfMap K (coordinateHopfMap (G := S) (H := T) f)
    have hn := extendedCoordinateIso_natural (K := K) (G := S) (H := T) f
    have h : (groupBaseChange F K).map f ≫ (a T).val.inv =
        (a S).val.inv ≫ specGroupMap g := by
      apply (Iso.cancel_iso_hom_right _ _ (a T).val).mp
      have hn' : specGroupMap g ≫ (a T).val.hom =
          (a S).val.hom ≫ (groupBaseChange F K).map f := hn
      simpa only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id] using
        congrArg ((a S).val.inv ≫ ·) hn'.symm
    have hc := hnaturality _ _ g x.toMul
    change char _ (characterRestriction K (S := S) (T := T) f x).toMul =
      specGroupMap g ≫ char _ x.toMul at hc
    rw [hc]
    unfold pairing Specs.CharacterDescent.compositionPairing
    congr 1
    calc
      _ = y ≫ ((groupBaseChange F K).map f ≫ (a T).val.inv) ≫ char _ x.toMul := by
        simp only [Category.assoc]
      _ = _ := by
        rw [h]
        simp only [Category.assoc]
  · intro T hT σ y y' hy x x' hx
    obtain ⟨f, hf, _⟩ := hcoordinate _ x.toMul
    obtain ⟨f', hf', _⟩ := hcoordinate _ x'.toMul
    rw [eval' T hT y' x' f' hf', eval' T hT y x f hf]
    have h := cocharacterPullback_transport (a T) hy x.toMul.val
    rw [hx, ← hf, ← hf', cocharacterPullback_exponent, cocharacterPullback_exponent] at h
    change MonoidAlgebra.single _ (1 : K) =
      (MonoidAlgebra.mapRingEquiv IntegerCharacters σ.toRingEquiv) (MonoidAlgebra.single _ 1) at h
    rw [MonoidAlgebra.mapRingEquiv_single, map_one σ.toRingEquiv] at h
    have eq := MonoidAlgebra.of_injective (R := K) (M := IntegerCharacters) h
    simpa only [integerExponent_zpow] using congrArg integerExponent eq

private theorem linearRange_transport {X X' Y Y' : Type u}
    [AddCommGroup X] [AddCommGroup X'] [AddCommGroup Y] [AddCommGroup Y']
    {p : X →ₗ[ℤ] Y} {j : X' →ₗ[ℤ] Y'}
    (c : X ≃ₗ[ℤ] X') (d : Y ≃ₗ[ℤ] Y')
    (h : ∀ x, d (p x) = j (c x)) (hp : Function.Injective p) :
    Function.Injective j ∧ LinearMap.range j = (LinearMap.range p).map d.toLinearMap := by
  constructor
  · intro x y heq
    obtain ⟨s, rfl⟩ := c.surjective x
    obtain ⟨t, rfl⟩ := c.surjective y
    exact congrArg c (hp (d.injective ((h s).trans (heq.trans (h t).symm))))
  · ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := c.surjective x
      exact ⟨p y, ⟨y, rfl⟩, h y⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨c y, (h y).symm⟩

/-- The same decomposition on scheme cocharacters, with the semilinear
action and the maps induced by the given closed immersions. -/
theorem orbitTorusProductOnCocharacters : OrbitTorusProductOnCocharacters.{u} := by
  intro F K _ _ _ _ _ I _ ρ T hT
  obtain ⟨a, hcomm, e, hpair, hnaturality, htransport⟩ :=
    splitCocharacterDuality (F := F) (K := K)
  letI := hcomm T hT
  refine ⟨hcomm T hT, ?_⟩
  dsimp only
  intro b hb S hS
  let A := fun o => closedSubgroupAlgebraicGroup (G := T) (S o)
  have hsplit (o : _) := splitClosedSubtorus T (S o) hT (hS o)
  refine ⟨fun o => hcomm (A o) (hsplit o), ?_⟩
  intro hspan
  refine ⟨a T, e T hT, fun i x χ hx => hpair T hT (b i).toMul x χ hx, ?_⟩
  refine orbitTorusProduct (K := K) ρ T hT (b.map (e T hT)) ?_ S hS ?_
  · intro σ i χ ψ h
    exact htransport T hT σ (b i).toMul (b (ρ σ i)).toMul (hb σ i) χ ψ h
  · intro o
    letI : IsCommMonObj ((groupBaseChange F K).obj (S o).group).X :=
      hcomm (A o) (hsplit o)
    let f := (S o).inclusion
    let p := cocharacterPushforward (K := K) f
    let j := (characterRestriction K (S := A o) (T := T) f).dualMap
    let c : Additive (Cocharacter ((groupBaseChange F K).obj (S o).group)) ≃ₗ[ℤ]
        CocharacterLattice K (A o) := e (A o) (hsplit o)
    have comm (y : Additive (Cocharacter ((groupBaseChange F K).obj (S o).group))) :
        e T hT (p y) = j (c y) :=
      hnaturality (A o) T (hsplit o) hT f y.toMul
    obtain ⟨hinj, hrange⟩ := hspan o
    change Function.Injective p at hinj
    change LinearMap.range p = _ at hrange
    change Function.Injective j ∧ LinearMap.range j = _
    obtain ⟨hj, hr⟩ := linearRange_transport c (e T hT) comm hinj
    refine ⟨hj, ?_⟩
    rw [hr, hrange, Submodule.map_span, Set.image_image]
    rfl

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitTorusProduct
