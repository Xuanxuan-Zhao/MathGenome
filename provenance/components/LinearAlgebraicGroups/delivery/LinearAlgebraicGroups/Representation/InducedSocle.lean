import Specs.LinearAlgebraicGroups.Representation.InducedSocle
import LinearAlgebraicGroups.Representation.InductionAdjunction
import LinearAlgebraicGroups.Representation.PrimitiveLine
import LinearAlgebraicGroups.Flag.OpenCell
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Coalgebra Opposite WithConv
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.Representation.InducedSocle

open _root_.LinearAlgebraicGroups.Specs
open Specs.InducedSocle
open Specs.FlagLineBundle
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (subgroupRoots positiveRoots)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (characterValue pairing)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.RootWeightAction
open Specs.PrimitiveLine (IsStable orbitCoefficient)
open Specs.CyclicHighestWeight (orbitSpan)
open Specs.OrderedRootProducts (RootSubgroupFamily Enumerates rootProduct)
open RationalRepresentations (tensorCoordinate evaluate)

open private fromCoaction toCoaction evaluation orbit_le_iff orbit_properties
  orbit_stable stable_iff inclusion_equivariant act_eq_scalar_iff exists_primitive
  from LinearAlgebraicGroups.Representation.PrimitiveLine
open private affineTensor subgroupAffine dense_of_self_baseChange orbitSpan_of_dense
  positiveCone dominanceLE_iff positiveRoot_mem_cone rootPoint_surjective
  act_mul act_one dominance_of_reflections
  from LinearAlgebraicGroups.Representation.CyclicHighestWeight
open private tensorCoordinate_tmul
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private splitPresentation from LinearAlgebraicGroups.RootData.CharacterPairing
open private torusPoint_weights charactersOfIso characterValue_eq_eval
  from LinearAlgebraicGroups.Representation.RootWeightAction
open private rationalWeylLabel rationalWeylLabel_surjective
  from LinearAlgebraicGroups.RootData.BorelPositivity
open private longest_flips_sign radicalProductFor existsEnumeration rootOfNeg
  from LinearAlgebraicGroups.Flag.OpenCell

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {G : AffineAlgebraicGroup k} {A D : HopfAlgebraCategory k}
variable {q : A ⟶ D} {c : GroupLike k D}

private abbrev pointIso {H : GroupScheme k} (e : specGroup A ≅ H) :=
  hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e

private theorem inducedPoint {H L : GroupScheme k}
    (e : specGroup A ≅ H) (d : specGroup D ≅ L) (j : L ⟶ H)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ j)
    (R : TestAlgebra k) (a : WithConv (D →ₐ[k] R)) :
    (pointIso e).hom.app R (toConv (a.ofConv.comp q.hom.toAlgHom)) =
      (pointIso d).hom.app R a ≫ j.hom.hom := by
  let x : Points (specGroup D).X R := (hopfSpecPointIso D).hom.app R a
  let y : Points (specGroup A).X R :=
    (hopfSpecPointIso A).hom.app R (toConv (a.ofConv.comp q.hom.toAlgHom))
  have h : y = x ≫ (specGroupMap q).hom.hom := by
    apply Over.OverMorphism.ext
    exact Spec.map_comp (CommRingCat.ofHom q.hom.toAlgHom.toRingHom)
      (CommRingCat.ofHom a.ofConv.toRingHom)
  change y ≫ e.hom.hom.hom = (x ≫ d.hom.hom.hom) ≫ j.hom.hom
  have hq' : (specGroupMap q).hom.hom ≫ e.hom.hom.hom = d.hom.hom.hom ≫ j.hom.hom :=
    (Grp.forget _).congr_map hq
  rw [h, Category.assoc, hq', ← Category.assoc]

private theorem evalCovariant (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R))
    (a : D →ₐ[k] R) (f : covariantFunctions q c) :
    (g * toConv (a.comp q.hom.toAlgHom)) (f : A) =
      g (f : A) * a ((c⁻¹ : GroupLike k D) : D) := by
  have hf := f.property
  change q.hom.toAlgHom.toLinearMap.lTensor A (comul (R := k) (f : A)) =
    (f : A) ⊗ₜ[k] ((c⁻¹ : GroupLike k D) : D) at hf
  let l := Algebra.TensorProduct.lift g.ofConv a (fun _ _ ↦ Commute.all _ _)
  have he (x : A ⊗[k] A) : l (q.hom.toAlgHom.toLinearMap.lTensor A x) =
      Algebra.TensorProduct.lift g.ofConv (a.comp q.hom.toAlgHom)
        (fun _ _ ↦ Commute.all _ _) x := by
    refine TensorProduct.inductionOn x (fun x y => ?_) (fun x y hx hy => by simp [hx, hy])
    simp [l, Algebra.TensorProduct.lift_tmul]
  have hs := congrArg l hf
  rw [he] at hs
  simpa [l, Algebra.TensorProduct.lift_tmul, AlgHom.convMul_apply] using hs

private def evaluationLinear (b : Module.Basis I k (covariantFunctions q c))
    (R : TestAlgebra k) : (I → R) →ₗ[R] R :=
  ∑ i, algebraMap k R (counit (R := k) (b i : A)) • LinearMap.proj i

omit [DecidableEq I] in
private theorem evaluationLinear_extend (b : Module.Basis I k (covariantFunctions q c))
    (R : TestAlgebra k) (v : I → k) :
    evaluationLinear b R (extendVector R v) =
      algebraMap k R (counit (R := k) (b.equivFun.symm v : A)) := by
  obtain ⟨f, rfl⟩ := b.equivFun.surjective v
  rw [LinearEquiv.symm_apply_apply]
  let ε : covariantFunctions q c →ₗ[k] k :=
    (counit (R := k) (A := A)).comp (covariantFunctions q c).subtype
  have he := congrArg (fun w => algebraMap k R (ε w)) (b.sum_repr f)
  simp only [map_sum, map_smul, smul_eq_mul, map_mul, ε, LinearMap.comp_apply,
    Submodule.subtype_apply] at he
  simpa only [evaluationLinear, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, extendVector, Module.Basis.equivFun_apply, smul_eq_mul, mul_comm]
    using he

omit [DecidableEq I] in
private theorem evaluationLinear_tensor (b : Module.Basis I k (covariantFunctions q c))
    (R : TestAlgebra k) (h : WithConv (A →ₐ[k] R))
    (t : covariantFunctions q c ⊗[k] A) :
    evaluationLinear b R (fun i ↦ tensorCoordinate b i (h.ofConv.toLinearMap.lTensor _ t)) =
      Algebra.TensorProduct.lift (1 : WithConv (A →ₐ[k] R)).ofConv h.ofConv
        (fun _ _ ↦ Commute.all _ _) (((covariantFunctions q c).subtype.rTensor A) t) := by
  refine TensorProduct.inductionOn t (fun f a ↦ ?_) (fun x y hx hy ↦ ?_)
  · have heq : (fun i ↦ tensorCoordinate b i
        (h.ofConv.toLinearMap.lTensor _ (f ⊗ₜ[k] a))) =
          h a • extendVector R (b.equivFun f) := by
      funext i
      rw [LinearMap.lTensor_tmul, tensorCoordinate_tmul]
      simp [extendVector, Module.Basis.equivFun_apply, Module.Basis.coord_apply,
        Algebra.smul_def, mul_comm]
    rw [heq, map_smul, evaluationLinear_extend, LinearEquiv.symm_apply_apply]
    simp [Algebra.TensorProduct.lift_tmul, mul_comm]
  · simp only [map_add]
    change evaluationLinear b R ((fun i ↦ tensorCoordinate b i (h.ofConv.toLinearMap.lTensor _ x)) +
      (fun i ↦ tensorCoordinate b i (h.ofConv.toLinearMap.lTensor _ y))) = _
    rw [map_add, hx, hy]

private abbrev IsLeftTranslation (ρ : RightComodule k A (covariantFunctions q c)) :=
  ∀ (R : TestAlgebra k) (h g : WithConv (A →ₐ[k] R)) (f : covariantFunctions q c),
    letI := convolutionGroup A R
    (Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ Commute.all _ _))
      (((covariantFunctions q c).subtype.rTensor A) (ρ.coaction f)) = (h⁻¹ * g) (f : A)

private theorem evaluationLinear_act (b : Module.Basis I k (covariantFunctions q c))
    (ρ : RightComodule k A (covariantFunctions q c))
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (htrans : IsLeftTranslation ρ)
    (R : TestAlgebra k) (h : WithConv (A →ₐ[k] R)) (v : I → k) :
    letI := convolutionGroup A R
    evaluationLinear b R (act (fromCoaction e b ρ) R (e.hom.app R h) (extendVector R v)) =
      h⁻¹ (b.equivFun.symm v : A) := by
  letI := convolutionGroup A R
  obtain ⟨f, rfl⟩ := b.equivFun.surjective v
  rw [LinearEquiv.symm_apply_apply]
  have heq : act (fromCoaction e b ρ) R (e.hom.app R h) (extendVector R (b.equivFun f)) =
      fun i ↦ tensorCoordinate b i (h.ofConv.toLinearMap.lTensor _ (ρ.coaction f)) := by
    funext i
    exact evaluation e b ρ R h.ofConv f i
  rw [heq, evaluationLinear_tensor]
  exact (htrans R h 1 f).trans (by rw [mul_one])

private abbrev TranslatedEvaluation (e : specGroup A ≅ G.val)
    (b : Module.Basis I k (covariantFunctions q c)) (σ : Representation G.val I) :=
  ∀ (R : TestAlgebra k) (h : WithConv (A →ₐ[k] R)) (v : I → k),
    letI := convolutionGroup A R
    evaluationLinear b R (act σ R ((pointIso e).hom.app R h) (extendVector R v)) =
      h⁻¹ (b.equivFun.symm v : A)

private theorem evaluationLinear_subgroup {P : OppositeBorelPair G}
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (b : Module.Basis I k (covariantFunctions q c))
    (σ : Representation G.val I) (heval : TranslatedEvaluation e b σ)
    (R : TestAlgebra k) (g : GroupPoints P.negative.group R) (v : I → k) :
    let a : WithConv (D →ₐ[k] R) := (pointIso d).inv.app R g
    evaluationLinear b R
      (act σ R (g ≫ P.negative.inclusion.hom.hom)
        (extendVector R v)) = a (c : D) * evaluationLinear b R (extendVector R v) := by
  letI := convolutionGroup A R
  letI := convolutionGroup D R
  let a : WithConv (D →ₐ[k] R) := (pointIso d).inv.app R g
  let qa : WithConv (A →ₐ[k] R) := toConv (a.ofConv.comp q.hom.toAlgHom)
  have ha : (pointIso d).hom.app R a = g := (pointIso d).app R |>.inv_hom_id_apply g
  change _ = a (c : D) * _
  have hpoint := inducedPoint e d P.negative.inclusion hq R a
  rw [ha] at hpoint
  rw [← hpoint, heval, evaluationLinear_extend]
  have hinv : qa⁻¹ = toConv ((a⁻¹).ofConv.comp q.hom.toAlgHom) := by
    apply ((forget GrpCat).mapIso ((pointIso e).app R)).toEquiv.injective
    change (pointIso e).hom.app R (qa⁻¹) =
      (pointIso e).hom.app R (toConv ((a⁻¹).ofConv.comp q.hom.toAlgHom))
    have hqa := inducedPoint e d P.negative.inclusion hq R a
    rw [map_inv, show (pointIso e).hom.app R qa = _ from hqa,
      inducedPoint e d P.negative.inclusion hq, map_inv]
    exact (map_inv (((groupPointsFunctor k).map P.negative.inclusion).app R).hom
      ((pointIso d).hom.app R a)).symm
  change qa⁻¹ (b.equivFun.symm v : A) = _
  rw [hinv, ← one_mul (toConv ((a⁻¹).ofConv.comp q.hom.toAlgHom) :
    WithConv (A →ₐ[k] R)), evalCovariant]
  have hcancel : a⁻¹ ((c⁻¹ : GroupLike k D) : D) = a (c : D) := by
    change a.ofConv (HopfAlgebra.antipode k (HopfAlgebra.antipode k (c : D))) = _
    rw [c.2.antipode_antipode]
  rw [hcancel, AlgHom.convOne_apply, mul_comm]

private theorem denseCell (P : OppositeBorelPair G)
    {U : ClosedSubgroup P.positive.group} {N : ClosedSubgroup P.negative.group}
    (hU : IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive) U)
    (hN : IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.negative) N)
    (σ : Representation G.val I) (v : I → k) :
    orbitSpan σ (OpenCell.cellMap P.torus N U) v = orbitSpan σ (𝟙 G.val.X) v := by
  haveI : Smooth G.val.X.hom := P.reductive.1
  haveI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  haveI : IsAffine P.torus.group.X.left := subgroupAffine P.torus
  haveI : IsAffine U.group.X.left := subgroupAffine (G := Unipotent.closedSubgroupAlgebraicGroup P.positive) U
  haveI : IsAffine N.group.X.left := subgroupAffine (G := Unipotent.closedSubgroupAlgebraicGroup P.negative) N
  haveI : IsAffine (P.torus.group.X ⊗ U.group.X).left := affineTensor _ _
  haveI : IsAffine (N.group.X ⊗ (P.torus.group.X ⊗ U.group.X)).left := affineTensor _ _
  have hd := (LinearAlgebraicGroups.Flag.OpenCell.openCell G P.reductive P.torus P.split P.maximal
    P.positive P.negative P.positiveBorel P.negativeBorel P.inPositive P.inNegative
    P.opposite N U hN hU).2.1 k
  exact orbitSpan_of_dense σ _ (dense_of_self_baseChange _ hd) v

private theorem evaluation_fixed_kernel {P : OppositeBorelPair G}
    (p : BorelProjection P)
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (b : Module.Basis I k (covariantFunctions q c))
    (σ : Representation G.val I) (htrans : TranslatedEvaluation e b σ)
    (U : ClosedSubgroup P.positive.group)
    (hU : IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive) U)
    (v : I → k)
    (hv : v ∈ fixedSpace σ (U.inclusion ≫ P.positive.inclusion))
    (hzero : evaluationLinear b (CommAlgCat.of k k) v = 0) : v = 0 := by
  let N := p.radical
  let m := OpenCell.cellMap P.torus N U
  let ev := evaluationLinear b (CommAlgCat.of k k)
  have hz : counit (R := k) (b.equivFun.symm v : A) = 0 := by
    have he := evaluationLinear_extend b (CommAlgCat.of k k) v
    change ev v = counit (R := k) (b.equivFun.symm v : A) at he
    exact he.symm.trans hzero
  have heval (R : TestAlgebra k) (g : GroupPoints G.val R) (ℓ : R →ₗ[k] k) :
      ev (orbitCoefficient σ R g ℓ v) =
        ℓ (evaluationLinear b R (act σ R g (extendVector R v))) := by
    simp only [ev, evaluationLinear, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      orbitCoefficient, Algebra.algebraMap_self_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← map_smul, Algebra.smul_def, smul_eq_mul]
  have htest (R : TestAlgebra k) (x : Points (N.group.X ⊗ (P.torus.group.X ⊗ U.group.X)) R) :
      evaluationLinear b R (act σ R (x ≫ m) (extendVector R v)) = 0 := by
    let n : GroupPoints N.group R := x ≫ fst _ _
    let t : GroupPoints P.torus.group R := x ≫ snd _ _ ≫ fst _ _
    let u : GroupPoints U.group R := x ≫ snd _ _ ≫ snd _ _
    let g : GroupPoints P.negative.group R := (n ≫ N.inclusion.hom.hom) * (t ≫ p.inclusion.hom.hom)
    have ht : p.inclusion.hom.hom ≫ P.negative.inclusion.hom.hom = P.torus.inclusion.hom.hom :=
      (Grp.forget _).congr_map p.inclusion_comp
    have hx : x ≫ m = (g ≫ P.negative.inclusion.hom.hom) *
        (u ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom) := by
      simp only [m, OpenCell.cellMap, CocharacterDynamics.multiplyFactors, g, n, t, u,
        MonObj.comp_mul, MonObj.mul_comp, Category.assoc, ht, mul_assoc]
      rfl
    rw [hx]
    erw [act_mul σ R (g ≫ P.negative.inclusion.hom.hom)
      (u ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom), mem_fixedSpace.mp hv R u]
    erw [evaluationLinear_subgroup e d hq b σ htrans R g v]
    rw [evaluationLinear_extend, hz, map_zero, mul_zero]
  have hle : orbitSpan σ m v ≤ LinearMap.ker ev := by
    refine iSup_le fun R ↦ iSup_le fun x ↦ Submodule.span_le.mpr ?_
    rintro _ ⟨ℓ, rfl⟩
    change orbitCoefficient σ R (x ≫ m) ℓ v ∈ LinearMap.ker ev
    apply LinearMap.mem_ker.mpr
    erw [heval R (x ≫ m) ℓ, htest R x, map_zero]
  rw [denseCell P hU p.isRadical] at hle
  let R := CommAlgCat.of k A
  letI := convolutionGroup A R
  let a : WithConv (A →ₐ[k] R) := toConv (AlgHom.id k A)
  let g := (pointIso e).hom.app R a⁻¹
  have h (ℓ : A →ₗ[k] k) := (orbit_le_iff σ v _).mp hle R g ℓ
  have hfun (ℓ : A →ₗ[k] k) : ℓ (b.equivFun.symm v : A) = 0 := by
    have hh := h ℓ
    rw [LinearMap.mem_ker, heval, htrans] at hh
    simpa [g, a] using hh
  have hA : (b.equivFun.symm v : A) = 0 := by
    by_contra hn
    obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k hn
    exact hℓ (hfun ℓ)
  apply b.equivFun.symm.injective
  exact Subtype.ext (by simpa using hA)

private theorem weightSpacesIndependent (P : OppositeBorelPair G) (σ : Representation G.val I) :
    iSupIndep (weightSpace σ P.torus) := by
  classical
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation P.split
  obtain ⟨χ, _, hχ, _, _⟩ :=
    LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  obtain ⟨δ, hδ⟩ := torusPoint_weights σ i χ hχ
  let E := χ.toEquiv.trans (charactersOfIso i)
  have hi : iSupIndep (weightSpace σ P.torus) := by
    apply iSupIndep.comp' (f := E) _ E.surjective
    change iSupIndep (fun m ↦ weightSpace σ P.torus (E m))
    rw [show (fun m ↦ weightSpace σ P.torus (E m)) = _ from funext hδ]
    letI : DecidableEq (StandardLattice r) := Classical.decEq _
    exact (LinearAlgebraicGroups.WeightDecomposition.weightDecomposition δ).submodule_iSupIndep
  exact hi

private theorem exists_primitive_above (P : OppositeBorelPair G)
    [IsCommMonObj P.torus.group.X] (D₀ : Datum P.torus)
    {U : ClosedSubgroup P.positive.group}
    (hU : IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive) U)
    (σ : Representation G.val I) (hσ : RootOrbit σ P.torus)
    (height : Additive (Character P.torus.group) →ₗ[ℤ] ℝ)
    (hheight : ∀ α ∈ subgroupRoots P.torus P.positive, 0 < height (Additive.ofMul α.val))
    (mu : Character P.torus.group) (hmu : weightSpace σ P.torus mu ≠ ⊥) :
    ∃ nu : Character P.torus.group, DominanceLE P.torus P.positive mu nu ∧
      ∃ v, IsPrimitive σ P.torus P.positive U nu v := by
  classical
  let T := P.torus
  let B := P.positive
  letI := D₀.finiteRoots
  let S := {nu | weightSpace σ T nu ≠ ⊥ ∧ DominanceLE T B mu nu}
  have hs : S.Finite := (Submodule.finite_ne_bot_of_iSupIndep (weightSpacesIndependent P σ)).subset
    fun _ h => h.1
  have hself : mu ∈ S := ⟨hmu, (dominanceLE_iff T B mu mu).mpr (by simp)⟩
  obtain ⟨nu, hnu, hmax⟩ := Finset.exists_max_image hs.toFinset
    (fun nu ↦ height (Additive.ofMul nu)) ⟨mu, hs.mem_toFinset.mpr hself⟩
  have hnu' : nu ∈ S := hs.mem_toFinset.mp hnu
  obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff _).mp hnu'.1
  refine ⟨nu, hnu'.2, v, hvne, mem_fixedSpace.mpr ?_, hv⟩
  have hshift (α : Root T) (hα : α ∈ subgroupRoots T B) (j : ℕ) (hj : 0 < j) :
      weightSpace σ T (nu * α.val ^ j) = ⊥ := by
    let ψ := nu * α.val ^ j
    by_contra hn
    have he : Additive.ofMul ψ - Additive.ofMul nu = j • Additive.ofMul α.val := by
      change (Additive.ofMul nu + j • Additive.ofMul α.val) - Additive.ofMul nu = _
      abel
    have hψ : ψ ∈ S := by
      refine ⟨hn, (dominanceLE_iff T B mu ψ).mpr ?_⟩
      rw [show Additive.ofMul ψ - Additive.ofMul mu =
        (Additive.ofMul ψ - Additive.ofMul nu) + (Additive.ofMul nu - Additive.ofMul mu) by abel, he]
      exact Submodule.add_mem _ (Submodule.smul_mem _ j
        (positiveRoot_mem_cone T B height hheight α hα))
        ((dominanceLE_iff T B mu nu).mp hnu'.2)
    have h := hmax ψ (hs.mem_toFinset.mpr hψ)
    have hh := congrArg height he
    rw [map_sub, map_nsmul] at hh
    have hpos := nsmul_pos (hheight α hα) hj.ne'
    change height (Additive.ofMul ψ) ≤ height (Additive.ofMul nu) at h
    linarith
  let Coord (α : Root T) :=
    Σ H : {H : ClosedSubgroup G.val // Specs.RootGroups.IsRootSubgroup T H α.val},
      Σ L : Specs.RootGroups.AdditiveLine k, {x : L.group ≅ H.val.group //
        Specs.RootGroups.HasScalarAction T α.val (x.hom ≫ H.val.inclusion)}
  have hc (α : Root T) : Nonempty (Coord α) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, L, pos, _, hpos, _, hact, _, _⟩ := D₀.attached α
    exact ⟨⟨⟨_, hpos⟩, L, ⟨pos.root, hact⟩⟩⟩
  let coord (α : Root T) := Classical.choice (hc α)
  let roots : RootSubgroupFamily T := fun α ↦ (coord α).1
  obtain ⟨l, hl⟩ := existsEnumeration (subgroupRoots T B)
  obtain ⟨comm, _, _, _, _, _, dec⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity G P.reductive T P.split P.maximal
  obtain ⟨V, _, _, hV, _, _, _, _, _, chart⟩ := dec B P.positiveBorel P.inPositive
  obtain ⟨E, hE⟩ := radicalProductFor roots l hU hV (chart roots l hl)
  intro R u
  have hprod (l' : List (Root T)) (hm : ∀ α ∈ l', α ∈ subgroupRoots T B)
      (x : Points (OrderedRootProducts.product (fun α => (roots α).val.group.X) l') R) :
      act σ R (x ≫ rootProduct roots l') (extendVector R v) = extendVector R v := by
    induction l' with
    | nil =>
      rw [show x ≫ rootProduct roots [] = (1 : GroupPoints G.val R) from MonObj.comp_one x]
      rw [act_one]
    | cons α l' ih =>
      let x₁ := x ≫ fst _ _
      let x₂ := x ≫ snd _ _
      let g : GroupPoints G.val R := x ≫ rootProduct roots (α :: l')
      let g₁ : GroupPoints G.val R := x₁ ≫ (roots α).val.inclusion.hom.hom
      let g₂ : GroupPoints G.val R := x₂ ≫ rootProduct roots l'
      have hmul : g = g₁ * g₂ := by
        dsimp only [g, g₁, g₂, rootProduct, x₁, x₂]
        erw [MonObj.comp_mul, Category.assoc, Category.assoc]
        rfl
      change act σ R g (extendVector R v) = _
      rw [hmul, act_mul]
      erw [ih (fun a ha => hm a (List.mem_cons_of_mem _ ha)) x₂]
      change act σ R (x₁ ≫ (roots α).val.inclusion.hom.hom) (extendVector R v) = _
      obtain ⟨z, hz⟩ := rootPoint_surjective (coord α).2.2.val R x₁
      obtain ⟨pp, h₀, hcoeff, hact⟩ := hσ α (roots α).val (roots α).property
        (coord α).2.1 (coord α).2.2.val (coord α).2.2.property nu ⟨v, hv⟩
      have hg : x₁ ≫ (roots α).val.inclusion.hom.hom =
          Specs.RootGroups.rootPoint ((coord α).2.2.val.hom ≫ (roots α).val.inclusion) R z := by
        rw [← hz]
        rfl
      rw [hg, hact R z]
      funext i
      have hpp : pp i = Polynomial.C (v i) := by
        ext j
        rcases j with _ | j
        · simpa using congrFun h₀ i
        · have hh := hcoeff (j + 1) (Nat.succ_pos _)
          rw [hshift α (hm α (List.mem_cons_self ..)) _ (Nat.succ_pos _),
            Submodule.mem_bot] at hh
          simpa using congrFun hh i
      simp [hpp, extendVector]
  let x := u ≫ E.inv
  have hx : x ≫ rootProduct roots l = u ≫ (U.inclusion ≫ B.inclusion).hom.hom := by
    rw [← hE]
    change ((u : Points U.group.X R) ≫ E.inv) ≫ E.hom ≫ _ = _
    erw [Category.assoc, E.inv_hom_id_assoc]
    rfl
  rw [← hx]
  exact hprod l (fun α ha => (hl.2 α).mp ha) x

private theorem nonzero_fixed_in_submodule (P : OppositeBorelPair G)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (σ : Representation G.val I) (hcyc : Specs.CyclicHighestWeight.CoactionComparison.{u})
    {U : ClosedSubgroup P.positive.group}
    (hU : IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive) U)
    (hweights : by
      classical
      exact ∀ {J : Type u} [Fintype J] [DecidableEq J] (τ : Representation G.val J),
        DirectSum.IsInternal (fun mu : Character P.torus.group ↦
          (weightSpace τ P.torus mu).comap (fixedSpace τ (U.inclusion ≫ P.positive.inclusion)).subtype))
    (M : Submodule k (I → k)) (hM : IsStable σ M) (hM0 : M ≠ ⊥) :
    ∃ x : I → k, x ∈ M ∧ x ≠ 0 ∧ x ∈ fixedSpace σ (U.inclusion ≫ P.positive.inclusion) := by
  classical
  obtain ⟨δ, hδ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction
    (toCoaction e (Pi.basisFun k I) σ) M).mp ((stable_iff hcyc σ A e M).mp hM)
  let J := ULift.{u} (Fin (Module.finrank k M))
  let b : Module.Basis J k M := (Module.finBasis k M).reindex Equiv.ulift.symm
  let τ := fromCoaction e b δ
  let inc := M.subtype.comp b.equivFun.symm.toLinearMap
  have hinc := inclusion_equivariant e σ M b δ hδ
  have hInj : Function.Injective inc := Subtype.val_injective.comp b.equivFun.symm.injective
  have hn : (⊤ : Submodule k (J → k)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hM0
    refine (Submodule.ne_bot_iff _).mpr ⟨b.equivFun ⟨x, hx⟩, Submodule.mem_top, ?_⟩
    exact fun h ↦ hx0 (congrArg Subtype.val (b.equivFun.injective (h.trans b.equivFun.map_zero.symm)))
  obtain ⟨mu, x, hx⟩ := exists_primitive τ hU.2.1 (hweights τ) hn
  refine ⟨inc x, (b.equivFun.symm x).property, fun h ↦ hx.1 (hInj (h.trans inc.map_zero.symm)),
    mem_fixedSpace.mpr ?_⟩
  intro R g
  let gG : GroupPoints G.val R := g ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom
  have hfix : act τ R gG (extendVector R x) = (1 : R) • extendVector R x := by
    simpa only [one_smul] using mem_fixedSpace.mp hx.2.1 R g
  have hfix' : act σ R gG (extendVector R (inc x)) = (1 : R) • extendVector R (inc x) := by
    apply (act_eq_scalar_iff σ R gG (inc x) 1).mpr
    intro ℓ
    rw [← hinc R gG ℓ x, (act_eq_scalar_iff τ R gG x 1).mp hfix ℓ, map_smul]
  simpa only [one_smul] using hfix'

private theorem eval_torus {P : OppositeBorelPair G}
    (p : BorelProjection P) (χ : Character P.torus.group)
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ D)
    (hφ : specGroupMap φ = d.hom ≫ p.projection ≫ χ)
    (hc : (c : D) = characterCoordinate φ)
    (b : Module.Basis I k (covariantFunctions q c))
    (σ : Representation G.val I) (htrans : TranslatedEvaluation e b σ)
    (R : TestAlgebra k) (t : GroupPoints P.torus.group R) (v : I → k) :
    evaluationLinear b R
      (act σ R (t ≫ P.torus.inclusion.hom.hom) (extendVector R v)) =
        characterValue χ R t * evaluationLinear b R (extendVector R v) := by
  let a : WithConv (D →ₐ[k] R) := (pointIso d).inv.app R (t ≫ p.inclusion.hom.hom)
  have ha : (pointIso d).hom.app R a = t ≫ p.inclusion.hom.hom :=
    ((pointIso d).app R).inv_hom_id_apply _
  have ht := congrArg (fun f : P.torus.group ⟶ G.val ↦ f.hom.hom) p.inclusion_comp
  change p.inclusion.hom.hom ≫ P.negative.inclusion.hom.hom = _ at ht
  have hcomp : (t ≫ p.inclusion.hom.hom) ≫ P.negative.inclusion.hom.hom =
      t ≫ P.torus.inclusion.hom.hom := by
    change ((t : Points P.torus.group.X R) ≫ p.inclusion.hom.hom) ≫ _ = _
    erw [Category.assoc, ht]
  rw [← hcomp]
  erw [evaluationLinear_subgroup e d hq b σ htrans R (t ≫ p.inclusion.hom.hom) v]
  change a (c : D) * _ = _
  congr 1
  let M := DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters
  have he := inducedPoint (q := φ) (Iso.refl (specGroup M)) d (p.projection ≫ χ)
    (by change specGroupMap φ ≫ 𝟙 _ = _
        rw [Category.comp_id]
        exact hφ) R a
  change (hopfSpecPointIso M).hom.app R (toConv (a.ofConv.comp φ.hom.toAlgHom)) =
    (pointIso d).hom.app R a ≫ p.projection.hom.hom ≫ χ.hom.hom at he
  have hprojection : (t ≫ p.inclusion.hom.hom) ≫ p.projection.hom.hom =
      (t : Points P.torus.group.X R) := by
    change ((t : Points P.torus.group.X R) ≫ p.inclusion.hom.hom) ≫ _ = _
    erw [Category.assoc, show p.inclusion.hom.hom ≫ p.projection.hom.hom = 𝟙 _ from
      (Grp.forget _).congr_map p.section_projection, Category.comp_id]
  rw [ha] at he
  have he' : (hopfSpecPointIso M).hom.app R (toConv (a.ofConv.comp φ.hom.toAlgHom)) =
      t ≫ χ.hom.hom := he.trans ((Category.assoc
        (t ≫ p.inclusion.hom.hom : Points P.negative.group.X R) _ _).symm.trans
        (congrArg (fun f => f ≫ χ.hom.hom) hprojection))
  have hinv := ((hopfSpecPointIso M).app R).hom_inv_id_apply
    (toConv (a.ofConv.comp φ.hom.toAlgHom))
  change (hopfSpecPointIso M).inv.app R
    ((hopfSpecPointIso M).hom.app R (toConv (a.ofConv.comp φ.hom.toAlgHom))) = _ at hinv
  erw [characterValue_eq_eval, ← he', hinv]
  rw [hc]
  rfl

private theorem weyl_weight_nonzero {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D₀ : Datum T} (ey : DatumAndWeyl.Identification D₀)
    (σ : Representation G.val I) (hσ : WeylTransport σ ey) (w : D₀.rootDatum.weylGroup)
    (mu : Character T.group) (hmu : weightSpace σ T mu ≠ ⊥) :
    weightSpace σ T ((ey.labelEquiv w).val mu) ≠ ⊥ := by
  let K := CommAlgCat.of k k
  obtain ⟨n, hn⟩ := rationalWeylLabel_surjective ey w
  have hw : n ≫ ey.quotient.hom.hom = ey.image.constantGroup.sectionPoint (ey.labelEquiv w) := by
    let F := ey.image.constantGroup.families (𝟙_ (SchemeOver k))
    have hlabel : ey.labelEquiv w = F (n ≫ ey.quotient.hom.hom) (IsLocalRing.closedPoint k) :=
      hn ▸ ey.labelEquiv.apply_symm_apply _
    apply F.injective
    change F _ = ey.image.constantGroup.families _ _
    have hid : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) := Subsingleton.elim _ _
    have hs := ey.image.constantGroup.constant (𝟙_ (SchemeOver k)) (ey.labelEquiv w)
    rw [hid, Category.id_comp] at hs
    rw [hs]
    apply LocallyConstant.ext
    intro x
    change F _ x = ey.labelEquiv w
    rw [hlabel, Subsingleton.elim (α := PrimeSpectrum k) x (IsLocalRing.closedPoint k)]
  let S := unop ((testSpec k).rightOp.obj K)
  let nK : GroupPoints ey.normalizer.group K := toUnit S ≫ n
  have hnK : nK ≫ ey.quotient.hom.hom =
      toUnit _ ≫ ey.image.constantGroup.sectionPoint (ey.labelEquiv w) := by
    change (toUnit S ≫ n) ≫ ey.quotient.hom.hom =
      toUnit S ≫ ey.image.constantGroup.sectionPoint (ey.labelEquiv w)
    rw [Category.assoc, hw]
  obtain ⟨E, _⟩ := hσ w nK hnK mu
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hmu
  refine (Submodule.ne_bot_iff _).mpr ⟨E ⟨v, hv⟩, (E ⟨v, hv⟩).property, ?_⟩
  exact fun h => hv0 (congrArg Subtype.val (E.injective ((Subtype.ext h).trans E.map_zero.symm)))

private theorem lowerBound (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D₀ : Datum P.torus) (ey : DatumAndWeyl.Identification D₀)
    (f : Additive (Character P.torus.group) →ₗ[ℤ] ℤ) (base : D₀.rootDatum.Base)
    (hf : ∀ i, f (D₀.rootDatum.root i) ≠ 0)
    (hb : ∀ i, base.IsPos i ↔ i ∈ SimpleRoots.positive D₀.rootDatum f)
    (hB : ∀ i, base.IsPos i ↔ i ∈ subgroupRoots P.torus P.positive)
    (height : Additive (Character P.torus.group) →ₗ[ℤ] ℝ)
    (hheight : ∀ α ∈ subgroupRoots P.torus P.positive, 0 < height (Additive.ofMul α.val))
    (σ : Representation G.val I) (hσ : WeylTransport σ ey)
    (χ mu : Character P.torus.group) (hmu : weightSpace σ P.torus mu ≠ ⊥)
    (hu : ∀ nu, weightSpace σ P.torus nu ≠ ⊥ → DominanceLE P.torus P.positive nu χ)
    (w : D₀.rootDatum.weylGroup)
    (hw : ∀ w', SimpleRoots.wordLength D₀.rootDatum base w' ≤
      SimpleRoots.wordLength D₀.rootDatum base w) :
    DominanceLE P.torus P.positive ((ey.labelEquiv w).val χ) mu := by
  let T := P.torus
  let B := P.positive
  letI := D₀.finiteRoots
  letI := D₀.freeCharacters
  letI := D₀.finiteCharacters
  letI := D₀.reduced
  letI := D₀.rootDatum.indexNeg
  let nu := (ey.labelEquiv w⁻¹).val mu
  have hnu := hu nu (weyl_weight_nonzero ey σ hσ w⁻¹ mu hmu)
  let a := w.val.weightEquiv
  have hmu' : a (Additive.ofMul nu) = Additive.ofMul mu := by
    change w.val.weightEquiv (Additive.ofMul ((ey.labelEquiv w⁻¹).val mu)) = _
    rw [← ey.characterAction]
    change w.val.weightEquiv (w.val.weightEquiv.symm (Additive.ofMul mu)) = _
    exact a.apply_symm_apply _
  have hcone (x : Additive (Character T.group)) (hx : x ∈ positiveCone T B) :
      -a x ∈ positiveCone T B := by
    refine Submodule.span_induction (p := fun x _ ↦ -a x ∈ positiveCone T B) ?_
      (by simp) (fun x y _ _ hx hy => by
        rw [map_add, neg_add_rev]
        exact Submodule.add_mem _ hy hx)
      (fun n x _ hx => by
        rw [map_nsmul, ← smul_neg]
        exact Submodule.smul_mem _ n hx) hx
    rintro _ ⟨α, rfl⟩
    let i := D₀.rootDatum.weylGroupToPerm w α.val
    have hi : ¬ base.IsPos i := fun h =>
      (longest_flips_sign base f hf hb w hw α.val).mp h ((hB _).mpr α.property.1)
    have hneg : -i ∈ subgroupRoots T B :=
      (hB _).mp ((RootPairing.Base.IsPos.neg_iff_not base i).mpr hi)
    have hh := positiveRoot_mem_cone T B height hheight (-i) hneg
    rw [← D₀.root_eq, rootOfNeg, ← D₀.rootDatum.weylGroup_apply_root, D₀.root_eq] at hh
    exact hh
  have h := hcone _ ((dominanceLE_iff T B nu χ).mp hnu)
  rw [map_sub, neg_sub, hmu', ey.characterAction] at h
  exact (dominanceLE_iff T B _ _).mpr h

private theorem moduleSocle {P : OppositeBorelPair G}
    (p : BorelProjection P) (χ : Character P.torus.group)
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ D)
    (hφ : specGroupMap φ = d.hom ≫ p.projection ≫ χ) (hc : (c : D) = characterCoordinate φ)
    (ρ : RightComodule k A (covariantFunctions q c)) [FiniteDimensional k (covariantFunctions q c)]
    (htrans : IsLeftTranslation ρ) : SocleProperties P χ A e q c ρ := by
  classical
  let T := P.torus
  let B := P.positive
  let W := covariantFunctions q c
  let J := ULift.{u} (Fin (Module.finrank k W))
  let b : Module.Basis J k W := (Module.finBasis k W).reindex Equiv.ulift.symm
  let σ := fromCoaction (pointIso e) b ρ
  have htranslate : TranslatedEvaluation e b σ := evaluationLinear_act b ρ (pointIso e) htrans
  obtain ⟨comm, D₀, ey, U, _, hU, _, data⟩ :=
    LinearAlgebraicGroups.Representation.RootWeightAction.rootWeightAction
      G P.reductive T B P.split P.maximal P.positiveBorel P.inPositive
  letI := comm
  letI := D₀.finiteRoots
  letI := D₀.freeCharacters
  letI := D₀.finiteCharacters
  letI := D₀.reduced
  obtain ⟨cochar, _, hreg, _, hpos⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
      G P.reductive T P.split P.maximal).1 B P.positiveBorel P.inPositive
  let f := Specs.SimpleRoots.evaluate D₀ cochar
  have hf (i : Root T) : f (D₀.rootDatum.root i) = pairing T.group i.val cochar := by
    change D₀.rootDatum.toLinearMap (D₀.rootDatum.root i) (Additive.ofMul cochar) = _
    rw [D₀.root_eq, D₀.pairing_eq]
  have hfreg (i : Root T) : f (D₀.rootDatum.root i) ≠ 0 := by
    rw [hf]
    exact hreg i
  obtain ⟨base, hb⟩ := LinearAlgebraicGroups.RootData.SimpleRoots.baseFor D₀.rootDatum f hfreg
  have hb' (i : Root T) : base.IsPos i ↔ i ∈ subgroupRoots T B := by
    rw [hb.positive_iff, hpos]
    change 0 < f (D₀.rootDatum.root i) ↔ 0 < pairing T.group i.val cochar
    rw [hf]
  let height := Specs.SimpleRoots.realFunctional f
  have hheight (i : Root T) (hi : i ∈ subgroupRoots T B) : 0 < height (Additive.ofMul i.val) := by
    have h := (hb.positive_iff i).mp ((hb' i).mpr hi)
    change 0 < f (D₀.rootDatum.root i) at h
    rw [D₀.root_eq] at h
    change 0 < (f (Additive.ofMul i.val) : ℝ)
    exact_mod_cast h
  let F := fixedSpace σ (U.inclusion ≫ B.inclusion)
  let ev := evaluationLinear b (CommAlgCat.of k k)
  have heval (v : J → k) : ev v = counit (R := k) (b.equivFun.symm v : A) := by
    exact evaluationLinear_extend b (CommAlgCat.of k k) v
  have hk (v : J → k) (hv : v ∈ F) (h0 : ev v = 0) : v = 0 :=
    evaluation_fixed_kernel p e d hq b σ htranslate U hU v hv h0
  have hinj : Function.Injective (fun v : F ↦ counit (R := k) (b.equivFun.symm v.val : A)) := by
    intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hk _ (F.sub_mem x.property y.property)
    rw [map_sub, heval, heval]
    exact sub_eq_zero.mpr h
  refine ⟨J, inferInstance, inferInstance, b, U, hU, comm, D₀, ey, base, hb', σ, ?_, hinj, ?_⟩
  · intro S g v i
    have h := evaluation (pointIso e) b ρ S g (b.equivFun.symm v) i
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  intro hW
  letI := hW
  have hn : (⊤ : Submodule k (J → k)) ≠ ⊥ := by
    obtain ⟨v, w, hvw⟩ := exists_pair_ne W
    refine (Submodule.ne_bot_iff _).mpr ⟨b.equivFun (v - w), Submodule.mem_top, ?_⟩
    exact fun h ↦ hvw (sub_eq_zero.mp (b.equivFun.injective (h.trans b.equivFun.map_zero.symm)))
  obtain ⟨hroot, hweyl, _, hstable, hdecomp⟩ := data σ
  obtain ⟨_, v, hv⟩ := exists_primitive σ hU.2.1 hdecomp hn
  have hv0 : ev v ≠ 0 := fun h ↦ hv.1 (hk v hv.2.1 h)
  have hline : F = Submodule.span k {v} := by
    apply le_antisymm
    · intro x hx
      apply Submodule.mem_span_singleton.mpr
      refine ⟨ev x / ev v, ?_⟩
      apply sub_eq_zero.mp
      apply hk _ (F.sub_mem (F.smul_mem _ hv.2.1) hx)
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv0, sub_self]
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv.2.1)
  have hχ : v ∈ weightSpace σ T χ := by
    apply mem_weightSpace.mpr
    intro R t
    have hs := hstable R t ⟨v, hv.2.1⟩
    have hl : Submodule.span R (Set.range fun z : F ↦ extendVector R z.val) ≤
        Submodule.span R {extendVector R v} := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      have hz : z.val ∈ Submodule.span k {v} := hline.le z.property
      rw [Submodule.mem_span_singleton] at hz
      change extendVector R z.val ∈ _
      obtain ⟨a, ha⟩ := hz
      rw [← ha]
      have hex : extendVector R (a • v) = algebraMap k R a • extendVector R v := by
        ext i
        simp [extendVector, Algebra.smul_def]
      rw [hex]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hl hs)
    have h := eval_torus p χ e d hq φ hφ hc b σ htranslate R t v
    change evaluationLinear b R (act σ R (t ≫ T.inclusion.hom.hom) (extendVector R v)) = _ at h
    rw [← ha, map_smul, smul_eq_mul] at h
    have hunit : IsUnit (evaluationLinear b R (extendVector R v)) := by
      rw [evaluationLinear_extend, ← heval]
      exact (isUnit_iff_ne_zero.mpr hv0).map (algebraMap k R)
    have ha' : a = characterValue χ R t := by
      obtain ⟨u, hu⟩ := hunit
      rw [← hu] at h
      have hr := congrArg (fun x : R => x * ↑u⁻¹) h
      simpa [mul_assoc] using hr
    rw [← ha']
    exact ha.symm
  have hupper (mu : Character T.group) (hmu : weightSpace σ T mu ≠ ⊥) :
      DominanceLE T B mu χ := by
    obtain ⟨nu, hle, x, hx⟩ := exists_primitive_above P D₀ hU σ hroot height hheight mu hmu
    have hs := hx.2.1
    change x ∈ F at hs
    rw [hline] at hs
    have hxχ : x ∈ weightSpace σ T χ :=
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hχ)) hs
    have hnu : nu = χ := by
      by_contra hne
      have hz := ((weightSpacesIndependent P σ).pairwiseDisjoint hne).le_bot
        (show x ∈ weightSpace σ T nu ⊓ weightSpace σ T χ from ⟨hx.2.2, hxχ⟩)
      exact hx.1 ((Submodule.mem_bot k).mp hz)
    exact hnu ▸ hle
  have hd := dominance_of_reflections σ T B D₀ height hheight χ v hχ hv.1
    (fun mu _ => hupper mu)
  let C := orbitSpan σ (𝟙 G.val.X) v
  have hcyc : Specs.CyclicHighestWeight.CoactionComparison.{u} :=
    LinearAlgebraicGroups.Representation.CyclicHighestWeight.cyclicHighestWeight.1
  have hvC : v ∈ C := (orbit_properties hcyc σ A (pointIso e) v).1
  have hC0 : C ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨v, hvC, hv.1⟩
  have hCs : IsStable σ C := orbit_stable hcyc σ A (pointIso e) v
  have hmin (M : Submodule k (J → k)) (hM : IsStable σ M) (hM0 : M ≠ ⊥) : C ≤ M := by
    obtain ⟨x, hxM, hx0, hxF⟩ := nonzero_fixed_in_submodule P (pointIso e) σ hcyc hU
      (fun {_} _ _ τ ↦ (data τ).2.2.2.2) M hM hM0
    change x ∈ F at hxF
    rw [hline, Submodule.mem_span_singleton] at hxF
    obtain ⟨a, ha⟩ := hxF
    have ha0 : a ≠ 0 := fun h ↦ hx0 (by rw [← ha, h, zero_smul])
    have hvM := M.smul_mem a⁻¹ hxM
    rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul] at hvM
    exact hM v hvM
  have hsimple : IsSimpleSubmodule σ C :=
    ⟨hCs, hC0, fun M hs hle => or_iff_not_imp_left.mpr fun h0 => le_antisymm hle (hmin M hs h0)⟩
  have hFC : F ≤ C := by
    rw [hline]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvC)
  refine ⟨v, hv.1, hline, hχ, hd, ⟨C, hsimple, ?_⟩, hFC, hsimple, ?_⟩
  · intro M hM
    exact (hM.2.2 C hCs (hmin M hM.1 hM.2.1)).resolve_left hC0 |>.symm
  · intro mu hmu
    exact ⟨hupper mu hmu, lowerBound P D₀ ey f base hfreg hb.positive_iff hb'
      height hheight σ hweyl χ mu hmu hupper⟩

/-- Evaluation detects unipotent invariants in the induced module. In the
nonzero case the invariant line generates the unique simple submodule and the
weights lie in the interval determined by the inducing character. -/
theorem inducedSocle : Specs.InducedSocle.Statement.{u} := by
  intro k _ G P χ
  obtain ⟨p, Q, a, A, D, e, d, q, φ, c, ρ₁, L, E, ρ, hs, hp, ht, hj,
    ha, hq, hφ, hc, hρ₁, hfinite, hE, hcoact, htrans, _⟩ :=
    LinearAlgebraicGroups.InductionAdjunction.flagInductionAdjunction k G P χ
  letI := hfinite
  exact ⟨p, Q, a, A, D, e, d, q, φ, c, ρ₁, L, E, ρ, hs, hp, ht, hj, ha, hq, hφ, hc,
    hρ₁, hfinite, hE, hcoact, htrans, moduleSocle p χ e d hq φ hφ hc ρ htrans⟩

end
end LinearAlgebraicGroups.Representation.InducedSocle
