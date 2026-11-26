import Specs.LinearAlgebraicGroups.Albert.SplitAlbertAdjointWeights
import LinearAlgebraicGroups.Albert.SplitFrameTorus
import LinearAlgebraicGroups.Albert.ShortDirections
import LinearAlgebraicGroups.RootData.SchemeCentre
import LinearAlgebraicGroups.Reductive.CentralDerived
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Albert.SplitAlbertAdjointWeights

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open SplitAlbertAdjointWeightsSpecification SplitFrameTorusSpecification
open IntegralSmoothnessSpecification
open ShortDirectionSpecification (IntegralPresentation)
open TrialitySpecification (Model mapModel)
open CubicSpecification (singleBlockCoordinates)
open FrameSpecification (frameAxis)
open HermitianSpecification (cyclicNext)
open IntegralZornDirectionsSpecification (DirectionIndex direction)
open LinearAlgebraicGroups.Specs.SpinWeights
open LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open LinearAlgebraicGroups.Specs.CharacterPairing (absoluteRoots characterValue)
open LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus)
open LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

open private shortElement mem_splitAutomorphisms integralShortFamilies from LinearAlgebraicGroups.Albert.ShortDirections
open private pullbackPointGroupEquiv from LinearAlgebraicGroups.Albert.IntegralSmoothness

variable {P : IntegralPresentation} (G : SplitGroup P)

private theorem affine_point_centre (S : ScalarTest) (g : ScalarPoints G.group S)
    (central : ∀ (A : ScalarTest) (f : S ⟶ A) (a : ScalarPoints G.group A),
      (scalarSpec.map f.op ≫ g) * a = a * (scalarSpec.map f.op ≫ g)) :
    g = 1 := by
  obtain ⟨T, _, hfix, _, _⟩ := SplitFrameTorus.splitFrameTorus P G
  have hframe := hfix S g (fun A f t => central A f (t ≫ T.inclusion.hom.hom))
  let a := G.action S g
  have fixBlock (i : Fin 3) (j : DirectionIndex) :
      a (singleBlockCoordinates i (direction S j)) =
        singleBlockCoordinates i (direction S j) := by
    let b := shortElement S (i, j) (1 : S)
    have hb : b.val ∈ {q | IdempotentSpecification.IsSplitAutomorphism q} := (mem_splitAutomorphisms _).mp b.property
    rw [← G.image S] at hb
    obtain ⟨p, hp⟩ := hb
    have hh := central S (𝟙 S) p
    rw [op_id, (scalarSpec).map_id, Category.id_comp] at hh
    have hcomm : a (b.val (frameAxis (cyclicNext i))) =
        b.val (a (frameAxis (cyclicNext i))) := by
      have := congrArg (fun q => (G.action S q) (frameAxis (cyclicNext i))) hh
      simpa only [map_mul, hp, LinearEquiv.mul_apply] using this
    have he : b.val (frameAxis (cyclicNext i)) =
        frameAxis (cyclicNext i) + singleBlockCoordinates i (direction S j) := by
      rw [← one_smul S (singleBlockCoordinates i (direction S j))]
      exact (integralShortFamilies.evaluates S i j 1).2.1
    rw [hframe, he, map_add, hframe] at hcomm
    exact add_left_cancel hcomm
  apply G.injective S
  rw [map_one]
  apply LinearEquiv.toLinearMap_injective
  apply ((Pi.basisFun S (Fin 3)).prod
    (Pi.basis fun _ : Fin 3 => IntegralZornDirections.directionBasis S)).ext
  intro j
  rcases j with i | ⟨i, j⟩
  · rw [Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply, Pi.basisFun_apply,
      LinearMap.inl_apply]
    exact hframe i
  · rw [Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply, Pi.basis_apply,
      LinearMap.inr_apply, IntegralZornDirections.directionBasis_apply]
    exact fixBlock i j

private theorem integral_has_trivial_centre : HasTrivialCentre G.group := by
  intro X z central
  apply Over.OverMorphism.ext
  apply X.left.affineCover.hom_ext
  intro i
  let Y := X.left.affineCover.X i
  let φ := X.left.affineCover.f i
  let : IsAffine Y := X.left.isAffine_affineCover i
  let e := Y.isoSpec.symm
  let f := Scheme.Spec.preimage (e.hom ≫ φ ≫ X.hom)
  let A := Y.presheaf.obj (op ⊤)
  let : Algebra ℤ A := f.unop.hom.toAlgebra
  let S := CommAlgCat.of ℤ A
  let u : scalarSpec.obj (op S) ⟶ X := Over.homMk (e.hom ≫ φ) (by
    change (e.hom ≫ φ) ≫ X.hom = Spec.map f.unop
    exact (Scheme.Spec.map_preimage _).symm)
  have hz : u ≫ z = 1 := affine_point_centre G S (u ≫ z) fun B a b => by
    simpa only [Category.assoc] using central _ (scalarSpec.map a.op ≫ u) b
  have h := congrArg Over.Hom.left (hz.trans (MonObj.comp_one u).symm)
  change (e.hom ≫ φ) ≫ z.left = (e.hom ≫ φ) ≫ (1 : X ⟶ G.group.X).left at h
  apply (cancel_epi e.hom).mp
  simpa only [Category.assoc] using h

theorem integralCentre : IntegralCentre := by
  intro P G R _
  let a := Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
  let H := ((Over.pullback a).mapGrp).obj G.group
  intro X z central
  let E := pullbackPointGroupEquiv a X G.group
  let z₀ := E z
  have hz : z₀ = 1 := integral_has_trivial_centre G _ z₀ fun Y f g => by
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (f.left ≫ X.hom)
    let f' : Y' ⟶ X := Over.homMk f.left rfl
    let e : (Over.map a).obj Y' ≅ Y := Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Y.hom = (f.left ≫ X.hom) ≫ a
      rw [Category.id_comp, Category.assoc]
      exact (Over.w f).symm)
    let F := pullbackPointGroupEquiv a Y' G.group
    let b := F.symm (e.hom ≫ g)
    have hb : F b = e.hom ≫ g := F.apply_symm_apply _
    have hleft : F (f' ≫ z) = e.hom ≫ f ≫ z₀ := by
      apply Over.OverMorphism.ext
      change (f.left ≫ z.left) ≫ pullback.fst G.group.X.hom a =
        𝟙 _ ≫ f.left ≫ (z.left ≫ pullback.fst G.group.X.hom a)
      rw [Category.id_comp]
      exact Category.assoc _ _ _
    have eq : (e.hom ≫ (f ≫ z₀)) * (e.hom ≫ g) =
        (e.hom ≫ g) * (e.hom ≫ (f ≫ z₀)) := by
      have h := congrArg F (central Y' f' b)
      rwa [map_mul, map_mul, hleft, hb] at h
    apply (cancel_epi e.hom).mp
    simpa only [MonObj.comp_mul] using eq
  apply E.injective
  rw [map_one]
  exact hz

open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers

open private integralFibrePoints overIntegers overIntegersMap projectIntegralPoint_natural
  from LinearAlgebraicGroups.Albert.SplitFrameTorus
open private splitDiagonalGroup diagonalGroupPoints diagonalGroupPoints_natural
  diagonalGroup_affine splitDiagonalGroup_split diagonalCharacterCoordinates
  from LinearAlgebraicGroups.Albert.SpinWeights
open private groupIsoOfPoints groupIsoOfPoints_hom
  from LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 2048 in
theorem fibreCharacters : FibreCharacters := by
  intro P G T k _
  let H := (T.fibre k).group
  let D := splitDiagonalGroup k
  let d (R : TestAlgebra k) : Points H.X R ≃* DiagonalPoints R :=
    (integralFibrePoints diagonalTorus R).trans (T.points (overIntegers R))
  have hn {R S : TestAlgebra k} (f : R ⟶ S) (t : Points H.X R) :
      d S (mapPoints f t) = mapDiagonal f.hom.toRingHom (d R t) := by
    change T.points (overIntegers S) (integralFibrePoints diagonalTorus S (mapPoints f t)) = _
    rw [show integralFibrePoints diagonalTorus S (mapPoints f t) =
        scalarSpec.map (overIntegersMap f).op ≫ integralFibrePoints diagonalTorus R t from
      projectIntegralPoint_natural diagonalTorus.X f t, T.natural]
    rfl
  let : IsAffine H.X.left := by
    have : IsAffine diagonalTorus.X.left := by
      change IsAffine (Spec (CommRingCat.of LaurentRing))
      infer_instance
    change IsAffine (pullback diagonalTorus.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))
    infer_instance
  let : IsAffine D.X.left := diagonalGroup_affine k
  let h (R : TestAlgebra k) := (d R).trans (diagonalGroupPoints k R).symm
  let n : (groupPointsFunctor k).obj H ≅ (groupPointsFunctor k).obj D :=
    NatIso.ofComponents (fun R => (h R).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro t
      change Points H.X R at t
      change h S (mapPoints f t) = mapPoints f (h R t)
      apply (diagonalGroupPoints k S).injective
      change diagonalGroupPoints k S ((diagonalGroupPoints k S).symm (d S (mapPoints f t))) = _
      rw [MulEquiv.apply_symm_apply, diagonalGroupPoints_natural, hn f t]
      change _ = mapDiagonal f.hom.toRingHom
        (diagonalGroupPoints k R ((diagonalGroupPoints k R).symm (d R t)))
      rw [MulEquiv.apply_symm_apply])
  let e := groupIsoOfPoints H D n
  have he (R : TestAlgebra k) (t : Points H.X R) :
      diagonalGroupPoints k R (t ≫ e.hom.hom.hom) = d R t := by
    have h' := DFunLike.congr_fun
      (congrArg (fun q => (q.app R).hom) (groupIsoOfPoints_hom H D n)) t
    change t ≫ e.hom.hom.hom = (diagonalGroupPoints k R).symm (d R t) at h'
    rw [h', MulEquiv.apply_symm_apply]
  have hs : IsSplitTorus H := by
    obtain ⟨r, ⟨j⟩⟩ := splitDiagonalGroup_split k
    exact ⟨r, ⟨e ≪≫ j⟩⟩
  obtain ⟨C, hC⟩ := diagonalCharacterCoordinates k
  refine ⟨hs, ⟨⟨d, (charactersOfIso e).toAdditive.toIntLinearEquiv.trans C, ?_, ?_⟩⟩⟩
  · intro R t
    exact ⟨integralFibrePoints diagonalTorus R t, rfl, rfl⟩
  · intro R t χ
    have hc := hC R (t ≫ e.hom.hom.hom) ((charactersOfIso e) χ)
    rw [he] at hc
    have hcomp : (t ≫ e.hom.hom.hom) ≫ ((charactersOfIso e) χ).hom.hom =
        t ≫ χ.hom.hom := by
      change (t ≫ e.hom.hom.hom) ≫ (e.inv.hom.hom ≫ χ.hom.hom) = _
      have hi : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 H.X :=
        (Grp.forget _).congr_map e.hom_inv_id
      rw [Category.assoc, ← Category.assoc (f := e.hom.hom.hom), hi, Category.id_comp]
    calc
      characterValue χ R t = characterValue ((charactersOfIso e) χ) R
          (t ≫ e.hom.hom.hom) := by
        unfold characterValue
        dsimp only
        rw [hcomp]
      _ = _ := hc

open private fieldSpinGroup fieldSpinPoints spinPointEquiv_natural diagonalInclusion
  diagonalInclusion_point diagonalSubgroup absoluteRoots_coordinates diagonalLift
  from LinearAlgebraicGroups.Albert.SpinWeights
open private markedTorus spinAlbert spinAlbert_injective spinAlbert_natural
  spinAlbert_of_fixesFrame torusInclusion torusInclusion_points projectIntegralPoint_comp
  from LinearAlgebraicGroups.Albert.SplitFrameTorus

section LongRoots

open LinearAlgebraicGroups.Specs (Lie)
open LinearAlgebraicGroups.Specs.AdjointRepresentation (constants dualMap reduction scale)
open LinearAlgebraicGroups.Specs.CharacterPairing (adjointWeightVectors)
variable (k : Type) [Field k]

private def spinIntoAlbert (R : TestAlgebra k) :
    Points (fieldSpinGroup k).val.X R →* Points (geometricFiber G k).X R :=
  (integralFibrePoints G.group R).symm.toMonoidHom.comp
    ((spinAlbert G (overIntegers R)).comp (fieldSpinPoints k R).toMonoidHom)

private theorem spinIntoAlbert_injective (R : TestAlgebra k) :
    Function.Injective (spinIntoAlbert G k R) :=
  (integralFibrePoints G.group R).symm.injective.comp
    ((spinAlbert_injective G (overIntegers R)).comp (fieldSpinPoints k R).injective)

private theorem spinIntoAlbert_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (p : Points (fieldSpinGroup k).val.X R) :
    spinIntoAlbert G k S (mapPoints f p) = mapPoints f (spinIntoAlbert G k R p) := by
  let e := integralFibrePoints G.group S
  apply e.injective
  change e (e.symm (spinAlbert G (overIntegers S) (fieldSpinPoints k S (mapPoints f p)))) =
    e (mapPoints f (spinIntoAlbert G k R p))
  rw [MulEquiv.apply_symm_apply]
  have hs := projectIntegralPoint_natural G.group.X f (spinIntoAlbert G k R p)
  change e (mapPoints f (spinIntoAlbert G k R p)) =
    scalarSpec.map (overIntegersMap f).op ≫
      integralFibrePoints G.group R (spinIntoAlbert G k R p) at hs
  rw [hs]
  change _ = scalarSpec.map (overIntegersMap f).op ≫
    integralFibrePoints G.group R ((integralFibrePoints G.group R).symm
      (spinAlbert G (overIntegers R) (fieldSpinPoints k R p)))
  rw [MulEquiv.apply_symm_apply, ← spinAlbert_natural]
  exact congrArg (spinAlbert G (overIntegers S)) (spinPointEquiv_natural k f p)

private theorem fibrePoint_inclusion (T : FrameTorus G) (R : TestAlgebra k)
    (t : Points (T.fibre k).group.X R) :
    integralFibrePoints G.group R (t ≫ (T.fibre k).inclusion.hom.hom) =
      integralFibrePoints diagonalTorus R t ≫ T.inclusion.hom.hom :=
  projectIntegralPoint_comp T.inclusion.hom.hom R t

private theorem fibreCalibratedPoint (T : FrameTorus G) (C : FibreCalibration T k)
    (R : TestAlgebra k) (t : Points (T.fibre k).group.X R) :
    C.points R t = T.points (overIntegers R) (integralFibrePoints diagonalTorus R t) := by
  obtain ⟨z, hz, he⟩ := C.projection R t
  rw [he]
  congr 1
  exact Over.OverMorphism.ext hz

private theorem spinIntoAlbert_torus (C : FibreCalibration (markedTorus G) k)
    (R : TestAlgebra k) (t : Points ((markedTorus G).fibre k).group.X R) :
    spinIntoAlbert G k R ((diagonalGroupPoints k R).symm (C.points R t) ≫
      (diagonalInclusion k).hom.hom) = t ≫ ((markedTorus G).fibre k).inclusion.hom.hom := by
  apply (integralFibrePoints G.group R).injective
  rw [fibrePoint_inclusion]
  change (integralFibrePoints G.group R) ((integralFibrePoints G.group R).symm _) =
    integralFibrePoints diagonalTorus R t ≫ (markedTorus G).inclusion.hom.hom
  rw [MulEquiv.apply_symm_apply]
  change spinAlbert G (overIntegers R) (fieldSpinPoints k R _) =
    integralFibrePoints diagonalTorus R t ≫ (markedTorus G).inclusion.hom.hom
  rw [diagonalInclusion_point, MulEquiv.apply_symm_apply]
  rw [show (markedTorus G).inclusion = torusInclusion G from rfl, torusInclusion_points]
  exact congrArg (fun d => spinAlbert G (overIntegers R) (diagonalLift d))
    (fibreCalibratedPoint G k _ C R t)

private abbrev dualTest (R : TestAlgebra k) := CommAlgCat.of k (DualNumber R)
private abbrev baseTest := CommAlgCat.of k k

private def spinTangentIntoAlbert : Lie k (fieldSpinGroup k).val → Lie k (geometricFiber G k) :=
  fun v => Additive.ofMul ⟨spinIntoAlbert G k (dualTest k (baseTest k)) v.toMul.val, by
    change mapPoints (reduction (baseTest k)) (spinIntoAlbert G k _ v.toMul.val) = 1
    rw [← spinIntoAlbert_natural, show mapPoints (reduction (baseTest k)) v.toMul.val = 1
      from v.toMul.property, map_one]⟩

private theorem spinTangentIntoAlbert_ne_zero (v : Lie k (fieldSpinGroup k).val) (hv : v ≠ 0) :
    spinTangentIntoAlbert G k v ≠ 0 := by
  intro h
  apply hv
  apply Subtype.ext
  apply spinIntoAlbert_injective G k (dualTest k (baseTest k))
  change (spinTangentIntoAlbert G k v).toMul.val = _
  rw [h]
  exact (map_one (spinIntoAlbert G k _)).symm

private theorem spinWeight_transfer (C : FibreCalibration (markedTorus G) k)
    (C₀ : Additive (Character (splitDiagonalGroup k)) ≃ₗ[ℤ] CharacterExponents)
    (ev₀ : ∀ (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R)
      (χ : Character (splitDiagonalGroup k)), characterValue χ R t =
      (Additive.toMul (evaluate (diagonalGroupPoints k R t) (C₀ (Additive.ofMul χ))) : Rˣ).val)
    (χ : Character ((markedTorus G).fibre k).group) (χ₀ : Character (splitDiagonalGroup k))
    (he : C.characters (Additive.ofMul χ) = C₀ (Additive.ofMul χ₀))
    (v : Lie k (fieldSpinGroup k).val) :
    spinTangentIntoAlbert G k v ∈ adjointWeightVectors ((markedTorus G).fibre k) χ ↔
      v ∈ adjointWeightVectors (diagonalSubgroup k) χ₀ := by
  have commute (R : TestAlgebra k) (t : Points ((markedTorus G).fibre k).group.X R)
      (u : Points (splitDiagonalGroup k).X R) (hu : diagonalGroupPoints k R u = C.points R t) :
      let ext := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
      let p := mapPoints ext v.toMul.val
      let g := mapPoints (constants R) (u ≫ (diagonalInclusion k).hom.hom)
      (g * p * g⁻¹ = mapPoints (scale R (characterValue χ₀ R u)) p) ↔
        let q := mapPoints ext (spinTangentIntoAlbert G k v).toMul.val
        let h := mapPoints (constants R) (t ≫ ((markedTorus G).fibre k).inclusion.hom.hom)
        h * q * h⁻¹ = mapPoints (scale R (characterValue χ R t)) q := by
    have hχ : characterValue χ R t = characterValue χ₀ R u := by rw [C.evaluation, ev₀, hu, he]
    have ht : spinIntoAlbert G k R (u ≫ (diagonalInclusion k).hom.hom) =
        t ≫ ((markedTorus G).fibre k).inclusion.hom.hom := by
      rw [← spinIntoAlbert_torus G k C R t, ← hu, MulEquiv.symm_apply_apply]
    dsimp only
    rw [← (spinIntoAlbert_injective G k (dualTest k R)).eq_iff, map_mul, map_mul, map_inv,
      spinIntoAlbert_natural, spinIntoAlbert_natural, ht, spinIntoAlbert_natural,
      spinIntoAlbert_natural, hχ]
    rfl
  constructor
  · intro h R u
    let t := (C.points R).symm (diagonalGroupPoints k R u)
    exact (commute R t u ((C.points R).apply_symm_apply _).symm).mpr (h R t)
  · intro h R t
    let u := (diagonalGroupPoints k R).symm (C.points R t)
    exact (commute R t u ((diagonalGroupPoints k R).apply_symm_apply _)).mp (h R u)

private theorem longWeightRoots
    (C : FibreCalibration (markedTorus G) k) :
    rootCharacters ⊆ (fun χ : Character ((markedTorus G).fibre k).group =>
      C.characters (Additive.ofMul χ)) '' absoluteRoots ((markedTorus G).fibre k) := by
  obtain ⟨C₀, ev₀⟩ := diagonalCharacterCoordinates k
  have hroots := absoluteRoots_coordinates k
    RootData.CharacterPairing.characterValuesDetectCharacters C₀ ev₀
  intro r hr
  obtain ⟨χ₀, hχ₀, hr₀⟩ := hroots.2.2 hr
  change C₀ (Additive.ofMul χ₀) = r at hr₀
  let χ := Additive.toMul (C.characters.symm r)
  have hr₁ : C.characters (Additive.ofMul χ) = r := C.characters.apply_symm_apply r
  have hχ : χ ≠ 1 := by
    intro hχ
    have hz : C₀ (Additive.ofMul χ₀) = 0 := by
      rw [hr₀, ← hr₁, hχ]
      exact C.characters.map_zero
    exact hχ₀.1 (C₀.injective (hz.trans C₀.map_zero.symm))
  obtain ⟨v, hv, hv₀⟩ := hχ₀.2
  exact ⟨χ, ⟨hχ, spinTangentIntoAlbert G k v,
    (spinWeight_transfer G k C C₀ ev₀ χ χ₀ (hr₁.trans hr₀.symm) v).mpr hv,
    spinTangentIntoAlbert_ne_zero G k v hv₀⟩, hr₁⟩

end LongRoots

section TangentMatrices

open LinearAlgebraicGroups.Specs (Lie GroupScheme)
open LinearAlgebraicGroups.Specs.AdjointRepresentation
  (constants dualMap reduction scale)
open LinearAlgebraicGroups.Specs.CharacterPairing (adjointWeightVectors)
open private ModelIndex BlockIndex blockNumber blockVector modelWeight modelBasis
  modelBasis_axis modelBasis_block modelBasis_natural modelBasis_repr_natural torus_action_basis
  modelWeight_block_ne_zero
  from LinearAlgebraicGroups.Albert.SplitFrameTorus
open scoped Matrix DualNumber

variable (k : Type) [Field k]

private def actionMatrix (R : TestAlgebra k) :
    Points (geometricFiber G k).X R →* Matrix ModelIndex ModelIndex R :=
  (LinearMap.toMatrixAlgEquiv (modelBasis (overIntegers R))).toMonoidHom.comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((IntegralSmoothness.geometricFiberAction G k).action R))

private theorem actionMatrix_apply (R : TestAlgebra k)
    (p : Points (geometricFiber G k).X R) (i j : ModelIndex) :
    actionMatrix G k R p i j =
      (modelBasis (overIntegers R)).repr
        ((IntegralSmoothness.geometricFiberAction G k).action R p (modelBasis (overIntegers R) j)) i := by
  change LinearMap.toMatrix (modelBasis _) (modelBasis _) _ i j = _
  rw [LinearMap.toMatrix_apply]
  rfl

private theorem actionMatrix_injective (R : TestAlgebra k) :
    Function.Injective (actionMatrix G k R) :=
  (LinearMap.toMatrixAlgEquiv (modelBasis (overIntegers R))).injective.comp
    (LinearEquiv.toLinearMap_injective.comp ((IntegralSmoothness.geometricFiberAction G k).injective R))

private theorem actionMatrix_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (p : Points (geometricFiber G k).X R) (i j : ModelIndex) :
    actionMatrix G k S (mapPoints f p) i j = f.hom (actionMatrix G k R p i j) := by
  rw [actionMatrix_apply, actionMatrix_apply]
  have h := (IntegralSmoothness.geometricFiberAction G k).natural f p (modelBasis (overIntegers R) j)
  change mapModel (overIntegersMap f).hom.toRingHom
    ((IntegralSmoothness.geometricFiberAction G k).action R p (modelBasis (overIntegers R) j)) =
    (IntegralSmoothness.geometricFiberAction G k).action S (mapPoints f p)
      (mapModel (overIntegersMap f).hom.toRingHom (modelBasis (overIntegers R) j)) at h
  rw [modelBasis_natural (overIntegersMap f)] at h
  rw [← h, modelBasis_repr_natural (overIntegersMap f)]
  rfl

open private geometricFiberPointEquiv geometricFiberPointEquiv_left
  from LinearAlgebraicGroups.Albert.IntegralSmoothness

private theorem actionIntegralPoint (R : TestAlgebra k) (p : Points (geometricFiber G k).X R) :
    geometricFiberPointEquiv G R p = integralFibrePoints G.group R p := by
  apply Over.OverMorphism.ext
  exact geometricFiberPointEquiv_left G R p

private def weightValue (R : Type) [CommRing R] (t : DiagonalPoints R) (r : CharacterExponents) :
    Rˣ := Additive.toMul (evaluate t r)

private theorem actionMatrix_torus (C : FibreCalibration (markedTorus G) k) (R : TestAlgebra k)
    (t : Points ((markedTorus G).fibre k).group.X R) :
    actionMatrix G k R (t ≫ ((markedTorus G).fibre k).inclusion.hom.hom) =
      Matrix.diagonal (fun i => (weightValue R (C.points R t) (modelWeight i) : R)) := by
  classical
  apply Matrix.ext
  intro i j
  rw [actionMatrix_apply]
  change (modelBasis (overIntegers R)).repr
    (G.action (overIntegers R) (geometricFiberPointEquiv G R
      (t ≫ ((markedTorus G).fibre k).inclusion.hom.hom)) (modelBasis (overIntegers R) j)) i = _
  rw [actionIntegralPoint, fibrePoint_inclusion,
    show (markedTorus G).inclusion = torusInclusion G from rfl, torus_action_basis,
    fibreCalibratedPoint G k _ C]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp [weightValue]
    rfl
  · simp [hij, Ne.symm hij]

private def tangentEntries (R : TestAlgebra k) (p : Points (geometricFiber G k).X (dualTest k R)) :
    Matrix ModelIndex ModelIndex R :=
  fun i j => (actionMatrix G k (dualTest k R) p i j).snd

private theorem tangentEntry_fst (R : TestAlgebra k)
    (p : Points (geometricFiber G k).X (dualTest k R)) (hp : mapPoints (reduction R) p = 1)
    (i j : ModelIndex) :
    (actionMatrix G k (dualTest k R) p i j).fst = (1 : Matrix ModelIndex ModelIndex R) i j := by
  change (reduction R).hom (actionMatrix G k (dualTest k R) p i j) = _
  rw [← actionMatrix_natural G k (reduction R) p, hp, map_one]

private theorem tangentEntries_dualMap {R S : TestAlgebra k} (f : R ⟶ S)
    (p : Points (geometricFiber G k).X (dualTest k R)) (i j : ModelIndex) :
    tangentEntries G k S (mapPoints (dualMap f) p) i j =
      f.hom (tangentEntries G k R p i j) := by
  unfold tangentEntries
  rw [actionMatrix_natural]
  rfl

private theorem tangentEntries_scale (R : TestAlgebra k) (a : R)
    (p : Points (geometricFiber G k).X (dualTest k R)) (i j : ModelIndex) :
    tangentEntries G k R (mapPoints (scale R a) p) i j =
      a * tangentEntries G k R p i j := by
  unfold tangentEntries
  rw [actionMatrix_natural]
  rfl


private def entryWeight (i j : ModelIndex) : CharacterExponents := modelWeight i - modelWeight j

private theorem tangentConjugation_entries (C : FibreCalibration (markedTorus G) k)
    (R : TestAlgebra k) (t : Points ((markedTorus G).fibre k).group.X R)
    (p q : Points (geometricFiber G k).X (dualTest k R))
    (hp : mapPoints (reduction R) p = 1) (hq : mapPoints (reduction R) q = 1) :
    let g := mapPoints (constants R) (t ≫ ((markedTorus G).fibre k).inclusion.hom.hom)
    (g * p * g⁻¹ = q) ↔ ∀ i j,
      tangentEntries G k R q i j =
        (weightValue R (C.points R t) (entryWeight i j) : R) *
          tangentEntries G k R p i j := by
  classical
  let g := mapPoints (constants R) (t ≫ ((markedTorus G).fibre k).inclusion.hom.hom)
  let u (i : ModelIndex) := weightValue R (C.points R t) (modelWeight i)
  let a (i : ModelIndex) : DualNumber R := TrivSqZeroExt.inl (u i : R)
  have hg : actionMatrix G k (dualTest k R) g = Matrix.diagonal a := by
    apply Matrix.ext
    intro i j
    rw [actionMatrix_natural, actionMatrix_torus G k C]
    by_cases hij : i = j <;> simp [a, u, hij]
  have hr (i j : ModelIndex) :
      (weightValue R (C.points R t) (entryWeight i j) : R) * (u j : R) = (u i : R) := by
    have h : weightValue R (C.points R t) (entryWeight i j) = u i / u j := by
      unfold weightValue entryWeight
      rw [map_sub]
      rfl
    rw [h]
    exact congrArg Units.val (div_mul_cancel (u i) (u j))
  change (g * p * g⁻¹ = q) ↔ _
  rw [mul_inv_eq_iff_eq_mul, ← (actionMatrix_injective G k (dualTest k R)).eq_iff,
    map_mul, map_mul, hg]
  constructor
  · intro h i j
    have he := congrArg (fun M : Matrix ModelIndex ModelIndex (DualNumber R) => (M i j).snd) h
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    change (u i : R) * tangentEntries G k R p i j + 0 * _ =
      _ * 0 + tangentEntries G k R q i j * (u j : R) at he
    rw [zero_mul, add_zero, mul_zero, zero_add] at he
    apply (u j).isUnit.mul_right_cancel
    calc
      tangentEntries G k R q i j * (u j : R) = (u i : R) * tangentEntries G k R p i j := he.symm
      _ = _ := by rw [← hr i j]; ac_rfl
  · intro h
    apply Matrix.ext
    intro i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    apply TrivSqZeroExt.ext
    · change (u i : R) * (actionMatrix G k (dualTest k R) p i j).fst =
        (actionMatrix G k (dualTest k R) q i j).fst * (u j : R)
      rw [tangentEntry_fst G k R p hp, tangentEntry_fst G k R q hq]
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    · change (u i : R) * tangentEntries G k R p i j + 0 * _ =
        _ * 0 + tangentEntries G k R q i j * (u j : R)
      rw [zero_mul, add_zero, mul_zero, zero_add, h]
      calc
        (u i : R) * tangentEntries G k R p i j =
          ((weightValue R (C.points R t) (entryWeight i j) : R) * (u j : R)) *
            tangentEntries G k R p i j := by rw [hr]
        _ = _ := by ac_rfl

open private map_comp_apply from LinearAlgebraicGroups.Affine.AdjointRepresentation

private theorem scale_reduces {H : GroupScheme k} (R : TestAlgebra k) (a : R)
    (p : Points H.X (dualTest k R)) :
    mapPoints (reduction R) (mapPoints (scale R a) p) = mapPoints (reduction R) p := by
  have h : scale R a ≫ reduction R = reduction R := by
    apply CommAlgCat.hom_ext
    exact AlgHom.ext (fun z => rfl)
  exact (map_comp_apply H (scale R a) (reduction R) p).symm.trans
    (congrArg (fun f => mapPoints f p) h)

private theorem extend_reduces {H : GroupScheme k} {R S : TestAlgebra k} (f : R ⟶ S)
    (p : Points H.X (dualTest k R)) :
    mapPoints (reduction S) (mapPoints (dualMap f) p) =
      mapPoints f (mapPoints (reduction R) p) := by
  have h : dualMap f ≫ reduction S = reduction R ≫ f := by
    apply CommAlgCat.hom_ext
    exact AlgHom.ext (fun z => rfl)
  exact (map_comp_apply H (dualMap f) (reduction S) p).symm.trans
    ((congrArg (fun a => mapPoints a p) h).trans (map_comp_apply H (reduction R) f p))

private theorem tangentWeightEntries (C : FibreCalibration (markedTorus G) k)
    (χ : Character ((markedTorus G).fibre k).group) (v : Lie k (geometricFiber G k)) :
    v ∈ adjointWeightVectors ((markedTorus G).fibre k) χ ↔
      ∀ i j, entryWeight i j ≠ C.characters (Additive.ofMul χ) →
        tangentEntries G k (baseTest k) v.toMul.val i j = 0 := by
  let m := C.characters (Additive.ofMul χ)
  let H := ((markedTorus G).fibre k).group
  let M := tangentEntries G k (baseTest k) v.toMul.val
  have hR (R : TestAlgebra k) (t : Points H.X R) :
      let f : baseTest k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
      let p := mapPoints (dualMap f) v.toMul.val
      let g := mapPoints (constants R) (t ≫ ((markedTorus G).fibre k).inclusion.hom.hom)
      (g * p * g⁻¹ = mapPoints (scale R (characterValue χ R t)) p) ↔
        ∀ i j, characterValue χ R t * algebraMap k R (M i j) =
          (weightValue R (C.points R t) (entryWeight i j) : R) * algebraMap k R (M i j) := by
    intro f p g
    have hp : mapPoints (reduction R) p = 1 := by
      rw [extend_reduces, show mapPoints (reduction (baseTest k)) v.toMul.val = 1
        from v.toMul.property]
      exact (((groupPointsFunctor k).obj (geometricFiber G k)).map f).hom.map_one
    have hq : mapPoints (reduction R) (mapPoints (scale R (characterValue χ R t)) p) = 1 :=
      (scale_reduces k R _ _).trans hp
    refine (tangentConjugation_entries G k C R t p _ hp hq).trans ?_
    simp only [tangentEntries_scale, show ∀ i j, tangentEntries G k R p i j =
      algebraMap k R (M i j) from fun i j => tangentEntries_dualMap G k f v.toMul.val i j]
  constructor
  · intro hv i j hij
    by_contra hM
    apply hij
    let ψ := Additive.toMul (C.characters.symm (entryWeight i j))
    have he (R : TestAlgebra k) (t : Points H.X R) :
        characterValue χ R t = characterValue ψ R t := by
      rw [C.evaluation R t ψ]
      change characterValue χ R t = (weightValue R (C.points R t)
        (C.characters (C.characters.symm (entryWeight i j))) : R)
      rw [LinearEquiv.apply_symm_apply]
      apply ((isUnit_iff_ne_zero.mpr hM).map (algebraMap k R)).mul_right_cancel
      exact (hR R t).mp (hv R t) i j
    have hχ := RootData.CharacterPairing.characterValuesDetectCharacters
      (fibreCharacters (markedTorus G) k).1 he
    rw [hχ]
    exact (C.characters.apply_symm_apply _).symm
  · intro hv R t
    apply (hR R t).mpr
    intro i j
    by_cases hij : entryWeight i j = m
    · rw [C.evaluation, hij]
      rfl
    · have hzero : M i j = 0 := hv i j hij
      rw [hzero, map_zero, mul_zero, mul_zero]


private theorem tangentEntries_mul (R : TestAlgebra k)
    (p q : Points (geometricFiber G k).X (dualTest k R))
    (hp : mapPoints (reduction R) p = 1) (hq : mapPoints (reduction R) q = 1)
    (i j : ModelIndex) :
    tangentEntries G k R (p * q) i j = tangentEntries G k R p i j + tangentEntries G k R q i j := by
  classical
  unfold tangentEntries
  rw [map_mul, Matrix.mul_apply, TrivSqZeroExt.snd_sum]
  simp only [DualNumber.snd_mul, tangentEntry_fst G k R p hp, tangentEntry_fst G k R q hq,
    Finset.sum_add_distrib]
  rw [add_comm]
  simp only [Matrix.one_apply, ite_mul, mul_ite, zero_mul, mul_zero, one_mul,
    mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

open private torusParam torusParam_apply from LinearAlgebraicGroups.Albert.SpinWeights

private theorem unit_zpow_ne_one [IsAlgClosed k] (n : ℤ) (hn : n ≠ 0) :
    ∃ a : kˣ, a ^ n ≠ 1 := by
  classical
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have hy₀ : y ≠ 0 := fun h => hy (by simp [h])
  have hy₁ : y ≠ 1 := fun h => hy (by simp [h])
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (Int.natAbs_pos.mpr hn)
  have hx₀ : x ≠ 0 := by
    intro h
    apply hy₀
    rw [← hx, h, zero_pow (Int.natAbs_pos.mpr hn).ne']
  let a := Units.mk0 x hx₀
  have ha : a ^ n.natAbs ≠ 1 := fun h => hy₁ (hx.symm.trans (congrArg Units.val h))
  refine ⟨a, ?_⟩
  rcases Int.natAbs_eq n with h | h
  · rw [congrArg (fun z : ℤ => a ^ z) h, zpow_natCast]
    exact ha
  · rw [congrArg (fun z : ℤ => a ^ z) h, zpow_neg, zpow_natCast]
    intro h'
    exact ha (inv_eq_one.mp h')

private theorem weightValue_detect [IsAlgClosed k] (r : CharacterExponents) (hr : r ≠ 0) :
    ∃ z : DiagonalPoints k, weightValue k z r ≠ 1 := by
  classical
  by_cases h₀ : r.1 = 0
  · have h₂ : r.2 ≠ 0 := fun h => hr (Prod.ext h₀ h)
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, r.2 i ≠ 0 := by
      by_contra! hh
      exact h₂ (funext hh)
    obtain ⟨x, hx⟩ := unit_zpow_ne_one k (r.2 i) hi
    let u : kˣ × (Fin 3 → kˣ) := (1, fun j => if j = i then x else 1)
    let z := (torusParam k).symm u
    have hz : (scalar z, fun j => scales z j.succ) = u :=
      (torusParam_apply z).symm.trans ((torusParam k).apply_symm_apply u)
    have hvals (j : Fin 3) : scales z j.succ = if j = i then x else 1 :=
      congrFun (congrArg Prod.snd hz) j
    refine ⟨z, ?_⟩
    change scalar z ^ r.1 * (∏ j : Fin 3, scales z j.succ ^ r.2 j) ≠ 1
    have hpow (j : Fin 3) : scales z j.succ ^ r.2 j =
        if j = i then x ^ r.2 j else 1 := by
      rw [hvals]
      by_cases hj : j = i <;> simp [hj]
    simpa only [h₀, zpow_zero, one_mul, hpow, Finset.prod_ite_eq',
      Finset.mem_univ, ite_true] using hx
  · obtain ⟨x, hx⟩ := unit_zpow_ne_one k r.1 h₀
    let u : kˣ × (Fin 3 → kˣ) := (x, fun _ => 1)
    let z := (torusParam k).symm u
    have hz : (scalar z, fun j => scales z j.succ) = u :=
      (torusParam_apply z).symm.trans ((torusParam k).apply_symm_apply u)
    have hval : scalar z = x := congrArg Prod.fst hz
    have hvals (j : Fin 3) : scales z j.succ = 1 := congrFun (congrArg Prod.snd hz) j
    refine ⟨z, ?_⟩
    change scalar z ^ r.1 * (∏ j : Fin 3, scales z j.succ ^ r.2 j) ≠ 1
    simpa only [hval, hvals, one_zpow, Finset.prod_const_one, mul_one] using hx

private theorem weightValue_separates [IsAlgClosed k] (r m : CharacterExponents) (hr : r ≠ m) :
    ∃ z : DiagonalPoints k, (weightValue k z r : k) ≠ (weightValue k z m : k) := by
  obtain ⟨z, hz⟩ := weightValue_detect k (r - m) (sub_ne_zero.mpr hr)
  refine ⟨z, fun he => hz ?_⟩
  have h := Units.ext he
  change Additive.toMul (evaluate z r) = Additive.toMul (evaluate z m) at h
  unfold weightValue
  rw [map_sub]
  change Additive.toMul (evaluate z r) / Additive.toMul (evaluate z m) = 1
  rw [h, div_self']

private theorem tangentConj_reduces (R : TestAlgebra k)
    (p g : Points (geometricFiber G k).X (dualTest k R)) (hp : mapPoints (reduction R) p = 1) :
    mapPoints (reduction R) (g * p * g⁻¹) = 1 := by
  let f := (((groupPointsFunctor k).obj (geometricFiber G k)).map (reduction R)).hom
  change f (g * p * g⁻¹) = 1
  rw [map_mul, map_mul, map_inv, show f p = 1 from hp, mul_one, mul_inv_cancel]

private theorem tangentMul_reduces (R : TestAlgebra k)
    (p q : Points (geometricFiber G k).X (dualTest k R))
    (hp : mapPoints (reduction R) p = 1) (hq : mapPoints (reduction R) q = 1) :
    mapPoints (reduction R) (p * q) = 1 := by
  let f := (((groupPointsFunctor k).obj (geometricFiber G k)).map (reduction R)).hom
  change f (p * q) = 1
  rw [map_mul, show f p = 1 from hp, show f q = 1 from hq, mul_one]

/-- Project to one weight using conjugations by torus points. For each
competing weight choose one point that separates it from the desired weight. -/
private theorem project_tangentEntries [IsAlgClosed k] (C : FibreCalibration (markedTorus G) k)
    (m : CharacterExponents) (v : Lie k (geometricFiber G k)) :
    ∃ w : Lie k (geometricFiber G k),
      (∀ i j, entryWeight i j ≠ m → tangentEntries G k (baseTest k) w.toMul.val i j = 0) ∧
      ∀ i j, entryWeight i j = m →
        tangentEntries G k (baseTest k) w.toMul.val i j =
          tangentEntries G k (baseTest k) v.toMul.val i j := by
  classical
  let R := baseTest k
  have go (s : Finset CharacterExponents) (hm : m ∉ s) :
      ∃ w : Lie k (geometricFiber G k),
        (∀ i j, entryWeight i j ∈ s → tangentEntries G k R w.toMul.val i j = 0) ∧
        ∀ i j, entryWeight i j = m →
          tangentEntries G k R w.toMul.val i j = tangentEntries G k R v.toMul.val i j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨v, fun _ _ h => (Finset.notMem_empty _ h).elim, fun _ _ _ => rfl⟩
    | @insert r s hrs ih =>
      have hr : m ≠ r := fun h => hm (Finset.mem_insert.mpr (Or.inl h))
      have hms : m ∉ s := fun h => hm (Finset.mem_insert.mpr (Or.inr h))
      obtain ⟨w, hw, hv⟩ := ih hms
      obtain ⟨d, hd⟩ := weightValue_separates k m r hr
      let t := (C.points R).symm d
      let g := mapPoints (constants R) (t ≫ ((markedTorus G).fibre k).inclusion.hom.hom)
      let p : Points (geometricFiber G k).X (dualTest k R) := w.toMul.val
      let q := g * p * g⁻¹
      let a (r : CharacterExponents) : k := weightValue k d r
      let c := (a m - a r)⁻¹
      have hp : mapPoints (reduction R) p = 1 := w.toMul.property
      have hq := tangentConj_reduces G k R p g hp
      have he := (tangentConjugation_entries G k C R t p q hp hq).mp rfl
      rw [(C.points R).apply_symm_apply] at he
      let p' := mapPoints (scale R (-(c * a r))) p
      let q' := mapPoints (scale R c) q
      have hp' : mapPoints (reduction R) p' = 1 := (scale_reduces k R _ _).trans hp
      have hq' : mapPoints (reduction R) q' = 1 := (scale_reduces k R _ _).trans hq
      let u : Lie k (geometricFiber G k) :=
        Additive.ofMul ⟨q' * p', tangentMul_reduces G k R q' p' hq' hp'⟩
      have hu (i j : ModelIndex) :
          tangentEntries G k R u.toMul.val i j =
            c * (a (entryWeight i j) - a r) * tangentEntries G k R p i j := by
        change tangentEntries G k R (q' * p') i j = _
        rw [tangentEntries_mul G k R q' p' hq' hp']
        change tangentEntries G k R (mapPoints (scale R c) q) i j +
          tangentEntries G k R (mapPoints (scale R (-(c * a r))) p) i j = _
        rw [tangentEntries_scale, tangentEntries_scale, he]
        change c * (a (entryWeight i j) * tangentEntries G k R p i j) +
          -(c * a r) * tangentEntries G k R p i j = _
        ring
      refine ⟨u, ?_, ?_⟩
      · intro i j hij
        rw [hu]
        rcases Finset.mem_insert.mp hij with hi | hi
        · rw [hi, sub_self, mul_zero, zero_mul]
        · rw [hw i j hi, mul_zero]
      · intro i j hij
        have hne : a m - a r ≠ 0 := sub_ne_zero.mpr hd
        rw [hu, hij, show c * (a m - a r) = 1 from inv_mul_cancel₀ hne, one_mul]
        exact hv i j hij
  let s := (Finset.univ.image (fun ij : ModelIndex × ModelIndex => entryWeight ij.1 ij.2)).erase m
  obtain ⟨w, hw, hm⟩ := go s (Finset.notMem_erase _ _)
  exact ⟨w, fun i j hij =>
    hw i j (Finset.mem_erase.mpr ⟨hij, Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩⟩), hm⟩


private theorem spinTangent_of_frameFixed
    (v : Lie k (geometricFiber G k))
    (hv : ∀ i, G.action (overIntegers (dualTest k (baseTest k)))
      (integralFibrePoints G.group _ v.toMul.val) (frameAxis i) = frameAxis i) :
    ∃ w : Lie k (fieldSpinGroup k).val, spinTangentIntoAlbert G k w = v := by
  let R := dualTest k (baseTest k)
  obtain ⟨a, ha⟩ := spinAlbert_of_fixesFrame G (overIntegers R)
    (integralFibrePoints G.group R v.toMul.val) hv
  let p := (fieldSpinPoints k R).symm a
  have hp : spinIntoAlbert G k R p = v.toMul.val := by
    change (integralFibrePoints G.group R).symm
      (spinAlbert G (overIntegers R) ((fieldSpinPoints k R) ((fieldSpinPoints k R).symm a))) = _
    rw [MulEquiv.apply_symm_apply, ha, MulEquiv.symm_apply_apply]
  have hred : mapPoints (reduction (baseTest k)) p = 1 := by
    apply spinIntoAlbert_injective G k (baseTest k)
    rw [spinIntoAlbert_natural, hp, map_one]
    exact v.toMul.property
  exact ⟨Additive.ofMul ⟨p, hred⟩, Subtype.ext hp⟩

private theorem frameFixed_of_zero_columns (v : Lie k (geometricFiber G k))
    (hv : ∀ j i, tangentEntries G k (baseTest k) v.toMul.val j (.inl i) = 0) :
    ∀ i, G.action (overIntegers (dualTest k (baseTest k)))
      (integralFibrePoints G.group _ v.toMul.val) (frameAxis i) = frameAxis i := by
  intro i
  let R := dualTest k (baseTest k)
  have h (j : ModelIndex) : actionMatrix G k R v.toMul.val j (.inl i) =
      actionMatrix G k R 1 j (.inl i) := by
    apply TrivSqZeroExt.ext
    · rw [tangentEntry_fst G k (baseTest k) v.toMul.val v.toMul.property,
        tangentEntry_fst G k (baseTest k) 1
          ((((groupPointsFunctor k).obj (geometricFiber G k)).map (reduction (baseTest k))).hom.map_one)]
    · change tangentEntries G k (baseTest k) v.toMul.val j (.inl i) = _
      rw [hv, map_one]
      classical
      by_cases hj : j = .inl i <;> simp [Matrix.one_apply, hj]
  apply (modelBasis (overIntegers R)).repr.injective
  apply Finsupp.ext
  intro j
  have h' := h j
  rw [actionMatrix_apply, actionMatrix_apply, map_one, modelBasis_axis] at h'
  change (modelBasis (overIntegers R)).repr
      (G.action (overIntegers R) (geometricFiberPointEquiv G R v.toMul.val) (frameAxis i)) j =
    (modelBasis (overIntegers R)).repr (frameAxis i) j at h'
  rw [actionIntegralPoint] at h'
  exact h'

private theorem shortRoots_eq_range :
    shortRoots = Set.range (fun j : BlockIndex => modelWeight (.inr j)) := by
  classical
  apply Set.Subset.antisymm
  · rintro _ (⟨i, rfl⟩ | ⟨I, rfl⟩)
    · exact ⟨.inr (.inl i), rfl⟩
    · have h : I.card % 2 = 0 ∨ I.card % 2 = 1 := by omega
      rcases h with h | h
      · exact ⟨.inl ⟨I, h⟩, rfl⟩
      · exact ⟨.inr (.inr ⟨I, h⟩), rfl⟩
  · rintro _ ⟨j, rfl⟩
    rcases j with j | j | j
    · exact Or.inr ⟨j.val, rfl⟩
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨j.val, rfl⟩

private theorem roots_upper_bound (C : FibreCalibration (markedTorus G) k)
    {χ : Character ((markedTorus G).fibre k).group}
    (hχ : χ ∈ absoluteRoots ((markedTorus G).fibre k)) :
    C.characters (Additive.ofMul χ) ∈ roots := by
  obtain ⟨hne, v, hv, hv₀⟩ := hχ
  let m := C.characters (Additive.ofMul χ)
  have hm : m ≠ 0 := fun h => hne (C.characters.injective (h.trans C.characters.map_zero.symm))
  have hM := (tangentWeightEntries G k C χ v).mp hv
  by_cases h : ∃ (j : BlockIndex) (i : Fin 3),
      tangentEntries G k (baseTest k) v.toMul.val (.inr j) (.inl i) ≠ 0
  · obtain ⟨j, i, h⟩ := h
    have hj : modelWeight (.inr j) = m := by
      by_contra hne
      apply h
      apply hM
      change modelWeight (.inr j) - 0 ≠ m
      rwa [sub_zero]
    exact Or.inr (shortRoots_eq_range ▸ ⟨j, hj⟩)
  · have hcolumns (j : ModelIndex) (i : Fin 3) :
        tangentEntries G k (baseTest k) v.toMul.val j (.inl i) = 0 := by
      rcases j with j | j
      · apply hM
        change 0 - 0 ≠ m
        simpa only [sub_zero] using hm.symm
      · exact not_not.mp (fun hne => h ⟨j, i, hne⟩)
    obtain ⟨w, hw⟩ := spinTangent_of_frameFixed G k v
      (frameFixed_of_zero_columns G k v hcolumns)
    obtain ⟨C₀, ev₀⟩ := diagonalCharacterCoordinates k
    let ψ := Additive.toMul (C₀.symm m)
    have hψ : C₀ (Additive.ofMul ψ) = m := C₀.apply_symm_apply _
    have hψne : ψ ≠ 1 := fun h => hm (hψ.symm.trans (h ▸ C₀.map_zero))
    have hroots := absoluteRoots_coordinates k
      RootData.CharacterPairing.characterValuesDetectCharacters C₀ ev₀
    have hψroot : ψ ∈ absoluteRoots (diagonalSubgroup k) := ⟨hψne, w, by
      apply (spinWeight_transfer G k C C₀ ev₀ χ ψ hψ.symm w).mp
      rwa [hw], fun hw₀ => by
        apply hv₀
        rw [← hw, hw₀]
        exact Subtype.ext ((spinIntoAlbert G k _).map_one)⟩
    have hlong := hroots.1 hψroot
    change C₀ (Additive.ofMul ψ) ∈ rootCharacters at hlong
    rw [hψ] at hlong
    exact Or.inl hlong

open private shortFamily_natural mapModel_direction from LinearAlgebraicGroups.Albert.ShortDirections
open private splitAction_ext blockEmbedding
  from LinearAlgebraicGroups.Albert.SplitFrameTorus

private theorem direction_detects_block (j : BlockIndex) :
    ∃ l : DirectionIndex, (modelBasis (overIntegers (baseTest k))).repr
        (singleBlockCoordinates (blockNumber j) (direction k l)) (.inr j) ≠ 0 := by
  by_contra! h
  let R := overIntegers (baseTest k)
  let L : Composition.Zorn k →ₗ[k] k :=
    ((Finsupp.lapply (.inr j)).comp (modelBasis R).repr.toLinearMap).comp
      (blockEmbedding R (blockNumber j))
  have hz : L = 0 := by
    apply (IntegralZornDirections.directionBasis k).ext
    intro l
    rw [IntegralZornDirections.directionBasis_apply]
    exact h l
  have hu : L (blockVector R j) = 1 := by
    change (modelBasis R).repr (singleBlockCoordinates (blockNumber j) (blockVector R j)) (.inr j) = 1
    rw [← modelBasis_block, Module.Basis.repr_self, Finsupp.single_eq_same]
  have := congrArg (fun f : Composition.Zorn k →ₗ[k] k => f (blockVector R j)) hz
  exact zero_ne_one (this.symm.trans hu)

private theorem short_tangent_evaluates (j : BlockIndex) :
    ∃ v : Lie k (geometricFiber G k),
      tangentEntries G k (baseTest k) v.toMul.val (.inr j) (.inl (cyclicNext (blockNumber j))) ≠ 0 := by
  obtain ⟨l, hl⟩ := direction_detects_block k j
  let i := blockNumber j
  let R := baseTest k
  let D := dualTest k R
  let b := shortElement (DualNumber k) (i, l) ε
  have hb : b.val ∈ {g | IdempotentSpecification.IsSplitAutomorphism g} :=
    (mem_splitAutomorphisms _).mp b.property
  rw [← G.image (overIntegers D)] at hb
  obtain ⟨p, hp⟩ := hb
  let q := (integralFibrePoints G.group D).symm p
  have hq : geometricFiberPointEquiv G D q = p := by
    rw [actionIntegralPoint, MulEquiv.apply_symm_apply]
  have hred : mapPoints (reduction R) q = 1 := by
    let f := overIntegersMap (reduction R)
    apply (integralFibrePoints G.group R).injective
    rw [map_one]
    have hn := projectIntegralPoint_natural G.group.X (reduction R) q
    change integralFibrePoints G.group R (mapPoints (reduction R) q) =
      scalarSpec.map f.op ≫ integralFibrePoints G.group D q at hn
    rw [hn, MulEquiv.apply_symm_apply]
    apply G.injective (overIntegers R)
    rw [map_one]
    apply splitAction_ext f
    intro x
    rw [← G.natural, hp]
    change mapModel f.hom.toRingHom
      (ShortDirections.shortFamily (DualNumber k) i l (Multiplicative.ofAdd ε) x) =
      mapModel f.hom.toRingHom x
    rw [shortFamily_natural]
    change (ShortDirections.shortFamily k i l 1) (mapModel f.hom.toRingHom x) = _
    rw [map_one]
    rfl
  refine ⟨Additive.ofMul ⟨q, hred⟩, ?_⟩
  change tangentEntries G k R q (.inr j) (.inl (cyclicNext i)) ≠ 0
  unfold tangentEntries
  rw [actionMatrix_apply, modelBasis_axis]
  change ((modelBasis (overIntegers D)).repr
      (G.action (overIntegers D) (geometricFiberPointEquiv G D q) (frameAxis (cyclicNext i)))
        (.inr j)).snd ≠ 0
  rw [hq, hp]
  have hb' : b.val (frameAxis (cyclicNext i)) = frameAxis (cyclicNext i) +
      ε • singleBlockCoordinates i (direction (DualNumber k) l) :=
    (integralShortFamilies.evaluates (DualNumber k) i l ε).2.1
  have hAxis : (modelBasis (overIntegers D)).repr (frameAxis (cyclicNext i)) (.inr j) = 0 := by
    calc
      _ = (modelBasis (overIntegers D)).repr (modelBasis (overIntegers D) (.inl (cyclicNext i)))
          (.inr j) := congrArg (fun x => (modelBasis (overIntegers D)).repr x (.inr j))
        (modelBasis_axis (overIntegers D) (cyclicNext i)).symm
      _ = _ := by simp [Module.Basis.repr_self]
  rw [hb', map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, hAxis,
    zero_add, smul_eq_mul, DualNumber.snd_mul]
  change 0 * _ + 1 * ((modelBasis (overIntegers D)).repr
    (singleBlockCoordinates i (direction (DualNumber k) l)) (.inr j)).fst ≠ 0
  rw [zero_mul, zero_add, one_mul]
  let f := overIntegersMap (reduction R)
  have he := modelBasis_repr_natural f (singleBlockCoordinates i (direction (DualNumber k) l)) (.inr j)
  rw [mapModel_direction] at he
  change (modelBasis (overIntegers R)).repr
      (singleBlockCoordinates i (direction k l)) (.inr j) =
    ((modelBasis (overIntegers D)).repr
      (singleBlockCoordinates i (direction (DualNumber k) l)) (.inr j)).fst at he
  rw [← he]
  exact hl

private theorem shortWeightRoots [IsAlgClosed k] (C : FibreCalibration (markedTorus G) k) :
    shortRoots ⊆ (fun χ : Character ((markedTorus G).fibre k).group =>
      C.characters (Additive.ofMul χ)) '' absoluteRoots ((markedTorus G).fibre k) := by
  rw [shortRoots_eq_range]
  rintro _ ⟨j, rfl⟩
  let m := modelWeight (.inr j)
  let χ := Additive.toMul (C.characters.symm m)
  have hχ : C.characters (Additive.ofMul χ) = m := C.characters.apply_symm_apply _
  have hne : χ ≠ 1 := by
    intro h
    apply modelWeight_block_ne_zero j
    change m = 0
    rw [← hχ, h]
    exact C.characters.map_zero
  obtain ⟨v, hv⟩ := short_tangent_evaluates G k j
  obtain ⟨w, hw, hkeep⟩ := project_tangentEntries G k C m v
  refine ⟨χ, ⟨hne, w, (tangentWeightEntries G k C χ w).mpr (by rwa [hχ]), ?_⟩, hχ⟩
  intro hz
  have hj : entryWeight (.inr j) (.inl (cyclicNext (blockNumber j))) = m := sub_zero _
  have he := hkeep (.inr j) (.inl (cyclicNext (blockNumber j))) hj
  change tangentEntries G k (baseTest k) w.toMul.val _ _ = _ at he
  rw [hz] at he
  change (actionMatrix G k (dualTest k (baseTest k)) 1 _ _).snd = _ at he
  rw [map_one] at he
  classical
  simp only [Matrix.one_apply, Sum.inr_ne_inl, ite_false, TrivSqZeroExt.snd_zero] at he
  exact hv he.symm

private theorem fibreWeights_marked (k : Type) [Field k] [IsAlgClosed k]
    (hmax : IsGeometricallyMaximal ((markedTorus G).fibre k)) :
    FibreWeights (markedTorus G) k := by
  obtain ⟨hs, ⟨C⟩⟩ := fibreCharacters (markedTorus G) k
  refine ⟨hs, hmax, C, ?_, ?_, ?_⟩
  · intro χ hχ
    exact roots_upper_bound G k C hχ
  · intro χ _ ψ _ h
    exact C.characters.injective h
  · rintro r (hlong | hshort)
    · exact longWeightRoots G k C hlong
    · exact shortWeightRoots G k C hshort

end TangentMatrices

open LinearAlgebraicGroups.Specs.SchemeCentre (rootLattice)
open LinearAlgebraicGroups.Specs.DiagonalizableGroups
  (groupAlgebra groupAlgebraMap diagonalClosedInclusion)
open LinearAlgebraicGroups.Specs (ClosedSubgroup)
open scoped MonoidAlgebra

private def longIndexPairs : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter (fun ij => ij.1 ≠ ij.2)

private def longRootList : Finset CharacterExponents :=
  longIndexPairs.image (fun ij => vectorPullback (coordinate ij.1 + coordinate ij.2)) ∪
    longIndexPairs.image (fun ij => vectorPullback (coordinate ij.1 - coordinate ij.2)) ∪
    longIndexPairs.image (fun ij => vectorPullback (-coordinate ij.1 - coordinate ij.2))

private def vectorRootList : Finset CharacterExponents := Finset.univ.image vectorWeight

private def halfSumRootList : Finset CharacterExponents := Finset.univ.image exteriorWeight

private theorem coe_longRootList : (longRootList : Set CharacterExponents) = rootCharacters := by
  ext x
  simp only [longRootList, longIndexPairs, Finset.mem_coe, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ((⟨i, j, h, rfl⟩ | ⟨i, j, h, rfl⟩) | ⟨i, j, h, rfl⟩)
    · exact ⟨_, ⟨i, j, h, Or.inl rfl⟩, rfl⟩
    · exact ⟨_, ⟨i, j, h, Or.inr (Or.inl rfl)⟩, rfl⟩
    · exact ⟨_, ⟨i, j, h, Or.inr (Or.inr rfl)⟩, rfl⟩
  · rintro ⟨_, ⟨i, j, h, hi | hi | hi⟩, rfl⟩
    · exact Or.inl (Or.inl ⟨i, j, h, (congrArg vectorPullback hi).symm⟩)
    · exact Or.inl (Or.inr ⟨i, j, h, (congrArg vectorPullback hi).symm⟩)
    · exact Or.inr ⟨i, j, h, (congrArg vectorPullback hi).symm⟩

set_option maxRecDepth 12000 in
theorem rootCardinalities : RootCardinalities := by
  have hv : (vectorRootList : Set CharacterExponents) = Set.range vectorWeight := by
    simp [vectorRootList]
  have hh : (halfSumRootList : Set CharacterExponents) = Set.range exteriorWeight := by
    simp [halfSumRootList]
  have h : (↑(longRootList ∪ (vectorRootList ∪ halfSumRootList)) : Set CharacterExponents) = roots := by
    rw [Finset.coe_union, Finset.coe_union, coe_longRootList, hv, hh]
    rfl
  unfold RootCardinalities
  rw [← h, ← coe_longRootList, ← hv, ← hh]
  simp only [Set.ncard_coe_finset]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem roots_span : RootsSpan := by
  change Submodule.span ℤ roots = ⊤
  have he (i : Fin 4) : epsilon i ∈ roots :=
    Or.inr (Or.inl ⟨Sum.inl i, rfl⟩)
  have hhalf : -halfSum ∈ roots := Or.inr (Or.inr ⟨∅, by simp [exteriorWeight]⟩)
  apply top_unique
  rw [← SpinWeights.characterGenerators]
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with hx | ⟨i, rfl⟩
  · rw [hx]
    exact neg_mem_iff.mp (Submodule.subset_span hhalf)
  · exact Submodule.subset_span (he _)

private theorem rootLattice_eq_top {k : Type} [Field k] (T : FrameTorus G)
    (C : FibreCalibration T k)
    (h : Set.SurjOn (fun χ : Character (T.fibre k).group =>
      C.characters (Additive.ofMul χ)) (absoluteRoots (T.fibre k)) roots) :
    rootLattice (T.fibre k) = ⊤ := by
  let H := T.fibre k
  let L := (rootLattice H).toAddSubgroup.toIntSubmodule
  have hs : roots ⊆ L.map C.characters.toLinearMap := by
    intro r hr
    obtain ⟨χ, ha, hχ⟩ := h hr
    refine ⟨Additive.ofMul χ, ?_, hχ⟩
    change χ ∈ rootLattice H
    exact Subgroup.subset_closure ha
  have htop : L.map C.characters.toLinearMap = ⊤ :=
    top_unique ((show Submodule.span ℤ roots = ⊤ from roots_span) ▸ Submodule.span_le.mpr hs)
  apply top_unique
  intro χ _
  have hh : C.characters (Additive.ofMul χ) ∈ L.map C.characters.toLinearMap :=
    htop ▸ Submodule.mem_top
  obtain ⟨x, hx, hex⟩ := hh
  have hχ : x = Additive.ofMul χ := C.characters.injective hex
  change Additive.ofMul χ ∈ L
  exact hχ ▸ hx

private theorem semisimple_and_centre_of_weights {k : Type} [Field k]
    (T : FrameTorus G) (hw : FibreWeights T k) (hG : IsReductive (algebraicFiber G k)) :
    IsSemisimple (algebraicFiber G k) ∧ HasTrivialCentre (geometricFiber G k) := by
  obtain ⟨hs, hm, C, hr⟩ := hw
  let H := T.fibre k
  let A := algebraicFiber G k
  have hL : rootLattice H = ⊤ := rootLattice_eq_top G T C hr.2.2
  obtain ⟨_, e, _, hcl, hz, _⟩ := RootData.SchemeCentre.schemeCentre A hG H hs hm
  let Q := Character H.group ⧸ rootLattice H
  let Z : ClosedSubgroup A.val :=
    ⟨specGroup (groupAlgebra k Q), diagonalClosedInclusion k (rootLattice H) ≫ e.hom ≫ H.inclusion,
      hcl⟩
  have hZ : LinearAlgebraicGroups.Specs.CentralTorus.IsSchemeCentre Z := hz
  have : Subsingleton Q := QuotientGroup.subsingleton_iff.mpr hL
  have hiso : IsIso Z.group.X.hom := by
    let f : MonoidAlgebra k Q ≃ₐ[k] k := MonoidAlgebra.uniqueAlgEquiv k Q
    have hf : algebraMap k (MonoidAlgebra k Q) = f.symm.toRingHom := by
      apply RingHom.ext
      intro x
      exact (f.symm.commutes x).symm
    change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k Q))))
    rw [hf]
    exact Scheme.Spec.map_isIso f.symm.toRingEquiv.toCommRingCatIso.hom.op
  have hfinite : IsFinite Z.group.X.hom := by
    let : IsIso Z.group.X.hom := hiso
    infer_instance
  refine ⟨(Reductive.CentralDerived.semisimpleIffFiniteCentre A hG Z hZ).mpr hfinite, ?_⟩
  intro X z central
  have hz' : Centralizes (𝟙 A.val) z :=
    (centralizes_iff _ _).mpr fun Y f g => by
      rw [Grp.id_hom_hom, Category.comp_id]
      exact central Y f g
  obtain ⟨y, hy⟩ := (hZ X z).mp hz'
  have hyone : y = 1 := by
    apply Over.OverMorphism.ext
    exact (cancel_mono Z.group.X.hom).mp
      ((Over.w y).trans (Over.w (1 : X ⟶ Z.group.X)).symm)
  rw [← hy, hyone, MonObj.one_comp]

open private markedTorus_stabilizer markedTorus_geometricallyMaximal
  from LinearAlgebraicGroups.Albert.SplitFrameTorus

theorem splitAlbertAdjointWeights : SplitAlbertAdjointWeightsSpecification.Statement := by
  intro P G hG
  refine ⟨markedTorus G, markedTorus_stabilizer G, ?_, integralCentre P G⟩
  intro k _ _
  have hw := fibreWeights_marked G k (markedTorus_geometricallyMaximal k G)
  exact ⟨hw, semisimple_and_centre_of_weights G _ hw (hG k)⟩

end

end LinearAlgebraicGroups.Albert.SplitAlbertAdjointWeights
