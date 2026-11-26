import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusCentralizer
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.RootData.CharacterPairing

open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup Lie IdentityLieStructure)
open Specs.CharacterDescent (Character Cocharacter StandardLattice compositionPairing)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters integerGenerator)
open Specs.GeometricRadicals (IsSplitTorus IsTorus)
open Specs.AdjointRepresentation
open CocharacterDynamics (unitCoordinates unitPoint cocharacterPoint)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

abbrev pairing := @Specs.CharacterPairing.pairing
abbrev adjointWeightSpace := @Specs.CharacterPairing.adjointWeightSpace
abbrev absoluteRoots := @Specs.CharacterPairing.absoluteRoots

open Specs.CharacterPairing (powerMorphism characterValue adjointWeightVectors)
open private integerHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private splitGroupHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private isCommMonObj_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras

local notation "Gm" => specGroup (groupAlgebra k IntegerCharacters)

private def integerExponent : IntegerCharacters.{u} ≃ ℤ where
  toFun a := Multiplicative.toAdd a.down
  invFun n := ⟨Multiplicative.ofAdd n⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem integerExponent_zpow (n : ℤ) :
    integerExponent (integerGenerator ^ n : IntegerCharacters.{u}) = n := by
  change n • (1 : ℤ) = n
  simp

private def powerEquiv : ℤ ≃ Character Gm :=
  integerExponent.symm.trans ((integerHomEquiv IntegerCharacters).toEquiv.trans
    (splitGroupHomEquiv (k := k) IntegerCharacters IntegerCharacters).toEquiv)

private theorem powerEquiv_apply (n : ℤ) : (powerEquiv (k := k)) n = powerMorphism n := by
  have h : integerExponent.{u}.symm n = (integerGenerator ^ n : IntegerCharacters.{u}) :=
    integerExponent.{u}.symm_apply_eq.mpr (integerExponent_zpow.{u} n).symm
  change specGroupMap (groupAlgebraMap k
    ((zpowersHom IntegerCharacters (integerExponent.symm n)).comp MulEquiv.ulift.toMonoidHom)) = _
  rw [h]
  rfl

private theorem pairing_eq_iff {T : GroupScheme k} (χ : Character T) (cochar : Cocharacter T)
    (n : ℤ) :
    compositionPairing T χ cochar = powerMorphism n ↔ pairing T χ cochar = n := by
  have hb : Function.Bijective (powerMorphism (k := k)) := by
    rw [show powerMorphism (k := k) = powerEquiv (k := k) from
      funext fun a => (powerEquiv_apply a).symm]
    exact (powerEquiv (k := k)).bijective
  constructor
  · intro h
    change Function.invFun (powerMorphism (k := k)) (compositionPairing T χ cochar) = n
    rw [h, Function.leftInverse_invFun hb.injective]
  · intro h
    exact ((Function.rightInverse_invFun hb.surjective) (compositionPairing T χ cochar)).symm.trans
      (congrArg (powerMorphism (k := k)) h)

private def algebraPoint {M : Type u} [CommGroup M] (R : TestAlgebra k)
    (f : MonoidAlgebra k M →ₐ[k] R) :
    GroupPoints (specGroup (groupAlgebra k M)) R :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private theorem characterValue_monomial {M : Type u} [CommGroup M]
    (R : TestAlgebra k) (f : MonoidAlgebra k M →ₐ[k] R) (m : M) :
    characterValue
      (specGroupMap (groupAlgebraMap k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)))
      R (algebraPoint R f) = f (MonoidAlgebra.single m 1) := by
  let h := MonoidAlgebra.mapDomainBialgHom k
    ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      ((testSpec k).map (CommAlgCat.ofHom f).op ≫
        (testSpec k).map (CommAlgCat.ofHom h.toAlgHom).op)).unop.hom
      (MonoidAlgebra.single integerGenerator 1) = _
  rw [← Functor.map_comp, Functor.FullyFaithful.preimage_map]
  change f (h (MonoidAlgebra.single integerGenerator 1)) = _
  rw [MonoidAlgebra.mapDomainBialgHom_single]
  change f (MonoidAlgebra.single (m ^ (1 : ℤ)) 1) = _
  rw [zpow_one]

theorem characterPairingComposition : Specs.CharacterPairing.CharacterPairingComposition.{u} := by
  intro k _ T χ cochar
  refine ⟨pairing_eq_iff χ cochar, ?_⟩
  intro R t
  let n := pairing T χ cochar
  have hcomp : cochar ≫ χ = powerMorphism n := (pairing_eq_iff χ cochar n).mpr rfl
  have heval : characterValue χ R (cocharacterPoint cochar R t) =
      characterValue (cochar ≫ χ) R (unitPoint R t) := by
    unfold characterValue
    rfl
  rw [heval, hcomp]
  change characterValue (powerMorphism n) R (algebraPoint R (unitCoordinates R t)) = _
  rw [powerMorphism, characterValue_monomial]
  rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  change ((t ^ integerExponent (integerGenerator ^ n : IntegerCharacters.{u}) : Rˣ) : R) = _
  rw [integerExponent_zpow]

private theorem splitPresentation {T : GroupScheme k} (hT : IsSplitTorus T) :
    ∃ r : ℕ, Nonempty (specGroup (groupAlgebra k (StandardLattice.{u} r)) ≅ T) := by
  obtain ⟨r, ⟨i⟩⟩ := hT
  obtain ⟨j⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  exact ⟨r, ⟨j ≪≫ i.symm⟩⟩

private def charactersOfIso {A B : GroupScheme k} (i : A ≅ B) :
    Character A ≃* Character B where
  toFun f := i.inv ≫ f
  invFun f := i.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_mul' f g := by
    apply Grp.hom_ext
    exact MonObj.comp_mul _ _ _

private def cocharactersOfIso {A B : GroupScheme k} [IsCommMonObj A.X] [IsCommMonObj B.X]
    (i : A ≅ B) : Cocharacter A ≃* Cocharacter B where
  toFun f := f ≫ i.hom
  invFun f := f ≫ i.inv
  left_inv f := by simp
  right_inv f := by simp
  map_mul' f g := by
    apply Grp.hom_ext
    exact MonObj.mul_comp _ _ _

private def latticeCoordinates (r : ℕ) :
    Additive (StandardLattice.{u} r) ≃ₗ[ℤ] (Fin r → ℤ) :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun x i => integerExponent (x.toMul i)
      invFun := fun a => Additive.ofMul (fun i => integerExponent.symm (a i))
      left_inv := by intro x; funext i; exact integerExponent.symm_apply_apply _
      right_inv := by intro x; funext i; exact integerExponent.apply_symm_apply _
      map_add' := by intros; rfl }

private def homToDual (M : Type u) [CommGroup M] :
    Additive (M →* IntegerCharacters.{u}) ≃ₗ[ℤ] Module.Dual ℤ (Additive M) :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun f => AddMonoidHom.toIntLinearMap
        { toFun := fun x => integerExponent.{u} (f.toMul x.toMul)
          map_zero' := by change integerExponent.{u} (f.toMul 1) = _; rw [map_one]; rfl
          map_add' := by
            intro x y
            change integerExponent.{u} (f.toMul (x.toMul * y.toMul)) = _
            rw [map_mul]
            rfl }
      invFun := fun g => Additive.ofMul
        { toFun := fun x => integerExponent.{u}.symm (g (Additive.ofMul x))
          map_one' := by change integerExponent.{u}.symm (g 0) = _; rw [map_zero]; rfl
          map_mul' := by
            intro x y
            change integerExponent.{u}.symm (g (Additive.ofMul x + Additive.ofMul y)) = _
            rw [map_add]
            rfl }
      left_inv := by
        intro f
        change (show M →* IntegerCharacters from _) = f.toMul
        apply MonoidHom.ext
        intro x
        exact integerExponent.{u}.symm_apply_apply _
      right_inv := by
        intro g
        ext x
        exact integerExponent.{u}.apply_symm_apply _
      map_add' := by intros; ext; rfl }

theorem perfectCharacterPairing : Specs.CharacterPairing.PerfectCharacterPairing.{u} := by
  intro k _ T hT
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  have hcomm : IsCommMonObj T.X := isCommMonObj_of_groupIso i inferInstance
  refine ⟨hcomm, ?_⟩
  letI := hcomm
  obtain ⟨χ, cochar, _, _, h⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) r
  let c : Additive M ≃ₗ[ℤ] Additive (Character T) :=
    (χ.trans (charactersOfIso i)).toAdditive.toIntLinearEquiv
  let d : Additive (M →* IntegerCharacters.{u}) ≃ₗ[ℤ] Additive (Cocharacter T) :=
    (cochar.trans (cocharactersOfIso i)).toAdditive.toIntLinearEquiv
  let e := d.symm.trans (homToDual M)
  letI : Module.Free ℤ (Additive M) := Module.Free.of_equiv (latticeCoordinates r).symm
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates r).symm
  let dualBasis := ((Pi.basisFun ℤ (Fin r)).map (latticeCoordinates r).symm).dualBasis
  letI : Module.Free ℤ (Module.Dual ℤ (Additive M)) := Module.Free.of_basis dualBasis
  letI : Module.Finite ℤ (Module.Dual ℤ (Additive M)) := Module.Finite.of_basis dualBasis
  refine ⟨Module.Free.of_equiv c, Module.Finite.equiv c,
    Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm,
    (Module.Dual.eval ℤ (Additive M)).compl₁₂ c.symm e, inferInstance, ?_⟩
  intro x y
  obtain ⟨m, rfl⟩ := (χ.trans (charactersOfIso i)).surjective x
  obtain ⟨f, rfl⟩ := (cochar.trans (cocharactersOfIso i)).surjective y
  have hc : c.symm (Additive.ofMul ((χ.trans (charactersOfIso i)) m)) = Additive.ofMul m :=
    c.symm_apply_apply _
  have hd : d.symm (Additive.ofMul ((cochar.trans (cocharactersOfIso i)) f)) = Additive.ofMul f :=
    d.symm_apply_apply _
  change (homToDual M (d.symm _)) (c.symm _) = _
  rw [hc, hd]
  symm
  apply (pairing_eq_iff _ _ _).mp
  change (cochar f ≫ i.hom) ≫ (i.inv ≫ χ m) = powerMorphism (integerExponent (f m))
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hf : integerGenerator ^ integerExponent (f m) = f m :=
    (integerExponent.apply_eq_iff_eq).mp (integerExponent_zpow _)
  rw [powerMorphism, hf]
  exact h m f

private def extendCoordinates {G : GroupScheme k} {J : Type u} [Fintype J]
    [AddCommGroup (Lie k G)] [Module k (Lie k G)] (b : Module.Basis J k (Lie k G))
    (R : TestAlgebra k) : Lie k G →ₗ[k] (J → R) :=
  (LinearMap.pi fun i => (Algebra.linearMap k R).comp (LinearMap.proj i)).comp
    b.equivFun.toLinearMap

private theorem adjointWeightVectors_iff {G : GroupScheme k} {J : Type u}
    [Fintype J] [DecidableEq J] [AddCommGroup (Lie k G)] [Module k (Lie k G)]
    {b : Module.Basis J k (Lie k G)} (C : TangentCoordinates G J b)
    {L : GroupScheme k} (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k J)
    (Ad : G ⟶ L)
    (hAd : ∀ (R : TestAlgebra k) (g : GroupPoints G R) (v : J → R),
      let M := (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g)
      (C.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (C.equiv R v))
    (T : ClosedSubgroup G) (χ : Character T.group) (v : Lie k G) :
    v ∈ adjointWeightVectors T χ ↔ ∀ (R : TestAlgebra k) (t : GroupPoints T.group R),
      let M := (l.hom.app R).hom (((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app R t)
      M.val *ᵥ extendCoordinates b R v = characterValue χ R t • extendCoordinates b R v := by
  unfold adjointWeightVectors
  change (∀ R t, _) ↔ _
  apply forall_congr'
  intro R
  apply forall_congr'
  intro t
  have hbase : (C.equiv R (extendCoordinates b R v)).toMul.val =
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val := by
    exact (C.naturality (CommAlgCat.ofHom (Algebra.ofId k R)) (b.equivFun v)).trans
      (congrArg (mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R)))) (C.at_base v))
  change mapPoints (constants R) (t ≫ T.inclusion.hom.hom) *
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val *
        (mapPoints (constants R) (t ≫ T.inclusion.hom.hom))⁻¹ =
      mapPoints (scale R (characterValue χ R t))
        (mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val) ↔ _
  rw [← hbase, ← C.smul R (characterValue χ R t)]
  change conjugate (t ≫ T.inclusion.hom.hom) (C.equiv R (extendCoordinates b R v)) = _ ↔ _
  rw [← hAd R (t ≫ T.inclusion.hom.hom)]
  have hi : Function.Injective (fun w : J → R => (C.equiv R w).toMul.val) :=
    Subtype.val_injective.comp (C.equiv R).injective
  rw [hi.eq_iff]
  simp only [Functor.map_comp, NatTrans.comp_app]
  rfl

theorem adjointWeightSpaceVectors : Specs.CharacterPairing.AdjointWeightSpaceVectors.{u} := by
  classical
  intro k _ G T s χ
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, b, C, L, l, Ad, hAd, _, _⟩ := adjointRepresentation k G s
  let equiv := adjointWeightVectors_iff C l Ad hAd T χ
  let W : Submodule k (Lie k G.val) :=
    { carrier := adjointWeightVectors T χ
      zero_mem' := by
        apply (equiv _).mpr
        intro R t
        simp
      add_mem' := by
        intro x y hx hy
        apply (equiv _).mpr
        intro R t
        have a := (equiv x).mp hx R t
        have b := (equiv y).mp hy R t
        simp only [map_add, Matrix.mulVec_add, smul_add, a, b]
      smul_mem' := by
        intro z x hx
        apply (equiv _).mpr
        intro R t
        have h := (equiv x).mp hx R t
        let M := (l.hom.app R).hom (((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app R t)
        let F := (Matrix.mulVecLin M.val).restrictScalars k
        have h' : F (extendCoordinates b R x) = characterValue χ R t • extendCoordinates b R x := h
        change F (extendCoordinates b R _) = characterValue χ R t • extendCoordinates b R _
        rw [(extendCoordinates b R).map_smul z x, F.map_smul, h', smul_comm] }
  change (Submodule.span k (W : Set (Lie k G.val)) : Set (Lie k G.val)) = W
  rw [Submodule.span_eq]

private theorem canonicalZero_eq {G : GroupScheme k} (s : IdentityLieStructure G) :
    (0 : Lie k G) = @Zero.zero _ s.lieRing.toAddCommGroup.toZero :=
  (congrArg (fun i : AddGroup (Lie k G) => @Zero.zero _ i.toZero) s.group_law).symm

theorem absoluteRootWeights : Specs.CharacterPairing.AbsoluteRootWeights.{u} := by
  intro k _ G T s χ
  letI := s.lieRing
  letI := s.lieAlgebra
  rw [Submodule.ne_bot_iff]
  change (χ ≠ 1 ∧ ∃ v ∈ adjointWeightVectors T χ, v ≠ _) ↔
    (χ ≠ 1 ∧ ∃ v ∈ (adjointWeightSpace T χ s : Set (Lie k G.val)), v ≠ _)
  rw [adjointWeightSpaceVectors G T s χ]
  refine and_congr_right fun _ => exists_congr fun v => and_congr_right fun _ => ?_
  exact not_congr (Iff.of_eq (congrArg (fun z : Lie k G.val => v = z) (canonicalZero_eq s)))

private theorem universalCharacterValue {T : GroupScheme k} {r : ℕ}
    (i : specGroup (groupAlgebra k (StandardLattice.{u} r)) ≅ T)
    (χ : StandardLattice.{u} r ≃* Character (specGroup (groupAlgebra k (StandardLattice.{u} r))))
    (hχ : ∀ m, χ m = specGroupMap (groupAlgebraMap k
      ((zpowersHom _ m).comp MulEquiv.ulift.toMonoidHom)))
    (m : StandardLattice.{u} r) :
    let A := CommAlgCat.of k (MonoidAlgebra k (StandardLattice.{u} r))
    let t : GroupPoints T A :=
      algebraPoint A (AlgHom.id k (MonoidAlgebra k (StandardLattice.{u} r))) ≫ i.hom.hom.hom
    characterValue ((charactersOfIso i) (χ m)) A t = MonoidAlgebra.single m 1 := by
  dsimp only
  have he (R : TestAlgebra k) (t : GroupPoints (specGroup (groupAlgebra k (StandardLattice.{u} r))) R) :
      characterValue ((charactersOfIso i) (χ m)) R (t ≫ i.hom.hom.hom) =
        characterValue (χ m) R t := by
    unfold characterValue
    have heq : (t ≫ i.hom.hom.hom) ≫ ((charactersOfIso i) (χ m)).hom.hom =
        t ≫ (χ m).hom.hom := by
      change (t ≫ i.hom.hom.hom) ≫ i.inv.hom.hom ≫ (χ m).hom.hom = t ≫ (χ m).hom.hom
      rw [Category.assoc]
      have h : i.hom.hom.hom ≫ i.inv.hom.hom = 𝟙 _ :=
        (Grp.forget _).congr_map i.hom_inv_id
      rw [← Category.assoc (f := i.hom.hom.hom), h, Category.id_comp]
    dsimp only
    rw [heq]
  rw [he, hχ, characterValue_monomial]
  rfl

theorem finiteAbsoluteRoots : Specs.CharacterPairing.FiniteAbsoluteRoots.{u} := by
  classical
  intro k _ G T hT
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) r
  obtain ⟨s⟩ := identityLieBracket k G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, b, C, L, l, Ad, hAd, _, _⟩ := adjointRepresentation k G s
  let I := ULift.{u} (Fin n)
  let M := StandardLattice.{u} r
  let A := CommAlgCat.of k (MonoidAlgebra k M)
  let t : GroupPoints T.group A :=
    algebraPoint A (AlgHom.id k (MonoidAlgebra k M)) ≫ i.hom.hom.hom
  let Q := (l.hom.app A).hom (((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app A t)
  let chars := χ.trans (charactersOfIso i)
  let F : Finset M := (Finset.univ : Finset (I × I)).biUnion (fun ij => (Q.val ij.1 ij.2).coeff.support)
  refine ((F.finite_toSet).image chars).subset ?_
  intro α hα
  obtain ⟨m, rfl⟩ := chars.surjective α
  obtain ⟨_, v, hv, hv0⟩ := hα
  have h := (adjointWeightVectors_iff C l Ad hAd T (chars m) v).mp hv A t
  change Q.val *ᵥ extendCoordinates b A v = characterValue (chars m) A t • extendCoordinates b A v at h
  have hval : characterValue (chars m) A t = MonoidAlgebra.single m 1 :=
    universalCharacterValue i χ hχ m
  rw [hval] at h
  refine ⟨m, ?_, rfl⟩
  by_contra hm
  apply hv0
  refine Eq.trans ?_ (canonicalZero_eq s).symm
  apply b.equivFun.injective
  funext j
  have hz (j' : I) : MonoidAlgebra.coeff (Q.val j j') m = 0 := by
    rw [← Finsupp.notMem_support_iff]
    intro hj
    exact hm (Finset.mem_biUnion.mpr ⟨(j, j'), Finset.mem_univ _, hj⟩)
  have hj := congrArg (fun w : I → A => MonoidAlgebra.coeff (w j) m) h
  change MonoidAlgebra.coeff (∑ j', Q.val j j' * algebraMap k A (b.equivFun v j')) m =
    MonoidAlgebra.coeff
      (MonoidAlgebra.single m 1 * algebraMap k A (b.equivFun v j)) m at hj
  have hscalar (a : MonoidAlgebra k M) (c : k) : a * algebraMap k A c = c • a := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  simp only [hscalar, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, hz, MonoidAlgebra.coeff_single,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at hj
  have hzero := congrArg (fun w : I → k => w j) b.equivFun.map_zero
  have hj0 : b.equivFun v j = 0 := by
    simpa only [mul_zero, Finset.sum_const_zero] using hj.symm
  exact hj0.trans hzero.symm

theorem characterValuesDetectCharacters : Specs.CharacterPairing.CharacterValuesDetectCharacters.{u} := by
  intro k _ T hT χ ψ h
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  obtain ⟨χ₀, _, hχ₀, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) r
  let c := χ₀.trans (charactersOfIso i)
  obtain ⟨m, rfl⟩ := c.surjective χ
  obtain ⟨n, rfl⟩ := c.surjective ψ
  let A := CommAlgCat.of k (MonoidAlgebra k (StandardLattice.{u} r))
  let t : GroupPoints T A :=
    algebraPoint A (AlgHom.id k (MonoidAlgebra k (StandardLattice.{u} r))) ≫ i.hom.hom.hom
  have he := h A t
  change characterValue ((charactersOfIso i) (χ₀ m)) A t =
    characterValue ((charactersOfIso i) (χ₀ n)) A t at he
  have hm := universalCharacterValue i χ₀ hχ₀ m
  have hn := universalCharacterValue i χ₀ hχ₀ n
  change characterValue ((charactersOfIso i) (χ₀ m)) A t = _ at hm
  change characterValue ((charactersOfIso i) (χ₀ n)) A t = _ at hn
  rw [hm, hn] at he
  apply congrArg c
  by_contra hne
  have hcoeff := congrArg (fun f : MonoidAlgebra k (StandardLattice.{u} r) => f.coeff m) he
  classical
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne] at hcoeff
  exact one_ne_zero hcoeff

open WithConv
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private centralizes_iff comp_conjugateFamily mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private theorem characterValue_one {T : GroupScheme k} (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue (1 : Character T) R t = 1 := by
  let f : WithConv (MonoidAlgebra k IntegerCharacters →ₐ[k] R) := 1
  have he : algebraPoint R f.ofConv = (1 : GroupPoints Gm R) :=
    ((hopfSpecPointIso (groupAlgebra k IntegerCharacters)).hom.app R).hom.map_one
  have ht : t ≫ (1 : Character T).hom.hom = (1 : GroupPoints Gm R) :=
    MonObj.comp_one _
  unfold characterValue
  dsimp only
  rw [ht, ← he]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((testSpec k).map (CommAlgCat.ofHom f.ofConv).op)).unop.hom
    (MonoidAlgebra.single integerGenerator 1) = _
  rw [Functor.FullyFaithful.preimage_map]
  change algebraMap k R (Coalgebra.counit (R := k)
    (MonoidAlgebra.single integerGenerator 1 : MonoidAlgebra k IntegerCharacters)) = 1
  rw [MonoidAlgebra.counit_single]
  exact map_one (algebraMap k R)

private theorem isTorus_of_split {T : GroupScheme k} (hT : IsSplitTorus T) : IsTorus T := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let A := groupAlgebra k (StandardLattice.{u} r)
  have eA : extendedHopf k A ≅ A :=
    CommHopfAlgCat.isoMk (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange
      k k (StandardLattice.{u} r))
  have hA : Specs.CharacterDescent.IsTorus A :=
    ⟨k, inferInstance, inferInstance, inferInstance, r, ⟨eA.symm⟩⟩
  obtain ⟨K, _, _, _, n, ⟨j⟩⟩ := (LinearAlgebraicGroups.CharacterDescent.torusOnSchemes A).mp hA
  exact ⟨K, inferInstance, inferInstance, inferInstance, n,
    ⟨(groupBaseChange k K).mapIso i.symm ≪≫ j⟩⟩

private theorem mapPoints_comp {X : SchemeOver k} {R S U : TestAlgebra k}
    (a : R ⟶ S) (b : S ⟶ U) (x : Points X R) :
    mapPoints (a ≫ b) x = mapPoints b (mapPoints a x) := by
  simp only [mapPoints, op_comp, Functor.map_comp, Category.assoc]

local notation "dual" => fun (R : TestAlgebra k) => CommAlgCat.of k (DualNumber R)
local notation "base" => CommAlgCat.of k k

/-- Any test of a dual-number point factors through dual numbers over the test algebra.
The factorization specializes the square-zero parameter to its image under the test. -/
private theorem factorDualTest {R : TestAlgebra k} (a : dual base ⟶ R) :
    ∃ b : dual R ⟶ R,
      constants R ≫ b = 𝟙 R ∧
      dualMap (CommAlgCat.ofHom (Algebra.ofId k R)) ≫ b = a := by
  have he : a.hom (DualNumber.eps : DualNumber k) * a.hom DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  let b : dual R ⟶ R :=
    CommAlgCat.ofHom (DualNumber.lift ⟨(AlgHom.id k R, a.hom DualNumber.eps), he,
      fun _ => Commute.all _ _⟩)
  refine ⟨b, ?_, ?_⟩
  · apply CommAlgCat.hom_ext
    exact DualNumber.lift_comp_inlHom _
  · apply CommAlgCat.hom_ext
    apply AlgHom.toRingHom_injective
    apply DualNumber.ringHom_ext
    · apply RingHom.ext
      intro r
      exact ((dualMap (CommAlgCat.ofHom (Algebra.ofId k R)) ≫ b).hom.commutes r).trans
        (a.hom.commutes r).symm
    · change b.hom ((dualMap (CommAlgCat.ofHom (Algebra.ofId k R))).hom DualNumber.eps) = _
      rw [show (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))).hom DualNumber.eps =
        (DualNumber.eps : DualNumber R) from TrivSqZeroExt.ext
          (map_zero (Algebra.ofId k R)) (map_one (Algebra.ofId k R))]
      exact DualNumber.lift_apply_eps _

private theorem zeroWeightVectors_iff_centralizes {G : GroupScheme k}
    (T : ClosedSubgroup G) (hT : IsAffine T.group.X.left) (v : Lie k G) :
    v ∈ adjointWeightVectors T 1 ↔ Centralizes T.inclusion v.toMul.val := by
  have hs (R : TestAlgebra k) : scale R 1 = 𝟙 _ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    exact TrivSqZeroExt.ext rfl (one_mul z.snd)
  have hi {X : SchemeOver k} (R : TestAlgebra k) (p : Points X R) :
      mapPoints (𝟙 R) p = p := by
    change (testSpec k).map (𝟙 (op R)) ≫ p = p
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  change (∀ (R : TestAlgebra k) (t : GroupPoints T.group R), _) ↔ _
  simp only [characterValue_one, hs, hi]
  constructor
  · intro hv
    unfold Centralizes
    have hAff : IsAffine (T.group.X ⊗ (testSpec k).obj (op (dual base))).left := by
      change IsAffine (CategoryTheory.Limits.pullback T.group.X.hom ((testSpec k).obj _).hom)
      letI := hT
      have : IsAffine ((testSpec k).obj (op (dual base))).left :=
        inferInstanceAs (IsAffine (Spec (CommRingCat.of (DualNumber k))))
      have : IsAffine (Spec (CommRingCat.of k)) := inferInstance
      infer_instance
    apply hom_ext_of_points hAff
    intro R t
    let a := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (t ≫ snd T.group.X ((testSpec k).obj (op (dual base))))).unop
    let g : GroupPoints T.group R := t ≫ fst _ _
    have ha : (testSpec k).map a.op = t ≫ snd _ _ :=
      (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
    obtain ⟨b, hb₁, hb₂⟩ := factorDualTest a
    let p : GroupPoints G (dual R) :=
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val
    let q : GroupPoints G (dual R) := mapPoints (constants R) (g ≫ T.inclusion.hom.hom)
    have hq : q * p * q⁻¹ = p := hv R g
    have hcomm := (mul_inv_eq_iff_eq_mul.mp hq)
    have hmap := congrArg (((groupPointsFunctor k).obj G).map b).hom hcomm
    change mapPoints b (q * p) = mapPoints b (p * q) at hmap
    have map_mul' (x y : GroupPoints G (dual R)) :
        mapPoints b (x * y) = (mapPoints b x : GroupPoints G R) * mapPoints b y :=
      (((groupPointsFunctor k).obj G).map b).hom.map_mul x y
    rw [map_mul', map_mul'] at hmap
    have hp : mapPoints b p = mapPoints a v.toMul.val := by
      dsimp only [p]
      rw [← mapPoints_comp, hb₂]
    have hq' : (mapPoints b q : GroupPoints G R) = g ≫ T.inclusion.hom.hom := by
      dsimp only [q]
      rw [← mapPoints_comp, hb₁, hi]
    rw [hp, hq'] at hmap
    rw [comp_conjugateFamily]
    apply mul_inv_eq_iff_eq_mul.mpr
    have ht₁ : (t ≫ snd T.group.X ((testSpec k).obj (op (dual base))) ≫ v.toMul.val :
        GroupPoints G R) = mapPoints a v.toMul.val := by rw [mapPoints, ha, Category.assoc]
    rw [ht₁]
    exact hmap.symm
  · intro h R g
    have hc := (centralizes_iff T.inclusion v.toMul.val).mp h
      ((testSpec k).obj (op (dual R))) ((testSpec k).map
        (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))).op)
      (mapPoints (constants R) g)
    apply mul_inv_eq_iff_eq_mul.mpr
    exact hc.symm.eq

theorem zeroWeightSpace : Specs.CharacterPairing.ZeroWeightSpace.{u} := by
  intro k _ G hG T hT hmax s
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := mono_over T.inclusion.hom.hom T.isClosedImmersion
  refine ⟨?_, ?_⟩
  · intro p q hpq
    apply Subtype.ext
    apply (cancel_mono T.inclusion.hom.hom).mp
    exact congrArg (fun x : Lie k G.val => x.toMul.val) hpq
  rw [adjointWeightSpaceVectors G T s 1]
  have hAff : IsAffine T.group.X.left := by
    letI := G.property.1
    letI := T.isClosedImmersion
    exact isAffine_of_isAffineHom T.inclusion.hom.hom.left
  have hcent := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T (isTorus_of_split hT) hmax
  ext v
  rw [zeroWeightVectors_iff_centralizes T hAff v]
  change Centralizes T.inclusion v.toMul.val ↔ ∃ w : Lie k T.group, mapPointKernel T.inclusion w = v
  constructor
  · intro hc
    obtain ⟨w, hw⟩ := (hcent _ v.toMul.val).mp hc
    have hred : reduceTangentPoints T.group w = 1 := by
      apply (cancel_mono T.inclusion.hom.hom).mp
      change ((testSpec k).map (dualReduction k).op ≫ w) ≫ T.inclusion.hom.hom =
        (1 : Points T.group.X (CommAlgCat.of k k)) ≫ T.inclusion.hom.hom
      rw [Category.assoc, hw, MonObj.one_comp]
      exact v.toMul.property
    exact ⟨⟨w, hred⟩, Subtype.ext hw⟩
  · rintro ⟨w, rfl⟩
    exact (hcent _ _).mpr ⟨w.toMul.val, rfl⟩

end

end LinearAlgebraicGroups.RootData.CharacterPairing
