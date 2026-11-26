import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.FiberDimension
import MathGenome.Internal.AlgebraCore.P103.Ch06.AffineDimension
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import LinearAlgebraicGroups.RootData.CharacterPairing
import LinearAlgebraicGroups.Affine.LieLeftExact
import LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
import LinearAlgebraicGroups.Reductive.CocharacterLieWeights
import Specs.LinearAlgebraicGroups.RootData.RootGroups
import LinearAlgebraicGroups.Affine.GroupSchemes
import LinearAlgebraicGroups.Affine.SchemeImageQuotient
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Units
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.RootData.RankOneFlag
open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct LaurentPolynomial

universe u

namespace LinearAlgebraicGroups.RootData.RootGroups

open LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.CharacterDescent (Cocharacter Character)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.ProjectiveSpaces (LineRepresentation)
open Specs.RankOneFlag
open Specs.RootGroups
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter)

open private subgroupInclusionFactors centralizes_hasLimit invertLaurent orbit_opposite
  polynomialConstants polynomialConstants_laurent polynomial_family_constant_of_reverse evalLaurent
  orbit_eval evalLaurent_constants unitPointHom unitPointHom_apply unitEquiv unitEquiv_unitPoint
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private mono_over comp_conjugateFamily conjugateLe_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private orbit_constant_iff from LinearAlgebraicGroups.Reductive.CocharacterLieWeights
open CocharacterDynamics (HasLimit HasExtension orbit polynomialToLaurent polynomialEvaluate
  laurentConstants cocharacterPoint limitIsUnique mapPoints_comp unitPoint unitCoordinates mapPoints_unitPoint)

open Specs.AdjointRepresentation (dualMap constants scale)
open Specs.CharacterPairing (characterValue adjointWeightVectors adjointWeightSpace)
open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters groupAlgebraMap)
open CocharacterDynamics (laurentAlgebra laurentParameter AdjointWeightBasis lieImage)
open private laurentParameter_zpow monomial_coeff
  from LinearAlgebraicGroups.Reductive.CocharacterLieWeights
open private characterValue_one zeroWeightVectors_iff_centralizes splitPresentation
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private laurentHopfEquiv laurentHopfEquiv_single
  from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies

open LinearAlgebraicGroups.Specs.CharacterDescent (GeometricCharacters)
open private groupLikeIso from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private charactersOfIso canonicalZero_eq adjointWeightVectors_iff
  from LinearAlgebraicGroups.RootData.CharacterPairing
open CocharacterDynamics (relativeLieImage)

open private latticeCoordinates from LinearAlgebraicGroups.RootData.CharacterPairing
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

private theorem laurent_unit_monomial {k : Type u} [Field k]
    {f : LaurentPolynomial k} (hf : IsUnit f) :
    ∃ a : k, IsUnit a ∧ ∃ n : ℤ, f = LaurentPolynomial.C a * LaurentPolynomial.T n := by
  open LaurentPolynomial in
  obtain ⟨v, rfl⟩ := hf
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow (v : LaurentPolynomial k)
  obtain ⟨m, q, hq⟩ := LaurentPolynomial.exists_T_pow (↑v⁻¹ : LaurentPolynomial k)
  have hpq : p * q = (Polynomial.X : Polynomial k) ^ (n + m) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hp, hq, Polynomial.toLaurent_X_pow]
    calc
      _ = ((v : LaurentPolynomial k) * (↑v⁻¹ : LaurentPolynomial k)) *
          (LaurentPolynomial.T n * LaurentPolynomial.T m) := by ac_rfl
      _ = _ := by rw [Units.mul_inv, one_mul, ← LaurentPolynomial.T_add]; rfl
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow Polynomial.prime_X (n + m)).mp ⟨q, hpq.symm⟩
  obtain ⟨u, hu⟩ := hi.symm
  obtain ⟨a, ha, hau⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hval : p = Polynomial.X ^ i * Polynomial.C a := by
    rw [hau]
    exact hu.symm
  rw [hval, map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, mul_comm] at hp
  refine ⟨a, ha, (i : ℤ) - n, ?_⟩
  have hz := congrArg (fun z : LaurentPolynomial k => z * LaurentPolynomial.T (-(n : ℤ))) hp.symm
  rw [LaurentPolynomial.mul_T_assoc, LaurentPolynomial.mul_T_assoc, add_neg_cancel,
    LaurentPolynomial.T_zero, mul_one] at hz
  exact hz

private theorem laurent_unit_pointed {k : Type u} [Field k]
    {f : LaurentPolynomial k} (hf : IsUnit f)
    (he : LaurentPolynomial.eval₂ (RingHom.id k) 1 f = 1) :
    ∃ n : ℤ, f = LaurentPolynomial.T n := by
  obtain ⟨a, _, n, rfl⟩ := laurent_unit_monomial hf
  rw [LaurentPolynomial.eval₂_C_mul_T] at he
  have h : a = 1 := by simpa using he
  subst a
  refine ⟨n, ?_⟩
  simp


variable {k : Type u} [Field k]

/-- The conditional geometry supplies the flag with its two marked points. -/
private theorem rankOneFlagData
    (centralizer : CentralizerAndPositiveCocharacter.{u}) (geometry : RankOneFlagGeometry.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (α : Character T.group) (hα : α ∈ absoluteRoots T) :
    ∃ (C : Centralizer T α) (cochar : Cocharacter T.group),
      IsReductive (Unipotent.closedSubgroupAlgebraicGroup C.subgroup) ∧
      0 < pairing T.group α cochar ∧
      ∃ (D : LimitDecomposition (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))
        (E : LimitDecomposition (oppositeCocharacter (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))),
        IsRankOneBorelPair C cochar D E ∧
        ∃ Q : QuotientEmbedding.Presentation D.parabolic,
          Nonempty (FlagIdentification C.torus D.parabolic E.parabolic E.contracting Q) := by
  obtain ⟨C, hC, cochar, hcochar⟩ := centralizer G hG T hT hmax α hα
  obtain ⟨D, E, hpair, ⟨Q⟩, hflag⟩ := geometry G hG T hT hmax α hα C cochar hcochar
  exact ⟨C, cochar, hC, hcochar, D, E, hpair, Q, (hflag Q).2.2.2⟩

/-- The change of projective frame associated with two representations of the same line functor. -/
private def changeFrameHom (ρ σ : LineRepresentation k (plane k)) :
    projectiveLine k ⟶ projectiveLine k :=
  (σ.points _).symm (ρ.points _ (𝟙 _))

private theorem changeFrameHom_points (ρ σ : LineRepresentation k (plane k))
    {S : SchemeOver k} (p : S ⟶ projectiveLine k) :
    σ.points _ (p ≫ changeFrameHom ρ σ) = ρ.points _ p := by
  rw [σ.naturality, changeFrameHom, Equiv.apply_symm_apply]
  simpa only [Category.comp_id] using (ρ.naturality p (𝟙 _)).symm

private def changeFrame (ρ σ : LineRepresentation k (plane k)) :
    projectiveLine k ≅ projectiveLine k where
  hom := changeFrameHom ρ σ
  inv := changeFrameHom σ ρ
  hom_inv_id := by
    apply (ρ.points _).injective
    rw [changeFrameHom_points, changeFrameHom, Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (σ.points _).injective
    rw [changeFrameHom_points, changeFrameHom, Equiv.apply_symm_apply]

private abbrev lineFst (R : TestAlgebra k) :
    (lineOver R).left ⟶ projectiveLine k :=
  fst (projectiveLine k) ((testSpec k).obj (op R))

private abbrev lineSnd (R : TestAlgebra k) :
    (lineOver R).left ⟶ (testSpec k).obj (op R) :=
  snd (projectiveLine k) ((testSpec k).obj (op R))

section CartesianAction

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable {M X : C} [GrpObj M] [ModObj M X]

private abbrev baseProduct (X R : C) : Over R := Over.mk (snd X R)

private def baseActionHom {R : C} (g : R ⟶ M) : baseProduct X R ⟶ baseProduct X R :=
  Over.homMk (lift ((snd X R ≫ g) • fst X R) (snd X R)) (lift_snd _ _)

private theorem baseActionHom_fst {R : C} (g : R ⟶ M) :
    (baseActionHom (X := X) g).left ≫ fst X R = (snd X R ≫ g) • fst X R :=
  lift_fst _ _

private theorem baseActionHom_snd {R : C} (g : R ⟶ M) :
    (baseActionHom (X := X) g).left ≫ snd X R = snd X R :=
  lift_snd _ _

private theorem baseActionHom_one (R : C) :
    baseActionHom (X := X) (1 : R ⟶ M) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change lift ((snd X R ≫ (1 : R ⟶ M)) • fst X R) (snd X R) = 𝟙 (X ⊗ R)
  simp only [MonObj.comp_one, one_smul, lift_fst_snd]

private theorem baseActionHom_mul {R : C} (g h : R ⟶ M) :
    baseActionHom (X := X) (g * h) = baseActionHom h ≫ baseActionHom g := by
  apply Over.OverMorphism.ext
  apply CartesianMonoidalCategory.hom_ext
  · change (baseActionHom (g * h)).left ≫ fst X R =
      ((baseActionHom h).left ≫ (baseActionHom g).left) ≫ fst X R
    rw [Category.assoc, baseActionHom_fst, baseActionHom_fst, MonObj.comp_mul, mul_smul,
      ModObj.comp_smul, baseActionHom_fst, ← Category.assoc, baseActionHom_snd]
  · change (baseActionHom (g * h)).left ≫ snd X R =
      ((baseActionHom h).left ≫ (baseActionHom g).left) ≫ snd X R
    rw [Category.assoc, baseActionHom_snd, baseActionHom_snd, baseActionHom_snd]

private def baseAction (R : C) : (R ⟶ M) →* Aut (baseProduct X R) where
  toFun g := Aut.of
    { hom := baseActionHom g
      inv := baseActionHom g⁻¹
      hom_inv_id := by rw [← baseActionHom_mul, inv_mul_cancel, baseActionHom_one]
      inv_hom_id := by rw [← baseActionHom_mul, mul_inv_cancel, baseActionHom_one] }
  map_one' := by
    apply Aut.isoEquiv.injective
    apply Iso.ext
    exact baseActionHom_one R
  map_mul' g h := by
    apply Aut.isoEquiv.injective
    apply Iso.ext
    exact baseActionHom_mul g h

private theorem baseAction_natural {R S : C} (t : S ⟶ R) (g : R ⟶ M) :
    (baseAction (X := X) S (t ≫ g)).asIso.hom.left ≫ (𝟙 X ⊗ₘ t) =
      (𝟙 X ⊗ₘ t) ≫ (baseAction (X := X) R g).asIso.hom.left := by
  have hfst : (𝟙 X ⊗ₘ t) ≫ fst X R = fst X S := by simp
  have hsnd : (𝟙 X ⊗ₘ t) ≫ snd X R = snd X S ≫ t := tensorHom_snd _ _
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc]
    change (baseActionHom (t ≫ g)).left ≫ (𝟙 X ⊗ₘ t) ≫ fst X R =
      (𝟙 X ⊗ₘ t) ≫ (baseActionHom g).left ≫ fst X R
    rw [hfst, baseActionHom_fst, baseActionHom_fst, ModObj.comp_smul, hfst]
    rw [← Category.assoc (f := (𝟙 X ⊗ₘ t)), hsnd, Category.assoc]
  · simp only [Category.assoc]
    change (baseActionHom (t ≫ g)).left ≫ (𝟙 X ⊗ₘ t) ≫ snd X R =
      (𝟙 X ⊗ₘ t) ≫ (baseActionHom g).left ≫ snd X R
    rw [baseActionHom_snd, hsnd, ← Category.assoc, baseActionHom_snd]

end CartesianAction

private abbrev actionOver {H : GroupScheme k} [a : ModObj H.X (projectiveLine k)]
    (R : TestAlgebra k) : GroupPoints H R →* Aut (lineOver R) :=
  baseAction ((testSpec k).obj (op R))

private theorem actionOver_natural {H : GroupScheme k} [a : ModObj H.X (projectiveLine k)]
    (R S : TestAlgebra k) (b : R ⟶ S) (g : GroupPoints H R) :
    (actionOver (H := H) S (mapPoints b g)).asIso.hom.left ≫ lineBaseMap b =
      lineBaseMap b ≫ (actionOver (H := H) R g).asIso.hom.left := by
  have heq : lineBaseMap b = 𝟙 (projectiveLine k) ⊗ₘ (testSpec k).map b.op := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [lineBaseMap]
  rw [heq]
  exact baseAction_natural ((testSpec k).map b.op) g

private theorem projectiveHomOfAction {H K : GroupScheme k} (hH : IsAffine H.X.left)
    (a : ModObj H.X (projectiveLine k)) (b : ModObj K.X (projectiveLine k))
    (e : ∀ R : TestAlgebra k, GroupPoints K R ≃* Aut (lineOver R))
    (enat : ∀ (R S : TestAlgebra k) (t : R ⟶ S) (g : GroupPoints K R),
      (e S (mapPoints t g)).asIso.hom.left ≫ lineBaseMap t =
        lineBaseMap t ≫ (e R g).asIso.hom.left)
    (eact : ∀ (R : TestAlgebra k) (g : GroupPoints K R),
      (e R g).asIso.hom.left ≫ lineFst R = lift (lineSnd R ≫ g) (lineFst R) ≫ b.smul) :
    ∃ f : H ⟶ K, (f.hom.hom ⊗ₘ 𝟙 (projectiveLine k)) ≫ b.smul = a.smul := by
  letI := a
  let pointMap (R : TestAlgebra k) : GroupPoints H R →* GroupPoints K R :=
    (e R).symm.toMonoidHom.comp (actionOver R)
  have pointMap_spec (R : TestAlgebra k) (g : GroupPoints H R) :
      e R (pointMap R g) = actionOver R g := (e R).apply_symm_apply _
  let τ : (groupPointsFunctor k).obj H ⟶ (groupPointsFunctor k).obj K :=
    { app := fun R ↦ GrpCat.ofHom (pointMap R)
      naturality := by
        intro R S t
        ext g
        change pointMap S (mapPoints t g) = mapPoints t (pointMap R g)
        apply (e S).injective
        rw [pointMap_spec]
        have ha := actionOver_natural R S t g
        have he := enat R S t (pointMap R g)
        rw [pointMap_spec] at he
        have h := ha.trans he.symm
        apply Aut.isoEquiv.injective
        apply Iso.ext
        apply Over.OverMorphism.ext
        apply CartesianMonoidalCategory.hom_ext
        · have hp := congrArg (· ≫ lineFst R) h
          simpa only [Category.assoc, lineBaseMap, lift_fst, Aut.isoEquiv_apply] using hp
        · exact (Over.w ((actionOver S (mapPoints t g)).asIso.hom)).trans
            (Over.w ((e S (mapPoints t (pointMap R g))).asIso.hom)).symm }
  let f := (LinearAlgebraicGroups.groupHomEquiv H K hH).symm τ
  have hf (R : TestAlgebra k) (g : GroupPoints H R) :
      g ≫ f.hom.hom = pointMap R g := by
    have h := (LinearAlgebraicGroups.groupHomEquiv H K hH).apply_symm_apply τ
    exact congrArg (fun σ : (groupPointsFunctor k).obj H ⟶ (groupPointsFunctor k).obj K =>
      σ.app R g) h
  refine ⟨f, ?_⟩
  obtain ⟨A, ⟨i⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hH
  let test := A.unop
  let swap : (lineOver test).left ≅ H.X ⊗ projectiveLine k :=
    (β_ (projectiveLine k) ((testSpec k).obj A)) ≪≫ (i ⊗ᵢ Iso.refl (projectiveLine k))
  apply (cancel_epi swap.hom).mp
  have hswap : swap.hom = lift (lineSnd test ≫ i.hom) (lineFst test) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [swap, lineFst, lineSnd, Category.assoc, test]
  have hlift : swap.hom ≫ (f.hom.hom ⊗ₘ 𝟙 (projectiveLine k)) =
      lift (lineSnd test ≫ (i.hom ≫ f.hom.hom)) (lineFst test) := by
    rw [hswap]
    apply CartesianMonoidalCategory.hom_ext <;> simp [Category.assoc]
  rw [← Category.assoc, hlift, hswap, hf]
  rw [← eact, pointMap_spec]
  exact baseActionHom_fst i.hom

/-- Every affine test point in the kernel of the projective quotient is scalar. -/
def HasScalarKernel {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {infinity zero : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a infinity zero) : Prop :=
  ∀ (R : TestAlgebra k) (m : GroupPoints P.linearGroup.val R),
    (m ≫ P.quotient.hom.hom : GroupPoints P.projectiveGroup.val R) = 1 →
    ∃ u : Rˣ, P.matrices.hom.app R m = Matrix.GeneralLinearGroup.scalar Index u

/-- Map invertible matrices into the projective linear group used by the flag action. -/
def projectiveMatrixPoint {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {infinity zero : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a infinity zero) (R : TestAlgebra k) :
    Matrix.GeneralLinearGroup Index.{u} R →* GroupPoints P.projectiveGroup.val R :=
  (((groupPointsFunctor k).map P.quotient).app R).hom.comp (P.matrices.inv.app R).hom

private structure ProjectiveMatrixPresentation {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) : Prop where
  scalar : ∀ (R : TestAlgebra k) (v : Rˣ),
    projectiveMatrixPoint P R (Matrix.GeneralLinearGroup.scalar Index v) = 1
  lifts : ∀ (R : TestAlgebra k) (g : GroupPoints P.projectiveGroup.val R),
    ∃ (S : TestAlgebra k) (b : R ⟶ S) (m : Matrix.GeneralLinearGroup Index.{u} S),
      Fppf.IsFppf ((testSpec k).map b.op).left ∧ projectiveMatrixPoint P S m = mapPoints b g

/-- Marked projective actions induced by the affine rank-one group action on its flag. -/
private theorem projectiveActionWithMatrices (projective : ProjectiveLineAutomorphisms.{u})
    {H : GroupScheme k} (hH : IsAffine H.X.left)
    {T Bpos Bneg Uneg : ClosedSubgroup H} {Q : QuotientEmbedding.Presentation Bpos}
    (F : FlagIdentification T Bpos Bneg Uneg Q) :
    ∃ P : ProjectiveAction F.action (η[H.X] ≫ Q.projection)
      (F.normalizerPoint ≫ Q.projection), HasScalarKernel P ∧ ProjectiveMatrixPresentation P := by
  obtain ⟨hm, hl, em, el, s, hs, hscalar, hnormal, QGL, PGL, q, i, b, σ, e,
    htorsor, hkernel, hquotient, enat, eact, matrix, hlift, hline⟩ := projective k
  let L : AffineAlgebraicGroup k :=
    letI := hl.hopf
    StandardGroups.spectrum k (StandardGroups.GLCoordinates k Index.{u})
  let frame := F.iso ≪≫ changeFrame F.coordinates σ
  letI := F.action
  letI : IsMonHom (Iso.refl H.X).hom := by
    change IsMonHom (𝟙 H.X)
    infer_instance
  let a : ModObj H.X (projectiveLine k) := ModObj.ofIso (Iso.refl H.X) frame
  obtain ⟨f, hf⟩ := projectiveHomOfAction hH a b e enat eact
  have ha : (𝟙 H.X ⊗ₘ frame.hom) ≫ a.smul = F.action.smul ≫ frame.hom := by
    change (𝟙 H.X ⊗ₘ frame.hom) ≫ (𝟙 H.X ⊗ₘ frame.inv) ≫ F.action.smul ≫ frame.hom = _
    simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Iso.hom_inv_id, id_tensorHom_id]
  refine ⟨{ coordinates := σ, frame := frame
            infinityCoordinates := ?_, zeroCoordinates := ?_
            linearGroup := L, matrices := el, projectiveGroup := PGL, quotient := q
            action := b, automorphisms := e, automorphismNaturality := enat
            automorphismAction := eact, matrixAction := matrix, hom := f, transportsAction := ?_ }, ?_, ⟨?_, ?_⟩⟩
  · unfold HasCoordinates
    change ((σ.points _
      ((toUnit _ ≫ η[H.X] ≫ Q.projection ≫ F.iso.hom) ≫ changeFrameHom F.coordinates σ)).line
        (CommAlgCat.of k k) (𝟙 _)).submodule = _
    rw [changeFrameHom_points]
    exact F.infinityCoordinates
  · unfold HasCoordinates
    change ((σ.points _
      ((toUnit _ ≫ F.normalizerPoint ≫ Q.projection ≫ F.iso.hom) ≫
        changeFrameHom F.coordinates σ)).line (CommAlgCat.of k k) (𝟙 _)).submodule = _
    rw [changeFrameHom_points]
    exact F.zeroCoordinates
  · rw [← ha, ← hf, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  · intro R m hm'
    let S := (testSpec k).obj (op R)
    have h : m ≫ q.hom.hom = toUnit S ≫ η[PGL.val.X] := hm'
    let x := hkernel.lift m (toUnit S) h
    have hx : x ≫ s.hom.hom = m := hkernel.lift_fst _ _ _
    exact ⟨em.hom.app R x, hx ▸ hscalar R x⟩

  · intro R v
    let x := em.inv.app R v
    have hx : em.hom.app R x = v :=
      congrArg (fun f : (StandardGroups.multiplicativePoints k).obj R ⟶
        (StandardGroups.multiplicativePoints k).obj R => f v) (em.inv_hom_id_app R)
    have hsv := hscalar R x
    rw [hx] at hsv
    have he : el.inv.app R (Matrix.GeneralLinearGroup.scalar Index v) = x ≫ s.hom.hom := by
      rw [← hsv]
      exact congrArg (fun f : ((groupPointsFunctor k).obj L.val).obj R ⟶
        ((groupPointsFunctor k).obj L.val).obj R => f (x ≫ s.hom.hom)) (el.hom_inv_id_app R)
    change el.inv.app R _ ≫ q.hom.hom = _
    rw [he, Category.assoc, hkernel.w, ← Category.assoc, comp_toUnit]
    rfl
  · intro R g
    obtain ⟨S, b, m, hb, hm⟩ := hlift R g
    refine ⟨S, b, el.hom.app S m, hb, ?_⟩
    change el.inv.app S (el.hom.app S m) ≫ q.hom.hom = _
    have he : el.inv.app S (el.hom.app S m) = m :=
      congrArg (fun f : ((groupPointsFunctor k).obj L.val).obj S ⟶
        ((groupPointsFunctor k).obj L.val).obj S => f m) (el.hom_inv_id_app S)
    rw [he, hm]

/-- Marked projective actions with scalar kernel. -/
theorem projectiveActionOfFlag (projective : ProjectiveLineAutomorphisms.{u})
    {H : GroupScheme k} (hH : IsAffine H.X.left)
    {T Bpos Bneg Uneg : ClosedSubgroup H} {Q : QuotientEmbedding.Presentation Bpos}
    (F : FlagIdentification T Bpos Bneg Uneg Q) :
    ∃ P : ProjectiveAction F.action (η[H.X] ≫ Q.projection)
      (F.normalizerPoint ≫ Q.projection), HasScalarKernel P :=
  (projectiveActionWithMatrices projective hH F).imp fun _ h => h.1

/-- The conditional premises supply the marked projective action and the opposite Borels. -/
theorem rankOneProjectiveData
    (centralizer : CentralizerAndPositiveCocharacter.{u})
    (projective : ProjectiveLineAutomorphisms.{u}) (geometry : RankOneFlagGeometry.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (α : Character T.group) (hα : α ∈ absoluteRoots T) :
    ∃ (C : Centralizer T α) (cochar : Cocharacter T.group),
      IsReductive (Unipotent.closedSubgroupAlgebraicGroup C.subgroup) ∧
      0 < pairing T.group α cochar ∧
      ∃ (D : LimitDecomposition (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))
        (E : LimitDecomposition (oppositeCocharacter (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))),
        IsRankOneBorelPair C cochar D E ∧
        ∃ (Q : QuotientEmbedding.Presentation D.parabolic)
          (F : FlagIdentification C.torus D.parabolic E.parabolic E.contracting Q),
          ∃ P : ProjectiveAction F.action (η[C.subgroup.group.X] ≫ Q.projection)
            (F.normalizerPoint ≫ Q.projection), HasScalarKernel P := by
  obtain ⟨C, cochar, hC, hcochar, D, E, hpair, Q, ⟨F⟩⟩ :=
    rankOneFlagData centralizer geometry G hG T hT hmax α hα
  have hAff : IsAffine C.subgroup.group.X.left :=
    (Unipotent.closedSubgroupAlgebraicGroup C.subgroup).property.1
  exact ⟨C, cochar, hC, hcochar, D, E, hpair, Q, F, projectiveActionOfFlag projective hAff F⟩

/-- Evaluating the standard polynomial coordinate enumerates all additive-line points. -/
def additivePoints (A : AdditiveLine k) (R : TestAlgebra k) : R ≃ GroupPoints A.group R where
  toFun a := rootPoint (𝟙 A.group) R a
  invFun g :=
    ((AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).preimage g).unop.hom
      Polynomial.X
  left_inv a := by
    unfold rootPoint
    change (((AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      ((testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval a : Polynomial k →ₐ[k] R)).op ≫
        𝟙 _)).unop.hom Polynomial.X) = a
    rw [Category.comp_id, Functor.FullyFaithful.preimage_map]
    exact Polynomial.aeval_X a
  right_inv g := by
    unfold rootPoint
    change (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval _) : CommAlgCat.of k (Polynomial k) ⟶ R).op
      ≫ 𝟙 _ = g
    rw [Category.comp_id]
    have h : CommAlgCat.ofHom (Polynomial.aeval
        (((AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).preimage g).unop.hom
          Polynomial.X)) =
        ((AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).preimage g).unop := by
      apply CommAlgCat.hom_ext
      apply Polynomial.algHom_ext
      exact Polynomial.aeval_X _
    rw [h, Quiver.Hom.op_unop, Functor.FullyFaithful.map_preimage]

private theorem additivePoints_add (A : AdditiveLine k) (R : TestAlgebra k) (x y : R) :
    additivePoints A R (x + y) = additivePoints A R x * additivePoints A R y := by
  letI := A.operations.hopf
  let e := Spec.mapMulEquiv (R := k) (S := Polynomial k) (T := R)
  change e (WithConv.toConv (Polynomial.aeval (x + y))) =
    e (WithConv.toConv (Polynomial.aeval x)) * e (WithConv.toConv (Polynomial.aeval y))
  rw [← map_mul]
  apply congrArg e
  apply WithConv.ofConv_injective
  apply Polynomial.algHom_ext
  change Polynomial.aeval (x + y) Polynomial.X =
    (WithConv.toConv (Polynomial.aeval x : Polynomial k →ₐ[k] R) *
      WithConv.toConv (Polynomial.aeval y : Polynomial k →ₐ[k] R)) Polynomial.X
  rw [AlgHom.convMul_apply, Polynomial.aeval_X]
  change x + y = Algebra.TensorProduct.lift (Polynomial.aeval x) (Polynomial.aeval y)
    (fun _ _ ↦ Commute.all _ _) (A.operations.delta Polynomial.X)
  rw [A.comultiplication]
  simp

private theorem additivePoints_natural (A : AdditiveLine k) {R S : TestAlgebra k}
    (a : R ⟶ S) (x : R) :
    mapPoints a (additivePoints A R x) = additivePoints A S (a.hom x) := by
  change (testSpec k).map a.op ≫ (testSpec k).map
      (CommAlgCat.ofHom (Polynomial.aeval x : Polynomial k →ₐ[k] R)).op ≫ 𝟙 _ =
    (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval (a.hom x) : Polynomial k →ₐ[k] S)).op ≫ 𝟙 _
  rw [Category.comp_id, Category.comp_id, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change a.hom (Polynomial.aeval x Polynomial.X) = Polynomial.aeval (a.hom x) Polynomial.X
  simp

private theorem rootPoint_comp {A : AdditiveLine k} {G H : GroupScheme k}
    (x : A.group ⟶ G) (f : G ⟶ H) (R : TestAlgebra k) (a : R) :
    rootPoint (x ≫ f) R a = rootPoint x R a ≫ f.hom.hom :=
  (Category.assoc _ _ _).symm

/-- Equality of scheme maps is detected by all affine tests over the base. -/
private theorem hom_ext_on_affine_tests {X Y : SchemeOver k} {f g : X ⟶ Y}
    (h : ∀ (R : TestAlgebra k) (x : Points X R), x ≫ f = x ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  let 𝒰 := X.left.affineCover
  apply 𝒰.hom_ext
  intro i
  let W : SchemeOver k := Over.mk (𝒰.f i ≫ X.hom)
  let j : W ⟶ X := Over.homMk (𝒰.f i) rfl
  have hW : IsAffine W.left := by
    change IsAffine (Spec _)
    infer_instance
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hW
  have hh := (cancel_epi e.hom).mp (by
    simpa only [Category.assoc] using h A.unop (e.hom ≫ j) :
      e.hom ≫ (j ≫ f) = e.hom ≫ (j ≫ g))
  exact congrArg Over.Hom.left hh

/-- A homomorphism of affine algebraic groups injective on all affine tests is a closed immersion. -/
theorem isClosedImmersion_of_injectivePoints (G H : AffineAlgebraicGroup k) (f : G.val ⟶ H.val)
    (hf : ∀ R : TestAlgebra k, Function.Injective (fun x : GroupPoints G.val R ↦ x ≫ f.hom.hom)) :
    IsClosedImmersion f.hom.hom.left := by
  obtain ⟨I, p, i, ⟨hp, hflat, hsurj, _, _, himm⟩, _, _⟩ :=
    LinearAlgebraicGroups.schemeImageFactorization G H f
  have hp' := congrArg (fun a : G.val ⟶ H.val ↦ a.hom.hom) hp
  have hpLeft : p.hom.hom.left ≫ i.hom.hom.left = f.hom.hom.left :=
    congrArg Over.Hom.left hp'
  have hmono : Mono p.hom.hom.left := by
    constructor
    intro W a b hab
    let W' : SchemeOver k := Over.mk (a ≫ G.val.X.hom)
    let a' : W' ⟶ G.val.X := Over.homMk a rfl
    have hw : b ≫ G.val.X.hom = W'.hom := by
      change b ≫ G.val.X.hom = a ≫ G.val.X.hom
      rw [← Over.w p.hom.hom, ← Category.assoc, ← Category.assoc, hab]
    let b' : W' ⟶ G.val.X := Over.homMk b hw
    have heq : a' = b' := by
      apply hom_ext_on_affine_tests
      intro R x
      apply hf R
      change (x ≫ a') ≫ f.hom.hom = (x ≫ b') ≫ f.hom.hom
      have he : a' ≫ p.hom.hom = b' ≫ p.hom.hom := Over.OverMorphism.ext hab
      rw [← hp']
      change (x ≫ a') ≫ (p.hom.hom ≫ i.hom.hom) = (x ≫ b') ≫ (p.hom.hom ≫ i.hom.hom)
      simpa only [Category.assoc] using
        congrArg (fun z ↦ x ≫ z ≫ i.hom.hom) he
    exact congrArg Over.Hom.left heq
  letI := hflat
  letI := hsurj
  letI := hmono
  letI := Flat.isIso_of_surjective_of_mono p.hom.hom.left
  letI := himm
  rw [← hpLeft]
  infer_instance

private def i0 : Index.{u} := ⟨0⟩
private def i1 : Index.{u} := ⟨1⟩

private theorem i0_ne_i1 : i0.{u} ≠ i1.{u} := by decide
private theorem i1_ne_i0 : i1.{u} ≠ i0.{u} := i0_ne_i1.symm

/-- The elementary-matrix lift of the rank-one word. -/
def wordMatrix {R : Type*} [CommRing R] (a : Rˣ) :
    Matrix.GeneralLinearGroup Index.{u} R :=
  Matrix.GeneralLinearGroup.transvection i0 i1 i0_ne_i1 (a : R) *
    Matrix.GeneralLinearGroup.transvection i1 i0 i1_ne_i0 (-(↑a⁻¹ : R)) *
    Matrix.GeneralLinearGroup.transvection i0 i1 i0_ne_i1 (a : R)

private theorem sum_index {R : Type*} [AddCommMonoid R] (f : Index.{u} → R) :
    ∑ i, f i = f i0 + f i1 := by
  refine ((Equiv.ulift.symm : Fin 2 ≃ Index.{u}).sum_comp f).symm.trans ?_
  rw [Fin.sum_univ_two]
  rfl

private theorem entry_expand {R : Type*} [CommRing R] (M N : Matrix Index.{u} Index.{u} R)
    (i j : Index.{u}) : (M * N) i j = M i i0 * N i0 j + M i i1 * N i1 j := by
  rw [Matrix.mul_apply]
  exact sum_index _

private theorem wordMatrix_entries {R : Type*} [CommRing R] (a : Rˣ) :
    (wordMatrix.{u} a).val i0 i0 = 0 ∧ (wordMatrix.{u} a).val i0 i1 = (a : R) ∧
    (wordMatrix.{u} a).val i1 i0 = -(↑a⁻¹ : R) ∧ (wordMatrix.{u} a).val i1 i1 = 0 := by
  simp [wordMatrix, Units.val_mul, entry_expand, Matrix.transvection,
    i0_ne_i1, i1_ne_i0]

/-- The quotient of the rank-one word by its value at one is diagonal. -/
theorem normalizedWordMatrix {R : Type*} [CommRing R] (a : Rˣ) :
    ((wordMatrix.{u} a) * (wordMatrix.{u} (1 : Rˣ))⁻¹).val =
      Matrix.diagonal (fun i : Index.{u} => if i = i0 then (a : R) else (↑a⁻¹ : R)) := by
  have h0 := wordMatrix_entries.{u} a
  have h1 := wordMatrix_entries.{u} (1 : Rˣ)
  have hmul : (wordMatrix.{u} a).val =
      Matrix.diagonal (fun i : Index.{u} => if i = i0 then (a : R) else (↑a⁻¹ : R)) *
        (wordMatrix.{u} (1 : Rˣ)).val := by
    ext i j
    have cases_i (t : Index.{u}) : t = i0 ∨ t = i1 := by
      rcases t with ⟨t⟩
      fin_cases t <;> simp [i0, i1]
    rcases cases_i i with rfl | rfl <;> rcases cases_i j with rfl | rfl <;>
      simp [i1_ne_i0,
        h0.1, h0.2.1, h0.2.2.1, h0.2.2.2, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
  simp only [Units.val_mul]
  rw [hmul, mul_assoc, Units.mul_inv, mul_one]

/-- Conjugation of the rank-one word scales its argument by the positive root character. -/
theorem conjugateRankOneWord {G : GroupScheme k} (T : ClosedSubgroup G)
    {α : Character T.group} {A : AdditiveLine k} {xpos xneg : A.group ⟶ G}
    (hpos : HasScalarAction T α xpos) (hneg : HasScalarAction T α⁻¹ xneg)
    (R : TestAlgebra k) (t : GroupPoints T.group R) (z b : Rˣ)
    (hz : Specs.CharacterPairing.characterValue α R t = (z : R))
    (hzneg : Specs.CharacterPairing.characterValue α⁻¹ R t = (↑z⁻¹ : R)) :
    let g : GroupPoints G R := t ≫ T.inclusion.hom.hom
    g * rankOneWord xpos xneg R b * g⁻¹ = rankOneWord xpos xneg R (z * b) := by
  let g : GroupPoints G R := t ≫ T.inclusion.hom.hom
  change MulAut.conj g (rankOneWord xpos xneg R b) = rankOneWord xpos xneg R (z * b)
  have hp : g * rootPoint xpos R (b : R) * g⁻¹ = rootPoint xpos R ((z : R) * b) :=
    hz ▸ hpos R t (b : R)
  have hn : g * rootPoint xneg R (-(↑b⁻¹ : R)) * g⁻¹ =
      rootPoint xneg R ((↑z⁻¹ : R) * -(↑b⁻¹ : R)) :=
    hzneg ▸ hneg R t (-(↑b⁻¹ : R))
  simp only [rankOneWord, map_mul, MulAut.conj_apply, hp, hn, Units.val_mul, _root_.mul_inv_rev,
    neg_mul, mul_comm (↑z⁻¹ : R)]


private def standardTransvections (A : AdditiveLine k) (i j : Index.{u}) (hij : i ≠ j) :
    (groupPointsFunctor k).obj A.group ⟶ StandardGroups.generalLinearPoints k Index.{u} where
  app R := GrpCat.ofHom <| MonoidHom.mk'
    (fun a ↦ Matrix.GeneralLinearGroup.transvection i j hij ((additivePoints A R).symm a))
    (by
      intro a b
      obtain ⟨x, rfl⟩ := (additivePoints A R).surjective a
      obtain ⟨y, rfl⟩ := (additivePoints A R).surjective b
      rw [← additivePoints_add, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      apply Units.ext
      exact (Matrix.transvection_mul_transvection_same (i := i) (j := j) hij x y).symm)
  naturality R S a := by
    ext g
    obtain ⟨x, rfl⟩ := (additivePoints A R).surjective g
    change Matrix.GeneralLinearGroup.transvection i j hij
      ((additivePoints A S).symm (mapPoints a (additivePoints A R x))) =
      (Matrix.GeneralLinearGroup.transvection i j hij ((additivePoints A R).symm
        (additivePoints A R x))).map a.hom.toRingHom
    rw [additivePoints_natural, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    apply Units.ext
    ext r s
    change Matrix.transvection i j (a.hom x) r s =
      (Matrix.GeneralLinearGroup.transvection i j hij x).map a.hom.toRingHom r s
    rw [Matrix.GeneralLinearGroup.map_apply]
    change Matrix.transvection i j (a.hom x) r s = a.hom (Matrix.transvection i j x r s)
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      map_add, apply_ite, map_one, map_zero]
    split_ifs <;> rfl

private abbrev additiveLineGroup (A : AdditiveLine k) : AffineAlgebraicGroup k :=
  letI := A.operations.hopf
  StandardGroups.spectrum k (Polynomial k)

/-- The upper or lower transvection, viewed as a group scheme morphism to the projective group. -/
def transvectionHom {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {infinity zero : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a infinity zero) (A : AdditiveLine k)
    (i j : Index.{u}) (hij : i ≠ j) : A.group ⟶ P.projectiveGroup.val :=
  (LinearAlgebraicGroups.groupHomEquiv _ _ (additiveLineGroup A).property.1).symm
    (standardTransvections A i j hij ≫ P.matrices.inv ≫ (groupPointsFunctor k).map P.quotient)

/-- The transvection morphism has its elementary-matrix formula over each test algebra. -/
theorem transvectionHom_point {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {infinity zero : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a infinity zero) (A : AdditiveLine k)
    (i j : Index.{u}) (hij : i ≠ j) (R : TestAlgebra k) (c : R) :
    rootPoint (transvectionHom P A i j hij) R c =
      projectiveMatrixPoint P R (Matrix.GeneralLinearGroup.transvection i j hij c) := by
  let τ := standardTransvections A i j hij ≫ P.matrices.inv ≫ (groupPointsFunctor k).map P.quotient
  have h := (LinearAlgebraicGroups.groupHomEquiv _ _ (additiveLineGroup A).property.1).apply_symm_apply τ
  have hp := congrArg (fun σ : (groupPointsFunctor k).obj A.group ⟶
    (groupPointsFunctor k).obj P.projectiveGroup.val => σ.app R (additivePoints A R c)) h
  change additivePoints A R c ≫ (transvectionHom P A i j hij).hom.hom =
    projectiveMatrixPoint P R (Matrix.GeneralLinearGroup.transvection i j hij
      ((additivePoints A R).symm (additivePoints A R c))) at hp
  rw [Equiv.symm_apply_apply] at hp
  rw [← Category.id_comp (transvectionHom P A i j hij), rootPoint_comp]
  exact hp

/-- The projective class of each elementary transvection is a closed additive subgroup. -/
theorem transvectionHom_closedImmersion {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {infinity zero : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a infinity zero) (hscalar : HasScalarKernel P)
    (A : AdditiveLine k) (i j : Index.{u}) (hij : i ≠ j) :
    IsClosedImmersion (transvectionHom P A i j hij).hom.hom.left := by
  let f := transvectionHom P A i j hij
  apply isClosedImmersion_of_injectivePoints (additiveLineGroup A) P.projectiveGroup
  intro R
  let fR := (((groupPointsFunctor k).map f).app R).hom
  change Function.Injective fR
  apply (injective_iff_map_eq_one fR).mpr
  intro p hp
  obtain ⟨c, rfl⟩ := (additivePoints A R).surjective p
  have hp' : rootPoint f R c = 1 := by
    rw [← Category.id_comp f, rootPoint_comp]
    exact hp
  rw [transvectionHom_point] at hp'
  let m := Matrix.GeneralLinearGroup.transvection i j hij c
  obtain ⟨u, hu⟩ := hscalar R (P.matrices.inv.app R m) hp'
  have hmi : (P.matrices.hom.app R) ((P.matrices.inv.app R) m) = m := by
    exact congrArg (fun g : (StandardGroups.generalLinearPoints k Index).obj R ⟶
      (StandardGroups.generalLinearPoints k Index).obj R => g m) (P.matrices.inv_hom_id_app R)
  rw [hmi] at hu
  have hc := congrArg (fun g : Matrix.GeneralLinearGroup Index R => g.val i j) hu
  have hcz : c = 0 := by
    simpa [m, Matrix.transvection, Matrix.one_apply, Matrix.single_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply, hij] using hc
  subst c
  have hz := additivePoints_add A R (0 : R) 0
  rw [zero_add] at hz
  exact (mul_left_cancel ((mul_one (additivePoints A R 0)).trans hz)).symm

/-- The image of a matched rank-one word is the class of the corresponding product of matrices. -/
theorem rankOneWord_projective {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {infinity zero : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a infinity zero) (A : AdditiveLine k) (U V : ClosedSubgroup H)
    (p : TransvectionParametrization P A U ⟨0⟩ ⟨1⟩ (by decide))
    (n : TransvectionParametrization P A V ⟨1⟩ ⟨0⟩ (by decide))
    (R : TestAlgebra k) (b : Rˣ) :
    rankOneWord (p.root.hom ≫ U.inclusion) (n.root.hom ≫ V.inclusion) R b ≫ P.hom.hom.hom =
      projectiveMatrixPoint P R (wordMatrix b) := by
  let F := (((groupPointsFunctor k).map P.hom).app R).hom
  change F (rankOneWord (p.root.hom ≫ U.inclusion) (n.root.hom ≫ V.inclusion) R b) =
    projectiveMatrixPoint P R (wordMatrix b)
  have hp (c : R) :
      F (rootPoint (p.root.hom ≫ U.inclusion) R c) =
        projectiveMatrixPoint P R (Matrix.GeneralLinearGroup.transvection i0 i1 i0_ne_i1 c) := by
    change rootPoint _ R c ≫ P.hom.hom.hom = _
    rw [← rootPoint_comp, Category.assoc, p.matchesTransvection]
    exact p.matrixPoints R c
  have hn (c : R) :
      F (rootPoint (n.root.hom ≫ V.inclusion) R c) =
        projectiveMatrixPoint P R (Matrix.GeneralLinearGroup.transvection i1 i0 i1_ne_i0 c) := by
    change rootPoint _ R c ≫ P.hom.hom.hom = _
    rw [← rootPoint_comp, Category.assoc, n.matchesTransvection]
    exact n.matrixPoints R c
  simp only [rankOneWord, wordMatrix, map_mul, hp, hn]




private def pointLine (ρ : LineRepresentation k (plane k))
    (R : TestAlgebra k) (p : Points (projectiveLine k) R) : Submodule R (R ⊗[k] plane k) :=
  ((ρ.points _ p).line R (𝟙 _)).submodule

private theorem pointLine_natural (ρ : LineRepresentation k (plane k))
    {R S : TestAlgebra k} (b : R ⟶ S) (p : Points (projectiveLine k) R) :
    pointLine ρ S (mapPoints b p) = ProjectiveSpaces.changeLineSubmodule k _ b (pointLine ρ R p) := by
  unfold pointLine
  rw [mapPoints, ρ.naturality]
  simpa only [mapPoints, ProjectiveSpaces.LineFamily.pullback, Category.id_comp, Category.comp_id] using
    (ρ.points _ p).compatible b (𝟙 _)

private theorem pointLine_injective (ρ : LineRepresentation k (plane k)) (R : TestAlgebra k) :
    Function.Injective (pointLine ρ R) := by
  intro p q h
  apply (ρ.points _).injective
  cases hLp : ρ.points _ p with
  | mk lp hp =>
    cases hLq : ρ.points _ q with
    | mk lq hq =>
      unfold pointLine at h
      rw [hLp, hLq] at h
      suffices lp = lq by cases this; rfl
      funext S t
      let b : R ⟶ S := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage t).unop
      have ht : mapPoints b (𝟙 _) = t := by
        change (testSpec k).map b.op ≫ 𝟙 _ = t
        rw [Category.comp_id]
        exact (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
      have he := (hp b (𝟙 _)).trans ((congrArg (ProjectiveSpaces.changeLineSubmodule k _ b) h).trans
        (hq b (𝟙 _)).symm)
      rw [ht] at he
      generalize hpl : lp S t = pl at he ⊢
      generalize hql : lq S t = ql at he ⊢
      cases pl
      cases ql
      congr

private def axis (R : TestAlgebra k) (i : Index.{u}) : Submodule R (R ⊗[k] plane k) :=
  R ∙ ((planeBasis k).baseChange R i)

private theorem axis_natural {R S : TestAlgebra k} (b : R ⟶ S) (i : Index.{u}) :
    ProjectiveSpaces.changeLineSubmodule k (plane k) b (axis R i) = axis S i := by
  letI : Algebra R S := b.hom.toAlgebra
  letI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' (b.hom.comp_algebraMap).symm
  change ((axis R i).baseChange S).map
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k R S S (plane k)).toLinearMap = axis S i
  rw [axis, Submodule.baseChange_span, Set.image_singleton, Submodule.map_span, Set.image_singleton]
  congr 2
  rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply]
  change TensorProduct.AlgebraTensorModule.cancelBaseChange k R S S (plane k)
    (1 ⊗ₜ[R] ((1 : R) ⊗ₜ[k] (planeBasis k) i)) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  simp

private abbrev baseTest (k : Type u) [Field k] := CommAlgCat.of k k

private theorem axis_of_mark (ρ : LineRepresentation k (plane k))
    (p : 𝟙_ (SchemeOver k) ⟶ projectiveLine k) (i : Index.{u})
    (h : HasCoordinates ρ (baseTest k) (toUnit _ ≫ p)
      (fun j => if j.down = i.down then 1 else 0))
    (R : TestAlgebra k) : pointLine ρ R (toUnit _ ≫ p) = axis R i := by
  have hb : ((planeBasis k).baseChange (baseTest k)).equivFun.symm
      (fun j => if j.down = i.down then 1 else 0) = (planeBasis k).baseChange (baseTest k) i := by
    apply ((planeBasis k).baseChange (baseTest k)).equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext j
    rw [Module.Basis.equivFun_self]
    by_cases hj : j = i
    · subst j
      simp
    · have hd : j.down ≠ i.down := fun h => hj (ULift.ext h)
      simp [hd, Ne.symm hj]
  change pointLine ρ (baseTest k) (toUnit _ ≫ p) = _ at h
  rw [hb] at h
  let b : baseTest k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have ht : (mapPoints b (toUnit _ ≫ p) : Points (projectiveLine k) R) = toUnit _ ≫ p := by
    simp only [mapPoints, ← Category.assoc, comp_toUnit]
  rw [← ht, pointLine_natural, h]
  exact axis_natural b i

private theorem matrixTransport_column (R : TestAlgebra k)
    (m : Matrix.GeneralLinearGroup Index.{u} R) (i j : Index.{u}) :
    ((planeBasis k).baseChange R).equivFun
        (PluckerEmbedding.matrixTransport (planeBasis k) R m ((planeBasis k).baseChange R i)) j =
      m.val j i := by
  let b := (planeBasis k).baseChange R
  change b.equivFun ((Matrix.GeneralLinearGroup.toLin' b m).toLinearEquiv (b i)) j = _
  rw [Matrix.GeneralLinearGroup.toLin'_apply, Module.Basis.repr_self]
  have h : ((Finsupp.single i 1 : Index →₀ R) : Index → R) = Pi.single i 1 := by
    funext l
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [h, Matrix.mulVec_single_one]
  change b.equivFun (∑ l, m.val l i • b l) j = _
  rw [← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

private theorem axis_map_eq_iff (R : TestAlgebra k) (m : Matrix.GeneralLinearGroup Index.{u} R)
    (i j : Index.{u}) :
    (axis R i).map (PluckerEmbedding.matrixTransport (planeBasis k) R m).toLinearMap = axis R j ↔
      (∀ l, l ≠ j → m.val l i = 0) ∧ IsUnit (m.val j i) := by
  let e := ((planeBasis k).baseChange R).equivFun
  let f := PluckerEmbedding.matrixTransport (planeBasis k) R m
  let b := (planeBasis k).baseChange R
  rw [axis, axis, Submodule.map_span, Set.image_singleton]
  change R ∙ f (b i) = R ∙ b j ↔ _
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
      (h ▸ Submodule.mem_span_singleton_self (f (b i)))
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp
      (h.symm ▸ Submodule.mem_span_singleton_self (b j))
    have hr' (l : Index.{u}) := congrArg (fun v => e v l) hr
    have hs' := congrArg (fun v => e v j) hs
    have hu : s * m.val j i = 1 := by
      dsimp only [e] at hs'
      rw [map_smul, Pi.smul_apply, smul_eq_mul,
        Module.Basis.equivFun_self] at hs'
      change s * ((planeBasis k).baseChange R).equivFun
        (PluckerEmbedding.matrixTransport (planeBasis k) R m ((planeBasis k).baseChange R i)) j
        = (if j = j then 1 else 0) at hs'
      rw [matrixTransport_column] at hs'
      simpa using hs'
    refine ⟨?_, ⟨⟨m.val j i, s, (mul_comm _ _).trans hu, hu⟩, rfl⟩⟩
    intro l hl
    specialize hr' l
    dsimp only [e] at hr'
    rw [map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self] at hr'
    change r * (if j = l then 1 else 0) =
      ((planeBasis k).baseChange R).equivFun
        (PluckerEmbedding.matrixTransport (planeBasis k) R m ((planeBasis k).baseChange R i)) l at hr'
    rw [matrixTransport_column, ite_eq_right (Ne.symm hl), mul_zero] at hr'
    exact hr'.symm
  · rintro ⟨hz, hu⟩
    have he : f (b i) = m.val j i • b j := by
      apply e.injective
      funext l
      have hl := matrixTransport_column (k := k) R m i l
      change e (f (b i)) l = _ at hl
      rw [hl]
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      change m.val l i = m.val j i * (b.equivFun (b j)) l
      rw [Module.Basis.equivFun_self]
      by_cases hlj : l = j
      · subst l
        simp
      · rw [hz l hlj, ite_eq_right (Ne.symm hlj), mul_zero]
    rw [he]
    exact Submodule.span_singleton_smul_eq hu (b j)

private theorem index_cases (i : Index.{u}) : i = i0 ∨ i = i1 := by
  rcases i with ⟨i⟩
  fin_cases i <;> simp [i0, i1]

private theorem frame_action_point {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) (R : TestAlgebra k) (g : GroupPoints H R) (z : Points X R) :
    (lift g z ≫ a.smul) ≫ P.frame.hom =
      lift (g ≫ P.hom.hom.hom) (z ≫ P.frame.hom) ≫ P.action.smul := by
  rw [Category.assoc, ← P.transportsAction, ← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

private theorem projective_point_matrixAction
    {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) (R : TestAlgebra k)
    (m : Matrix.GeneralLinearGroup Index.{u} R) (z : Points (projectiveLine k) R) :
    pointLine P.coordinates R (lift (projectiveMatrixPoint P R m) z ≫ P.action.smul) =
      (pointLine P.coordinates R z).map
        (PluckerEmbedding.matrixTransport (planeBasis k) R m).toLinearMap := by
  let g := P.matrices.inv.app R m
  have hg : P.matrices.hom.app R g = m := by
    exact congrArg (fun f : (StandardGroups.generalLinearPoints k Index).obj R ⟶
      (StandardGroups.generalLinearPoints k Index).obj R => f m) (P.matrices.inv_hom_id_app R)
  have h := P.matrixAction R g z
  change pointLine _ R
    (lift (projectiveMatrixPoint P R m) z ≫ P.action.smul) =
      (pointLine P.coordinates R z).map _ at h
  rw [hg] at h
  exact h

private theorem sends_axis_iff {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) (R : TestAlgebra k)
    (g : GroupPoints H R) (m : Matrix.GeneralLinearGroup Index.{u} R)
    (hm : g ≫ P.hom.hom.hom = projectiveMatrixPoint P R m)
    (p q : Points X R) (i j : Index.{u})
    (hp : pointLine P.coordinates R (p ≫ P.frame.hom) = axis R i)
    (hq : pointLine P.coordinates R (q ≫ P.frame.hom) = axis R j) :
    lift g p ≫ a.smul = q ↔ (∀ l, l ≠ j → m.val l i = 0) ∧ IsUnit (m.val j i) := by
  rw [← (cancel_mono P.frame.hom), frame_action_point, hm,
    ← (pointLine_injective P.coordinates R).eq_iff]
  rw [projective_point_matrixAction, hp, hq, axis_map_eq_iff]

private theorem infinity_axis {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) (R : TestAlgebra k) :
    pointLine P.coordinates R (toUnit _ ≫ x ≫ P.frame.hom) = axis R i0 :=
  axis_of_mark P.coordinates (x ≫ P.frame.hom) i0 P.infinityCoordinates R

private theorem zero_axis {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) (R : TestAlgebra k) :
    pointLine P.coordinates R (toUnit _ ≫ y ≫ P.frame.hom) = axis R i1 :=
  axis_of_mark P.coordinates (y ≫ P.frame.hom) i1 P.zeroCoordinates R

section WordAction

variable {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {infinity zero : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a infinity zero) (A : AdditiveLine k) (U V : ClosedSubgroup H)
    (p : TransvectionParametrization P A U i0 i1 i0_ne_i1)
    (n : TransvectionParametrization P A V i1 i0 i1_ne_i0)
    (R : TestAlgebra k) (b : Rˣ)

private abbrev wordPoint : GroupPoints H R :=
  rankOneWord (p.root.hom ≫ U.inclusion) (n.root.hom ≫ V.inclusion) R b

/-- The word exchanges the two marked points over every test algebra. -/
theorem rankOneWord_swaps_marks :
    (lift (wordPoint P A U V p n R b) (toUnit _ ≫ infinity) ≫ a.smul = toUnit _ ≫ zero) ∧
    (lift (wordPoint P A U V p n R b) (toUnit _ ≫ zero) ≫ a.smul = toUnit _ ≫ infinity) := by
  let w := wordPoint P A U V p n R b
  let m := wordMatrix.{u} b
  have hm : w ≫ P.hom.hom.hom = projectiveMatrixPoint P R m :=
    rankOneWord_projective P A U V p n R b
  have h0 := infinity_axis P R
  have h1 := zero_axis P R
  have he := wordMatrix_entries.{u} b
  refine ⟨(sends_axis_iff P R w m hm _ _ i0 i1 h0 h1).mpr ⟨?_, ?_⟩,
    (sends_axis_iff P R w m hm _ _ i1 i0 h1 h0).mpr ⟨?_, ?_⟩⟩
  · intro l hl
    rw [(index_cases l).resolve_right hl]
    exact he.1
  · rw [he.2.2.1]
    exact (b⁻¹).isUnit.neg
  · intro l hl
    rw [(index_cases l).resolve_left hl]
    exact he.2.2.2
  · rw [he.2.1]
    exact b.isUnit

/-- The normalized word fixes the two marked points over every test algebra. -/
theorem normalizedRankOneWord_fixes_marks :
    let w := wordPoint P A U V p n R b * (wordPoint P A U V p n R 1)⁻¹
    Stabilizes a.smul infinity w ∧ Stabilizes a.smul zero w := by
  dsimp only
  let w := wordPoint P A U V p n R b * (wordPoint P A U V p n R 1)⁻¹
  let m := wordMatrix.{u} b * (wordMatrix.{u} (1 : Rˣ))⁻¹
  have hm : w ≫ P.hom.hom.hom = projectiveMatrixPoint P R m := by
    let f := (((groupPointsFunctor k).map P.hom).app R).hom
    change f (_ * _) = projectiveMatrixPoint P R (_ * _)
    rw [map_mul, map_inv, map_mul, map_inv]
    exact congrArg₂ (· * ·) (rankOneWord_projective P A U V p n R b)
      (congrArg Inv.inv (rankOneWord_projective P A U V p n R 1))
  have he : m.val = Matrix.diagonal (fun i : Index.{u} => if i = i0 then (b : R) else (↑b⁻¹ : R)) :=
    normalizedWordMatrix b
  have hdiag (i : Index.{u}) : (∀ j, j ≠ i → m.val j i = 0) ∧ IsUnit (m.val i i) := by
    constructor
    · intro j hj
      rw [he, Matrix.diagonal_apply_ne _ hj]
    · rw [he, Matrix.diagonal_apply_eq]
      split
      · exact b.isUnit
      · exact (b⁻¹).isUnit
  have h0 := infinity_axis P R
  have h1 := zero_axis P R
  exact ⟨(sends_axis_iff P R w m hm _ _ i0 i0 h0 h0).mpr (hdiag i0),
    (sends_axis_iff P R w m hm _ _ i1 i1 h1 h1).mpr (hdiag i1)⟩

end WordAction



private theorem faithfullyFlat_of_fppf {R S : TestAlgebra k} (b : R ⟶ S)
    (hb : Fppf.IsFppf ((testSpec k).map b.op).left) : b.hom.toRingHom.FaithfullyFlat :=
  (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom b.hom.toRingHom)).mp ⟨hb.1, hb.2.1⟩

private theorem projectiveMatrixPoint_natural {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) {R S : TestAlgebra k} (b : R ⟶ S)
    (m : Matrix.GeneralLinearGroup Index.{u} R) :
    mapPoints b (projectiveMatrixPoint P R m) =
      projectiveMatrixPoint P S (m.map b.hom.toRingHom) := by
  let τ := P.matrices.inv ≫ (groupPointsFunctor k).map P.quotient
  exact congrArg (fun f : (StandardGroups.generalLinearPoints k Index).obj R ⟶
    ((groupPointsFunctor k).obj P.projectiveGroup.val).obj S => f m) (τ.naturality b).symm

private theorem eq_of_mapPoints_fppf {R S : TestAlgebra k} {X : SchemeOver k} (b : R ⟶ S)
    (hb : Fppf.IsFppf ((testSpec k).map b.op).left) {g g' : Points X R}
    (h : mapPoints b g = mapPoints b g') : g = g' := by
  let f := ((testSpec k).map b.op).left
  letI : Flat f := hb.1
  letI : Surjective f := hb.2.1
  letI := Flat.epi_of_flat_of_surjective f
  apply Over.OverMorphism.ext
  apply (cancel_epi f).mp
  exact congrArg Over.Hom.left h

private theorem matrices_with_same_projective_image {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) (hP : HasScalarKernel P)
    (R : TestAlgebra k) {m n : Matrix.GeneralLinearGroup Index.{u} R}
    (h : projectiveMatrixPoint P R m = projectiveMatrixPoint P R n) :
    ∃ v : Rˣ, m = Matrix.GeneralLinearGroup.scalar Index v * n := by
  have hf : projectiveMatrixPoint P R (m * n⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨v, hv⟩ := hP R (P.matrices.inv.app R (m * n⁻¹)) hf
  have hmn : (P.matrices.hom.app R) ((P.matrices.inv.app R) (m * n⁻¹)) = m * n⁻¹ :=
    congrArg (fun f : (StandardGroups.generalLinearPoints k Index).obj R ⟶
      (StandardGroups.generalLinearPoints k Index).obj R => f (m * n⁻¹))
      (P.matrices.inv_hom_id_app R)
  rw [hmn] at hv
  exact ⟨v, mul_inv_eq_iff_eq_mul.mp hv⟩

private theorem scalar_matrix_mul_apply {R : Type*} [CommRing R]
    (v : Rˣ) (n : Matrix.GeneralLinearGroup Index.{u} R) (i j : Index.{u}) :
    (Matrix.GeneralLinearGroup.scalar Index v * n).val i j = v.val * n.val i j := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Matrix.smul_apply, smul_eq_mul]

private theorem normalizedMatrix_eq_of_projectiveImage {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) (hP : HasScalarKernel P)
    (R : TestAlgebra k) {m n : Matrix.GeneralLinearGroup Index.{u} R}
    (i j : Index.{u}) (hm : m.val i j = 1) (hn : n.val i j = 1)
    (h : projectiveMatrixPoint P R m = projectiveMatrixPoint P R n) : m = n := by
  obtain ⟨v, hv⟩ := matrices_with_same_projective_image P hP R h
  have he := congrArg (fun g : Matrix.GeneralLinearGroup Index R => g.val i j) hv
  change m.val i j = _ at he
  rw [hm, scalar_matrix_mul_apply, hn, mul_one] at he
  have hv1 : v = 1 := Units.ext he.symm
  simpa [hv1] using hv

/-- A projective matrix with a prescribed entry equal to one descends from a
faithfully flat lift, using scalar uniqueness on the double overlap. -/
theorem descendNormalizedMatrix {H : GroupScheme k} {X : SchemeOver k}
    {a : ModObj H.X X} {x y : 𝟙_ (SchemeOver k) ⟶ X}
    (P : ProjectiveAction a x y) (hP : HasScalarKernel P)
    {R S : TestAlgebra k} (b : R ⟶ S) (hb : Fppf.IsFppf ((testSpec k).map b.op).left)
    (g : GroupPoints P.projectiveGroup.val R) (m : Matrix.GeneralLinearGroup Index.{u} S)
    (hm : projectiveMatrixPoint P S m = mapPoints b g)
    (i j : Index.{u}) (hij : m.val i j = 1) :
    ∃ n : Matrix.GeneralLinearGroup Index.{u} R, n.map b.hom.toRingHom = m ∧
      projectiveMatrixPoint P R n = g := by
  have hbflat := faithfullyFlat_of_fppf b hb
  letI : Algebra R S := b.hom.toAlgebra
  letI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' (b.hom.comp_algebraMap).symm
  letI : Module.FaithfullyFlat R S := hbflat
  let D := CommAlgCat.of k (S ⊗[R] S)
  let l' : S →ₐ[R] (S ⊗[R] S) := Algebra.TensorProduct.includeLeft
  let r' : S →ₐ[R] (S ⊗[R] S) := Algebra.TensorProduct.includeRight
  let l : S ⟶ D := CommAlgCat.ofHom (l'.restrictScalars k)
  let r : S ⟶ D := CommAlgCat.ofHom (r'.restrictScalars k)
  have hbase : b ≫ l = b ≫ r := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change (b.hom z) ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] (b.hom z)
    change (algebraMap R S z) ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] (algebraMap R S z)
    rw [Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul (R := R) z (1 : S) (1 : S)
  have hh : projectiveMatrixPoint P D (m.map l.hom.toRingHom) =
      projectiveMatrixPoint P D (m.map r.hom.toRingHom) := by
    rw [← projectiveMatrixPoint_natural P l, ← projectiveMatrixPoint_natural P r, hm]
    simpa only [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp] using
      congrArg (fun f : R ⟶ D => mapPoints f g) hbase
  have hentries (b' : S ⟶ D) :
      (m.map b'.hom.toRingHom).val i j = 1 := by
    rw [Matrix.GeneralLinearGroup.map_apply, hij, map_one]
  have hn := normalizedMatrix_eq_of_projectiveImage P hP D i j (hentries l) (hentries r) hh
  have descend (p : Matrix Index.{u} Index.{u} S)
      (hp : p.map l.hom.toRingHom = p.map r.hom.toRingHom) :
      ∃ q : Matrix Index.{u} Index.{u} R, q.map b.hom.toRingHom = p := by
    have hex (s t : Index.{u}) : ∃ z : R, algebraMap R S z = p s t := by
      have he := congrFun (congrFun hp s) t
      change Algebra.TensorProduct.includeLeftRingHom (p s t) =
        Algebra.TensorProduct.includeRight.toRingHom (p s t) at he
      have h := Algebra.IsEffective.eqLocus_includeLeft_includeRight
        (Algebra.IsEffective.of_faithfullyFlat (R := R) (S := S))
      change p s t ∈ Set.range (algebraMap R S)
      rw [← h]
      exact he
    choose q hq using hex
    exact ⟨q, Matrix.ext hq⟩
  obtain ⟨n, hnv⟩ := descend m.val (congrArg Units.val hn)
  obtain ⟨nin, hniv⟩ := descend (m⁻¹).val (congrArg (fun u => (u⁻¹).val) hn)
  let f := b.hom.toRingHom
  have hmul (M N : Matrix Index.{u} Index.{u} R) (v w : Matrix.GeneralLinearGroup Index.{u} S)
      (hM : M.map f = v.val) (hN : N.map f = w.val) (hu : v * w = 1) : M * N = 1 := by
    apply Matrix.map_injective (f := f) hbflat.injective
    change f.mapMatrix (M * N) = f.mapMatrix 1
    rw [map_mul, map_one]
    change M.map f * N.map f = 1
    rw [hM, hN]
    exact congrArg Units.val hu
  let n' : Matrix.GeneralLinearGroup Index.{u} R :=
    ⟨n, nin, hmul n nin m m⁻¹ hnv hniv (mul_inv_cancel m),
      hmul nin n m⁻¹ m hniv hnv (inv_mul_cancel m)⟩
  have hn' : n'.map b.hom.toRingHom = m := Units.ext hnv
  refine ⟨n', hn', eq_of_mapPoints_fppf b hb ?_⟩
  rw [projectiveMatrixPoint_natural, hn', hm]



private theorem polynomialEndo_injective_of_surjective (f : Polynomial k →ₐ[k] Polynomial k)
    (hf : Function.Surjective f) : Function.Injective f := by
  let v := f Polynomial.X
  have he : f = Polynomial.aeval v := by
    exact Polynomial.algHom_ext (Polynomial.aeval_X v).symm
  obtain ⟨p, hp⟩ := hf Polynomial.X
  have hdeg : p.natDegree * v.natDegree = 1 := by
    rw [← Polynomial.natDegree_comp, Polynomial.comp_eq_aeval, ← he, hp, Polynomial.natDegree_X]
  have hv : v.natDegree = 1 := by
    apply Nat.dvd_one.mp
    exact ⟨p.natDegree, hdeg.symm.trans (mul_comm _ _)⟩
  intro x y hxy
  apply sub_eq_zero.mp
  have h0 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [he, ← Polynomial.comp_eq_aeval] at h0
  rcases Polynomial.comp_eq_zero_iff.mp h0 with h | ⟨_, h⟩
  · exact h
  · have hh := congrArg Polynomial.natDegree h
    rw [hv, Polynomial.natDegree_C] at hh
    contradiction

/-- A closed immersion between two copies of the split additive group is an
isomorphism, by the polynomial coordinate ring. -/
theorem additiveLine_closedImmersion_isIso (A B : AdditiveLine k) (f : A.group ⟶ B.group)
    (h : IsClosedImmersion f.hom.hom.left) : IsIso f := by
  letI := h
  letI : IsAffine B.group.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial k))))
  let Φ := algSpec.fullyFaithful (R := CommRingCat.of k)
  let F : CommAlgCat.of k (Polynomial k) ⟶ CommAlgCat.of k (Polynomial k) :=
    (Φ.preimage f.hom.hom).unop
  let g := CommRingCat.ofHom F.hom.toRingHom
  have hmap : Spec.map g = f.hom.hom.left :=
    congrArg Over.Hom.left (Φ.map_preimage f.hom.hom)
  let e := Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))
  have he : e.inv ≫ f.hom.hom.left.appTop ≫ e.hom = g := by
    rw [← hmap, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine f.hom.hom.left).2
  have hg : Function.Surjective F.hom := by
    have hg' : Function.Surjective g := by
      rw [← he]
      exact (ConcreteCategory.bijective_of_isIso e.hom).2.comp
        (hsurj.comp (ConcreteCategory.bijective_of_isIso e.inv).2)
    exact hg'
  have hinj := polynomialEndo_injective_of_surjective F.hom hg
  have hG : Function.Injective f.hom.hom.left.appTop := by
    intro a b hab
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.inv).2 a
    obtain ⟨d, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.inv).2 b
    have eq : g c = g d := by
      rw [← he]
      exact congrArg e.hom hab
    rw [hinj eq]
  haveI : IsIso ((Over.forget _).map f.hom.hom) := by
    change IsIso f.hom.hom.left
    exact IsClosedImmersion.isIso_of_injective_of_isAffine hG
  haveI : IsIso f.hom.hom := isIso_of_reflects_iso f.hom.hom (Over.forget _)
  let i := asIso f.hom.hom
  haveI : IsMonHom i.hom := inferInstanceAs (IsMonHom f.hom.hom)
  let j := Grp.mkIso' i
  have hj : j.hom = f := by
    apply Grp.hom_ext
    change i.hom = f.hom.hom
    rfl
  rw [← hj]
  infer_instance



private theorem centralizes_of_opposite_limits {H : GroupScheme k} (ha : IsAffine H.X.left)
    (c : Cocharacter H) {R : TestAlgebra k} (g : GroupPoints H R)
    (hp : HasExtension c g) (hn : HasExtension (oppositeCocharacter c) g) : Centralizes c g := by
  obtain ⟨z, f, hf, hf0⟩ := hp
  obtain ⟨_, y, hy, _⟩ := hn
  have he : mapPoints (polynomialToLaurent R) y =
      mapPoints (invertLaurent R) (mapPoints (polynomialToLaurent R) f) := by
    rw [hy, hf, orbit_opposite]
  have hc := polynomial_family_constant_of_reverse ha f y he
  rw [hf0] at hc
  have hconst : orbit c g = mapPoints (laurentConstants R) z := by
    rw [← hf, hc, ← mapPoints_comp, polynomialConstants_laurent]
  have hg := congrArg (mapPoints (X := H.X) (evalLaurent (𝟙 R) (1 : Rˣ))) hconst
  rw [orbit_eval, ← mapPoints_comp, evalLaurent_constants] at hg
  have hunit : cocharacterPoint c R 1 = 1 := by
    simp only [cocharacterPoint, ← unitPointHom_apply, map_one]
  rw [hunit] at hg
  have hid (a : GroupPoints H R) : mapPoints (𝟙 R) a = a := by
    change (testSpec k).map (𝟙 (op R)) ≫ a = a
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hid, hid, one_mul, inv_one, mul_one] at hg
  exact (orbit_constant_iff g).mpr (hconst.trans (congrArg (mapPoints (laurentConstants R)) hg.symm))

/-- The simultaneous stabilizer of the two marked cosets is the shared Levi torus. -/
theorem fixes_marked_cosets_iff {H : GroupScheme k} (ha : IsAffine H.X.left)
    {T : ClosedSubgroup H} {c : Cocharacter H}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hT : SameSubgroup D.centralizer T) (hB : AreTwoBorels T D.parabolic E.parabolic)
    {Q : QuotientEmbedding.Presentation D.parabolic}
    (F : FlagIdentification T D.parabolic E.parabolic E.contracting Q)
    (R : TestAlgebra k) (g : GroupPoints H R) :
    (Stabilizes F.action.smul (η[H.X] ≫ Q.projection) g ∧
      Stabilizes F.action.smul (F.normalizerPoint ≫ Q.projection) g) ↔
      ∃ t : GroupPoints T.group R, t ≫ T.inclusion.hom.hom = g := by
  constructor
  · rintro ⟨hpos, hneg⟩
    have hp := (F.positiveStabilizer _ g).mp hpos
    have hn := (F.negativeStabilizer _ g).mp hneg
    have hc := centralizes_of_opposite_limits ha c g
      ((D.parabolic_points R g).mpr hp) ((E.parabolic_points R g).mpr hn)
    obtain ⟨d, hd⟩ := (D.centralizer_points _ g).mp hc
    obtain ⟨i, hi⟩ := hT.1
    refine ⟨d ≫ i.hom.hom, ?_⟩
    rw [Category.assoc, show i.hom.hom ≫ T.inclusion.hom.hom = D.centralizer.inclusion.hom.hom from
      congrArg (fun f : D.centralizer.group ⟶ H => f.hom.hom) hi, hd]
  · rintro ⟨t, rfl⟩
    obtain ⟨_, _, _, ⟨i, hi⟩, ⟨j, hj⟩, _⟩ := hB
    refine ⟨(F.positiveStabilizer _ _).mpr ⟨t ≫ i.hom.hom, ?_⟩,
      (F.negativeStabilizer _ _).mpr ⟨t ≫ j.hom.hom, ?_⟩⟩
    · rw [Category.assoc]
      exact congrArg (fun f : T.group ⟶ H => t ≫ f.hom.hom) hi
    · rw [Category.assoc]
      exact congrArg (fun f : T.group ⟶ H => t ≫ f.hom.hom) hj



private theorem index_cases_pair {i j : Index.{u}} (hij : i ≠ j) (l : Index.{u}) :
    l = i ∨ l = j := by
  rcases index_cases i with rfl | rfl
  · rcases index_cases j with rfl | rfl
    · exact (hij rfl).elim
    · exact index_cases l
  · rcases index_cases j with rfl | rfl
    · exact (index_cases l).symm
    · exact (hij rfl).elim

private theorem entry_expand_pair {R : Type*} [CommRing R]
    {i j : Index.{u}} (hij : i ≠ j) (M N : Matrix Index.{u} Index.{u} R)
    (r s : Index.{u}) : (M * N) r s = M r i * N i s + M r j * N j s := by
  rw [entry_expand]
  rcases index_cases i with rfl | rfl
  · rw [(index_cases j).resolve_left (Ne.symm hij)]
  · rw [(index_cases j).resolve_right (Ne.symm hij), add_comm]

private theorem mapPoints_stabilizes {H : GroupScheme k} {Y : SchemeOver k}
    (a : ModObj H.X Y) (z : 𝟙_ (SchemeOver k) ⟶ Y)
    {R S : TestAlgebra k} (b : R ⟶ S) {g : GroupPoints H R}
    (hg : Stabilizes a.smul z g) : Stabilizes a.smul z (mapPoints b g) := by
  unfold Stabilizes at hg ⊢
  let t := (testSpec k).map b.op
  have he := congrArg (fun f => t ≫ f) hg
  rw [← Category.assoc, comp_lift, ← Category.assoc (f := t)] at he
  have ht : t ≫ toUnit ((testSpec k).obj (op R)) = toUnit ((testSpec k).obj (op S)) :=
    toUnit_unique _ _
  change lift (mapPoints b g) ((t ≫ toUnit ((testSpec k).obj (op R))) ≫ z) ≫ a.smul =
    (t ≫ toUnit ((testSpec k).obj (op R))) ≫ z at he
  rw [ht] at he
  exact he

private theorem normalized_triangular_lift {H : GroupScheme k} {Y : SchemeOver k}
    {a : ModObj H.X Y} {x y : 𝟙_ (SchemeOver k) ⟶ Y}
    (P : ProjectiveAction a x y) (hscalar : HasScalarKernel P)
    (hP : ProjectiveMatrixPresentation P)
    (z : 𝟙_ (SchemeOver k) ⟶ Y) {i j : Index.{u}} (hij : i ≠ j)
    (hz : ∀ R : TestAlgebra k, pointLine P.coordinates R (toUnit _ ≫ z ≫ P.frame.hom) = axis R i)
    (R : TestAlgebra k) (g : GroupPoints H R) (hg : Stabilizes a.smul z g) :
    ∃ M : Matrix.GeneralLinearGroup Index.{u} R, M.val j i = 0 ∧ M.val j j = 1 ∧
      IsUnit (M.val i i) ∧ projectiveMatrixPoint P R M = g ≫ P.hom.hom.hom := by
  obtain ⟨S, b, m, hb, hm⟩ := hP.lifts R (g ≫ P.hom.hom.hom)
  have hmeq : mapPoints b g ≫ P.hom.hom.hom = projectiveMatrixPoint P S m := hm.symm
  have htri := (sends_axis_iff P S (mapPoints b g) m hmeq _ _ i i (hz S) (hz S)).mp
    (mapPoints_stabilizes a z b hg)
  have hji := htri.1 j (Ne.symm hij)
  have huu := congrArg (fun n : Matrix.GeneralLinearGroup Index S => n.val j j) (mul_inv_cancel m)
  change (m.val * (m⁻¹).val) j j = (1 : Matrix Index Index S) j j at huu
  rw [entry_expand_pair hij, hji, zero_mul, zero_add, Matrix.one_apply_eq] at huu
  let u : Sˣ := ⟨m.val j j, (m⁻¹).val j j, huu, (mul_comm _ _).trans huu⟩
  let n := Matrix.GeneralLinearGroup.scalar Index u⁻¹ * m
  have hnjj : n.val j j = 1 := by
    rw [scalar_matrix_mul_apply]
    exact u.inv_val
  have hnji : n.val j i = 0 := by
    rw [scalar_matrix_mul_apply, hji, mul_zero]
  have hnp : projectiveMatrixPoint P S n = mapPoints b (g ≫ P.hom.hom.hom) := by
    rw [map_mul, hP.scalar, one_mul, hm]
  obtain ⟨M, hM, hproj⟩ := descendNormalizedMatrix P hscalar b hb _ n hnp j j hnjj
  have hval (r s : Index.{u}) : b.hom (M.val r s) = n.val r s := by
    exact congrArg (fun t : Matrix.GeneralLinearGroup Index S => t.val r s) hM
  have hinj := (faithfullyFlat_of_fppf b hb).injective
  have hMj : M.val j i = 0 := hinj ((hval j i).trans (hnji.trans (map_zero b.hom).symm))
  have hM1 : M.val j j = 1 := hinj ((hval j j).trans (hnjj.trans (map_one b.hom).symm))
  have hMU := congrArg (fun t : Matrix.GeneralLinearGroup Index R => t.val i i) (inv_mul_cancel M)
  change ((M⁻¹).val * M.val) i i = (1 : Matrix Index Index R) i i at hMU
  rw [entry_expand_pair hij, hMj, mul_zero, add_zero, Matrix.one_apply_eq] at hMU
  refine ⟨M, hMj, hM1, ?_, hproj⟩
  exact ⟨⟨M.val i i, (M⁻¹).val i i, (mul_comm _ _).trans hMU, hMU⟩, rfl⟩

private theorem additivePoints_zero (A : AdditiveLine k) (R : TestAlgebra k) :
    additivePoints A R (0 : R) = 1 := by
  have h := additivePoints_add A R 0 0
  rw [zero_add] at h
  exact (mul_left_cancel ((mul_one (additivePoints A R 0)).trans h)).symm

private theorem rootPoint_eq {A : AdditiveLine k} {H : GroupScheme k}
    (x : A.group ⟶ H) (R : TestAlgebra k) (s : R) :
    rootPoint x R s = additivePoints A R s ≫ x.hom.hom := by
  change rootPoint x R s = rootPoint (𝟙 A.group) R s ≫ x.hom.hom
  have he := rootPoint_comp (𝟙 A.group) x R s
  simpa only [Category.id_comp] using he

private theorem rootPoint_natural {A : AdditiveLine k} {H : GroupScheme k}
    (x : A.group ⟶ H) {R S : TestAlgebra k} (b : R ⟶ S) (t : R) :
    mapPoints b (rootPoint x R t) = rootPoint x S (b.hom t) := by
  rw [rootPoint_eq, rootPoint_eq]
  exact congrArg (· ≫ x.hom.hom) (additivePoints_natural A b t)

private theorem rootPoint_zero {A : AdditiveLine k} {H : GroupScheme k}
    (x : A.group ⟶ H) (R : TestAlgebra k) :
    rootPoint x R (0 : R) = 1 := by
  rw [← Category.id_comp x, rootPoint_comp]
  change additivePoints A R 0 ≫ x.hom.hom = _
  rw [additivePoints_zero, MonObj.one_comp]

private theorem transvection_map {k : Type u} [Field k] (A : AdditiveLine k)
    {i j : Index.{u}} (hij : i ≠ j)
    {R S : TestAlgebra k} (b : R ⟶ S) (r : R) :
    (Matrix.GeneralLinearGroup.transvection i j hij r).map b.hom.toRingHom =
      Matrix.GeneralLinearGroup.transvection i j hij (b.hom r) := by
  have h := (standardTransvections A i j hij).naturality b
  have he := congrArg (fun f : ((groupPointsFunctor k).obj A.group).obj R ⟶
    (StandardGroups.generalLinearPoints k Index).obj S => f (additivePoints A R r)) h
  change Matrix.GeneralLinearGroup.transvection i j hij
    ((additivePoints A S).symm (mapPoints b (additivePoints A R r))) =
    (Matrix.GeneralLinearGroup.transvection i j hij ((additivePoints A R).symm
      (additivePoints A R r))).map b.hom.toRingHom at he
  rw [additivePoints_natural, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at he
  exact he.symm

private theorem split_additive_projects_into_transvections
    {H : GroupScheme k} {Y : SchemeOver k} {a : ModObj H.X Y}
    {x y : 𝟙_ (SchemeOver k) ⟶ Y}
    (P : ProjectiveAction a x y) (hscalar : HasScalarKernel P)
    (hP : ProjectiveMatrixPresentation P)
    (z : 𝟙_ (SchemeOver k) ⟶ Y) {i j : Index.{u}} (hij : i ≠ j)
    (hz : ∀ R : TestAlgebra k, pointLine P.coordinates R (toUnit _ ≫ z ≫ P.frame.hom) = axis R i)
    {A : AdditiveLine k} (f : A.group ⟶ H)
    (hf : ∀ (R : TestAlgebra k) (s : R), Stabilizes a.smul z (rootPoint f R s)) :
    ∀ (R : TestAlgebra k) (s : R), ∃ t : R,
      rootPoint f R s ≫ P.hom.hom.hom =
        projectiveMatrixPoint P R (Matrix.GeneralLinearGroup.transvection i j hij t) := by
  let B := CommAlgCat.of k (Polynomial k)
  let X := (Polynomial.X : B)
  obtain ⟨M, hji, hjj, hii, hM⟩ := normalized_triangular_lift P hscalar hP z hij hz B
    (rootPoint f B X) (hf B X)
  let e : B ⟶ baseTest k := CommAlgCat.ofHom (Polynomial.aeval (0 : k))
  have hzero : projectiveMatrixPoint P (baseTest k) (M.map e.hom.toRingHom) = 1 := by
    rw [← projectiveMatrixPoint_natural, hM]
    change mapPoints e (rootPoint (f ≫ P.hom) B X) = _
    rw [rootPoint_natural]
    have he : e.hom X = 0 := Polynomial.aeval_X _
    rw [he, rootPoint_zero]
  have hentry : (M.map e.hom.toRingHom).val j j = 1 := by
    rw [Matrix.GeneralLinearGroup.map_apply, hjj, map_one]
  have hM0 : M.map e.hom.toRingHom = 1 :=
    normalizedMatrix_eq_of_projectiveImage P hscalar (baseTest k) j j hentry
      (Matrix.one_apply_eq _) (hzero.trans (map_one _).symm)
  have hui : M.val i i = 1 := by
    obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.mp hii
    have heval := congrArg (fun m : Matrix.GeneralLinearGroup Index (baseTest k) => m.val i i) hM0
    rw [Matrix.GeneralLinearGroup.map_apply, ← hc] at heval
    change e.hom (Polynomial.C c) = (1 : Matrix Index Index k) i i at heval
    rw [Matrix.one_apply_eq] at heval
    change Polynomial.aeval (0 : k) (Polynomial.C c) = (1 : k) at heval
    have hc1 : c = 1 := by simpa using heval
    rw [← hc, hc1, map_one]
  let d := M.val i j
  have htrans : M = Matrix.GeneralLinearGroup.transvection i j hij d := by
    apply Units.ext
    ext r s
    rcases index_cases_pair hij r with rfl | rfl <;>
      rcases index_cases_pair hij s with rfl | rfl <;>
      simp [Matrix.transvection, hij, Ne.symm hij,
        hui, hjj, hji, d]
  intro R s
  let b : B ⟶ R := CommAlgCat.ofHom (Polynomial.aeval s)
  refine ⟨b.hom d, ?_⟩
  rw [htrans] at hM
  have h := congrArg (mapPoints b) hM
  rw [projectiveMatrixPoint_natural, transvection_map A hij] at h
  change _ = mapPoints b (rootPoint (f ≫ P.hom) B X) at h
  rw [rootPoint_natural, show b.hom X = s from Polynomial.aeval_X _, rootPoint_comp] at h
  exact h.symm

private theorem transvectionParametrization_of_projective_embedding
    {H : GroupScheme k} {Y : SchemeOver k} {a : ModObj H.X Y}
    {x y : 𝟙_ (SchemeOver k) ⟶ Y}
    (P : ProjectiveAction a x y) (hscalar : HasScalarKernel P)
    (hP : ProjectiveMatrixPresentation P)
    (z : 𝟙_ (SchemeOver k) ⟶ Y) {i j : Index.{u}} (hij : i ≠ j)
    (hz : ∀ R : TestAlgebra k, pointLine P.coordinates R (toUnit _ ≫ z ≫ P.frame.hom) = axis R i)
    (A : AdditiveLine k) (U : ClosedSubgroup H) (e : A.group ≅ U.group)
    (hU : ∀ (R : TestAlgebra k) (s : GroupPoints U.group R),
      Stabilizes a.smul z (s ≫ U.inclusion.hom.hom))
    (hinj : ∀ (R : TestAlgebra k), Function.Injective
      (fun s : GroupPoints U.group R => s ≫ (U.inclusion ≫ P.hom).hom.hom)) :
    Nonempty (TransvectionParametrization P A U i j hij) := by
  let t := transvectionHom P A i j hij
  have ht := transvectionHom_closedImmersion P hscalar A i j hij
  let S : ClosedSubgroup P.projectiveGroup.val := ⟨A.group, t, ht⟩
  let f := e.hom ≫ U.inclusion
  obtain ⟨m, hm⟩ := subgroupInclusionFactors (additiveLineGroup A).property.1 S (f ≫ P.hom) (by
    intro R g
    obtain ⟨s, rfl⟩ := (additivePoints A R).surjective g
    obtain ⟨q, hq⟩ := split_additive_projects_into_transvections P hscalar hP z hij hz f
      (fun R s => by rw [rootPoint_comp]; exact hU R _) R s
    refine ⟨additivePoints A R q, ?_⟩
    change additivePoints A R q ≫ t.hom.hom = additivePoints A R s ≫ (f ≫ P.hom).hom.hom
    rw [← rootPoint_eq, transvectionHom_point, ← rootPoint_eq, rootPoint_comp]
    exact hq.symm)
  have hmono (R : TestAlgebra k) : Function.Injective
      (fun g : GroupPoints A.group R => g ≫ m.hom.hom) := by
    intro p q hpq
    have h := congrArg (· ≫ t.hom.hom) hpq
    rw [Category.assoc, Category.assoc] at h
    have hmt : m.hom.hom ≫ t.hom.hom = f.hom.hom ≫ P.hom.hom.hom :=
      congrArg (fun j : A.group ⟶ P.projectiveGroup.val => j.hom.hom) hm
    rw [hmt] at h
    apply (cancel_mono e.hom.hom.hom).mp
    apply hinj R
    change p ≫ (e.hom.hom.hom ≫ U.inclusion.hom.hom) ≫ P.hom.hom.hom =
      q ≫ (e.hom.hom.hom ≫ U.inclusion.hom.hom) ≫ P.hom.hom.hom at h
    change (p ≫ e.hom.hom.hom) ≫ U.inclusion.hom.hom ≫ P.hom.hom.hom =
      (q ≫ e.hom.hom.hom) ≫ U.inclusion.hom.hom ≫ P.hom.hom.hom
    simpa only [Category.assoc] using h
  letI := additiveLine_closedImmersion_isIso A A m
    (isClosedImmersion_of_injectivePoints (additiveLineGroup A) (additiveLineGroup A) m hmono)
  let r := (asIso m).symm ≪≫ e
  refine ⟨⟨r, t, ht, ?_, transvectionHom_point P A i j hij⟩⟩
  change inv m ≫ (e.hom ≫ U.inclusion) ≫ P.hom = t
  rw [← hm, IsIso.inv_hom_id_assoc]



private def additiveLinePointsIso (A : AdditiveLine k) :
    StandardGroups.additivePoints k ≅ (groupPointsFunctor k).obj A.group :=
  NatIso.ofComponents
    (fun R =>
      (show (StandardGroups.additivePoints k).obj R ≃* ((groupPointsFunctor k).obj A.group).obj R from
        { toFun := fun a => additivePoints A R a.toAdd
          invFun := fun p => Multiplicative.ofAdd ((additivePoints A R).symm p)
          left_inv := fun a => congrArg Multiplicative.ofAdd ((additivePoints A R).symm_apply_apply a.toAdd)
          right_inv := (additivePoints A R).apply_symm_apply
          map_mul' := fun a b => additivePoints_add A R a.toAdd b.toAdd }).toGrpIso)
    (by
      intro R S a
      apply GrpCat.ext
      intro x
      exact (additivePoints_natural A a x.toAdd).symm)




private theorem inclusion_stabilizes {H : GroupScheme k} {Y : SchemeOver k}
    (a : ModObj H.X Y) (z : 𝟙_ (SchemeOver k) ⟶ Y) (U B : ClosedSubgroup H)
    (hB : RepresentsSubgroup B (fun _ g => Stabilizes a.smul z g))
    (j : U.group ⟶ B.group) (hj : j ≫ B.inclusion = U.inclusion)
    (R : TestAlgebra k) (u : GroupPoints U.group R) :
    Stabilizes a.smul z (u ≫ U.inclusion.hom.hom) := by
  apply (hB _ _).mpr
  refine ⟨u ≫ j.hom.hom, ?_⟩
  rw [Category.assoc]
  exact congrArg (fun f : U.group ⟶ H => u ≫ f.hom.hom) hj

private theorem in_projective_kernel_fixes {H : GroupScheme k} {Y : SchemeOver k}
    {a : ModObj H.X Y} {x y : 𝟙_ (SchemeOver k) ⟶ Y}
    (P : ProjectiveAction a x y)
    {R : TestAlgebra k} {g : GroupPoints H R}
    (hg : (g ≫ P.hom.hom.hom : GroupPoints P.projectiveGroup.val R) = 1)
    (z : 𝟙_ (SchemeOver k) ⟶ Y) : Stabilizes a.smul z g := by
  letI := P.action
  change lift g (toUnit _ ≫ z) ≫ a.smul = toUnit _ ≫ z
  apply (cancel_mono P.frame.hom).mp
  rw [frame_action_point P, hg]
  let Z := (testSpec k).obj (op R)
  let p : Z ⟶ projectiveLine k := (toUnit Z ≫ z) ≫ P.frame.hom
  exact (one_smul (Z ⟶ P.projectiveGroup.val.X) p :
    (1 : Z ⟶ P.projectiveGroup.val.X) • p = p)

private theorem contracting_projective_injective {H : GroupScheme k} (ha : IsAffine H.X.left)
    {Y : SchemeOver k} {a : ModObj H.X Y} {x y : 𝟙_ (SchemeOver k) ⟶ Y}
    (P : ProjectiveAction a x y)
    (T : ClosedSubgroup H) {c : Cocharacter H} (D : LimitDecomposition c)
    (hT : SameSubgroup D.centralizer T)
    (hfix : ∀ (R : TestAlgebra k) (g : GroupPoints H R),
      Stabilizes a.smul x g → Stabilizes a.smul y g →
      ∃ t : GroupPoints T.group R, t ≫ T.inclusion.hom.hom = g)
    (R : TestAlgebra k) :
    Function.Injective (fun s : GroupPoints D.contracting.group R =>
      s ≫ (D.contracting.inclusion ≫ P.hom).hom.hom) := by
  let F := (((groupPointsFunctor k).map (D.contracting.inclusion ≫ P.hom)).app R).hom
  change Function.Injective F
  apply (injective_iff_map_eq_one F).mpr
  intro s hs
  let g : GroupPoints H R := s ≫ D.contracting.inclusion.hom.hom
  have hp : (g ≫ P.hom.hom.hom : GroupPoints P.projectiveGroup.val R) = 1 := hs
  obtain ⟨t, ht⟩ := hfix R g (in_projective_kernel_fixes P hp x) (in_projective_kernel_fixes P hp y)
  obtain ⟨j, hj⟩ := hT.2
  have hc := (D.centralizer_points _ g).mpr ⟨t ≫ j.hom.hom, by
    rw [Category.assoc, show j.hom.hom ≫ D.centralizer.inclusion.hom.hom = T.inclusion.hom.hom from
      congrArg (fun f : T.group ⟶ H => f.hom.hom) hj, ht]⟩
  letI := ha
  have hlim := (D.contracting_points R g).mpr ⟨s, rfl⟩
  have h1 := limitIsUnique c (centralizes_hasLimit c hc) hlim
  letI := mono_over D.contracting.inclusion.hom.hom D.contracting.isClosedImmersion
  apply (cancel_mono D.contracting.inclusion.hom.hom).mp
  simpa only [MonObj.one_comp] using h1

private def additiveLineIso (A B : AdditiveLine k) : A.group ≅ B.group := by
  letI := (additiveLineGroup A).property.1
  letI := (additiveLineGroup B).property.1
  exact groupIsoOfPointIso ((additiveLinePointsIso A).symm ≪≫ additiveLinePointsIso B)

/-- The two contracting groups admit matched elementary coordinates for the
action on the marked rank-one flag, over the original field. -/
private theorem rankOneTransvectionPairWithMatrices
    (projective : ProjectiveLineAutomorphisms.{u})
    {H : GroupScheme k} (ha : IsAffine H.X.left) (T : ClosedSubgroup H)
    {c : Cocharacter H} (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hplus : SameSubgroup D.centralizer T) (hminus : SameSubgroup E.centralizer T)
    (hB : AreTwoBorels T D.parabolic E.parabolic)
    (hpos : IsSplitAdditive D.contracting.group) (hneg : IsSplitAdditive E.contracting.group)
    {Q : QuotientEmbedding.Presentation D.parabolic}
    (F : FlagIdentification T D.parabolic E.parabolic E.contracting Q) :
    ∃ (P : ProjectiveAction F.action (η[H.X] ≫ Q.projection) (F.normalizerPoint ≫ Q.projection))
      (A : AdditiveLine k),
      HasScalarKernel P ∧ ProjectiveMatrixPresentation P ∧
      Nonempty (TransvectionParametrization P A D.contracting i0 i1 i0_ne_i1) ∧
      Nonempty (TransvectionParametrization P A E.contracting i1 i0 i1_ne_i0) := by
  obtain ⟨P, hs, hP⟩ := projectiveActionWithMatrices projective ha F
  obtain ⟨ap, hpd, hpe, hpi, ⟨ip⟩⟩ := hpos
  obtain ⟨an, hnd, hne, hni, ⟨inn⟩⟩ := hneg
  let A : AdditiveLine k := ⟨ap, hpd, hpe, hpi⟩
  let B : AdditiveLine k := ⟨an, hnd, hne, hni⟩
  have hf (R : TestAlgebra k) (g : GroupPoints H R)
      (hp : Stabilizes F.action.smul (η[H.X] ≫ Q.projection) g)
      (hn : Stabilizes F.action.smul (F.normalizerPoint ≫ Q.projection) g) :=
    (fixes_marked_cosets_iff ha D E hplus hB F R g).mp ⟨hp, hn⟩
  refine ⟨P, A, hs, hP, ?_, ?_⟩
  · exact transvectionParametrization_of_projective_embedding P hs hP _ i0_ne_i1
      (infinity_axis P) A D.contracting ip.symm
      (inclusion_stabilizes _ _ _ _ F.positiveStabilizer D.contractingToParabolic D.contracting_in_G)
      (contracting_projective_injective ha P T D hplus hf)
  · exact transvectionParametrization_of_projective_embedding P hs hP _ i1_ne_i0
      (zero_axis P) A E.contracting (additiveLineIso A B ≪≫ inn.symm)
      (inclusion_stabilizes _ _ _ _ F.negativeStabilizer E.contractingToParabolic E.contracting_in_G)
      (contracting_projective_injective ha P T E hminus hf)

/-- The two contracting groups admit matched elementary coordinates for the
action on the marked rank-one flag, over the original field. -/
theorem rankOneTransvectionPair
    (projective : ProjectiveLineAutomorphisms.{u})
    {H : GroupScheme k} (ha : IsAffine H.X.left) (T : ClosedSubgroup H)
    {c : Cocharacter H} (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hplus : SameSubgroup D.centralizer T) (hminus : SameSubgroup E.centralizer T)
    (hB : AreTwoBorels T D.parabolic E.parabolic)
    (hpos : IsSplitAdditive D.contracting.group) (hneg : IsSplitAdditive E.contracting.group)
    {Q : QuotientEmbedding.Presentation D.parabolic}
    (F : FlagIdentification T D.parabolic E.parabolic E.contracting Q) :
    ∃ (P : ProjectiveAction F.action (η[H.X] ≫ Q.projection) (F.normalizerPoint ≫ Q.projection))
      (A : AdditiveLine k),
      Nonempty (TransvectionParametrization P A D.contracting i0 i1 i0_ne_i1) ∧
      Nonempty (TransvectionParametrization P A E.contracting i1 i0 i1_ne_i0) := by
  obtain ⟨P, A, _, _, p, n⟩ := rankOneTransvectionPairWithMatrices projective ha T D E
    hplus hminus hB hpos hneg F
  exact ⟨P, A, p, n⟩



private theorem rankOneWord_natural {A : AdditiveLine k} {G : GroupScheme k}
    (x y : A.group ⟶ G) {R S : TestAlgebra k} (b : R ⟶ S) (t : Rˣ) :
    mapPoints b (rankOneWord x y R t) =
      rankOneWord x y S (Units.map b.hom.toMonoidHom t) := by
  let f := (((groupPointsFunctor k).obj G).map b).hom
  change f (rootPoint x R t * rootPoint y R (-(↑t⁻¹ : R)) * rootPoint x R t) = _
  rw [map_mul, map_mul]
  change mapPoints b (rootPoint x R t) * mapPoints b (rootPoint y R (-(↑t⁻¹ : R))) *
    mapPoints b (rootPoint x R t) = _
  simp only [rootPoint_natural, rankOneWord, Units.coe_map, map_neg]
  rfl

private abbrev Gm (k : Type u) [Field k] :=
  specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)

private abbrev laurentCoordinateAlgebra (k : Type u) [Field k] :=
  CommAlgCat.of k (MonoidAlgebra k DiagonalizableGroups.IntegerCharacters.{u})

private def rankOneWordMorph {A : AdditiveLine k} {G : GroupScheme k} (x y : A.group ⟶ G) :
    (Gm k).X ⟶ G.X :=
  let R := laurentCoordinateAlgebra k
  rankOneWord x y R (unitEquiv R (𝟙 (Gm k).X))

private theorem rankOneWordMorph_point {A : AdditiveLine k} {G : GroupScheme k}
    (x y : A.group ⟶ G) (R : TestAlgebra k) (t : Rˣ) :
    unitPoint R t ≫ rankOneWordMorph x y = rankOneWord x y R t := by
  let S := laurentCoordinateAlgebra k
  let a : S ⟶ R := CommAlgCat.ofHom (unitCoordinates R t)
  let b := unitEquiv S (𝟙 (Gm k).X)
  have h : unitPoint S b = 𝟙 (Gm k).X := (unitEquiv S).injective (unitEquiv_unitPoint S b)
  have hmap : mapPoints a (unitPoint S b) = unitPoint R t := by
    rw [h, mapPoints]
    change (testSpec k).map a.op ≫ 𝟙 ((testSpec k).obj (op S)) = _
    rw [Category.comp_id]
    rfl
  rw [mapPoints_unitPoint] at hmap
  have ha : Units.map a.hom.toMonoidHom b = t :=
    (unitEquiv_unitPoint R _).symm.trans
      ((congrArg (unitEquiv R) hmap).trans (unitEquiv_unitPoint R _))
  change mapPoints a (rankOneWord x y S b) = _
  rw [rankOneWord_natural, ha]

private def rankOneRepresentative {A : AdditiveLine k} {G : GroupScheme k}
    (x y : A.group ⟶ G) : 𝟙_ (SchemeOver k) ⟶ G.X :=
  η[(Gm k).X] ≫ rankOneWordMorph x y

private theorem rankOneRepresentative_point {A : AdditiveLine k} {G : GroupScheme k}
    (x y : A.group ⟶ G) (R : TestAlgebra k) :
    toUnit _ ≫ rankOneRepresentative x y = rankOneWord x y R 1 := by
  have h : unitPoint R 1 = (1 : GroupPoints (Gm k) R) := by
    rw [← unitPointHom_apply, map_one]
  rw [rankOneRepresentative, ← Category.assoc]
  change (1 : GroupPoints (Gm k) R) ≫ rankOneWordMorph x y = _
  rw [← h, rankOneWordMorph_point]

private theorem normalizes_of_swapping_marks {H : GroupScheme k} {Y : SchemeOver k}
    (a : ModObj H.X Y) (T : ClosedSubgroup H) (p q : 𝟙_ (SchemeOver k) ⟶ Y)
    (hT : ∀ (R : TestAlgebra k) (g : GroupPoints H R),
      (Stabilizes a.smul p g ∧ Stabilizes a.smul q g) ↔
        ∃ t : GroupPoints T.group R, t ≫ T.inclusion.hom.hom = g)
    (n : 𝟙_ (SchemeOver k) ⟶ H.X)
    (hswap : ∀ R : TestAlgebra k,
      (lift (toUnit _ ≫ n) (toUnit _ ≫ p) ≫ a.smul : Points Y R) = toUnit _ ≫ q ∧
      (lift (toUnit _ ≫ n) (toUnit _ ≫ q) ≫ a.smul : Points Y R) = toUnit _ ≫ p) :
    Normalizes T.inclusion n := by
  letI := a
  have hle (w : 𝟙_ (SchemeOver k) ⟶ H.X)
      (hw : ∀ R : TestAlgebra k,
        (lift (toUnit _ ≫ w) (toUnit _ ≫ p) ≫ a.smul : Points Y R) = toUnit _ ≫ q ∧
        (lift (toUnit _ ≫ w) (toUnit _ ≫ q) ≫ a.smul : Points Y R) = toUnit _ ≫ p) :
      ConjugateLe T.inclusion w := by
    apply (CocharacterDynamics.factorsThroughClosed_iff _ T.isClosedImmersion _).mpr
    intro R f
    let Z := (testSpec k).obj (op R)
    let u : Z ⟶ H.X := toUnit _ ≫ w
    let t : Z ⟶ T.group.X := f ≫ fst _ _
    let g : Z ⟶ H.X := t ≫ T.inclusion.hom.hom
    let x : Z ⟶ Y := toUnit _ ≫ p
    let y : Z ⟶ Y := toUnit _ ≫ q
    have hx : u • x = y := (hw R).1
    have hy : u • y = x := (hw R).2
    have hxi : u⁻¹ • x = y := inv_smul_eq_iff.mpr hy.symm
    have hyi : u⁻¹ • y = x := inv_smul_eq_iff.mpr hx.symm
    have hf := (hT R g).mpr ⟨t, rfl⟩
    have hfx : g • x = x := hf.1
    have hfy : g • y = y := hf.2
    have hpx : (u * g * u⁻¹) • x = x := by rw [mul_smul, hxi, mul_smul, hfy, hy]
    have hpy : (u * g * u⁻¹) • y = y := by rw [mul_smul, hyi, mul_smul, hfx, hx]
    obtain ⟨z, hz⟩ := (hT R (u * g * u⁻¹)).mp ⟨hpx, hpy⟩
    refine ⟨z, ?_⟩
    rw [hz, comp_conjugateFamily, ← Category.assoc (f := f) (g := snd _ _)]
    rw [toUnit_unique (f ≫ snd T.group.X (𝟙_ (SchemeOver k))) (toUnit _)]
    rfl
  apply (normalizesIff k T.inclusion T.isClosedImmersion _ n).mpr
  refine ⟨hle n hswap, hle n⁻¹ ?_⟩
  intro R
  let Z := (testSpec k).obj (op R)
  let u : Z ⟶ H.X := toUnit _ ≫ n
  let x : Z ⟶ Y := toUnit _ ≫ p
  let y : Z ⟶ Y := toUnit _ ≫ q
  have hx : u • x = y := (hswap R).1
  have hy : u • y = x := (hswap R).2
  have hi : (toUnit _ ≫ n⁻¹ : Z ⟶ H.X) = u⁻¹ := GrpObj.comp_inv _ _
  change (toUnit _ ≫ n⁻¹ : Z ⟶ H.X) • x = y ∧
    (toUnit _ ≫ n⁻¹ : Z ⟶ H.X) • y = x
  rw [hi]
  exact ⟨inv_smul_eq_iff.mpr hy.symm, inv_smul_eq_iff.mpr hx.symm⟩

/-- The matched word at one gives a rational point in the normalizer, and
the normalized word factors through the common torus over the ground field. -/
theorem matchedWord_in_torus_and_normalizer
    {H : GroupScheme k} (ha : IsAffine H.X.left) (T : ClosedSubgroup H)
    {c : Cocharacter H} (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hT : SameSubgroup D.centralizer T) (hB : AreTwoBorels T D.parabolic E.parabolic)
    {Q : QuotientEmbedding.Presentation D.parabolic}
    (F : FlagIdentification T D.parabolic E.parabolic E.contracting Q)
    (P : ProjectiveAction F.action (η[H.X] ≫ Q.projection) (F.normalizerPoint ≫ Q.projection))
    (A : AdditiveLine k)
    (p : TransvectionParametrization P A D.contracting i0 i1 i0_ne_i1)
    (n : TransvectionParametrization P A E.contracting i1 i0 i1_ne_i0) :
    let x := p.root.hom ≫ D.contracting.inclusion
    let y := n.root.hom ≫ E.contracting.inclusion
    ∃ (w : 𝟙_ (SchemeOver k) ⟶ H.X) (d : (Gm k).X ⟶ T.group.X),
      Normalizes T.inclusion w ∧ η[(Gm k).X] ≫ d = η[T.group.X] ∧
      (∀ R : TestAlgebra k, toUnit _ ≫ w = rankOneWord x y R (1 : Rˣ)) ∧
      ∀ (R : TestAlgebra k) (b : Rˣ), unitPoint R b ≫ d ≫ T.inclusion.hom.hom =
        rankOneWord x y R b * (rankOneWord x y R 1)⁻¹ := by
  dsimp only
  let x := p.root.hom ≫ D.contracting.inclusion
  let y := n.root.hom ≫ E.contracting.inclusion
  let w := rankOneRepresentative x y
  let δ := rankOneWordMorph x y * (toUnit _ ≫ w)⁻¹
  have hw (R : TestAlgebra k) : toUnit _ ≫ w = rankOneWord x y R (1 : Rˣ) :=
    rankOneRepresentative_point x y R
  have hword (R : TestAlgebra k) (b : Rˣ) :
      unitPoint R b ≫ δ = rankOneWord x y R b * (rankOneWord x y R 1)⁻¹ := by
    dsimp only [δ]
    rw [MonObj.comp_mul, GrpObj.comp_inv, rankOneWordMorph_point, ← Category.assoc, comp_toUnit, hw]
  have ht := fixes_marked_cosets_iff ha D E hT hB F
  have hfactor := (CocharacterDynamics.factorsThroughClosed_iff _ T.isClosedImmersion δ).mpr
    (by
      intro R g
      let b := unitEquiv R g
      have h : unitPoint R b = g := (unitEquiv R).injective (unitEquiv_unitPoint R b)
      rw [← h, hword]
      exact (ht R _).mp (normalizedRankOneWord_fixes_marks P A D.contracting E.contracting p n R b))
  obtain ⟨d, hd⟩ := hfactor
  refine ⟨w, d, normalizes_of_swapping_marks _ T _ _ ht w ?_, ?_, hw, ?_⟩
  · intro R
    have he : toUnit ((testSpec k).obj (op R)) ≫ w = rankOneWord x y R 1 := hw R
    rw [he]
    exact rankOneWord_swaps_marks P A D.contracting E.contracting p n R 1
  · letI := mono_over T.inclusion.hom.hom T.isClosedImmersion
    apply (cancel_mono T.inclusion.hom.hom).mp
    rw [Category.assoc, hd]
    have hη : η[T.group.X] ≫ T.inclusion.hom.hom = η[H.X] :=
      IsMonHom.one_hom _
    rw [hη]
    change η[(Gm k).X] ≫ (rankOneWordMorph x y * (toUnit _ ≫ w)⁻¹) = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit]
    have he : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := toUnit_unique _ _
    rw [he, Category.id_comp]
    change w * w⁻¹ = η[H.X]
    rw [mul_inv_cancel]
    change toUnit (𝟙_ (SchemeOver k)) ≫ η[H.X] = _
    rw [he, Category.id_comp]
  · intro R b
    rw [hd, hword]



private theorem diagonal_conjugation_transvection {R : Type*} [CommRing R]
    (M : Matrix.GeneralLinearGroup Index.{u} R) (d : Index.{u} → R)
    (hM : M.val = Matrix.diagonal d) {i j : Index.{u}} (hij : i ≠ j)
    {r : R} (hr : r * d j = d i) (s : R) :
    M * Matrix.GeneralLinearGroup.transvection i j hij s * M⁻¹ =
      Matrix.GeneralLinearGroup.transvection i j hij (r * s) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Units.ext
  change M.val * Matrix.transvection i j s = Matrix.transvection i j (r * s) * M.val
  rw [hM]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases index_cases_pair hij a with ha | ha <;> subst a <;>
    rcases index_cases_pair hij b with hb | hb <;> subst b
  · simp [Matrix.transvection, Ne.symm hij]
  · simp [Matrix.transvection, hij]
    calc
      d i * s = (r * d j) * s := by rw [hr]
      _ = r * s * d j := by ac_rfl
  · simp [Matrix.transvection, hij, Ne.symm hij]
  · simp [Matrix.transvection, hij]

private theorem simultaneous_stabilizer_diagonal_lift {H : GroupScheme k} {Y : SchemeOver k}
    {a : ModObj H.X Y} {x y : 𝟙_ (SchemeOver k) ⟶ Y}
    (P : ProjectiveAction a x y) (hs : HasScalarKernel P) (hP : ProjectiveMatrixPresentation P)
    (R : TestAlgebra k) (g : GroupPoints H R)
    (hx : Stabilizes a.smul x g) (hy : Stabilizes a.smul y g) :
    ∃ (M : Matrix.GeneralLinearGroup Index.{u} R) (u : Rˣ),
      M.val = Matrix.diagonal (fun i => if i = i0 then (u : R) else 1) ∧
        projectiveMatrixPoint P R M = g ≫ P.hom.hom.hom := by
  obtain ⟨M, h10, h11, h00, hM⟩ := normalized_triangular_lift P hs hP x i0_ne_i1
    (infinity_axis P) R g hx
  have h01 := ((sends_axis_iff P R g M hM.symm _ _ i1 i1 (zero_axis P R) (zero_axis P R)).mp hy).1
    i0 i0_ne_i1
  obtain ⟨u, hu⟩ := h00
  refine ⟨M, u, ?_, hM⟩
  ext i j
  rcases index_cases i with rfl | rfl <;> rcases index_cases j with rfl | rfl <;>
    simp [i0_ne_i1, i1_ne_i0, h10, h11, h01, hu]

private theorem conjugate_contracting_points {H : GroupScheme k} {c : Cocharacter H}
    (D : LimitDecomposition c) {R : TestAlgebra k} {g : GroupPoints H R}
    (hg : Centralizes c g) (p : GroupPoints D.contracting.group R) :
    ∃ q : GroupPoints D.contracting.group R,
      q ≫ D.contracting.inclusion.hom.hom =
        g * (show GroupPoints H R from p ≫ D.contracting.inclusion.hom.hom) * g⁻¹ := by
  let x : GroupPoints H R := p ≫ D.contracting.inclusion.hom.hom
  have hx := (D.contracting_points R x).mpr ⟨p, rfl⟩
  have h := centralizes_hasLimit c hg
  have H := (h.mul hx).mul h.inv
  rw [mul_one, mul_inv_cancel] at H
  exact (D.contracting_points R _).mp H

private theorem rootProjectivePoint
    {H : GroupScheme k} {Y : SchemeOver k} {a : ModObj H.X Y}
    {x y : 𝟙_ (SchemeOver k) ⟶ Y}
    (P : ProjectiveAction a x y) (U : ClosedSubgroup H)
    {A : AdditiveLine k} {i j : Index.{u}} (hij : i ≠ j)
    (p : TransvectionParametrization P A U i j hij)
    (R : TestAlgebra k) (s : R) :
    rootPoint (p.root.hom ≫ U.inclusion) R s ≫ P.hom.hom.hom =
      projectiveMatrixPoint P R (Matrix.GeneralLinearGroup.transvection i j hij s) := by
  rw [← rootPoint_comp, Category.assoc, p.matchesTransvection]
  exact p.matrixPoints R s

private theorem scalarAction_from_diagonal_lift
    {H : GroupScheme k} {Y : SchemeOver k} {a : ModObj H.X Y}
    {x y : 𝟙_ (SchemeOver k) ⟶ Y}
    (P : ProjectiveAction a x y)
    {c : Cocharacter H} (D : LimitDecomposition c)
    {A : AdditiveLine k} {i j : Index.{u}} (hij : i ≠ j)
    (p : TransvectionParametrization P A D.contracting i j hij)
    (R : TestAlgebra k) (g : GroupPoints H R) (hg : Centralizes c g)
    (hinj : Function.Injective (fun u : GroupPoints D.contracting.group R =>
      u ≫ (D.contracting.inclusion ≫ P.hom).hom.hom))
    (M : Matrix.GeneralLinearGroup Index.{u} R) (d : Index.{u} → R)
    (hM : M.val = Matrix.diagonal d) (hproj : g ≫ P.hom.hom.hom = projectiveMatrixPoint P R M)
    {r : R} (hr : r * d j = d i) (s : R) :
    let f := p.root.hom ≫ D.contracting.inclusion
    g * rootPoint f R s * g⁻¹ = rootPoint f R (r * s) := by
  let f := p.root.hom ≫ D.contracting.inclusion
  let u := rootPoint p.root.hom R s
  obtain ⟨v, hv⟩ := conjugate_contracting_points D hg u
  have hx : rootPoint f R s = u ≫ D.contracting.inclusion.hom.hom :=
    rootPoint_comp p.root.hom D.contracting.inclusion R s
  let φ := (((groupPointsFunctor k).map P.hom).app R).hom
  have hm : φ g = projectiveMatrixPoint P R M := hproj
  have htrans (b : R) :
      φ (rootPoint f R b) =
        projectiveMatrixPoint P R (Matrix.GeneralLinearGroup.transvection i j hij b) :=
    rootProjectivePoint P D.contracting hij p R b
  have hp : φ (g * rootPoint f R s * g⁻¹) = φ (rootPoint f R (r * s)) := by
    rw [map_mul, map_mul, map_inv, hm, htrans, htrans, ← map_inv, ← map_mul, ← map_mul,
      diagonal_conjugation_transvection M d hM hij hr s]
  rw [hx, ← hv] at hp
  have he : v = rootPoint p.root.hom R (r * s) := by
    apply hinj
    change φ (v ≫ D.contracting.inclusion.hom.hom) =
      φ (rootPoint p.root.hom R (r * s) ≫ D.contracting.inclusion.hom.hom)
    rw [← rootPoint_comp]
    exact hp
  change g * rootPoint f R s * g⁻¹ = rootPoint f R (r * s)
  rw [hx, ← hv, he, rootPoint_comp]



private theorem pullback_character_is_character {M : Type u} [CommGroup M]
    (φ : MonoidAlgebra k M →ₐ[k] MonoidAlgebra k IntegerCharacters.{u})
    (he : ∀ m : M, unitCoordinates (baseTest k) (1 : kˣ) (φ (MonoidAlgebra.of k M m)) = 1)
    (m : M) : ∃ a : IntegerCharacters.{u},
      φ (MonoidAlgebra.of k M m) = MonoidAlgebra.of k IntegerCharacters a := by
  let p := φ (MonoidAlgebra.of k M m)
  let e := laurentHopfEquiv k
  have hp : IsUnit p := by
    apply IsUnit.map φ
    exact (Group.isUnit m).map (MonoidAlgebra.of k M)
  have hL : IsUnit (e.symm p) := hp.map e.symm
  obtain ⟨a, _, n, hn⟩ := laurent_unit_monomial hL
  have hs : p = MonoidAlgebra.single (⟨Multiplicative.ofAdd n⟩ : IntegerCharacters.{u}) a := by
    calc
      p = e (e.symm p) := (e.apply_symm_apply p).symm
      _ = e (LaurentPolynomial.C a * LaurentPolynomial.T n) := congrArg e hn
      _ = _ := by rw [← LaurentPolynomial.single_eq_C_mul_T, laurentHopfEquiv_single]
  have hv := he m
  change unitCoordinates (baseTest k) (1 : kˣ) p = _ at hv
  rw [hs, unitCoordinates, MonoidAlgebra.lift_single] at hv
  change a • ((↑((1 : kˣ) ^ n) : k) : k) = 1 at hv
  simp only [one_zpow, Units.val_one, smul_eq_mul, mul_one] at hv
  rw [hv] at hs
  exact ⟨⟨Multiplicative.ofAdd n⟩, hs⟩

/-- A pointed map from the multiplicative line to a split torus is a cocharacter. -/
theorem pointedMap_to_splitTorus {T : GroupScheme k} (hT : IsSplitTorus T)
    (g : (Gm k).X ⟶ T.X) (hg : η[(Gm k).X] ≫ g = η[T.X]) :
    ∃ cochar : Cocharacter T, cochar.hom.hom = g := by
  classical
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  let C := CommAlgCat.of k (MonoidAlgebra k M)
  let D := laurentCoordinateAlgebra k
  let Y := specGroup (groupAlgebra k M)
  let q : (testSpec k).obj (op D) ⟶ (testSpec k).obj (op C) := g ≫ i.inv.hom.hom
  let Φ := algSpec.fullyFaithful (R := CommRingCat.of k)
  let φ : C ⟶ D := (Φ.preimage q).unop
  have hq : (testSpec k).map φ.op = q := Φ.map_preimage q
  have hη : η[(Gm k).X] ≫ q = η[Y.X] := by
    change η[(Gm k).X] ≫ g ≫ i.inv.hom.hom = _
    rw [← Category.assoc, hg]
    exact IsMonHom.one_hom _
  let e : C ⟶ baseTest k := CommAlgCat.ofHom (Bialgebra.counitAlgHom k (groupAlgebra k M))
  let a : D ⟶ baseTest k := CommAlgCat.ofHom (unitCoordinates (baseTest k) (1 : kˣ))
  have ha : (testSpec k).map a.op = (1 : GroupPoints (Gm k) (baseTest k)) := by
    change unitPoint (baseTest k) 1 = _
    rw [← unitPointHom_apply, map_one]
  have he : (testSpec k).map e.op = (1 : GroupPoints Y (baseTest k)) :=
    ((hopfSpecPointIso (groupAlgebra k M)).hom.app (baseTest k)).hom.map_one
  have hφa : φ ≫ a = e := by
    apply Quiver.Hom.op_inj
    apply Φ.map_injective
    rw [op_comp, Functor.map_comp, hq, ha, he]
    change (toUnit _ ≫ η[(Gm k).X]) ≫ q = toUnit _ ≫ η[Y.X]
    rw [Category.assoc, hη]
  have hval (m : M) :
      unitCoordinates (baseTest k) (1 : kˣ) (φ.hom (MonoidAlgebra.of k M m)) = 1 := by
    have h := congrArg (fun f : C ⟶ baseTest k => f.hom (MonoidAlgebra.of k M m)) hφa
    change _ = Coalgebra.counit (R := k) (MonoidAlgebra.single m 1 : MonoidAlgebra k M) at h
    rw [MonoidAlgebra.counit_single] at h
    exact h
  choose u hu using pullback_character_is_character φ.hom hval
  let ψ : M →* IntegerCharacters.{u} :=
    { toFun := u
      map_one' := by
        apply MonoidAlgebra.of_injective (R := k)
        rw [← hu, map_one, map_one, map_one]
      map_mul' := by
        intro m n
        apply MonoidAlgebra.of_injective (R := k)
        calc
          _ = φ.hom (MonoidAlgebra.of k M (m * n)) := (hu _).symm
          _ = φ.hom (MonoidAlgebra.of k M m) * φ.hom (MonoidAlgebra.of k M n) := by rw [map_mul, map_mul]
          _ = _ := by rw [hu m, hu n, map_mul] }
  let cochar₀ : (Gm k) ⟶ Y := specGroupMap (groupAlgebraMap k ψ)
  have hφ : CommAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k ψ).toAlgHom = φ := by
    apply CommAlgCat.hom_ext
    apply (MonoidAlgebra.lift k (MonoidAlgebra k IntegerCharacters) M).symm.injective
    apply MonoidHom.ext
    intro m
    change (MonoidAlgebra.mapDomainBialgHom k ψ) (MonoidAlgebra.single m 1) =
      φ.hom (MonoidAlgebra.single m 1)
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    exact (hu m).symm
  have hcochar : cochar₀.hom.hom = q := by
    rw [← hq]
    change (testSpec k).map (CommAlgCat.ofHom
      (MonoidAlgebra.mapDomainBialgHom k ψ).toAlgHom).op = _
    rw [hφ]
  refine ⟨cochar₀ ≫ i.hom, ?_⟩
  change cochar₀.hom.hom ≫ i.hom.hom.hom = _
  rw [hcochar]
  change (g ≫ i.inv.hom.hom) ≫ i.hom.hom.hom = g
  have hh := (Grp.forget _).congr_map i.inv_hom_id
  change i.inv.hom.hom ≫ i.hom.hom.hom = 𝟙 _ at hh
  rw [Category.assoc, hh, Category.comp_id]



private def characterUnit {T : GroupScheme k} (χ : Character T) (R : TestAlgebra k)
    (t : GroupPoints T R) : Rˣ :=
  unitEquiv R (t ≫ χ.hom.hom)

private theorem characterUnit_point {T : GroupScheme k} (χ : Character T) (R : TestAlgebra k)
    (t : GroupPoints T R) :
    unitPoint R (characterUnit χ R t) = t ≫ χ.hom.hom :=
  (unitEquiv R).injective (unitEquiv_unitPoint R _)

private theorem characterValue_eq_unit {T : GroupScheme k} (χ : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue χ R t = (characterUnit χ R t : R) := by
  unfold characterValue
  dsimp only
  rw [← characterUnit_point χ R t]
  unfold unitPoint
  rw [Functor.FullyFaithful.preimage_map]
  change (unitCoordinates R _) (MonoidAlgebra.single DiagonalizableGroups.integerGenerator 1) = _
  rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  change (↑(characterUnit χ R t ^ (1 : ℤ)) : R) = _
  rw [zpow_one]

private theorem characterUnit_natural {T : GroupScheme k} (χ : Character T)
    {R S : TestAlgebra k} (b : R ⟶ S) (t : GroupPoints T R) :
    characterUnit χ S (mapPoints b t) = Units.map b.hom.toMonoidHom (characterUnit χ R t) := by
  apply (unitEquiv S).symm.injective
  change unitPointHom S _ = unitPointHom S _
  rw [unitPointHom_apply, unitPointHom_apply, characterUnit_point, ← mapPoints_unitPoint,
    characterUnit_point]
  rfl

private theorem characterUnit_inv {T : GroupScheme k} (χ : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterUnit χ⁻¹ R t = (characterUnit χ R t)⁻¹ := by
  change unitEquiv R (t ≫ (χ.hom.hom)⁻¹) = _
  rw [GrpObj.comp_inv, map_inv]
  rfl

private theorem characterValue_natural {T : GroupScheme k} (χ : Character T)
    {R S : TestAlgebra k} (b : R ⟶ S) (t : GroupPoints T R) :
    characterValue χ S (mapPoints b t) = b.hom (characterValue χ R t) := by
  rw [characterValue_eq_unit, characterValue_eq_unit, characterUnit_natural]
  rfl



private abbrev dualTest (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

private theorem affineSubgroup {G : GroupScheme k} (hG : IsAffine G.X.left) (S : ClosedSubgroup G) :
    IsAffine S.group.X.left := by
  let := hG
  let := S.isClosedImmersion
  exact isAffine_of_isAffineHom S.inclusion.hom.hom.left

/-- A weight trivial on a subgroup of the torus gives a tangent vector
in the scheme-theoretic centralizer of that subgroup. -/
private theorem liftWeightToCentralizer {G : GroupScheme k} (T : ClosedSubgroup G)
    (α : Character T.group) (C : Centralizer T α) (hG : IsAffine G.X.left)
    {β : Character T.group} (hβ : C.kernelTorus.inclusion ≫ β = 1) {v : Lie k G}
    (hv : v ∈ adjointWeightVectors T β) :
    ∃ w : Lie k C.subgroup.group, mapPointKernel C.subgroup.inclusion w = v := by
  let S := GeometricBorelConjugacy.subgroupOfSubgroup T C.kernelTorus
  have hS : IsAffine S.group.X.left := affineSubgroup hG S
  have hw : v ∈ adjointWeightVectors S 1 := by
    intro R t
    have heval : characterValue β R (t ≫ C.kernelTorus.inclusion.hom.hom) =
        characterValue (1 : Character S.group) R t := by
      rw [← hβ]
      rfl
    have he := hv R (t ≫ C.kernelTorus.inclusion.hom.hom)
    change _ * _ * _ = mapPoints (scale R (characterValue β R (t ≫ C.kernelTorus.inclusion.hom.hom))) _ at he
    rw [heval] at he
    let g : GroupPoints G R := t ≫ C.kernelTorus.inclusion.hom.hom ≫ T.inclusion.hom.hom
    change mapPoints (constants R) g * _ * (mapPoints (constants R) g)⁻¹ = _
    exact he
  obtain ⟨w, hw⟩ := (C.centralizes _ _).mp
    ((zeroWeightVectors_iff_centralizes S hS v).mp hw)
  letI := mono_over C.subgroup.inclusion.hom.hom C.subgroup.isClosedImmersion
  have hred : reduceTangentPoints C.subgroup.group w = 1 := by
    apply (cancel_mono C.subgroup.inclusion.hom.hom).mp
    change ((testSpec k).map (dualReduction k).op ≫ w) ≫ C.subgroup.inclusion.hom.hom =
      (1 : GroupPoints C.subgroup.group (baseTest k)) ≫ C.subgroup.inclusion.hom.hom
    rw [Category.assoc, hw, MonObj.one_comp]
    exact v.toMul.property
  exact ⟨⟨w, hred⟩, Subtype.ext hw⟩

private theorem restrictedCocharacterEigenvector {G : GroupScheme k} (T C : ClosedSubgroup G)
    (i : T.group ⟶ C.group) (hi : i ≫ C.inclusion = T.inclusion)
    (cochar : Cocharacter T.group) (β : Character T.group) (w : Lie k C.group)
    (hw : mapPointKernel C.inclusion w ∈ adjointWeightVectors T β)
    (R : TestAlgebra k) (t : Rˣ) :
    let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
    let p : GroupPoints C.group (CommAlgCat.of k (DualNumber R)) := mapPoints a w.toMul.val
    let g : GroupPoints C.group (CommAlgCat.of k (DualNumber R)) :=
      mapPoints (constants R) (cocharacterPoint (cochar ≫ i) R t)
    g * p * g⁻¹ = mapPoints (scale R (↑(t ^ pairing T.group β cochar) : R)) p := by
  letI := mono_over C.inclusion.hom.hom C.isClosedImmersion
  dsimp only
  apply (cancel_mono C.inclusion.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  have hmap : cocharacterPoint (cochar ≫ i) R t ≫ C.inclusion.hom.hom =
      cocharacterPoint cochar R t ≫ T.inclusion.hom.hom := by
    change (CocharacterDynamics.unitPoint R t ≫ (cochar.hom.hom ≫ i.hom.hom)) ≫ C.inclusion.hom.hom = _
    simp only [Category.assoc]
    rw [show i.hom.hom ≫ C.inclusion.hom.hom = T.inclusion.hom.hom from
      congrArg (fun f : T.group ⟶ G => f.hom.hom) hi]
    rfl
  have hc : (mapPoints (constants R) (cocharacterPoint (cochar ≫ i) R t) :
      GroupPoints C.group (CommAlgCat.of k (DualNumber R))) ≫ C.inclusion.hom.hom =
    mapPoints (constants R) (cocharacterPoint cochar R t ≫ T.inclusion.hom.hom) := by
    change ((testSpec k).map (constants R).op ≫ cocharacterPoint (cochar ≫ i) R t) ≫ _ =
      (testSpec k).map (constants R).op ≫ _
    rw [Category.assoc, hmap]
  rw [hc]
  have h := hw R (cocharacterPoint cochar R t)
  rw [(CharacterPairing.characterPairingComposition T.group β cochar).2 R t] at h
  exact h

private theorem eigenvector_coordinates {H : GroupScheme k} {s : IdentityLieStructure H}
    (cochar : Cocharacter H) (W : AdjointWeightBasis cochar s) (v : Lie k H) (m : ℤ)
    (he : ∀ (R : TestAlgebra k) (t : Rˣ),
      let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
      let p : GroupPoints H (CommAlgCat.of k (DualNumber R)) := mapPoints a v.toMul.val
      let g : GroupPoints H (CommAlgCat.of k (DualNumber R)) :=
        mapPoints (constants R) (cocharacterPoint cochar R t)
      g * p * g⁻¹ = mapPoints (scale R (↑(t ^ m) : R)) p) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ j, W.weight j ≠ m → W.basis.equivFun v j = 0 := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro j hj
  let R := laurentAlgebra (baseTest k)
  let t := laurentParameter (baseTest k)
  let a : baseTest k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  let z (i : ULift.{u} (Fin W.dimension)) : R := a.hom (W.basis.equivFun v i)
  have hbase : (W.coordinates.equiv R z).toMul.val =
      mapPoints (dualMap a) v.toMul.val :=
    (W.coordinates.naturality a _).trans (congrArg (mapPoints (dualMap a)) (W.coordinates.at_base v))
  have hdiag := W.diagonal R t z
  have heq : Specs.AdjointRepresentation.conjugate (cocharacterPoint cochar R t)
      (W.coordinates.equiv R z) =
        mapPoints (scale R (↑(t ^ m) : R)) (W.coordinates.equiv R z).toMul.val := by
    let g : GroupPoints H (CommAlgCat.of k (DualNumber R)) :=
      mapPoints (constants R) (cocharacterPoint cochar R t)
    change g * (W.coordinates.equiv R z).toMul.val * g⁻¹ = _
    rw [hbase]
    exact he R t
  rw [heq, ← W.coordinates.smul] at hdiag
  have hvec := (W.coordinates.equiv R).injective (Subtype.ext hdiag)
  have h := congrFun hvec j
  change (↑(t ^ W.weight j) : R) * z j = (↑(t ^ m) : R) * z j at h
  rw [laurentParameter_zpow, laurentParameter_zpow] at h
  change LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (W.basis.equivFun v j) =
    LaurentPolynomial.T m * LaurentPolynomial.C (W.basis.equivFun v j) at h
  have hcoeff := congrArg (fun p : LaurentPolynomial k => p.coeff (W.weight j)) h
  rw [monomial_coeff, monomial_coeff] at hcoeff
  simpa [hj, Ne.symm hj] using hcoeff

private theorem weight_in_positive_contracting (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (α : Character T.group) (C : Centralizer T α)
    (cochar : Cocharacter T.group)
    (D : LimitDecomposition (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))
    {β : Character T.group} (hβ : C.kernelTorus.inclusion ≫ β = 1)
    (hpos : 0 < pairing T.group β cochar) {v : Lie k G.val} (hv : v ∈ adjointWeightVectors T β) :
    ∃ w : Lie k D.contracting.group, mapPointKernel (D.contracting.inclusion ≫ C.subgroup.inclusion) w = v := by
  obtain ⟨w, hw⟩ := liftWeightToCentralizer T α C G.property.1 hβ hv
  let H := Unipotent.closedSubgroupAlgebraicGroup C.subgroup
  let s := identityLieStructure H
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W, _, hW, _⟩ := CocharacterDynamics.lieWeights H _ D s
  have hj := restrictedCocharacterEigenvector T C.subgroup (C.torusIso.hom ≫ C.torus.inclusion)
    C.torus_inclusion cochar β w (hw.symm ▸ hv)
  have hmem : w ∈ lieImage D.contracting := by
    rw [hW]
    intro j hj'
    exact eigenvector_coordinates _ W w _ hj j (by omega)
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  rw [((lieFunctoriality k).2.2) D.contracting.group C.subgroup.group G.val
    D.contracting.inclusion C.subgroup.inclusion, hz, hw]

private theorem lieDimension_of_splitAdditive (U : AffineAlgebraicGroup k)
    (hU : IsSplitAdditive U.val) (s : IdentityLieStructure U.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Module.finrank k (Lie k U.val) = 1 := by
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨h, hd, he, hi, ⟨i⟩⟩ := hU
  let A : AdditiveLine k := ⟨h, hd, he, hi⟩
  let p : (groupPointsFunctor k).obj U.val ≅ StandardGroups.additivePoints k :=
    (groupPointsFunctor k).mapIso i ≪≫ (additiveLinePointsIso A).symm
  obtain ⟨d, _, _⟩ := lieAdditiveGroup k U p s
  exact d.finrank_eq.trans (CommSemiring.finrank_self k)

private theorem positive_root_space_comparison (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (α : Character T.group) (hα : α ∈ absoluteRoots T)
    (C : Centralizer T α) (cochar : Cocharacter T.group) (hcochar : 0 < pairing T.group α cochar)
    (D : LimitDecomposition (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion))
    (hsplit : IsSplitAdditive D.contracting.group) (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Module.finrank k (adjointWeightSpace T α s) = 1 ∧
      Set.range (mapPointKernel (D.contracting.inclusion ≫ C.subgroup.inclusion)) =
        adjointWeightVectors T α := by
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommGroup (Lie k G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k G.val) := s.lieAlgebra.toModule
  letI := G.property.1
  let U := Unipotent.closedSubgroupAlgebraicGroup
    (GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup D.contracting)
  let sU := identityLieStructure U
  letI := sU.lieRing
  letI := sU.lieAlgebra
  letI : AddCommGroup (Lie k U.val) := sU.lieRing.toAddCommGroup
  letI : Module k (Lie k U.val) := sU.lieAlgebra.toModule
  letI := U.property.1
  obtain ⟨_, bG, _, _, _, _, _, _, _⟩ := adjointRepresentation k G s
  letI : Module.Finite k (Lie k G.val) := Module.Finite.of_basis bG
  obtain ⟨_, bU, _, _, _, _, _, _, _⟩ := adjointRepresentation k U sU
  letI : Module.Finite k (Lie k U.val) := Module.Finite.of_basis bU
  let j : U.val ⟶ G.val := D.contracting.inclusion ≫ C.subgroup.inclusion
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k U.val G.val j sU s
  let f := d.toLinearMap
  have hle : adjointWeightSpace T α s ≤ LinearMap.range f := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨w, hw⟩ := weight_in_positive_contracting G T α C cochar D
      C.kernelTorus_largest.2.1 hcochar hv
    exact ⟨w, (hd w).trans hw⟩
  have hU := lieDimension_of_splitAdditive U hsplit sU
  have hupper : Module.finrank k (LinearMap.range f) ≤ 1 := f.finrank_range_le.trans_eq hU
  have hdim := Submodule.finrank_mono hle
  have hne := ((CharacterPairing.absoluteRootWeights T s α).mp hα).2
  have hlower : 0 < Module.finrank k (adjointWeightSpace T α s) := by
    by_contra! hz
    exact hne (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz))
  have hfin : Module.finrank k (adjointWeightSpace T α s) = 1 := by omega
  have hrange : adjointWeightSpace T α s = LinearMap.range f :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  refine ⟨hfin, ?_⟩
  rw [← CharacterPairing.adjointWeightSpaceVectors G T s α, hrange]
  change Set.range (mapPointKernel j) = Set.range f
  exact congrArg Set.range (funext fun a => (hd a).symm)

/-- Each absolute root line is one-dimensional under the conditional flag geometry. -/
theorem rootSpaceDimension_conditional
    (centralizer : CentralizerAndPositiveCocharacter.{u})
    (_projective : ProjectiveLineAutomorphisms.{u})
    (geometry : RankOneFlagGeometry.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (α : Character T.group) (hα : α ∈ absoluteRoots T)
    (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Module.finrank k (adjointWeightSpace T α s) = 1 := by
  obtain ⟨C, _, cochar, hcochar⟩ := centralizer G hG T hT hmax α hα
  obtain ⟨D, E, ⟨_, _, _, _, _, _, _, hsplit, _⟩, _⟩ :=
    geometry G hG T hT hmax α hα C cochar hcochar
  exact (positive_root_space_comparison G T α hα C cochar hcochar D hsplit s).1



private theorem mapPointKernel_injective {G : GroupScheme k} (U : ClosedSubgroup G) :
    Function.Injective (mapPointKernel U.inclusion) := by
  letI := mono_over U.inclusion.hom.hom U.isClosedImmersion
  intro x y h
  apply Subtype.ext
  apply (cancel_mono U.inclusion.hom.hom).mp
  exact congrArg (fun z : Lie k G => z.toMul.val) h

private theorem normalizes_of_point_conjugation {G : GroupScheme k}
    (T U : ClosedSubgroup G)
    (h : ∀ (R : TestAlgebra k) (t : GroupPoints T.group R) (p : GroupPoints U.group R),
      let g : GroupPoints G R := t ≫ T.inclusion.hom.hom
      ∃ q : GroupPoints U.group R, q ≫ U.inclusion.hom.hom =
        g * (show GroupPoints G R from p ≫ U.inclusion.hom.hom) * g⁻¹) :
    Normalizes U.inclusion T.inclusion.hom.hom := by
  apply (normalizesIff k U.inclusion U.isClosedImmersion _ _).mpr
  constructor
  · apply (CocharacterDynamics.factorsThroughClosed_iff _ U.isClosedImmersion _).mpr
    intro R f
    rw [comp_conjugateFamily]
    exact h R (f ≫ snd _ _) (f ≫ fst _ _)
  · apply (CocharacterDynamics.factorsThroughClosed_iff _ U.isClosedImmersion _).mpr
    intro R f
    rw [comp_conjugateFamily]
    have he : ((f ≫ snd U.group.X T.group.X)⁻¹ : GroupPoints T.group R) ≫ T.inclusion.hom.hom =
        (f ≫ snd U.group.X T.group.X ≫ T.inclusion.hom.hom)⁻¹ := by
      rw [GrpObj.inv_comp, Category.assoc]
    have hw := h R (f ≫ snd U.group.X T.group.X)⁻¹ (f ≫ fst _ _)
    dsimp only at hw
    rw [he] at hw
    obtain ⟨z, hz⟩ := hw
    refine ⟨z, ?_⟩
    simpa only [Category.assoc, GrpObj.comp_inv] using hz

private theorem contracting_normalized_in_ambient {G : GroupScheme k}
    (T : ClosedSubgroup G) {α : Character T.group} (C : Centralizer T α)
    (c : Cocharacter C.subgroup.group) (D : LimitDecomposition c)
    (hT : SameSubgroup D.centralizer C.torus) :
    Normalizes
      (GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup D.contracting).inclusion
      T.inclusion.hom.hom := by
  apply normalizes_of_point_conjugation
  intro R t p
  let u : GroupPoints C.torus.group R := t ≫ C.torusIso.hom.hom.hom
  let g : GroupPoints C.subgroup.group R := u ≫ C.torus.inclusion.hom.hom
  have htg : g ≫ C.subgroup.inclusion.hom.hom = t ≫ T.inclusion.hom.hom := by
    have he := congrArg (fun f : T.group ⟶ G => t ≫ f.hom.hom) C.torus_inclusion
    change t ≫ C.torusIso.hom.hom.hom ≫ C.torus.inclusion.hom.hom ≫ C.subgroup.inclusion.hom.hom =
      t ≫ T.inclusion.hom.hom at he
    simpa only [g, u, Category.assoc] using he
  obtain ⟨j, hj⟩ := hT.2
  have hg := (D.centralizer_points _ g).mpr ⟨u ≫ j.hom.hom, by
    rw [Category.assoc]
    exact congrArg (fun f : C.torus.group ⟶ C.subgroup.group => u ≫ f.hom.hom) hj⟩
  obtain ⟨q, hq⟩ := conjugate_contracting_points D hg p
  refine ⟨q, ?_⟩
  have h := congrArg (· ≫ C.subgroup.inclusion.hom.hom) hq
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, htg] at h
  let j := D.contracting.inclusion.hom.hom ≫ C.subgroup.inclusion.hom.hom
  change q ≫ j = (t ≫ T.inclusion.hom.hom) * (p ≫ j) * (t ≫ T.inclusion.hom.hom)⁻¹
  simpa only [j, Category.assoc] using h

/-- The conditional geometry recovers the zero weight and the nonzero
one-dimensional root spaces together with their split additive subgroups. -/
theorem rootSubgroupGeometry_conditional
    (centralizer : CentralizerAndPositiveCocharacter.{u})
    (projective : ProjectiveLineAutomorphisms.{u})
    (geometry : RankOneFlagGeometry.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T) :
    (Function.Injective (mapPointKernel T.inclusion) ∧
      Set.range (mapPointKernel T.inclusion) = adjointWeightVectors T 1) ∧
    ∀ α ∈ absoluteRoots T,
      (∀ s : IdentityLieStructure G.val,
        letI := s.lieRing
        letI := s.lieAlgebra
        Module.finrank k (adjointWeightSpace T α s) = 1) ∧
      ∃ U : ClosedSubgroup G.val, IsRootSubgroup T U α ∧
        Function.Injective (mapPointKernel U.inclusion) ∧
        Set.range (mapPointKernel U.inclusion) = adjointWeightVectors T α := by
  let s := identityLieStructure G
  have h0 := CharacterPairing.zeroWeightSpace G hG T hT hmax s
  refine ⟨⟨h0.1, h0.2.symm.trans (CharacterPairing.adjointWeightSpaceVectors G T s 1)⟩, ?_⟩
  intro α hα
  obtain ⟨C, _, cochar, hcochar⟩ := centralizer G hG T hT hmax α hα
  obtain ⟨D, E, ⟨ht, _, _, hsmooth, _, _, _, hsplit, _⟩, _⟩ :=
    geometry G hG T hT hmax α hα C cochar hcochar
  let U := GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup D.contracting
  have hU : Set.range (mapPointKernel U.inclusion) = adjointWeightVectors T α :=
    (positive_root_space_comparison G T α hα C cochar hcochar D hsplit s).2
  refine ⟨rootSpaceDimension_conditional centralizer projective geometry G hG T hT hmax α hα,
    U, ⟨hsmooth, hsplit, contracting_normalized_in_ambient T C _ D ht, hU.le⟩,
    mapPointKernel_injective U, hU⟩



private theorem rootPoint_injective_of_mono {A : AdditiveLine k} {G : GroupScheme k}
    (f : A.group ⟶ G) [Mono f.hom.hom] (R : TestAlgebra k) :
    Function.Injective (rootPoint f R) := by
  intro b c h
  apply (additivePoints A R).injective
  rw [rootPoint_eq, rootPoint_eq] at h
  exact (cancel_mono f.hom.hom).mp h

private theorem torus_points_centralize_limit {H : GroupScheme k}
    (T : ClosedSubgroup H) {c : Cocharacter H}
    (D : LimitDecomposition c) (hT : SameSubgroup D.centralizer T)
    (R : TestAlgebra k) (t : GroupPoints T.group R) :
    Centralizes c (t ≫ T.inclusion.hom.hom) := by
  obtain ⟨j, hj⟩ := hT.2
  apply (D.centralizer_points _ _).mpr
  refine ⟨t ≫ j.hom.hom, ?_⟩
  rw [Category.assoc]
  exact congrArg (fun f : T.group ⟶ H => t ≫ f.hom.hom) hj

private theorem rootPoint_eps_reduces {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G) :
    reduceTangentPoints G (rootPoint x (dualTest k) (DualNumber.eps : DualNumber k)) = 1 := by
  change mapPoints (dualReduction k) (rootPoint x (dualTest k) (DualNumber.eps : DualNumber k)) = _
  rw [rootPoint_natural]
  change rootPoint x (baseTest k) 0 = _
  rw [rootPoint_zero]

private theorem base_change_root_eps {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G)
    (R : TestAlgebra k) :
    mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R)))
      (rootPoint x (dualTest k) (DualNumber.eps : DualNumber k)) =
        rootPoint x (CommAlgCat.of k (DualNumber R)) (DualNumber.eps : DualNumber R) := by
  rw [rootPoint_natural]
  congr 1
  exact TrivSqZeroExt.ext (map_zero (Algebra.ofId k R)) (map_one (Algebra.ofId k R))

private theorem weight_at_root_eps {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G)
    (T : ClosedSubgroup G) (α : Character T.group)
    (hα : (⟨rootPoint x (dualTest k) (DualNumber.eps : DualNumber k),
      rootPoint_eps_reduces x⟩ : Lie k G) ∈ adjointWeightVectors T α)
    (R : TestAlgebra k) (t : GroupPoints T.group R) :
    let B := CommAlgCat.of k (DualNumber R)
    let g : GroupPoints G B := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
    g * rootPoint x B (DualNumber.eps : DualNumber R) * g⁻¹ =
      rootPoint x B (⟨0, characterValue α R t⟩ : DualNumber R) := by
  have h := hα R t
  change _ * (mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R)))
    (rootPoint x (dualTest k) (DualNumber.eps : DualNumber k))) * _ =
    mapPoints (scale R (characterValue α R t)) (mapPoints
      (dualMap (CommAlgCat.ofHom (Algebra.ofId k R)))
      (rootPoint x (dualTest k) (DualNumber.eps : DualNumber k))) at h
  rw [base_change_root_eps, rootPoint_natural] at h
  exact h.trans (congrArg (rootPoint x (CommAlgCat.of k (DualNumber R)))
    (TrivSqZeroExt.ext rfl (mul_one _)))

private theorem root_diagonal_scalar
    {H G : GroupScheme k} (l : H ⟶ G)
    (T : ClosedSubgroup G) (TH : ClosedSubgroup H) (i : T.group ⟶ TH.group)
    (hi : i ≫ TH.inclusion ≫ l = T.inclusion)
    {c : Cocharacter H} (D : LimitDecomposition c) (hT : SameSubgroup D.centralizer TH)
    {Y : SchemeOver k} {a : ModObj H.X Y} {p q : 𝟙_ (SchemeOver k) ⟶ Y}
    (P : ProjectiveAction a p q) {A : AdditiveLine k}
    (x : TransvectionParametrization P A D.contracting i0 i1 i0_ne_i1)
    (hinj : ∀ R : TestAlgebra k, Function.Injective
      (fun u : GroupPoints D.contracting.group R => u ≫ (D.contracting.inclusion ≫ P.hom).hom.hom))
    [Mono ((x.root.hom ≫ D.contracting.inclusion ≫ l).hom.hom)]
    (α : Character T.group)
    (hroot : Set.range (mapPointKernel (D.contracting.inclusion ≫ l)) ⊆ adjointWeightVectors T α)
    (R : TestAlgebra k) (t : GroupPoints T.group R)
    (M : Matrix.GeneralLinearGroup Index.{u} R) (u : Rˣ)
    (hM : M.val = Matrix.diagonal (fun j => if j = i0 then (u : R) else 1))
    (hproj : projectiveMatrixPoint P R M = t ≫ (i ≫ TH.inclusion ≫ P.hom).hom.hom) :
    (u : R) = characterValue α R t := by
  let ht := i ≫ TH.inclusion
  let f := x.root.hom ≫ D.contracting.inclusion
  let F := f ≫ l
  let B := CommAlgCat.of k (DualNumber R)
  let z := constants R
  let U := Matrix.GeneralLinearGroup.map z.hom.toRingHom M
  let d (j : Index.{u}) : B := if j = i0 then z.hom (u : R) else 1
  have hd : U.val = Matrix.diagonal d := by
    apply Matrix.ext
    intro a b
    rw [Matrix.GeneralLinearGroup.map_apply, hM]
    by_cases hab : a = b
    · subst b
      by_cases ha : a = i0 <;> simp [ha, d]
    · simp [Matrix.diagonal_apply_ne _ hab, map_zero]
  let t' : GroupPoints T.group B := mapPoints z t
  let s : GroupPoints TH.group B := t' ≫ i.hom.hom
  let g : GroupPoints H B := s ≫ TH.inclusion.hom.hom
  have he := congrArg (mapPoints z) hproj
  rw [projectiveMatrixPoint_natural] at he
  have he' : g ≫ P.hom.hom.hom = projectiveMatrixPoint P B U := he.symm
  have hc := torus_points_centralize_limit TH D hT B s
  have hratio : z.hom (u : R) * d i1 = d i0 := by simp [d, i1_ne_i0]
  have hconj := scalarAction_from_diagonal_lift P D i0_ne_i1 x B g hc (hinj B)
    U d hd he' hratio (DualNumber.eps : DualNumber R)
  change g * (rootPoint f B (DualNumber.eps : DualNumber R)) * g⁻¹ =
    rootPoint f B (z.hom (u : R) * (DualNumber.eps : DualNumber R)) at hconj
  have hgl : g ≫ l.hom.hom = t' ≫ T.inclusion.hom.hom := by
    have h := congrArg (fun a : T.group ⟶ G => t' ≫ a.hom.hom) hi
    change t' ≫ i.hom.hom ≫ TH.inclusion.hom.hom ≫ l.hom.hom =
      t' ≫ T.inclusion.hom.hom at h
    simpa only [g, s, Category.assoc] using h
  have hF : (⟨rootPoint F (dualTest k) (DualNumber.eps : DualNumber k),
      rootPoint_eps_reduces F⟩ : Lie k G) ∈ adjointWeightVectors T α := by
    apply hroot
    refine ⟨⟨rootPoint x.root.hom (dualTest k) (DualNumber.eps : DualNumber k),
      rootPoint_eps_reduces x.root.hom⟩, ?_⟩
    apply Subtype.ext
    change rootPoint x.root.hom (dualTest k) (DualNumber.eps : DualNumber k) ≫
      (D.contracting.inclusion ≫ l).hom.hom = _
    rw [← rootPoint_comp]
    change rootPoint (x.root.hom ≫ D.contracting.inclusion ≫ l) (dualTest k)
        (DualNumber.eps : DualNumber k) = _
    rw [← Category.assoc]
  have h := weight_at_root_eps F T α hF R t
  have h' := congrArg (· ≫ l.hom.hom) hconj
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hgl,
    ← rootPoint_comp, ← rootPoint_comp] at h'
  have hh := h'.symm.trans h
  have hFcomp : F = x.root.hom ≫ D.contracting.inclusion ≫ l := Category.assoc _ _ _
  letI : Mono F.hom.hom := hFcomp.symm ▸ (inferInstance : Mono ((x.root.hom ≫ D.contracting.inclusion ≫ l).hom.hom))
  have hsame := rootPoint_injective_of_mono F B hh
  have hc := congrArg TrivSqZeroExt.snd hsame
  change (u : R) * 1 + 0 * 0 = characterValue α R t at hc
  simpa only [mul_one, zero_mul, add_zero] using hc



private theorem additiveLine_tangent_point
    (A : AdditiveLine k) {U : GroupScheme k} (i : A.group ≅ U) (p : Lie k U) :
    ∃ s : k, p.toMul.val = rootPoint i.hom (dualTest k) (⟨0, s⟩ : DualNumber k) := by
  let q : GroupPoints A.group (dualTest k) := p.toMul.val ≫ i.inv.hom.hom
  obtain ⟨z, hz⟩ := (additivePoints A (dualTest k)).surjective q
  have hp : mapPoints (dualReduction k) p.toMul.val = (1 : GroupPoints U (baseTest k)) :=
    p.toMul.property
  have hq : mapPoints (dualReduction k) q = 1 := by
    change mapPoints (dualReduction k) p.toMul.val ≫ i.inv.hom.hom = _
    rw [hp, MonObj.one_comp]
  rw [← hz, additivePoints_natural, ← additivePoints_zero A (baseTest k)] at hq
  have h0 : z.fst = 0 := (additivePoints A (baseTest k)).injective hq
  refine ⟨z.snd, ?_⟩
  rw [← show z = (⟨0, z.snd⟩ : DualNumber k) from TrivSqZeroExt.ext h0 rfl,
    rootPoint_eq, hz]
  change p.toMul.val = (p.toMul.val ≫ i.inv.hom.hom) ≫ i.hom.hom.hom
  have hι : i.inv.hom.hom ≫ i.hom.hom.hom = 𝟙 _ := (Grp.forget _).congr_map i.inv_hom_id
  rw [Category.assoc, hι, Category.comp_id]

private theorem tangent_weight_of_scalarAction {G : GroupScheme k}
    (T U : ClosedSubgroup G) (α : Character T.group) (A : AdditiveLine k)
    (i : A.group ≅ U.group) (h : HasScalarAction T α (i.hom ≫ U.inclusion)) :
    Set.range (mapPointKernel U.inclusion) ⊆ adjointWeightVectors T α := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨b, hb⟩ := additiveLine_tangent_point A i p
  let f := i.hom ≫ U.inclusion
  have he : (mapPointKernel U.inclusion p).toMul.val =
      rootPoint f (dualTest k) (⟨0, b⟩ : DualNumber k) := by
    change p.toMul.val ≫ U.inclusion.hom.hom = _
    rw [hb, ← rootPoint_comp]
  intro R t
  let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
  let d := a.hom (⟨0, b⟩ : DualNumber k)
  let c := characterValue α R t
  let B := CommAlgCat.of k (DualNumber R)
  let g : GroupPoints G B := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
  change g * (show GroupPoints G B from mapPoints a (mapPointKernel U.inclusion p).toMul.val) * g⁻¹ =
    mapPoints (scale R c) (mapPoints a (mapPointKernel U.inclusion p).toMul.val)
  rw [he, rootPoint_natural, rootPoint_natural]
  have hs := h B (mapPoints (constants R) t) d
  rw [characterValue_natural α] at hs
  have hd : (constants R).hom c * d = (scale R c).hom d := by
    apply TrivSqZeroExt.ext
    · change c * algebraMap k R 0 = algebraMap k R 0
      rw [map_zero, mul_zero]
    · change c * algebraMap k R b + (0 : R) * algebraMap k R 0 = c * algebraMap k R b
      rw [zero_mul, add_zero]
  rw [hd] at hs
  exact hs

private theorem rankOne_matched_scalarActions
    {G : GroupScheme k} (T : ClosedSubgroup G)
    (α : Character T.group) (C : Centralizer T α) (hAff : IsAffine C.subgroup.group.X.left)
    {c : Cocharacter C.subgroup.group}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hplus : SameSubgroup D.centralizer C.torus) (hminus : SameSubgroup E.centralizer C.torus)
    (hB : AreTwoBorels C.torus D.parabolic E.parabolic)
    {Q : QuotientEmbedding.Presentation D.parabolic}
    (F : FlagIdentification C.torus D.parabolic E.parabolic E.contracting Q)
    (P : ProjectiveAction F.action (η[C.subgroup.group.X] ≫ Q.projection)
      (F.normalizerPoint ≫ Q.projection))
    (hs : HasScalarKernel P) (hP : ProjectiveMatrixPresentation P)
    (A : AdditiveLine k)
    (p : TransvectionParametrization P A D.contracting i0 i1 i0_ne_i1)
    (n : TransvectionParametrization P A E.contracting i1 i0 i1_ne_i0)
    (hroot : Set.range (mapPointKernel (D.contracting.inclusion ≫ C.subgroup.inclusion)) ⊆
      adjointWeightVectors T α) :
    HasScalarAction T α (p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion) ∧
    HasScalarAction T α⁻¹ (n.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion) := by
  let l := C.subgroup.inclusion
  let i := C.torusIso.hom
  let H := C.subgroup.group
  let x := η[H.X] ≫ Q.projection
  let y := F.normalizerPoint ≫ Q.projection
  have hfix := fixes_marked_cosets_iff hAff D E hplus hB F
  have hfix' (R : TestAlgebra k) (g : GroupPoints H R)
      (hp : Stabilizes F.action.smul x g) (hn : Stabilizes F.action.smul y g) :=
    (hfix R g).mp ⟨hp, hn⟩
  have hp := contracting_projective_injective hAff P C.torus D hplus hfix'
  have hn := contracting_projective_injective hAff P C.torus E hminus hfix'
  let V := GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup D.contracting
  haveI : Mono V.inclusion.hom.hom := mono_over _ V.isClosedImmersion
  letI : Mono ((p.root.hom ≫ D.contracting.inclusion ≫ l).hom.hom) := by
    change Mono (p.root.hom.hom.hom ≫ V.inclusion.hom.hom)
    infer_instance
  have haux (R : TestAlgebra k) (t : GroupPoints T.group R) (b : R) :
      let g : GroupPoints G R := t ≫ T.inclusion.hom.hom
      g * rootPoint (p.root.hom ≫ D.contracting.inclusion ≫ l) R b * g⁻¹ =
        rootPoint (p.root.hom ≫ D.contracting.inclusion ≫ l) R (characterValue α R t * b) ∧
      g * rootPoint (n.root.hom ≫ E.contracting.inclusion ≫ l) R b * g⁻¹ =
        rootPoint (n.root.hom ≫ E.contracting.inclusion ≫ l) R (characterValue α⁻¹ R t * b) := by
    let s : GroupPoints C.torus.group R := t ≫ i.hom.hom
    let g : GroupPoints H R := s ≫ C.torus.inclusion.hom.hom
    have hx := (hfix R g).mpr ⟨s, rfl⟩
    obtain ⟨M, u, hM, hproj⟩ := simultaneous_stabilizer_diagonal_lift P hs hP R g hx.1 hx.2
    have hval := root_diagonal_scalar l T C.torus i C.torus_inclusion D hplus P p hp α hroot R t M u hM
      hproj
    have hunit : u = characterUnit α R t := Units.ext (hval.trans (characterValue_eq_unit α R t))
    have hinv : (↑u⁻¹ : R) = characterValue α⁻¹ R t := by
      rw [characterValue_eq_unit, characterUnit_inv, hunit]
    have htg : g ≫ l.hom.hom = t ≫ T.inclusion.hom.hom := by
      have h := congrArg (fun a : T.group ⟶ G => t ≫ a.hom.hom) C.torus_inclusion
      change t ≫ i.hom.hom ≫ C.torus.inclusion.hom.hom ≫ l.hom.hom = t ≫ T.inclusion.hom.hom at h
      simpa only [g, s, Category.assoc] using h
    have Pos := scalarAction_from_diagonal_lift P D i0_ne_i1 p R g
      (torus_points_centralize_limit C.torus D hplus R s) (hp R) M _ hM hproj.symm
      (r := (u : R)) (by simp [i1_ne_i0]) b
    have Neg := scalarAction_from_diagonal_lift P E i1_ne_i0 n R g
      (torus_points_centralize_limit C.torus E hminus R s) (hn R) M _ hM hproj.symm
      (r := (↑u⁻¹ : R)) (by simp [i1_ne_i0]) b
    constructor
    · have h := congrArg (· ≫ l.hom.hom) Pos
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, htg, ← rootPoint_comp, ← rootPoint_comp,
        hval, Category.assoc] at h
      exact h
    · have h := congrArg (· ≫ l.hom.hom) Neg
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, htg, ← rootPoint_comp, ← rootPoint_comp,
        hinv, Category.assoc] at h
      exact h
  exact ⟨fun R t s => (haux R t s).1, fun R t s => (haux R t s).2⟩



private def characterUnitOnPoints {T : GroupScheme k} (χ : Character T)
    (R : TestAlgebra k) : GroupPoints T R →* Rˣ :=
  (unitEquiv R).toMonoidHom.comp (((groupPointsFunctor k).map χ).app R).hom

private def characterEvaluation {T : GroupScheme k} (R : TestAlgebra k)
    (t : GroupPoints T R) : Character T →* Rˣ where
  toFun χ := characterUnit χ R t
  map_one' := by
    change unitEquiv R (t ≫ (1 : (T.X ⟶ (Gm k).X))) = 1
    rw [MonObj.comp_one, map_one]
  map_mul' χ ψ := by
    change unitEquiv R (t ≫ (χ.hom.hom * ψ.hom.hom)) = _
    rw [MonObj.comp_mul, map_mul]
    rfl

private theorem characterUnit_cocharacter {T : GroupScheme k} (χ : Character T)
    (cochar : Cocharacter T) (R : TestAlgebra k) (b : Rˣ) :
    characterUnit χ R (cocharacterPoint cochar R b) = b ^ pairing T χ cochar := by
  apply Units.ext
  rw [← characterValue_eq_unit]
  exact (CharacterPairing.characterPairingComposition T χ cochar).2 R b

private theorem cocharacterPoint_inv {T : GroupScheme k} (cochar : Cocharacter T)
    (R : TestAlgebra k) (b : Rˣ) :
    cocharacterPoint cochar R b⁻¹ = (cocharacterPoint cochar R b)⁻¹ := by
  simp only [cocharacterPoint, ← unitPointHom_apply]
  exact ((((groupPointsFunctor k).map cochar).app R).hom.comp (unitPointHom R)).map_inv b

private theorem conjugation_by_word
    {G : GroupScheme k} (T : ClosedSubgroup G) (α : Character T.group)
    {A : AdditiveLine k} {x y : A.group ⟶ G}
    (hx : HasScalarAction T α x) (hy : HasScalarAction T α⁻¹ y)
    (cochar : Cocharacter T.group) (n : 𝟙_ (SchemeOver k) ⟶ G.X)
    (hn : ∀ R : TestAlgebra k, toUnit _ ≫ n = rankOneWord x y R (1 : Rˣ))
    (hcochar : ∀ (R : TestAlgebra k) (b : Rˣ),
      cocharacterPoint cochar R b ≫ T.inclusion.hom.hom =
        rankOneWord x y R b * (rankOneWord x y R 1)⁻¹)
    (R : TestAlgebra k) (t : GroupPoints T.group R) :
    let nR : GroupPoints G R := toUnit _ ≫ n
    let tR : GroupPoints G R := t ≫ T.inclusion.hom.hom
    let dR : GroupPoints G R :=
      cocharacterPoint cochar R (characterUnit α R t) ≫ T.inclusion.hom.hom
    nR * tR * nR⁻¹ = dR⁻¹ * tR := by
  let nR : GroupPoints G R := toUnit _ ≫ n
  let tR : GroupPoints G R := t ≫ T.inclusion.hom.hom
  let b := characterUnit α R t
  let dR : GroupPoints G R := cocharacterPoint cochar R b ≫ T.inclusion.hom.hom
  have h := conjugateRankOneWord T hx hy R t b 1 (characterValue_eq_unit _ _ _) (by
    rw [characterValue_eq_unit, characterUnit_inv])
  change (tR * rankOneWord x y R 1) * tR⁻¹ = _ at h
  rw [mul_one, ← hn R] at h
  have hd : rankOneWord x y R b = dR * nR := by
    apply (mul_inv_eq_iff_eq_mul).mp
    have he : nR = rankOneWord x y R 1 := hn R
    rw [he]
    exact (hcochar R b).symm
  change tR * nR * tR⁻¹ = _ at h
  rw [hd] at h
  have he : tR * nR = (dR * nR) * tR := mul_inv_eq_iff_eq_mul.mp h
  apply mul_inv_eq_iff_eq_mul.mpr
  calc
    nR * tR = dR⁻¹ * ((dR * nR) * tR) := by simp [mul_assoc]
    _ = dR⁻¹ * (tR * nR) := congrArg (dR⁻¹ * ·) he.symm
    _ = (dR⁻¹ * tR) * nR := (mul_assoc _ _ _).symm

/-- The word formulas for a cocharacter with root pairing two give the actual
Weyl reflection on the character lattice. -/
theorem corootReflection_of_word
    {G : GroupScheme k} (T : ClosedSubgroup G) (hT : IsSplitTorus T.group)
    (α : Character T.group) {A : AdditiveLine k} (x y : A.group ⟶ G)
    (hx : HasScalarAction T α x) (hy : HasScalarAction T α⁻¹ y)
    (cochar : Cocharacter T.group) (n : 𝟙_ (SchemeOver k) ⟶ G.X)
    (hn : ∀ R : TestAlgebra k, toUnit _ ≫ n = rankOneWord x y R (1 : Rˣ))
    (hcochar : ∀ (R : TestAlgebra k) (b : Rˣ),
      cocharacterPoint cochar R b ≫ T.inclusion.hom.hom =
        rankOneWord x y R b * (rankOneWord x y R 1)⁻¹)
    (hpair : pairing T.group α cochar = 2) :
    Nonempty (CorootReflection T α x y) := by
  obtain ⟨hcomm, _⟩ := CharacterPairing.perfectCharacterPairing T.group hT
  letI := hcomm
  let f : T.group ⟶ T.group := (α ≫ cochar)⁻¹ * 𝟙 T.group
  have hf (R : TestAlgebra k) (t : GroupPoints T.group R) :
      t ≫ f.hom.hom = (cocharacterPoint cochar R (characterUnit α R t))⁻¹ * t := by
    change t ≫ ((α.hom.hom ≫ cochar.hom.hom)⁻¹ * 𝟙 _) = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ← Category.assoc, ← characterUnit_point]
    rfl
  have hα (R : TestAlgebra k) (t : GroupPoints T.group R) :
      characterUnit α R (t ≫ f.hom.hom) = (characterUnit α R t)⁻¹ := by
    let e := characterUnitOnPoints α R
    change e (t ≫ f.hom.hom) = (e t)⁻¹
    rw [hf, map_mul, map_inv]
    change (characterUnit α R (cocharacterPoint cochar R (characterUnit α R t)))⁻¹ *
      characterUnit α R t = _
    rw [characterUnit_cocharacter, hpair, zpow_ofNat, pow_two, mul_inv_rev]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    rfl
  have hff : f ≫ f = 𝟙 T.group := by
    apply Grp.hom_ext
    apply hom_ext_on_affine_tests
    intro R t
    change (t ≫ f.hom.hom) ≫ f.hom.hom = t
    rw [hf R (t ≫ f.hom.hom), hα, cocharacterPoint_inv, inv_inv, hf]
    exact mul_inv_cancel_left _ _
  let e : T.group ≅ T.group := ⟨f, f, hff, hff⟩
  have hconj : (e.hom ≫ T.inclusion).hom.hom =
      (toUnit T.group.X ≫ n) * T.inclusion.hom.hom * (toUnit T.group.X ≫ n)⁻¹ := by
    apply hom_ext_on_affine_tests
    intro R t
    change t ≫ f.hom.hom ≫ T.inclusion.hom.hom = _
    rw [← Category.assoc, hf, MonObj.mul_comp, GrpObj.inv_comp,
      MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit]
    exact (conjugation_by_word T α hx hy cochar n hn hcochar R t).symm
  have hnorm : Normalizes T.inclusion n := by
    let j := (Grp.forget _).mapIso e
    let u := j ⊗ᵢ Iso.refl (𝟙_ (SchemeOver k))
    refine ⟨u, toUnit_unique _ _, ?_⟩
    change (j.hom ⊗ₘ 𝟙 _) ≫ fst _ _ ≫ T.inclusion.hom.hom = _
    rw [tensorHom_fst_assoc]
    change fst _ _ ≫ f.hom.hom ≫ T.inclusion.hom.hom = _
    change _ ≫ (e.hom ≫ T.inclusion).hom.hom = _
    rw [hconj, conjugateFamily, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
      ← Category.assoc, comp_toUnit]
    rw [toUnit_unique (snd T.group.X (𝟙_ (SchemeOver k))) (toUnit _)]
  refine ⟨⟨cochar, n, hnorm, hn (baseTest k), hcochar, e, hconj, ?_, hpair⟩⟩
  intro χ
  apply CharacterPairing.characterValuesDetectCharacters hT
  intro R t
  change characterValue χ R (t ≫ f.hom.hom) =
    characterValue (χ * α ^ (-pairing T.group χ cochar)) R t
  rw [characterValue_eq_unit, characterValue_eq_unit]
  let E := characterEvaluation R t
  let F := characterUnitOnPoints χ R
  change (↑(F (t ≫ f.hom.hom)) : R) = (↑(E (χ * α ^ (-pairing T.group χ cochar))) : R)
  rw [hf, map_mul E, map_zpow E, map_mul F, map_inv F]
  change (↑((characterUnit χ R (cocharacterPoint cochar R (characterUnit α R t)))⁻¹ *
    characterUnit χ R t) : R) =
      (↑(characterUnit χ R t * characterUnit α R t ^ (-pairing T.group χ cochar)) : R)
  rw [characterUnit_cocharacter, zpow_neg, mul_comm]



private theorem rankOneWord_comp {A : AdditiveLine k} {G H : GroupScheme k}
    (x y : A.group ⟶ G) (f : G ⟶ H) (R : TestAlgebra k) (b : Rˣ) :
    rankOneWord (x ≫ f) (y ≫ f) R b = rankOneWord x y R b ≫ f.hom.hom := by
  unfold rankOneWord
  rw [MonObj.mul_comp, MonObj.mul_comp]
  simp only [rootPoint_comp]

private theorem pairing_two_of_characterValues {T : GroupScheme k} (α : Character T)
    (cochar : Cocharacter T)
    (h : ∀ (R : TestAlgebra k) (b : Rˣ),
      characterValue α R (cocharacterPoint cochar R b) = (b : R) ^ 2) :
    pairing T α cochar = 2 := by
  let R := laurentAlgebra (baseTest k)
  let b := laurentParameter (baseTest k)
  have hEq : (↑(b ^ pairing T α cochar) : R) = (↑(b ^ (2 : ℤ)) : R) := by
    rw [← (CharacterPairing.characterPairingComposition T α cochar).2 R b, h, zpow_ofNat,
      Units.val_pow_eq_pow_val]
  rw [laurentParameter_zpow, laurentParameter_zpow] at hEq
  by_contra hne
  have hc := congrArg (fun f : LaurentPolynomial k => (f * LaurentPolynomial.C 1).coeff 2) hEq
  rw [monomial_coeff, monomial_coeff] at hc
  simp [Ne.symm hne] at hc

private theorem coroot_from_matched_rankOne_word
    {G : GroupScheme k} (T : ClosedSubgroup G) (hT : IsSplitTorus T.group)
    (α : Character T.group) (C : Centralizer T α) (ha : IsAffine C.subgroup.group.X.left)
    {c : Cocharacter C.subgroup.group}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hplus : SameSubgroup D.centralizer C.torus)
    (hB : AreTwoBorels C.torus D.parabolic E.parabolic)
    {Q : QuotientEmbedding.Presentation D.parabolic}
    (F : FlagIdentification C.torus D.parabolic E.parabolic E.contracting Q)
    (P : ProjectiveAction F.action (η[C.subgroup.group.X] ≫ Q.projection)
      (F.normalizerPoint ≫ Q.projection))
    (A : AdditiveLine k)
    (p : TransvectionParametrization P A D.contracting i0 i1 i0_ne_i1)
    (n : TransvectionParametrization P A E.contracting i1 i0 i1_ne_i0)
    (hx : HasScalarAction T α (p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion))
    (hy : HasScalarAction T α⁻¹ (n.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion)) :
    Nonempty (CorootReflection T α
      (p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion)
      (n.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion)) := by
  let H := C.subgroup.group
  let l := C.subgroup.inclusion
  let i := C.torusIso
  let x := p.root.hom ≫ D.contracting.inclusion
  let y := n.root.hom ≫ E.contracting.inclusion
  have hx' : HasScalarAction T α (x ≫ l) := by simpa only [x, Category.assoc] using hx
  have hy' : HasScalarAction T α⁻¹ (y ≫ l) := by simpa only [y, Category.assoc] using hy
  suffices h : Nonempty (CorootReflection T α (x ≫ l) (y ≫ l)) by
    simpa only [x, y, Category.assoc] using h
  obtain ⟨w, d, _, hdOne, hw, hd⟩ := matchedWord_in_torus_and_normalizer ha C.torus D E hplus hB F P A p n
  let ξ := d ≫ i.inv.hom.hom
  have hξ : η[(Gm k).X] ≫ ξ = η[T.group.X] := by
    rw [← Category.assoc, hdOne]
    exact IsMonHom.one_hom _
  obtain ⟨cochar, hcochar⟩ := pointedMap_to_splitTorus hT ξ hξ
  let rep := w ≫ l.hom.hom
  have hrep (R : TestAlgebra k) : toUnit _ ≫ rep = rankOneWord (x ≫ l) (y ≫ l) R 1 := by
    rw [rankOneWord_comp]
    change toUnit _ ≫ w ≫ l.hom.hom = _
    rw [← Category.assoc, hw R]
  have hd' (R : TestAlgebra k) (b : Rˣ) :
      cocharacterPoint cochar R b ≫ i.hom.hom.hom = unitPoint R b ≫ d := by
    change (unitPoint R b ≫ cochar.hom.hom) ≫ i.hom.hom.hom = _
    rw [hcochar]
    change (unitPoint R b ≫ d ≫ i.inv.hom.hom) ≫ i.hom.hom.hom = _
    rw [Category.assoc, Category.assoc]
    have hi : i.inv.hom.hom ≫ i.hom.hom.hom = 𝟙 _ := (Grp.forget _).congr_map i.inv_hom_id
    rw [hi, Category.comp_id]
  have hinc (R : TestAlgebra k) (t : GroupPoints T.group R) :
      t ≫ i.hom.hom.hom ≫ C.torus.inclusion.hom.hom ≫ l.hom.hom = t ≫ T.inclusion.hom.hom := by
    have h := congrArg (fun u : T.group ⟶ G => t ≫ u.hom.hom) C.torus_inclusion
    exact h
  have hword (R : TestAlgebra k) (b : Rˣ) :
      cocharacterPoint cochar R b ≫ T.inclusion.hom.hom =
        rankOneWord (x ≫ l) (y ≫ l) R b * (rankOneWord (x ≫ l) (y ≫ l) R 1)⁻¹ := by
    rw [← hinc, ← Category.assoc (f := cocharacterPoint cochar R b), hd']
    change (unitPoint R b ≫ d ≫ C.torus.inclusion.hom.hom) ≫ l.hom.hom = _
    rw [hd]
    rw [rankOneWord_comp, rankOneWord_comp, MonObj.mul_comp, GrpObj.inv_comp]
  have hfix (R : TestAlgebra k) (g : GroupPoints H R)
      (hp : Stabilizes F.action.smul (η[H.X] ≫ Q.projection) g)
      (hn : Stabilizes F.action.smul (F.normalizerPoint ≫ Q.projection) g) :=
    (fixes_marked_cosets_iff ha D E hplus hB F R g).mp ⟨hp, hn⟩
  have hinj := contracting_projective_injective ha P C.torus D hplus hfix
  let U := GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup D.contracting
  letI : Mono U.inclusion.hom.hom := mono_over _ U.isClosedImmersion
  letI : Mono (x ≫ l).hom.hom := by
    rw [show x ≫ l = p.root.hom ≫ U.inclusion from Category.assoc _ _ _]
    change Mono (p.root.hom.hom.hom ≫ U.inclusion.hom.hom)
    infer_instance
  have hcharacter (R : TestAlgebra k) (b : Rˣ) :
      characterValue α R (cocharacterPoint cochar R b) = (b : R) ^ 2 := by
    let t := cocharacterPoint cochar R b
    let z : GroupPoints C.torus.group R := unitPoint R b ≫ d
    let g : GroupPoints H R := z ≫ C.torus.inclusion.hom.hom
    let M := wordMatrix.{u} b * (wordMatrix.{u} (1 : Rˣ))⁻¹
    let diagonal (j : Index.{u}) := if j = i0 then (b : R) else (↑b⁻¹ : R)
    have hg : g = rankOneWord x y R b * (rankOneWord x y R 1)⁻¹ := by exact hd R b
    have hM : M.val = Matrix.diagonal diagonal := normalizedWordMatrix b
    have hproj : g ≫ P.hom.hom.hom = projectiveMatrixPoint P R M := by
      rw [hg]
      let ρ := (((groupPointsFunctor k).map P.hom).app R).hom
      change ρ (_ * _) = projectiveMatrixPoint P R (_ * _)
      rw [map_mul, map_inv, map_mul, map_inv]
      exact congrArg₂ (· * ·) (rankOneWord_projective P A D.contracting E.contracting p n R b)
        (congrArg Inv.inv (rankOneWord_projective P A D.contracting E.contracting p n R 1))
    have hr : (b : R) ^ 2 * diagonal i1 = diagonal i0 := by
      simp [diagonal, i1_ne_i0, pow_two, mul_assoc]
    have h := scalarAction_from_diagonal_lift P D i0_ne_i1 p R g
      (torus_points_centralize_limit C.torus D hplus R z) (hinj R)
      M diagonal hM hproj hr (1 : R)
    have hgl : g ≫ l.hom.hom = t ≫ T.inclusion.hom.hom := by
      have he := hinc R t
      rw [← Category.assoc (f := t), hd'] at he
      simpa only [g, z, Category.assoc] using he
    have h' := congrArg (· ≫ l.hom.hom) h
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hgl, ← rootPoint_comp, ← rootPoint_comp] at h'
    have hα := hx' R t (1 : R)
    apply rootPoint_injective_of_mono (x ≫ l) R
    rw [← mul_one (characterValue α R t), ← mul_one ((b : R) ^ 2)]
    exact hα.symm.trans h'
  exact corootReflection_of_word T hT α (x ≫ l) (y ≫ l) hx' hy' cochar rep hrep hword
    (pairing_two_of_characterValues α cochar hcharacter)



/-- The rank-one group, its matched root coordinates, and the reflection follow
from the centralizer, projective automorphism and marked flag premises. -/
theorem rankOneRootGroups_conditional
    (centralizer : CentralizerAndPositiveCocharacter.{u})
    (projective : ProjectiveLineAutomorphisms.{u})
    (geometry : RankOneFlagGeometry.{u}) : RankOneRootGroups.{u} := by
  intro k _ G hG T hT hmax α hα
  obtain ⟨C, cochar, hC, hcochar, D, E, hpair, Q, ⟨F⟩⟩ :=
    rankOneFlagData centralizer geometry G hG T hT hmax α hα
  have hp := hpair
  obtain ⟨hplus, hminus, hB, hsmooth, hsmooth', _, _, hsplit, hsplit'⟩ := hp
  have hAff := (Unipotent.closedSubgroupAlgebraicGroup C.subgroup).property.1
  obtain ⟨P, A, hs, hP, ⟨p⟩, ⟨n⟩⟩ :=
    rankOneTransvectionPairWithMatrices projective hAff C.torus D E
      hplus hminus hB hsplit hsplit' F
  have hroot := (positive_root_space_comparison G T α hα C cochar hcochar D hsplit
    (identityLieStructure G)).2
  obtain ⟨hx, hy⟩ := rankOne_matched_scalarActions T α C hAff D E hplus hminus hB
    F P hs hP A p n hroot.le
  let U := GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup D.contracting
  let V := GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup E.contracting
  have hU : IsRootSubgroup T U α :=
    ⟨hsmooth, hsplit, contracting_normalized_in_ambient T C _ D hplus, hroot.le⟩
  have hV : IsRootSubgroup T V α⁻¹ :=
    ⟨hsmooth', hsplit', contracting_normalized_in_ambient T C _ E hminus,
      tangent_weight_of_scalarAction T V α⁻¹ A n.root hy⟩
  exact ⟨C, cochar, hC, hcochar, D, E, hpair, Q, F, P, A, p, n, hU, hV, hx, hy,
    coroot_from_matched_rankOne_word T hT α C hAff D E hplus hB F P A p n hx hy⟩



private theorem torusCharacter_zpow_eq_one {T : GroupScheme k}
    (ha : IsAffine T.X.left) (ht : GeometricRadicals.IsTorus T)
    {χ : Character T} {n : ℤ} (hn : n ≠ 0) (hχ : χ ^ n = 1) : χ = 1 := by
  let G : AffineGroupCategory k := ⟨T, ha⟩
  let A := coordinateHopf G
  let i := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso G)
  have hA : Specs.CharacterDescent.IsTorus A := by
    apply (LinearAlgebraicGroups.CharacterDescent.torusOnSchemes A).mpr
    obtain ⟨E, _, _, _, r, ⟨j⟩⟩ := ht
    exact ⟨E, inferInstance, inferInstance, inferInstance, r,
      ⟨(groupBaseChange k E).mapIso i ≪≫ j⟩⟩
  obtain ⟨E, _, _, _, r, ⟨q⟩⟩ := hA
  let e := (LinearAlgebraicGroups.CharacterDescent.groupLikeCharacterEquiv A).trans (charactersOfIso i)
  let f := LinearAlgebraicGroups.CharacterDescent.baseChangeCharacterMap E A
  let j := (groupLikeIso q.symm).trans
    (LinearAlgebraicGroups.CharacterDescent.monomialCharacterEquiv (M := StandardLattice.{u} r) E).symm
  let p : Character T →* StandardLattice.{u} r :=
    j.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  have hinj : Function.Injective p := j.injective.comp
    ((LinearAlgebraicGroups.CharacterDescent.baseChangeCharacterMap_injective E A).comp e.symm.injective)
  have hp := congrArg p hχ
  rw [map_zpow, map_one] at hp
  apply hinj
  rw [map_one]
  funext l
  have h := congrFun hp l
  apply ULift.ext
  have hw := congrArg (fun v : IntegerCharacters => Multiplicative.toAdd v.down) h
  change n • Multiplicative.toAdd ((p χ l).down) = 0 at hw
  change Multiplicative.toAdd ((p χ l).down) = 0
  exact (mul_eq_zero.mp hw).resolve_left hn

private def restrictCharacter {S T : GroupScheme k} (i : S ⟶ T) :
    Character T →* Character S where
  toFun χ := i ≫ χ
  map_one' := by
    apply Grp.hom_ext
    exact MonObj.comp_one _
  map_mul' α β := by
    apply Grp.hom_ext
    exact MonObj.comp_mul _ _ _

private theorem proportional_restriction_trivial {G : GroupScheme k} (T : ClosedSubgroup G)
    (ha : IsAffine G.X.left) {α β : Character T.group}
    (C : Centralizer T α) (h : Proportional α β) :
    C.kernelTorus.inclusion ≫ β = 1 := by
  obtain ⟨m, n, _, hn, he⟩ := h
  let f := restrictCharacter C.kernelTorus.inclusion
  have ha' : f α = 1 := C.kernelTorus_largest.2.1
  have h' := congrArg f he
  rw [map_zpow, map_zpow, ha', one_zpow] at h'
  exact torusCharacter_zpow_eq_one (affineSubgroup (affineSubgroup ha T) C.kernelTorus)
    C.kernelTorus_largest.1 hn h'.symm

private theorem proportional_pairing_ne_zero {T : GroupScheme k}
    (hT : IsSplitTorus T) {α β : Character T} (h : Proportional α β)
    (cochar : Cocharacter T) (hpos : 0 < pairing T α cochar) :
    pairing T β cochar ≠ 0 := by
  obtain ⟨m, n, hm, _, hmn⟩ := h
  obtain ⟨hcomm, _, _, _, _, P, _, hP⟩ := CharacterPairing.perfectCharacterPairing T hT
  letI := hcomm
  have h := congrArg (fun e : Character T => P (Additive.ofMul e) (Additive.ofMul cochar)) hmn
  change P (m • Additive.ofMul α) (Additive.ofMul cochar) =
    P (n • Additive.ofMul β) (Additive.ofMul cochar) at h
  simp only [map_zsmul, LinearMap.smul_apply, hP, zsmul_eq_mul] at h
  intro hz
  rw [hz, mul_zero] at h
  exact (mul_ne_zero hm hpos.ne') h

private theorem weight_in_negative_contracting (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (α : Character T.group) (C : Centralizer T α)
    (cochar : Cocharacter T.group)
    (E : LimitDecomposition (oppositeCocharacter (cochar ≫ C.torusIso.hom ≫ C.torus.inclusion)))
    {β : Character T.group} (hβ : C.kernelTorus.inclusion ≫ β = 1)
    (hneg : pairing T.group β cochar < 0) {v : Lie k G.val} (hv : v ∈ adjointWeightVectors T β) :
    ∃ q : Lie k E.contracting.group, mapPointKernel (E.contracting.inclusion ≫ C.subgroup.inclusion) q = v := by
  obtain ⟨w, hw⟩ := liftWeightToCentralizer T α C G.property.1 hβ hv
  let H := Unipotent.closedSubgroupAlgebraicGroup C.subgroup
  let s := identityLieStructure H
  letI := s.lieRing
  letI := s.lieAlgebra
  let c := cochar ≫ C.torusIso.hom ≫ C.torus.inclusion
  obtain ⟨W⟩ := CocharacterDynamics.existsAdjointWeightBasis H c s
  have h := CocharacterDynamics.relativeOppositeContractingWeights H c E s W
    (baseTest k) (W.basis.equivFun w)
  have hj := restrictedCocharacterEigenvector T C.subgroup (C.torusIso.hom ≫ C.torus.inclusion)
    C.torus_inclusion cochar β w (hw.symm ▸ hv)
  obtain ⟨q, hq⟩ := h.mpr (fun j hge => eigenvector_coordinates c W w _ hj j (by omega))
  refine ⟨q, ?_⟩
  rw [((lieFunctoriality k).2.2) E.contracting.group C.subgroup.group G.val]
  have hqw : mapPointKernel E.contracting.inclusion q = w :=
    Subtype.ext (hq.trans (W.coordinates.at_base w))
  rw [hqw, hw]

private theorem root_weight_unique (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) {α β : Character T.group} {v : Lie k G.val} (hv : v ≠ 0)
    (ha : v ∈ adjointWeightVectors T α) (hb : v ∈ adjointWeightVectors T β) :
    α = β := by
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, basis, C, L, mat, Ad, hAd, _, _⟩ := adjointRepresentation k G s
  obtain ⟨j, hj⟩ : ∃ j : ULift.{u} (Fin n), basis.equivFun v j ≠ 0 := by
    by_contra! h
    apply hv
    refine (basis.equivFun.injective ?_).trans (canonicalZero_eq s).symm
    exact (funext h).trans basis.equivFun.map_zero.symm
  apply CharacterPairing.characterValuesDetectCharacters hT
  intro R t
  have ha' := (adjointWeightVectors_iff C mat Ad hAd T α v).mp ha R t
  have hb' := (adjointWeightVectors_iff C mat Ad hAd T β v).mp hb R t
  have he := congrFun (ha'.symm.trans hb') j
  change characterValue α R t * algebraMap k R (basis.equivFun v j) =
    characterValue β R t * algebraMap k R (basis.equivFun v j) at he
  exact ((hj.isUnit.map (algebraMap k R)).mul_left_inj).mp he

/-- The nonzero Lie weights on the rational line through a root are exactly its opposite pair. -/
theorem rootProportionality_conditional
    (centralizer : CentralizerAndPositiveCocharacter.{u})
    (projective : ProjectiveLineAutomorphisms.{u})
    (geometry : RankOneFlagGeometry.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (α : Character T.group) (hα : α ∈ absoluteRoots T) (β : Character T.group) :
    β ∈ absoluteRoots T ∧ Proportional α β ↔ β = α ∨ β = α⁻¹ := by
  obtain ⟨C, cochar, _, hc, D, E, _, Q, F, P, A, p, n, hU, hV, _⟩ :=
    rankOneRootGroups_conditional centralizer projective geometry G hG T hT hmax α hα
  let U := GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup D.contracting
  let V := GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup E.contracting
  constructor
  · rintro ⟨⟨_, v, hv, hv0⟩, hp⟩
    have hβ := proportional_restriction_trivial T G.property.1 C hp
    rcases lt_or_gt_of_ne (proportional_pairing_ne_zero hT hp cochar hc) with hn | hp
    · obtain ⟨w, hw⟩ := weight_in_negative_contracting G T α C cochar E hβ hn hv
      exact Or.inr (root_weight_unique G T hT hv0 hv (hV.2.2.2 ⟨w, hw⟩))
    · obtain ⟨w, hw⟩ := weight_in_positive_contracting G T α C cochar D hβ hp hv
      exact Or.inl (root_weight_unique G T hT hv0 hv (hU.2.2.2 ⟨w, hw⟩))
  · rintro (rfl | rfl)
    · exact ⟨hα, ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩⟩
    refine ⟨⟨by simpa using hα.1, ?_⟩, ⟨1, -1, by decide, by decide, by simp⟩⟩
    let w : Lie k V.group :=
      ⟨rootPoint n.root.hom (dualTest k) (DualNumber.eps : DualNumber k), rootPoint_eps_reduces _⟩
    refine ⟨mapPointKernel V.inclusion w, hV.2.2.2 ⟨w, rfl⟩, ?_⟩
    intro hz
    have he : w = 0 := mapPointKernel_injective V (hz.trans (map_zero (mapPointKernel V.inclusion)).symm)
    have hw := congrArg (fun p : Lie k V.group => p.toMul.val) he
    change rootPoint n.root.hom (dualTest k) (DualNumber.eps : DualNumber k) = 1 at hw
    rw [← rootPoint_zero n.root.hom (dualTest k)] at hw
    have hc := rootPoint_injective_of_mono n.root.hom (dualTest k) hw
    exact one_ne_zero (congrArg TrivSqZeroExt.snd hc)



private theorem additive_normalization_on_points {G : GroupScheme k}
    (T V : ClosedSubgroup G) (hnorm : Normalizes V.inclusion T.inclusion.hom.hom)
    (A : AdditiveLine k) (e : A.group ≅ V.group) (R : TestAlgebra k)
    (t : GroupPoints T.group R) (b : R) :
    ∃ s : R, let g : GroupPoints G R := t ≫ T.inclusion.hom.hom
      let x := e.hom ≫ V.inclusion
      g * rootPoint x R b * g⁻¹ = rootPoint x R s := by
  have hc := ((normalizesIff k V.inclusion V.isClosedImmersion _ _).mp hnorm).1
  obtain ⟨q, hq⟩ := (conjugateLe_iff V.inclusion T.inclusion.hom.hom).mp hc
    ((testSpec k).obj (op R)) t (rootPoint e.hom R b)
  let q' : GroupPoints A.group R := q ≫ e.inv.hom.hom
  obtain ⟨s, hs⟩ := (additivePoints A R).surjective q'
  have eInv : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ := (Grp.forget _).congr_map e.inv_hom_id
  have hq' : rootPoint e.hom R s = q := by
    rw [rootPoint_eq, hs, Category.assoc, eInv, Category.comp_id]
  refine ⟨s, ?_⟩
  dsimp only
  rw [rootPoint_comp, rootPoint_comp, hq', hq]

private theorem normalized_additive_polynomial {G : GroupScheme k}
    (T V : ClosedSubgroup G) (hnorm : Normalizes V.inclusion T.inclusion.hom.hom)
    (A : AdditiveLine k) (i : A.group ≅ V.group) (R : TestAlgebra k)
    (t : GroupPoints T.group R) :
    ∃ f : Polynomial R, ∀ (S : TestAlgebra k) (a : R ⟶ S) (b : S),
      let g : GroupPoints G S := (mapPoints a t) ≫ T.inclusion.hom.hom
      let x := i.hom ≫ V.inclusion
      g * rootPoint x S b * g⁻¹ = rootPoint x S (Polynomial.aevalTower a.hom b f) := by
  let P := CocharacterDynamics.polynomialAlgebra R
  let c := polynomialConstants R
  obtain ⟨p, hp⟩ := additive_normalization_on_points T V hnorm A i P (mapPoints c t) Polynomial.X
  refine ⟨p, ?_⟩
  intro S a b
  let e : P ⟶ S := CommAlgCat.ofHom (Polynomial.aevalTower a.hom b)
  have ha : c ≫ e = a := by
    apply CommAlgCat.hom_ext
    exact Polynomial.aevalTower_comp_toAlgHom a.hom b
  dsimp only at hp
  have h := congrArg ((((groupPointsFunctor k).obj G).map e).hom) hp
  rw [map_mul, map_mul, map_inv] at h
  change (show GroupPoints G S from mapPoints e (mapPoints c t ≫ T.inclusion.hom.hom)) *
      (show GroupPoints G S from mapPoints e (rootPoint (i.hom ≫ V.inclusion) P Polynomial.X)) *
      (show GroupPoints G S from mapPoints e (mapPoints c t ≫ T.inclusion.hom.hom))⁻¹ =
    mapPoints e (rootPoint (i.hom ≫ V.inclusion) P p) at h
  have h1 : mapPoints e (mapPoints c t ≫ T.inclusion.hom.hom) =
      mapPoints a t ≫ T.inclusion.hom.hom := by
    change mapPoints e (mapPoints c t) ≫ T.inclusion.hom.hom = _
    rw [← mapPoints_comp, ha]
  rw [h1, rootPoint_natural, rootPoint_natural,
    show e.hom Polynomial.X = b from Polynomial.aevalTower_X _ _] at h
  exact h

private theorem normalized_additive_linear {G : GroupScheme k}
    (T V : ClosedSubgroup G) (hnorm : Normalizes V.inclusion T.inclusion.hom.hom)
    (A : AdditiveLine k) (i : A.group ≅ V.group) (R : TestAlgebra k) [IsDomain R]
    (t : GroupPoints T.group R) :
    ∃ c : R, ∀ (S : TestAlgebra k) (a : R ⟶ S) (b : S),
      let g : GroupPoints G S := (mapPoints a t) ≫ T.inclusion.hom.hom
      let x := i.hom ≫ V.inclusion
      g * rootPoint x S b * g⁻¹ = rootPoint x S (a.hom c * b) := by
  obtain ⟨p, hp⟩ := normalized_additive_polynomial T V hnorm A i R t
  obtain ⟨q, hq⟩ := normalized_additive_polynomial T V hnorm A i R t⁻¹
  let x := i.hom ≫ V.inclusion
  letI : Mono V.inclusion.hom.hom := mono_over _ V.isClosedImmersion
  haveI : Mono x.hom.hom := by
    change Mono (i.hom.hom.hom ≫ V.inclusion.hom.hom)
    infer_instance
  let P := CocharacterDynamics.polynomialAlgebra R
  let c := polynomialConstants R
  let g : GroupPoints G P := mapPoints c t ≫ T.inclusion.hom.hom
  have hinv : mapPoints c t⁻¹ ≫ T.inclusion.hom.hom = g⁻¹ := by
    change ((((groupPointsFunctor k).map T.inclusion).app P).hom.comp
      (((groupPointsFunctor k).obj T.group).map c).hom) t⁻¹ = _
    rw [map_inv]
    rfl
  have hp' := hp P c Polynomial.X
  have hq' := hq P c p
  change g * rootPoint x P Polynomial.X * g⁻¹ = rootPoint x P (Polynomial.aevalTower c.hom Polynomial.X p) at hp'
  change (show GroupPoints G P from mapPoints c t⁻¹ ≫ T.inclusion.hom.hom) *
    rootPoint x P p * (show GroupPoints G P from mapPoints c t⁻¹ ≫ T.inclusion.hom.hom)⁻¹ =
      rootPoint x P (Polynomial.aevalTower c.hom p q) at hq'
  change _ = rootPoint x P (p.comp Polynomial.X) at hp'
  rw [Polynomial.comp_X] at hp'
  rw [hinv, ← hp', inv_inv] at hq'
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at hq'
  have hqp : q.comp p = Polynomial.X := by
    symm
    exact rootPoint_injective_of_mono x P hq'
  have hd : q.natDegree * p.natDegree = 1 := by
    rw [← Polynomial.natDegree_comp, hqp, Polynomial.natDegree_X]
  have hdeg : p.natDegree = 1 := by
    apply Nat.dvd_one.mp
    exact ⟨q.natDegree, hd.symm.trans (mul_comm _ _)⟩
  obtain ⟨z, _, w, hzw⟩ := Polynomial.natDegree_eq_one.mp hdeg
  have hzero := hp R (𝟙 R) 0
  dsimp only at hzero
  rw [rootPoint_zero, mul_one, mul_inv_cancel, ← hzw, map_add, map_mul,
    Polynomial.aevalTower_C, Polynomial.aevalTower_C, Polynomial.aevalTower_X,
    mul_zero, zero_add, ← rootPoint_zero x R] at hzero
  have hw : w = 0 := (rootPoint_injective_of_mono x R hzero).symm
  refine ⟨z, ?_⟩
  intro S a b
  have h := hp S a b
  dsimp only at h
  rw [← hzw, hw, map_add, map_mul, Polynomial.aevalTower_C, Polynomial.aevalTower_C,
    Polynomial.aevalTower_X, map_zero, add_zero] at h
  exact h



private theorem splitCoordinate_isDomain (r : ℕ) :
    IsDomain (MonoidAlgebra k (StandardLattice.{u} r)) := by
  let e : (Fin r →₀ ℤ) ≃+ (Fin r → ℤ) :=
    { toEquiv := Finsupp.equivFunOnFinite
      map_add' := fun _ _ => rfl }
  let q := (latticeCoordinates r).toAddEquiv.trans e.symm
  letI : UniqueSums (Additive (StandardLattice.{u} r)) := q.uniqueSums_iff.mpr inferInstance
  letI : UniqueProds (StandardLattice.{u} r) :=
    inferInstanceAs (UniqueProds (Multiplicative (Additive (StandardLattice.{u} r))))
  infer_instance

private theorem scalar_action_of_normalized_tangent {G : GroupScheme k}
    (T V : ClosedSubgroup G) (hT : IsSplitTorus T.group)
    (α : Character T.group) (hV : IsRootSubgroup T V α)
    (A : AdditiveLine k) (i : A.group ≅ V.group) :
    HasScalarAction T α (i.hom ≫ V.inclusion) := by
  obtain ⟨r, ⟨j⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  let R := CommAlgCat.of k (MonoidAlgebra k M)
  letI : IsDomain R := splitCoordinate_isDomain r
  let t : GroupPoints T.group R := j.hom.hom.hom
  let x := i.hom ≫ V.inclusion
  letI : Mono V.inclusion.hom.hom := mono_over _ V.isClosedImmersion
  letI : Mono x.hom.hom := by
    change Mono (i.hom.hom.hom ≫ V.inclusion.hom.hom)
    infer_instance
  obtain ⟨c, hc⟩ := normalized_additive_linear T V hV.2.2.1 A i R t
  have he : (⟨rootPoint x (dualTest k) (DualNumber.eps : DualNumber k),
      rootPoint_eps_reduces x⟩ : Lie k G) ∈ adjointWeightVectors T α := by
    apply hV.2.2.2
    refine ⟨⟨rootPoint i.hom (dualTest k) (DualNumber.eps : DualNumber k),
      rootPoint_eps_reduces i.hom⟩, Subtype.ext ?_⟩
    exact (rootPoint_comp i.hom V.inclusion _ _).symm
  have ht := weight_at_root_eps x T α he R t
  let B := CommAlgCat.of k (DualNumber R)
  have ht' := hc B (constants R) (DualNumber.eps : DualNumber R)
  have h := rootPoint_injective_of_mono x B (ht'.symm.trans ht)
  have hval := congrArg TrivSqZeroExt.snd h
  change c * 1 + 0 * 0 = characterValue α R t at hval
  simp only [mul_one, zero_mul, add_zero] at hval
  intro S s b
  let Y := specGroup (groupAlgebra k M)
  let f : Points Y.X S := s ≫ j.inv.hom.hom
  let φ := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a : R ⟶ S := (φ.preimage f).unop
  have ha : (testSpec k).map a.op = f := φ.map_preimage f
  have hts : mapPoints a t = s := by
    rw [mapPoints, ha]
    change (s ≫ j.inv.hom.hom) ≫ j.hom.hom.hom = _
    have hj : j.inv.hom.hom ≫ j.hom.hom.hom = 𝟙 _ := (Grp.forget _).congr_map j.inv_hom_id
    rw [Category.assoc, hj, Category.comp_id]
  have h := hc S a b
  rw [hval, ← characterValue_natural α a, hts] at h
  exact h



private theorem root_coordinate_lifts_to_centralizer {G : GroupScheme k}
    (T : ClosedSubgroup G) {α : Character T.group} (C : Centralizer T α)
    {A : AdditiveLine k} (x : A.group ⟶ G) (hx : HasScalarAction T α x) :
    ∃ f : A.group ⟶ C.subgroup.group, f ≫ C.subgroup.inclusion = x := by
  apply subgroupInclusionFactors (additiveLineGroup A).property.1 C.subgroup x
  intro R p
  obtain ⟨b, rfl⟩ := (additivePoints A R).surjective p
  change ∃ z : GroupPoints C.subgroup.group R, z ≫ C.subgroup.inclusion.hom.hom =
    additivePoints A R b ≫ x.hom.hom
  rw [← rootPoint_eq]
  apply (C.centralizes _ _).mp
  unfold Centralizes
  apply hom_ext_on_affine_tests
  intro U a
  rw [comp_conjugateFamily]
  let S := GeometricBorelConjugacy.subgroupOfSubgroup T C.kernelTorus
  let s : GroupPoints C.kernelTorus.group U := a ≫ fst S.group.X ((testSpec k).obj (op R))
  let t : GroupPoints T.group U := s ≫ C.kernelTorus.inclusion.hom.hom
  let e : Points ((testSpec k).obj (op R)) U := a ≫ snd _ _
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let j : R ⟶ U := (F.preimage e).unop
  have hj : (testSpec k).map j.op = e := F.map_preimage e
  have he : a ≫ snd _ _ ≫ rootPoint x R b = rootPoint x U (j.hom b) := by
    rw [← Category.assoc]
    change e ≫ rootPoint x R b = _
    rw [← hj]
    exact rootPoint_natural x j b
  have hα : characterValue α U t = 1 := by
    change characterValue (C.kernelTorus.inclusion ≫ α) U s = _
    rw [C.kernelTorus_largest.2.1, characterValue_one]
  have h := hx U t (j.hom b)
  rw [hα, one_mul] at h
  have hcomm := mul_inv_eq_iff_eq_mul.mp h
  rw [he]
  change rootPoint x U (j.hom b) * (show GroupPoints G U from t ≫ T.inclusion.hom.hom) *
    (rootPoint x U (j.hom b))⁻¹ = t ≫ T.inclusion.hom.hom
  exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm

private theorem root_coordinate_contracts {G : GroupScheme k}
    (T : ClosedSubgroup G) (α : Character T.group) (C : Centralizer T α)
    (c : Cocharacter T.group) (hc : 0 < pairing T.group α c)
    {A : AdditiveLine k} (f : A.group ⟶ C.subgroup.group)
    (hf : HasScalarAction T α (f ≫ C.subgroup.inclusion))
    (R : TestAlgebra k) (b : R) :
    HasLimit (c ≫ C.torusIso.hom ≫ C.torus.inclusion) (rootPoint f R b) 1 := by
  let n := pairing T.group α c
  let P := CocharacterDynamics.polynomialAlgebra R
  let L := laurentAlgebra R
  let z := CocharacterDynamics.laurentParameter R
  let w : P := Polynomial.C b * Polynomial.X ^ n.toNat
  letI := mono_over C.subgroup.inclusion.hom.hom C.subgroup.isClosedImmersion
  refine ⟨rootPoint f P w, ?_, ?_⟩
  · apply (cancel_mono C.subgroup.inclusion.hom.hom).mp
    rw [rootPoint_natural]
    let t : GroupPoints T.group L := cocharacterPoint c L z
    have ht : cocharacterPoint (c ≫ C.torusIso.hom ≫ C.torus.inclusion) L z ≫
        C.subgroup.inclusion.hom.hom = t ≫ T.inclusion.hom.hom := by
      have he := congrArg (fun a : T.group ⟶ G => t ≫ a.hom.hom) C.torus_inclusion
      exact he
    unfold orbit
    dsimp only
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, ht, rootPoint_natural, ← rootPoint_comp,
      ← rootPoint_comp]
    have heval := (CharacterPairing.characterPairingComposition T.group α c).2 L z
    have hpow : (polynomialToLaurent R).hom w =
        characterValue α L t * (laurentConstants R).hom b := by
      rw [heval, laurentParameter_zpow]
      change (Polynomial.C b * Polynomial.X ^ n.toNat).toLaurent = LaurentPolynomial.T n * LaurentPolynomial.C b
      rw [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow, Int.toNat_of_nonneg hc.le, mul_comm]
    rw [hpow]
    exact (hf L t ((laurentConstants R).hom b)).symm
  · rw [rootPoint_natural]
    have hn : n.toNat ≠ 0 := by omega
    have hw : (polynomialEvaluate R 0).hom w = 0 := by
      change Polynomial.aevalTower (AlgHom.id k R) 0 (Polynomial.C b * Polynomial.X ^ n.toNat) = _
      rw [map_mul, map_pow, Polynomial.aevalTower_X, zero_pow hn, mul_zero]
    rw [hw, rootPoint_zero]

private theorem two_additive_subgroups_equal
    {G : GroupScheme k} (U V : ClosedSubgroup G) (A B : AdditiveLine k)
    (p : A.group ≅ U.group) (q : B.group ≅ V.group)
    (m : B.group ⟶ U.group) (hm : m ≫ U.inclusion = q.hom ≫ V.inclusion) :
    SameSubgroup U V := by
  have hClosed : IsClosedImmersion (q.hom ≫ V.inclusion).hom.hom.left := by
    change IsClosedImmersion (q.hom.hom.hom.left ≫ V.inclusion.hom.hom.left)
    letI : IsIso q.hom.hom.hom.left :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso q.hom
    letI := V.isClosedImmersion
    exact IsClosedImmersion.comp _ _
  have hcomp : IsClosedImmersion (m.hom.hom.left ≫ U.inclusion.hom.hom.left) := by
    change IsClosedImmersion (m ≫ U.inclusion).hom.hom.left
    exact hm.symm ▸ hClosed
  letI := U.isClosedImmersion
  letI := hcomp
  have hmClosed := IsClosedImmersion.of_comp_isClosedImmersion m.hom.hom.left U.inclusion.hom.hom.left
  let v := m ≫ p.inv
  have hv : IsClosedImmersion v.hom.hom.left := by
    change IsClosedImmersion (m.hom.hom.left ≫ p.inv.hom.hom.left)
    letI : IsIso p.inv.hom.hom.left :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso p.inv
    letI := hmClosed
    exact IsClosedImmersion.comp _ _
  letI := additiveLine_closedImmersion_isIso B A v hv
  let j := asIso v
  let e := q.symm ≪≫ j ≪≫ p
  have hv' : v ≫ p.hom = m := by
    change (m ≫ p.inv) ≫ p.hom = m
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hep : e.hom ≫ U.inclusion = V.inclusion := by
    change (q.inv ≫ v ≫ p.hom) ≫ U.inclusion = V.inclusion
    rw [hv', Category.assoc, hm, Iso.inv_hom_id_assoc]
  exact ⟨⟨e.inv, by rw [← hep, Iso.inv_hom_id_assoc]⟩, ⟨e.hom, hep⟩⟩

private theorem normalized_additive_subgroup_unique
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (α : Character T.group) (C : Centralizer T α)
    (c : Cocharacter T.group) (hc : 0 < pairing T.group α c)
    (D : LimitDecomposition (c ≫ C.torusIso.hom ≫ C.torus.inclusion))
    (A : AdditiveLine k) (p : A.group ≅ D.contracting.group)
    (V : ClosedSubgroup G.val) (hV : IsRootSubgroup T V α) :
    SameSubgroup (GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup D.contracting) V := by
  obtain ⟨ops, hd, he, hi, ⟨i⟩⟩ := hV.2.1
  let B : AdditiveLine k := ⟨ops, hd, he, hi⟩
  let q : B.group ≅ V.group := i.symm
  let x := q.hom ≫ V.inclusion
  have hx : HasScalarAction T α x := scalar_action_of_normalized_tangent T V hT α hV B q
  obtain ⟨f, hf⟩ := root_coordinate_lifts_to_centralizer T C x hx
  have hx' : HasScalarAction T α (f ≫ C.subgroup.inclusion) := by rwa [hf]
  have hpoints (R : TestAlgebra k) (b : GroupPoints B.group R) :
      ∃ z : GroupPoints D.contracting.group R, z ≫ D.contracting.inclusion.hom.hom =
        b ≫ f.hom.hom := by
    obtain ⟨t, rfl⟩ := (additivePoints B R).surjective b
    rw [← rootPoint_eq]
    exact (D.contracting_points R _).mp (root_coordinate_contracts T α C c hc f hx' R t)
  obtain ⟨m, hm⟩ := subgroupInclusionFactors (additiveLineGroup B).property.1 D.contracting f hpoints
  apply two_additive_subgroups_equal _ V A B p q m
  change m ≫ D.contracting.inclusion ≫ C.subgroup.inclusion = x
  rw [← Category.assoc, hm, hf]

/-- The root spaces, reducedness and unique smooth additive subgroups follow
from the rank-one data supplied by the conditional premises. -/
theorem rootSubgroups_conditional
    (centralizer : CentralizerAndPositiveCocharacter.{u})
    (projective : ProjectiveLineAutomorphisms.{u})
    (geometry : RankOneFlagGeometry.{u}) : RootSubgroups.{u} := by
  intro k _ G hG T hT hmax
  let s := identityLieStructure G
  have h0 := CharacterPairing.zeroWeightSpace G hG T hT hmax s
  refine ⟨⟨h0.1, h0.2.symm.trans (CharacterPairing.adjointWeightSpaceVectors G T s 1)⟩, ?_⟩
  intro α hα
  obtain ⟨C, c, _, hc, D, _, hp, _, _, _, A, p, _, hU, _, hx, _, _⟩ :=
    rankOneRootGroups_conditional centralizer projective geometry G hG T hT hmax α hα
  let U := GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup D.contracting
  have hcomp s' := positive_root_space_comparison G T α hα C c hc D hU.2.1 s'
  refine ⟨fun s' => (hcomp s').1,
    rootProportionality_conditional centralizer projective geometry G hG T hT hmax α hα,
    U, hU, mapPointKernel_injective U, (hcomp s).2, ⟨A, p.root, hx⟩, ?_⟩
  exact normalized_additive_subgroup_unique G T hT α C c hc D A p.root


section Dimension

open WithConv Bialgebra
open scoped DirectSum Matrix

open LinearAlgebraicGroups.RationalRepresentations (representationCoactionComparison evaluationComparison)
open private tensorCoordinate_sum_basis tensor_eq_sum_basis tensorCoordinate_tmul tensorCoordinate_evaluation
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private algebraPoint extendCoordinates characterValue_monomial
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private standardLatticeDomain smoothStandardLattice
  from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open private irreducible_of_geometricallyConnected from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

set_option maxHeartbeats 1500000

private theorem coaction_coordinate_formula {V I : Type u} [AddCommGroup V] [Module k V]
    [Fintype I] [DecidableEq I] (A : HopfAlgebraCategory k) (b : Module.Basis I k V)
    (ρ : RightComodule k A V) (R : TestAlgebra k) (a : A →ₐ[k] R)
    (M : Matrix I I R) (hM : ∀ j,
      RationalRepresentations.evaluate A ρ a (b j) = ∑ i, b i ⊗ₜ[k] M i j)
    (v : V) (i : I) :
    RationalRepresentations.tensorCoordinate b i (RationalRepresentations.evaluate A ρ a v) =
      (M *ᵥ fun j => algebraMap k R (b.equivFun v j)) i := by
  calc
    _ = RationalRepresentations.tensorCoordinate b i
        (RationalRepresentations.evaluate A ρ a (∑ j, b.equivFun v j • b j)) := by
        rw [b.sum_equivFun]
    _ = ∑ j, b.equivFun v j • M i j := by
      have hj (j : I) : RationalRepresentations.tensorCoordinate b i
          (RationalRepresentations.evaluate A ρ a (b j)) = M i j :=
        (congrArg (RationalRepresentations.tensorCoordinate b i) (hM j)).trans
          (tensorCoordinate_sum_basis b (fun l => M l j) i)
      simp only [map_sum, map_smul, hj]
    _ = _ := by
      simp only [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]

private theorem coaction_eq_iff_eigenvector {V I : Type u} [AddCommGroup V] [Module k V]
    [Fintype I] [DecidableEq I] (A : HopfAlgebraCategory k) (b : Module.Basis I k V)
    (ρ : RightComodule k A V) (M : ∀ R : TestAlgebra k, (A →ₐ[k] R) → Matrix I I R)
    (hM : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (j : I),
      RationalRepresentations.evaluate A ρ a (b j) = ∑ i, b i ⊗ₜ[k] M R a i j)
    (v : V) (g : A) :
    ρ.coaction v = v ⊗ₜ[k] g ↔ ∀ (R : TestAlgebra k) (a : A →ₐ[k] R),
      M R a *ᵥ (fun j => algebraMap k R (b.equivFun v j)) =
        a g • (fun j => algebraMap k R (b.equivFun v j)) := by
  have hcoord (R : TestAlgebra k) (a : A →ₐ[k] R) (i : I) :
      RationalRepresentations.tensorCoordinate b i
        (RationalRepresentations.evaluate A ρ a v) =
          (M R a *ᵥ (fun j => algebraMap k R (b.equivFun v j))) i :=
    coaction_coordinate_formula A b ρ R a (M R a) (hM R a) v i
  have heval (R : TestAlgebra k) (a : A →ₐ[k] R) (i : I) :
      RationalRepresentations.tensorCoordinate b i (RationalRepresentations.evaluate A ρ a v) =
        a (RationalRepresentations.tensorCoordinate b i (ρ.coaction v)) :=
    tensorCoordinate_evaluation b a.toLinearMap (ρ.coaction v) i
  have hpure (R : TestAlgebra k) (a : A →ₐ[k] R) (i : I) :
      (a g • (fun j => algebraMap k R (b.equivFun v j))) i =
        a (RationalRepresentations.tensorCoordinate b i (v ⊗ₜ[k] g)) := by
    change a g * algebraMap k R (b.equivFun v i) = _
    rw [tensorCoordinate_tmul, Module.Basis.coord_apply, Algebra.smul_def, map_mul, AlgHom.commutes]
    exact mul_comm _ _
  constructor
  · intro h R a
    funext i
    rw [← hcoord R a i, heval R a i, hpure R a i, h]
  · intro h
    let R := CommAlgCat.of k A
    let a : A →ₐ[k] R := AlgHom.id k A
    have h' (i : I) : RationalRepresentations.tensorCoordinate b i (ρ.coaction v) =
        RationalRepresentations.tensorCoordinate b i (v ⊗ₜ[k] g) :=
      ((heval R a i).symm.trans (hcoord R a i)).trans ((congrFun (h R a) i).trans (hpure R a i))
    calc
      ρ.coaction v = ∑ i, b i ⊗ₜ[k] RationalRepresentations.tensorCoordinate b i (ρ.coaction v) :=
        (tensor_eq_sum_basis b _).symm
      _ = ∑ i, b i ⊗ₜ[k] RationalRepresentations.tensorCoordinate b i (v ⊗ₜ[k] g) := by simp_rw [h']
      _ = _ := tensor_eq_sum_basis b _

private theorem torus_point_from_coordinates {T : GroupScheme k} (r : ℕ)
    (i : (DiagonalizableGroups.diagonalGroup k (StandardLattice.{u} r)).val ≅ T)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    ∃ a : groupAlgebra k (StandardLattice.{u} r) →ₐ[k] R,
      algebraPoint R a ≫ i.hom.hom.hom = t := by
  let D := (DiagonalizableGroups.diagonalGroup k (StandardLattice.{u} r)).val
  let p : GroupPoints D R := t ≫ i.inv.hom.hom
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a := (F.preimage p).unop.hom
  have ha : algebraPoint R a = p := F.map_preimage p
  refine ⟨a, ?_⟩
  rw [ha]
  have hi : i.inv.hom.hom ≫ i.hom.hom.hom = 𝟙 _ := (Grp.forget _).congr_map i.inv_hom_id
  change (_ ≫ i.inv.hom.hom) ≫ i.hom.hom.hom = _
  rw [Category.assoc, hi, Category.comp_id]

/-- The adjoint weight spaces are the internal sum of the actual character weights. -/
private theorem adjointWeightsInternal (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (s : IdentityLieStructure G.val) : by
    classical
    letI := s.lieRing
    letI := s.lieAlgebra
    exact DirectSum.IsInternal (fun χ : Character T.group => adjointWeightSpace T χ s) := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨_, b, C, L, mat, Ad, hAd, _, _⟩ := adjointRepresentation k G s
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  let M := StandardLattice.{u} r
  letI : DecidableEq M := Classical.decEq M
  let A := groupAlgebra k M
  let DT := DiagonalizableGroups.diagonalGroup k M
  let B : AffineGroupCategory k := ⟨DT.val, DT.property.1⟩
  let f : B.val ⟶ L.val := i.hom ≫ T.inclusion ≫ Ad
  let e := hopfSpecPointIso A
  obtain ⟨E, hE⟩ :=
    representationCoactionComparison A b B L.val e mat
  let ρ := E f
  let chars := χ.trans (charactersOfIso i)
  have heval (R : TestAlgebra k) (a : A →ₐ[k] R) (m : M) :
      characterValue (chars m) R (algebraPoint R a ≫ i.hom.hom.hom) =
        a (MonoidAlgebra.single m 1) := by
    change characterValue (i.inv ≫ χ m) R (algebraPoint R a ≫ i.hom.hom.hom) = _
    have he : ((algebraPoint R a ≫ i.hom.hom.hom) ≫ (i.inv ≫ χ m).hom.hom) =
        algebraPoint R a ≫ (χ m).hom.hom := by
      change _ ≫ i.hom.hom.hom ≫ i.inv.hom.hom ≫ (χ m).hom.hom = _
      have hi : i.hom.hom.hom ≫ i.inv.hom.hom = 𝟙 _ := (Grp.forget _).congr_map i.hom_inv_id
      rw [← Category.assoc (f := i.hom.hom.hom), hi, Category.id_comp]
    unfold characterValue
    dsimp only
    rw [he]
    change characterValue (χ m) R (algebraPoint R a) = _
    rw [hχ, characterValue_monomial]
  have heval' (R : TestAlgebra k) (a : A →ₐ[k] R) (m : M) :
      characterValue (chars m) R (algebraPoint R a ≫ i.hom.hom.hom) =
        a (MonoidAlgebra.of k M m) := heval R a m
  let M' (R : TestAlgebra k) (a : A →ₐ[k] R) : Matrix _ _ R :=
    ((mat.hom.app R).hom (((groupPointsFunctor k).map f).app R (e.hom.app R (toConv a)))).val
  have hM (R : TestAlgebra k) (a : A →ₐ[k] R) (j) :
      RationalRepresentations.evaluate A ρ a (b j) = ∑ i, b i ⊗ₜ[k] M' R a i j :=
    evaluationComparison A b B L.val e mat f ρ (hE f) R a j
  have hformula (R : TestAlgebra k) (a : A →ₐ[k] R) :
      M' R a =
        ((mat.hom.app R).hom (((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app R
          (algebraPoint R a ≫ i.hom.hom.hom))).val := rfl
  have hW (m : M) : adjointWeightSpace T (chars m) s = WeightDecomposition.weightSpace ρ m := by
    apply Submodule.ext
    intro v
    change v ∈ (adjointWeightSpace T (chars m) s : Set (Lie k G.val)) ↔ _
    rw [CharacterPairing.adjointWeightSpaceVectors G T s (chars m),
      adjointWeightVectors_iff C mat Ad hAd T (chars m) v, WeightDecomposition.mem_weightSpace,
      coaction_eq_iff_eigenvector A b ρ M' hM v (MonoidAlgebra.of k M m)]
    constructor
    · intro hv R a
      rw [hformula, ← heval' R a m]
      exact hv R (algebraPoint R a ≫ i.hom.hom.hom)
    · intro hv R t
      obtain ⟨a, rfl⟩ := torus_point_from_coordinates r i R t
      dsimp only
      rw [← hformula R a, heval' R a m]
      exact hv R a
  have hi := WeightDecomposition.weightDecomposition ρ
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · have he : (fun χ : Character T.group => adjointWeightSpace T χ s) =
        (fun m : M => WeightDecomposition.weightSpace ρ m) ∘ chars.symm := by
      funext χ
      exact (congrArg (fun d => adjointWeightSpace T d s) (chars.apply_symm_apply χ).symm).trans (hW _)
    rw [he]
    exact hi.submodule_iSupIndep.comp chars.symm.injective
  · rw [← chars.surjective.iSup_comp (fun χ : Character T.group => adjointWeightSpace T χ s)]
    simp only [hW]
    exact hi.submodule_iSup_eq_top

private theorem affine_domain_krull_dimension (A : Type u) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k A).toENat : WithBot ℕ∞) := by
  letI : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have h := trdeg_add_eq k A (A := FractionRing A)
  rw [(trdeg_eq_zero_iff (R := A) (A := FractionRing A)).mpr inferInstance, add_zero] at h
  rw [h]
  exact P103.Ch06.AffineDimension.domain_dimension k A

private theorem krull_dimension_localization_away {A : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] {f : A} (hf : f ≠ 0) :
    ringKrullDim (Localization.Away f) = ringKrullDim A := by
  let B := Localization.Away f
  have hM : Submonoid.powers f ≤ nonZeroDivisors A :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf)
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (IsLocalization.injective B hM)
  letI : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp
    (RingHom.finiteType_holdsForLocalizationAway B f)
  letI : Algebra.FiniteType k B := Algebra.FiniteType.trans (R := k) (S := A) inferInstance inferInstance
  letI : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (Submonoid.powers f)
  have h := trdeg_add_eq k A (A := B)
  rw [(trdeg_eq_zero_iff (R := A) (A := B)).mpr inferInstance, add_zero] at h
  rw [affine_domain_krull_dimension (k := k) B, affine_domain_krull_dimension (k := k) A, h]

private theorem cotangent_fiber_localization_dimension {A : Type u} [CommRing A]
    [Algebra k A] (x : A →ₐ[k] k) {f : A} (hf : x f ≠ 0)
    [Algebra.IsStandardSmooth k (Localization.Away f)] [Nontrivial (Localization.Away f)] :
    Module.finrank k (PointTangent x) =
      Module.finrank (Localization.Away f) (KaehlerDifferential k (Localization.Away f)) := by
  let B := Localization.Away f
  let y : B →ₐ[k] k := IsLocalization.Away.liftAlgHom f ((isUnit_iff_ne_zero).mpr hf)
  letI : Algebra A k := x.toRingHom.toAlgebra
  letI : Algebra B k := y.toRingHom.toAlgebra
  letI : IsScalarTower A B k := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq (S := B) f ((isUnit_iff_ne_zero).mpr hf) a).symm
  letI : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (Rₘ := B) (Submonoid.powers f)
  obtain ⟨e, _⟩ := AdvCommAlg.Differentials.point_cotangent k A x
  let q := TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k (KaehlerDifferential k A)
  let t := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl k k)
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A B)
  rw [Subspace.dual_finrank_eq, e.finrank_eq, q.symm.finrank_eq, t.finrank_eq, Module.finrank_baseChange]

private theorem smooth_affine_domain_dimension_at_point {A : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.Smooth k A] (x : A →ₐ[k] k) :
    ringKrullDim A = (Module.finrank k (PointTangent x) : WithBot ℕ∞) := by
  classical
  let p := RingHom.ker x.toRingHom
  have hx : Function.Surjective x.toRingHom := fun a => ⟨algebraMap k A a, x.commutes a⟩
  letI : p.IsMaximal := RingHom.ker_isMaximal_of_surjective x.toRingHom hx
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  obtain ⟨f, hfp, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth k p
  have hf : x f ≠ 0 := hfp
  have hf0 : f ≠ 0 := fun h => hf (h ▸ map_zero x)
  let B := Localization.Away f
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf0))
  letI : Algebra.IsStandardSmooth k B := hsm
  obtain ⟨n, c, P, hP⟩ := (AdvCommAlg.Smooth.standard_smooth_iff k B).mp hsm
  obtain ⟨Q, hQ⟩ := (AdvCommAlg.Smooth.presentation_standard_smooth_iff_submersive P).mp hP
  have hr : ringKrullDim B = ((n - c : ℕ) : WithBot ℕ∞) := by
    apply AdvCommAlg.Smooth.ringKrullDim_eq_of_maximal_localizations
    intro m hm
    exact (AdvCommAlg.Smooth.standard_smooth_closed_point_regularity P hP m hm).2
  have hΩ : Module.finrank B (KaehlerDifferential k B) = n - c := by
    have hdim := Q.rank_kaehlerDifferential
    change _ = (Q.toPresentation.dimension : Cardinal) at hdim
    rw [hQ] at hdim
    simp only [Module.finrank, hdim, Algebra.Presentation.dimension, Nat.card_fin, Cardinal.toNat_natCast]
  rw [← krull_dimension_localization_away (k := k) hf0, hr,
    cotangent_fiber_localization_dimension x hf, hΩ]

private theorem group_dimension_eq_lie_finrank {A : HopfAlgebraCategory k}
    [IsDomain A] [Algebra.Smooth k A] {G : GroupScheme k}
    (i : hopfSpectrum A ≅ G) (s : IdentityLieStructure G) :
    letI := s.lieRing
    letI := s.lieAlgebra
    topologicalKrullDim G.X.left = (Module.finrank k (Lie k G) : WithBot ℕ∞) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨e, _, hs⟩ := liePresentation k A G i
  let L : PointTangent (counitAlgHom k A) ≃ₗ[k] Lie k G :=
    { e.toEquiv with
      map_add' := fun v w => (e.map_add v w).trans
        (congrFun (congrFun (congrArg (fun a : AddGroup (Lie k G) => a.toAdd.add) s.group_law)
          (e v)) (e w)).symm
      map_smul' := fun a v => (hs a v).trans (congrFun (congrFun s.scalar_law a) (e v)).symm }
  let j := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso i
  have h := IsHomeomorph.topologicalKrullDim_eq _ j.hom.homeomorph.isHomeomorph
  change topologicalKrullDim (PrimeSpectrum A) = topologicalKrullDim G.X.left at h
  rw [← h, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    smooth_affine_domain_dimension_at_point (counitAlgHom k A), L.finrank_eq]

private theorem smooth_coordinate_hopf {A : HopfAlgebraCategory k} {G : GroupScheme k}
    (i : hopfSpectrum A ≅ G) (h : Smooth G.X.hom) : Algebra.Smooth k A := by
  let j := (Grp.forget (SchemeOver k)).mapIso i
  haveI : IsIso j.hom.left := (Over.forget _).map_isIso j.hom
  letI := h
  have hsm : Smooth (j.hom.left ≫ G.X.hom) := inferInstance
  have hw : j.hom.left ≫ G.X.hom = (hopfSpectrum A).X.hom := Over.w j.hom
  rw [hw] at hsm
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hsm
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)

private theorem reductive_dimension_eq_lie_finrank (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    topologicalKrullDim G.val.X.left = (Module.finrank k (Lie k G.val) : WithBot ℕ∞) := by
  let C : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let A := coordinateHopf C
  let i : hopfSpectrum A ≅ G.val := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso C)
  letI : GeometricallyConnected G.val.X.hom := hG.2.1
  letI := G.property.2.1
  letI := G.property.2.2
  letI : IrreducibleSpace G.val.X.left := irreducible_of_geometricallyConnected G.val
  letI := hG.1
  letI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  letI : IsIntegral G.val.X.left := isIntegral_of_irreducibleSpace_of_isReduced _
  let j := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso i
  letI : IsIntegral ((Grp.forget (SchemeOver k) ⋙ Over.forget _).obj G.val) :=
    inferInstanceAs (IsIntegral G.val.X.left)
  letI : IsDomain A := (affine_isIntegral_iff (.of A)).mp (IsIntegral.of_isIso j.inv)
  letI : Algebra.Smooth k A := smooth_coordinate_hopf i hG.1
  exact group_dimension_eq_lie_finrank i s

private theorem split_torus_dimension_eq_lie_finrank {T : GroupScheme k}
    (hT : IsSplitTorus T) (s : IdentityLieStructure T) :
    letI := s.lieRing
    letI := s.lieAlgebra
    topologicalKrullDim T.X.left = (Module.finrank k (Lie k T) : WithBot ℕ∞) := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let A := Specs.DiagonalizableGroups.groupAlgebra k (Specs.CharacterDescent.StandardLattice.{u} r)
  letI : IsDomain A := standardLatticeDomain r
  letI : Algebra.Smooth k A := smooth_coordinate_hopf (Iso.refl _) (smoothStandardLattice r)
  exact group_dimension_eq_lie_finrank i s

private theorem finrank_of_internal_character_weights {V X : Type u} [AddCommGroup V]
    [Module k V] [Module.Finite k V] [One X] [DecidableEq X]
    (Φ : Set X) (W : X → Submodule k V) (hW : DirectSum.IsInternal W)
    (hΦ : Φ.Finite) (hmem : ∀ χ, χ ∈ Φ ↔ χ ≠ 1 ∧ W χ ≠ ⊥)
    (hdim : ∀ χ ∈ Φ, Module.finrank k (W χ) = 1) :
    Module.finrank k V = Module.finrank k (W 1) + Φ.ncard := by
  classical
  letI : Fintype ↥Φ := hΦ.fintype
  let I := Option ↥Φ
  let c : I → X := fun j => j.elim 1 Subtype.val
  have hc : Function.Injective c := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some β => exact False.elim (((hmem β.val).mp β.property).1 h.symm)
    | some α =>
      cases b with
      | none => exact False.elim (((hmem α.val).mp α.property).1 h)
      | some β => exact congrArg some (Subtype.ext h)
  have hi : DirectSum.IsInternal (fun j : I => W (c j)) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact hW.submodule_iSupIndep.comp hc
    · apply top_unique
      rw [← hW.submodule_iSup_eq_top]
      apply iSup_le
      intro χ
      by_cases hχ : χ = 1
      · subst χ
        exact le_iSup (fun j : I => W (c j)) none
      by_cases h : W χ = ⊥
      · rw [h]
        exact bot_le
      · exact le_iSup (fun j : I => W (c j)) (some ⟨χ, (hmem χ).mpr ⟨hχ, h⟩⟩)
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun j : I => W (c j))) hi
  calc
    Module.finrank k V = Module.finrank k (⨁ j : I, W (c j)) := e.symm.finrank_eq
    _ = ∑ j : I, Module.finrank k (W (c j)) :=
      Module.finrank_directSum k (fun j : I => ↥(W (c j)))
    _ = _ := by
      rw [Fintype.sum_option]
      change Module.finrank k (W 1) + (∑ j : ↥Φ, Module.finrank k (W j.val)) =
        Module.finrank k (W 1) + Φ.ncard
      have h (j : ↥Φ) := hdim j.val j.property
      simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Nat.cast_id]

private theorem zero_weight_finrank (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (s : IdentityLieStructure G.val)
    (sT : IdentityLieStructure T.group) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := sT.lieRing
    letI := sT.lieAlgebra
    Module.finrank k (adjointWeightSpace T 1 s) = Module.finrank k (Lie k T.group) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := sT.lieRing
  letI := sT.lieAlgebra
  letI := G.property.1
  letI : IsAffine T.group.X.left := (Unipotent.closedSubgroupAlgebraicGroup T).property.1
  letI : AddCommGroup (Lie k G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k G.val) := s.lieAlgebra.toModule
  letI : AddCommGroup (Lie k T.group) := sT.lieRing.toAddCommGroup
  letI : Module k (Lie k T.group) := sT.lieAlgebra.toModule
  obtain ⟨hi, hW⟩ := CharacterPairing.zeroWeightSpace G hG T hT hmax s
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k T.group G.val T.inclusion sT s
  let f := d.toLinearMap
  have hf : (f : Lie k T.group → Lie k G.val) = mapPointKernel T.inclusion := funext hd
  have he : adjointWeightSpace T 1 s = LinearMap.range f := by
    apply SetLike.coe_injective
    exact hW.trans (congrArg Set.range hf).symm
  have hinj : Function.Injective f := hf.symm ▸ hi
  rw [he]
  exact (LinearEquiv.ofInjective f hinj).symm.finrank_eq

/-- The dimension of the reductive group is the dimension of its split maximal
torus plus the number of roots. -/
theorem rootDimension_conditional
    (centralizer : CentralizerAndPositiveCocharacter.{u})
    (projective : ProjectiveLineAutomorphisms.{u})
    (geometry : RankOneFlagGeometry.{u}) : RootDimension.{u} := by
  classical
  intro k _ G hG T hT hmax
  let s := identityLieStructure G
  let sT := identityLieStructure (Unipotent.closedSubgroupAlgebraicGroup T)
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := sT.lieRing
  letI := sT.lieAlgebra
  obtain ⟨_, b, _, _, _, _, _, _, _⟩ := adjointRepresentation k G s
  letI : Module.Finite k (Lie k G.val) := Module.Finite.of_basis b
  have hΦ := CharacterPairing.finiteAbsoluteRoots G T hT
  refine ⟨hΦ, ?_⟩
  have hdim := finrank_of_internal_character_weights (absoluteRoots T)
    (fun χ => adjointWeightSpace T χ s) (adjointWeightsInternal G T hT s) hΦ
    (CharacterPairing.absoluteRootWeights T s)
    (fun α hα => rootSpaceDimension_conditional centralizer projective geometry G hG T hT hmax α hα s)
  rw [zero_weight_finrank G hG T hT hmax s sT] at hdim
  rw [reductive_dimension_eq_lie_finrank G hG s, split_torus_dimension_eq_lie_finrank hT sT]
  exact_mod_cast hdim

end Dimension

end

end LinearAlgebraicGroups.RootData.RootGroups

universe v8_closure_c5bda8bcb1d4ba68_u0
theorem _root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups» : _root_.«LinearAlgebraicGroups».«Specs».«RootGroups».«RankOneRootGroups».{v8_closure_c5bda8bcb1d4ba68_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups_conditional».{v8_closure_c5bda8bcb1d4ba68_u0} (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«centralizerAndPositiveCocharacter».{v8_closure_c5bda8bcb1d4ba68_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«projectiveLineAutomorphisms».{v8_closure_c5bda8bcb1d4ba68_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«rankOneFlagGeometry».{v8_closure_c5bda8bcb1d4ba68_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension» : _root_.«LinearAlgebraicGroups».«Specs».«RootGroups».«RootDimension».{v8_closure_c5bda8bcb1d4ba68_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension_conditional».{v8_closure_c5bda8bcb1d4ba68_u0} (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«centralizerAndPositiveCocharacter».{v8_closure_c5bda8bcb1d4ba68_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«projectiveLineAutomorphisms».{v8_closure_c5bda8bcb1d4ba68_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«rankOneFlagGeometry».{v8_closure_c5bda8bcb1d4ba68_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups» : _root_.«LinearAlgebraicGroups».«Specs».«RootGroups».«RootSubgroups».{v8_closure_c5bda8bcb1d4ba68_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups_conditional».{v8_closure_c5bda8bcb1d4ba68_u0} (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«centralizerAndPositiveCocharacter».{v8_closure_c5bda8bcb1d4ba68_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«projectiveLineAutomorphisms».{v8_closure_c5bda8bcb1d4ba68_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«rankOneFlagGeometry».{v8_closure_c5bda8bcb1d4ba68_u0})
