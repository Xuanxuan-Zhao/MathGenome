import Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianFixedRootSL2
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
import LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
import LinearAlgebraicGroups.Relative.MaximalSplitTori
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianFixedRootSL2

open _root_.LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open AdjointRepresentation (GroupPoints)
open Arithmetic.TrialitarianFixedRootSL2 (RankOne)
open CharacterDescent (Cocharacter)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open GeometricRadicals (baseChangedSubgroup)
open OrderedRootProducts (RootSubgroupFamily)
open Pinning (SimpleRoot)
open QuasiSplitOrbitDerivedRoots (diagramRoot pinnedRootMap)
open Specs.QuasiSplitOrbitLevis
open Specs.QuasiSplitOrbitPinnedModels (MatrixMark specialLinearPointsOfSize)
open RootGroups (AdditiveLine rootPoint)
open Unipotent (Index)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)
open Matrix

open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private rationalOppositePair from LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
open private sameSubgroupIso from LinearAlgebraicGroups.Classification.CentralIsogenies
open private faceRadicals_nonempty markedFace from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private reindexSpecialLinear from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem singletonOrbitField [FiniteDimensional F K] [IsGalois F K]
    {J : Type u} [Subsingleton J] (ρ : Gal(K/F) →* Equiv.Perm J) (i : J) :
    Specs.QuasiSplitOrbitPinnedModels.orbitField ρ i = ⊥ := by
  letI := MulAction.compHom J ρ
  have h : MulAction.stabilizer Gal(K/F) i = ⊤ := by
    ext σ
    exact iff_of_true (Subsingleton.elim (σ • i) i) (Subgroup.mem_top σ)
  change IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i) = _
  rw [h, IsGalois.fixedField_top]

private abbrev tensorGroundEquiv {E : Type u} [Field E] [Algebra F E]
    (R : TestAlgebra F) (e : E ≃ₐ[F] F) : R ⊗[F] E ≃ₐ[F] R :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[F] R) e).trans
    (Algebra.TensorProduct.rid F F R)

private def matrixScalarIso {E : Type u} [Field E] [Algebra F E] (e : E ≃ₐ[F] F) :
    extendScalars F E ⋙ specialLinearPointsOfSize 2 E ≅ specialLinearPointsOfSize 2 F :=
  NatIso.ofComponents (fun R =>
    let s := tensorGroundEquiv R e
    (show SpecialLinearGroup (Fin 2) (R ⊗[F] E) ≃* SpecialLinearGroup (Fin 2) R from
      { toFun := SpecialLinearGroup.map s.toRingHom
        invFun := SpecialLinearGroup.map s.symm.toRingHom
        left_inv := fun g => Subtype.ext (Matrix.ext fun i j => s.symm_apply_apply (g.val i j))
        right_inv := fun g => Subtype.ext (Matrix.ext fun i j => s.apply_symm_apply (g.val i j))
        map_mul' := map_mul (SpecialLinearGroup.map s.toRingHom) }).toGrpIso) (by
    intro R S f
    have h : (tensorGroundEquiv S e).toAlgHom.comp
        (Algebra.TensorProduct.map f.hom (AlgHom.id F E)) =
        f.hom.comp (tensorGroundEquiv R e).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro r x
      change e x • f.hom r = f.hom (e x • r)
      simp only [Algebra.smul_def, map_mul, AlgHom.commutes]
    apply GrpCat.ext
    intro g
    apply Subtype.ext
    exact Matrix.ext fun i j => DFunLike.congr_fun h (g.val i j))

private def matrixIndexIso (F : Type u) [Field F] :
    specialLinearPointsOfSize 2 F ≅ StandardGroups.specialLinearPoints F (Index.{u} 2) :=
  NatIso.ofComponents (fun R =>
    (reindexSpecialLinear (R := R) (Equiv.ulift.symm : Fin 2 ≃ Index.{u} 2)).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro g
    apply Subtype.ext
    rfl)

open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open CocharacterDynamics (factorsThroughClosed_iff mapPoints_unitPoint)
open private factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private additiveLinePointsIso rootPoint_comp rootPoint_eq hom_ext_on_affine_tests
  from LinearAlgebraicGroups.RootData.RootGroups
open private additiveIso_linear from LinearAlgebraicGroups.Classification.Pinning
open private unitEquiv unitPointHom_apply unitEquiv_unitPoint
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private mark_map_iff rankOneCoroot from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels

private theorem liftToSubgroup {X Y : GroupScheme F} (V : ClosedSubgroup Y)
    (g : X ⟶ Y)
    (hg : ∀ (R : TestAlgebra F) (x : GroupPoints X R),
      x ≫ g.hom.hom ∈ SubgroupSections V _) :
    ∃ f : X ⟶ V.group, f ≫ V.inclusion = g := by
  obtain ⟨f, hf⟩ := (factorsThroughClosed_iff V.inclusion.hom.hom V.isClosedImmersion
    g.hom.hom).mpr hg
  exact factor_group_through_subgroup V g f hf

private theorem liftPointCoordinates {X Y : GroupScheme F} (hX : IsAffine X.X.left)
    (V : ClosedSubgroup Y)
    (n₀ : (groupPointsFunctor F).obj X ⟶ (groupPointsFunctor F).obj Y)
    (hη : ∀ (R : TestAlgebra F) (x : GroupPoints X R), n₀.app R x ∈ SubgroupSections V _) :
    ∃ f : X ⟶ V.group, (groupPointsFunctor F).map (f ≫ V.inclusion) = n₀ := by
  obtain ⟨g, hg⟩ := (groupHomComparison F X Y hX).2 n₀
  obtain ⟨f, hf⟩ := liftToSubgroup V g (fun R x => by
    rw [← hg] at hη
    exact hη R x)
  exact ⟨f, hf ▸ hg⟩

private theorem closedSubgroupPointInclusion {Y : GroupScheme F} (V : ClosedSubgroup Y)
    (R : TestAlgebra F) :
    Function.Injective (fun x : GroupPoints V.group R => x ≫ V.inclusion.hom.hom) := by
  letI := mono_over _ V.isClosedImmersion
  intro x y h
  exact (cancel_mono V.inclusion.hom.hom).mp h

private theorem liftPointCoordinatesIso {X : GroupScheme F} (hX : IsAffine X.X.left)
    (Y : AffineAlgebraicGroup F) (V : ClosedSubgroup Y.val)
    (n₀ : (groupPointsFunctor F).obj X ⟶ (groupPointsFunctor F).obj Y.val)
    (hinj : ∀ R, Function.Injective (n₀.app R))
    (hη : ∀ (R : TestAlgebra F) (x : GroupPoints Y.val R),
      x ∈ SubgroupSections V _ ↔ ∃ z, n₀.app R z = x) :
    ∃ f : X ≅ V.group, (groupPointsFunctor F).map (f.hom ≫ V.inclusion) = n₀ := by
  obtain ⟨f, hf⟩ := liftPointCoordinates hX V n₀ (fun R x => (hη R _).mpr ⟨x, rfl⟩)
  have hf_app (R : TestAlgebra F) (x : GroupPoints X R) :
      (x ≫ f.hom.hom) ≫ V.inclusion.hom.hom = n₀.app R x := by
    have h := congrArg (fun a => a.app R x) hf
    change x ≫ (f ≫ V.inclusion).hom.hom = n₀.app R x at h
    simpa only [Grp.comp_hom_hom, Category.assoc] using h
  have happ (R : TestAlgebra F) :
      Function.Bijective (((groupPointsFunctor F).map f).app R) := by
    constructor
    · intro x y h
      apply hinj R
      rw [← hf_app, ← hf_app]
      exact congrArg (· ≫ V.inclusion.hom.hom) h
    · intro x
      obtain ⟨z, hz⟩ := (hη R _).mp ⟨x, rfl⟩
      exact ⟨z, closedSubgroupPointInclusion V R ((hf_app R z).trans hz)⟩
  let n := (groupPointsFunctor F).map f
  haveI (R : TestAlgebra F) : IsIso (n.app R) :=
    (MulEquiv.ofBijective (n.app R).hom (happ R)).toGrpIso.isIso_hom
  letI : IsIso n := NatIso.isIso_of_isIso_app n
  let hV := (closedSubgroupAlgebraicGroup V).property.1
  obtain ⟨g, hg⟩ := (groupHomComparison F V.group X hV).2 (inv n)
  have hfg : f ≫ g = 𝟙 _ := (groupHomComparison F X X hX).1 (by
    simp only [Functor.map_comp, hg, show (groupPointsFunctor F).map f = n from rfl,
    IsIso.hom_inv_id]
    exact ((groupPointsFunctor F).map_id X).symm)
  have hgf : g ≫ f = 𝟙 _ := (groupHomComparison F V.group V.group hV).1 (by
    simp only [Functor.map_comp, hg, show (groupPointsFunctor F).map f = n from rfl,
    IsIso.inv_hom_id]
    exact ((groupPointsFunctor F).map_id V.group).symm)
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

private def transvectionPoints (i j : Fin 2) (hij : i ≠ j) :
    StandardGroups.additivePoints F ⟶ specialLinearPointsOfSize 2 F where
  app R := GrpCat.ofHom
    (show Multiplicative R →* SpecialLinearGroup (Fin 2) R from
      { toFun := fun x => SpecialLinearGroup.transvection hij (Multiplicative.toAdd x : R)
        map_one' := SpecialLinearGroup.transvection_coeff_zero hij
        map_mul' := fun x y => SpecialLinearGroup.transvection_add hij (x.toAdd : R) y.toAdd })
  naturality R S f := by
    apply GrpCat.ext
    intro x
    change Multiplicative R at x
    apply Subtype.ext
    change 1 + Matrix.single i j (f.hom x.toAdd) =
      (1 + Matrix.single i j x.toAdd : Matrix (Fin 2) (Fin 2) R).map f.hom
    ext l r
    by_cases hl : i = l <;> by_cases hr : j = r <;>
      simp [Matrix.one_apply, hl, hr]

private theorem transvectionInjective {R : Type u} [CommRing R]
    (i j : Fin 2) (hij : i ≠ j) :
    Function.Injective (SpecialLinearGroup.transvection hij :
      R → SpecialLinearGroup (Fin 2) R) := by
  intro x y h
  have hh := congrArg (fun g : SpecialLinearGroup (Fin 2) R => g.val i j) h
  simpa only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne hij,
    zero_add, Matrix.single_apply_same] using hh

private theorem upperMark_iff {R : Type u} [CommRing R]
    (g : SpecialLinearGroup (Fin 2) R) :
    MatrixMark.positiveRadical.Holds g ↔
      ∃ x : R, SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) x = g := by
  constructor
  · rintro ⟨h, hd⟩
    have h10 : g.val 1 0 = 0 := h (show (0 : Fin 2) < 1 by decide)
    refine ⟨g.val 0 1, Subtype.ext ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe, hd, h10]
  · rintro ⟨x, rfl⟩
    constructor
    · intro i j hij
      change j < i at hij
      fin_cases i <;> fin_cases j <;>
        simp_all [SpecialLinearGroup.transvection_coe]
    · intro i
      fin_cases i <;> simp [SpecialLinearGroup.transvection_coe]

private theorem lowerMark_iff {R : Type u} [CommRing R]
    (g : SpecialLinearGroup (Fin 2) R) :
    MatrixMark.negativeRadical.Holds g ↔
      ∃ x : R, SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) x = g := by
  constructor
  · rintro ⟨h, hd⟩
    have h01 : g.val 0 1 = 0 := h (show (0 : Fin 2) < 1 by decide)
    refine ⟨g.val 1 0, Subtype.ext ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe, hd, h01]
  · rintro ⟨x, rfl⟩
    constructor
    · intro i j hij
      change i < j at hij
      fin_cases i <;> fin_cases j <;>
        simp_all [SpecialLinearGroup.transvection_coe]
    · intro i
      fin_cases i <;> simp [SpecialLinearGroup.transvection_coe]

private theorem additiveMarkIso (A : AdditiveLine F) (Y : AffineAlgebraicGroup F)
    (V : ClosedSubgroup Y.val)
    (m : (groupPointsFunctor F).obj Y.val ≅ specialLinearPointsOfSize 2 F)
    (i j : Fin 2) (hij : i ≠ j)
    (h : ∀ (R : TestAlgebra F) (z : GroupPoints Y.val R), z ∈ SubgroupSections V _ ↔
      ∃ x : R, SpecialLinearGroup.transvection hij x = m.hom.app R z) :
    ∃ e : A.group ≅ V.group, ∀ (R : TestAlgebra F) (x : R),
      m.hom.app R (rootPoint (e.hom ≫ V.inclusion) R x) =
        SpecialLinearGroup.transvection hij x := by
  let n := (additiveLinePointsIso A).inv ≫ transvectionPoints i j hij ≫ m.inv
  have hA : IsAffine A.group.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial F))))
  have h_app (R : TestAlgebra F) (z : GroupPoints A.group R) :
      m.hom.app R (n.app R z) =
        SpecialLinearGroup.transvection hij ((additivePoints A R).symm z) := by
    exact GrpCat.hom_inv_apply (m.app R) _
  obtain ⟨e, he⟩ := liftPointCoordinatesIso hA Y V n (fun R x y hh => by
    apply (additivePoints A R).symm.injective
    apply transvectionInjective i j hij
    exact (h_app R x).symm.trans ((congrArg (m.hom.app R) hh).trans (h_app R y)))
    (fun R z => by
      rw [h]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨additivePoints A R x, ?_⟩
        apply ((m.app R).groupIsoToMulEquiv).injective
        exact (h_app R _).trans (congrArg _ ((additivePoints A R).symm_apply_apply x) |>.trans hx)
      · rintro ⟨x, rfl⟩
        exact ⟨_, (h_app R x).symm⟩)
  refine ⟨e, fun R x => ?_⟩
  have hx := congrArg (fun v => m.hom.app R (v.app R (additivePoints A R x))) he
  change m.hom.app R (rootPoint (e.hom ≫ V.inclusion) R x) =
    m.hom.app R (n.app R (additivePoints A R x)) at hx
  exact hx.trans ((h_app R _).trans (congrArg _ ((additivePoints A R).symm_apply_apply x)))

private def diagonalPoints (F : Type u) [Field F] :
    (groupPointsFunctor F).obj (Specs.Arithmetic.QuasiSplitFixedWeyl.multiplicativeGroup F) ⟶
      specialLinearPointsOfSize 2 F where
  app R := GrpCat.ofHom ((show Rˣ →* SpecialLinearGroup (Fin 2) R from
    { toFun := rankOneCoroot
      map_one' := Subtype.ext (by
        change Matrix.diagonal ![(↑(1 : Rˣ) : R), (↑(1 : Rˣ)⁻¹ : R)] = 1
        rw [← Matrix.diagonal_one]
        congr 1
        funext i
        fin_cases i <;> simp)
      map_mul' := fun v w => Subtype.ext (by
        change (rankOneCoroot (v * w)).val =
          (rankOneCoroot v).val * (rankOneCoroot w).val
        change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        fin_cases i <;> simp [mul_comm]) }).comp (unitEquiv R).toMonoidHom)
  naturality R S f := by
    apply GrpCat.ext
    intro x
    obtain ⟨v, rfl⟩ := (unitEquiv R).symm.surjective x
    rw [show (unitEquiv R).symm v = unitPoint R v from unitPointHom_apply R v]
    change rankOneCoroot (unitEquiv S (mapPoints f (unitPoint R v))) =
      SpecialLinearGroup.map f.hom.toRingHom (rankOneCoroot (unitEquiv R (unitPoint R v)))
    rw [mapPoints_unitPoint, unitEquiv_unitPoint, unitEquiv_unitPoint]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rankOneCoroot]

private theorem diagonalMark (Y : AffineAlgebraicGroup F)
    (T : ClosedSubgroup Y.val)
    (m : (groupPointsFunctor F).obj Y.val ≅ specialLinearPointsOfSize 2 F)
    (h : ∀ (R : TestAlgebra F) (z : GroupPoints Y.val R),
      MatrixMark.torus.Holds (m.hom.app R z) ↔ z ∈ SubgroupSections T _) :
    ∃ c : Cocharacter T.group, ∀ (R : TestAlgebra F) (v : Rˣ),
      m.hom.app R (cocharacterPoint (c ≫ T.inclusion) R v) = rankOneCoroot v := by
  let n := diagonalPoints F ≫ m.inv
  let C := Specs.Arithmetic.QuasiSplitFixedWeyl.multiplicativeGroup F
  have hC : IsAffine C.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of
    (MonoidAlgebra F DiagonalizableGroups.IntegerCharacters.{u}))))
  have hdiag (R : TestAlgebra F) (x : GroupPoints C R) :
      m.hom.app R (n.app R x) = rankOneCoroot (unitEquiv R x) :=
    GrpCat.hom_inv_apply (m.app R) _
  obtain ⟨c, hc⟩ := liftPointCoordinates hC T n (fun R x => (h R _).mp (by
    rw [hdiag]
    intro i j hij
    exact Matrix.diagonal_apply_ne _ hij))
  refine ⟨c, fun R v => ?_⟩
  have hx := congrArg (fun a => m.hom.app R (a.app R (unitPoint R v))) hc
  change m.hom.app R (cocharacterPoint (c ≫ T.inclusion) R v) =
    m.hom.app R (n.app R (unitPoint R v)) at hx
  rw [hx, hdiag, unitEquiv_unitPoint]

private theorem scalarLift_eq {E : Type u} [Field E] [Algebra F E]
    (R : TestAlgebra F) (e : E ≃ₐ[F] F) (a : E →ₐ[F] R) :
    Algebra.TensorProduct.lift (AlgHom.id F R) a (fun _ _ => Commute.all _ _) =
      (tensorGroundEquiv R e).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro r y
  obtain ⟨z, rfl⟩ := e.symm.surjective y
  have he : e.symm z = algebraMap F E z := by
    exact e.symm.commutes z
  rw [he]
  change r * a (algebraMap F E z) = e (algebraMap F E z) • r
  rw [a.commutes, show e (algebraMap F E z) = z from e.commutes z, Algebra.smul_def, mul_comm]

private def scaleDiagonal {R : Type u} [CommRing R] (v : Rˣ) :
    Matrix (Fin 2) (Fin 2) R :=
  Matrix.diagonal (fun i => if i = 0 then (v : R) else 1)

private theorem scaleDiagonal_mul_inv {R : Type u} [CommRing R] (v : Rˣ) :
    scaleDiagonal v * scaleDiagonal v⁻¹ = 1 := by
  rw [scaleDiagonal, scaleDiagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [hi]

private def scaleDiagonalUnit {R : Type u} [CommRing R] (v : Rˣ) :
    (Matrix (Fin 2) (Fin 2) R)ˣ :=
  ⟨scaleDiagonal v, scaleDiagonal v⁻¹, scaleDiagonal_mul_inv v,
    by simpa only [inv_inv] using scaleDiagonal_mul_inv v⁻¹⟩

private def conjugateMatrixGroup {R : Type u} [CommRing R]
    (v : (Matrix (Fin 2) (Fin 2) R)ˣ) : SpecialLinearGroup (Fin 2) R ≃* SpecialLinearGroup (Fin 2) R := by
  let conjugate (u : (Matrix (Fin 2) (Fin 2) R)ˣ) (g : SpecialLinearGroup (Fin 2) R) :
      SpecialLinearGroup (Fin 2) R :=
    ⟨u.val * g.val * (u⁻¹).val, by
      rw [Matrix.det_mul, Matrix.det_mul, g.property, mul_one, ← Matrix.det_mul]
      simp⟩
  have cancel (u : (Matrix (Fin 2) (Fin 2) R)ˣ) (g : SpecialLinearGroup (Fin 2) R) :
      conjugate u⁻¹ (conjugate u g) = g := by
    apply Subtype.ext
    change (u⁻¹).val * (u.val * g.val * (u⁻¹).val) * ((u⁻¹)⁻¹).val = g.val
    calc
      _ = ((u⁻¹).val * u.val) * g.val * ((u⁻¹).val * u.val) := by
        simp only [inv_inv, mul_assoc]
      _ = _ := by simp
  refine ⟨⟨conjugate v, conjugate v⁻¹, cancel v, fun g => ?_⟩, ?_⟩
  · simpa only [inv_inv] using cancel v⁻¹ g
  · intro g h
    apply Subtype.ext
    change v.val * (g.val * h.val) * (v⁻¹).val =
      (v.val * g.val * (v⁻¹).val) * (v.val * h.val * (v⁻¹).val)
    symm
    calc
      _ = (v.val * g.val) * ((v⁻¹).val * v.val) * (h.val * (v⁻¹).val) := by
        simp only [mul_assoc]
      _ = _ := by simp [mul_assoc]

private abbrev scaleMatrixGroup {R : Type u} [CommRing R] (v : Rˣ) :=
  conjugateMatrixGroup (scaleDiagonalUnit v)

private theorem scaleMatrixEntry {R : Type u} [CommRing R] (v : Rˣ)
    (g : SpecialLinearGroup (Fin 2) R) (i j : Fin 2) :
    (scaleMatrixGroup v g).val i j =
      (if i = 0 then (v : R) else 1) * g.val i j * (if j = 0 then (↑v⁻¹ : R) else 1) := by
  change (scaleDiagonal v * g.val * scaleDiagonal v⁻¹) i j = _
  simp only [scaleDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]

private def scaleMatrixIso (v : Fˣ) :
    specialLinearPointsOfSize 2 F ≅ specialLinearPointsOfSize 2 F :=
  NatIso.ofComponents (fun R =>
    (scaleMatrixGroup (Units.map (algebraMap F R : F →* R) v)).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro g
    apply Subtype.ext
    ext i j
    change (scaleMatrixGroup (Units.map (algebraMap F S : F →* S) v)
      (SpecialLinearGroup.map f.hom.toRingHom g)).val i j =
      f.hom ((scaleMatrixGroup (Units.map (algebraMap F R : F →* R) v) g).val i j)
    rw [scaleMatrixEntry, scaleMatrixEntry]
    change _ * f.hom (g.val i j) * _ = _
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp [hi, hj, ← map_inv, AlgHom.commutes])

private theorem scaleMatrixDiagonal {R : Type u} [CommRing R] (v w : Rˣ) :
    scaleMatrixGroup v (rankOneCoroot w) = rankOneCoroot w := by
  apply Subtype.ext
  ext i j
  rw [scaleMatrixEntry]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0
    · rw [ite_eq_left hi, ite_eq_left hi, mul_right_comm, Units.mul_inv, one_mul]
    · simp only [hi, ite_false, one_mul, mul_one]
  · rw [show (rankOneCoroot w).val i j = 0 from Matrix.diagonal_apply_ne _ hij, mul_zero, zero_mul]

private theorem scaleMatrixUpper {R : Type u} [CommRing R] (v : Rˣ) (x : R) :
    scaleMatrixGroup v (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) x) =
      SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) ((v : R) * x) := by
  apply Subtype.ext
  ext i j
  rw [scaleMatrixEntry]
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe]

private theorem scaleMatrixLower {R : Type u} [CommRing R] (v : Rˣ) (x : R) :
    scaleMatrixGroup v (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) x) =
      SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) ((↑v⁻¹ : R) * x) := by
  apply Subtype.ext
  ext i j
  rw [scaleMatrixEntry]
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, mul_comm]

open private orbitTrivialization_eq faceOpposite faceModelAction_character faceModelAction_transitive
  faceCoroot faceCoroot_ambient faceCoroot_coordinates
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private cocharacterFactorsThroughMaximalSplit from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private scaleIso scaleIso_point from LinearAlgebraicGroups.Classification.Pinning

private theorem reindexTransvection {R : Type u} [CommRing R] (i j : Fin 2) (hij : i ≠ j) (x : R) :
    reindexSpecialLinear (Equiv.ulift.symm : Fin 2 ≃ Index.{u} 2)
      (SpecialLinearGroup.transvection hij x) =
    SpecialLinearGroup.transvection (i := (⟨i⟩ : Index.{u} 2)) (j := ⟨j⟩)
      (fun h => hij (congrArg ULift.down h)) x := by
  apply Subtype.ext
  ext ⟨l⟩ ⟨r⟩
  change (1 + Matrix.single i j x : Matrix (Fin 2) (Fin 2) R) l r =
    (1 + Matrix.single ⟨i⟩ ⟨j⟩ x : Matrix (Index.{u} 2) (Index.{u} 2) R) ⟨l⟩ ⟨r⟩
  simp [Matrix.one_apply, Matrix.single_apply]

open Specs.Pinning (SplitBorelPair AttachedDatum)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.QuasiSplitOrbitAmbientWords (BorelRadical SplitRadical)
open Specs.StandardParabolicLevi (leviRoots)
open Specs.RankOneFlag (SameSubgroup)
open private extendBorelRadical rootSubgroupIso from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private radicalProduct from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords
open private pushSubgroup radical_transport from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private oppositeRoot oppositeRoot_character oppositeRoot_mem_face attachedBase_regular
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots

private theorem singletonFaceRoots {P : SplitBorelPair K} (D : AttachedDatum P) (r : Root P.T) :
    letI := D.comm
    ∀ z ∈ leviRoots D.datum {r}, z = r ∨ z = oppositeRoot D r := by
  letI := D.comm
  intro z hz
  change D.datum.rootDatum.root z ∈ Submodule.span ℤ (D.datum.rootDatum.root '' {r}) at hz
  rw [Set.image_singleton, Submodule.mem_span_singleton] at hz
  obtain ⟨n, hn⟩ := hz
  have hh : r.val ^ n = z.val := by
    rw [D.datum.root_eq, D.datum.root_eq] at hn
    exact congrArg Additive.toMul hn
  have hn0 : n ≠ 0 := fun h => z.property.1 (by simpa only [h, zpow_zero] using hh.symm)
  have hp : Specs.RootGroups.Proportional r.val z.val :=
    ⟨n, 1, hn0, one_ne_zero, hh.trans (zpow_one z.val).symm⟩
  have h := (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups P.G P.reductive
    P.T P.split P.maximal).2 r.val r.property
  rcases (h.2.1 z.val).mp ⟨z.property, hp⟩ with e | e
  · exact Or.inl (Subtype.ext e)
  · exact Or.inr (Subtype.ext (e.trans (oppositeRoot_character D r).symm))

private theorem singletonBorelRoots {P : SplitBorelPair K} (D : AttachedDatum P)
    (r : Root P.T) (hr : letI := D.comm; r ∈ D.base.support)
    (hcases : ∀ z : Root P.T, z = r ∨ z.val = r.val⁻¹) :
    subgroupRoots P.T P.B = {r} := by
  letI := D.comm
  obtain ⟨c, _, hc, hb⟩ := attachedBase_regular D
  let φ := Specs.SimpleRoots.evaluate D.datum c
  have hval (z : Root P.T) : φ (D.datum.rootDatum.root z) =
      Specs.CharacterPairing.pairing P.T.group z.val c := by
    change D.datum.rootDatum.toLinearMap _ (Additive.ofMul c) = _
    rw [D.datum.root_eq, D.datum.pairing_eq]
  have hpositive (z : Root P.T) : z ∈ subgroupRoots P.T P.B ↔
      0 < φ (D.datum.rootDatum.root z) := by
    rw [← hc, hval]
    rfl
  have hr' : 0 < φ (D.datum.rootDatum.root r) :=
    (hb.positive_iff r).mp (D.base.isPos_of_mem_support hr)
  ext z
  constructor
  · intro hz
    rcases hcases z with rfl | hz'
    · rfl
    · have he : D.datum.rootDatum.root z = -D.datum.rootDatum.root r := by
        rw [D.datum.root_eq, D.datum.root_eq, hz']
        rfl
      have hn := (hpositive z).mp hz
      rw [he, map_neg] at hn
      omega
  · intro hz
    have hz' : z = r := hz
    exact (hpositive z).mpr (hz'.symm ▸ hr')

private theorem sameSubgroup_of_iso {Y : GroupScheme K} {J L : ClosedSubgroup Y}
    (e : J.group ≅ L.group) (he : e.hom ≫ L.inclusion = J.inclusion) : SameSubgroup J L :=
  ⟨⟨e.hom, he⟩, ⟨e.inv, by rw [← he, Iso.inv_hom_id_assoc]⟩⟩

private theorem singletonRadicalIso {P : SplitBorelPair K}
    (B : BorelRadical P.G) (hB : B.borel = P.B)
    (U : RootSubgroupFamily P.T) (r : Root P.T)
    (hr : subgroupRoots P.T P.B = {r}) :
    ∃ j : (U r).val.group ≅ B.inAmbient.group, j.hom ≫ B.inAmbient.inclusion = (U r).val.inclusion := by
  have hTB : SchemeDerivedGroup.IsSubgroupOf P.T B.borel := hB.symm ▸ P.containsTorus
  have hEnum : Specs.OrderedRootProducts.Enumerates [r] (subgroupRoots P.T B.borel) := by
    rw [hB, hr]
    exact ⟨List.nodup_singleton _, fun _ => List.mem_singleton⟩
  obtain ⟨e, he⟩ := radicalProduct P.reductive P.split P.maximal B hTB U [r] hEnum
  let p : (U r).val.group.X ≅ B.inAmbient.group.X := (ρ_ _).symm ≪≫ e
  have hp : p.hom ≫ B.inAmbient.inclusion.hom.hom = (U r).val.inclusion.hom.hom := by
    change ((ρ_ _).inv ≫ e.hom) ≫ B.inAmbient.inclusion.hom.hom = _
    rw [Category.assoc, he]
    simp only [Specs.OrderedRootProducts.rootProduct, Specs.OrderedRootProducts.product,
      MonObj.comp_one, rightUnitor_inv_fst_assoc, mul_one]
  have hp' : p.inv ≫ (U r).val.inclusion.hom.hom = B.inAmbient.inclusion.hom.hom := by
    rw [← hp, Iso.inv_hom_id_assoc]
  exact sameSubgroupIso ⟨
    factor_group_through_subgroup B.inAmbient _ p.hom hp,
    factor_group_through_subgroup (U r).val _ p.inv hp'⟩

private theorem baseChangedRadicalIso {Y : AffineAlgebraicGroup F}
    (B : BorelRadical Y) (Bₖ : SplitRadical K B) (P : SplitBorelPair K)
    (e : (groupBaseChange F K).obj Y.val ≅ P.G.val)
    (b : (groupBaseChange F K).obj B.borel.group ≅ P.B.group)
    (hb : b.hom ≫ P.B.inclusion = (groupBaseChange F K).map B.borel.inclusion ≫ e.hom)
    (U : RootSubgroupFamily P.T) (r : Root P.T)
    (hr : subgroupRoots P.T P.B = {r}) :
    ∃ j : (groupBaseChange F K).obj B.radical.group ≅ (U r).val.group,
      j.hom ≫ (U r).val.inclusion =
        (groupBaseChange F K).map B.inAmbient.inclusion ≫ e.hom := by
  let W : BorelRadical P.G :=
    ⟨P.B, P.borel, pushSubgroup b Bₖ.radical,
      radical_transport
        (A := closedSubgroupAlgebraicGroup (G := Unipotent.baseChangedAlgebraicGroup K Y) Bₖ.borel)
        (B := closedSubgroupAlgebraicGroup (G := P.G) P.B) b Bₖ.radical Bₖ.isRadical⟩
  obtain ⟨j, hj⟩ := singletonRadicalIso W rfl U r hr
  refine ⟨j.symm, ?_⟩
  rw [← hj, Iso.symm_hom, Iso.inv_hom_id_assoc]
  change ((groupBaseChange F K).map B.radical.inclusion ≫ b.hom) ≫ P.B.inclusion = _
  rw [Category.assoc, hb, ← Category.assoc, ← Functor.map_comp]
  rfl

set_option maxHeartbeats 2200000 in
/-- The derived group of the singleton standard Levi, with its prescribed
absolute pin in the determinant-one matrix coordinates. -/
theorem fixedSimpleRootSL2 : Specs.Arithmetic.TrialitarianFixedRootSL2.Statement.{u} := by
  classical
  intro F K _ _ _ _ _ G hG hsc M S _ hS P D A₀ A U p a m ω hm ha hcoord α hα
  letI := D.comm
  have hred := reductive_of_semisimple G hG
  have hsplit : GeometricRadicals.IsSemisimple P.pair.G :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  have hlattice := QuasiSplitPinnedPairModel.corootLatticeAfterSplitting G hG hsc P.pair D
    ⟨Iso.refl _⟩
  have hsplitSC : SimplyConnectedLattice.GeometricallySimplyConnected P.pair.G :=
    (Classification.SimplyConnectedLattice.latticeCriterion P.pair.G hsplit P.pair.T P.split
      P.maximal D.datum).mpr hlattice
  obtain ⟨pair⟩ : Nonempty (RationalOppositePair M.torus M.positive M.negative) :=
    rationalOppositePair M
  let I : Set (Root P.pair.T) := {α.val}
  let i₀ : I := ⟨α.val, rfl⟩
  have hsimple : I ⊆ D.base.support := by
    intro i hi
    have hi' : i = α.val := hi
    rw [hi']
    exact (D.simple_iff _).mpr α.property
  have hstable (σ : Gal(K/F)) (i : Root P.pair.T) : diagramRoot ω σ i ∈ I ↔ i ∈ I := by
    change diagramRoot ω σ i = α.val ↔ i = α.val
    constructor
    · intro h
      exact (ω σ).asIso.hom.val.indexEquiv.injective (h.trans (hα σ).symm)
    · rintro rfl
      exact hα σ
  obtain ⟨L, hL⟩ := QuasiSplitOrbitLevis.rationalStandardFaceExists G M.torus M.positive
    P D m ω hred M.isTorus M.maximal hsplit hsplitSC hm ha.cocharacters I hsimple hstable
  have ha' : IsAmbientPinnedAction D p a L.scalar ω := hL.symm ▸ ha
  have hm' : PreservesUnits L.scalar := hL.symm ▸ hm
  obtain ⟨d⟩ := QuasiSplitOrbitLevis.rationalFacePinning D pair hred M.isTorus M.maximal U p a ω
    I L ha' hstable
  obtain ⟨q⟩ := QuasiSplitOrbitLevis.rationalFacePinnedForm d hm' hstable
  obtain ⟨V⟩ := faceRadicals_nonempty d
  haveI : Subsingleton I := ⟨fun i j => Subtype.ext ((show i.val = α.val from i.property).trans
    (show j.val = α.val from j.property).symm)⟩
  have htrans (i j : I) : ∃ σ, diagramRoot ω σ i.val = j.val := by
    refine ⟨1, ?_⟩
    rw [Subsingleton.elim i i₀, Subsingleton.elim j i₀]
    exact hα 1
  let H := markedFace q V htrans
  let j₀ := q.modelVertices i₀
  letI : Subsingleton (SimpleRoot H.P.pair) := q.modelVertices.symm.injective.subsingleton
  obtain ⟨W, f, mat, emb, t, splitMat, ht, hmark, hemb, hnat, hscalar, hcoords⟩ :=
    QuasiSplitOrbitPinnedModels.orthogonalPinnedOrbitModel H j₀
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
  -- The stabilizer of the only simple vertex is the full Galois group.
  let E := Specs.QuasiSplitOrbitPinnedModels.orbitField H.action j₀
  let e : E ≃ₐ[F] F := (IntermediateField.equivOfEq (singletonOrbitField H.action j₀)).trans
    (IntermediateField.botEquiv F K)
  let matF := (groupPointsFunctor F).mapIso f ≪≫ mat ≪≫ matrixScalarIso e
  let inclusion : H.G.val ⟶ G.val := L.derived.inclusion ≫ L.limit.centralizer.inclusion
  have hinclusion : IsClosedImmersion inclusion.hom.hom.left := by
    letI := L.derived.isClosedImmersion
    letI := L.limit.centralizer.isClosedImmersion
    exact IsClosedImmersion.comp L.derived.inclusion.hom.hom.left
      L.limit.centralizer.inclusion.hom.hom.left
  have hkernel : IsPullback (η[H.G.val.X]) (𝟙 _) inclusion.hom.hom (η[G.val.X]) := by
    letI := mono_over _ hinclusion
    apply IsPullback.of_vert_isIso_mono
    exact ⟨by rw [Category.id_comp, IsMonHom.one_hom]⟩
  obtain ⟨b, hb⟩ := QuasiSplitOrbitLevis.attachedCorootBasis P.pair D hsplit hsplitSC
  let i : D.base.support := ⟨α.val, hsimple i₀.property⟩
  have hprimitive : (b.coord i) (D.datum.rootDatum.coroot α.val) = 1 := by
    rw [← hb i, Module.Basis.coord_apply, Module.Basis.repr_self]
    exact Finsupp.single_eq_same
  let C := groupBaseChange F K
  have hcomparison : H.trivialization t = q.groupComparison := orbitTrivialization_eq q V
    (faceOpposite d) (faceModelAction_character q) (faceModelAction_transitive q htrans) t ht
  have hcompare (R : TestAlgebra K) (z : GroupPoints (C.obj H.G.val) R) :
      matF.hom.app ((restrictTestAlgebra F K).obj R) (baseChangePoint F K H.G.val.X R z) =
        splitMat R (z ≫ q.groupComparison.hom.hom.hom) j₀ := by
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    have hz := hscalar R j₀ z
    rw [hcomparison] at hz
    change splitMat R (z ≫ q.groupComparison.hom.hom.hom) j₀ =
      SpecialLinearGroup.map (Algebra.TensorProduct.lift (AlgHom.id F R₀)
        (((Algebra.ofId K R₀).restrictScalars F).comp (emb j₀)) (fun _ _ => Commute.all _ _)).toRingHom
        (mat.hom.app R₀ (baseChangePoint F K H.G.val.X R z ≫ f.hom.hom.hom)) at hz
    rw [scalarLift_eq R₀ e] at hz
    exact hz.symm
  have hmarkF (b : MatrixMark) (R : TestAlgebra F) (z : GroupPoints H.G.val R) :
      b.Holds (matF.hom.app R z) ↔ z ∈ SubgroupSections (H.mark b) _ :=
    (mark_map_iff (tensorGroundEquiv R e).toRingHom (tensorGroundEquiv R e).injective b
      (mat.hom.app R (z ≫ f.hom.hom.hom))).trans (hmark b R z)
  let Vpos := H.mark MatrixMark.positiveRadical
  let Vneg := H.mark MatrixMark.negativeRadical
  obtain ⟨upper, hupper⟩ := additiveMarkIso A₀ H.G Vpos matF 0 1 (by decide)
    (fun R z => (hmarkF MatrixMark.positiveRadical R z).symm.trans (upperMark_iff _))
  obtain ⟨lower, hlower⟩ := additiveMarkIso A₀ H.G Vneg matF 1 0 (by decide)
    (fun R z => (hmarkF MatrixMark.negativeRadical R z).symm.trans (lowerMark_iff _))
  obtain ⟨diagonal, hdiagonal⟩ := diagonalMark H.G L.torus matF (hmarkF MatrixMark.torus)
  obtain ⟨c, hc⟩ := cocharacterFactorsThroughMaximalSplit G (subgroupOfSubgroup M.torus S)
    M.torus hS M.isTorus S.inclusion rfl (diagonal ≫ L.torusMap)
  have hdiagSquare : (diagonal ≫ L.torus.inclusion) ≫ inclusion =
      c ≫ (subgroupOfSubgroup M.torus S).inclusion := by
    change (diagonal ≫ L.torus.inclusion) ≫ inclusion = c ≫ S.inclusion ≫ M.torus.inclusion
    rw [Category.assoc, ← L.intersection.w, ← Category.assoc, ← Category.assoc, hc]
  have hCinc : C.map inclusion = (L.splitFace D).inclusion := by
    change C.map (L.derived.inclusion ≫ L.limit.centralizer.inclusion) =
      (C.map L.derived.inclusion ≫ L.comparison.hom) ≫ L.splitLimit.centralizer.inclusion
    rw [C.map_comp, Category.assoc, L.comparisonSquare]
  -- Normalize the two parameters by conjugating the matrix comparison.
  obtain ⟨s, hs⟩ := additiveIso_linear A₀ q.line q.normalizedLine
  let matNorm := matF ≪≫ scaleMatrixIso s⁻¹
  let matNorm' := matNorm ≪≫ matrixIndexIso F
  let upper' := scaleIso A₀ A₀ s ≪≫ upper
  let lower' := scaleIso A₀ A₀ s⁻¹ ≪≫ lower
  have hupperNorm (R : TestAlgebra F) (x : R) :
      matNorm.hom.app R (rootPoint (upper'.hom ≫ Vpos.inclusion) R x) =
        SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) x := by
    change scaleMatrixGroup (Units.map (algebraMap F R : F →* R) s⁻¹)
      (matF.hom.app R (rootPoint ((scaleIso A₀ A₀ s).hom ≫ upper.hom ≫ Vpos.inclusion) R x)) = _
    rw [rootPoint_comp, scaleIso_point, ← rootPoint_eq, hupper, scaleMatrixUpper]
    congr 1
    change (algebraMap F R (↑s⁻¹ : F)) * (algebraMap F R (s : F) * x) = x
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  have hlowerNorm (R : TestAlgebra F) (x : R) :
      matNorm.hom.app R (rootPoint (lower'.hom ≫ Vneg.inclusion) R x) =
        SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) x := by
    change scaleMatrixGroup (Units.map (algebraMap F R : F →* R) s⁻¹)
      (matF.hom.app R (rootPoint ((scaleIso A₀ A₀ s⁻¹).hom ≫ lower.hom ≫ Vneg.inclusion) R x)) = _
    rw [rootPoint_comp, scaleIso_point, ← rootPoint_eq, hlower, scaleMatrixLower]
    rw [← map_inv, inv_inv]
    congr 1
    change (algebraMap F R (s : F)) * (algebraMap F R (↑s⁻¹ : F) * x) = x
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  let Hsub := subgroupOfSubgroup L.limit.centralizer L.derived
  let Hp := subgroupOfSubgroup Hsub Vpos
  let Hn := subgroupOfSubgroup Hsub Vneg
  let Q : RankOne (subgroupOfSubgroup M.torus S) :=
    { group := H.G
      matrix := matNorm'
      embedding := inclusion
      closedEmbedding := hinclusion
      trivialKernel := hkernel
      positive := Hp
      negative := Hn
      additive := A₀
      upper := upper'
      lower := lower'
      cochar := c
      upperFormula := by
        intro R x
        have hx : matNorm'.inv.app R
              (SpecialLinearGroup.transvection (i := (⟨0⟩ : Index.{u} 2)) (j := ⟨1⟩) (by decide) x) =
            rootPoint (upper'.hom ≫ Vpos.inclusion) R x := by
          apply (matNorm'.app R).groupIsoToMulEquiv.injective
          refine (GrpCat.hom_inv_apply (matNorm'.app R) _).trans ?_
          change _ = reindexSpecialLinear (Equiv.ulift.symm : Fin 2 ≃ Index.{u} 2)
            (matNorm.hom.app R (rootPoint (upper'.hom ≫ Vpos.inclusion) R x))
          rw [hupperNorm]
          exact (reindexTransvection _ _ _ _).symm
        rw [hx, rootPoint_comp]
        simp only [Hp, Hsub, inclusion, subgroupOfSubgroup, Grp.comp_hom_hom, Category.assoc, rootPoint]
      lowerFormula := by
        intro R x
        have hx : matNorm'.inv.app R
              (SpecialLinearGroup.transvection (i := (⟨1⟩ : Index.{u} 2)) (j := ⟨0⟩) (by decide) x) =
            rootPoint (lower'.hom ≫ Vneg.inclusion) R x := by
          apply (matNorm'.app R).groupIsoToMulEquiv.injective
          refine (GrpCat.hom_inv_apply (matNorm'.app R) _).trans ?_
          change _ = reindexSpecialLinear (Equiv.ulift.symm : Fin 2 ≃ Index.{u} 2)
            (matNorm.hom.app R (rootPoint (lower'.hom ≫ Vneg.inclusion) R x))
          rw [hlowerNorm]
          exact (reindexTransvection _ _ _ _).symm
        rw [hx, rootPoint_comp]
        simp only [Hn, Hsub, inclusion, subgroupOfSubgroup, Grp.comp_hom_hom, Category.assoc, rootPoint]
      diagonalFormula := by
        intro R v
        refine ⟨cocharacterPoint (diagonal ≫ L.torus.inclusion) R v, ?_, ?_⟩
        · change unitPoint R v ≫ (diagonal ≫ L.torus.inclusion).hom.hom ≫ inclusion.hom.hom = _
          exact congrArg (fun r => unitPoint R v ≫ r.hom.hom) hdiagSquare
        · change (reindexSpecialLinear (Equiv.ulift.symm : Fin 2 ≃ Index.{u} 2)
            (scaleMatrixGroup (Units.map (algebraMap F R : F →* R) s⁻¹)
              (matF.hom.app R (cocharacterPoint (diagonal ≫ L.torus.inclusion) R v)))).val = _
          rw [hdiagonal, scaleMatrixDiagonal]
          ext ⟨i⟩ ⟨j⟩
          fin_cases i <;> fin_cases j <;> rfl }
  have hdiagK (R : TestAlgebra K) (v : Rˣ) :
      let R₀ := (restrictTestAlgebra F K).obj R
      let y := cocharacterPoint (faceCoroot q i₀ ≫ C.map L.torus.inclusion) R v
      matF.hom.app R₀ (baseChangePoint F K H.G.val.X R y) = rankOneCoroot v := by
    dsimp only
    rw [hcompare]
    let R₀ := (restrictTestAlgebra F K).obj R
    let z := rootPoint (pinnedRootMap H.P.pin j₀) R₀ 0
    obtain ⟨z', hz'⟩ := (baseChangePoints F K H.P.pair.G.val.X R).surjective z
    apply Subtype.ext
    exact (hcoords R j₀ 0 v z' _ hz' (faceCoroot_coordinates q hm' i₀ R v)).2.1
  have hdiagExt : m.hom ≫ C.map diagonal = faceCoroot q i₀ := by
    apply Grp.hom_ext
    apply hom_ext_on_affine_tests
    intro R x
    obtain ⟨v, rfl⟩ := (unitEquiv R).symm.surjective x
    rw [show (unitEquiv R).symm v = unitPoint R v from unitPointHom_apply R v]
    let R₀ := (restrictTestAlgebra F K).obj R
    letI := mono_over _ L.splitClosed
    apply (cancel_mono ((C.map L.torus.inclusion).hom.hom)).mp
    apply (baseChangePoints F K H.G.val.X R).injective
    apply (matF.app R₀).groupIsoToMulEquiv.injective
    change matF.hom.app R₀ (baseChangePoint F K H.G.val.X R
      ((unitPoint R v ≫ (m.hom ≫ C.map diagonal).hom.hom) ≫
        (C.map L.torus.inclusion).hom.hom)) = _
    have hleft :
        (unitPoint R v ≫ (m.hom ≫ C.map diagonal).hom.hom) ≫
            (C.map L.torus.inclusion).hom.hom =
          (unitPoint R v ≫ m.hom.hom.hom) ≫ (C.map (diagonal ≫ L.torus.inclusion)).hom.hom := by
      simp only [C, Functor.map_comp, Grp.comp_hom_hom, Category.assoc]
    rw [hleft]
    have hnat := baseChangePointsSchemeNaturality F K (diagonal ≫ L.torus.inclusion).hom.hom R
      (unitPoint R v ≫ m.hom.hom.hom)
    refine (congrArg (matF.hom.app R₀) (hnat.trans ?_)).trans
      ((hdiagonal R₀ v).trans (hdiagK R v).symm)
    exact congrArg (· ≫ (diagonal ≫ L.torus.inclusion).hom.hom) (hm R v)
  have hcoroot : Additive.ofMul (m.hom ≫ C.map (c ≫ S.inclusion)) =
      D.datum.rootDatum.coroot α.val := by
    have h : m.hom ≫ C.map (c ≫ S.inclusion) = (D.datum.rootDatum.coroot α.val).toMul := by
      rw [hc, C.map_comp, ← Category.assoc, hdiagExt]
      exact faceCoroot_ambient q i₀
    exact congrArg Additive.ofMul h
  let r₀ : ↥(Specs.StandardParabolicLevi.leviRoots D.datum I) :=
    ⟨α.val, Submodule.subset_span ⟨α.val, i₀.property, rfl⟩⟩
  let r := simpleRootsOfAttachedDatum ⟨d.positive.pair d.reductive, d.rootGroups, d.pinning⟩
    d.posDatum (q.vertices i₀)
  have hr : r.val = d.roots r₀ := q.vertexRoot i₀ r₀ rfl
  have hpin (R : TestAlgebra K) (x : R) :
      baseChangePoint F K G.val.X R (rootPoint (pinnedRootMap p α) R x) =
        rootPoint (upper'.hom ≫ Hp.inclusion) ((restrictTestAlgebra F K).obj R) x := by
    let R₀ := (restrictTestAlgebra F K).obj R
    let z := rootPoint (pinnedRootMap d.pinning r) R x
    let x₀ : R₀ := (algebraMap F R₀ (s : F)) * x
    have hz :
        baseChangePoint F K H.P.pair.G.val.X R (z ≫ q.groupComparison.hom.hom.hom) =
          rootPoint (pinnedRootMap H.P.pin j₀) R₀ x₀ := by
      change baseChangePoint F K H.P.pair.G.val.X R
        (rootPoint (pinnedRootMap d.pinning r) R x ≫ q.groupComparison.hom.hom.hom) = _
      rw [← rootPoint_comp, q.rootMap (q.vertices i₀), rootPoint_comp]
      refine (baseChangePointsSchemeNaturality F K
        (q.normalizedLine.hom ≫ q.splitModel.rootMap (q.vertices i₀)).hom.hom R
        (rootPoint a.inv R x)).trans ?_
      rw [hcoord R x, ← rootPoint_comp, Category.id_comp]
      rw [rootPoint_comp q.normalizedLine.hom, hs R₀ x, ← rootPoint_eq]
      rfl
    obtain ⟨y', hy'⟩ := (baseChangePoints F K H.P.pair.G.val.X R).surjective
      (cocharacterPoint (simpleCorootOfAttachedDatum H.P H.D j₀) R₀ (1 : R₀ˣ) ≫
        H.P.pair.T.inclusion.hom.hom)
    have hMat :
        matF.hom.app R₀ (baseChangePoint F K H.G.val.X R z) =
          SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) x₀ := by
      rw [hcompare]
      apply Subtype.ext
      exact (hcoords R j₀ x₀ 1 _ y' hz hy').1
    have hLift : baseChangePoint F K H.G.val.X R z =
          rootPoint (upper'.hom ≫ Vpos.inclusion) R₀ x := by
      apply (matF.app R₀).groupIsoToMulEquiv.injective
      change matF.hom.app R₀ (baseChangePoint F K H.G.val.X R z) =
        matF.hom.app R₀ (rootPoint (upper'.hom ≫ Vpos.inclusion) R₀ x)
      rw [hMat]
      change _ = matF.hom.app R₀
        (rootPoint ((scaleIso A₀ A₀ s).hom ≫ upper.hom ≫ Vpos.inclusion) R₀ x)
      rw [rootPoint_comp, scaleIso_point, ← rootPoint_eq, hupper]
    have hcomparison := d.pinningComparison r₀ α r rfl hr
    rw [← hcomparison, rootPoint_comp, ← hCinc]
    refine (baseChangePointsSchemeNaturality F K inclusion.hom.hom R z).trans ?_
    rw [hLift, ← rootPoint_comp]
    rfl
  -- The two scalar-extended radicals are the single root factors of their Borels.
  let β := oppositeRoot D α.val
  let r₁ : ↥(leviRoots D.datum I) := ⟨β, oppositeRoot_mem_face D r₀.property⟩
  let rp := d.roots r₀
  let rn := d.roots r₁
  letI := d.posDatum.comm
  have hcase (j : Root (G := (L.splitFace D).group) (L.splitFace D).torus) : j = rp ∨ j = rn := by
    obtain ⟨z, rfl⟩ := d.roots.surjective j
    rcases singletonFaceRoots D α.val z.val z.property with he | he
    · exact Or.inl (congrArg d.roots (Subtype.ext he : z = r₀))
    · exact Or.inr (congrArg d.roots (Subtype.ext he : z = r₁))
  have hnegRoot : rn.val = rp.val⁻¹ := by
    rw [(d.rootComparison r₁).1, (d.rootComparison r₀).1, oppositeRoot_character D α.val]
    exact map_inv (Specs.CentralIsogenies.characterPullback (L.splitFace D).toAmbientTorus) α.val.val
  have hpRoots : subgroupRoots (L.splitFace D).torus d.positive.split = {rp} :=
    singletonBorelRoots d.posDatum rp ((d.rootComparison r₀).2.2.1.mpr i₀.property) (by
      intro j
      rcases hcase j with he | he
      · exact Or.inl he
      · exact Or.inr (he.symm ▸ hnegRoot))
  have hnRoots : subgroupRoots (L.splitFace D).torus d.negative.split = {rn} := by
    letI := d.negDatum.comm
    have hnSimple : rn ∈ d.negDatum.base.support := (d.rootComparison r₁).2.2.2.1.mpr
      ⟨α.val, i₀.property, oppositeRoot_character D α.val⟩
    apply singletonBorelRoots d.negDatum rn hnSimple
    intro j
    rcases hcase j with he | he
    · right
      rw [he, hnegRoot, inv_inv]
    · exact Or.inl he
  let Bp : BorelRadical H.G := ⟨d.positive.rational, d.positive.isKBorel, V.positive, V.isPositive⟩
  let Bn : BorelRadical H.G := ⟨d.negative.rational, d.negative.isKBorel, V.negative, V.isNegative⟩
  obtain ⟨tp, tn, ht, htp⟩ := d.opposite
  have htn : tn ≫ d.negative.rational.inclusion = L.torus.inclusion := ht.w.symm.trans htp
  have hHred := reductive_of_semisimple H.G L.semisimple
  obtain ⟨BpK⟩ := extendBorelRadical (K := K) hHred L.torus L.maximal L.splitTorus Bp tp htp
  obtain ⟨BnK⟩ := extendBorelRadical (K := K) hHred L.torus L.maximal L.splitTorus Bn tn htn
  obtain ⟨ip, hip⟩ := baseChangedRadicalIso Bp BpK (d.positive.pair d.reductive)
    (Iso.refl _) d.positive.comparison d.positive.square d.rootGroups rp hpRoots
  obtain ⟨in', hin'⟩ := baseChangedRadicalIso Bn BnK (d.negative.pair d.reductive)
    (Iso.refl _) d.negative.comparison d.negative.square d.rootGroups rn hnRoots
  have rootMatch (x : ↥(leviRoots D.datum I)) :
      ∃ j : (d.rootGroups (d.roots x)).val.group ≅ (U x.val).val.group,
        j.hom ≫ (U x.val).val.inclusion =
          (d.rootGroups (d.roots x)).val.inclusion ≫ C.map inclusion := by
    obtain ⟨J, hJ, eJ, heJ⟩ := (d.rootComparison x).2.2.2.2 (U x.val).val (U x.val).property
    obtain ⟨g, hg⟩ := rootSubgroupIso d.reductive L.splitTorus L.splitMaximal (d.roots x)
      (d.rootGroups (d.roots x)).property hJ
    refine ⟨g ≪≫ eJ, ?_⟩
    rw [Iso.trans_hom, Category.assoc, heJ, ← Category.assoc, hg, hCinc]
  obtain ⟨jp, hjp⟩ := rootMatch r₀
  obtain ⟨jn, hjn⟩ := rootMatch r₁
  have hp := baseChangeClosedSubgroup F K Hp.inclusion Hp.isClosedImmersion
  have hn := baseChangeClosedSubgroup F K Hn.inclusion Hn.isClosedImmersion
  have hpMatch : SameSubgroup (baseChangedSubgroup K Hp hp) (U α.val).val := by
    apply sameSubgroup_of_iso (ip ≪≫ jp)
    change (ip.hom ≫ jp.hom) ≫ (U α.val).val.inclusion = C.map Hp.inclusion
    rw [Category.assoc, hjp, ← Category.assoc, hip, Iso.refl_hom, Category.comp_id, ← Functor.map_comp]
    rfl
  have hnMatch : SameSubgroup (baseChangedSubgroup K Hn hn) (U β).val := by
    apply sameSubgroup_of_iso (in' ≪≫ jn)
    change (in'.hom ≫ jn.hom) ≫ (U β).val.inclusion = C.map Hn.inclusion
    rw [Category.assoc, hjn, ← Category.assoc, hin', Iso.refl_hom, Category.comp_id, ← Functor.map_comp]
    rfl
  exact ⟨β, Q, oppositeRoot_character D α.val, ⟨hp, hn, hpMatch, hnMatch⟩, hpin,
    hcoroot, b.coord i, hprimitive⟩

end

end LinearAlgebraicGroups.Arithmetic.TrialitarianFixedRootSL2
