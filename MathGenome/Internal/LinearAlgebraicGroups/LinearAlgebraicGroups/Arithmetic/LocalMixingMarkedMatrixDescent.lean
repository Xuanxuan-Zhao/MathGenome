import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalMixingMarkedMatrixDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRankOneExtension
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalMixingMarkedMatrixDescent

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.LocalMixingMarkedMatrixDescent
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open CocharacterDynamics (cocharacterPoint unitPoint mapPoints_cocharacterPoint)
open GeneralLinearStructure (SpecialMatrixPoints)
open IntegralFibreReductivity (rankOnePoints)
open IntegralRootRelations (upper lower diagonal)
open QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open RootGroups (AdditiveLine rootPoint)
open Specs.StandardGroups (SLCoordinates determinantOneIdeal universalMatrix)
open Unipotent (Index baseChangedAlgebraicGroup)

open private rankOne_pivot_factorization exists_rankOne_pivots_after_injective_extension
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRankOneExtension
open private mapPoints_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
open private rootPoint_eq rootPoint_comp rootPoint_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private cocharacterPoint_postcompose from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private reindexSpecialLinear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
open private baseChangePointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent
open private SemilinearTestMap SemilinearTestMap.restrict semilinearSource semilinearSourceMap
  semilinearPoint semilinearPoint_apply semilinearPoint_natural scalarMorphism scalarMorphism_descends
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- The pivot chart after an injective extension suffices to compare marked group maps. -/
private theorem rankOneMaps_equal_of_marks (G : AffineAlgebraicGroup F)
    (f g : rankOnePoints F ⟶ (groupPointsFunctor F).obj G.val)
    (hu : ∀ (R : TestAlgebra F) (x : R), f.app R (upper x) = g.app R (upper x))
    (hl : ∀ (R : TestAlgebra F) (x : R), f.app R (lower x) = g.app R (lower x))
    (hd : ∀ (R : TestAlgebra F) (v : Rˣ), f.app R (diagonal v) = g.app R (diagonal v)) : f = g := by
  ext R x
  change Matrix.SpecialLinearGroup (Fin 2) R at x
  obtain ⟨S, hS, a, t, ha, hp⟩ := exists_rankOne_pivots_after_injective_extension [x]
  let _ : Algebra F S := (a.comp (algebraMap F R)).toAlgebra
  let S' := CommAlgCat.of F S
  let j : R ⟶ S' := CommAlgCat.ofHom ⟨a, fun _ => rfl⟩
  let m := Matrix.SpecialLinearGroup.map a x
  have hs : IsUnit ((upper t * m).val 0 0) := hp x (by simp)
  let fS : Matrix.SpecialLinearGroup (Fin 2) S →* GroupPoints G.val S' := (f.app S').hom
  let gS : Matrix.SpecialLinearGroup (Fin 2) S →* GroupPoints G.val S' := (g.app S').hom
  have hUpper (z : S) : fS (upper z) = gS (upper z) := hu S' z
  have hLower (z : S) : fS (lower z) = gS (lower z) := hl S' z
  have hDiagonal (v : Sˣ) : fS (diagonal v) = gS (diagonal v) := hd S' v
  have hchart : fS (upper t * m) = gS (upper t * m) := by
    rw [rankOne_pivot_factorization (upper t * m) hs.unit hs.unit_spec]
    simp only [map_mul, hUpper, hLower, hDiagonal]
  simp only [map_mul, hUpper] at hchart
  apply mapPoints_injective G.property.1 j ha
  exact (ConcreteCategory.congr_hom (f.naturality j) x).symm.trans
    ((mul_left_cancel hchart).trans (ConcreteCategory.congr_hom (g.naturality j) x))

private def rankOneComparison {H : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints H 2) :
    (groupPointsFunctor F).obj H.val ≅ rankOnePoints F :=
  matrix ≪≫ NatIso.ofComponents
    (F := Specs.StandardGroups.specialLinearPoints F (Index.{u} 2)) (G := rankOnePoints F)
    (fun R => (reindexSpecialLinear (R := R) Equiv.ulift).toGrpIso) (by
      intro R S a
      apply GrpCat.ext
      intro x
      exact Subtype.ext rfl)

private theorem rankOneComparison_inv {H : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints H 2)
    (R : TestAlgebra F) (x : Matrix.SpecialLinearGroup (Fin 2) R) :
    (rankOneComparison matrix).inv.app R x = matrix.inv.app R (liftMatrix x) := by
  rfl

private def restrictRankOnePoints : restrictTestAlgebra F K ⋙ rankOnePoints F ≅ rankOnePoints K :=
  NatIso.ofComponents (fun _ => (MulEquiv.refl _).toGrpIso) (by
    intro R S a
    apply GrpCat.ext
    intro x
    rfl)

private def baseChangedComparison {H : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints H 2) :
    (groupPointsFunctor K).obj ((groupBaseChange F K).obj H.val) ≅ rankOnePoints K :=
  baseChangePointIso K H.val ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra F K) (rankOneComparison matrix) ≪≫
    restrictRankOnePoints

private theorem baseChangedComparison_inv {H : AffineAlgebraicGroup F}
    (matrix : SpecialMatrixPoints H 2)
    (R : TestAlgebra K) (x : Matrix.SpecialLinearGroup (Fin 2) R) :
    baseChangePoint F K H.val.X R ((baseChangedComparison matrix).inv.app R x) =
      (rankOneComparison matrix).inv.app ((restrictTestAlgebra F K).obj R) x := by
  exact (baseChangePointsEquiv K H.val.X R).apply_symm_apply _

private theorem baseChangedComparison_semilinear {H : AffineAlgebraicGroup F}
    (matrix : SpecialMatrixPoints H 2) {σ : Gal(K/F)} {R U : TestAlgebra K}
    (a : SemilinearTestMap σ R U)
    (p : GroupPoints ((groupBaseChange F K).obj H.val) R) :
    (baseChangedComparison matrix).hom.app U (semilinearPoint H.val a p) =
      Matrix.SpecialLinearGroup.map (SemilinearTestMap.restrict a).hom.toRingHom
        ((baseChangedComparison matrix).hom.app R p) := by
  let N := rankOneComparison matrix
  change N.hom.app ((restrictTestAlgebra F K).obj U)
      (baseChangePoint F K H.val.X U (semilinearPoint H.val a p)) =
    (rankOnePoints F).map (SemilinearTestMap.restrict a)
      (N.hom.app ((restrictTestAlgebra F K).obj R) (baseChangePoint F K H.val.X R p))
  rw [semilinearPoint_apply]
  exact ConcreteCategory.congr_hom (N.hom.naturality (SemilinearTestMap.restrict a)) _


/-- Descent of a marked point map whose three restrictions already come from F. -/
private theorem descendRankOnePoints [IsGalois F K]
    (H G : AffineAlgebraicGroup F) (matrix : SpecialMatrixPoints H 2)
    (m : rankOnePoints K ⟶ (groupPointsFunctor K).obj ((groupBaseChange F K).obj G.val))
    {A₀ : AdditiveLine F} (yPlus yMinus : A₀.group ⟶ G.val) (C : Cocharacter G.val)
    (hu : ∀ (R : TestAlgebra K) (z : R),
      baseChangePoint F K G.val.X R (m.app R (upper z)) =
        rootPoint yPlus ((restrictTestAlgebra F K).obj R) z)
    (hl : ∀ (R : TestAlgebra K) (z : R),
      baseChangePoint F K G.val.X R (m.app R (lower z)) =
        rootPoint yMinus ((restrictTestAlgebra F K).obj R) z)
    (hd : ∀ (R : TestAlgebra K) (v : Rˣ),
      baseChangePoint F K G.val.X R (m.app R (diagonal v)) =
        cocharacterPoint C ((restrictTestAlgebra F K).obj R) v) :
    ∃ f : H.val ⟶ G.val,
      ∀ (R : TestAlgebra K) (x : Matrix.SpecialLinearGroup (Fin 2) R),
        baseChangePoint F K G.val.X R (m.app R x) =
          ((rankOneComparison matrix).inv.app ((restrictTestAlgebra F K).obj R) x :
            GroupPoints H.val ((restrictTestAlgebra F K).obj R)) ≫ f.hom.hom := by
  let HK := baseChangedAlgebraicGroup K H
  let GK := baseChangedAlgebraicGroup K G
  let N := baseChangedComparison (K := K) matrix
  obtain ⟨g, hg⟩ := (groupHomComparison K HK.val GK.val HK.property.1).surjective (N.hom ≫ m)
  change (groupPointsFunctor K).map g = N.hom ≫ m at hg
  have hpoint (R : TestAlgebra K) (p : GroupPoints HK.val R) :
      p ≫ g.hom.hom = m.app R (N.hom.app R p) := by
    change ((groupPointsFunctor K).map g).app R p = _
    exact congrArg (fun t : (groupPointsFunctor K).obj HK.val ⟶
      (groupPointsFunctor K).obj GK.val => t.app R p) hg
  have hfix (σ : Gal(K/F)) : scalarMorphism σ g = g := by
    let φ := N.inv ≫ (groupPointsFunctor K).map (scalarMorphism σ g)
    have hsem (U : TestAlgebra K) (x : Matrix.SpecialLinearGroup (Fin 2) U) :
        φ.app U x = semilinearPoint G.val (semilinearSourceMap σ U)
          (m.app (semilinearSource σ U)
            (show Matrix.SpecialLinearGroup (Fin 2) (semilinearSource σ U) from x)) := by
      let R := semilinearSource σ U
      let a := semilinearSourceMap σ U
      let p : GroupPoints HK.val R := N.inv.app R x
      have h : N.hom.app R p = (show Matrix.SpecialLinearGroup (Fin 2) R from x) :=
        GrpCat.hom_inv_apply (N.app R) x
      have hmap : Matrix.SpecialLinearGroup.map (SemilinearTestMap.restrict a).hom.toRingHom
          (show Matrix.SpecialLinearGroup (Fin 2) R from x) = x := Subtype.ext rfl
      have hs : N.hom.app U (semilinearPoint H.val a p) = x :=
        (baseChangedComparison_semilinear matrix a p).trans ((congrArg _ h).trans hmap)
      have hp : N.inv.app U x = semilinearPoint H.val a p :=
        (N.app U).groupIsoToMulEquiv.injective ((GrpCat.hom_inv_apply (N.app U) x).trans hs.symm)
      change (N.inv.app U x : GroupPoints HK.val U) ≫ (scalarMorphism σ g).hom.hom = _
      rw [hp, ← semilinearPoint_natural σ a g, hpoint, h]
    have hsemBase (R : TestAlgebra K) (x : Matrix.SpecialLinearGroup (Fin 2) R) :
        baseChangePoint F K G.val.X R (φ.app R x) =
          mapPoints (SemilinearTestMap.restrict (semilinearSourceMap σ R))
            (baseChangePoint F K G.val.X (semilinearSource σ R)
              (m.app (semilinearSource σ R) x)) :=
      (congrArg (baseChangePoint F K G.val.X R) (hsem R x)).trans
        (semilinearPoint_apply G.val (semilinearSourceMap σ R) _)
    have hφ : φ = m := by
      apply rankOneMaps_equal_of_marks GK
      · intro R z
        let a := SemilinearTestMap.restrict (semilinearSourceMap σ R)
        apply (baseChangePoints F K G.val.X R).injective
        exact (hsemBase R (upper z)).trans ((congrArg (mapPoints a) (hu (semilinearSource σ R) z)).trans
          ((rootPoint_natural yPlus a z).trans (hu R z).symm))
      · intro R z
        let a := SemilinearTestMap.restrict (semilinearSourceMap σ R)
        apply (baseChangePoints F K G.val.X R).injective
        exact (hsemBase R (lower z)).trans ((congrArg (mapPoints a) (hl (semilinearSource σ R) z)).trans
          ((rootPoint_natural yMinus a z).trans (hl R z).symm))
      · intro R v
        let a := SemilinearTestMap.restrict (semilinearSourceMap σ R)
        apply (baseChangePoints F K G.val.X R).injective
        have hunit : Units.map a.hom.toMonoidHom v = v := Units.ext rfl
        exact (hsemBase R (diagonal v)).trans
          ((congrArg (mapPoints a) (hd (semilinearSource σ R) v)).trans
          ((mapPoints_cocharacterPoint a C v).trans
            ((congrArg (cocharacterPoint C ((restrictTestAlgebra F K).obj R)) hunit).trans
              (hd R v).symm)))
    apply (groupHomComparison K HK.val GK.val HK.property.1).injective
    have he := congrArg (N.hom ≫ ·) hφ
    change N.hom ≫ (N.inv ≫ (groupPointsFunctor K).map (scalarMorphism σ g)) = N.hom ≫ m at he
    rwa [← Category.assoc, N.hom_inv_id, Category.id_comp, ← hg] at he
  obtain ⟨f, hf⟩ := scalarMorphism_descends H G g hfix
  refine ⟨f, fun R x => ?_⟩
  let p : GroupPoints HK.val R := N.inv.app R x
  have hp : N.hom.app R p = x := GrpCat.hom_inv_apply (N.app R) x
  have h := hpoint R p
  rw [hp, ← hf] at h
  rw [← h]
  exact (baseChangePointsSchemeNaturality F K f.hom.hom R p).trans
    (congrArg (· ≫ f.hom.hom) (baseChangedComparison_inv matrix R x))

private def extensionMap (R : TestAlgebra F) :
    R ⟶ (restrictTestAlgebra F K).obj ((WeilRestriction.extendScalars F K).obj R) := by
  let R₀ := (restrictTestAlgebra F K).obj ((WeilRestriction.extendScalars F K).obj R)
  let j : R →+* (R ⊗[F] K) :=
    (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := R) (B := K)).toRingHom
  letI : Algebra F R₀ := R₀.algebra
  let f : R →ₐ[F] R₀ := {
    toRingHom := j
    commutes' := fun a => by
      change (algebraMap F R a) ⊗ₜ[F] (1 : K) =
        (1 : R) ⊗ₜ[F] (algebraMap F K a)
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (TensorProduct.smul_tmul (R := F) a (1 : R) (1 : K)) }
  exact ConcreteCategory.ofHom (C := CommAlgCat F) f

private theorem extensionMap_injective (R : TestAlgebra F) :
    Function.Injective (extensionMap (K := K) R).hom := by
  change Function.Injective
    (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := R) (B := K)).toRingHom
  exact Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F K).injective

private theorem map_rankOne_upper {R S : TestAlgebra F} (a : R ⟶ S) (z : R) :
    (rankOnePoints F).map a (upper z) = upper (a.hom z) := by
  change Matrix.SpecialLinearGroup.map a.hom.toRingHom (upper z) = _
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper]

private theorem map_rankOne_lower {R S : TestAlgebra F} (a : R ⟶ S) (z : R) :
    (rankOnePoints F).map a (lower z) = lower (a.hom z) := by
  change Matrix.SpecialLinearGroup.map a.hom.toRingHom (lower z) = _
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower]

private theorem map_rankOne_diagonal {R S : TestAlgebra F} (a : R ⟶ S) (v : Rˣ) :
    (rankOnePoints F).map a (diagonal v) = diagonal (Units.map a.hom.toMonoidHom v) := by
  change Matrix.SpecialLinearGroup.map a.hom.toRingHom (diagonal v) = _
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]



private theorem baseChange_rootPoint {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (j : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (hj : ∀ (R : TestAlgebra K) (z : R),
      baseChangePoint F K A₀.group.X R (rootPoint j.inv R z) =
        rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) z)
    {G : GroupScheme F} (y : A₀.group ⟶ G) (R : TestAlgebra K) (z : R) :
    baseChangePoint F K G.X R (rootPoint (j.inv ≫ (groupBaseChange F K).map y) R z) =
      rootPoint y ((restrictTestAlgebra F K).obj R) z := by
  rw [rootPoint_comp]
  let S := (restrictTestAlgebra F K).obj R
  have hy : rootPoint y S z = rootPoint (𝟙 A₀.group) S z ≫ y.hom.hom := rootPoint_eq y S z
  exact (baseChangePointsSchemeNaturality F K y.hom.hom R (rootPoint j.inv R z)).trans
    ((congrArg (fun p : Points A₀.group.X S => p ≫ y.hom.hom) (hj R z)).trans hy.symm)

private theorem baseChange_cocharacterPoint {G : GroupScheme F}
    (e : MultiplicativeComparison F K) (he : PreservesUnits e)
    (C : Cocharacter G) (R : TestAlgebra K) (v : Rˣ) :
    baseChangePoint F K G.X R (cocharacterPoint (e.hom ≫ (groupBaseChange F K).map C) R v) =
      cocharacterPoint C ((restrictTestAlgebra F K).obj R) v := by
  rw [cocharacterPoint_postcompose]
  exact (baseChangePointsSchemeNaturality F K C.hom.hom R (unitPoint R v ≫ e.hom.hom.hom)).trans
    (congrArg (· ≫ C.hom.hom) (he R v))

private theorem closedImmersion_of_restrictedPoints {H G : AffineAlgebraicGroup F}
    (f : H.val ⟶ G.val)
    (h : ∀ (R : TestAlgebra K), Function.Injective
      (fun p : GroupPoints H.val ((restrictTestAlgebra F K).obj R) => p ≫ f.hom.hom)) :
    IsClosedImmersion f.hom.hom.left := by
  apply RootData.RootGroups.isClosedImmersion_of_injectivePoints H G f
  intro R p q hpq
  let S := (WeilRestriction.extendScalars F K).obj R
  let a := extensionMap (K := K) R
  apply mapPoints_injective H.property.1 a (extensionMap_injective (K := K) R)
  apply h S
  exact (Category.assoc _ _ _).trans
    ((congrArg (mapPoints (X := G.val.X) a) hpq).trans (Category.assoc _ _ _).symm)

private theorem point_eq_of_extension (G : AffineAlgebraicGroup F)
    (D : rankOnePoints F ⟶ (groupPointsFunctor F).obj G.val)
    (R : TestAlgebra F) (x : Matrix.SpecialLinearGroup (Fin 2) R) (p : Points G.val.X R)
    (h : let a := extensionMap (K := K) R
         D.app _ ((rankOnePoints F).map a x) = mapPoints a p) :
    D.app R x = p := by
  let a := extensionMap (K := K) R
  apply mapPoints_injective G.property.1 a (extensionMap_injective (K := K) R)
  exact (ConcreteCategory.congr_hom (D.naturality a) x).symm.trans h

set_option maxHeartbeats 1000000 in
/-- The injective matrix map descends with its three marks and prescribed matrix coordinates. -/
theorem markedMatrixDescent : MarkedMatrixDescent.{u} := by
  intro F K _ _ _ _ _ G A₀ A E j e hj he yPlus yMinus C _ _ m hinj hUpper hLower hDiagonal
  have hu (R : TestAlgebra K) (z : R) :
      baseChangePoint F K G.val.X R (m.app R (upper z)) =
        rootPoint yPlus ((restrictTestAlgebra F K).obj R) z :=
    (congrArg (baseChangePoint F K G.val.X R) (hUpper R z)).trans
      (baseChange_rootPoint j hj yPlus R z)
  have hl (R : TestAlgebra K) (z : R) :
      baseChangePoint F K G.val.X R (m.app R (lower z)) =
        rootPoint yMinus ((restrictTestAlgebra F K).obj R) z :=
    (congrArg (baseChangePoint F K G.val.X R) (hLower R z)).trans
      (baseChange_rootPoint j hj yMinus R z)
  have hd (R : TestAlgebra K) (v : Rˣ) :
      baseChangePoint F K G.val.X R (m.app R (diagonal v)) =
        cocharacterPoint C ((restrictTestAlgebra F K).obj R) v :=
    (congrArg (baseChangePoint F K G.val.X R) (hDiagonal R v)).trans
      (baseChange_cocharacterPoint e he C R v)
  obtain ⟨_, operations, _, _, _, _, _, _, _, hRep⟩ :=
    StandardGroups.specialLinearGroupSpecification F (Index.{u} 2)
  let H := @Specs.StandardGroups.spectrum F _ (SLCoordinates F (Index.{u} 2))
    _ operations.hopf inferInstance
  obtain ⟨eSpec, hSpec, matrix, hMatrix⟩ := hRep
  change SpecialMatrixPoints H 2 at matrix
  obtain ⟨f, hDescent⟩ := descendRankOnePoints H G matrix m yPlus yMinus C hu hl hd
  have hf : IsClosedImmersion f.hom.hom.left := by
    apply closedImmersion_of_restrictedPoints (K := K) f
    intro R
    let R₀ := (restrictTestAlgebra F K).obj R
    let b := (rankOneComparison matrix).app R₀
    have hPoint (p : GroupPoints H.val R₀) :
        baseChangePoint F K G.val.X R (m.app R (b.hom p)) = p ≫ f.hom.hom :=
      (hDescent R (b.hom p)).trans
        (congrArg (· ≫ f.hom.hom) (GrpCat.inv_hom_apply b p))
    intro p q hpq
    apply b.groupIsoToMulEquiv.injective
    apply hinj R
    apply (baseChangePoints F K G.val.X R).injective
    exact (hPoint p).trans (hpq.trans (hPoint q).symm)
  let D := (rankOneComparison matrix).inv ≫ (groupPointsFunctor F).map f
  have hD (R : TestAlgebra K) (x : Matrix.SpecialLinearGroup (Fin 2) R) :
      baseChangePoint F K G.val.X R (m.app R x) = D.app ((restrictTestAlgebra F K).obj R) x :=
    hDescent R x
  have hDUpper (R : TestAlgebra F) (z : R) : D.app R (upper z) = rootPoint yPlus R z := by
    let S := (WeilRestriction.extendScalars F K).obj R
    let a := extensionMap (K := K) R
    apply point_eq_of_extension (K := K) G D R
    change D.app _ ((rankOnePoints F).map a (upper z)) = mapPoints a (rootPoint yPlus R z)
    rw [map_rankOne_upper, rootPoint_natural]
    exact (hD S (upper (a.hom z))).symm.trans (hu S (a.hom z))
  have hDLower (R : TestAlgebra F) (z : R) : D.app R (lower z) = rootPoint yMinus R z := by
    let S := (WeilRestriction.extendScalars F K).obj R
    let a := extensionMap (K := K) R
    apply point_eq_of_extension (K := K) G D R
    change D.app _ ((rankOnePoints F).map a (lower z)) = mapPoints a (rootPoint yMinus R z)
    rw [map_rankOne_lower, rootPoint_natural]
    exact (hD S (lower (a.hom z))).symm.trans (hl S (a.hom z))
  have hDDiagonal (R : TestAlgebra F) (v : Rˣ) : D.app R (diagonal v) = cocharacterPoint C R v := by
    let S := (WeilRestriction.extendScalars F K).obj R
    let a := extensionMap (K := K) R
    apply point_eq_of_extension (K := K) G D R
    change D.app _ ((rankOnePoints F).map a (diagonal v)) = mapPoints a (cocharacterPoint C R v)
    rw [map_rankOne_diagonal, mapPoints_cocharacterPoint]
    exact (hD S (diagonal (Units.map a.hom.toMonoidHom v))).symm.trans
      (hd S (Units.map a.hom.toMonoidHom v))
  refine ⟨operations, matrix, f, hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro R a
    let p : Points H.val.X R := (testSpec F).map (CommAlgCat.ofHom a).op
    have hPoint : (eSpec.hom.app R (WithConv.toConv a) : Points H.val.X R) = p :=
      Over.OverMorphism.ext (hSpec R a)
    have hEval := hMatrix R a
    change (show Matrix.SpecialLinearGroup (Index.{u} 2) R from
      matrix.hom.app R (eSpec.hom.app R (WithConv.toConv a))).val = _ at hEval
    rw [hPoint] at hEval
    exact hEval
  · intro R z
    exact (congrArg (· ≫ f.hom.hom) (rankOneComparison_inv matrix R (upper z))).symm.trans (hDUpper R z)
  · intro R z
    exact (congrArg (· ≫ f.hom.hom) (rankOneComparison_inv matrix R (lower z))).symm.trans (hDLower R z)
  · intro R v
    exact (congrArg (· ≫ f.hom.hom) (rankOneComparison_inv matrix R (diagonal v))).symm.trans (hDDiagonal R v)
  · intro R x
    exact (hDescent R x).trans (congrArg (· ≫ f.hom.hom)
      (rankOneComparison_inv matrix ((restrictTestAlgebra F K).obj R) x))

end

end LinearAlgebraicGroups.Arithmetic.LocalMixingMarkedMatrixDescent
