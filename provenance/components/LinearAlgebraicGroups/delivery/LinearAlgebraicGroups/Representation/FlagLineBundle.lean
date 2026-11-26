import Specs.LinearAlgebraicGroups.Representation.FlagLineBundle
import LinearAlgebraicGroups.Affine.ComoduleFiniteness
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import LinearAlgebraicGroups.Flag.ProjectiveFlags
import LinearAlgebraicGroups.Flag.BruhatCells
import LinearAlgebraicGroups.Flag.OpenCell
import LinearAlgebraicGroups.RootData.BorelPositivity
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Valuation.ValuationSubring

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open Coalgebra Bialgebra WithConv
open scoped TensorProduct CategoryTheory.MonObj

universe u

noncomputable section

namespace LinearAlgebraicGroups.FlagLineBundle

open Specs.FlagLineBundle
open Algebra.TensorProduct (includeLeft includeRight)

variable {k : Type u} [Field k] {A D : HopfAlgebraCategory k}

private def tensorPoint {U V R : Type u} [CommRing U] [CommRing V] [CommRing R]
    [Algebra k U] [Algebra k V] [Algebra k R] (g : U →ₐ[k] R) (h : V →ₐ[k] R) :
    U ⊗[k] V →ₐ[k] R :=
  Algebra.TensorProduct.lift g h (fun _ _ ↦ Commute.all _ _)

@[simp]
private theorem tensorPoint_tmul {U V R : Type u} [CommRing U] [CommRing V] [CommRing R]
    [Algebra k U] [Algebra k V] [Algebra k R] (g : U →ₐ[k] R) (h : V →ₐ[k] R)
    (x : U) (y : V) : tensorPoint g h (x ⊗ₜ[k] y) = g x * h y :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

private theorem tensorPoint_inclusions {U V : Type u} [CommRing U] [CommRing V]
    [Algebra k U] [Algebra k V] :
    tensorPoint includeLeft includeRight = AlgHom.id k (U ⊗[k] V) :=
  Algebra.TensorProduct.lift_includeLeft_includeRight

private theorem tensorPoint_post {U V R S : Type u} [CommRing U] [CommRing V]
    [CommRing R] [CommRing S] [Algebra k U] [Algebra k V] [Algebra k R] [Algebra k S]
    (j : R →ₐ[k] S) (g : U →ₐ[k] R) (h : V →ₐ[k] R) :
    tensorPoint (j.comp g) (j.comp h) = j.comp (tensorPoint g h) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp only [tensorPoint_tmul, AlgHom.comp_apply, map_mul]

private theorem tensorPoint_map {U V U' V' R : Type u} [CommRing U] [CommRing V]
    [CommRing U'] [CommRing V'] [CommRing R]
    [Algebra k U] [Algebra k V] [Algebra k U'] [Algebra k V'] [Algebra k R]
    (f : U' →ₐ[k] U) (l : V' →ₐ[k] V) (g : U →ₐ[k] R) (h : V →ₐ[k] R) :
    (tensorPoint g h).comp (Algebra.TensorProduct.map f l) =
      tensorPoint (g.comp f) (h.comp l) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp only [tensorPoint_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]

private theorem includeLeft_mul_includeRight {U V : Type u} [CommRing U] [CommRing V]
    [Algebra k U] [Algebra k V] (x : U) (y : V) :
    (includeLeft (R := k) (S := k) x : U ⊗[k] V) *
      includeRight (R := k) y = x ⊗ₜ[k] y := by
  exact DFunLike.congr_fun (tensorPoint_inclusions (k := k) (U := U) (V := V)) (x ⊗ₜ[k] y)

private theorem convolution_apply {R : TestAlgebra k}
    (g h : A →ₐ[k] R) (f : A) :
    ((toConv g * toConv h : WithConv (A →ₐ[k] R))) f =
      tensorPoint g h (comul f) :=
  AlgHom.convMul_apply ..

private theorem comul_counit_groupLike (D : HopfAlgebraCategory k) (c : GroupLike k D) :
    ∃ ρ : RightComodule k D k, ∀ z, ρ.coaction z = z ⊗ₜ[k] (c : D) := by
  let t := (TensorProduct.mk k k D).flip (c : D)
  refine ⟨⟨t, ?_, ?_⟩, fun _ ↦ rfl⟩
  · intro z
    change TensorProduct.assoc k k D D (t.rTensor D (z ⊗ₜ[k] (c : D))) =
      (comul (R := k)).lTensor k (z ⊗ₜ[k] (c : D))
    simp [t, c.2.comul_eq_tmul_self]
  · intro z
    change TensorProduct.rid k k ((counit (R := k)).lTensor k (z ⊗ₜ[k] (c : D))) = z
    simp [c.2.counit_eq_one]

/-- The character acts on the one-dimensional vector space by its scalar coordinate. -/
theorem characterLine : CharacterLine.{u} :=
  fun D c ↦ comul_counit_groupLike D c

/-- The coordinate of a character is group-like. -/
theorem characterCoordinate_groupLike
    (φ : Specs.DiagonalizableGroups.groupAlgebra k
      Specs.DiagonalizableGroups.IntegerCharacters ⟶ D) :
    IsGroupLikeElem k (characterCoordinate φ) := by
  refine IsGroupLikeElem.map φ.hom ?_
  constructor
  · simp
  · simp

private def rightMultiplicationHom (q : A ⟶ D) : A →ₐ[k] A ⊗[k] D :=
  (Algebra.TensorProduct.map (AlgHom.id k A) q.hom.toAlgHom).comp (comulAlgHom k A)

private theorem rightMultiplicationHom_linear (q : A ⟶ D) :
    (rightMultiplicationHom q).toLinearMap = q.hom.toAlgHom.toLinearMap.lTensor A ∘ₗ comul :=
  rfl

private theorem rightEval (q : A ⟶ D) {R : TestAlgebra k}
    (g : A →ₐ[k] R) (b : D →ₐ[k] R) (f : A) :
    tensorPoint g b (rightMultiplicationHom q f) =
      ((toConv g * toConv (b.comp q.hom.toAlgHom) : WithConv (A →ₐ[k] R))) f := by
  rw [convolution_apply]
  change (tensorPoint g b |>.comp (Algebra.TensorProduct.map (AlgHom.id k A) q.hom.toAlgHom))
    (comul f) = _
  congr 1
  apply Algebra.TensorProduct.ext'
  intro x y
  simp

/-- Covariance is the scheme identity, so the equivalence holds uniformly
over all commutative test algebras. -/
theorem covarianceOnPoints : CovarianceOnPoints.{u} := by
  intro k _ A D q c f
  change rightMultiplicationHom q f = f ⊗ₜ[k] (↑(c⁻¹) : D) ↔ _
  constructor
  · intro hf R g b
    rw [← rightEval q g.ofConv b f, hf, tensorPoint_tmul, mul_comm]
  · intro hf
    specialize hf (CommAlgCat.of k (A ⊗[k] D)) (toConv includeLeft) includeRight
    rw [← rightEval q (R := CommAlgCat.of k (A ⊗[k] D)) includeLeft includeRight f,
      tensorPoint_inclusions] at hf
    change rightMultiplicationHom q f = _ at hf
    rw [hf, mul_comm]
    exact includeLeft_mul_includeRight f (↑(c⁻¹) : D)

private def leftCoactionHom (A : HopfAlgebraCategory k) : A →ₐ[k] A ⊗[k] A :=
  (Algebra.TensorProduct.map (AlgHom.id k A) (HopfAlgebra.antipodeAlgHom k A)).comp
    ((Algebra.TensorProduct.comm k A A).toAlgHom.comp (comulAlgHom k A))

private theorem leftCoactionHom_linear (A : HopfAlgebraCategory k) :
    (leftCoactionHom A).toLinearMap = leftRegularCoaction A :=
  rfl

private theorem leftEval {R : TestAlgebra k} (g h : A →ₐ[k] R) (f : A) :
    let := convolutionGroup A R
    tensorPoint g h (leftCoactionHom A f) =
      (((toConv h)⁻¹ * toConv g : WithConv (A →ₐ[k] R))) f := by
  change _ = ((toConv (h.comp (HopfAlgebra.antipodeAlgHom k A)) * toConv g :
    WithConv (A →ₐ[k] R))) f
  rw [convolution_apply]
  change (tensorPoint g h |>.comp ((Algebra.TensorProduct.map (AlgHom.id k A)
    (HopfAlgebra.antipodeAlgHom k A)).comp (Algebra.TensorProduct.comm k A A).toAlgHom))
      (comul f) = _
  congr 1
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [mul_comm]

private theorem coassocLeft (A : HopfAlgebraCategory k) (f : A) :
    TensorProduct.assoc k A A A
        ((leftRegularCoaction A).rTensor A (leftRegularCoaction A f)) =
      (comul (R := k)).lTensor A (leftRegularCoaction A f) := by
  let R := CommAlgCat.of k (A ⊗[k] (A ⊗[k] A))
  let := convolutionGroup A R
  let g : A →ₐ[k] R := includeLeft
  let h : A →ₐ[k] R := includeRight.comp includeLeft
  let j : A →ₐ[k] R := includeRight.comp includeRight
  have hj : tensorPoint h j = (includeRight : A ⊗[k] A →ₐ[k] R) := by
    dsimp only [h, j]
    rw [tensorPoint_post, tensorPoint_inclusions, AlgHom.comp_id]
  have hghj : tensorPoint g (tensorPoint h j) = AlgHom.id k R := by
    rw [hj]
    exact tensorPoint_inclusions
  have hassoc : (tensorPoint (tensorPoint g h) j).toLinearMap =
      (TensorProduct.assoc k A A A).toLinearMap := by
    apply TensorProduct.ext_threefold
    intro x y z
    simp only [AlgHom.toLinearMap_apply, tensorPoint_tmul, LinearEquiv.coe_toLinearMap,
      TensorProduct.assoc_tmul]
    change (includeLeft (R := k) (S := k) x : A ⊗[k] (A ⊗[k] A)) *
        includeRight (R := k) (includeLeft (R := k) (S := k) y) *
          includeRight (R := k) (includeRight (R := k) z) = _
    rw [mul_assoc, ← map_mul, includeLeft_mul_includeRight (k := k),
      includeLeft_mul_includeRight (k := k)]
  have hgh : (tensorPoint g h).comp (leftCoactionHom A) =
      ((toConv h)⁻¹ * toConv g : WithConv (A →ₐ[k] R)).ofConv :=
    AlgHom.ext (leftEval (R := R) g h)
  have hmul : (tensorPoint h j).comp (comulAlgHom k A) =
      (toConv h * toConv j : WithConv (A →ₐ[k] R)).ofConv :=
    AlgHom.ext (fun x ↦ (convolution_apply (R := R) h j x).symm)
  rw [← LinearEquiv.coe_toLinearMap, ← hassoc]
  change ((tensorPoint (tensorPoint g h) j).comp
      (Algebra.TensorProduct.map (leftCoactionHom A) (AlgHom.id k A))) (leftCoactionHom A f) =
    ((AlgHom.id k R).comp (Algebra.TensorProduct.map (AlgHom.id k A) (comulAlgHom k A)))
      (leftCoactionHom A f)
  rw [← hghj, tensorPoint_map, tensorPoint_map, hgh, hmul, AlgHom.comp_id, AlgHom.comp_id]
  rw [leftEval (R := R), leftEval (R := R), mul_inv_rev, mul_assoc]

private theorem counitLeft (A : HopfAlgebraCategory k) (f : A) :
    TensorProduct.rid k A ((counit (R := k)).lTensor A (leftRegularCoaction A f)) = f := by
  let R := CommAlgCat.of k A
  let := convolutionGroup A R
  let g := AlgHom.id k A
  let e : A →ₐ[k] R := (1 : WithConv (A →ₐ[k] R)).ofConv
  have h : (tensorPoint g e).toLinearMap =
      (TensorProduct.rid k A).toLinearMap.comp ((counit (R := k)).lTensor A) := by
    ext a b
    simp [g, e, R, AlgHom.convOne_apply, Algebra.smul_def, mul_comm]
  rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply, ← h]
  change tensorPoint g e (leftCoactionHom A f) = f
  rw [leftEval (R := R)]
  change ((1 : WithConv (A →ₐ[k] R))⁻¹ * toConv g) f = f
  simp [g]

private def leftRegular (A : HopfAlgebraCategory k) : RightComodule k A A where
  coaction := leftRegularCoaction A
  coassoc := coassocLeft A
  counit := counitLeft A

private theorem covariant_stable (q : A ⟶ D) (c : GroupLike k D) :
    (leftRegular A).IsSubcomodule (covariantFunctions q c) := by
  let M := covariantFunctions q c
  let d := (rightMultiplicationHom q).toLinearMap
  let t := (TensorProduct.mk k A D).flip (↑(c⁻¹) : D)
  have heq : LinearMap.eqLocus (d.rTensor A) (t.rTensor A) =
      LinearMap.range (M.subtype.rTensor A) := by
    have hM : M = LinearMap.ker (d - t) := LinearMap.eqLocus_eq_ker_sub _ _
    rw [LinearMap.eqLocus_eq_ker_sub, ← LinearMap.rTensor_sub, hM, ← LinearMap.exact_iff]
    exact Module.Flat.rTensor_exact A (LinearMap.exact_subtype_ker_map (d - t))
  intro f
  rw [← heq]
  change d.rTensor A (leftRegularCoaction A f) = t.rTensor A (leftRegularCoaction A f)
  let R := CommAlgCat.of k ((A ⊗[k] D) ⊗[k] A)
  let := convolutionGroup A R
  let g : A →ₐ[k] R := includeLeft.comp includeLeft
  let b : D →ₐ[k] R := includeLeft.comp includeRight
  let h : A →ₐ[k] R := includeRight
  have hgb : tensorPoint g b = (includeLeft : A ⊗[k] D →ₐ[k] R) := by
    dsimp only [g, b]
    rw [tensorPoint_post, tensorPoint_inclusions, AlgHom.comp_id]
  have hL : Algebra.TensorProduct.map (rightMultiplicationHom q) (AlgHom.id k A) =
      tensorPoint (toConv g * toConv (b.comp q.hom.toAlgHom) :
        WithConv (A →ₐ[k] R)).ofConv h := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [tensorPoint_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [← rightEval q (R := R) g b, hgb]
    exact (includeLeft_mul_includeRight (rightMultiplicationHom q x) y).symm
  have hR : t.rTensor A =
      b (↑(c⁻¹) : D) • (tensorPoint g h).toLinearMap := by
    ext x y
    change x ⊗ₜ[k] (↑(c⁻¹) : D) ⊗ₜ[k] y =
      (includeLeft (R := k) (S := k) (includeRight (R := k) (↑(c⁻¹) : D)) : (A ⊗[k] D) ⊗[k] A) *
        (includeLeft (R := k) (S := k) (includeLeft (R := k) (S := k) x) *
          includeRight (R := k) y)
    rw [← mul_assoc, ← map_mul, mul_comm (includeRight (R := k) _) (includeLeft (R := k) (S := k) x),
      includeLeft_mul_includeRight (k := k), includeLeft_mul_includeRight (k := k)]
  rw [hR]
  change (Algebra.TensorProduct.map (rightMultiplicationHom q) (AlgHom.id k A))
      (leftCoactionHom A f) = b (↑(c⁻¹) : D) * tensorPoint g h (leftCoactionHom A f)
  rw [hL, leftEval (R := R), leftEval (R := R), ← mul_assoc]
  exact (covarianceOnPoints q c f).mp f.property R ((toConv h)⁻¹ * toConv g) b

/-- The functions with the prescribed right covariance form a rational module
for left translation. -/
theorem covariantCoaction : CovariantCoaction.{u} := by
  intro k _ A D q c
  dsimp only
  obtain ⟨ρ, hρ⟩ :=
    (LinearAlgebraicGroups.RightComodule.isSubcomodule_iff_exists_coaction (leftRegular A)
      (covariantFunctions q c)).mp (covariant_stable q c)
  refine ⟨ρ, hρ, ?_⟩
  intro R h g f
  change tensorPoint g.ofConv h.ofConv
    (((covariantFunctions q c).subtype.rTensor A ∘ₗ ρ.coaction) f) = _
  rw [hρ]
  exact leftEval (R := R) g.ofConv h.ofConv (f : A)

open private kBorel_smooth_connected from LinearAlgebraicGroups.RootData.BorelsAndChambers

/-- The opposite Borel projects onto the chosen torus, and its quotient is the
smooth projective flag scheme with the right quotient torsor. -/
theorem oppositeFlagGeometry : OppositeFlagGeometry.{u} := by
  intro k _ G P
  have hPar : Specs.BorelProper.IsParabolic G P.negative := by
    refine ⟨P.reductive, (kBorel_smooth_connected G P.negative P.negativeBorel).1, ?_⟩
    obtain ⟨h, hb⟩ := P.negativeBorel
    exact ⟨h, _, hb, ⟨𝟙 _, Category.id_comp _⟩⟩
  obtain ⟨hQ, hgeo⟩ := ProjectiveFlags.smoothProjectiveQuotient k G P.negative hPar
  obtain ⟨_, htor⟩ := HomogeneousQuotient.homogeneousQuotient k G P.negative
  refine ⟨?_, hQ, ?_⟩
  · obtain ⟨_hcomm, _, _, _, _, _, hproj⟩ :=
      RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
    obtain ⟨R, j, q, hR, _, hj, hjq, hkern, _, _⟩ :=
      hproj P.negative P.negativeBorel P.inNegative
    exact ⟨⟨j, hj, q, hjq, R, hR, hkern⟩⟩
  · intro Q
    obtain ⟨hs, hproper, V, hV, hMV, hFV, _, _, a, j, hj, _, ha, _⟩ := hgeo Q
    exact ⟨hs, hproper, (htor Q).1, V, hV, hMV, hFV, a, j, hj, ha⟩


section Geometry

open CategoryTheory.CartesianMonoidalCategory
open Specs.CharacterDescent (Character)
open Specs.QuotientEmbedding (Presentation)
open private descends from LinearAlgebraicGroups.Reductive.BorelProper
open private comp_rightMultiplication from LinearAlgebraicGroups.Flag.HomogeneousQuotient

/-- The character extends along the Borel projection and gives the coefficient
of the one-dimensional Borel module. -/
theorem borelCharacterLine : BorelCharacterLine.{u} := by
  intro k _ G P p χ
  have hAff : IsAffine P.negative.group.X.left :=
    (Specs.Unipotent.closedSubgroupAlgebraicGroup P.negative).property.1
  obtain ⟨D, ⟨d⟩⟩ := AlgebraicGeometry.essImage_hopfSpec.mpr hAff
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let φ := (ff.preimage (d.hom ≫ p.projection ≫ χ)).unop
  let c : GroupLike k D.unop := ⟨characterCoordinate φ, characterCoordinate_groupLike φ⟩
  obtain ⟨ρ, hρ⟩ := characterLine D.unop c
  exact ⟨D.unop, d, φ, c, ρ, ff.map_preimage _, rfl, hρ⟩

private def linePointEquiv (R : TestAlgebra k) : R ≃ Points (affineLine k) R :=
  (Polynomial.aevalEquiv (R := k) (A := R)).trans
    ((ConcreteCategory.homEquiv (X := CommAlgCat.of k (Polynomial k)) (Y := R)).symm.trans
      (Quiver.Hom.opEquiv.trans (algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv))

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {G : Specs.AffineAlgebraicGroup k} {P : OppositeBorelPair G}
  {p : BorelProjection P} {χ : Character P.torus.group}

private theorem linePointEquiv_apply (R : TestAlgebra k) (z : R) :
    linePointEquiv R z = linePoint R z :=
  rfl

private theorem linePoint_comp {R S : TestAlgebra k} (g : R →ₐ[k] S) (f : R) :
    (testSpec k).map (CommAlgCat.ofHom g).op ≫ linePoint R f = linePoint S (g f) := by
  have h : g.comp (Polynomial.aeval f) = Polynomial.aeval (g f) := by
    apply Polynomial.algHom_ext
    simp
  rw [linePoint, linePoint, ← Functor.map_comp]
  congr 1
  exact congrArg Quiver.Hom.op (CommAlgCat.hom_ext h)

private def affinePoint (R : TestAlgebra k) (g : A →ₐ[k] R) : Points (specGroup A).X R :=
  (testSpec k).map (CommAlgCat.ofHom g).op

private theorem affinePoint_specGroupMap (R : TestAlgebra k) (q : A ⟶ D)
    (b : D →ₐ[k] R) :
    affinePoint R b ≫ (specGroupMap q).hom.hom = affinePoint R (b.comp q.hom.toAlgHom) := by
  change (testSpec k).map (CommAlgCat.ofHom b).op ≫
    (testSpec k).map (CommAlgCat.ofHom q.hom.toAlgHom).op = _
  rw [← Functor.map_comp]
  rfl

private theorem affinePoint_mul {R : TestAlgebra k} (g h : WithConv (A →ₐ[k] R)) :
    affinePoint R (g * h).ofConv = affinePoint R g.ofConv * affinePoint R h.ofConv :=
  (Spec.mapMulEquiv (R := k) (S := A) (T := R)).map_mul g h

private theorem affinePoint_inv {R : TestAlgebra k} (g : WithConv (A →ₐ[k] R)) :
    letI := convolutionGroup A R
    affinePoint R g⁻¹.ofConv = (affinePoint R g.ofConv)⁻¹ := by
  letI := convolutionGroup A R
  exact (Spec.mapMulEquiv (R := k) (S := A) (T := R)).map_inv g

private def affinePointEquiv (A : HopfAlgebraCategory k) (R : TestAlgebra k) :
    (A →ₐ[k] R) ≃ Points (specGroup A).X R :=
  (ConcreteCategory.homEquiv (X := CommAlgCat.of k A) (Y := R)).symm.trans
    (Quiver.Hom.opEquiv.trans (algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv)

private theorem affinePointEquiv_apply (R : TestAlgebra k) (g : A →ₐ[k] R) :
    affinePointEquiv A R g = affinePoint R g :=
  rfl

private theorem inverseCharacterValue {D : HopfAlgebraCategory k}
    (d : specGroup D ≅ P.negative.group)
    (φ : Specs.DiagonalizableGroups.groupAlgebra k
      Specs.DiagonalizableGroups.IntegerCharacters ⟶ D)
    (hφ : specGroupMap φ = d.hom ≫ p.projection ≫ χ)
    (c : GroupLike k D) (hc : (c : D) = characterCoordinate φ)
    (R : TestAlgebra k) (b : D →ₐ[k] R) :
    Specs.CharacterPairing.characterValue (p.projection ≫ χ) R
      ((affinePoint R b ≫ d.hom.hom.hom)⁻¹) = b (↑(c⁻¹) : D) := by
  letI := convolutionGroup D R
  let bi : D →ₐ[k] R := (toConv b)⁻¹.ofConv
  have hbi : affinePoint R bi = (affinePoint R b)⁻¹ := affinePoint_inv (toConv b)
  have ht : ((affinePoint R b ≫ d.hom.hom.hom)⁻¹) ≫ (p.projection ≫ χ).hom.hom =
      affinePoint R (bi.comp φ.hom.toAlgHom) := by
    rw [← GrpObj.inv_comp, ← hbi, Category.assoc]
    change affinePoint R bi ≫ (d.hom ≫ p.projection ≫ χ).hom.hom = _
    rw [← hφ, affinePoint_specGroupMap]
  unfold Specs.CharacterPairing.characterValue
  rw [ht]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((testSpec k).map (CommAlgCat.ofHom (bi.comp φ.hom.toAlgHom)).op)).unop.hom
      (MonoidAlgebra.single Specs.DiagonalizableGroups.integerGenerator 1) = _
  rw [Functor.FullyFaithful.preimage_map]
  change b (HopfAlgebra.antipode k (characterCoordinate φ)) = b (↑(c⁻¹) : D)
  rw [GroupLike.val_inv, hc]

private def coordinateFunction (e : specGroup A ≅ G.val) (f : A) :
    G.val.X ⟶ affineLine k := e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) f

private theorem eval_coordinateFunction (e : specGroup A ≅ G.val)
    (R : TestAlgebra k) (g : A →ₐ[k] R) (f : A) :
    (affinePoint R g ≫ e.hom.hom.hom) ≫ coordinateFunction e f = linePoint R (g f) := by
  dsimp only [coordinateFunction]
  have h : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 (specGroup A).X :=
    (Grp.forget (SchemeOver k)).mapIso e |>.hom_inv_id
  rw [Category.assoc, ← Category.assoc e.hom.hom.hom, h, Category.id_comp]
  exact linePoint_comp (R := CommAlgCat.of k A) (S := R) g f

private theorem point_right_mul (e : specGroup A ≅ G.val)
    (d : specGroup D ≅ P.negative.group) (q : A ⟶ D)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (b : D →ₐ[k] R) :
    (affinePoint R g.ofConv ≫ e.hom.hom.hom) *
      ((affinePoint R b ≫ d.hom.hom.hom) ≫ P.negative.inclusion.hom.hom) =
    affinePoint R (g * toConv (b.comp q.hom.toAlgHom)).ofConv ≫ e.hom.hom.hom := by
  have he := congrArg (fun f : specGroup D ⟶ G.val ↦ f.hom.hom) hq
  change (specGroupMap q).hom.hom ≫ e.hom.hom.hom =
    d.hom.hom.hom ≫ P.negative.inclusion.hom.hom at he
  rw [Category.assoc, ← he, ← Category.assoc, affinePoint_specGroupMap,
    affinePoint_mul, MonObj.mul_comp]

private theorem transport_point_surjective {H : Specs.GroupScheme k}
    (e : specGroup A ≅ H) (R : TestAlgebra k) :
    Function.Surjective (fun g : A →ₐ[k] R ↦ affinePoint R g ≫ e.hom.hom.hom) := by
  intro h
  obtain ⟨g, hg⟩ := (affinePointEquiv A R).surjective (h ≫ e.inv.hom.hom)
  refine ⟨g, ?_⟩
  change affinePoint R g ≫ e.hom.hom.hom = h
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.X :=
    (Grp.forget (SchemeOver k)).mapIso e |>.inv_hom_id
  rw [← affinePointEquiv_apply, hg, Category.assoc, he, Category.comp_id]

private def coordinateFunctionEquiv (e : specGroup A ≅ G.val) :
    A ≃ (G.val.X ⟶ affineLine k) :=
  (linePointEquiv (CommAlgCat.of k A)).trans
    (Iso.homCongr ((Grp.forget (SchemeOver k)).mapIso e) (Iso.refl _))

private theorem coordinateFunctionEquiv_apply (e : specGroup A ≅ G.val) (f : A) :
    coordinateFunctionEquiv e f = coordinateFunction e f := by
  change e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) f ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

private theorem schemeCovariant_iff
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group) (q : A ⟶ D)
    (φ : Specs.DiagonalizableGroups.groupAlgebra k
      Specs.DiagonalizableGroups.IntegerCharacters ⟶ D)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion)
    (hφ : specGroupMap φ = d.hom ≫ p.projection ≫ χ)
    (c : GroupLike k D) (hc : (c : D) = characterCoordinate φ) (f : A) :
    SchemeCovariant p χ (coordinateFunction e f) ↔ f ∈ covariantFunctions q c := by
  rw [covarianceOnPoints q c f]
  constructor
  · intro hf R g b
    have h := hf R (affinePoint R g.ofConv ≫ e.hom.hom.hom)
      (affinePoint R b ≫ d.hom.hom.hom) (g f) (eval_coordinateFunction e R g.ofConv f)
    rw [point_right_mul e d q hq R g b, eval_coordinateFunction,
      inverseCharacterValue d φ hφ c hc R b] at h
    exact (linePointEquiv R).injective h
  · intro hf R g b z hz
    obtain ⟨g', rfl⟩ := transport_point_surjective e R g
    obtain ⟨b', rfl⟩ := transport_point_surjective d R b
    rw [eval_coordinateFunction] at hz
    have hz' : g' f = z := (linePointEquiv R).injective hz
    rw [point_right_mul e d q hq R (toConv g') b', eval_coordinateFunction,
      inverseCharacterValue d φ hφ c hc R b', ← hz']
    exact congrArg (linePoint R) (hf R (toConv g') b')

/-- Pullback through the chosen spectrum isomorphism carries the scheme
covariance equation to the corresponding coordinate-algebra equalizer. -/
theorem schemeCovarianceComparison : SchemeCovarianceComparison.{u} := by
  intro k _ G P p χ A D e d q φ hq hφ c hc
  refine ⟨coordinateFunctionEquiv e, coordinateFunctionEquiv_apply e, fun f ↦ ?_⟩
  rw [coordinateFunctionEquiv_apply]
  exact (schemeCovariant_iff e d q φ hq hφ c hc f).symm

variable {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
  (L : AssociatedBundle Q a p χ)

private def sectionGraph (s : BundleSection L) : G.val.X ⟶ G.val.X ⨯ affineLine k :=
  L.trivializes.lift (𝟙 _) (Q.projection ≫ s.val) (by
    simp [Category.assoc, s.property])

private theorem sectionGraph_fst (s : BundleSection L) :
    sectionGraph L s ≫ prod.fst = 𝟙 _ :=
  L.trivializes.lift_fst _ _ _

private theorem sectionGraph_factor (s : BundleSection L) :
    sectionGraph L s ≫ L.trivialization = Q.projection ≫ s.val :=
  L.trivializes.lift_snd _ _ _

private theorem sectionGraph_eq (s : BundleSection L) :
    sectionGraph L s = prod.lift (𝟙 _) (sectionGraph L s ≫ prod.snd) := by
  apply prod.hom_ext
  · rw [sectionGraph_fst, prod.lift_fst]
  · rw [prod.lift_snd]

private theorem sectionGraph_covariant (s : BundleSection L) :
    SchemeCovariant p χ (sectionGraph L s ≫ prod.snd) := by
  intro R g b z hz
  let gb := g * (b ≫ P.negative.inclusion.hom.hom)
  let u := Specs.CharacterPairing.characterValue (p.projection ≫ χ) R (b⁻¹)
  have hg : g ≫ sectionGraph L s = prod.lift g (linePoint R z) := by
    apply prod.hom_ext
    · simp [Category.assoc, sectionGraph_fst]
    · simpa only [prod.lift_snd, Category.assoc] using hz
  have hgb : g ≫ Q.projection = gb ≫ Q.projection := by
    have eq := (HomogeneousQuotient.quotientPullback Q).w
    have h := congrArg (prod.lift g b ≫ ·) eq
    simpa only [← Category.assoc, prod.lift_fst, comp_rightMultiplication] using h
  have he : gb ≫ sectionGraph L s =
      prod.lift gb (linePoint R (u * z)) := by
    apply L.trivializes.hom_ext
    · simp [Category.assoc, sectionGraph_fst]
    · rw [L.transition R g b z, ← hg]
      simp only [Category.assoc, sectionGraph_factor]
      rw [← Category.assoc gb, ← hgb, Category.assoc]
  simpa only [Category.assoc, prod.lift_snd] using congrArg (· ≫ prod.snd) he

private theorem descent_of_covariant (f : G.val.X ⟶ affineLine k) (hf : SchemeCovariant p χ f) :
    ∃ s : BundleSection L, Q.projection ≫ s.val =
      prod.lift (𝟙 G.val.X) f ≫ L.trivialization := by
  let w := prod.lift (𝟙 G.val.X) f ≫ L.trivialization
  have hw : w ≫ L.projection = Q.projection := by
    simp only [w, Category.assoc, ← L.trivializes.w, prod.lift_fst_assoc, Category.id_comp]
  have he :
      (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X) ≫ w =
      Specs.HomogeneousQuotient.rightMultiplication P.negative ≫ w := by
    apply GrassmannianCharts.hom_ext_on_affines
    intro R t
    let g := t ≫ prod.fst
    let b := t ≫ prod.snd
    let z := (linePointEquiv R).symm (g ≫ f)
    have hz : g ≫ f = linePoint R z := ((linePointEquiv R).apply_symm_apply _).symm
    have hb := hf R g b z hz
    have ht : t ≫ Specs.HomogeneousQuotient.rightMultiplication P.negative =
        g * (b ≫ P.negative.inclusion.hom.hom) := by
      have hh : t = prod.lift g b := by ext <;> simp [g, b]
      rw [hh, comp_rightMultiplication]
    rw [← Category.assoc t prod.fst w,
      ← Category.assoc t (Specs.HomogeneousQuotient.rightMultiplication P.negative) w, ht]
    simp only [w, ← Category.assoc, prod.comp_lift, Category.comp_id]
    change prod.lift g (g ≫ f) ≫ L.trivialization =
      prod.lift (g * (b ≫ P.negative.inclusion.hom.hom))
        ((g * (b ≫ P.negative.inclusion.hom.hom)) ≫ f) ≫ L.trivialization
    rw [hz, hb]
    exact (L.transition R g b z).symm
  letI := Q.flat
  letI := Q.surjective
  letI := Q.finitePresentation
  obtain ⟨s, hs⟩ := descends Q.projection w (fun T r t h ↦ by
    let l := (HomogeneousQuotient.quotientPullback Q).lift r t h
    calc
      r ≫ w = l ≫ prod.fst ≫ w := by simp [l]
      _ = l ≫ Specs.HomogeneousQuotient.rightMultiplication P.negative ≫ w := by rw [he]
      _ = t ≫ w := by simp [l])
  letI : Epi Q.projection := by
    letI : Epi Q.projection.left := inferInstance
    exact Over.epi_of_epi_left _
  refine ⟨⟨s, ?_⟩, hs⟩
  apply (cancel_epi Q.projection).mp
  rw [← Category.assoc, hs, hw, Category.comp_id]

/-- The equalizer for the quotient torsor identifies sections with regular
functions having the inverse-character covariance. -/
theorem sectionsAreCovariant : SectionsAreCovariant.{u} := by
  intro k _ G P Q a p χ L
  let F : BundleSection L → {f : G.val.X ⟶ affineLine k // SchemeCovariant p χ f} :=
    fun s ↦ ⟨sectionGraph L s ≫ prod.snd, sectionGraph_covariant L s⟩
  have hF (s : BundleSection L) :
      Q.projection ≫ s.val = prod.lift (𝟙 _) (F s).val ≫ L.trivialization := by
    change _ = prod.lift (𝟙 _) (sectionGraph L s ≫ prod.snd) ≫ L.trivialization
    rw [← sectionGraph_factor L s, ← sectionGraph_eq L s]
  refine ⟨Equiv.ofBijective F ⟨?_, ?_⟩, hF⟩
  · intro s t h
    apply Subtype.ext
    letI := Q.flat
    letI := Q.surjective
    letI := Q.finitePresentation
    letI : Epi Q.projection := by
      letI : Epi Q.projection.left := inferInstance
      exact Over.epi_of_epi_left _
    apply (cancel_epi Q.projection).mp
    rw [hF, hF, h]
  · intro ⟨f, hf⟩
    obtain ⟨s, hs⟩ := descent_of_covariant L f hf
    refine ⟨s, Subtype.ext ?_⟩
    have he : sectionGraph L s = prod.lift (𝟙 _) f := by
      apply L.trivializes.hom_ext
      · rw [sectionGraph_fst, prod.lift_fst]
      · rw [sectionGraph_factor, hs]
    change sectionGraph L s ≫ prod.snd = f
    rw [he, prod.lift_snd]

end Geometry

section Finiteness

open WithZero
open scoped Polynomial
open Specs.CharacterDescent (Character)
open Specs.QuotientEmbedding (Presentation)

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem extend_point_of_proper {Y : SchemeOver k} (hY : IsProper Y.hom)
    (R K : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] [IsFractionRing R K]
    (y : Points Y (CommAlgCat.of k K)) :
    ∃ y₀ : Points Y (CommAlgCat.of k R),
      mapPoints (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R K)) y₀ = y := by
  have h₀ : ValuativeCriterion Y.hom :=
    ((Iff.of_eq (congrArg (fun P : MorphismProperty Scheme.{u} ↦ P Y.hom)
      IsProper.eq_valuativeCriterion)).mp hY).1.1.1
  let S : ValuativeCommSq Y.hom :=
    { R := R
      K := K
      i₁ := y.left
      i₂ := ((testSpec k).obj (op (CommAlgCat.of k R))).hom
      commSq := ⟨by
        rw [Over.w y]
        change Spec.map (CommRingCat.ofHom (algebraMap k K)) =
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap k R))
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq k R K]⟩ }
  obtain ⟨t, ht, hw⟩ := (h₀.existence S).exists_lift
  exact ⟨Over.homMk t hw, Over.OverMorphism.ext ht⟩

private theorem chart_contains_local_point {R : Type u} [CommRing R] [Algebra k R]
    [IsLocalRing R] {X Y : SchemeOver k} (j : X ⟶ Y) (hj : IsOpenImmersion j.left)
    (y : Points Y (CommAlgCat.of k R)) (hy : y.left (IsLocalRing.closedPoint R) ∈ Set.range j.left) :
    ∃ x : Points X (CommAlgCat.of k R), x ≫ j = y := by
  have h : Set.range y.left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    change PrimeSpectrum R at x
    exact ((IsLocalRing.specializes_closedPoint (R := R) x).map y.left.continuous).mem_open
      j.left.isOpenMap.isOpen_range hy
  let l := IsOpenImmersion.lift j.left y.left h
  have hl : l ≫ j.left = y.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
  rw [← Over.w j, ← Category.assoc, hl, Over.w y]


variable {G : Specs.AffineAlgebraicGroup k} {P : OppositeBorelPair G}
  {p : BorelProjection P} {χ : Character P.torus.group}

private theorem bundleSections_bounded
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    (L : AssociatedBundle Q a p χ) (hQ : IsProper Q.scheme.hom)
    (R K : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] [IsFractionRing R K]
    (g : Points G.val.X (CommAlgCat.of k K)) :
    ∃ e : Kˣ, ∀ (s : BundleSection L) (f : G.val.X ⟶ affineLine k) (z : K),
      Q.projection ≫ s.val = prod.lift (𝟙 _) f ≫ L.trivialization →
      g ≫ f = linePoint (CommAlgCat.of k K) z →
      ∃ x : R, z = (e : K) * algebraMap R K x := by
  let R₀ := CommAlgCat.of k R
  let K₀ := CommAlgCat.of k K
  let i := (testSpec k).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R K)).op
  obtain ⟨y₀, hy₀⟩ := extend_point_of_proper hQ R K (g ≫ Q.projection)
  have hy₀' : i ≫ y₀ = g ≫ Q.projection := hy₀
  obtain ⟨U, j, t, hj, hjrange, hp, htrans⟩ :=
    L.charts (y₀.left (IsLocalRing.closedPoint R))
  obtain ⟨u₀, hu₀⟩ := chart_contains_local_point j hj y₀ hjrange
  let u := i ≫ u₀
  have hu : u ≫ j = g ≫ Q.projection := by rw [show u = i ≫ u₀ from rfl,
    Category.assoc, hu₀, hy₀']
  obtain ⟨e, he⟩ := htrans K₀ u g hu
  refine ⟨e, fun s f z hs hz ↦ ?_⟩
  have hw : u₀ ≫ j = (y₀ ≫ s.val) ≫ L.projection := by
    rw [hu₀, Category.assoc, s.property, Category.comp_id]
  let l := hp.lift u₀ (y₀ ≫ s.val) hw
  let x := (linePointEquiv R₀).symm (l ≫ prod.snd)
  have hx : l = prod.lift u₀ (linePoint R₀ x) := by
    apply prod.hom_ext
    · rw [prod.lift_fst, hp.lift_fst]
    · rw [prod.lift_snd, ← linePointEquiv_apply]
      exact ((linePointEquiv R₀).apply_symm_apply _).symm
  have hline : i ≫ linePoint R₀ x = linePoint K₀ (algebraMap R K x) :=
    linePoint_comp (R := R₀) (S := K₀) (IsScalarTower.toAlgHom k R K) x
  have h₁ : prod.lift u (linePoint K₀ (algebraMap R K x)) ≫ t =
      g ≫ Q.projection ≫ s.val := by
    rw [← hline, ← prod.comp_lift, ← hx, Category.assoc, hp.lift_snd,
      ← Category.assoc, hy₀', Category.assoc]
  have h₂ : prod.lift g (linePoint K₀ z) ≫ L.trivialization =
      g ≫ Q.projection ≫ s.val := by
    rw [← hz, hs, ← Category.assoc, prod.comp_lift, Category.comp_id]
  have h₃ := h₁.trans h₂.symm
  rw [he] at h₃
  have h₄ := L.trivializes.hom_ext (by simp : prod.lift g _ ≫ prod.fst =
    prod.lift g _ ≫ prod.fst) h₃
  refine ⟨x, (linePointEquiv K₀).injective ?_⟩
  simpa only [linePointEquiv_apply, prod.lift_snd] using (congrArg (· ≫ prod.snd) h₄).symm

variable (k : Type u) [Field k] (I : Type)

private abbrev ParameterField := FractionRing (MvPolynomial I k)

private abbrev RayField := RatFunc (ParameterField k I)

private def genericRayPolynomial : MvPolynomial I k →ₐ[k] Polynomial (ParameterField k I) :=
  MvPolynomial.aeval fun i ↦ Polynomial.C (algebraMap (MvPolynomial I k) (ParameterField k I) (MvPolynomial.X i)) *
    Polynomial.X

private theorem genericRayPolynomial_monomial (d : I →₀ ℕ) (r : k) :
    genericRayPolynomial k I (MvPolynomial.monomial d r) =
      Polynomial.C (algebraMap _ (ParameterField k I) (MvPolynomial.monomial d r)) *
        Polynomial.X ^ d.degree := by
  classical
  rw [genericRayPolynomial, MvPolynomial.aeval_monomial, Finsupp.prod]
  simp only [mul_pow, ← map_pow, Finset.prod_mul_distrib, ← map_prod]
  rw [← mul_assoc]
  have h : algebraMap k (Polynomial (ParameterField k I)) r =
      Polynomial.C (algebraMap k (ParameterField k I) r) := by
    rw [IsScalarTower.algebraMap_apply k (ParameterField k I)]
    rfl
  rw [h, ← map_mul, IsScalarTower.algebraMap_apply k (MvPolynomial I k) (ParameterField k I),
    ← map_mul, Finset.prod_pow_eq_pow_sum]
  change Polynomial.C (algebraMap (MvPolynomial I k) (ParameterField k I)
      (MvPolynomial.C r * d.prod (fun i j ↦ MvPolynomial.X i ^ j))) * Polynomial.X ^ d.degree = _
  rw [← MvPolynomial.monomial_eq]

private theorem genericRayPolynomial_coeff (p : MvPolynomial I k) (n : ℕ) :
    (genericRayPolynomial k I p).coeff n =
      algebraMap _ (ParameterField k I) (MvPolynomial.homogeneousComponent n p) := by
  classical
  let j : MvPolynomial I k →+* ParameterField k I := algebraMap _ _
  change (genericRayPolynomial k I p).coeff n = j (MvPolynomial.homogeneousComponent n p)
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : MvPolynomial.homogeneousComponent n (MvPolynomial.monomial d r) =
        if d.degree = n then MvPolynomial.monomial d r else 0 := by
      ext e
      rw [MvPolynomial.coeff_homogeneousComponent]
      by_cases he : e = d
      · subst e
        split_ifs <;> simp
      · by_cases hd : d.degree = n <;>
          simp [hd, MvPolynomial.coeff_monomial, Ne.symm he]
    rw [genericRayPolynomial_monomial, Polynomial.coeff_C_mul_X_pow, hm]
    by_cases hd : d.degree = n
    · simp only [hd, ite_true]
      rfl
    · simp only [hd, Ne.symm hd, ite_false, map_zero]
  | add p q hp hq =>
    have h₁ : genericRayPolynomial k I (p + q) =
        genericRayPolynomial k I p + genericRayPolynomial k I q :=
      (genericRayPolynomial k I).map_add p q
    have h₂ := (MvPolynomial.homogeneousComponent (σ := I) (R := k) n).map_add p q
    have h₃ : j (MvPolynomial.homogeneousComponent n p + MvPolynomial.homogeneousComponent n q) =
        j (MvPolynomial.homogeneousComponent n p) + j (MvPolynomial.homogeneousComponent n q) :=
      j.map_add' _ _
    rw [h₁, Polynomial.coeff_add, h₂, h₃, hp, hq]

private theorem totalDegree_le_rayDegree (p : MvPolynomial I k) :
    p.totalDegree ≤ (genericRayPolynomial k I p).natDegree := by
  classical
  apply Finset.sup_le
  intro d hd
  change d.degree ≤ _
  have hn : (MvPolynomial.homogeneousComponent d.degree p).coeff d ≠ 0 := by
    simpa [MvPolynomial.coeff_homogeneousComponent] using
      (MvPolynomial.mem_support_iff.mp hd)
  have hcomp : MvPolynomial.homogeneousComponent d.degree p ≠ 0 := by
    intro h
    simp [h] at hn
  apply Polynomial.le_natDegree_of_ne_zero
  rw [genericRayPolynomial_coeff, map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  exact hcomp

private def genericRay : MvPolynomial I k →ₐ[k] RayField k I :=
  (IsScalarTower.toAlgHom k (Polynomial (ParameterField k I)) (RayField k I)).comp
    (genericRayPolynomial k I)

private lemma genericRayPolynomial_ne_zero {p : MvPolynomial I k} (hp : p ≠ 0) :
    genericRayPolynomial k I p ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr (MvPolynomial.support_nonempty.mpr hp).ne_empty
  have he : (MvPolynomial.homogeneousComponent d.degree p).coeff d ≠ 0 := by
    simpa [MvPolynomial.coeff_homogeneousComponent] using (MvPolynomial.mem_support_iff.mp hd)
  intro hz
  have hc := genericRayPolynomial_coeff k I p d.degree
  rw [hz, Polynomial.coeff_zero, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at hc
  simp [hc] at he

open scoped Classical in
private theorem finite_of_boundedRay [Finite I] {W : Type u} [AddCommGroup W] [Module k W]
    (f : W →ₗ[k] MvPolynomial I k) (hf : Function.Injective f)
    (c : RayField k I) (hc : c ≠ 0)
    (hb : ∀ x : W, RatFunc.inftyValuation (ParameterField k I) (genericRay k I (f x)) ≤
      RatFunc.inftyValuation (ParameterField k I) c) :
    FiniteDimensional k W := by
  classical
  let N := c.intDegree.toNat
  have hmem (x : W) : f x ∈ MvPolynomial.restrictTotalDegree I k N := by
    apply (MvPolynomial.mem_restrictTotalDegree I N _).mpr
    by_cases h : f x = 0
    · simp [h]
    · have hx := hb x
      change RatFunc.inftyValuationDef (ParameterField k I) (algebraMap _ _
        (genericRayPolynomial k I (f x))) ≤ RatFunc.inftyValuationDef (ParameterField k I) c at hx
      rw [RatFunc.inftyValuation.polynomial _ (genericRayPolynomial_ne_zero k I h),
        RatFunc.inftyValuation_of_nonzero _ hc] at hx
      have hn := exp_le_exp.mp hx
      exact (totalDegree_le_rayDegree k I (f x)).trans (by omega)
  exact Module.Finite.of_injective (f.codRestrict _ hmem) (fun _ _ h ↦ hf (congrArg Subtype.val h))


end Finiteness

section BundleConstruction

open CategoryTheory.CartesianMonoidalCategory TopologicalSpace
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.QuotientEmbedding (Presentation)
open private descends from LinearAlgebraicGroups.Reductive.BorelProper
open private comp_rightMultiplication from LinearAlgebraicGroups.Flag.HomogeneousQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

variable {M : Specs.GroupScheme k} {H : Specs.ClosedSubgroup M}

private abbrev MultiplicativeCoordinates (k : Type u) [Field k] :=
  Specs.DiagonalizableGroups.groupAlgebra k Specs.DiagonalizableGroups.IntegerCharacters

private def torusCoordinate (k : Type u) [Field k] : GroupLike k (MultiplicativeCoordinates k) :=
  ⟨characterCoordinate (𝟙 (MultiplicativeCoordinates k)),
    characterCoordinate_groupLike (𝟙 (MultiplicativeCoordinates k))⟩

private def characterPoint (ψ : Character H.group) (R : TestAlgebra k)
    (b : Points H.group.X R) : MultiplicativeCoordinates k →ₐ[k] R :=
  (affinePointEquiv _ R).symm (b ≫ ψ.hom.hom)

private theorem characterPoint_eq (ψ : Character H.group) (R : TestAlgebra k)
    (b : Points H.group.X R) :
    affinePoint R (characterPoint ψ R b) = b ≫ ψ.hom.hom :=
  (affinePointEquiv _ R).apply_symm_apply _

private theorem affinePoint_map {R S : TestAlgebra k} (a : R ⟶ S) (f : A →ₐ[k] R) :
    mapPoints a (affinePoint R f) = affinePoint S (a.hom.comp f) := by
  change (testSpec k).map a.op ≫ (testSpec k).map (CommAlgCat.ofHom f).op =
    (testSpec k).map (CommAlgCat.ofHom (a.hom.comp f)).op
  rw [← Functor.map_comp]
  rfl

private theorem characterPoint_map (ψ : Character H.group) {R S : TestAlgebra k}
    (a : R ⟶ S) (b : Points H.group.X R) :
    characterPoint ψ S (mapPoints a b) = a.hom.comp (characterPoint ψ R b) := by
  apply (affinePointEquiv _ S).injective
  change affinePoint S (characterPoint ψ S (mapPoints a b)) =
    affinePoint S (a.hom.comp (characterPoint ψ R b))
  rw [characterPoint_eq, ← affinePoint_map, characterPoint_eq, Category.assoc]

private theorem characterPoint_mul (ψ : Character H.group) (R : TestAlgebra k)
    (b d : Points H.group.X R) :
    letI := convolutionGroup (MultiplicativeCoordinates k) R
    toConv (characterPoint ψ R (b * d)) =
      toConv (characterPoint ψ R b) * toConv (characterPoint ψ R d) := by
  letI := convolutionGroup (MultiplicativeCoordinates k) R
  apply (Spec.mapMulEquiv (R := k) (S := MultiplicativeCoordinates k) (T := R)).injective
  change affinePoint R (characterPoint ψ R (b * d)) =
    affinePoint R ((toConv (characterPoint ψ R b) * toConv (characterPoint ψ R d)).ofConv)
  rw [affinePoint_mul, characterPoint_eq, characterPoint_eq, characterPoint_eq, MonObj.mul_comp]

private def characterUnit (ψ : Character H.group) (R : TestAlgebra k)
    (b : Points H.group.X R) : Rˣ :=
  Units.map (characterPoint ψ R b).toMonoidHom (GroupLike.toUnits k (torusCoordinate k))

private theorem characterUnit_val (ψ : Character H.group) (R : TestAlgebra k)
    (b : Points H.group.X R) : (characterUnit ψ R b : R) = characterValue ψ R b := rfl

private theorem characterUnit_map (ψ : Character H.group) {R S : TestAlgebra k}
    (a : R ⟶ S) (b : Points H.group.X R) :
    (characterUnit ψ S (mapPoints a b) : S) = a.hom (characterUnit ψ R b) := by
  change characterPoint ψ S _ _ = _
  rw [characterPoint_map]
  rfl

private theorem characterUnit_mul (ψ : Character H.group) (R : TestAlgebra k)
    (b d : Points H.group.X R) :
    characterUnit ψ R (b * d) = characterUnit ψ R b * characterUnit ψ R d := by
  letI := convolutionGroup (MultiplicativeCoordinates k) R
  apply Units.ext
  change characterPoint ψ R (b * d) (torusCoordinate k : MultiplicativeCoordinates k) = _
  rw [← show (toConv (characterPoint ψ R (b * d))) (torusCoordinate k :
    MultiplicativeCoordinates k) = _ from rfl,
    characterPoint_mul, convolution_apply, (torusCoordinate k).2.comul_eq_tmul_self]
  simp [characterUnit, tensorPoint_tmul]

private def characterUnits (ψ : Character H.group) (R : TestAlgebra k) :
    Points H.group.X R →* Rˣ :=
  MonoidHom.mk' (characterUnit ψ R) (characterUnit_mul ψ R)

private abbrev lineValue (R : TestAlgebra k) (f : Points (affineLine k) R) : R :=
  (linePointEquiv R).symm f

@[simp] private theorem linePoint_lineValue (R : TestAlgebra k) (f : Points (affineLine k) R) :
    linePoint R (lineValue R f) = f := (linePointEquiv R).apply_symm_apply f

@[simp] private theorem lineValue_linePoint (R : TestAlgebra k) (z : R) :
    lineValue R (linePoint R z) = z := (linePointEquiv R).symm_apply_apply z

private theorem lineValue_map {R S : TestAlgebra k} (a : R ⟶ S)
    (f : Points (affineLine k) R) :
    lineValue S (mapPoints a f) = a.hom (lineValue R f) := by
  rw [← linePoint_lineValue R f, show mapPoints a (linePoint R (lineValue R f)) =
    linePoint S (a.hom (lineValue R f)) by exact linePoint_comp a.hom _, lineValue_linePoint,
    lineValue_linePoint]

/-- Multiply the line coordinate by the value of a character at a family of points. -/
private def scaleLine (ψ : Character H.group) {T : SchemeOver k}
    (b : T ⟶ H.group.X) (z : T ⟶ affineLine k) : T ⟶ affineLine k :=
  (GrassmannianCharts.affineProbesEquiv T _).symm
    { app := fun R ↦ ↾fun x ↦
        linePoint R ((characterUnit ψ R (x ≫ b) : R) * lineValue R (x ≫ z))
      naturality := by
        intro R S a
        apply ConcreteCategory.hom_ext
        intro x
        change Points T R at x
        symm
        change mapPoints a (linePoint R (_ * _)) =
          linePoint S (↑(characterUnit ψ S ((mapPoints a x) ≫ b)) *
            lineValue S ((mapPoints a x) ≫ z))
        rw [show mapPoints a (linePoint R
              ((characterUnit ψ R (x ≫ b) : R) * lineValue R (x ≫ z))) = _ from
            linePoint_comp a.hom _, map_mul]
        have h₁ : (mapPoints a x) ≫ b = mapPoints a (x ≫ b) := Category.assoc _ _ _
        have h₂ : (mapPoints a x) ≫ z = mapPoints a (x ≫ z) := Category.assoc _ _ _
        rw [h₁, h₂, characterUnit_map, lineValue_map] }

private theorem scaleLine_eval (ψ : Character H.group) {T : SchemeOver k}
    (b : T ⟶ H.group.X) (z : T ⟶ affineLine k) (R : TestAlgebra k) (x : Points T R) :
    x ≫ scaleLine ψ b z = linePoint R
      ((characterUnit ψ R (x ≫ b) : R) * lineValue R (x ≫ z)) := by
  rw [← GrassmannianCharts.affineProbesEquiv_apply]
  exact congrArg (fun α : pointsFunctor T ⟶ pointsFunctor (affineLine k) ↦ α.app R x)
    ((GrassmannianCharts.affineProbesEquiv T _).apply_symm_apply _)

@[simp] private theorem comp_scaleLine (ψ : Character H.group) {T S : SchemeOver k}
    (f : S ⟶ T) (b : T ⟶ H.group.X) (z : T ⟶ affineLine k) :
    f ≫ scaleLine ψ b z = scaleLine ψ (f ≫ b) (f ≫ z) := by
  apply GrassmannianCharts.hom_ext_on_affines
  intro R x
  simp only [← Category.assoc, scaleLine_eval]

@[simp] private theorem scaleLine_one (ψ : Character H.group) {T : SchemeOver k}
    (z : T ⟶ affineLine k) : scaleLine ψ 1 z = z := by
  apply GrassmannianCharts.hom_ext_on_affines
  intro R x
  have h := (characterUnits ψ R).map_one
  change characterUnit ψ R 1 = 1 at h
  rw [scaleLine_eval]; simp [h]

private theorem scaleLine_mul (ψ : Character H.group) {T : SchemeOver k}
    (b d : T ⟶ H.group.X) (z : T ⟶ affineLine k) :
    scaleLine ψ (b * d) z = scaleLine ψ b (scaleLine ψ d z) := by
  apply GrassmannianCharts.hom_ext_on_affines
  intro R x
  rw [scaleLine_eval, scaleLine_eval, scaleLine_eval]
  simp [MonObj.comp_mul, characterUnit_mul, mul_assoc]

variable (Q : Presentation H)

/-- The unique subgroup coordinate relating two lifts of the same point of the quotient. -/
private def torsorDifference {T : SchemeOver k} (g g' : T ⟶ M.X)
    (h : g ≫ Q.projection = g' ≫ Q.projection) : T ⟶ H.group.X :=
  (HomogeneousQuotient.quotientPullback Q).lift g g' h ≫ prod.snd

private theorem torsorDifference_value {T : SchemeOver k} (g g' : T ⟶ M.X)
    (h : g ≫ Q.projection = g' ≫ Q.projection) :
    torsorDifference Q g g' h ≫ H.inclusion.hom.hom = g⁻¹ * g' := by
  let l := (HomogeneousQuotient.quotientPullback Q).lift g g' h
  have h₁ : l ≫ prod.fst = g := IsPullback.lift_fst _ _ _ _
  have h₂ : g * (l ≫ prod.snd ≫ H.inclusion.hom.hom) = g' := by
    have hh := (HomogeneousQuotient.quotientPullback Q).lift_snd g g' h
    change l ≫ Specs.HomogeneousQuotient.rightMultiplication H = g' at hh
    simpa only [Specs.HomogeneousQuotient.rightMultiplication, MonObj.comp_mul,
      Category.assoc, ← Category.assoc l prod.fst, h₁] using hh
  change (l ≫ prod.snd) ≫ H.inclusion.hom.hom = _
  simpa only [Category.assoc, inv_mul_cancel_left] using congrArg (g⁻¹ * ·) h₂

private theorem torsorDifference_unique {T : SchemeOver k} (g g' : T ⟶ M.X)
    (h : g ≫ Q.projection = g' ≫ Q.projection) (b : T ⟶ H.group.X)
    (hb : g' = g * (b ≫ H.inclusion.hom.hom)) :
    torsorDifference Q g g' h = b := by
  haveI : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  letI : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono H.inclusion.hom.hom).mp
  rw [torsorDifference_value, hb, inv_mul_cancel_left]

private theorem torsorDifference_mul {T : SchemeOver k} (g₀ g₁ g₂ : T ⟶ M.X)
    (h₀₁ : g₀ ≫ Q.projection = g₁ ≫ Q.projection)
    (h₁₂ : g₁ ≫ Q.projection = g₂ ≫ Q.projection) :
    torsorDifference Q g₀ g₂ (h₀₁.trans h₁₂) =
      torsorDifference Q g₀ g₁ h₀₁ * torsorDifference Q g₁ g₂ h₁₂ := by
  apply torsorDifference_unique
  rw [MonObj.mul_comp, torsorDifference_value, torsorDifference_value]
  group

private theorem comp_torsorDifference {T S : SchemeOver k} (f : S ⟶ T) (g g' : T ⟶ M.X)
    (h : g ≫ Q.projection = g' ≫ Q.projection) :
    f ≫ torsorDifference Q g g' h =
      torsorDifference Q (f ≫ g) (f ≫ g') (by simp only [Category.assoc, h]) := by
  symm
  apply torsorDifference_unique
  simp only [Category.assoc, torsorDifference_value, ← MonObj.comp_mul, mul_inv_cancel_left]

private theorem quotient_right_mul {T : SchemeOver k} (g : T ⟶ M.X) (b : T ⟶ H.group.X) :
    (g * (b ≫ H.inclusion.hom.hom)) ≫ Q.projection = g ≫ Q.projection := by
  have h := congrArg (prod.lift g b ≫ ·) (HomogeneousQuotient.quotientPullback Q).w
  simpa only [← Category.assoc, comp_rightMultiplication, prod.lift_fst] using h.symm


private abbrev opened (Y : SchemeOver k) (U : Y.left.Opens) : SchemeOver k :=
  Over.mk (U.ι ≫ Y.hom)

private def openIncl (Y : SchemeOver k) (U : Y.left.Opens) : opened Y U ⟶ Y :=
  Over.homMk U.ι

private def openMap (Y : SchemeOver k) {U V : Y.left.Opens} (h : U ≤ V) :
    opened Y U ⟶ opened Y V :=
  Over.homMk (Y.left.homOfLE h) (by simp [← Category.assoc])

@[simp] private theorem openMap_incl (Y : SchemeOver k) {U V : Y.left.Opens} (h : U ≤ V) :
    openMap Y h ≫ openIncl Y V = openIncl Y U := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι _ h

private abbrev SplitOpen {X Y : SchemeOver k} (q : X ⟶ Y) :=
  {U : Y.left.Opens // ∃ s : opened Y U ⟶ X, s ≫ q = openIncl Y U}

private def localSection {X Y : SchemeOver k} {q : X ⟶ Y} (U : SplitOpen q) :
    opened Y U.val ⟶ X := U.property.choose

@[simp] private theorem localSection_proj {X Y : SchemeOver k} {q : X ⟶ Y}
    (U : SplitOpen q) : localSection U ≫ q = openIncl Y U.val :=
  U.property.choose_spec

private def splitOpenInter {X Y : SchemeOver k} {q : X ⟶ Y} (U V : SplitOpen q) : SplitOpen q :=
  ⟨U.val ⊓ V.val, openMap Y inf_le_left ≫ localSection U, by simp [Category.assoc]⟩

private abbrev CoversWithSections {X Y : SchemeOver k} (q : X ⟶ Y) : Prop :=
  ∀ y : Y.left, ∃ U : SplitOpen q, y ∈ U.val

private theorem coversWithSections_of_local {X Y : SchemeOver k} (q : X ⟶ Y)
    (h : ∀ y : Y.left, ∃ (U : SchemeOver k) (s : U ⟶ X),
      IsOpenImmersion (s ≫ q).left ∧ y ∈ Set.range (s ≫ q).left) :
    CoversWithSections q := by
  intro y
  obtain ⟨U, s, hOpen, hy⟩ := h y
  let f := s ≫ q
  let W := f.left.opensRange
  haveI : IsOpenImmersion f.left := hOpen
  let e := f.left.isoOpensRange.inv
  have he : e ≫ f.left = W.ι := Scheme.Hom.isoOpensRange_inv_comp _
  let t : opened Y W ⟶ U := Over.homMk e (by
    change e ≫ U.hom = W.ι ≫ Y.hom
    rw [← Over.w f, ← Category.assoc, he])
  refine ⟨⟨W, t ≫ s, ?_⟩, hy⟩
  apply Over.OverMorphism.ext
  exact he

private def splitCover {X Y : SchemeOver k} {q : X ⟶ Y} (h : CoversWithSections q) :
    Y.left.OpenCover :=
  Y.left.openCoverOfIsOpenCover (fun U : SplitOpen q ↦ U.val) <| .mk <| by
    ext y
    change y ∈ (⨆ U : SplitOpen q, U.val) ↔ y ∈ (⊤ : Y.left.Opens)
    simp only [Opens.mem_iSup, Opens.mem_top, iff_true]
    exact h y

private instance splitCover_category {X Y : SchemeOver k} {q : X ⟶ Y}
    (h : CoversWithSections q) : Category.{u} (splitCover h).I₀ :=
  inferInstanceAs (Category.{u} (SplitOpen q))

private instance splitCover_thin {X Y : SchemeOver k} {q : X ⟶ Y}
    (h : CoversWithSections q) : Quiver.IsThin (splitCover h).I₀ := by
  change Quiver.IsThin (SplitOpen q)
  infer_instance

private instance splitCover_directed {X Y : SchemeOver k} {q : X ⟶ Y} (h : CoversWithSections q) :
    (splitCover h).LocallyDirected where
  trans f := Y.left.homOfLE (show _ ≤ _ from leOfHom f)
  trans_id U := Scheme.homOfLE_rfl _ _
  trans_comp f g := (Scheme.homOfLE_homOfLE _ (leOfHom f) (leOfHom g)).symm
  w f := Scheme.homOfLE_ι _ (leOfHom f)
  directed {i j} x := by
    let K := splitOpenInter i j
    have hi : K ≤ i := show K.val ≤ i.val from inf_le_left
    have hj : K ≤ j := show K.val ≤ j.val from inf_le_right
    let pb := isPullback_opens_inf i.val j.val
    refine ⟨K, hi.hom, hj.hom, pb.isoPullback.inv x, ?_⟩
    change pb.isoPullback.hom (pb.isoPullback.inv x) = x
    simp
  property_trans f := by
    change IsOpenImmersion (Y.left.homOfLE (show _ ≤ _ from leOfHom f))
    infer_instance

variable (ψ : Character H.group)

private theorem scaleLine_inv (T : SchemeOver k) (b : T ⟶ H.group.X) (z : T ⟶ affineLine k) :
    scaleLine ψ b⁻¹ (scaleLine ψ b z) = z := by
  rw [← scaleLine_mul, inv_mul_cancel, scaleLine_one]

private theorem scaleLine_inv' (T : SchemeOver k) (b : T ⟶ H.group.X) (z : T ⟶ affineLine k) :
    scaleLine ψ b (scaleLine ψ b⁻¹ z) = z := by
  rw [← scaleLine_mul, mul_inv_cancel, scaleLine_one]

private def twistedProductMap {U V : SchemeOver k} (f : U ⟶ V) (b : U ⟶ H.group.X) :
    U ⨯ affineLine k ⟶ V ⨯ affineLine k :=
  prod.lift (prod.fst ≫ f) (scaleLine ψ (prod.fst ≫ b) prod.snd)

private theorem twistedProduct_pullback {U V : SchemeOver k} (f : U ⟶ V) (b : U ⟶ H.group.X) :
    IsPullback prod.fst (twistedProductMap ψ f b) f prod.fst := by
  have hw : prod.fst ≫ f = twistedProductMap ψ f b ≫ prod.fst := by simp [twistedProductMap]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun a ↦ prod.lift a.fst (scaleLine ψ (a.fst ≫ b)⁻¹ (a.snd ≫ prod.snd)))
    (fun _ ↦ prod.lift_fst _ _) (fun a ↦ ?_) (fun a m hm₁ hm₂ ↦ ?_))
  · apply prod.hom_ext
    · simpa only [Category.assoc, twistedProductMap, prod.lift_fst, prod.lift_fst_assoc] using a.condition
    · simp [twistedProductMap, ← Category.assoc, comp_scaleLine, scaleLine_inv']
  · apply prod.hom_ext
    · rwa [prod.lift_fst]
    · have he := congrArg (· ≫ prod.snd) hm₂
      rw [Category.assoc, twistedProductMap, prod.lift_snd, comp_scaleLine,
        ← Category.assoc m prod.fst, hm₁] at he
      rw [prod.lift_snd, ← he, scaleLine_inv]

private abbrev FlagOpen (Q : Presentation H) := SplitOpen Q.projection

private def transitionFactor (Q : Presentation H) {U V : FlagOpen Q} (h : U ≤ V) :
    opened Q.scheme U.val ⟶ H.group.X :=
  torsorDifference Q (openMap Q.scheme h ≫ localSection V) (localSection U)
    (by simp [Category.assoc])

private def bundleTransition (Q : Presentation H) {U V : FlagOpen Q} (f : U ⟶ V) :
    opened Q.scheme U.val ⨯ affineLine k ⟶ opened Q.scheme V.val ⨯ affineLine k :=
  twistedProductMap ψ (openMap Q.scheme (leOfHom f)) (transitionFactor Q (leOfHom f))

private theorem transitionFactor_value (Q : Presentation H) {U V : FlagOpen Q} (h : U ≤ V) :
    transitionFactor Q h ≫ H.inclusion.hom.hom =
      (openMap Q.scheme h ≫ localSection V)⁻¹ * localSection U :=
  torsorDifference_value _ _ _ _

private theorem bundleTransition_id (Q : Presentation H) (U : FlagOpen Q) :
    bundleTransition ψ Q (𝟙 U) = 𝟙 _ := by
  have hd : transitionFactor Q (leOfHom (𝟙 U)) = 1 := by
    apply torsorDifference_unique
    have hd : openMap Q.scheme (leOfHom (𝟙 U)) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      exact Scheme.homOfLE_rfl _ _
    simp [hd]
  have he : openMap Q.scheme (leOfHom (𝟙 U)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Scheme.homOfLE_rfl _ _
  apply prod.hom_ext <;> simp [bundleTransition, twistedProductMap, hd, he]

private theorem openMap_comp (Y : SchemeOver k) {U V W : Y.left.Opens} (f : U ≤ V) (g : V ≤ W) :
    openMap Y (f.trans g) = openMap Y f ≫ openMap Y g := by
  apply Over.OverMorphism.ext
  exact (Scheme.homOfLE_homOfLE _ f g).symm

private theorem transitionFactor_comp (Q : Presentation H) {U V W : FlagOpen Q}
    (f : U ≤ V) (g : V ≤ W) :
    transitionFactor Q (f.trans g) =
      (openMap Q.scheme f ≫ transitionFactor Q g) * transitionFactor Q f := by
  haveI : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  letI : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono H.inclusion.hom.hom).mp
  rw [transitionFactor_value, MonObj.mul_comp, Category.assoc, transitionFactor_value,
    transitionFactor_value, openMap_comp Q.scheme f g]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
  group

private theorem bundleTransition_comp (Q : Presentation H) {U V W : FlagOpen Q}
    (f : U ⟶ V) (g : V ⟶ W) :
    bundleTransition ψ Q (f ≫ g) = bundleTransition ψ Q f ≫ bundleTransition ψ Q g := by
  simp only [bundleTransition, twistedProductMap]
  rw [openMap_comp Q.scheme (leOfHom f) (leOfHom g),
    transitionFactor_comp Q (leOfHom f) (leOfHom g)]
  apply prod.hom_ext
  · simp [Category.assoc]
  · simp only [Category.assoc, prod.lift_snd, comp_scaleLine, prod.lift_fst_assoc,
      MonObj.comp_mul, scaleLine_mul]

private def bundleGluing (h : CoversWithSections Q.projection) :
    Scheme.Cover.RelativeGluingData (splitCover h) where
  functor :=
    { obj := fun U ↦ (opened Q.scheme U.val ⨯ affineLine k).left
      map := fun f ↦ (bundleTransition ψ Q f).left
      map_id := fun U ↦ congrArg Over.Hom.left (bundleTransition_id ψ Q U)
      map_comp := fun f g ↦ congrArg Over.Hom.left (bundleTransition_comp ψ Q f g) }
  natTrans :=
    { app := fun U ↦ (prod.fst : opened Q.scheme U.val ⨯ affineLine k ⟶ _).left
      naturality := by
        intro U V f
        exact congrArg Over.Hom.left ((twistedProduct_pullback ψ (openMap _ (leOfHom f))
          (transitionFactor Q (leOfHom f))).w.symm) }
  equifibered := fun _ _ f ↦ ((twistedProduct_pullback ψ (openMap _ (leOfHom f))
    (transitionFactor Q (leOfHom f))).map (Over.forget _)).flip

private def gluedBundle (h : CoversWithSections Q.projection) : SchemeOver k :=
  Over.mk ((bundleGluing Q ψ h).toBase ≫ Q.scheme.hom)

private def gluedProjection (h : CoversWithSections Q.projection) :
    gluedBundle Q ψ h ⟶ Q.scheme :=
  Over.homMk (bundleGluing Q ψ h).toBase

private def gluedChart (h : CoversWithSections Q.projection) (U : FlagOpen Q) :
    opened Q.scheme U.val ⨯ affineLine k ⟶ gluedBundle Q ψ h := by
  refine Over.homMk (colimit.ι (bundleGluing Q ψ h).functor U) ?_
  change _ ≫ ((bundleGluing Q ψ h).toBase ≫ Q.scheme.hom) = _
  rw [← Category.assoc, Scheme.Cover.RelativeGluingData.ι_toBase, Category.assoc]
  exact Over.w (prod.fst : opened Q.scheme U.val ⨯ affineLine k ⟶ _)

private theorem gluedChart_pullback (h : CoversWithSections Q.projection) (U : FlagOpen Q) :
    IsPullback prod.fst (gluedChart Q ψ h U) (openIncl Q.scheme U.val) (gluedProjection Q ψ h) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of k)))
  exact (bundleGluing Q ψ h).isPullback_natTrans_ι_toBase U

private theorem gluedChart_transition (h : CoversWithSections Q.projection) {U V : FlagOpen Q}
    (f : U ⟶ V) : bundleTransition ψ Q f ≫ gluedChart Q ψ h V = gluedChart Q ψ h U := by
  apply Over.OverMorphism.ext
  exact colimit.w (bundleGluing Q ψ h).functor f

private def bundleCoordinate {T : SchemeOver k} (U : FlagOpen Q)
    (u : T ⟶ opened Q.scheme U.val) (g : T ⟶ M.X) (z : T ⟶ affineLine k)
    (e : u ≫ openIncl Q.scheme U.val = g ≫ Q.projection) :
    T ⟶ opened Q.scheme U.val ⨯ affineLine k :=
  prod.lift u (scaleLine ψ (torsorDifference Q (u ≫ localSection U) g
    (by simpa only [Category.assoc, localSection_proj] using e)) z)

private theorem bundleCoordinate_comp {T S : SchemeOver k} (U : FlagOpen Q)
    (u : T ⟶ opened Q.scheme U.val) (g : T ⟶ M.X) (z : T ⟶ affineLine k)
    (e : u ≫ openIncl Q.scheme U.val = g ≫ Q.projection) (f : S ⟶ T) :
    f ≫ bundleCoordinate Q ψ U u g z e =
      bundleCoordinate Q ψ U (f ≫ u) (f ≫ g) (f ≫ z) (by simp only [Category.assoc, e]) := by
  simp only [bundleCoordinate, prod.comp_lift, comp_scaleLine, comp_torsorDifference, Category.assoc]

private theorem bundleCoordinate_congr {T : SchemeOver k} (U : FlagOpen Q)
    {u u' : T ⟶ opened Q.scheme U.val} {g g' : T ⟶ M.X} {z z' : T ⟶ affineLine k}
    {e : u ≫ openIncl Q.scheme U.val = g ≫ Q.projection}
    {e' : u' ≫ openIncl Q.scheme U.val = g' ≫ Q.projection}
    (hu : u = u') (hg : g = g') (hz : z = z') :
    bundleCoordinate Q ψ U u g z e = bundleCoordinate Q ψ U u' g' z' e' := by
  subst u' g' z'
  rfl

private theorem bundleCoordinate_transition {T : SchemeOver k} {U V : FlagOpen Q}
    (f : U ⟶ V) (u : T ⟶ opened Q.scheme U.val) (g : T ⟶ M.X) (z : T ⟶ affineLine k)
    (e : u ≫ openIncl Q.scheme U.val = g ≫ Q.projection) :
    bundleCoordinate Q ψ U u g z e ≫ bundleTransition ψ Q f =
      bundleCoordinate Q ψ V (u ≫ openMap Q.scheme (leOfHom f)) g z
        (by simpa only [Category.assoc, openMap_incl] using e) := by
  let s := u ≫ localSection U
  let t := (u ≫ openMap Q.scheme (leOfHom f)) ≫ localSection V
  have hts : t ≫ Q.projection = s ≫ Q.projection := by simp [s, t, Category.assoc]
  have hsg : s ≫ Q.projection = g ≫ Q.projection := by
    simpa only [s, Category.assoc, localSection_proj] using e
  have hm := torsorDifference_mul Q t s g hts hsg
  have hmap : u ≫ transitionFactor Q (leOfHom f) = torsorDifference Q t s hts := by
    simp only [transitionFactor, comp_torsorDifference, s, t, Category.assoc]
  apply prod.hom_ext
  · simp [bundleCoordinate, bundleTransition, twistedProductMap]
  · simp only [bundleCoordinate, bundleTransition, twistedProductMap, Category.assoc,
      prod.lift_snd, comp_scaleLine, prod.lift_fst_assoc]
    rw [hmap, ← scaleLine_mul]
    exact congrArg (fun b ↦ scaleLine ψ b z) hm.symm

private def asOver {S : Scheme.{u}} {Y : SchemeOver k} (f : S ⟶ Y.left) : SchemeOver k :=
  Over.mk (f ≫ Y.hom)

private def asOverIncl {S : Scheme.{u}} {Y : SchemeOver k} (f : S ⟶ Y.left) : asOver f ⟶ Y :=
  Over.homMk f

private abbrev PullbackCover {T : SchemeOver k} (h : CoversWithSections Q.projection)
    (p : T ⟶ Q.scheme) : T.left.OpenCover :=
  (splitCover h).pullback₁ p.left

private def coverPiece {T : SchemeOver k} (h : CoversWithSections Q.projection) (p : T ⟶ Q.scheme)
    (U : FlagOpen Q) : SchemeOver k :=
  asOver ((PullbackCover Q h p).f U)

private def coverPieceIncl {T : SchemeOver k} (h : CoversWithSections Q.projection) (p : T ⟶ Q.scheme)
    (U : FlagOpen Q) : coverPiece Q h p U ⟶ T :=
  asOverIncl ((PullbackCover Q h p).f U)

private def coverPieceOpen {T : SchemeOver k} (h : CoversWithSections Q.projection) (p : T ⟶ Q.scheme)
    (U : FlagOpen Q) : coverPiece Q h p U ⟶ opened Q.scheme U.val :=
  Over.homMk (pullback.snd p.left U.val.ι) (by
    change pullback.snd p.left U.val.ι ≫ (U.val.ι ≫ Q.scheme.hom) =
      pullback.fst p.left U.val.ι ≫ T.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w])

private theorem coverPiece_pullback {T : SchemeOver k}
    (h : CoversWithSections Q.projection) (p : T ⟶ Q.scheme) (U : FlagOpen Q) :
    IsPullback (coverPieceIncl Q h p U) (coverPieceOpen Q h p U) p (openIncl Q.scheme U.val) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of k)))
  exact IsPullback.of_hasPullback p.left U.val.ι

private def coverPieceMap {T : SchemeOver k}
    (h : CoversWithSections Q.projection) (p : T ⟶ Q.scheme) {U V : FlagOpen Q} (f : U ⟶ V) :
    coverPiece Q h p U ⟶ coverPiece Q h p V :=
  Over.homMk ((PullbackCover Q h p).trans f) (by
    change _ ≫ (((PullbackCover Q h p).f V) ≫ T.hom) = _
    rw [← Category.assoc, Scheme.Cover.trans_map]
    rfl)

private theorem coverPieceMap_incl {T : SchemeOver k}
    (h : CoversWithSections Q.projection) (p : T ⟶ Q.scheme) {U V : FlagOpen Q} (f : U ⟶ V) :
    coverPieceMap Q h p f ≫ coverPieceIncl Q h p V = coverPieceIncl Q h p U := by
  apply Over.OverMorphism.ext
  exact Scheme.Cover.trans_map (PullbackCover Q h p) f

private theorem coverPieceMap_open {T : SchemeOver k}
    (h : CoversWithSections Q.projection) (p : T ⟶ Q.scheme) {U V : FlagOpen Q} (f : U ⟶ V) :
    coverPieceMap Q h p f ≫ coverPieceOpen Q h p V =
      coverPieceOpen Q h p U ≫ openMap Q.scheme (leOfHom f) := by
  haveI : Mono (openIncl Q.scheme V.val).left := inferInstanceAs (Mono V.val.ι)
  letI : Mono (openIncl Q.scheme V.val) := Over.mono_of_mono_left _
  apply (cancel_mono (openIncl Q.scheme V.val)).mp
  rw [Category.assoc, ← (coverPiece_pullback Q h p V).w, ← Category.assoc,
    coverPieceMap_incl, Category.assoc, openMap_incl, (coverPiece_pullback Q h p U).w]

private theorem compat_openCover {T Y : SchemeOver k} {p : T ⟶ Q.scheme}
    (h : CoversWithSections Q.projection) (g : ∀ U, coverPiece Q h p U ⟶ Y)
    (hg : ∀ {U V}, ∀ f : U ⟶ V, coverPieceMap Q h p f ≫ g V = g U) :
    ∃ descended : T ⟶ Y, ∀ U, coverPieceIncl Q h p U ≫ descended = g U := by
  let C := PullbackCover Q h p
  have he : ∀ {i j : C.I₀} (f : i ⟶ j), C.trans f ≫ (g j).left = (g i).left :=
    fun f ↦ congrArg Over.Hom.left (hg f)
  have hw : ∀ i : C.I₀, (g i).left ≫ Y.hom = C.f i ≫ T.hom := fun i ↦ Over.w (g i)
  let descended := C.glueMorphismsOverOfLocallyDirected (fun i ↦ (g i).left) he hw
  refine ⟨descended, fun i ↦ Over.OverMorphism.ext ?_⟩
  exact C.map_glueMorphismsOverOfLocallyDirected_left _ _ _ i

private abbrev productProjection (Q : Presentation H) :
    M.X ⨯ affineLine k ⟶ Q.scheme :=
  prod.fst ≫ Q.projection

private theorem exists_bundleTrivialization (h : CoversWithSections Q.projection) :
    ∃ τ : M.X ⨯ affineLine k ⟶ gluedBundle Q ψ h,
      ∀ (T : SchemeOver k) (U : FlagOpen Q) (u : T ⟶ opened Q.scheme U.val)
        (g : T ⟶ M.X) (z : T ⟶ affineLine k)
        (e : u ≫ openIncl Q.scheme U.val = g ≫ Q.projection),
        prod.lift g z ≫ τ = bundleCoordinate Q ψ U u g z e ≫ gluedChart Q ψ h U := by
  let p := productProjection Q
  let i (U) := coverPieceIncl Q h p U
  let j (U) := coverPieceOpen Q h p U
  let hl (U) : j U ≫ openIncl Q.scheme U.val = (i U ≫ prod.fst) ≫ Q.projection :=
    by simpa only [Category.assoc] using (coverPiece_pullback Q h p U).w.symm
  let r (U : FlagOpen Q) := bundleCoordinate Q ψ U (j U) (i U ≫ prod.fst) (i U ≫ prod.snd) (hl U)
  have hc {U V : FlagOpen Q} (f : U ⟶ V) :
      coverPieceMap Q h p f ≫ r V = r U ≫ bundleTransition ψ Q f := by
    calc
      _ = bundleCoordinate Q ψ V (coverPieceMap Q h p f ≫ j V)
          (coverPieceMap Q h p f ≫ (i V ≫ prod.fst))
          (coverPieceMap Q h p f ≫ (i V ≫ prod.snd)) _ :=
        bundleCoordinate_comp Q ψ V _ _ _ _ _
      _ = bundleCoordinate Q ψ V (j U ≫ openMap Q.scheme (leOfHom f))
          (i U ≫ prod.fst) (i U ≫ prod.snd) _ := by
        apply bundleCoordinate_congr
        · exact coverPieceMap_open Q h p f
        · rw [← Category.assoc, show coverPieceMap Q h p f ≫ i V = i U from
            coverPieceMap_incl Q h p f]
        · rw [← Category.assoc, show coverPieceMap Q h p f ≫ i V = i U from
            coverPieceMap_incl Q h p f]
      _ = _ := (bundleCoordinate_transition Q ψ f _ _ _ (hl U)).symm
  obtain ⟨τ, hτ⟩ := compat_openCover Q h (fun U ↦ r U ≫ gluedChart Q ψ h U)
    (fun f ↦ by rw [← Category.assoc, hc f, Category.assoc, gluedChart_transition])
  refine ⟨τ, fun T U u g z e ↦ ?_⟩
  have he : prod.lift g z ≫ p = u ≫ openIncl Q.scheme U.val := by simp [p, e]
  let b := (coverPiece_pullback Q h p U).lift (prod.lift g z) u he
  have hi : b ≫ i U = prod.lift g z := IsPullback.lift_fst _ _ _ _
  have hj : b ≫ j U = u := IsPullback.lift_snd _ _ _ _
  rw [← hi, Category.assoc, hτ U, ← Category.assoc, show r U = _ from rfl, bundleCoordinate_comp]
  congr 1
  apply bundleCoordinate_congr
  · exact hj
  · rw [← Category.assoc, hi, prod.lift_fst]
  · rw [← Category.assoc, hi, prod.lift_snd]

private theorem coverPiece_hom_ext {T Y : SchemeOver k} (h : CoversWithSections Q.projection)
    (p : T ⟶ Q.scheme) {f g : T ⟶ Y}
    (he : ∀ U, coverPieceIncl Q h p U ≫ f = coverPieceIncl Q h p U ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  exact (PullbackCover Q h p).hom_ext _ _ (fun U ↦ congrArg Over.Hom.left (he U))

variable {h : CoversWithSections Q.projection}
  {τ : M.X ⨯ affineLine k ⟶ gluedBundle Q ψ h}

private abbrev HasBundleCoordinates (τ : M.X ⨯ affineLine k ⟶ gluedBundle Q ψ h) : Prop :=
  ∀ (T : SchemeOver k) (U : FlagOpen Q) (u : T ⟶ opened Q.scheme U.val)
    (g : T ⟶ M.X) (z : T ⟶ affineLine k)
    (e : u ≫ openIncl Q.scheme U.val = g ≫ Q.projection),
    prod.lift g z ≫ τ = bundleCoordinate Q ψ U u g z e ≫ gluedChart Q ψ h U

private theorem bundleTrivialization_pullback (hτ : HasBundleCoordinates Q ψ τ) :
    IsPullback prod.fst τ Q.projection (gluedProjection Q ψ h) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of k)))
  refine Scheme.isPullback_of_openCover _ _ _ _ (PullbackCover Q h Q.projection) fun U ↦ ?_
  let i := coverPieceIncl Q h Q.projection U
  let u := coverPieceOpen Q h Q.projection U
  have he : u ≫ openIncl Q.scheme U.val = i ≫ Q.projection :=
    (coverPiece_pullback Q h Q.projection U).w.symm
  let b := torsorDifference Q (u ≫ localSection U) i (by simpa only [Category.assoc, localSection_proj] using he)
  let m := twistedProductMap ψ u b
  let l := prod.map i (𝟙 (affineLine k))
  have hm : l ≫ τ = m ≫ gluedChart Q ψ h U := by
    have := hτ _ U (prod.fst ≫ u) (prod.fst ≫ i) prod.snd (by simp only [Category.assoc, he])
    have hl : l = prod.lift (prod.fst ≫ i) prod.snd := by apply prod.hom_ext <;> simp [l]
    have hb := comp_torsorDifference Q
      (prod.fst : coverPiece Q h Q.projection U ⨯ affineLine k ⟶ _)
      (u ≫ localSection U) i (by simpa only [Category.assoc, localSection_proj] using he)
    simpa only [hl, bundleCoordinate, m, twistedProductMap, b, hb, Category.assoc] using this
  have hQ := (twistedProduct_pullback ψ u b).paste_vert (gluedChart_pullback Q ψ h U)
  have hlocal : IsPullback (prod.fst : coverPiece Q h Q.projection U ⨯ affineLine k ⟶ _) (l ≫ τ)
      (i ≫ Q.projection) (gluedProjection Q ψ h) := by
    rw [hm, ← he]
    exact hQ
  let F := Over.forget (Spec (CommRingCat.of k))
  let e := ((IsPullback.of_prod_fst_with_id i (affineLine k)).flip.map F).isoPullback.symm
  refine (hlocal.map F).of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    exact ((IsPullback.of_prod_fst_with_id i (affineLine k)).flip.map F).isoPullback_inv_snd
  · simp only [Iso.refl_hom, Category.comp_id]
    change e.hom ≫ (l.left ≫ τ.left) = pullback.fst _ i.left ≫ τ.left
    rw [← Category.assoc]
    exact congrArg (· ≫ τ.left)
      (((IsPullback.of_prod_fst_with_id i (affineLine k)).flip.map F).isoPullback_inv_fst)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

private theorem bundleCoordinate_right {T : SchemeOver k} (U : FlagOpen Q)
    (u : T ⟶ opened Q.scheme U.val) (g : T ⟶ M.X) (z : T ⟶ affineLine k)
    (e : u ≫ openIncl Q.scheme U.val = g ≫ Q.projection) (b : T ⟶ H.group.X) :
    bundleCoordinate Q ψ U u (g * (b ≫ H.inclusion.hom.hom)) (scaleLine ψ b⁻¹ z)
        (e.trans (quotient_right_mul Q g b).symm) =
      bundleCoordinate Q ψ U u g z e := by
  let s := u ≫ localSection U
  have hs : s ≫ Q.projection = g ≫ Q.projection := by simpa [s, Category.assoc] using e
  have hb := torsorDifference_mul Q s g (g * (b ≫ H.inclusion.hom.hom)) hs (quotient_right_mul Q g b).symm
  rw [torsorDifference_unique Q g _ _ b rfl] at hb
  apply prod.hom_ext
  · simp [bundleCoordinate]
  · simp only [bundleCoordinate, prod.lift_snd]
    rw [hb, scaleLine_mul, scaleLine_inv']

private theorem bundleTrivialization_right (hτ : HasBundleCoordinates Q ψ τ) {T : SchemeOver k}
    (g : T ⟶ M.X) (b : T ⟶ H.group.X) (z : T ⟶ affineLine k) :
    prod.lift (g * (b ≫ H.inclusion.hom.hom)) (scaleLine ψ b⁻¹ z) ≫ τ =
      prod.lift g z ≫ τ := by
  apply coverPiece_hom_ext Q h (g ≫ Q.projection)
  intro U
  let i := coverPieceIncl Q h (g ≫ Q.projection) U
  let u := coverPieceOpen Q h (g ≫ Q.projection) U
  have he : u ≫ openIncl Q.scheme U.val = (i ≫ g) ≫ Q.projection := by
    simpa only [Category.assoc] using (coverPiece_pullback Q h (g ≫ Q.projection) U).w.symm
  change i ≫ _ = i ≫ _
  simp only [← Category.assoc, prod.comp_lift, MonObj.comp_mul, comp_scaleLine, GrpObj.comp_inv]
  have hr := hτ _ U u ((i ≫ g) * ((i ≫ b) ≫ H.inclusion.hom.hom))
    (scaleLine ψ (i ≫ b)⁻¹ (i ≫ z))
    (he.trans (quotient_right_mul Q (i ≫ g) (i ≫ b)).symm)
  rw [bundleCoordinate_right Q ψ U u (i ≫ g) (i ≫ z) he (i ≫ b)] at hr
  exact hr.trans (hτ _ U u (i ≫ g) (i ≫ z) he).symm

private theorem gluedChart_coordinate (hτ : HasBundleCoordinates Q ψ τ)
    (U : FlagOpen Q) (R : TestAlgebra k) (u : Points (opened Q.scheme U.val) R) (g : Points M.X R)
    (e : u ≫ openIncl Q.scheme U.val = g ≫ Q.projection) :
    ∃ a : Rˣ, ∀ z : R,
      prod.lift u (linePoint R z) ≫ gluedChart Q ψ h U =
        prod.lift g (linePoint R ((a : R) * z)) ≫ τ := by
  let b := torsorDifference Q (u ≫ localSection U) g
    (by simpa only [Category.assoc, localSection_proj] using e)
  let a := (characterUnit ψ R b)⁻¹
  refine ⟨a, fun z ↦ ?_⟩
  rw [hτ _ U u g _ e]
  change prod.lift u (linePoint R z) ≫ _ =
    prod.lift u (scaleLine ψ b (linePoint R ((a : R) * z))) ≫ _
  have ev := scaleLine_eval ψ b (linePoint R ((a : R) * z)) R
    (𝟙 ((testSpec k).obj (op R)))
  have hscale : scaleLine ψ b (linePoint R ((a : R) * z)) = linePoint R z := by
    simpa only [a, Category.id_comp, lineValue_linePoint, ← mul_assoc, Units.mul_inv, one_mul] using ev
  rw [hscale]

private theorem whiskerLeft_pullback (X : SchemeOver k) {Y Z : SchemeOver k} (f : Y ⟶ Z) :
    IsPullback (snd X Y) (X ◁ f) f (snd X Z) := by
  have hw : snd X Y ≫ f = (X ◁ f) ≫ snd X Z := by simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun c ↦ lift (c.snd ≫ fst X Z) c.fst) (fun _ ↦ lift_snd _ _) (fun c ↦ ?_)
    (fun c m hm hn ↦ ?_))
  · apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using c.condition
  · apply CartesianMonoidalCategory.hom_ext
    · have he := congrArg (· ≫ fst X Z) hn
      simpa using he
    · simpa using hm

private theorem fppf_whiskerLeft (X : SchemeOver k) {Y Z : SchemeOver k} (f : Y ⟶ Z)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left] :
    Flat (X ◁ f).left ∧ Surjective (X ◁ f).left ∧ LocallyOfFinitePresentation (X ◁ f).left := by
  have hp := (whiskerLeft_pullback X f).map (Over.forget (Spec (CommRingCat.of k)))
  exact ⟨MorphismProperty.of_isPullback hp (‹Flat f.left›),
    MorphismProperty.of_isPullback hp (‹Surjective f.left›),
    MorphismProperty.of_isPullback hp (‹LocallyOfFinitePresentation f.left›)⟩

private theorem fppf_epi {X Y : SchemeOver k} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left] :
    Epi f := Over.epi_of_epi_left _

open private modObjOfSchemeAction from LinearAlgebraicGroups.Flag.SmoothOrbit

/-- Left multiplication on the group factor descends through the character relation. -/
private theorem bundleAction {L : SchemeOver k} {π : L ⟶ Q.scheme}
    (a : ModObj M.X Q.scheme)
    (ha : μ[M.X] ≫ Q.projection = (𝟙 M.X ⊗ₘ Q.projection) ≫ a.smul)
    (τ : M.X ⨯ affineLine k ⟶ L)
    (hp : IsPullback prod.fst τ Q.projection π)
    (hτ : ∀ {T : SchemeOver k} (g : T ⟶ M.X) (b : T ⟶ H.group.X) (z : T ⟶ affineLine k),
      prod.lift (g * (b ≫ H.inclusion.hom.hom)) (scaleLine ψ b⁻¹ z) ≫ τ =
        prod.lift g z ≫ τ) :
    ∃ aL : ModObj M.X L,
      aL.smul ≫ π = (𝟙 M.X ⊗ₘ π) ≫ a.smul ∧
      ∀ (T : SchemeOver k) (h g : T ⟶ M.X) (z : T ⟶ affineLine k),
        lift h (prod.lift g z ≫ τ) ≫ aL.smul = prod.lift (h * g) z ≫ τ := by
  let W := M.X ⨯ affineLine k
  let F := Over.forget (Spec (CommRingCat.of k))
  have hp' := hp.map F
  haveI : Flat τ.left := MorphismProperty.of_isPullback hp' Q.flat
  haveI : Surjective τ.left := MorphismProperty.of_isPullback hp' Q.surjective
  haveI : LocallyOfFinitePresentation τ.left := MorphismProperty.of_isPullback hp' Q.finitePresentation
  letI : Epi τ := fppf_epi τ
  let q := M.X ◁ τ
  obtain ⟨hFlat, hSurj, hFP⟩ := fppf_whiskerLeft M.X τ
  letI : Flat q.left := hFlat
  letI : Surjective q.left := hSurj
  letI : LocallyOfFinitePresentation q.left := hFP
  letI : Epi q := fppf_epi q
  let m : M.X ⊗ W ⟶ L := prod.lift (fst M.X W * (snd M.X W ≫ prod.fst))
      (snd M.X W ≫ prod.snd) ≫ τ
  have hm {T : SchemeOver k} (r : T ⟶ M.X ⊗ W) :
      r ≫ m = prod.lift ((r ≫ fst M.X W) * (r ≫ snd M.X W ≫ prod.fst))
        (r ≫ snd M.X W ≫ prod.snd) ≫ τ := by
    simp only [m, ← Category.assoc, prod.comp_lift, MonObj.comp_mul]
  obtain ⟨act, hact⟩ := descends q m (fun T r t hrt ↦ by
    let g := r ≫ snd M.X W ≫ prod.fst
    let g' := t ≫ snd M.X W ≫ prod.fst
    let z := r ≫ snd M.X W ≫ prod.snd
    let z' := t ≫ snd M.X W ≫ prod.snd
    have h₀ : r ≫ fst M.X W = t ≫ fst M.X W := by
      simpa only [q, Category.assoc, whiskerLeft_fst] using congrArg (· ≫ fst M.X L) hrt
    have hw : r ≫ snd M.X W ≫ τ = t ≫ snd M.X W ≫ τ := by
      simpa only [q, Category.assoc, whiskerLeft_snd] using congrArg (· ≫ snd M.X L) hrt
    have hg : g ≫ Q.projection = g' ≫ Q.projection := by
      simpa only [g, g', Category.assoc, hp.w] using congrArg (· ≫ π) hw
    let b := torsorDifference Q g g' hg
    have hb : g' = g * (b ≫ H.inclusion.hom.hom) := by
      rw [show b ≫ H.inclusion.hom.hom = g⁻¹ * g' from torsorDifference_value Q g g' hg,
        mul_inv_cancel_left]
    have he : prod.lift g z ≫ τ = prod.lift g' z' ≫ τ := by
      have hex (y : T ⟶ W) : prod.lift (y ≫ prod.fst) (y ≫ prod.snd) = y := by
        apply prod.hom_ext <;> simp
      simpa only [g, g', z, z', ← Category.assoc, hex] using hw
    have h₁ := hτ g b z
    rw [← hb] at h₁
    have hz : scaleLine ψ b⁻¹ z = z' := by
      have h₁' := hp.hom_ext (by simp : prod.lift g' (scaleLine ψ b⁻¹ z) ≫ prod.fst =
        prod.lift g' z' ≫ prod.fst) (h₁.trans he)
      simpa only [prod.lift_snd] using congrArg (· ≫ prod.snd) h₁'
    rw [hm, hm, h₀]
    change prod.lift ((t ≫ fst M.X W) * g) z ≫ τ =
      prod.lift ((t ≫ fst M.X W) * g') z' ≫ τ
    rw [hb, ← hz, ← mul_assoc]
    exact (hτ ((t ≫ fst M.X W) * g) b z).symm)
  have eval {T : SchemeOver k} (h g : T ⟶ M.X) (z : T ⟶ affineLine k) :
      lift h (prod.lift g z ≫ τ) ≫ act = prod.lift (h * g) z ≫ τ := by
    rw [show lift h (prod.lift g z ≫ τ) = lift h (prod.lift g z) ≫ q from
      (lift_whiskerLeft _ _ _).symm, Category.assoc, hact, hm]
    have hfst : lift h (prod.lift g z) ≫ fst M.X W = h := lift_fst _ _
    have hsnd : lift h (prod.lift g z) ≫ snd M.X W = prod.lift g z := lift_snd _ _
    change prod.lift ((lift h (prod.lift g z) ≫ fst M.X W) *
      (lift h (prod.lift g z) ≫ snd M.X W ≫ prod.fst))
        (lift h (prod.lift g z) ≫ snd M.X W ≫ prod.snd) ≫ τ = _
    rw [hfst, reassoc_of% hsnd, reassoc_of% hsnd, prod.lift_fst, prod.lift_snd]
  have eqUnit : lift (toUnit L ≫ η[M.X]) (𝟙 L) ≫ act = 𝟙 L := by
    apply (cancel_epi τ).mp
    have he : prod.lift (prod.fst : W ⟶ M.X) (prod.snd : W ⟶ affineLine k) = 𝟙 W := by
      apply prod.hom_ext <;> simp [W]
    simp only [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id]
    change lift (1 : W ⟶ M.X) τ ≫ act = τ
    simpa only [he, Category.id_comp, one_mul] using eval (1 : W ⟶ M.X) prod.fst prod.snd
  have eqAssoc : (lift ((lift (fst M.X (M.X ⊗ L)) (snd M.X (M.X ⊗ L) ≫ fst M.X L)) ≫ μ[M.X])
        (snd M.X (M.X ⊗ L) ≫ snd M.X L)) ≫ act =
      lift (fst M.X (M.X ⊗ L)) (snd M.X (M.X ⊗ L) ≫ act) ≫ act := by
    obtain ⟨hF, hS, hP⟩ := fppf_whiskerLeft M.X q
    letI : Flat (M.X ◁ q).left := hF
    letI : Surjective (M.X ◁ q).left := hS
    letI : LocallyOfFinitePresentation (M.X ◁ q).left := hP
    letI : Epi (M.X ◁ q) := fppf_epi _
    apply (cancel_epi (M.X ◁ q)).mp
    let h := fst M.X (M.X ⊗ W)
    let j := snd M.X (M.X ⊗ W) ≫ fst M.X W
    let w := snd M.X (M.X ⊗ W) ≫ snd M.X W
    let g := w ≫ prod.fst
    let z := w ≫ prod.snd
    have hw : prod.lift g z = w := by apply prod.hom_ext <;> simp [g, z]
    have hq : M.X ◁ q = lift h (lift j (prod.lift g z ≫ τ)) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [h, W]
      · apply CartesianMonoidalCategory.hom_ext <;> simp [q, j, w, hw, W]
    rw [hq]
    simp only [comp_lift_assoc, lift_fst, lift_snd, lift_snd_assoc, eval]
    change prod.lift ((h * j) * g) z ≫ τ = prod.lift (h * (j * g)) z ≫ τ
    rw [mul_assoc]
  let aL := modObjOfSchemeAction (G := M) (X := L)
    ⟨act, eqUnit, eqAssoc⟩
  refine ⟨aL, ?_, fun _ ↦ eval⟩
  apply (cancel_epi q).mp
  change q ≫ act ≫ π = q ≫ (𝟙 M.X ⊗ₘ π) ≫ a.smul
  let x := fst M.X W
  let y := snd M.X W ≫ prod.fst
  have hbase : (x * y) ≫ Q.projection = lift x (y ≫ Q.projection) ≫ a.smul := by
    have h := congrArg (lift x y ≫ ·) ha
    rw [← Category.assoc (lift x y) μ, ← Category.assoc (lift x y) (𝟙 M.X ⊗ₘ Q.projection),
      id_tensorHom, lift_whiskerLeft] at h
    exact h
  have hq : q = lift x (snd M.X W ≫ τ) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [q, x, W]
  calc
    q ≫ act ≫ π = m ≫ π := by rw [← Category.assoc, hact]
    _ = (x * y) ≫ Q.projection := by
      simp only [m, Category.assoc, ← hp.w, prod.lift_fst_assoc, x, y]
    _ = lift x (y ≫ Q.projection) ≫ a.smul := hbase
    _ = q ≫ (𝟙 M.X ⊗ₘ π) ≫ a.smul := by
      rw [← Category.assoc q, hq, id_tensorHom, lift_whiskerLeft,
        Category.assoc (snd M.X W) τ π, ← hp.w]
      rfl

private theorem constructAssociatedBundle
    {G : Specs.AffineAlgebraicGroup k} {P : OppositeBorelPair G} {Q : Presentation P.negative}
    (p : BorelProjection P) (χ : Character P.torus.group) (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (h : CoversWithSections Q.projection) : Nonempty (AssociatedBundle Q a p χ) := by
  let ψ := p.projection ≫ χ
  obtain ⟨τ, hτ⟩ := exists_bundleTrivialization Q ψ h
  have hp := bundleTrivialization_pullback Q ψ hτ
  have hr {T : SchemeOver k} := bundleTrivialization_right Q ψ hτ (T := T)
  obtain ⟨act, he, hl⟩ := bundleAction Q ψ a ha τ hp hr
  refine ⟨⟨gluedBundle Q ψ h, gluedProjection Q ψ h, act, τ, hp, he, ?_, ?_, ?_⟩⟩
  · intro R g b z
    have hz : scaleLine ψ b⁻¹ (linePoint R z) =
        linePoint R (characterValue (p.projection ≫ χ) R b⁻¹ * z) := by
      simpa only [ψ, Category.id_comp, characterUnit_val, lineValue_linePoint] using
        scaleLine_eval ψ b⁻¹ (linePoint R z) R (𝟙 ((testSpec k).obj (op R)))
    rw [← hz]
    exact hr g b _
  · intro R h₀ g z
    exact hl _ h₀ g (linePoint R z)
  · intro y
    obtain ⟨U, hu⟩ := h y
    refine ⟨opened Q.scheme U.val, openIncl Q.scheme U.val, gluedChart Q ψ h U,
      inferInstanceAs (IsOpenImmersion U.val.ι), ?_, gluedChart_pullback Q ψ h U,
      gluedChart_coordinate Q ψ hτ U⟩
    exact ⟨⟨y, hu⟩, rfl⟩

end BundleConstruction

section SplitFlagCharts

open CategoryTheory.CartesianMonoidalCategory
open Specs.QuotientEmbedding (Presentation)
open Specs.BruhatOrbitParametrization (conjugatePoint)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open CocharacterDynamics (multiplyFactors)
open private rootProductAffineIso from LinearAlgebraicGroups.Flag.BruhatCells
open private leftTranslation radicalIso from LinearAlgebraicGroups.Flag.OpenCell
open private existsEnumeration from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private irreducible_of_geometricallyConnected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false

variable {M : Specs.GroupScheme k} {H : Specs.ClosedSubgroup M}

/-- The map on the inverse image of a family of points given by a section. -/
private def sectionProduct {U : SchemeOver k} (s : U ⟶ M.X) :
    U ⨯ H.group.X ⟶ M.X :=
  (prod.fst ≫ s) * (prod.snd ≫ H.inclusion.hom.hom)

private theorem sectionProduct_apply {U T : SchemeOver k}
    (s : U ⟶ M.X) (u : T ⟶ U) (b : T ⟶ H.group.X) :
    prod.lift u b ≫ sectionProduct (H := H) s = (u ≫ s) * (b ≫ H.inclusion.hom.hom) := by
  simp [sectionProduct, MonObj.comp_mul]

private theorem sectionProduct_pullback (Q : Presentation H) {U : SchemeOver k}
    (s : U ⟶ M.X) :
    IsPullback prod.fst (sectionProduct (H := H) s) (s ≫ Q.projection) Q.projection := by
  have hw : (prod.fst : U ⨯ H.group.X ⟶ U) ≫ (s ≫ Q.projection) =
      sectionProduct (H := H) s ≫ Q.projection :=
    (quotient_right_mul Q (prod.fst ≫ s) prod.snd).symm
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun a ↦ prod.lift a.fst (torsorDifference Q (a.fst ≫ s) a.snd
      (by simpa only [Category.assoc] using a.condition)))
    (fun a ↦ prod.lift_fst _ _) (fun a ↦ ?_) (fun a m hm₁ hm₂ ↦ ?_))
  · rw [sectionProduct_apply, torsorDifference_value, mul_inv_cancel_left]
  · apply prod.hom_ext
    · rwa [prod.lift_fst]
    · rw [prod.lift_snd]
      symm
      apply torsorDifference_unique
      simpa only [sectionProduct, MonObj.comp_mul, Category.assoc, reassoc_of% hm₁] using hm₂.symm

variable {G : Specs.AffineAlgebraicGroup k} {P : OppositeBorelPair G}

private theorem sectionProduct_open (Q : Presentation H) {U : SchemeOver k}
    (s : U ⟶ M.X) (hs : IsOpenImmersion (sectionProduct (H := H) s).left) :
    IsOpenImmersion (s ≫ Q.projection).left :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ((sectionProduct_pullback Q s).flip.map (Over.forget _))
    ⟨⟨Q.surjective, Q.flat⟩, Q.finitePresentation⟩ hs

private def tensorIsoProduct (U V : SchemeOver k) : U ⊗ V ≅ U ⨯ V where
  hom := prod.lift (fst U V) (snd U V)
  inv := lift prod.fst prod.snd
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  inv_hom_id := by
    apply prod.hom_ext <;> simp

@[reassoc] private theorem tensorIsoProduct_fst (U V : SchemeOver k) :
    (tensorIsoProduct U V).hom ≫ prod.fst = fst _ _ := prod.lift_fst _ _

@[reassoc] private theorem tensorIsoProduct_snd (U V : SchemeOver k) :
    (tensorIsoProduct U V).hom ≫ prod.snd = snd _ _ := prod.lift_snd _ _

private theorem sectionProduct_radical_open
    {Bneg : Specs.ClosedSubgroup G.val} {Rpos : Specs.ClosedSubgroup P.negative.group}
    {Rneg : Specs.ClosedSubgroup Bneg.group}
    {i : P.torus.group ⟶ P.negative.group}
    (hi : i ≫ P.negative.inclusion = P.torus.inclusion)
    (hFactor : IsIso (multiplyFactors i Rpos.inclusion))
    (hc : IsOpenImmersion (Specs.OpenCell.cellMap P.torus Rneg Rpos).left) :
    IsOpenImmersion
      (sectionProduct (H := P.negative) (Rneg.inclusion ≫ Bneg.inclusion).hom.hom).left := by
  let s := (Rneg.inclusion ≫ Bneg.inclusion).hom.hom
  let e := (𝟙 Rneg.group.X ⊗ₘ multiplyFactors i Rpos.inclusion) ≫
    (tensorIsoProduct Rneg.group.X P.negative.group.X).hom
  haveI : IsIso (multiplyFactors i Rpos.inclusion) := hFactor
  haveI : IsIso e := inferInstanceAs (IsIso (_ ≫ (tensorIsoProduct _ _).hom))
  have h :
      e ≫ sectionProduct (H := P.negative) s = Specs.OpenCell.cellMap P.torus Rneg Rpos := by
    have hi' : i.hom.hom ≫ P.negative.inclusion.hom.hom = P.torus.inclusion.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map hi
    simp only [e, s, sectionProduct, Specs.OpenCell.cellMap, MonObj.comp_mul,
      Category.assoc, tensorIsoProduct_fst_assoc, tensorIsoProduct_snd_assoc, tensorHom_fst_assoc,
      tensorHom_snd_assoc, Category.id_comp, multiplyFactors, MonObj.comp_mul, MonObj.mul_comp,
      hi']
    rfl
  haveI : IsOpenImmersion (e.left ≫ (sectionProduct (H := P.negative) s).left) := by
    simpa only [← Over.comp_left, h] using hc
  exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion e.left _).mp inferInstance

private theorem sectionProduct_translate_open {U : SchemeOver k}
    (s : U ⟶ M.X) (n : 𝟙_ (SchemeOver k) ⟶ M.X)
    (h : IsOpenImmersion (sectionProduct (H := H) s).left) :
    IsOpenImmersion (sectionProduct (H := H) ((toUnit U ≫ n) * s)).left := by
  let l := leftTranslation n
  have he : sectionProduct (H := H) ((toUnit U ≫ n) * s) =
      sectionProduct (H := H) s ≫ l.hom := by
    simp only [sectionProduct, l, leftTranslation, MonObj.comp_mul, comp_toUnit_assoc,
      Category.comp_id, mul_assoc]
  rw [he, Over.comp_left]
  letI := h
  infer_instance

private def polynomialChart (k : Type u) [Field k] (n : ℕ) :
    (testSpec k).obj (op (CommAlgCat.of k (MvPolynomial (Fin n) k))) ≅
      Specs.BruhatCells.affineSpace k n := by
  letI : (algSpec (CommRingCat.of k)).Braided := AlgebraicGeometry.braidedAlgSpec
  induction n with
  | zero =>
    exact (testSpec k).mapIso (CommAlgCat.isoMk (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm).op ≪≫
      (Functor.Monoidal.εIso (algSpec (CommRingCat.of k))).symm
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv k n).trans
      ((polyEquivTensor k (MvPolynomial (Fin n) k)).trans
        (Algebra.TensorProduct.comm k (MvPolynomial (Fin n) k) (Polynomial k)))
    exact (testSpec k).mapIso (CommAlgCat.isoMk e.symm).op ≪≫
      (Functor.Monoidal.μIso (algSpec (CommRingCat.of k)) (op (CommAlgCat.of k (Polynomial k)))
        (op (CommAlgCat.of k (MvPolynomial (Fin n) k)))).symm ≪≫
      tensorIso (Iso.refl (affineLine k)) ih

private theorem flagCover_and_polynomialChart (Q : Presentation P.negative) :
    (∀ y : Q.scheme.left, ∃ (U : SchemeOver k) (s : U ⟶ G.val.X),
        IsOpenImmersion (s ≫ Q.projection).left ∧ y ∈ Set.range (s ≫ Q.projection).left) ∧
    ∃ (n : ℕ) (s : (testSpec k).obj (op (CommAlgCat.of k (MvPolynomial (Fin n) k))) ⟶ G.val.X),
      IsOpenImmersion (sectionProduct (H := P.negative) s).left := by
  classical
  obtain ⟨hComm, D, I, U, Bneg, Rpos, Rneg, c, b, hBneg, hTneg, hOpp,
    hRpos, hRneg, _, _, _, hReps, _, hCells⟩ :=
    Flag.BruhatCells.bruhatCells G P.reductive P.torus P.negative P.split P.maximal
      P.negativeBorel P.inNegative
  letI := hComm
  obtain ⟨_, _, _, _, _, _, hBorel⟩ :=
    RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  obtain ⟨R, j, _, hR, _, hj, _, _, hIso, _⟩ :=
    hBorel P.negative P.negativeBorel P.inNegative
  obtain ⟨hOpen, _, _⟩ := Flag.OpenCell.openCell G P.reductive P.torus P.split P.maximal
    P.negative Bneg P.negativeBorel hBneg P.inNegative hTneg hOpp Rneg R hRneg hR
  let s := (Rneg.inclusion ≫ Bneg.inclusion).hom.hom
  have hs : IsOpenImmersion (sectionProduct (H := P.negative) s).left :=
    sectionProduct_radical_open hj hIso hOpen
  choose n hn using hReps
  obtain ⟨a, _, cover⟩ := hCells Q
  obtain ⟨A, C, hFactor, _, _, hCover⟩ := cover n hn
  refine ⟨?_, ?_⟩
  · intro y
    have hy : y ∈ ⋃ w, Set.range (C w).orbitInclusion.left := by simp [hCover]
    obtain ⟨w, x, hx⟩ := Set.mem_iUnion.mp hy
    let g := n w ≫ I.normalizer.inclusion.hom.hom
    let t := (toUnit Rneg.group.X ≫ g) * s
    have ht : IsOpenImmersion (t ≫ Q.projection).left :=
      sectionProduct_open Q t (sectionProduct_translate_open s g hs)
    have hin : (A w).inclusion.hom.hom ∈ Specs.SubgroupSections (A w) (A w).group.X := by
      change ∃ f : (A w).group.X ⟶ (A w).group.X, f ≫ (A w).inclusion.hom.hom = _
      exact ⟨𝟙 _, Category.id_comp _⟩
    have hconj := (((hFactor w).1 (A w).group.X (A w).inclusion.hom.hom).mp hin).2
    change ∃ r : (A w).group.X ⟶ Rneg.group.X,
      r ≫ s = conjugatePoint g⁻¹ (A w).inclusion.hom.hom at hconj
    obtain ⟨r, hr⟩ := hconj
    have hrt : r ≫ t = (A w).inclusion.hom.hom * (toUnit (A w).group.X ≫ g) := by
      rw [show t = (toUnit Rneg.group.X ≫ g) * s from rfl, MonObj.comp_mul, comp_toUnit_assoc, hr]
      simp only [conjugatePoint, GrpObj.comp_inv, inv_inv]
      group
    have horb : r ≫ t ≫ Q.projection = (C w).orbitIso.hom ≫ (C w).orbitInclusion := by
      rw [← Category.assoc r, hrt, (C w).orbitIso_eq]
    refine ⟨Rneg.group.X, t, ht, r.left ((C w).orbitIso.inv.left x), ?_⟩
    have hval := congrArg (fun f : (A w).group.X ⟶ Q.scheme ↦
      f.left ((C w).orbitIso.inv.left x)) horb
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at hval
    have hcancel : (C w).orbitIso.hom.left ((C w).orbitIso.inv.left x) = x := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
      rfl
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, hcancel, hx] using hval
  · letI := D.finiteRoots
    obtain ⟨l, hl⟩ := existsEnumeration (Specs.BorelsAndChambers.subgroupRoots P.torus Bneg)
    obtain ⟨Rb, _, _, hRb, _, _, _, _, _, hParam⟩ := hBorel Bneg hBneg hTneg
    obtain ⟨e, _⟩ := radicalIso hRb hRneg
    obtain ⟨par, _⟩ := hParam U l hl
    let iso := (polynomialChart k l.length) ≪≫ (rootProductAffineIso U l).symm ≪≫
      par ≪≫ (Grp.forget _).mapIso e
    refine ⟨l.length, iso.hom ≫ s, ?_⟩
    have hh : sectionProduct (H := P.negative) (iso.hom ≫ s) =
        prod.map iso.hom (𝟙 _) ≫ sectionProduct (H := P.negative) s := by
      simp [sectionProduct, MonObj.comp_mul]
    rw [hh, Over.comp_left]
    letI := hs
    haveI : IsIso (prod.map iso.hom (𝟙 P.negative.group.X)) := by infer_instance
    infer_instance

end SplitFlagCharts

section FiniteSections

open WithZero
open Specs.CharacterDescent (Character)
open Specs.QuotientEmbedding (Presentation)
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private irreducible_of_geometricallyConnected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

variable {G : Specs.AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {p : BorelProjection P} {χ : Character P.torus.group}

private def restrictToChart {B : TestAlgebra k} (e : specGroup A ≅ G.val)
    (s : (testSpec k).obj (op B) ⟶ G.val.X) : A →ₐ[k] B :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (s ≫ e.inv.hom.hom)).unop.hom

private theorem restrictToChart_eval {B : TestAlgebra k} (e : specGroup A ≅ G.val)
    (s : (testSpec k).obj (op B) ⟶ G.val.X) (f : A) :
    s ≫ coordinateFunction e f = linePoint B (restrictToChart e s f) := by
  have h : (testSpec k).map (CommAlgCat.ofHom (restrictToChart e s)).op =
      s ≫ e.inv.hom.hom :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  change s ≫ e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) f = _
  rw [← Category.assoc, ← h]
  exact linePoint_comp (R := CommAlgCat.of k A) (S := B) (restrictToChart e s) f

private theorem covariant_eq_of_chart_eq {U : SchemeOver k}
    (s : U ⟶ G.val.X) (hs : IsOpenImmersion (sectionProduct (H := P.negative) s).left)
    (u : Points U (CommAlgCat.of k k))
    {f f' : G.val.X ⟶ affineLine k} (hf : SchemeCovariant p χ f) (hf' : SchemeCovariant p χ f')
    (he : s ≫ f = s ≫ f') : f = f' := by
  let inc := sectionProduct (H := P.negative) s
  have hinc : inc ≫ f = inc ≫ f' := by
    apply GrassmannianCharts.hom_ext_on_affines
    intro R a
    let g := (a ≫ prod.fst) ≫ s
    let b := a ≫ prod.snd
    let z := lineValue R (g ≫ f)
    have hz : g ≫ f = linePoint R z := (linePoint_lineValue R _).symm
    have hz' : g ≫ f' = linePoint R z := by
      simpa only [g, Category.assoc, he] using hz
    have ha : a ≫ inc = g * (b ≫ P.negative.inclusion.hom.hom) := by
      have hsplit : a = prod.lift (a ≫ prod.fst) (a ≫ prod.snd) := by
        apply prod.hom_ext <;> simp
      rw [show a ≫ inc = prod.lift (a ≫ prod.fst) (a ≫ prod.snd) ≫ inc from
        congrArg (· ≫ inc) hsplit, sectionProduct_apply]
    rw [← Category.assoc, ← Category.assoc, ha, hf R g b z hz, hf' R g b z hz']
  letI : IsOpenImmersion inc.left := hs
  letI : GeometricallyConnected G.val.X.hom := P.reductive.2.1
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  letI : QuasiCompact G.val.X.hom := G.property.2.2
  letI : IrreducibleSpace G.val.X.left := irreducible_of_geometricallyConnected G.val
  let hpoint := prod.lift u (1 : Points P.negative.group.X (CommAlgCat.of k k))
  letI : IsDominant inc.left := ⟨inc.left.isOpenMap.isOpen_range.dense
    ⟨_, hpoint.left (IsLocalRing.closedPoint k), rfl⟩⟩
  letI : Smooth G.val.X.hom := P.reductive.1
  letI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  haveI : IsSeparated (affineLine k).hom := inferInstanceAs
    (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))))
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated (affineLine k).hom
    ((Over.w f).trans (Over.w f').symm) inc.left (congrArg Over.Hom.left hinc)

private abbrev valuationAlgebra {K : Type u} {Γ : Type} [Field K] [Algebra k K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (h : ∀ a : k, v (algebraMap k K a) ≤ 1) : Algebra k v.valuationSubring :=
  ((algebraMap k K).codRestrict v.valuationSubring.toSubring h).toAlgebra

private theorem valuationScalarTower {K : Type u} {Γ : Type} [Field K] [Algebra k K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (h : ∀ a : k, v (algebraMap k K a) ≤ 1) :
    letI := valuationAlgebra v h
    IsScalarTower k v.valuationSubring K := by
  letI := valuationAlgebra v h
  exact IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

private theorem sectionValues_bounded {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    (L : AssociatedBundle Q a p χ) (hproper : IsProper Q.scheme.hom)
    {K : Type u} {Γ : Type} [Field K] [Algebra k K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (h : ∀ r : k, v (algebraMap k K r) ≤ 1)
    (g : Points G.val.X (CommAlgCat.of k K)) :
    ∃ b : Kˣ, ∀ (s : BundleSection L) (f : G.val.X ⟶ affineLine k) (z : K),
        Q.projection ≫ s.val = prod.lift (𝟙 _) f ≫ L.trivialization →
        g ≫ f = linePoint (CommAlgCat.of k K) z → v z ≤ v (b : K) := by
  let R := v.valuationSubring
  letI : Algebra k R := valuationAlgebra v h
  letI : IsScalarTower k R K := valuationScalarTower v h
  obtain ⟨b, hb⟩ := bundleSections_bounded L hproper R K g
  refine ⟨b, fun s f z hs hz ↦ ?_⟩
  obtain ⟨x, hx⟩ := hb s f z hs hz
  have hval : v (algebraMap R K x) ≤ 1 := x.property
  rw [hx, map_mul]
  have hm : v (b : K) * v (algebraMap R K x) ≤ v (b : K) * 1 :=
    mul_le_mul_of_nonneg_left hval zero_le
  simpa only [mul_one] using hm

open scoped Classical in
private theorem inftyValuation_of_base (n : ℕ) (a : k) :
    RatFunc.inftyValuation (ParameterField k (Fin n)) (algebraMap k (RayField k (Fin n)) a) ≤ 1 := by
  let F := ParameterField k (Fin n)
  let K := RayField k (Fin n)
  by_cases h : a = 0
  · rw [h, map_zero, map_zero]
    exact zero_le
  · rw [IsScalarTower.algebraMap_apply k F K]
    change RatFunc.inftyValuation F (RatFunc.C (algebraMap k F a)) ≤ 1
    have hF : algebraMap k F a ≠ 0 := (map_ne_zero (algebraMap k F)).mpr h
    rw [RatFunc.inftyValuation.C F hF]

private theorem finiteDimensionalCovariant
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    (L : AssociatedBundle Q a p χ) (hproper : IsProper Q.scheme.hom)
    (e : specGroup A ≅ G.val) (q : A ⟶ D) (c : GroupLike k D)
    (E : BundleSection L ≃ covariantFunctions q c)
    (hE : ∀ s, Q.projection ≫ s.val = prod.lift (𝟙 G.val.X)
      (coordinateFunction e (E s : A)) ≫ L.trivialization)
    (hCov : ∀ f : covariantFunctions q c, SchemeCovariant p χ (coordinateFunction e (f : A)))
    (n : ℕ) (s : (testSpec k).obj (op (CommAlgCat.of k (MvPolynomial (Fin n) k))) ⟶ G.val.X)
    (hs : IsOpenImmersion (sectionProduct (H := P.negative) s).left) :
    FiniteDimensional k (covariantFunctions q c) := by
  classical
  let B := CommAlgCat.of k (MvPolynomial (Fin n) k)
  let f : covariantFunctions q c →ₗ[k] MvPolynomial (Fin n) k :=
    (restrictToChart e s).toLinearMap.comp (covariantFunctions q c).subtype
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply (coordinateFunctionEquiv e).injective
    simp only [coordinateFunctionEquiv_apply]
    have hu : Points ((testSpec k).obj (op B)) (CommAlgCat.of k k) :=
      (testSpec k).map (CommAlgCat.ofHom (MvPolynomial.aeval (fun _ : Fin n ↦ (0 : k)))).op
    apply covariant_eq_of_chart_eq s hs hu (hCov x) (hCov y)
    rw [restrictToChart_eval, restrictToChart_eval]
    exact congrArg (linePoint B) h
  let K := RayField k (Fin n)
  let v := RatFunc.inftyValuation (ParameterField k (Fin n))
  let g : Points G.val.X (CommAlgCat.of k K) :=
    (testSpec k).map (CommAlgCat.ofHom (genericRay k (Fin n))).op ≫ s
  obtain ⟨b, hb⟩ := sectionValues_bounded L hproper v (inftyValuation_of_base (k := k) n) g
  refine finite_of_boundedRay k (Fin n) f hf (b : K) b.ne_zero (fun w ↦ ?_)
  let t := E.symm w
  have ht : Q.projection ≫ t.val = prod.lift (𝟙 G.val.X)
      (coordinateFunction e (w : A)) ≫ L.trivialization := by
    simpa only [t, Equiv.apply_symm_apply] using hE t
  have hg : g ≫ coordinateFunction e (w : A) = linePoint (CommAlgCat.of k K)
      (genericRay k (Fin n) (f w)) := by
    change ((testSpec k).map (CommAlgCat.ofHom (genericRay k (Fin n))).op ≫ s) ≫
      coordinateFunction e (w : A) = _
    rw [Category.assoc, restrictToChart_eval]
    exact linePoint_comp (R := B) (S := CommAlgCat.of k K) (genericRay k (Fin n)) _
  exact hb t (coordinateFunction e (w : A)) _ ht hg

/-- For each opposite Borel character, the associated bundle has the prescribed
covariant sections and the induced finite-dimensional coaction. -/
theorem flagLineBundleAndSections : FlagLineBundleAndSections.{u} := by
  intro k _ G P p χ Q a ha A D e d q φ hq hφ
  let c : GroupLike k D := ⟨characterCoordinate φ, characterCoordinate_groupLike φ⟩
  have hc : (c : D) = characterCoordinate φ := rfl
  obtain ⟨hCover, n, s, hs⟩ := flagCover_and_polynomialChart Q
  obtain ⟨L⟩ := constructAssociatedBundle p χ a ha
    (coversWithSections_of_local Q.projection hCover)
  obtain ⟨F, hF⟩ := sectionsAreCovariant L
  let J : covariantFunctions q c ≃ {f : G.val.X ⟶ affineLine k // SchemeCovariant p χ f} :=
    Equiv.subtypeEquiv (coordinateFunctionEquiv e) (fun f ↦ by
      rw [coordinateFunctionEquiv_apply]
      exact (schemeCovariant_iff e d q φ hq hφ c hc f).symm)
  let E := F.trans J.symm
  have hE (s : BundleSection L) : Q.projection ≫ s.val =
      prod.lift (𝟙 _) (coordinateFunction e (E s : A)) ≫ L.trivialization := by
    have he := congrArg Subtype.val (J.apply_symm_apply (F s))
    have he' : coordinateFunctionEquiv e (E s : A) = (F s).val := he
    rw [coordinateFunctionEquiv_apply] at he'
    rw [he']
    exact hF s
  have hCov (f : covariantFunctions q c) : SchemeCovariant p χ (coordinateFunction e (f : A)) :=
    (schemeCovariant_iff e d q φ hq hφ c hc _).mpr f.property
  have hproper := ((oppositeFlagGeometry k G P).2.2 Q).2.1
  have hfinite := finiteDimensionalCovariant L hproper e q c E hE hCov n s hs
  obtain ⟨ρ, hρ, hleft⟩ := covariantCoaction q c
  exact ⟨c, hc, L, E, ρ, hfinite, hE, hρ, hleft⟩

/-- Existence of the character line, projective quotient, linearized line bundle,
and rational module of covariant sections with the original split hypotheses. -/
theorem flagInduction : FlagInduction.{u} := by
  intro k _ G P χ
  obtain ⟨⟨p⟩, ⟨Q⟩, hQ⟩ := oppositeFlagGeometry k G P
  obtain ⟨hSmooth, hProper, hTorsor, V, hV, hMod, hFinite, a, j, hj, ha⟩ := hQ Q
  obtain ⟨D, d, φ, c, ρ₁, hφ, hc, hρ₁⟩ := borelCharacterLine p χ
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_hopfSpec.mpr G.property.1
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let q := (ff.preimage (d.hom ≫ P.negative.inclusion ≫ e.inv)).unop
  have hq : specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion := by
    have h : specGroupMap q = d.hom ≫ P.negative.inclusion ≫ e.inv := ff.map_preimage _
    simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨c', hc', L, E, ρ, hW, hE, hρ, hleft⟩ :=
    flagLineBundleAndSections k G P p χ Q a ha A.unop D e d q φ hq hφ
  have he : c' = c := GroupLike.val_injective (hc'.trans hc.symm)
  subst c'
  exact ⟨p, Q, a, A.unop, D, e, d, q, φ, c, ρ₁, L, E, ρ, hSmooth, hProper, hTorsor,
    ⟨V, hV, hMod, hFinite, j, hj⟩, ha, hq, hφ, hc, hρ₁, hW, hE, hρ, hleft⟩

end FiniteSections

end LinearAlgebraicGroups.FlagLineBundle
