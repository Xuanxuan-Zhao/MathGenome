import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import Mathlib.Data.Matrix.Basis
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix
open scoped CategoryTheory.MonObj Matrix TensorProduct

universe u

namespace LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.SymplecticDatumAdjointDescent
open Specs.SymplecticMatrixStructure (Indices PointGroup symplecticPoints mapSymplecticPoint)
open LinearAlgebraicGroups.StandardGroups (generalLinearGroup generalLinearGroupPointsIso)
open Specs.StandardGroups (generalLinearPoints)

open private quotientRepresentsImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private schemeKernel_imageProjection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {I R : Type u} [Fintype I] [DecidableEq I] [CommRing R]

private lemma negJ_mul_J : (-Matrix.J I R) * Matrix.J I R = 1 := by
  rw [Matrix.neg_mul, Matrix.J_squared, neg_neg]

private lemma J_mul_negJ : Matrix.J I R * (-Matrix.J I R) = 1 := by
  rw [Matrix.mul_neg, Matrix.J_squared, neg_neg]

private lemma adjoint_mul (X Y : MatrixAlgebra I R) :
    adjoint (X * Y) = adjoint Y * adjoint X := by
  simp only [adjoint, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.J I R), J_mul_negJ, one_mul]

private lemma adjoint_adjoint (X : MatrixAlgebra I R) :
    adjoint (adjoint X) = X := by
  simp only [adjoint, Matrix.transpose_mul, Matrix.transpose_neg, Matrix.J_transpose,
    Matrix.transpose_transpose, neg_neg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (-Matrix.J I R) (-Matrix.J I R)]
  rw [neg_mul_neg, Matrix.J_squared]
  simp

private lemma adjoint_scalar (a : R) :
    adjoint (Matrix.scalar (Indices I) a) = Matrix.scalar (Indices I) a := by
  rw [adjoint, Matrix.scalar_apply, Matrix.diagonal_transpose]
  have hc := (Algebra.commutes (R := R) a (-Matrix.J I R)).symm
  change -Matrix.J I R * Matrix.scalar (Indices I) a =
    Matrix.scalar (Indices I) a * -Matrix.J I R at hc
  rw [← Matrix.scalar_apply, hc, Matrix.mul_assoc, negJ_mul_J, mul_one]

private lemma isometry_iff (X : MatrixAlgebra I R) :
    X ∈ Matrix.symplecticGroup I R ↔ adjoint X * X = 1 := by
  rw [SymplecticGroup.mem_iff']
  simp only [adjoint, Matrix.mul_assoc]
  constructor
  · intro h
    rw [h, negJ_mul_J]
  · intro h
    have hh := congrArg (Matrix.J I R * ·) h
    rw [← Matrix.mul_assoc (Matrix.J I R), J_mul_negJ, one_mul, mul_one] at hh
    exact hh

private lemma adjoint_map {S : Type u} [CommRing S] (f : R →+* S) (X : MatrixAlgebra I R) :
    (adjoint X).map f = adjoint (X.map f) := by
  simp [adjoint, Matrix.map_mul, Matrix.map_neg, Matrix.transpose_map]

theorem adjointIdentities : AdjointIdentities.{u} := by
  intro I R _ _ _
  exact ⟨adjoint_adjoint, adjoint_mul, adjoint_scalar, isometry_iff, fun f X ↦ adjoint_map f X⟩

set_option maxHeartbeats 600000 in
theorem matrixScalarExtension : MatrixScalarExtension.{u} := by
  intro k I R _ _ _ _ _
  let e₀ := (matrixEquivTensor (Indices I) k R).symm
  let e : R ⊗[k] MatrixAlgebra I k ≃ₐ[R] MatrixAlgebra I R :=
    { e₀.toRingEquiv with
      commutes' := fun r ↦ by
        change e₀ (r ⊗ₜ[k] 1) = algebraMap R (MatrixAlgebra I R) r
        dsimp only [e₀]
        rw [matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
          Algebra.algebraMap_eq_smul_one] }
  have ht (r : R) (X : MatrixAlgebra I k) : e (r ⊗ₜ[k] X) = r • X.map (algebraMap k R) := by
    change (matrixEquivTensor (Indices I) k R).symm (r ⊗ₜ[k] X) = _
    exact matrixEquivTensor_apply_symm (Indices I) k R r X
  refine ⟨e, ht, fun r X ↦ ?_⟩
  rw [ht r (adjoint X), ht r X, adjoint_map]
  simp only [adjoint, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

private lemma adjoint_point (g : PointGroup I R) : adjoint g.val = (g⁻¹).val := rfl

private lemma point_inv_mul (g : PointGroup I R) : (g⁻¹).val * g.val = 1 :=
  congrArg Subtype.val (inv_mul_cancel g)

private lemma point_mul_inv (g : PointGroup I R) : g.val * (g⁻¹).val = 1 :=
  congrArg Subtype.val (mul_inv_cancel g)

private def matrixConjugation (g : PointGroup I R) :
    MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R where
  toFun := conjugateMatrix g
  invFun := conjugateMatrix g⁻¹
  left_inv X := by
    change (g⁻¹).val * (g.val * X * (g⁻¹).val) * (g⁻¹⁻¹).val = X
    simp only [inv_inv, ← Matrix.mul_assoc, point_inv_mul, one_mul]
    rw [Matrix.mul_assoc X, point_inv_mul, mul_one]
  right_inv X := by
    change g.val * ((g⁻¹).val * X * (g⁻¹⁻¹).val) * (g⁻¹).val = X
    simp only [inv_inv, ← Matrix.mul_assoc, point_mul_inv, one_mul]
    rw [Matrix.mul_assoc X, point_mul_inv, mul_one]
  map_mul' X Y := by
    dsimp [conjugateMatrix]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (g⁻¹).val, point_inv_mul, one_mul]
  map_add' X Y := by simp [conjugateMatrix, Matrix.mul_add, Matrix.add_mul]
  commutes' a := by
    dsimp [conjugateMatrix]
    rw [← (Algebra.commutes (R := R) a g.val), Matrix.mul_assoc, point_mul_inv, mul_one]

private def conjugationHom : PointGroup I R →* (MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R) where
  toFun := matrixConjugation
  map_one' := by
    ext X : 1
    change conjugateMatrix (1 : PointGroup I R) X = X
    simp [conjugateMatrix]
  map_mul' g h := by
    ext X : 1
    change conjugateMatrix (g * h) X = conjugateMatrix g (conjugateMatrix h X)
    simp only [conjugateMatrix, _root_.mul_inv_rev]
    change g.val * h.val * X * ((h⁻¹).val * (g⁻¹).val) =
      g.val * (h.val * X * (h⁻¹).val) * (g⁻¹).val
    simp only [Matrix.mul_assoc]

private lemma scalar_point (g : PointGroup I R) {a : R}
    [Nonempty I] (h : g.val = Matrix.scalar (Indices I) a) : a * a = 1 := by
  have h' := isometry_iff g.val |>.mp g.property
  rw [h, adjoint_scalar, ← map_mul, ← map_one (Matrix.scalar (Indices I))] at h'
  let i : Indices I := Sum.inl (Classical.choice (inferInstance : Nonempty I))
  simpa [Matrix.scalar_apply] using congrArg (fun M : MatrixAlgebra I R => M i i) h'

private lemma conjugateMatrix_eq_self_iff (g : PointGroup I R) (X : MatrixAlgebra I R) :
    conjugateMatrix g X = X ↔ Commute g.val X := by
  change g.val * X * (g⁻¹).val = X ↔ g.val * X = X * g.val
  constructor
  · intro h
    calc
      g.val * X = (g.val * X * (g⁻¹).val) * g.val := by
        rw [Matrix.mul_assoc (g.val * X), point_inv_mul, mul_one]
      _ = X * g.val := congrArg (· * g.val) h
  · intro h
    rw [h, Matrix.mul_assoc, point_mul_inv, mul_one]

private lemma conjugation_kernel (g : PointGroup I R) :
    conjugationHom g = 1 ↔ IsScalarMuTwo g.val := by
  classical
  constructor
  · intro h
    cases isEmpty_or_nonempty I with
    | inl hempty =>
      let : IsEmpty I := hempty
      exact ⟨1, one_mul 1, Subsingleton.elim _ _⟩
    | inr hnonempty =>
      let : Nonempty I := hnonempty
      obtain ⟨a, ha⟩ := (Matrix.mem_range_scalar_iff_commute_single' (M := g.val)).mpr
        fun i j => ((conjugateMatrix_eq_self_iff g _).mp
          (congrArg (fun e : MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R =>
            e (Matrix.single i j 1)) h)).symm
      exact ⟨a, scalar_point g ha.symm, ha.symm⟩
  · rintro ⟨a, -, ha⟩
    ext X : 1
    apply (conjugateMatrix_eq_self_iff g X).mpr
    rw [ha]
    exact Algebra.commutes (R := R) a X


private lemma conjugateMatrix_map {S : Type u} [CommRing S]
    (f : R →+* S) (g : PointGroup I R) (X : MatrixAlgebra I R) :
    (conjugateMatrix g X).map f = conjugateMatrix (mapSymplecticPoint f g) (X.map f) := by
  simp only [conjugateMatrix, Matrix.map_mul, ← map_inv (mapSymplecticPoint f)]
  rfl

private lemma conjugateMatrix_adjoint (g : PointGroup I R) (X : MatrixAlgebra I R) :
    conjugateMatrix g (adjoint X) = adjoint (conjugateMatrix g X) := by
  simp only [conjugateMatrix, adjoint_mul, adjoint_point, inv_inv, Matrix.mul_assoc]

private abbrev Entries (I : Type u) := Indices I × Indices I

/-- Matrix entries as the coordinates of the underlying free module. -/
private def entriesEquiv : MatrixAlgebra I R ≃ₗ[R] (Entries I → R) where
  toFun X p := X p.1 p.2
  invFun x := Matrix.of (fun i j ↦ x (i, j))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def glLinearEquiv :
    Matrix.GeneralLinearGroup (Entries I) R ≃* (MatrixAlgebra I R ≃ₗ[R] MatrixAlgebra I R) :=
  Matrix.GeneralLinearGroup.toLin.trans <|
    (LinearMap.GeneralLinearGroup.congrLinearEquiv entriesEquiv.symm).trans <|
      LinearMap.GeneralLinearGroup.generalLinearEquiv R (MatrixAlgebra I R)

private lemma glLinearEquiv_apply (M : Matrix.GeneralLinearGroup (Entries I) R)
    (X : MatrixAlgebra I R) (p : Entries I) :
    glLinearEquiv M X p.1 p.2 = ∑ t, M.val p t * X t.1 t.2 := rfl

private lemma glLinearEquiv_map {S : Type u} [CommRing S] (f : R →+* S)
    (M : Matrix.GeneralLinearGroup (Entries I) R) (X : MatrixAlgebra I R) :
    (glLinearEquiv M X).map f =
      glLinearEquiv (Matrix.GeneralLinearGroup.map f M) (X.map f) := by
  ext i j
  change f (glLinearEquiv M X i j) =
    glLinearEquiv (Matrix.GeneralLinearGroup.map f M) (X.map f) i j
  rw [glLinearEquiv_apply M X (i, j),
    glLinearEquiv_apply (Matrix.GeneralLinearGroup.map f M) (X.map f) (i, j), map_sum]
  simp only [map_mul, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]

private lemma glLinearEquiv_single (M : Matrix.GeneralLinearGroup (Entries I) R)
    (p t : Entries I) :
    glLinearEquiv M (Matrix.single t.1 t.2 1) p.1 p.2 = M.val p t := by
  rw [glLinearEquiv_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ h
    have hst : ¬(t.1 = s.1 ∧ t.2 = s.2) := by
      intro hh
      exact h (Prod.ext hh.1.symm hh.2.symm)
    simp [hst]
  · simp

private def conjugationLinear : PointGroup I R →*
    (MatrixAlgebra I R ≃ₗ[R] MatrixAlgebra I R) where
  toFun g := (conjugationHom g).toLinearEquiv
  map_one' := by
    change (conjugationHom (1 : PointGroup I R)).toLinearEquiv = _
    rw [map_one]
    rfl
  map_mul' g h := by
    change (conjugationHom (g * h)).toLinearEquiv = _
    rw [map_mul]
    rfl

private def conjugationGL : PointGroup I R →* Matrix.GeneralLinearGroup (Entries I) R :=
  glLinearEquiv.symm.toMonoidHom.comp conjugationLinear

private lemma glLinearEquiv_conjugationGL (g : PointGroup I R) (X : MatrixAlgebra I R) :
    glLinearEquiv (conjugationGL g) X = conjugateMatrix g X := by
  change glLinearEquiv (glLinearEquiv.symm (conjugationLinear g)) X = _
  rw [MulEquiv.apply_symm_apply]
  rfl

variable {k : Type u} [Field k]

private def conjugationNat (k I : Type u) [Field k] [Fintype I] [DecidableEq I] :
    symplecticPoints k I ⟶ generalLinearPoints k (Entries I) where
  app R := GrpCat.ofHom conjugationGL
  naturality {R S} f := by
    apply GrpCat.ext
    intro g
    change conjugationGL (mapSymplecticPoint f.hom.toRingHom g) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (conjugationGL g)
    apply Matrix.GeneralLinearGroup.ext
    intro p t
    rw [← glLinearEquiv_single _ p t, ← glLinearEquiv_single _ p t,
      glLinearEquiv_conjugationGL]
    have hm : (Matrix.single t.1 t.2 (1 : R)).map f.hom.toRingHom =
        Matrix.single t.1 t.2 (1 : S) := by
      ext i j
      by_cases hi : t.1 = i <;> by_cases hj : t.2 = j <;>
        simp [hi, hj]
    rw [← hm, ← glLinearEquiv_map, glLinearEquiv_conjugationGL, conjugateMatrix_map, hm]

private lemma conjugationGL_kernel (g : PointGroup I R) :
    conjugationGL g = 1 ↔ IsScalarMuTwo g.val := by
  rw [← conjugation_kernel]
  constructor
  · intro h
    have hl := congrArg glLinearEquiv h
    rw [map_one] at hl
    ext X : 1
    have := congrArg (fun e : MatrixAlgebra I R ≃ₗ[R] MatrixAlgebra I R ↦ e X) hl
    rw [glLinearEquiv_conjugationGL] at this
    exact this
  · intro h
    apply glLinearEquiv.injective
    rw [map_one]
    ext X : 1
    rw [glLinearEquiv_conjugationGL]
    exact congrArg (fun e : MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R ↦ e X) h

variable {G Q : GroupScheme k}

private lemma liftOverTestAlgebra (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] [IsAffineHom q.hom.hom.left]
    (R : TestAlgebra k) (a : GroupPoints Q R) :
    ∃ (S : TestAlgebra k) (f : R ⟶ S) (g : GroupPoints G S),
      f.hom.toRingHom.FaithfullyFlat ∧ f.hom.toRingHom.FinitePresentation ∧
      ((groupPointsFunctor k).map q).app S g = ((groupPointsFunctor k).obj Q).map f a := by
  let T := (testSpec k).obj (op R)
  let a : T ⟶ Q.X := a
  let r₀ := pullback.fst a.left q.hom.hom.left
  let s₀ := pullback.snd a.left q.hom.hom.left
  let V : SchemeOver k := Over.mk (r₀ ≫ T.hom)
  let r : V ⟶ T := Over.homMk r₀
  let s : V ⟶ G.X := Over.homMk s₀ (by
    change s₀ ≫ G.X.hom = r₀ ≫ T.hom
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w a])
  have : IsAffineHom r₀ := MorphismProperty.pullback_fst _ _ (inferInstanceAs (IsAffineHom q.hom.hom.left))
  have : IsAffine T.left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine V.left := isAffine_of_isAffineHom r₀
  obtain ⟨S, ⟨e⟩⟩ := essImage_algSpec.mpr (show IsAffine V.left from inferInstance)
  let f := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (e.hom ≫ r)
  have hf : (testSpec k).map f = e.hom ≫ r :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hspec : Spec.map ((forget₂ (TestAlgebra k) CommRingCat).map f.unop) = e.hom.left ≫ r₀ :=
    congrArg Over.Hom.left hf
  have : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  have hfFlat : f.unop.hom.toRingHom.Flat := by
    apply (Flat.SpecMap_iff (f := (forget₂ (TestAlgebra k) CommRingCat).map f.unop)).mp
    rw [hspec]
    exact (MorphismProperty.cancel_left_of_respectsIso @Flat e.hom.left r₀).mpr
      (inferInstanceAs (Flat (pullback.fst _ _)))
  have hfSurj : Function.Surjective (PrimeSpectrum.comap f.unop.hom.toRingHom) := by
    have h : Surjective (Spec.map ((forget₂ (TestAlgebra k) CommRingCat).map f.unop)) := by
      rw [hspec]
      exact (MorphismProperty.cancel_left_of_respectsIso @Surjective e.hom.left r₀).mpr
        (inferInstanceAs (Surjective (pullback.fst _ _)))
    exact h.1
  have hfFp : f.unop.hom.toRingHom.FinitePresentation := by
    apply (LocallyOfFinitePresentation.SpecMap_iff
      ((forget₂ (TestAlgebra k) CommRingCat).map f.unop)).mp
    rw [hspec]
    exact (MorphismProperty.cancel_left_of_respectsIso
      @LocallyOfFinitePresentation e.hom.left r₀).mpr
      (inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ _)))
  refine ⟨S.unop, f.unop, e.hom ≫ s,
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hfFlat, hfSurj⟩, hfFp, ?_⟩
  have hs : s ≫ q.hom.hom = r ≫ a :=
    Over.OverMorphism.ext pullback.condition.symm
  change (e.hom ≫ s) ≫ q.hom.hom = (testSpec k).map f.unop.op ≫ a
  rw [Category.assoc, hs, ← Category.assoc]
  exact congrArg (· ≫ a) hf.symm

private def representedConjugation (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I) :
    G.val ⟶ (generalLinearGroup k (Entries I)).val :=
  (groupHomEquiv _ _ G.property.1).symm
    (c.hom ≫ conjugationNat k I ≫ (generalLinearGroupPointsIso k (Entries I)).inv)

private lemma representedConjugation_app (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :
    (generalLinearGroupPointsIso k (Entries I)).hom.app R
      (((groupPointsFunctor k).map (representedConjugation G c)).app R g) =
        conjugationGL (c.hom.app R g) := by
  have h := (groupHomEquiv G.val (generalLinearGroup k (Entries I)).val
    G.property.1).apply_symm_apply
      (c.hom ≫ conjugationNat k I ≫ (generalLinearGroupPointsIso k (Entries I)).inv)
  change (groupPointsFunctor k).map (representedConjugation G c) = _ at h
  rw [h]
  exact GrpCat.hom_inv_apply ((generalLinearGroupPointsIso k (Entries I)).app R)
    (conjugationGL (c.hom.app R g))

private lemma representedConjugation_kernel (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I)
    (Z : ClosedSubgroup G.val) (hZ : ScalarCentre c Z) :
    IsSchemeKernel (representedConjugation G c) Z := by
  have : IsAffine G.val.X.left := G.property.1
  have : IsAffine (generalLinearGroup k (Entries I)).val.X.left :=
    (generalLinearGroup k (Entries I)).property.1
  apply schemeKernel_of_testPoints
  intro R g
  rw [hZ R g, ← conjugationGL_kernel]
  change conjugationGL (c.hom.app R g) = 1 ↔
    ((groupPointsFunctor k).map (representedConjugation G c)).app R g = 1
  rw [← representedConjugation_app G c R g]
  let e := (generalLinearGroupPointsIso k (Entries I)).hom.app R
  change e.hom (((groupPointsFunctor k).map (representedConjugation G c)).app R g) = 1 ↔ _
  rw [← e.hom.map_one]
  constructor
  · intro h
    exact (ConcreteCategory.bijective_of_isIso e).1 h
  · exact congrArg e.hom

private def imageMatrix (i : Q ⟶ (generalLinearGroup k (Entries I)).val) :
    (groupPointsFunctor k).obj Q ⟶ generalLinearPoints k (Entries I) :=
  (groupPointsFunctor k).map i ≫ (generalLinearGroupPointsIso k (Entries I)).hom

private def imageLinearAction (i : Q ⟶ (generalLinearGroup k (Entries I)).val)
    (R : TestAlgebra k) : GroupPoints Q R →* (MatrixAlgebra I R ≃ₗ[R] MatrixAlgebra I R) :=
  glLinearEquiv.toMonoidHom.comp ((imageMatrix i).app R).hom

private lemma imageLinearAction_map (i : Q ⟶ (generalLinearGroup k (Entries I)).val)
    (R S : TestAlgebra k) (f : R ⟶ S) (a : GroupPoints Q R) (X : MatrixAlgebra I R) :
    (imageLinearAction i R a X).map f.hom =
      imageLinearAction i S (((groupPointsFunctor k).obj Q).map f a) (X.map f.hom) := by
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom ((imageMatrix i).naturality f)) a
  change (imageMatrix i).app S (((groupPointsFunctor k).obj Q).map f a) =
    Matrix.GeneralLinearGroup.map f.hom.toRingHom ((imageMatrix i).app R a) at h
  change (glLinearEquiv ((imageMatrix i).app R a) X).map f.hom =
    glLinearEquiv ((imageMatrix i).app S (((groupPointsFunctor k).obj Q).map f a)) (X.map f.hom)
  rw [h]
  exact glLinearEquiv_map f.hom.toRingHom _ _

private lemma imageLinearAction_pullback (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I)
    (q : G.val ⟶ Q) (i : Q ⟶ (generalLinearGroup k (Entries I)).val)
    (hqi : q ≫ i = representedConjugation G c)
    (R : TestAlgebra k) (g : GroupPoints G.val R) (X : MatrixAlgebra I R) :
    imageLinearAction i R (((groupPointsFunctor k).map q).app R g) X =
      conjugateMatrix (c.hom.app R g) X := by
  change glLinearEquiv ((generalLinearGroupPointsIso k (Entries I)).hom.app R
    (((groupPointsFunctor k).map (q ≫ i)).app R g)) X = _
  rw [hqi, representedConjugation_app, glLinearEquiv_conjugationGL]

private lemma imageLinearAction_injective (i : Q ⟶ (generalLinearGroup k (Entries I)).val)
    (hi : IsClosedImmersion i.hom.hom.left) (R : TestAlgebra k) :
    Function.Injective (imageLinearAction i R) := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  intro a b h
  have he := glLinearEquiv.injective h
  change (generalLinearGroupPointsIso k (Entries I)).hom.app R
      (((groupPointsFunctor k).map i).app R a) =
    (generalLinearGroupPointsIso k (Entries I)).hom.app R
      (((groupPointsFunctor k).map i).app R b) at he
  have he' := (ConcreteCategory.bijective_of_isIso
    ((generalLinearGroupPointsIso k (Entries I)).hom.app R)).1 he
  exact (cancel_mono i.hom.hom).mp he'

omit [Fintype I] [DecidableEq I] in
private lemma matrix_map_injective {S : Type u} [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) :
    Function.Injective (fun X : MatrixAlgebra I R ↦ X.map f) := by
  intro X Y h
  exact Matrix.ext fun i j ↦ hf (congrArg (fun M : MatrixAlgebra I S ↦ M i j) h)

/-- An algebra automorphism preserving the involution preserves the isometry subgroup. -/
private def restrictIsometry (e : MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R)
    (he : ∀ X, e (adjoint X) = adjoint (e X)) : MulAut (PointGroup I R) where
  toFun g := ⟨e g.val, (isometry_iff _).mpr (by
    rw [← he, ← map_mul, (isometry_iff _).mp g.property, map_one])⟩
  invFun g := ⟨e.symm g.val, (isometry_iff _).mpr (by
    apply e.injective
    rw [map_mul, he, e.apply_symm_apply, (isometry_iff _).mp g.property, map_one])⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv g := Subtype.ext (e.apply_symm_apply g.val)
  map_mul' g h := Subtype.ext (map_mul e g.val h.val)

theorem adjointQuotientAction : AdjointQuotientAction.{u} := by
  intro k I _ _ _ _ G c Z hZ
  let L := generalLinearGroup k (Entries I)
  let f := representedConjugation G c
  have hK : IsSchemeKernel f Z := representedConjugation_kernel G c Z hZ
  obtain ⟨Q, q, i, hqi, _, _⟩ := schemeImageFactorization G L f
  have hqK := schemeKernel_imageProjection hqi.1 hqi.2.2.2.2.2 hK
  have hRep := quotientRepresentsImage hqi hK
  obtain ⟨hqif, hqflat, hqsurj, hqfp, hqaff, hi⟩ := hqi
  have hLift := liftOverTestAlgebra q
  let lin := imageLinearAction i
  have hMap (R S : TestAlgebra k) (b : R ⟶ S) (a : GroupPoints Q.val R)
      (X : MatrixAlgebra I R) : (lin R a X).map b.hom.toRingHom =
        lin S (((groupPointsFunctor k).obj Q.val).map b a) (X.map b.hom.toRingHom) :=
    imageLinearAction_map i R S b a X
  have hPull (R : TestAlgebra k) (g : GroupPoints G.val R) (X : MatrixAlgebra I R) :
      lin R (((groupPointsFunctor k).map q).app R g) X = conjugateMatrix (c.hom.app R g) X :=
    imageLinearAction_pullback G c q i hqif R g X
  have hAd (R : TestAlgebra k) (a : GroupPoints Q.val R) (X : MatrixAlgebra I R) :
      lin R a (adjoint X) = adjoint (lin R a X) := by
    obtain ⟨S, b, g, hb, _, hg⟩ := hLift R a
    apply matrix_map_injective hb.injective
    dsimp only
    rw [hMap, adjoint_map b.hom.toRingHom (lin R a X), hMap, ← hg, hPull, hPull,
      adjoint_map, conjugateMatrix_adjoint]
  have hOne (R : TestAlgebra k) (a : GroupPoints Q.val R) : lin R a 1 = 1 := by
    obtain ⟨S, b, g, hb, _, hg⟩ := hLift R a
    apply matrix_map_injective hb.injective
    dsimp only
    rw [hMap, ← hg, hPull, Matrix.map_one b.hom.toRingHom (map_zero _) (map_one _)]
    exact map_one (conjugationHom (c.hom.app S g))
  have hMul (R : TestAlgebra k) (a : GroupPoints Q.val R) (X Y : MatrixAlgebra I R) :
      lin R a (X * Y) = lin R a X * lin R a Y := by
    obtain ⟨S, b, g, hb, _, hg⟩ := hLift R a
    apply matrix_map_injective hb.injective
    dsimp only
    rw [Matrix.map_mul, hMap, hMap, hMap, ← hg, hPull, hPull, hPull, Matrix.map_mul]
    exact map_mul (conjugationHom (c.hom.app S g)) _ _
  let action (R : TestAlgebra k) :
      GroupPoints Q.val R →* (MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R) :=
    { toFun := fun a ↦ AlgEquiv.ofLinearEquiv (lin R a) (hOne R a) (hMul R a)
      map_one' := by
        ext X : 1
        change lin R 1 X = X
        rw [map_one]
        rfl
      map_mul' := fun a b ↦ by
        ext X : 1
        change lin R (a * b) X = lin R a (lin R b X)
        rw [map_mul]
        rfl }
  let isometryAction (R : TestAlgebra k) : GroupPoints Q.val R →* MulAut (PointGroup I R) :=
    { toFun := fun a ↦ restrictIsometry (action R a) (hAd R a)
      map_one' := by
        ext g : 1
        apply Subtype.ext
        change action R 1 g.val = g.val
        rw [map_one]
        rfl
      map_mul' := fun a b ↦ by
        ext g : 1
        apply Subtype.ext
        change action R (a * b) g.val = action R a (action R b g.val)
        rw [map_mul]
        rfl }
  refine ⟨Q, q, hqK, hRep, hLift, action, isometryAction,
    ?_, hAd, hMap, hPull, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro R a b hab
    apply imageLinearAction_injective i hi R
    ext X : 1
    exact congrArg (fun e : MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R ↦ e X) hab
  · intro R S b a h
    apply Subtype.ext
    exact hMap R S b a h.val
  · intro R S b a g h hg
    apply Subtype.ext
    change (lin R a h.val).map b.hom.toRingHom =
      conjugateMatrix (c.hom.app S g) (h.val.map b.hom.toRingHom)
    rw [hMap, ← hg, hPull]

end

end LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent
