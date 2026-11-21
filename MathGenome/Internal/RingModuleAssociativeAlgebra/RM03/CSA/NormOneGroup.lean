import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.NormOneGroup
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Central.Matrix

namespace RM03.CSA.NormOneGroup

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w z q p
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {R : Type w} [CommRing R] [Algebra k R] {S : Type q} [CommRing S] [Algebra k S]
  {ι : Type z} [Fintype ι] {K : Type p} [Field K] [Algebra k K]

noncomputable abbrev normAt (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (x : R ⊗[k] A) : R :=
  MvPolynomial.eval₂ (algebraMap k R) (fun i => (b.baseChange R).repr x i)
    (genericReducedNorm hA b)

/-- Apply a morphism of coefficient algebras to the left tensor factor. -/
def changeCoefficients (f : R →ₐ[k] S) : R ⊗[k] A →ₐ[k] S ⊗[k] A :=
  Algebra.TensorProduct.map f (.id k A)

omit [Fintype ι] in
/-- Basis coordinates commute with a change of the coefficient algebra. -/
private theorem coord_change (b : Module.Basis ι k A) (f : R →ₐ[k] S)
    (x : R ⊗[k] A) (i : ι) :
    (b.baseChange S).repr (changeCoefficients f x) i = f ((b.baseChange R).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp [changeCoefficients, Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

theorem normAt_natural (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (f : R →ₐ[k] S) (x : R ⊗[k] A) :
    normAt hA b (changeCoefficients f x) = f (normAt hA b x) := by
  change MvPolynomial.eval₂ (algebraMap k S) _ (genericReducedNorm hA b) =
    f.toRingHom (MvPolynomial.eval₂ (algebraMap k R) _ (genericReducedNorm hA b))
  rw [MvPolynomial.hom_eval₂ _ _ f.toRingHom]
  congr 1
  · exact RingHom.ext (fun r => (f.commutes r).symm)
  · exact funext (coord_change b f x)

/-- The given matrix splitting after any further extension of coefficients. -/
def extendSplitting [Algebra K R] [IsScalarTower k K R] {n : ℕ}
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    R ⊗[k] A ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
  let matrixEquiv : R ⊗[K] Matrix (Fin n) (Fin n) K ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
    AlgEquiv.ofRingEquiv (f := (matrixEquivTensor (Fin n) K R).symm.toRingEquiv) (by
      intro r
      change (matrixEquivTensor (Fin n) K R).symm (r ⊗ₜ[K] 1) = _
      simp [Algebra.algebraMap_eq_smul_one])
  Algebra.TensorProduct.congr (Algebra.TensorProduct.rid K R R).symm
    (AlgEquiv.refl : A ≃ₐ[k] A)
  |>.trans (Algebra.TensorProduct.assoc k K R R K A)
  |>.trans (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e)
  |>.trans matrixEquiv

theorem extendSplitting_tmul [Algebra K R] [IsScalarTower k K R] {n : ℕ}
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin n) (Fin n) K) (r : R) (a : A) :
    extendSplitting e (r ⊗ₜ[k] a) =
      r • (e (1 ⊗ₜ[k] a)).map (algebraMap K R) := by
  change (matrixEquivTensor (Fin n) K R).symm (r ⊗ₜ[K] e (1 ⊗ₜ[k] a)) = _
  simp

/-- The norm at every point above the splitting field is the matrix determinant. -/
theorem normAt_eq_det [Algebra K R] [IsScalarTower k K R]
    (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)
    (x : R ⊗[k] A) : normAt hA b x = (extendSplitting e x).det := by
  classical
  let c := fun i => (b.baseChange R).repr x i
  let M := fun i => e (1 ⊗ₜ[k] b i)
  change MvPolynomial.eval₂ (algebraMap k R) c (genericReducedNorm hA b) = _
  have h := congrArg (MvPolynomial.eval₂ (algebraMap K R) c) (genericReducedNorm_map hA b e)
  rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq] at h
  rw [h]
  change (MvPolynomial.eval₂Hom (algebraMap K R) c) (Specs.RM03.CSA.genericMatrix M).det = _
  rw [RingHom.map_det]
  congr 1
  have he : extendSplitting e x = ∑ i, c i • (M i).map (algebraMap K R) := by
    conv_lhs => rw [← (b.baseChange R).sum_repr x]
    simp only [map_sum, map_smul, Module.Basis.baseChange_apply, extendSplitting_tmul,
      one_smul]
    rfl
  rw [he]
  ext i j
  simp [Specs.RM03.CSA.genericMatrix, RingHom.mapMatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, M]

/-- The norm polynomial defines a multiplicative function over every test algebra. -/
noncomputable def normHom (hA : IsCentralSimple k A) (b : Module.Basis ι k A) :
    (R ⊗[k] A) →* R where
  toFun := normAt hA b
  map_one' := by
    obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
    let T := AlgebraicClosure k ⊗[k] R
    let f : R →ₐ[k] T := includeRight
    have hf : Function.Injective f :=
      includeRight_injective (algebraMap k (AlgebraicClosure k)).injective
    apply hf
    rw [← normAt_natural hA b, normAt_eq_det hA b e]
    simp
  map_mul' x y := by
    obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
    let T := AlgebraicClosure k ⊗[k] R
    let f : R →ₐ[k] T := includeRight
    have hf : Function.Injective f :=
      includeRight_injective (algebraMap k (AlgebraicClosure k)).injective
    apply hf
    rw [map_mul f, ← normAt_natural hA b, ← normAt_natural hA b,
      ← normAt_natural hA b]
    simp only [normAt_eq_det hA b e, map_mul, Matrix.det_mul]

theorem normAt_basis_independent {κ : Type*} [Fintype κ] (hA : IsCentralSimple k A)
    (b : Module.Basis ι k A) (c : Module.Basis κ k A) (x : R ⊗[k] A) :
    normAt hA b x = normAt hA c x := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
  let T := AlgebraicClosure k ⊗[k] R
  let f : R →ₐ[k] T := includeRight
  have hf : Function.Injective f :=
    includeRight_injective (algebraMap k (AlgebraicClosure k)).injective
  apply hf
  rw [← normAt_natural hA b f, ← normAt_natural hA c f, normAt_eq_det hA b e,
    normAt_eq_det hA c e]

private theorem isUnit_of_includeRight {B : Type*} [Ring B] [Algebra k B] (x : B)
    (h : IsUnit (includeRight (R := k) (A := K) x)) : IsUnit x := by
  apply IsUnit.isUnit_iff_mulLeft_bijective.mpr
  apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective k K (LinearMap.mulLeft k x)).mp
  have he : (LinearMap.mulLeft k x).lTensor K =
      LinearMap.mulLeft k (includeRight (R := k) (A := K) x) := by
    ext r y
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [he]
  exact IsUnit.isUnit_iff_mulLeft_bijective.mp h

theorem isUnit_of_normAt_eq_one (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (x : R ⊗[k] A) (hx : normAt hA b x = 1) : IsUnit x := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
  let K := AlgebraicClosure k
  let T := K ⊗[k] R
  let f : R →ₐ[k] T := includeRight
  have hd : (extendSplitting e (changeCoefficients f x)).det = 1 := by
    rw [← normAt_eq_det hA b e, normAt_natural, hx, map_one]
  have hm : IsUnit (extendSplitting e (changeCoefficients f x)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hd]; exact isUnit_one)
  have ht : IsUnit (changeCoefficients f x) := by simpa using hm.map (extendSplitting e).symm
  let assoc := Algebra.TensorProduct.assoc k k K K R A
  have he (y : R ⊗[k] A) : assoc (changeCoefficients f y) = 1 ⊗ₜ[k] y := by
    induction y using TensorProduct.inductionOn with
    | tmul r a => rfl
    | add y z hy hz => simp [hy, hz, TensorProduct.tmul_add]
  exact isUnit_of_includeRight x (he x ▸ ht.map assoc)

noncomputable abbrev normOne (hA : IsCentralSimple k A) (b : Module.Basis ι k A) :=
  {x : R ⊗[k] A // normAt hA b x = 1}

/-- Multiplication of norm-one points is multiplication in the scalar extension. -/
noncomputable instance normOneGroup (hA : IsCentralSimple k A) (b : Module.Basis ι k A) :
    Group (normOne (R := R) hA b) where
  one := ⟨1, (normHom hA b).map_one⟩
  mul x y := ⟨x.1 * y.1, by
    change normHom hA b (x.1 * y.1) = _
    rw [map_mul]
    change normAt hA b x.1 * normAt hA b y.1 = 1
    rw [x.2, y.2, mul_one]⟩
  inv x := by
    let u := (isUnit_of_normAt_eq_one hA b x.1 x.2).unit
    refine ⟨↑u⁻¹, ?_⟩
    have h := (normHom hA b).map_mul (u : R ⊗[k] A) (↑u⁻¹)
    rw [Units.mul_inv, map_one, (isUnit_of_normAt_eq_one hA b x.1 x.2).unit_spec,
      show normHom hA b x.1 = 1 from x.2, one_mul] at h
    exact h.symm
  mul_assoc x y z := Subtype.ext (mul_assoc x.1 y.1 z.1)
  one_mul x := Subtype.ext (one_mul x.1)
  mul_one x := Subtype.ext (mul_one x.1)
  inv_mul_cancel x := by
    apply Subtype.ext
    change ↑((isUnit_of_normAt_eq_one hA b x.1 x.2).unit⁻¹) * x.1 = 1
    let u := (isUnit_of_normAt_eq_one hA b x.1 x.2).unit
    change (↑u⁻¹ : R ⊗[k] A) * x.1 = 1
    exact (congrArg ((↑u⁻¹ : R ⊗[k] A) * ·) (isUnit_of_normAt_eq_one hA b x.1 x.2).unit_spec).symm.trans
      (Units.inv_mul u)

/-- A morphism of test algebras acts on norm-one points by changing coefficients. -/
noncomputable def mapNormOne (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (f : R →ₐ[k] S) : normOne (R := R) hA b →* normOne (R := S) hA b where
  toFun x := ⟨changeCoefficients f x.1, by rw [normAt_natural, x.2, map_one]⟩
  map_one' := Subtype.ext (map_one (changeCoefficients f))
  map_mul' x y := Subtype.ext (map_mul (changeCoefficients f) x.1 y.1)

private theorem changeCoefficients_id (x : R ⊗[k] A) :
    changeCoefficients (.id k R) x = x := by simp [changeCoefficients, map_id]

private theorem changeCoefficients_comp {T : Type*} [CommRing T] [Algebra k T]
    (f : R →ₐ[k] S) (g : S →ₐ[k] T) (x : R ⊗[k] A) :
    changeCoefficients (g.comp f) x = changeCoefficients g (changeCoefficients f x) := by
  simpa only [changeCoefficients, AlgHom.comp_apply, AlgHom.id_comp] using
    DFunLike.congr_fun (Algebra.TensorProduct.map_comp g f (AlgHom.id k A) (AlgHom.id k A)) x

open CategoryTheory

/-- The norm-one functor on commutative test algebras. -/
noncomputable def normOneFunctor (hA : IsCentralSimple k A) (b : Module.Basis ι k A) :
    CommAlgCat.{w} k ⥤ GrpCat.{max v w} where
  obj R := GrpCat.of (normOne (R := R) hA b)
  map f := GrpCat.ofHom (mapNormOne hA b (CommAlgCat.Hom.hom f))
  map_id R := by
    ext x : 2
    apply Subtype.ext
    exact changeCoefficients_id x.1
  map_comp f g := by
    ext x : 2
    apply Subtype.ext
    exact changeCoefficients_comp _ _ x.1


private theorem coeff_smul_tmul (r : R) (a : A) :
    r • (1 ⊗ₜ[k] a) = r ⊗ₜ[k] a := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- An algebra automorphism of a scalar extension is determined on the original algebra. -/
private theorem aut_ext (e d : (R ⊗[k] A) ≃ₐ[R] (R ⊗[k] A))
    (h : ∀ a : A, e (1 ⊗ₜ[k] a) = d (1 ⊗ₜ[k] a)) : e = d := by
  apply AlgEquiv.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [← coeff_smul_tmul r a]
    rw [map_smul, map_smul, h]
  | add x y hx hy => simp [hx, hy]

abbrev projectivePoints (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
    (R : Type w) [CommRing R] [Algebra k R] :=
  (R ⊗[k] A) ≃ₐ[R] (R ⊗[k] A)

private def extendAutHom (f : R →ₐ[k] S) (e : projectivePoints k A R) :
    (S ⊗[k] A) →ₐ[S] (S ⊗[k] A) :=
  lift (Algebra.ofId S _) ((changeCoefficients f).comp
    ((e.toAlgHom.restrictScalars k).comp includeRight)) fun s _ => Algebra.commutes s _

private theorem extendAutHom_intertwine (f : R →ₐ[k] S) (e : projectivePoints k A R)
    (x : R ⊗[k] A) :
    extendAutHom f e (changeCoefficients f x) = changeCoefficients f (e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    have h : e (r ⊗ₜ[k] a) = r • e (1 ⊗ₜ[k] a) :=
      (congrArg e (coeff_smul_tmul r a).symm).trans (map_smul e r (1 ⊗ₜ[k] a))
    simp only [extendAutHom, changeCoefficients, map_tmul, AlgHom.id_apply, lift_tmul,
      AlgHom.comp_apply, AlgHom.coe_restrictScalars', AlgEquiv.coe_toAlgHom, includeRight_apply,
      Algebra.ofId_apply, h, Algebra.smul_def, map_mul]
    congr 1
  | add x y hx hy => simp [hx, hy]

private theorem extendAutHom_cancel (f : R →ₐ[k] S) (e : projectivePoints k A R)
    (x : S ⊗[k] A) : extendAutHom f e.symm (extendAutHom f e x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [← coeff_smul_tmul r a, map_smul, map_smul]
    have ha : changeCoefficients f (1 ⊗ₜ[k] a) = 1 ⊗ₜ[k] a := by
      simp [changeCoefficients]
    rw [← ha, extendAutHom_intertwine, extendAutHom_intertwine, AlgEquiv.symm_apply_apply]
  | add x y hx hy => simp [hx, hy]

private def extendAut (f : R →ₐ[k] S) (e : projectivePoints k A R) :
    projectivePoints k A S where
  __ := extendAutHom f e
  invFun := extendAutHom f e.symm
  left_inv := extendAutHom_cancel f e
  right_inv x := by
    change extendAutHom f e (extendAutHom f e.symm x) = x
    simpa only [AlgEquiv.symm_symm] using extendAutHom_cancel f e.symm x

/-- Change of test algebra acts by scalar extension of automorphisms. -/
def mapProjective (f : R →ₐ[k] S) : projectivePoints k A R →* projectivePoints k A S where
  toFun := extendAut f
  map_one' := by
    apply aut_ext
    intro a
    change extendAutHom f 1 (1 ⊗ₜ[k] a) = _
    simpa [changeCoefficients] using extendAutHom_intertwine f (1 : projectivePoints k A R)
      (1 ⊗ₜ[k] a)
  map_mul' e d := by
    apply aut_ext
    intro a
    have hx : changeCoefficients f (1 ⊗ₜ[k] (a : A)) = 1 ⊗ₜ[k] a := by
      simp [changeCoefficients]
    change extendAutHom f (e * d) (1 ⊗ₜ[k] a) =
      extendAutHom f e (extendAutHom f d (1 ⊗ₜ[k] a))
    rw [← hx, extendAutHom_intertwine, extendAutHom_intertwine, extendAutHom_intertwine]
    rfl

theorem mapProjective_intertwine (f : R →ₐ[k] S) (e : projectivePoints k A R)
    (x : R ⊗[k] A) : mapProjective f e (changeCoefficients f x) = changeCoefficients f (e x) :=
  extendAutHom_intertwine f e x

/-- The projective group functor of the algebra. -/
def projectiveFunctor (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] :
    CommAlgCat.{w} k ⥤ GrpCat.{max v w} where
  obj R := GrpCat.of (projectivePoints k A R)
  map f := GrpCat.ofHom (mapProjective (CommAlgCat.Hom.hom f))
  map_id R := by
    ext e : 2
    apply aut_ext
    intro a
    change mapProjective (.id k R) e (1 ⊗ₜ[k] a) = e (1 ⊗ₜ[k] a)
    simpa only [changeCoefficients_id] using
      mapProjective_intertwine (.id k R) e (1 ⊗ₜ[k] a)
  map_comp f g := by
    ext e : 2
    apply aut_ext
    intro a
    have h := mapProjective_intertwine (g.hom.comp f.hom) e (1 ⊗ₜ[k] a)
    change mapProjective (g.hom.comp f.hom) e (1 ⊗ₜ[k] a) =
      mapProjective g.hom (mapProjective f.hom e) (1 ⊗ₜ[k] a)
    rw [← show changeCoefficients (g.hom.comp f.hom) (1 ⊗ₜ[k] (a : A)) = 1 ⊗ₜ[k] a by
      simp [changeCoefficients], h, changeCoefficients_comp, changeCoefficients_comp,
      mapProjective_intertwine, mapProjective_intertwine]

/-- The splitting identifies the norm-one points with special linear matrices. -/
noncomputable def normOneSplit [Algebra K R] [IsScalarTower k K R]
    (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K) :
    normOne (R := R) hA b ≃* Matrix.SpecialLinearGroup (Fin (degree k A)) R where
  toFun x := ⟨extendSplitting e x.1, (normAt_eq_det hA b e x.1).symm.trans x.2⟩
  invFun y := ⟨(extendSplitting e).symm y.1, by
    rw [normAt_eq_det hA b e, AlgEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext ((extendSplitting e).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((extendSplitting e).apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul (extendSplitting e) x.1 y.1)

/-- Compatibility of the matrix splitting with arbitrary morphisms of K-algebras. -/
theorem extendSplitting_natural [Algebra K R] [IsScalarTower k K R]
    [Algebra K S] [IsScalarTower k K S] {n : ℕ}
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (f : R →ₐ[K] S) (x : R ⊗[k] A) :
    extendSplitting e (changeCoefficients (f.restrictScalars k) x) =
      f.toRingHom.mapMatrix (extendSplitting e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [changeCoefficients, map_tmul, AlgHom.id_apply, extendSplitting_tmul, extendSplitting_tmul]
    ext i j
    simp [RingHom.mapMatrix_apply, smul_eq_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem normOneSplit_natural [Algebra K R] [IsScalarTower k K R]
    [Algebra K S] [IsScalarTower k K S] (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)
    (f : R →ₐ[K] S) (x : normOne (R := R) hA b) :
    normOneSplit hA b e (mapNormOne hA b (f.restrictScalars k) x) =
      Matrix.SpecialLinearGroup.map f.toRingHom (normOneSplit hA b e x) :=
  Subtype.ext (extendSplitting_natural e f x.1)

/-- The matrix projective group over a test algebra is the group of algebra automorphisms. -/
def projectiveSplit [Algebra K R] [IsScalarTower k K R] {n : ℕ}
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    projectivePoints k A R ≃* (Matrix (Fin n) (Fin n) R ≃ₐ[R] Matrix (Fin n) (Fin n) R) :=
  (extendSplitting e).autCongr

theorem projectiveSplit_natural [Algebra K R] [IsScalarTower k K R]
    [Algebra K S] [IsScalarTower k K S] {n : ℕ}
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (f : R →ₐ[K] S) (g : projectivePoints k A R) (m : Matrix (Fin n) (Fin n) R) :
    projectiveSplit e (mapProjective (f.restrictScalars k) g) (f.toRingHom.mapMatrix m) =
      f.toRingHom.mapMatrix (projectiveSplit e g m) := by
  obtain ⟨x, rfl⟩ := (extendSplitting e).surjective m
  rw [← extendSplitting_natural e f x]
  simp only [projectiveSplit, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply, mapProjective_intertwine]
  exact extendSplitting_natural e f (g x)


section Conjugation

variable {C : Type*} [Ring C] [Algebra R C]

/-- Conjugation by a unit gives an algebra automorphism. -/
def innerAut (u : Cˣ) : C ≃ₐ[R] C where
  toFun x := (u : C) * x * (↑u⁻¹ : C)
  invFun x := (↑u⁻¹ : C) * x * (u : C)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_add' x y := by rw [mul_add, add_mul]
  commutes' r := by rw [← (Algebra.commutes r (u : C)), Units.mul_inv_cancel_right]

/-- The homomorphism from units to algebra automorphisms, acting by conjugation. -/
def unitsToAut : Cˣ →* (C ≃ₐ[R] C) where
  toFun := innerAut
  map_one' := by ext x; simp [innerAut]
  map_mul' u v := by ext x; simp [innerAut, mul_assoc]

variable (R C) in
/-- The subgroup of invertible scalar multiples of the identity. -/
def scalarUnits : Subgroup Cˣ :=
  (Units.map (algebraMap R C).toMonoidHom).range

instance scalarUnits_normal : (scalarUnits R C).Normal :=
  Subgroup.normal_of_le_center fun u hu => by
    obtain ⟨r, rfl⟩ := hu
    apply Subgroup.mem_center_iff.mpr
    intro v
    apply Units.ext
    exact (Algebra.commutes (r : R) (v : C)).symm

end Conjugation

theorem unitsToAut_ker (hA : IsCentralSimple k A) :
    (unitsToAut (R := k) (C := A)).ker = scalarUnits k A := by
  let : IsSimpleRing A := hA.1
  ext u
  constructor
  · intro hu
    have h (x : A) : (u : A) * x * (↑u⁻¹ : A) = x :=
      DFunLike.congr_fun (MonoidHom.mem_ker.mp hu) x
    have hc : (u : A) ∈ Subalgebra.center k A := by
      rw [Subalgebra.mem_center_iff]
      intro x
      have hv := congrArg (· * (u : A)) (h x)
      simpa only [Units.inv_mul_cancel_right] using hv.symm
    have hcenter := ((isCentralSimple_iff k A).mp hA).2.2.2
    have hc' : (u : A) ∈ (Subalgebra.center k A : Set A) := hc
    rw [hcenter] at hc'
    obtain ⟨r, hr⟩ := hc'
    have hr0 : r ≠ 0 := by
      intro eq
      rw [eq, map_zero] at hr
      exact Units.ne_zero u hr.symm
    exact ⟨Units.mk0 r hr0, Units.ext hr⟩
  · rintro ⟨r, rfl⟩
    apply MonoidHom.mem_ker.mpr
    ext x
    change algebraMap k A (r : k) * x * _ = x
    rw [(Algebra.commutes (r : k) x)]
    exact Units.mul_inv_cancel_right x (Units.map (algebraMap k A).toMonoidHom r)

theorem unitsToAut_surjective (hA : IsCentralSimple k A) :
    Function.Surjective (unitsToAut (R := k) (C := A)) := by
  intro e
  obtain ⟨u, hu⟩ := algEquiv_isInner hA e
  exact ⟨u, AlgEquiv.ext fun x => (hu x).symm⟩

/-- Over a field, the projective points are the units modulo scalar units. -/
noncomputable def projectiveField {F : Type*} [Field F] [Algebra k F]
    (hA : IsCentralSimple k A) :
    ((F ⊗[k] A)ˣ ⧸ scalarUnits F (F ⊗[k] A)) ≃* projectivePoints k A F :=
  (QuotientGroup.quotientMulEquivOfEq (unitsToAut_ker (isCentralSimple_baseChange hA)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective unitsToAut
      (unitsToAut_surjective (isCentralSimple_baseChange hA)))

theorem projectiveField_apply {F : Type*} [Field F] [Algebra k F]
    (hA : IsCentralSimple k A) (u : (F ⊗[k] A)ˣ) (x : F ⊗[k] A) :
    projectiveField (F := F) hA (QuotientGroup.mk u) x = (u : F ⊗[k] A) * x * ↑u⁻¹ := by
  simp only [projectiveField, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The coefficient automorphism of the original scalar extension. -/
def coefficientAut (σ : K ≃ₐ[k] K) : BaseChange k K A ≃ₐ[k] BaseChange k K A :=
  Algebra.TensorProduct.congr σ AlgEquiv.refl

/-- Its transport through the given algebra splitting. -/
def transportedCoefficient {n : ℕ} (e : BaseChange k K A ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (σ : K ≃ₐ[k] K) : Matrix (Fin n) (Fin n) K ≃ₐ[k] Matrix (Fin n) (Fin n) K :=
  (e.restrictScalars k).symm.trans ((coefficientAut σ).trans (e.restrictScalars k))

theorem transportedCoefficient_inner (hA : IsCentralSimple k A)
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)
    (σ : K ≃ₐ[k] K) :
    ∃ u : (Matrix (Fin (degree k A)) (Fin (degree k A)) K)ˣ,
      ∀ x, transportedCoefficient e σ x =
        (u : Matrix _ _ _) * σ.mapMatrix x * (↑u⁻¹ : Matrix _ _ _) := by
  let inc := σ.mapMatrix (m := Fin (degree k A))
  let t := transportedCoefficient e σ
  let d : Matrix (Fin (degree k A)) (Fin (degree k A)) K ≃ₐ[K] _ :=
    AlgEquiv.ofRingEquiv (f := (inc.symm.trans t).toRingEquiv) (by
      intro r
      have hs (τ : K ≃ₐ[k] K) :
          τ.mapMatrix (algebraMap K (Matrix (Fin (degree k A)) (Fin (degree k A)) K) r) =
          algebraMap K _ (τ r) := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
      have ht (r : K) :
          t (algebraMap K (Matrix (Fin (degree k A)) (Fin (degree k A)) K) r) =
          algebraMap K _ (σ r) := by
        change e (coefficientAut σ (e.symm (algebraMap K _ r))) = _
        rw [e.symm.commutes, RM03.CSA.algebraMap_baseChange]
        change e (σ r ⊗ₜ[k] (1 : A)) = _
        exact e.commutes (σ r)
      change t (inc.symm (algebraMap K _ r)) = _
      rw [show inc.symm = σ.symm.mapMatrix by exact AlgEquiv.mapMatrix_symm σ,
        hs, ht, AlgEquiv.apply_symm_apply])
  have hM : IsCentralSimple K (Matrix (Fin (degree k A)) (Fin (degree k A)) K) := by
    let h := isCentralSimple_baseChange (L := K) hA
    let : Nonempty (Fin (degree k A)) := Fin.pos_iff_nonempty.mp (degree_pos hA)
    let : FiniteDimensional K (BaseChange k K A) := h.2.2
    exact ⟨IsSimpleRing.of_ringEquiv e.toRingEquiv h.1,
      inferInstance,
      FiniteDimensional.of_surjective e.toLinearMap e.surjective⟩
  obtain ⟨u, hu⟩ := algEquiv_isInner hM d
  refine ⟨u, fun x => ?_⟩
  have hx := hu (inc x)
  change t (inc.symm (inc x)) = _ at hx
  rwa [AlgEquiv.symm_apply_apply] at hx

private theorem extendSplitting_self {n : ℕ}
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (x : BaseChange k K A) : extendSplitting (R := K) e x = e x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [extendSplitting_tmul, ← coeff_smul_tmul r a, map_smul]
    congr
  | add x y hx hy => simp [hx, hy]

private theorem coefficientAut_apply (σ : K ≃ₐ[k] K) (x : BaseChange k K A) :
    coefficientAut σ x = changeCoefficients σ.toAlgHom x := rfl

/-- On norm-one points the transported action is entrywise Galois followed by
the conjugation supplied by the algebra descent. On projective points it is the
corresponding transport of algebra automorphisms. -/
theorem groupDescent (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)
    (σ : K ≃ₐ[k] K) :
    ∃ u : (Matrix (Fin (degree k A)) (Fin (degree k A)) K)ˣ,
      (∀ x, transportedCoefficient e σ x =
        (u : Matrix _ _ _) * σ.mapMatrix x * (↑u⁻¹ : Matrix _ _ _)) ∧
      (∀ x : normOne (R := K) hA b,
        (normOneSplit hA b e (mapNormOne hA b σ.toAlgHom x)).1 =
          (u : Matrix _ _ _) * σ.mapMatrix (normOneSplit hA b e x).1 * (↑u⁻¹ : Matrix _ _ _)) ∧
      (∀ (g : projectivePoints k A K) (x : Matrix (Fin (degree k A)) (Fin (degree k A)) K),
        projectiveSplit e (mapProjective σ.toAlgHom g) (transportedCoefficient e σ x) =
          transportedCoefficient e σ (projectiveSplit e g x)) := by
  obtain ⟨u, hu⟩ := transportedCoefficient_inner hA e σ
  refine ⟨u, hu, ?_, ?_⟩
  · intro x
    change extendSplitting e (changeCoefficients σ.toAlgHom x.1) =
      (u : Matrix _ _ _) * σ.mapMatrix (extendSplitting e x.1) * (↑u⁻¹ : Matrix _ _ _)
    rw [extendSplitting_self, extendSplitting_self, ← coefficientAut_apply]
    simpa [transportedCoefficient] using hu (e x.1)
  · intro g m
    have he : extendSplitting (R := K) e = e := AlgEquiv.ext (extendSplitting_self e)
    simp only [projectiveSplit, he, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      transportedCoefficient, AlgEquiv.restrictScalars_apply]
    change e (mapProjective σ.toAlgHom g (e.symm (e (coefficientAut σ (e.symm m))))) =
      e (coefficientAut σ (e.symm (e (g (e.symm m)))))
    rw [e.symm_apply_apply, e.symm_apply_apply, coefficientAut_apply, coefficientAut_apply,
      mapProjective_intertwine]


/-- Semilinear changes of test algebra use the very same conjugating matrix,
extended entrywise to the target test algebra. -/
theorem groupDescent_natural [Algebra K R] [IsScalarTower k K R]
    [Algebra K S] [IsScalarTower k K S]
    (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (e : BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)
    (σ : K ≃ₐ[k] K) (f : R →ₐ[k] S)
    (hf : ∀ c, f (algebraMap K R c) = algebraMap K S (σ c)) :
    ∃ u : (Matrix (Fin (degree k A)) (Fin (degree k A)) K)ˣ,
      (∀ x, transportedCoefficient e σ x =
        (u : Matrix _ _ _) * σ.mapMatrix x * (↑u⁻¹ : Matrix _ _ _)) ∧
      let U := Units.map (algebraMap K S).mapMatrix.toMonoidHom u
      let t := fun m => (U : Matrix _ _ _) * f.toRingHom.mapMatrix m * (↑U⁻¹ : Matrix _ _ _)
      (∀ x : normOne (R := R) hA b,
        (normOneSplit (R := S) hA b e (mapNormOne hA b f x)).1 =
          t (normOneSplit (R := R) hA b e x).1) ∧
      ∀ (g : projectivePoints k A R) (x : Matrix (Fin (degree k A)) (Fin (degree k A)) R),
        projectiveSplit (R := S) e (mapProjective f g) (t x) =
          t (projectiveSplit (R := R) e g x) := by
  obtain ⟨u, hu⟩ := transportedCoefficient_inner hA e σ
  let n := degree k A
  let j : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) S := (algebraMap K S).mapMatrix
  let U := Units.map j.toMonoidHom u
  let t : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) S :=
    fun m => (U : Matrix _ _ _) * f.toRingHom.mapMatrix m * (↑U⁻¹ : Matrix _ _ _)
  have hcoeff (m : Matrix (Fin n) (Fin n) K) :
      f.toRingHom.mapMatrix ((algebraMap K R).mapMatrix m) =
        (algebraMap K S).mapMatrix (σ.mapMatrix m) := by
    ext i j
    exact hf (m i j)
  have hsmul (r : R) (m : Matrix (Fin n) (Fin n) R) :
      f.toRingHom.mapMatrix (r • m) = f r • f.toRingHom.mapMatrix m := by
    ext i j
    simp [RingHom.mapMatrix_apply, smul_eq_mul]
  have ht (x : R ⊗[k] A) :
      extendSplitting e (changeCoefficients f x) = t (extendSplitting e x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r a =>
      let m := e (1 ⊗ₜ[k] a)
      have hm : transportedCoefficient e σ m = m := by
        simp only [m, transportedCoefficient, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
        change e (coefficientAut σ (e.symm (e (1 ⊗ₜ[k] a)))) = _
        rw [e.symm_apply_apply]
        change e (σ 1 ⊗ₜ[k] a) = _
        rw [map_one]
      have h := congrArg j ((hu m).symm.trans hm)
      rw [changeCoefficients, map_tmul, AlgHom.id_apply, extendSplitting_tmul, extendSplitting_tmul]
      change f r • (algebraMap K S).mapMatrix m =
        (U : Matrix _ _ _) * f.toRingHom.mapMatrix (r • (algebraMap K R).mapMatrix m) *
          (↑U⁻¹ : Matrix _ _ _)
      rw [hsmul, hcoeff, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      change j m = j (↑u) * j (σ.mapMatrix m) * (↑(U⁻¹) : Matrix (Fin n) (Fin n) S)
      have hi : (↑(U⁻¹) : Matrix (Fin n) (Fin n) S) = j (↑(u⁻¹)) :=
        congrArg Units.val ((map_inv (Units.map j.toMonoidHom) u).symm)
      rw [hi]
      simpa only [map_mul] using h.symm
    | add x y hx hy =>
      simp only [map_add, hx, hy, t, Matrix.mul_add, Matrix.add_mul]
  refine ⟨u, hu, fun x => ht x.1, ?_⟩
  intro g m
  obtain ⟨x, rfl⟩ := (extendSplitting e).surjective m
  change projectiveSplit (R := S) e (mapProjective f g) (t (extendSplitting e x)) =
    t (projectiveSplit (R := R) e g (extendSplitting e x))
  rw [← ht x]
  simp only [projectiveSplit, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply, mapProjective_intertwine]
  exact ht (g x)

section Specifications

open Specs.RM03.CSA.NormOneGroup

theorem splittingExtends : SplittingExtends.{u, v, w, z, q} := by
  intro k _ A _ _ K _ _ R _ _ _ _ ι _ hA b e
  exact ⟨extendSplitting e, extendSplitting_tmul e, normAt_eq_det hA b e⟩

theorem normOneFunctor_spec : NormOneFunctor.{u, v, w, z, q} := by
  intro k _ A _ _ ι _ hA b
  refine ⟨normOneFunctor hA b, fun _ => Equiv.refl _, fun _ => rfl,
    fun _ _ _ => rfl, fun {_ _} _ _ => rfl, ?_⟩
  intro K _ _ _ _ e
  refine ⟨fun R => extendSplitting (R := restrictTestAlgebra k K R) e,
    fun R => normOneSplit (R := restrictTestAlgebra k K R) hA b e, ?_, ?_, ?_⟩
  · intro R r a
    exact extendSplitting_tmul e r a
  · intro R x
    rfl
  · intro R S f x
    exact normOneSplit_natural (R := restrictTestAlgebra k K R)
      (S := restrictTestAlgebra k K S) hA b e f.hom x

theorem projectiveFunctor_spec : ProjectiveFunctor.{u, v, w} := by
  intro k _ A _ _
  exact ⟨projectiveFunctor k A, fun _ => MulEquiv.refl _, fun {_ _} f g x =>
    mapProjective_intertwine f.hom g x⟩

theorem projectiveField_spec : ProjectiveField.{u, v, w} := by
  intro k _ A _ _ F _ _ hA
  exact ⟨scalarUnits_normal, projectiveField hA, projectiveField_apply hA⟩

theorem projectiveSplit_spec : ProjectiveSplit.{u, v, w, q} := by
  intro k _ A _ _ K _ _ _ _ e
  refine ⟨projectiveFunctor k A, fun _ => MulEquiv.refl _,
    fun {_ _} f g x => mapProjective_intertwine f.hom g x,
    fun R => extendSplitting (R := restrictTestAlgebra k K R) e,
    fun R => projectiveSplit (R := restrictTestAlgebra k K R) e, ?_, ?_, ?_⟩
  · intro R r a
    exact extendSplitting_tmul e r a
  · intro R g x
    let d := extendSplitting (R := restrictTestAlgebra k K R) e
    change projectivePoints k A (restrictTestAlgebra k K R) at g
    change d (g (d.symm (d x))) = d (g x)
    rw [d.symm_apply_apply]
  · intro R S f g x
    exact projectiveSplit_natural (R := restrictTestAlgebra k K R)
      (S := restrictTestAlgebra k K S) e f.hom g x

theorem groupDescent_spec : GroupDescent.{u, v, z, q} := by
  intro k _ A _ _ K _ _ _ _ ι _ hA b e σ
  change IsCentralSimple k A at hA
  change BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K at e
  obtain ⟨u, hu, _, hp⟩ := groupDescent hA b e σ
  have h (x : K ⊗[k] A) :
      e (changeCoefficients σ.toAlgHom x) =
        (u : Matrix _ _ _) * σ.mapMatrix (e x) * (↑u⁻¹ : Matrix _ _ _) := by
    simpa [transportedCoefficient, coefficientAut_apply] using hu (e x)
  refine ⟨u, h, ?_, ?_⟩
  · intro x hx
    change normAt hA b x = 1 at hx
    change normAt hA b (changeCoefficients σ.toAlgHom x) = 1 ∧
      (e x).det = 1 ∧ (e (changeCoefficients σ.toAlgHom x)).det = 1
    have ht : normAt hA b (changeCoefficients σ.toAlgHom x) = 1 := by
      rw [normAt_natural, hx, map_one]
    exact ⟨ht, by
      rw [← extendSplitting_self e x, ← normAt_eq_det hA b e]
      exact hx, by
      rw [← extendSplitting_self e, ← normAt_eq_det hA b e]
      exact ht⟩
  · intro g
    let d := projectiveSplit (R := K) e (mapProjective σ.toAlgHom g)
    refine ⟨d, fun x => ?_⟩
    have he : extendSplitting (R := K) e = e := AlgEquiv.ext (extendSplitting_self e)
    have hc : projectiveSplit (R := K) e g (e x) = e (g x) := by
      simp only [projectiveSplit, he, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
        AlgEquiv.symm_apply_apply]
    have hpx := hp g (e x)
    rw [hc, hu (e x), hu (e (g x))] at hpx
    exact hpx

theorem groupDescent_natural_spec : GroupDescentNatural.{u, v, w, z, p, q} := by
  intro k _ A _ _ K _ _ _ _ R _ _ _ _ S _ _ _ _ ι _ hA b e σ f hf
  change IsCentralSimple k A at hA
  change BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K at e
  obtain ⟨u, hu, hn, hp⟩ := groupDescent_natural hA b e σ f hf
  refine ⟨u, extendSplitting e, extendSplitting e, ?_,
    extendSplitting_tmul e, extendSplitting_tmul e, ?_, ?_⟩
  · intro x
    have h := hu (e x)
    change e (coefficientAut σ (e.symm (e x))) = _ at h
    rw [e.symm_apply_apply] at h
    exact h
  · intro x hx
    exact hn ⟨x, hx⟩
  · intro g
    refine ⟨mapProjective f g, mapProjective_intertwine f g, fun x => ?_⟩
    have hpx := hp g (extendSplitting e x)
    simp only [projectiveSplit, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.symm_apply_apply] at hpx
    exact hpx

end Specifications

end RM03.CSA.NormOneGroup
