import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.RingTheory.FiniteStability

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.WeilRestriction

noncomputable section
open Algebra.TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Coordinates

variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
variable {ι σ : Type u} [Fintype ι] (b : Module.Basis ι k B)

omit [Fintype ι] in
private theorem map_coefficient {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (x : R ⊗[k] B) (j : ι) :
    (b.baseChange S).repr (tensorMap k B f x) j = f ((b.baseChange R).repr x j) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    change (b.baseChange S).repr (f r ⊗ₜ a) j = _
    simp only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, map_mul, AlgHom.commutes]
  | add _ _ hx hy => simp [hx, hy]

@[simp] private theorem tensorMap_tmul {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (r : R) (a : B) :
    tensorMap k B f (r ⊗ₜ a) = f r ⊗ₜ a := rfl

private abbrev coordinatePolynomial (k : Type u) [CommRing k] (σ ι : Type u) :=
  MvPolynomial (σ × ι) k

/-- Substitute the universal linear combination of the basis elements for each variable. -/
private def substitution (σ : Type u) :
    MvPolynomial σ B →ₐ[B] (coordinatePolynomial (k := k) (σ := σ) (ι := ι)) ⊗[k] B :=
  MvPolynomial.aeval fun i => ∑ j, MvPolynomial.X (i, j) ⊗ₜ b j

private def equations (I : Ideal (MvPolynomial σ B)) :
    Ideal (coordinatePolynomial (k := k) (σ := σ) (ι := ι)) :=
  Ideal.span (Set.range fun p : I × ι =>
    (b.baseChange _).repr (substitution b σ p.1) p.2)

/-- The coordinate algebra cut out by the basis coefficients of the relations. -/
abbrev presentationCoordinates (I : Ideal (MvPolynomial σ B)) : CommAlgCat.{u} k :=
  CommAlgCat.of k (coordinatePolynomial (k := k) (σ := σ) (ι := ι) ⧸ equations b I)

private theorem evaluate_substitution {R : CommAlgCat.{u} k} (x : σ → R ⊗[k] B) :
    (tensorMap k B (MvPolynomial.aeval fun p : σ × ι => (b.baseChange R).repr (x p.1) p.2)).comp
      (substitution b σ) = MvPolynomial.aeval x := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, substitution, MvPolynomial.aeval_X, map_sum]
  simp only [tensorMap_tmul, MvPolynomial.aeval_X]
  simpa only [Module.Basis.baseChange_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self_apply, tmul_mul_tmul, mul_one, one_mul] using
    (b.baseChange R).sum_repr (x i)

private theorem eval_equations {R : CommAlgCat.{u} k} (I : Ideal (MvPolynomial σ B))
    (g : coordinatePolynomial (k := k) (σ := σ) (ι := ι) →ₐ[k] R) :
    equations b I ≤ RingHom.ker g.toRingHom ↔
      I ≤ RingHom.ker
        (((tensorMap k B g).comp (substitution b σ)).toRingHom) := by
  rw [equations, Ideal.span_le]
  constructor
  · intro h p hp
    apply (b.baseChange R).ext_elem
    intro j
    change (b.baseChange R).repr (tensorMap k B g
      (substitution b σ p)) j = (b.baseChange R).repr 0 j
    rw [map_coefficient, map_zero, Finsupp.zero_apply]
    exact h ⟨(⟨p, hp⟩, j), rfl⟩
  · rintro h _ ⟨⟨p, j⟩, rfl⟩
    change g ((b.baseChange _).repr (substitution b σ p) j) = 0
    rw [← map_coefficient b g]
    have hz := h p.property
    change tensorMap k B g (substitution b σ p) = 0 at hz
    simp [hz]

private def homQuotient {R A : Type u} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    (I : Ideal A) : ((A ⧸ I) →ₐ[k] R) ≃ {f : A →ₐ[k] R // I ≤ RingHom.ker f.toRingHom} where
  toFun f := ⟨f.comp (Ideal.Quotient.mkₐ k I), fun _ hx => by
    change f (Ideal.Quotient.mk I _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩
  invFun f := Ideal.Quotient.liftₐ I f.1 f.2
  left_inv f := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I x
    rfl
  right_inv f := by ext x; rfl

private def polynomialHomEquiv (R : CommAlgCat.{u} k) :
    (coordinatePolynomial (k := k) (σ := σ) (ι := ι) →ₐ[k] R) ≃ (MvPolynomial σ B →ₐ[B] (R ⊗[k] B)) where
  toFun g := (tensorMap k B g).comp (substitution b σ)
  invFun f := MvPolynomial.aeval fun p : σ × ι => (b.baseChange R).repr (f (MvPolynomial.X p.1)) p.2
  left_inv g := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rw [map_coefficient]
    simp only [substitution, MvPolynomial.aeval_X, map_sum, Finsupp.finsetSum_apply,
      Module.Basis.baseChange_repr_tmul]
    classical
    simp [Module.Basis.repr_self, Finsupp.single_apply, apply_ite g]
  right_inv f := by
    dsimp only
    rw [evaluate_substitution b (R := R) (fun i => f (MvPolynomial.X i))]
    apply MvPolynomial.algHom_ext
    intro i
    simp

private def quotientPoints (I : Ideal (MvPolynomial σ B)) (R : CommAlgCat.{u} k) :
    ((coordinatePolynomial (k := k) (σ := σ) (ι := ι) ⧸ equations b I) →ₐ[k] R) ≃
      ((MvPolynomial σ B ⧸ I) →ₐ[B] (R ⊗[k] B)) :=
  (homQuotient (equations b I)).trans
    ((Equiv.subtypeEquiv (polynomialHomEquiv b R) (eval_equations b I)).trans (homQuotient I).symm)

private theorem quotientPoints_natural (I : Ideal (MvPolynomial σ B)) {R S : CommAlgCat.{u} k}
    (f : R ⟶ S) (g : (coordinatePolynomial (k := k) (σ := σ) (ι := ι) ⧸ equations b I) →ₐ[k] R) :
    quotientPoints b I S (f.hom.comp g) =
      (tensorMap k B f.hom).comp (quotientPoints b I R g) := by
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective B I x
  change tensorMap k B ((f.hom.comp g).comp (Ideal.Quotient.mkₐ k (equations b I)))
      (substitution b σ p) =
    tensorMap k B f.hom (tensorMap k B (g.comp (Ideal.Quotient.mkₐ k (equations b I)))
      (substitution b σ p))
  exact DFunLike.congr_fun (Algebra.TensorProduct.map_comp
    f.hom (g.comp (Ideal.Quotient.mkₐ k (equations b I))) (AlgHom.id k B) (AlgHom.id k B)) _

include b in
/-- Coordinate quotient obtained by expanding the relations in the chosen basis. -/
def ofPresentation [Finite σ] (A : CommAlgCat.{u} B) (f : MvPolynomial σ B →ₐ[B] A)
    (hf : Function.Surjective f) : Representation k B A := by
  let I := RingHom.ker f.toRingHom
  let e : (MvPolynomial σ B ⧸ I) ≃ₐ[B] A :=
    Ideal.quotientKerAlgEquivOfSurjective hf
  refine ⟨presentationCoordinates b I, inferInstance, NatIso.ofComponents
    (fun R => Equiv.toIso {
      toFun := fun g => CommAlgCat.ofHom ((quotientPoints b I R g.hom).comp e.symm.toAlgHom)
      invFun := fun h => CommAlgCat.ofHom ((quotientPoints b I R).symm (h.hom.comp e.toAlgHom))
      left_inv := by
        intro g
        apply CommAlgCat.hom_ext
        change (quotientPoints b I R).symm
          (((quotientPoints b I R) g.hom).comp e.symm.toAlgHom |>.comp e.toAlgHom) = g.hom
        simp [AlgHom.comp_assoc]
      right_inv := by
        intro h
        apply CommAlgCat.hom_ext
        change ((quotientPoints b I R) ((quotientPoints b I R).symm
          (h.hom.comp e.toAlgHom))).comp e.symm.toAlgHom = h.hom
        rw [Equiv.apply_symm_apply]
        ext x
        simp }) ?_⟩
  intro R S a
  apply ConcreteCategory.hom_ext
  intro g
  change CommAlgCat.ofHom ((quotientPoints b I S (a.hom.comp g.hom)).comp e.symm.toAlgHom) =
    CommAlgCat.ofHom ((tensorMap k B a.hom).comp
      ((quotientPoints b I R g.hom).comp e.symm.toAlgHom))
  rw [quotientPoints_natural]
  rfl

include b in
/-- Construct the restriction using a finite basis and any finite polynomial presentation. -/
def ofBasis (A : CommAlgCat.{u} B) [Algebra.FiniteType B A] :
    Representation k B A :=
  let h := (Algebra.FiniteType.iff_quotient_mvPolynomial').mp (inferInstance : Algebra.FiniteType B A)
  haveI := h.choose_spec.choose
  ofPresentation b A h.choose_spec.choose_spec.choose h.choose_spec.choose_spec.choose_spec

/-- The affine restriction for finite free scalar algebras. -/
theorem representability : LinearAlgebraicGroups.Specs.WeilRestriction.Representability.{u} := by
  intro k B _ _ _ _ _ A _
  exact ⟨ofBasis (Module.Free.chooseBasis k B) A⟩

end Coordinates

section Uniqueness

variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
variable {A : CommAlgCat.{u} B}

/-- The unique comparison of coordinate algebras inducing the given representation. -/
def coordinateIso (P Q : Representation k B A) : P.coordinate ≅ Q.coordinate :=
  (Coyoneda.fullyFaithful.preimageIso (Q.points ≪≫ P.points.symm)).unop

theorem coordinateIso_compatible (P Q : Representation k B A) :
    Compatible P Q (coordinateIso P Q) := by
  intro R f
  have h := Coyoneda.fullyFaithful.map_preimage (Q.points ≪≫ P.points.symm).hom
  have hf := congrArg (fun t => t.app R f) h
  change (coordinateIso P Q).hom ≫ f = P.points.inv.app R (Q.points.hom.app R f) at hf
  rw [hf]
  exact P.points.app R |>.toEquiv.apply_symm_apply _

theorem basisIndependence : LinearAlgebraicGroups.Specs.WeilRestriction.BasisIndependence.{u} := by
  intro k B _ _ _ A P Q
  refine ⟨coordinateIso P Q, coordinateIso_compatible P Q, ?_⟩
  intro e he
  apply Iso.ext
  have h := he Q.coordinate (𝟙 _)
  have h' := coordinateIso_compatible P Q Q.coordinate (𝟙 _)
  simp only [Category.comp_id] at h h'
  exact (P.points.app Q.coordinate).toEquiv.injective (h.trans h'.symm)

end Uniqueness

section Schemes

variable {k : Type u} [CommRing k]

private theorem spectrum_finiteType (A : CommAlgCat.{u} k) :
    LocallyOfFiniteType ((algSpec (CommRingCat.of k)).obj (op A)).hom ↔ Algebra.FiniteType k A := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔ _
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap

/-- Regard finite-type coordinates as an affine finite-type scheme. -/
def affineSpectrum (A : CommAlgCat.{u} k) (hA : Algebra.FiniteType k A) :
    AffineFiniteTypeScheme k :=
  ⟨(algSpec (CommRingCat.of k)).obj (op A),
    by
      change IsAffine (Spec (CommRingCat.of A))
      infer_instance,
    (spectrum_finiteType A).mpr hA, by
      change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      infer_instance⟩

/-- The affine coordinate description of the scheme points. -/
def spectrumPoints (A : CommAlgCat.{u} k) (X : Over (Spec (CommRingCat.of k)))
    (e : (algSpec (CommRingCat.of k)).obj (op A) ≅ X) :
    coyoneda.obj (op A) ≅ schemePoints k X :=
  NatIso.ofComponents (fun R => Equiv.toIso
    ((CategoryTheory.opEquiv (op R) (op A)).symm.trans
      ((algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv.trans
        { toFun := (· ≫ e.hom)
          invFun := (· ≫ e.inv)
          left_inv := by intro f; simp
          right_inv := by
            intro f
            simp }))) (by
    intro R S a
    apply ConcreteCategory.hom_ext
    intro f
    let S := algSpec (CommRingCat.of k)
    change S.map (f ≫ a).op ≫ e.hom = S.map a.op ≫ (S.map f.op ≫ e.hom)
    rw [← Category.assoc, ← Functor.map_comp]
    rfl)

private def affineCoordinates (X : AffineFiniteTypeScheme k) :
    {A : CommAlgCat.{u} k // Algebra.FiniteType k A ∧
      Nonempty ((algSpec (CommRingCat.of k)).obj (op A) ≅ X.val)} := by
  let E := AlgebraicGeometry.essImage_algSpec.mpr X.property.1
  let A := E.choose.unop
  let e := E.choose_spec.some
  refine ⟨A, (spectrum_finiteType A).mp ?_, ⟨e⟩⟩
  have h : e.hom.left ≫ X.val.hom = ((algSpec (CommRingCat.of k)).obj (op A)).hom :=
    Over.w e.hom
  rw [← h]
  let _ := X.property.2.1
  infer_instance

variable (k) (K : Type u) [CommRing K] [Algebra k K] [Module.Free k K] [Module.Finite k K]

/-- The affine Weil restriction and the point identification for the chosen representative. -/
def schemeRepresentation (X : AffineFiniteTypeScheme K) :
    Σ Y : AffineFiniteTypeScheme k, schemePoints k Y.val ≅ schemeRestrictionFunctor k K X.val := by
  let C := affineCoordinates X
  letI := C.property.1
  let P := ofBasis (Module.Free.chooseBasis k K) C.val
  let Y := affineSpectrum P.coordinate P.finiteType
  exact ⟨Y, (spectrumPoints P.coordinate Y.val (Iso.refl _)).symm ≪≫ P.points ≪≫
    Functor.isoWhiskerLeft (extendScalars k K) (spectrumPoints C.val X.val C.property.2.some)⟩

theorem schemeRepresentability :
    LinearAlgebraicGroups.Specs.WeilRestriction.SchemeRepresentability.{u} := by
  intro k K _ _ _ _ X
  exact ⟨(schemeRepresentation k K X).1, ⟨(schemeRepresentation k K X).2⟩⟩

end Schemes

section BaseChange

variable {k B L : Type u} [CommRing k] [CommRing B] [CommRing L] [Algebra k B] [Algebra k L]

local instance scalarAlgebraOnTensor (R : CommAlgCat.{u} L) :
    Algebra B (R ⊗[L] (L ⊗[k] B)) :=
  ((algebraMap (L ⊗[k] B) (R ⊗[L] (L ⊗[k] B))).comp (algebraMap B (L ⊗[k] B))).toAlgebra

local instance scalarTowerOnTensor (R : CommAlgCat.{u} L) :
    IsScalarTower B (L ⊗[k] B) (R ⊗[L] (L ⊗[k] B)) :=
  IsScalarTower.of_algebraMap_eq' rfl

private def scalarTensorComparison (R : CommAlgCat.{u} L) :
    R ⊗[L] (L ⊗[k] B) ≃ₐ[B] ((restrictScalars k L).obj R) ⊗[k] B := by
  refine { tensorCancellation k B L R with commutes' := ?_ }
  intro b
  change tensorCancellation k B L R (1 ⊗ₜ[L] (1 ⊗ₜ[k] b)) = 1 ⊗ₜ[k] b
  simp [tensorCancellation]

private def restrictedPure (R : CommAlgCat.{u} L) (r : R) (b : B) :
    ((restrictScalars k L).obj R) ⊗[k] B :=
  letI : Algebra k R := ((restrictScalars k L).obj R).algebra
  r ⊗ₜ[k] b

@[simp] private theorem scalarTensorComparison_tmul (R : CommAlgCat.{u} L)
    (r : R) (l : L) (b : B) :
    scalarTensorComparison (k := k) R (r ⊗ₜ[L] (l ⊗ₜ[k] b)) =
      restrictedPure (k := k) R (l • r) b := by
  let _ : Algebra k R := ((restrictScalars k L).obj R).algebra
  let _ : IsScalarTower k L R := IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.TensorProduct.cancelBaseChange_tmul k L L R B r l b

private theorem scalarTensorComparison_natural {R S : CommAlgCat.{u} L} (f : R ⟶ S)
    (x : R ⊗[L] (L ⊗[k] B)) :
    scalarTensorComparison (k := k) S (tensorMap L (L ⊗[k] B) f.hom x) =
      tensorMap k B ((restrictScalars k L).map f).hom (scalarTensorComparison (k := k) (B := B) R x) := by
  induction x using TensorProduct.inductionOn with
  | add _ _ hx hy => simp [hx, hy]
  | tmul r z =>
    simp only [tensorMap_tmul]
    induction z using TensorProduct.inductionOn with
    | add _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul l b =>
      rw [scalarTensorComparison_tmul, scalarTensorComparison_tmul]
      let _ : Algebra k R := ((restrictScalars k L).obj R).algebra
      let _ : Algebra k S := ((restrictScalars k L).obj S).algebra
      change (l • f.hom r) ⊗ₜ[k] b =
        tensorMap k B ((restrictScalars k L).map f).hom ((l • r) ⊗ₜ[k] b)
      rw [tensorMap_tmul]
      exact congrArg (fun r' : S => r' ⊗ₜ[k] b) (f.hom.toLinearMap.map_smul l r).symm

/-- At every test algebra over the new base, restriction uses the tensor product
of the scalar algebra with that base. -/
def changedPoints (A : CommAlgCat.{u} B) :
    restrictionFunctor L (L ⊗[k] B) (changedCoordinates k B L A) ≅
      restrictScalars k L ⋙ restrictionFunctor k B A :=
  NatIso.ofComponents (fun R => Equiv.toIso {
    toFun := fun h => CommAlgCat.ofHom ((scalarTensorComparison (k := k) (B := B) R).toAlgHom.comp
      ((AlgHom.liftEquiv B (L ⊗[k] B) A (R ⊗[L] (L ⊗[k] B))).symm h.hom))
    invFun := fun h => CommAlgCat.ofHom ((AlgHom.liftEquiv B (L ⊗[k] B) A (R ⊗[L] (L ⊗[k] B)))
      ((scalarTensorComparison (k := k) (B := B) R).symm.toAlgHom.comp h.hom))
    left_inv := by
      intro h
      apply CommAlgCat.hom_ext
      let E := AlgHom.liftEquiv B (L ⊗[k] B) A (R ⊗[L] (L ⊗[k] B))
      apply E.symm.injective
      change E.symm (E ((scalarTensorComparison (k := k) (B := B) R).symm.toAlgHom.comp
        ((scalarTensorComparison (k := k) (B := B) R).toAlgHom.comp (E.symm h.hom)))) = E.symm h.hom
      rw [Equiv.symm_apply_apply]
      ext a
      exact (scalarTensorComparison (k := k) (B := B) R).symm_apply_apply _
    right_inv := by
      intro h
      apply CommAlgCat.hom_ext
      let E := AlgHom.liftEquiv B (L ⊗[k] B) A (R ⊗[L] (L ⊗[k] B))
      change (scalarTensorComparison (k := k) (B := B) R).toAlgHom.comp
        (E.symm (E ((scalarTensorComparison (k := k) (B := B) R).symm.toAlgHom.comp h.hom))) = h.hom
      rw [Equiv.symm_apply_apply]
      ext a
      exact (scalarTensorComparison (k := k) (B := B) R).apply_symm_apply _ }) (by
    intro R S f
    apply ConcreteCategory.hom_ext
    intro h
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    change scalarTensorComparison (k := k) (B := B) S
        (tensorMap L (L ⊗[k] B) f.hom (h.hom (1 ⊗ₜ[B] a))) =
      tensorMap k B ((restrictScalars k L).map f).hom
        (scalarTensorComparison (k := k) (B := B) R (h.hom (1 ⊗ₜ[B] a)))
    exact scalarTensorComparison_natural f _)

private def changedRepresentable (C : CommAlgCat.{u} k) :
    coyoneda.obj (op (CommAlgCat.of L (L ⊗[k] C))) ≅
      restrictScalars k L ⋙ coyoneda.obj (op C) :=
  NatIso.ofComponents (fun R =>
    let S := (restrictScalars k L).obj R
    letI : Algebra k R := S.algebra
    letI : IsScalarTower k L R := IsScalarTower.of_algebraMap_eq' rfl
    let E := AlgHom.liftEquiv k L C R
    Equiv.toIso {
      toFun := restrictCoordinatePoint k L
      invFun := fun h => CommAlgCat.ofHom (E h.hom)
      left_inv := fun h => CommAlgCat.hom_ext (E.apply_symm_apply h.hom)
      right_inv := fun h => CommAlgCat.hom_ext (E.symm_apply_apply h.hom) }) (by
    intro R S f
    apply ConcreteCategory.hom_ext
    intro h
    apply CommAlgCat.hom_ext
    exact AlgHom.ext fun a => rfl)

theorem finiteFreeAfterBaseChange :
    LinearAlgebraicGroups.Specs.WeilRestriction.FiniteFreeAfterBaseChange.{u} := by
  intro k B L _ _ _ _ _ _ _
  let b := (Module.Free.chooseBasis k B).baseChange L
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- Base change of the representing algebra, carrying its canonical point identification. -/
def changeRepresentation {A : CommAlgCat.{u} B} (P : Representation k B A) :
    Representation L (L ⊗[k] B) (changedCoordinates k B L A) := by
  letI := P.finiteType
  exact ⟨CommAlgCat.of L (L ⊗[k] P.coordinate), inferInstance,
    changedRepresentable P.coordinate ≪≫
      Functor.isoWhiskerLeft (restrictScalars k L) P.points ≪≫ (changedPoints A).symm⟩

theorem coordinateBaseChange :
    LinearAlgebraicGroups.Specs.WeilRestriction.CoordinateBaseChange.{u} := by
  intro k B L _ _ _ _ _ A P
  let Q := changeRepresentation (L := L) P
  refine ⟨Q.finiteType, Q.points, ?_⟩
  intro R f a
  let e := changedPoints (k := k) (L := L) A
  have h := (e.app R).toEquiv.apply_symm_apply
    (P.points.hom.app ((restrictScalars k L).obj R) (restrictCoordinatePoint k L f))
  exact congrArg (fun g => g.hom a) h

private theorem pullback_affine_finiteType (Y : AffineFiniteTypeScheme k) :
    let Z := (pullbackScalars k L).obj Y.val
    IsAffine Z.left ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom := by
  let _ := Y.property.1
  let _ := Y.property.2.1
  let _ := Y.property.2.2
  let f := Spec.map (CommRingCat.ofHom (algebraMap k L))
  change IsAffine (Limits.pullback Y.val.hom f) ∧
    LocallyOfFiniteType (Limits.pullback.snd Y.val.hom f) ∧
    QuasiCompact (Limits.pullback.snd Y.val.hom f)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Pulling back an affine spectrum gives the spectrum of the scalar-extended algebra. -/
def spectrumPullbackIso (C : CommAlgCat.{u} k) :
    (pullbackScalars k L).obj ((algSpec (CommRingCat.of k)).obj (op C)) ≅
      (algSpec (CommRingCat.of L)).obj (op (CommAlgCat.of L (L ⊗[k] C))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  refine Over.isoMk (Limits.pullbackSymmetry f g ≪≫ pullbackSpecIso k L C) ?_
  change ((Limits.pullbackSymmetry f g).hom ≫ (pullbackSpecIso k L C).hom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[k] C))) = Limits.pullback.snd f g
  rw [Category.assoc, pullbackSpecIso_hom_fst', Limits.pullbackSymmetry_hom_comp_fst]

/-- The geometric pullback still represents restriction along the base-changed scalar algebra. -/
theorem schemePullbackRepresentability :
    LinearAlgebraicGroups.Specs.WeilRestriction.SchemePullbackRepresentability.{u} := by
  intro k B L _ _ _ _ _ X Y e
  obtain ⟨hAffine, hFiniteType, hQuasiCompact⟩ := pullback_affine_finiteType (L := L) Y
  let A := affineCoordinates X
  let C := affineCoordinates Y
  let iX := A.property.2.some
  let iY := C.property.2.some
  let P : Representation k B A.val :=
    ⟨C.val, C.property.1, spectrumPoints C.val Y.val iY ≪≫ e ≪≫
      Functor.isoWhiskerLeft (extendScalars k B) (spectrumPoints A.val X.val iX).symm⟩
  let iZ := (spectrumPullbackIso (L := L) C.val).symm ≪≫ (pullbackScalars k L).mapIso iY
  let iX' := (spectrumPullbackIso (L := L ⊗[k] B) A.val).symm ≪≫
    (pullbackScalars B (L ⊗[k] B)).mapIso iX
  exact ⟨hAffine, hFiniteType, hQuasiCompact,
    ⟨(spectrumPoints _ _ iZ).symm ≪≫ (changeRepresentation P).points ≪≫
      Functor.isoWhiskerLeft (extendScalars L (L ⊗[k] B)) (spectrumPoints _ _ iX')⟩⟩

end BaseChange

section SchemeBaseChange

variable {k B L : Type u} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]

private def baseChangePointIso (X : SchemeOver k) :
    pointsFunctor ((baseChange k L).obj X) ≅ restrictTestAlgebra k L ⋙ pointsFunctor X :=
  NatIso.ofComponents (fun R => Equiv.toIso (baseChangePointsEquiv L X R)) (by
    intro R S f
    apply ConcreteCategory.hom_ext
    intro p
    exact baseChangePointsNaturality k L X f p)

theorem schemeBaseChange :
    LinearAlgebraicGroups.Specs.WeilRestriction.SchemeBaseChange.{u} := by
  intro k B L _ _ _ _ _ A Y e
  obtain ⟨hAffine, hFiniteType, hQuasiCompact⟩ := pullback_affine_finiteType (L := L) Y
  let β := baseChangePointIso Y.val ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k L) e
  let γ := changedPoints (k := k) (L := L) A
  refine ⟨hAffine, hFiniteType, hQuasiCompact, β ≪≫ γ.symm, ?_⟩
  intro R p a
  have h := (γ.app R).toEquiv.apply_symm_apply (β.hom.app R p)
  exact congrArg (fun g => g.hom a) h

end SchemeBaseChange

section Groups

variable {k : Type u} [Field k]

private def transportGroupLaw {X : SchemeOver k} (F : TestAlgebra k ⥤ GrpCat.{u})
    (e : pointsFunctor X ≅ F ⋙ forget GrpCat) : NaturalGroupLaw X where
  group R := (e.app R).toEquiv.group
  map_one {R S} a := by
    let eR : Points X R ≃ F.obj R := (e.app R).toEquiv
    let eS : Points X S ≃ F.obj S := (e.app S).toEquiv
    have hn (p : Points X R) : eS (mapPoints a p) = F.map a (eR p) :=
      e.hom.naturality_apply a p
    apply eS.injective
    change eS (mapPoints a (eR.symm 1)) = eS (eS.symm 1)
    rw [hn]
    simp
  map_mul {R S} a p q := by
    let eR : Points X R ≃ F.obj R := (e.app R).toEquiv
    let eS : Points X S ≃ F.obj S := (e.app S).toEquiv
    have hn (x : Points X R) : eS (mapPoints a x) = F.map a (eR x) :=
      e.hom.naturality_apply a x
    apply eS.injective
    change eS (mapPoints a (eR.symm (eR p * eR q))) =
      eS (eS.symm (eS (mapPoints a p) * eS (mapPoints a q)))
    simp [hn]

/-- The group scheme induced by a natural group law on a represented functor. -/
abbrev groupFromPoints (Y : AffineFiniteTypeScheme k) (F : TestAlgebra k ⥤ GrpCat.{u})
    (e : pointsFunctor Y.val ≅ F ⋙ forget GrpCat) : AffineAlgebraicGroup k :=
  ⟨Grp.mk Y.val (grp := (groupLawEquiv Y.val Y.property.1).symm (transportGroupLaw F e)),
    Y.property⟩

/-- The induced affine group scheme realizes the original group operations on points. -/
def groupFromPointsIso (Y : AffineFiniteTypeScheme k) (F : TestAlgebra k ⥤ GrpCat.{u})
    (e : pointsFunctor Y.val ≅ F ⋙ forget GrpCat) :
    (groupPointsFunctor k).obj (groupFromPoints Y F e).val ≅ F :=
  NatIso.ofComponents (fun R => MulEquiv.toGrpIso
    { (e.app R).toEquiv with
      map_mul' := fun p q => by
        let s := (groupLawEquiv Y.val Y.property.1).symm (transportGroupLaw F e)
        have h : inducedGroupLaw Y.val s = transportGroupLaw F e :=
          (groupLawEquiv Y.val Y.property.1).apply_symm_apply _
        change e.hom.app R ((inducedGroupLaw Y.val s).group R |>.mul p q) =
          e.hom.app R p * e.hom.app R q
        rw [h]
        exact (e.app R).toEquiv.apply_symm_apply _ }) (by
    intro R S a
    apply GrpCat.ext
    intro p
    exact e.hom.naturality_apply a p)

variable (k) (K : Type u) [Field K] [Algebra k K] [Module.Finite k K]

/-- Restriction of scalars of an affine algebraic group. -/
def groupRepresentation (G : AffineAlgebraicGroup K) :
    Σ H : AffineAlgebraicGroup k, (groupPointsFunctor k).obj H.val ≅
      extendScalars k K ⋙ (groupPointsFunctor K).obj G.val := by
  let W := schemeRepresentation k K ⟨G.val.X, G.property⟩
  let F := extendScalars k K ⋙ (groupPointsFunctor K).obj G.val
  let e : pointsFunctor W.1.val ≅ F ⋙ forget GrpCat := W.2
  exact ⟨groupFromPoints W.1 F e, groupFromPointsIso W.1 F e⟩

theorem groupRepresentability : LinearAlgebraicGroups.Specs.WeilRestriction.GroupRepresentability.{u} := by
  intro k K _ _ _ _ G
  exact ⟨(groupRepresentation k K G).1, ⟨(groupRepresentation k K G).2⟩⟩

end Groups

section Norm

variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
variable [Module.Free k B] [Module.Finite k B]

/-- The determinant of multiplication commutes with arbitrary test-algebra maps. -/
theorem normNaturality : LinearAlgebraicGroups.Specs.WeilRestriction.NormNaturality.{u} := by
  intro k B _ _ _ _ _ R S f x
  classical
  let b := Module.Free.chooseBasis k B
  change f.hom (Algebra.norm R x) = Algebra.norm S (tensorMap k B f.hom x)
  rw [Algebra.norm_eq_matrix_det (b.baseChange R), Algebra.norm_eq_matrix_det (b.baseChange S)]
  change f.hom.toRingHom _ = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
  calc
    _ = (b.baseChange S).repr
          (tensorMap k B f.hom (x * b.baseChange R j)) i :=
      (map_coefficient b f.hom _ i).symm
    _ = _ := by simp

/-- A scalar-extended element is invertible exactly when its multiplication determinant is. -/
theorem normDetectsUnits : LinearAlgebraicGroups.Specs.WeilRestriction.NormDetectsUnits.{u} := by
  intro k B _ _ _ _ _ R x
  refine ⟨?_, fun h => h.map (pointNorm k B R)⟩
  classical
  let b := (Module.Free.chooseBasis k B).baseChange R
  change IsUnit (Algebra.norm R x) → _
  rw [Algebra.norm_eq_matrix_det b]
  intro h
  let e := (Algebra.leftMulMatrix b x).toLinearEquiv b h
  obtain ⟨y, hy⟩ := e.surjective 1
  refine isUnit_iff_exists_inv.mpr ⟨y, ?_⟩
  simpa only [e, Matrix.toLinearEquiv_apply, Algebra.leftMulMatrix_apply,
    Matrix.toLin_toMatrix, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using hy

end Norm

section Units

open LinearAlgebraicGroups.Specs.StandardGroups (multiplicativePoints)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {ι : Type u} [Fintype ι] (b : Module.Basis ι k K)

private def polynomialPoints (R : TestAlgebra k) :
    (MvPolynomial ι k →ₐ[k] R) ≃ (R ⊗[k] K) where
  toFun f := tensorMap k K f (genericElement b)
  invFun x := MvPolynomial.aeval ((b.baseChange R).repr x)
  left_inv f := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [MvPolynomial.aeval_X]
    change (b.baseChange R).repr (tensorMap k K f (genericElement b)) j = f (MvPolynomial.X j)
    classical
    simp [genericElement, Finsupp.finsetSum_apply, Module.Basis.repr_self, Finsupp.single_apply]
  right_inv x := by
    change tensorMap k K (MvPolynomial.aeval ((b.baseChange R).repr x)) (genericElement b) = x
    simp only [genericElement, map_sum, tensorMap_tmul, MvPolynomial.aeval_X]
    simpa only [Module.Basis.baseChange_apply, Algebra.smul_def,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      tmul_mul_tmul, mul_one, one_mul] using (b.baseChange R).sum_repr x

private abbrev localizationMap : MvPolynomial ι k →ₐ[k] NormCoordinates b :=
  Algebra.algHom k _ _

private def localizationHom (R : TestAlgebra k) :
    (NormCoordinates b →ₐ[k] R) ≃
      {f : MvPolynomial ι k →ₐ[k] R // IsUnit (f (normPolynomial b))} where
  toFun f := ⟨f.comp (localizationMap b),
    (IsLocalization.Away.algebraMap_isUnit (S := NormCoordinates b) (normPolynomial b)).map f⟩
  invFun f := IsLocalization.Away.liftAlgHom (normPolynomial b) f.2
  left_inv f := by
    apply IsLocalization.algHom_ext (Submonoid.powers (normPolynomial b))
    apply AlgHom.ext
    intro a
    let hu := (IsLocalization.Away.algebraMap_isUnit (S := NormCoordinates b)
      (normPolynomial b)).map f
    exact IsLocalization.Away.lift_eq (g := (f.comp (localizationMap b)).toRingHom)
      (normPolynomial b) hu a
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    exact IsLocalization.Away.lift_eq (g := f.1.toRingHom) (normPolynomial b) f.2 a

private def unitsSubtype {A : Type u} [CommRing A] : {x : A // IsUnit x} ≃ Aˣ where
  toFun x := x.property.unit
  invFun x := ⟨x.val, x.isUnit⟩
  left_inv x := Subtype.ext x.property.unit_spec
  right_inv x := Units.ext x.isUnit.unit_spec

private theorem normPolynomial_eval (R : TestAlgebra k) (f : MvPolynomial ι k →ₐ[k] R) :
    IsUnit (f (normPolynomial b)) ↔ IsUnit (polynomialPoints b R f) := by
  let _ := Module.Finite.of_basis b
  have he : f (normPolynomial b) = pointNorm k K R (polynomialPoints b R f) :=
    normNaturality k K (CommAlgCat.ofHom f) (genericElement b)
  rw [he]
  exact normDetectsUnits k K R _

private def unitPointsEquiv (R : TestAlgebra k) : (NormCoordinates b →ₐ[k] R) ≃ (R ⊗[k] K)ˣ :=
  (localizationHom b R).trans
    ((Equiv.subtypeEquiv (polynomialPoints b R) (normPolynomial_eval b R)).trans unitsSubtype)

private theorem unitPointsEquiv_val (R : TestAlgebra k) (f : NormCoordinates b →ₐ[k] R) :
    (unitPointsEquiv b R f).val = tensorMap k K (f.comp (localizationMap b)) (genericElement b) :=
  ((normPolynomial_eval b R _).mp ((localizationHom b R f).property)).unit_spec

private def localizationPoints :
    coyoneda.obj (op (CommAlgCat.of k (NormCoordinates b))) ≅
      extendedUnits k K ⋙ forget GrpCat :=
  NatIso.ofComponents (fun R => Equiv.toIso
    (({ toFun := CommAlgCat.Hom.hom
        invFun := CommAlgCat.ofHom
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } :
      ((CommAlgCat.of k (NormCoordinates b)) ⟶ R) ≃ (NormCoordinates b →ₐ[k] R)).trans
        (unitPointsEquiv b R))) (by
    intro R S f
    apply ConcreteCategory.hom_ext
    intro g
    apply Units.ext
    change (unitPointsEquiv b S (f.hom.comp g.hom)).val =
      tensorMap k K f.hom (unitPointsEquiv b R g.hom).val
    rw [unitPointsEquiv_val, unitPointsEquiv_val]
    exact DFunLike.congr_fun (Algebra.TensorProduct.map_comp f.hom
      (g.hom.comp (localizationMap b)) (AlgHom.id k K) (AlgHom.id k K)) _)

private def openNormScheme : AffineFiniteTypeScheme k :=
  affineSpectrum (CommAlgCat.of k (NormCoordinates b)) inferInstance

private def openNormPoints :
    pointsFunctor (openNormScheme b).val ≅ extendedUnits k K ⋙ forget GrpCat :=
  (spectrumPoints (CommAlgCat.of k (NormCoordinates b)) (openNormScheme b).val
    (Iso.refl _)).symm ≪≫ localizationPoints b

/-- The group of units, represented by the principal open of the norm polynomial. -/
def openNormGroup : AffineAlgebraicGroup k :=
  groupFromPoints (openNormScheme b) (extendedUnits k K) (openNormPoints b)

def openNormGroupPoints : (groupPointsFunctor k).obj (openNormGroup b).val ≅ extendedUnits k K :=
  groupFromPointsIso _ _ (openNormPoints b)

theorem normOpenImmersion : LinearAlgebraicGroups.Specs.WeilRestriction.NormOpenImmersion.{u} := by
  intro k K ι _ _ _ _ b
  exact ⟨inferInstance, Scheme.Hom.opensRange_localizationAway
    (R := CommRingCat.of (MvPolynomial ι k)) (normPolynomial b)⟩

theorem openNormLocus : LinearAlgebraicGroups.Specs.WeilRestriction.OpenNormLocus.{u} := by
  intro k K ι _ _ _ _ b
  refine ⟨openNormGroup b, openNormGroupPoints b, Iso.refl _, ?_⟩
  intro R f j
  have hf : (openNormGroupPoints b).hom.app R
        ((testSpec k).map (CommAlgCat.ofHom f).op ≫ (Iso.refl _).hom) =
      unitPointsEquiv b R f := by
    change (openNormPoints b).hom.app R
        ((testSpec k).map (CommAlgCat.ofHom f).op ≫ (Iso.refl _).hom) = _
    have h := ((spectrumPoints (CommAlgCat.of k (NormCoordinates b))
      (openNormScheme b).val (Iso.refl _)).app R).toEquiv.symm_apply_apply (CommAlgCat.ofHom f)
    change (spectrumPoints (CommAlgCat.of k (NormCoordinates b)) (openNormScheme b).val
      (Iso.refl _)).inv.app R ((testSpec k).map (CommAlgCat.ofHom f).op ≫ (Iso.refl _).hom) = _ at h
    exact congrArg ((localizationPoints b).hom.app R) h
  rw [hf, unitPointsEquiv_val]
  have he := (polynomialPoints b R).left_inv (f.comp (localizationMap b))
  exact (MvPolynomial.aeval_X _ _).symm.trans
    (congrArg (fun g : MvPolynomial ι k →ₐ[k] R => g (MvPolynomial.X j)) he)

variable (k K) [Module.Finite k K]

/-- The determinant norm on units as a natural transformation of group functors. -/
def unitNorm : extendedUnits k K ⟶ multiplicativePoints k where
  app R := GrpCat.ofHom (Units.map (pointNorm k K R))
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    apply Units.ext
    exact (normNaturality k K f x.val).symm

/-- The affine group representing restriction of scalars of the canonical multiplicative group. -/
def multiplicativeRestriction : AffineAlgebraicGroup k :=
  openNormGroup (Module.Free.chooseBasis k K)

def multiplicativeRestrictionUnits :
    (groupPointsFunctor k).obj (multiplicativeRestriction k K).val ≅ extendedUnits k K :=
  openNormGroupPoints (Module.Free.chooseBasis k K)

def multiplicativeRestrictionPoints :
    (groupPointsFunctor k).obj (multiplicativeRestriction k K).val ≅
      extendScalars k K ⋙
        (groupPointsFunctor K).obj (StandardGroups.multiplicativeGroup K).val :=
  multiplicativeRestrictionUnits k K ≪≫
    Functor.isoWhiskerLeft (extendScalars k K) (StandardGroups.multiplicativeGroupPointsIso K).symm

/-- The group scheme homomorphism realizing the determinant on all test-algebra points. -/
def normHom (G H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj G.val ≅ extendedUnits k K)
    (t : (groupPointsFunctor k).obj H.val ≅ multiplicativePoints k) :
    G.val ⟶ H.val :=
  (G.groupHomEquiv H).symm (e.hom ≫ unitNorm k K ≫ t.inv)

theorem normHom_apply (G H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj G.val ≅ extendedUnits k K)
    (t : (groupPointsFunctor k).obj H.val ≅ multiplicativePoints k)
    (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj G.val).obj R) :
    (t.hom.app R (((groupPointsFunctor k).map (normHom k K G H e t)).app R x) : Rˣ).val =
      pointNorm k K R (e.hom.app R x : (R ⊗[k] K)ˣ).val := by
  have h : (groupPointsFunctor k).map (normHom k K G H e t) =
      e.hom ≫ unitNorm k K ≫ t.inv := (G.groupHomEquiv H).apply_symm_apply _
  rw [h]
  exact congrArg (fun a : Rˣ => a.val)
    ((t.app R).groupIsoToMulEquiv.apply_symm_apply ((unitNorm k K).app R (e.hom.app R x)))

theorem normHomomorphism : LinearAlgebraicGroups.Specs.WeilRestriction.NormHomomorphism.{u} := by
  intro k K _ _ _ _ G H e t
  exact ⟨normHom k K G H e t, normHom_apply k K G H e t⟩

theorem multiplicativeRestrictionNorm :
    LinearAlgebraicGroups.Specs.WeilRestriction.MultiplicativeRestrictionNorm.{u} := by
  intro k K _ _ _ _ G H s t
  let W := multiplicativeRestriction k K
  let v := multiplicativeRestrictionUnits k K
  refine ⟨W, v ≪≫ Functor.isoWhiskerLeft (extendScalars k K) s.symm,
    normHom k K W H v t, ?_⟩
  intro R x
  have h := (s.app ((extendScalars k K).obj R)).groupIsoToMulEquiv.apply_symm_apply
    (v.hom.app R x)
  exact (normHom_apply k K W H v t R x).trans
    (congrArg (fun u : (R ⊗[k] K)ˣ => pointNorm k K R u.val) h.symm)

/-- The norm from the Weil restriction of the multiplicative group to the canonical multiplicative group. -/
def norm : (multiplicativeRestriction k K).val ⟶ (StandardGroups.multiplicativeGroup k).val :=
  normHom k K _ _ (multiplicativeRestrictionUnits k K) (StandardGroups.multiplicativeGroupPointsIso k)

theorem norm_apply (R : TestAlgebra k)
    (x : ((groupPointsFunctor k).obj (multiplicativeRestriction k K).val).obj R) :
    ((StandardGroups.multiplicativeGroupPointsIso k).hom.app R
      (((groupPointsFunctor k).map (norm k K)).app R x) : Rˣ).val =
        pointNorm k K R ((multiplicativeRestrictionUnits k K).hom.app R x : (R ⊗[k] K)ˣ).val :=
  normHom_apply k K _ _ (multiplicativeRestrictionUnits k K)
    (StandardGroups.multiplicativeGroupPointsIso k) R x

end Units

end
end LinearAlgebraicGroups.WeilRestriction
