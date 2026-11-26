import LinearAlgebraicGroups.Affine.HopfAlgebras
import Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

open CategoryTheory Opposite AlgebraicGeometry Coalgebra HopfAlgebra WithConv
open scoped TensorProduct Ring

set_option maxHeartbeats 1000000

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable {k : Type u} [Field k]

namespace StandardGroups

open Algebra.TensorProduct
open Specs.StandardGroups

private def spectrumPointsIso {A : Type u} [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] {F : TestAlgebra k ⥤ GrpCat.{u}}
    (c : convolutionPoints (CommHopfAlgCat.of k A) ≅ F) :
    (groupPointsFunctor k).obj (spectrum k A).val ≅ F :=
  (hopfSpecPointIso (CommHopfAlgCat.of k A)).symm ≪≫ c

/-- Convert an evaluation isomorphism on algebra homomorphisms to scheme points. -/
private theorem representsOfConvolutionIso {A : Type u} [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] {F : TestAlgebra k ⥤ GrpCat.{u}}
    (c : convolutionPoints (CommHopfAlgCat.of k A) ≅ F)
    (eval : ∀ R : TestAlgebra k, (A →ₐ[k] R) → F.obj R → Prop)
    (h : ∀ R f, eval R f (c.hom.app R (toConv f))) : Represents A F eval := by
  let e := hopfSpecPointIso (CommHopfAlgCat.of k A)
  refine ⟨e, fun _ _ => rfl, spectrumPointsIso c, ?_⟩
  intro R f
  have he : e ≪≫ (e.symm ≪≫ c) = c := by simp
  change eval R f ((e ≪≫ (e.symm ≪≫ c)).hom.app R (toConv f))
  rw [he]
  exact h R f

private structure Representation (A : Type u) [CommRing A] [Algebra k A]
    (F : TestAlgebra k ⥤ GrpCat.{u}) where
  equiv (R : TestAlgebra k) : (A →ₐ[k] R) ≃ F.obj R
  naturality {R S : TestAlgebra k} (h : R ⟶ S) (f : A →ₐ[k] R) :
    equiv S (h.hom.comp f) = F.map h (equiv R f)

namespace Representation

variable {A : Type u} [CommRing A] [Algebra k A] {F : TestAlgebra k ⥤ GrpCat.{u}}
variable (P : Representation A F)

private abbrev left : A →ₐ[k] A ⊗[k] A := includeLeft
private abbrev right : A →ₐ[k] A ⊗[k] A := includeRight

private def mul {B : Type u} [CommRing B] [Algebra k B] (f g : A →ₐ[k] B) : A →ₐ[k] B :=
  (P.equiv (CommAlgCat.of k B)).symm
    (P.equiv (CommAlgCat.of k B) f * P.equiv (CommAlgCat.of k B) g)

private theorem equiv_mul {B : Type u} [CommRing B] [Algebra k B] (f g : A →ₐ[k] B) :
    P.equiv (CommAlgCat.of k B) (P.mul f g) =
      P.equiv (CommAlgCat.of k B) f * P.equiv (CommAlgCat.of k B) g :=
  Equiv.apply_symm_apply _ _

private theorem post_mul {B C : Type u} [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]
    (h : B →ₐ[k] C) (f g : A →ₐ[k] B) :
    h.comp (P.mul f g) = P.mul (h.comp f) (h.comp g) := by
  let a : CommAlgCat.of k B ⟶ CommAlgCat.of k C := CommAlgCat.ofHom h
  apply (P.equiv (CommAlgCat.of k C)).injective
  have natural (b : A →ₐ[k] B) :
      P.equiv (CommAlgCat.of k C) (h.comp b) = F.map a (P.equiv (CommAlgCat.of k B) b) :=
    P.naturality a b
  rw [P.equiv_mul, natural, P.equiv_mul, natural, natural, map_mul]

private def delta : A →ₐ[k] A ⊗[k] A := P.mul left right

private def epsilon : A →ₐ[k] k := (P.equiv (CommAlgCat.of k k)).symm 1

private def inverse : A →ₐ[k] A :=
  (P.equiv (CommAlgCat.of k A)).symm ((P.equiv (CommAlgCat.of k A) (.id k A))⁻¹)

private theorem equiv_epsilon {B : Type u} [CommRing B] [Algebra k B] (h : k →ₐ[k] B) :
    P.equiv (CommAlgCat.of k B) (h.comp P.epsilon) = 1 := by
  let a : CommAlgCat.of k k ⟶ CommAlgCat.of k B := CommAlgCat.ofHom h
  change P.equiv (CommAlgCat.of k B) (a.hom.comp P.epsilon) = 1
  rw [P.naturality a P.epsilon]
  simp [epsilon]

private theorem equiv_inverse :
    P.equiv (CommAlgCat.of k A) P.inverse = (P.equiv (CommAlgCat.of k A) (.id k A))⁻¹ :=
  Equiv.apply_symm_apply _ _

private theorem compose_delta {B : Type u} [CommRing B] [Algebra k B] (f g : A →ₐ[k] B) :
    (lift f g (fun _ _ => Commute.all _ _)).comp P.delta = P.mul f g := by
  rw [delta, P.post_mul, lift_comp_includeLeft, lift_comp_includeRight']

private def operations : HopfOperations k A :=
  ⟨P.delta, P.epsilon, P.inverse, (by
    let α := (Algebra.TensorProduct.assoc k k k A A A).toAlgHom
    have hf : (α.comp includeLeft).comp left = (includeLeft : A →ₐ[k] A ⊗[k] (A ⊗[k] A)) := by
      apply AlgHom.ext
      intro x
      simp [α, left, includeLeft_apply, Algebra.TensorProduct.one_def]
    have hg : (α.comp includeLeft).comp right =
        (includeRight : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A)).comp left := by
      apply AlgHom.ext
      intro x
      simp [α, left, right, includeLeft_apply, includeRight_apply]
    have hh : α.comp includeRight =
        (includeRight : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A)).comp right := by
      apply AlgHom.ext
      intro x
      simp [α, right, includeRight_apply, Algebra.TensorProduct.one_def]
    change (α.comp (map P.delta (.id k A))).comp P.delta = _
    rw [AlgHom.comp_assoc α]
    simp only [delta, P.post_mul, map_comp_includeLeft, map_comp_includeRight, AlgHom.comp_id]
    rw [AlgHom.comp_assoc α includeLeft] at hf hg
    rw [hf, hg, hh]
    apply (P.equiv (CommAlgCat.of k (A ⊗[k] (A ⊗[k] A)))).injective
    simp only [P.equiv_mul, mul_assoc]
  ), (by
    simp only [delta, P.post_mul, map_comp_includeLeft, map_comp_includeRight, AlgHom.comp_id]
    apply (P.equiv (CommAlgCat.of k (k ⊗[k] A))).injective
    rw [P.equiv_mul, P.equiv_epsilon, one_mul]
    rfl
  ), (by
    simp only [delta, P.post_mul, map_comp_includeLeft, map_comp_includeRight, AlgHom.comp_id]
    apply (P.equiv (CommAlgCat.of k (A ⊗[k] k))).injective
    rw [P.equiv_mul, P.equiv_epsilon, mul_one]
    rfl), (by
    change (lift P.inverse (.id k A) (fun _ _ => Commute.all _ _)).comp P.delta =
      (Algebra.ofId k A).comp P.epsilon
    rw [P.compose_delta]
    apply (P.equiv (CommAlgCat.of k A)).injective
    rw [P.equiv_mul, P.equiv_inverse, P.equiv_epsilon, inv_mul_cancel]
  ), (by
    change (lift (.id k A) P.inverse (fun _ _ => Commute.all _ _)).comp P.delta =
      (Algebra.ofId k A).comp P.epsilon
    rw [P.compose_delta]
    apply (P.equiv (CommAlgCat.of k A)).injective
    rw [P.equiv_mul, P.equiv_inverse, P.equiv_epsilon, mul_inv_cancel])⟩

@[instance_reducible]
private def hopf : HopfAlgebra k A := P.operations.hopf

private def convolutionIso : letI := P.hopf
    convolutionPoints (CommHopfAlgCat.of k A) ≅ F := by
  letI := P.hopf
  let H := CommHopfAlgCat.of k A
  let iso (R : TestAlgebra k) : (convolutionPoints H).obj R ≃* F.obj R :=
    { toFun := fun f => P.equiv R f.ofConv
      invFun := fun x => toConv ((P.equiv R).symm x)
      left_inv := fun f => WithConv.ofConv_injective ((P.equiv R).symm_apply_apply f.ofConv)
      right_inv := (P.equiv R).apply_symm_apply
      map_mul' := by
        intro f g
        have h : (f * g).ofConv = P.mul f.ofConv g.ofConv := by
          calc
            _ = (lift f.ofConv g.ofConv (fun _ _ => Commute.all _ _)).comp P.delta :=
              AlgHom.ext fun x => AlgHom.convMul_apply f g x
            _ = _ := P.compose_delta _ _
        change P.equiv R (f * g).ofConv = _
        rw [h, P.equiv_mul] }
  refine NatIso.ofComponents (fun R => (iso R).toGrpIso) ?_
  intro R S a
  apply GrpCat.ext
  intro f
  exact P.naturality a f.ofConv

private theorem represents [Algebra.FiniteType k A]
    (eval : ∀ R : TestAlgebra k, (A →ₐ[k] R) → F.obj R → Prop)
    (he : ∀ R f, eval R f (P.equiv R f)) : letI := P.hopf; Represents A F eval := by
  let _ := P.hopf
  exact representsOfConvolutionIso P.convolutionIso eval he

/-- Pullback of operations along a map that gives a homomorphism on all test algebras. -/
private theorem compatible {B : Type u} [CommRing B] [Algebra k B]
    {G : TestAlgebra k ⥤ GrpCat.{u}} (Q : Representation B G)
    (q : A →ₐ[k] B) (j : ∀ R, G.obj R →* F.obj R)
    (hj : ∀ (R : TestAlgebra k) (f : B →ₐ[k] R),
      P.equiv R (f.comp q) = j R (Q.equiv R f)) :
    (map q q).comp P.delta = Q.delta.comp q ∧
    P.epsilon = Q.epsilon.comp q ∧ q.comp P.inverse = Q.inverse.comp q := by
  refine ⟨?_, ?_, ?_⟩
  · apply (P.equiv (CommAlgCat.of k (B ⊗[k] B))).injective
    simp only [delta, P.post_mul, map_comp_includeLeft, map_comp_includeRight, P.equiv_mul, hj,
      Q.equiv_mul, map_mul]
  · apply (P.equiv (CommAlgCat.of k k)).injective
    rw [hj]
    simp [epsilon]
  · apply (P.equiv (CommAlgCat.of k B)).injective
    rw [hj, Q.equiv_inverse, map_inv, ← hj, AlgHom.id_comp]
    let a : CommAlgCat.of k A ⟶ CommAlgCat.of k B := CommAlgCat.ofHom q
    change P.equiv (CommAlgCat.of k B) (a.hom.comp P.inverse) =
      (P.equiv (CommAlgCat.of k B) (a.hom.comp (.id k A)))⁻¹
    rw [P.naturality, P.naturality, P.equiv_inverse, map_inv]

end Representation
section Additive

variable (k)

private def additiveRepresentation : Representation (Polynomial k) (additivePoints k) where
  equiv R := (Polynomial.aevalEquiv (R := k) (A := R)).symm.trans
    Multiplicative.ofAdd
  naturality _ _ := rfl

/-- The Hopf algebra of the additive group, with primitive coordinate `X`. -/
@[instance_reducible]
def additiveHopf : HopfAlgebra k (Polynomial k) := (additiveRepresentation k).hopf

def additiveGroup : AffineAlgebraicGroup k :=
  letI := additiveHopf k
  spectrum k (Polynomial k)

theorem additiveGroupSpecification : AdditiveGroup.{u} := by
  intro k _
  refine ⟨(additiveRepresentation k).operations, ?_, ?_, ?_, ?_⟩
  · exact Polynomial.aeval_X _
  · exact Polynomial.aeval_X _
  · exact Polynomial.aeval_X _
  · exact (additiveRepresentation k).represents _ (fun _ _ => rfl)

end Additive

section Multiplicative

open LaurentPolynomial

variable {R : Type u} [CommRing R] [Algebra k R]

local notation "t" => (T 1 : LaurentPolynomial k)

private def laurentEvaluation (a : Rˣ) : LaurentPolynomial k →ₐ[k] R where
  toRingHom := eval₂ (algebraMap k R) a
  commutes' := eval₂_C _ _

private theorem laurentEvaluation_T (a : Rˣ) (n : ℤ) :
    laurentEvaluation (k := k) a (T n) = (a ^ n).val := eval₂_T _ _ _

private theorem laurentCoordinates_ext {f g : LaurentPolynomial k →ₐ[k] R}
    (h : f t = g t) : f = g := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k))
  have h' : f.comp Polynomial.toLaurentAlg = g.comp Polynomial.toLaurentAlg := by
    apply Polynomial.algHom_ext
    change f (Polynomial.toLaurent Polynomial.X) = g (Polynomial.toLaurent Polynomial.X)
    simpa only [Polynomial.toLaurent_X] using h
  exact congrArg AlgHom.toRingHom h'

variable (k) in
private def multiplicativeRepresentation :
    Representation (LaurentPolynomial k) (multiplicativePoints k) where
  equiv R :=
    { toFun := fun f => Units.map f.toMonoidHom ((isUnit_T 1 : IsUnit t).unit)
      invFun := laurentEvaluation
      left_inv := fun f => laurentCoordinates_ext (by
        rw [laurentEvaluation_T, zpow_one]
        exact congrArg f (isUnit_T 1 : IsUnit t).unit_spec)
      right_inv := fun a => Units.ext (by
        let b : Rˣ := a
        change laurentEvaluation b ((isUnit_T 1 : IsUnit t).unit.val) = b.val
        rw [(isUnit_T 1 : IsUnit t).unit_spec, laurentEvaluation_T, zpow_one]) }
  naturality _ _ := Units.ext rfl

variable (k)

@[instance_reducible]
def multiplicativeHopf : HopfAlgebra k (LaurentPolynomial k) :=
  (multiplicativeRepresentation k).hopf

def multiplicativeGroup : AffineAlgebraicGroup k :=
  letI := multiplicativeHopf k
  spectrum k (LaurentPolynomial k)

theorem multiplicativeGroupSpecification : MultiplicativeGroup.{u} := by
  intro k _
  let P := multiplicativeRepresentation k
  let ht : IsUnit (T 1 : LaurentPolynomial k) := isUnit_T 1
  refine ⟨P.operations, ?_, ?_, ?_, P.represents _ ?_⟩
  · change laurentEvaluation (Units.map includeLeft.toMonoidHom ht.unit *
      Units.map includeRight.toMonoidHom ht.unit) (T 1) = _
    rw [laurentEvaluation_T, zpow_one]
    change includeLeft ht.unit.val * includeRight ht.unit.val = _
    rw [ht.unit_spec]
    simp [includeLeft_apply, includeRight_apply]
  · exact (laurentEvaluation_T (1 : kˣ) 1).trans (by simp)
  · change laurentEvaluation (Units.map (AlgHom.id k _).toMonoidHom ht.unit)⁻¹ (T 1) = _
    rw [laurentEvaluation_T, zpow_one]
    rw [show Units.map (AlgHom.id k _).toMonoidHom ht.unit = ht.unit from Units.ext rfl]
    have he : ht.unit⁻¹ = (isUnit_T (-1) : IsUnit (T (-1) : LaurentPolynomial k)).unit := by
      apply mul_left_cancel (a := ht.unit)
      apply Units.ext
      rw [mul_inv_cancel, Units.val_one, Units.val_mul, ht.unit_spec, IsUnit.unit_spec, ← T_add]
      exact (T_zero (R := k)).symm
    rw [he, IsUnit.unit_spec]
  · intro R f
    change f ht.unit.val = _
    rw [ht.unit_spec]

end Multiplicative

/-- The generic matrix after localization at its determinant. -/
abbrev universalMatrix (k : Type u) [Field k] (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι (GLCoordinates k ι) :=
  Specs.StandardGroups.universalMatrix k ι

section GeneralLinear

variable (k) (ι : Type u) [Fintype ι] [DecidableEq ι]

private theorem universalDeterminant_eq :
    (universalMatrix k ι).det =
      algebraMap (MvPolynomial (ι × ι) k) (GLCoordinates k ι) (genericDeterminant k ι) :=
  ((algebraMap (MvPolynomial (ι × ι) k) (GLCoordinates k ι)).map_det _).symm

theorem isUnit_universalDeterminant : IsUnit (universalMatrix k ι).det := by
  rw [universalDeterminant_eq]
  exact IsLocalization.Away.algebraMap_isUnit (genericDeterminant k ι)

variable {k ι}

private def matrixEvaluation {R : Type u} [CommRing R] [Algebra k R] (M : Matrix ι ι R) :
    MvPolynomial (ι × ι) k →ₐ[k] R :=
  MvPolynomial.aeval (fun ij => M ij.1 ij.2)

private theorem matrixEvaluation_mapMatrix {R : Type u} [CommRing R] [Algebra k R]
    (M : Matrix ι ι R) :
    (matrixEvaluation M).mapMatrix (genericMatrix k ι) = M := by
  ext i j
  exact MvPolynomial.aeval_X _ (i, j)

private theorem isUnit_matrixEvaluation_det {R : Type u} [CommRing R] [Algebra k R]
    (M : Matrix.GeneralLinearGroup ι R) :
    IsUnit (matrixEvaluation M.val (genericDeterminant k ι)) := by
  rw [genericDeterminant, AlgHom.map_det, matrixEvaluation_mapMatrix]
  exact (Matrix.GeneralLinearGroup.det M).isUnit

private def glEvaluation {R : Type u} [CommRing R] [Algebra k R] (M : Matrix.GeneralLinearGroup ι R) :
    GLCoordinates k ι →ₐ[k] R :=
  IsLocalization.Away.liftAlgHom (genericDeterminant k ι) (isUnit_matrixEvaluation_det M)

private theorem glEvaluation_entry {R : Type u} [CommRing R] [Algebra k R]
    (M : Matrix.GeneralLinearGroup ι R) (i j : ι) :
    glEvaluation M (universalMatrix k ι i j) = M.val i j := by
  let A := MvPolynomial (ι × ι) k
  change glEvaluation M (algebraMap A (GLCoordinates k ι) (MvPolynomial.X (i, j))) = _
  calc
    _ = matrixEvaluation M.val (MvPolynomial.X (i, j)) :=
      IsLocalization.Away.lift_eq (S := GLCoordinates k ι) (genericDeterminant k ι)
        (g := (matrixEvaluation M.val).toRingHom) (isUnit_matrixEvaluation_det M) _
    _ = _ := MvPolynomial.aeval_X _ (i, j)

private theorem glCoordinates_ext {R : Type u} [CommRing R] [Algebra k R]
    {f g : GLCoordinates k ι →ₐ[k] R}
    (h : ∀ i j, f (universalMatrix k ι i j) = g (universalMatrix k ι i j)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (genericDeterminant k ι))
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  exact h i j

private def evaluatedGeneralLinear {R : Type u} [CommRing R] [Algebra k R]
    (f : GLCoordinates k ι →ₐ[k] R) : Matrix.GeneralLinearGroup ι R :=
  Matrix.GeneralLinearGroup.mk'' (f.mapMatrix (universalMatrix k ι)) (by
    rw [← f.map_det]
    exact (isUnit_universalDeterminant k ι).map f)

private def generalLinearRepresentation :
    Representation (GLCoordinates k ι) (generalLinearPoints k ι) where
  equiv R :=
    { toFun := evaluatedGeneralLinear
      invFun := glEvaluation
      left_inv := fun f => glCoordinates_ext fun i j => glEvaluation_entry _ i j
      right_inv := fun M => Matrix.GeneralLinearGroup.ext fun i j => glEvaluation_entry M i j }
  naturality a f := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

variable (k ι)

/-- The Hopf algebra of the general linear group on the determinant localization. -/
@[instance_reducible]
def generalLinearHopf : HopfAlgebra k (GLCoordinates k ι) :=
  (generalLinearRepresentation (k := k) (ι := ι)).hopf

def generalLinearGroup : AffineAlgebraicGroup k :=
  letI := generalLinearHopf k ι
  spectrum k (GLCoordinates k ι)

variable {k ι}

local notation "X" => universalMatrix k ι
local notation "d" => Matrix.det (universalMatrix k ι)
local instance : HopfAlgebra k (GLCoordinates k ι) := generalLinearHopf k ι

local notation "P" => generalLinearRepresentation (k := k) (ι := ι)

private theorem delta_matrix :
    (P).delta.mapMatrix X =
      (includeLeft : GLCoordinates k ι →ₐ[k] GLCoordinates k ι ⊗[k] GLCoordinates k ι).mapMatrix X *
      (includeRight : GLCoordinates k ι →ₐ[k] GLCoordinates k ι ⊗[k] GLCoordinates k ι).mapMatrix X :=
  congrArg Units.val ((P).equiv_mul
    (includeLeft : GLCoordinates k ι →ₐ[k] GLCoordinates k ι ⊗[k] GLCoordinates k ι)
    (includeRight : GLCoordinates k ι →ₐ[k] GLCoordinates k ι ⊗[k] GLCoordinates k ι))

private theorem epsilon_matrix : (P).epsilon.mapMatrix X = 1 := by
  exact congrArg Units.val ((P).equiv_epsilon (AlgHom.id k k))

private def universalGeneralLinear : Matrix.GeneralLinearGroup ι (GLCoordinates k ι) :=
  evaluatedGeneralLinear (AlgHom.id k _)

private theorem inverse_matrix :
    (P).inverse.mapMatrix X = (universalGeneralLinear⁻¹ : Matrix.GeneralLinearGroup ι (GLCoordinates k ι)).val :=
  congrArg Units.val (P).equiv_inverse

private theorem delta_determinant : (P).delta d = d ⊗ₜ[k] d := by
  rw [AlgHom.map_det, delta_matrix, Matrix.det_mul, ← AlgHom.map_det, ← AlgHom.map_det]
  simp [includeLeft_apply, includeRight_apply]

private theorem epsilon_determinant : (P).epsilon d = 1 := by
  rw [AlgHom.map_det, epsilon_matrix, Matrix.det_one]

private theorem inverse_determinant : (P).inverse d = d⁻¹ʳ := by
  rw [AlgHom.map_det, inverse_matrix]
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv]
  rfl

private theorem delta_entry (i j : ι) :
    (P).delta (X i j) = ∑ l, X i l ⊗ₜ[k] X l j := by
  have h := congrArg (fun M => M i j) (delta_matrix (k := k) (ι := ι))
  simpa only [Matrix.mul_apply, AlgHom.mapMatrix_apply, Matrix.map_apply,
    includeLeft_apply, includeRight_apply, tmul_mul_tmul, mul_one, one_mul] using h

private theorem epsilon_entry (i j : ι) :
    (P).epsilon (X i j) = if i = j then 1 else 0 :=
  (congrArg (fun M => M i j) (epsilon_matrix (k := k) (ι := ι))).trans Matrix.one_apply

private theorem inverse_entry (i j : ι) :
    (P).inverse (X i j) = d⁻¹ʳ * Matrix.adjugate X i j := by
  have h : (P).inverse (X i j) =
    (((universalGeneralLinear⁻¹ : Matrix.GeneralLinearGroup ι (GLCoordinates k ι))) :
      Matrix ι ι (GLCoordinates k ι)) i j :=
    congrArg (fun M => M i j) (inverse_matrix (k := k) (ι := ι))
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def] at h
  exact h

theorem generalLinearGroupSpecification : GeneralLinearGroup.{u} := by
  intro k ι _ _ _
  let model := generalLinearRepresentation (k := k) (ι := ι)
  exact ⟨model.operations, delta_entry, epsilon_entry, inverse_entry, delta_determinant, epsilon_determinant,
    inverse_determinant, model.represents _ (fun _ _ => rfl)⟩

end GeneralLinear

section SpecialLinear

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

local notation "X" => universalMatrix k ι
local notation "d" => Matrix.det (universalMatrix k ι)
local notation "I" => determinantOneIdeal k ι
local notation "q" => Ideal.Quotient.mkₐ k (determinantOneIdeal k ι)

private theorem quotient_det : q d = 1 := by
  have h : q (d - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  simpa only [map_sub, map_one, sub_eq_zero] using h

private theorem vanishes_on_ideal {R : Type u} [CommRing R] [Algebra k R]
    (f : GLCoordinates k ι →ₐ[k] R) (h : f (d - 1) = 0)
    {x : GLCoordinates k ι} (hx : x ∈ I) : f x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  rw [map_mul, h, zero_mul]

private def evaluatedSpecialLinear {R : Type u} [CommRing R] [Algebra k R]
    (f : SLCoordinates k ι →ₐ[k] R) : Matrix.SpecialLinearGroup ι R :=
  ⟨(f.comp q).mapMatrix X, by rw [← AlgHom.map_det, AlgHom.comp_apply, quotient_det, map_one]⟩

private def slEvaluation {R : Type u} [CommRing R] [Algebra k R]
    (g : Matrix.SpecialLinearGroup ι R) : SLCoordinates k ι →ₐ[k] R :=
  let f := glEvaluation (Matrix.SpecialLinearGroup.toGL g)
  Ideal.Quotient.liftₐ I f (by
    apply fun x hx => vanishes_on_ideal f ?_ hx
    have h : f.mapMatrix X = (g : Matrix ι ι R) :=
      Matrix.ext fun i j => glEvaluation_entry (Matrix.SpecialLinearGroup.toGL g) i j
    rw [map_sub, map_one, AlgHom.map_det, h, g.det_coe, sub_self])

private theorem slEvaluation_entry {R : Type u} [CommRing R] [Algebra k R]
    (g : Matrix.SpecialLinearGroup ι R) (i j : ι) :
    slEvaluation g (q (X i j)) = g i j :=
  glEvaluation_entry (Matrix.SpecialLinearGroup.toGL g) i j

private def specialLinearRepresentation :
    Representation (SLCoordinates k ι) (specialLinearPoints k ι) where
  equiv R :=
    { toFun := evaluatedSpecialLinear
      invFun := slEvaluation
      left_inv := fun f => by
        apply Ideal.Quotient.algHom_ext k
        apply glCoordinates_ext
        intro i j
        exact slEvaluation_entry (evaluatedSpecialLinear f) i j
      right_inv := fun g => Matrix.SpecialLinearGroup.ext _ _ (slEvaluation_entry g) }
  naturality a f := Matrix.SpecialLinearGroup.ext _ _ (fun i j => rfl)

local notation "Pgl" => generalLinearRepresentation (k := k) (ι := ι)
local notation "Psl" => specialLinearRepresentation (k := k) (ι := ι)

private theorem linearOperations_quotient :
    (map q q).comp (Pgl).delta = (Psl).delta.comp q ∧
    (Pgl).epsilon = (Psl).epsilon.comp q ∧
    (q).comp (Pgl).inverse = (Psl).inverse.comp q :=
  (Pgl).compatible (Psl) q (fun _ => Matrix.SpecialLinearGroup.toGL)
    (fun _ _ => Matrix.GeneralLinearGroup.ext fun _ _ => rfl)

local instance : HopfAlgebra k (GLCoordinates k ι) := generalLinearHopf k ι

private theorem delta_det_sub_one :
    (Pgl).delta (d - 1) = (d - 1) ⊗ₜ[k] d + 1 ⊗ₜ[k] (d - 1) := by
  simp only [map_sub, delta_determinant, map_one, TensorProduct.sub_tmul,
    TensorProduct.tmul_sub, sub_add_sub_cancel, Algebra.TensorProduct.one_def]

private theorem inverse_det_sub_one : (Pgl).inverse (d - 1) = -d⁻¹ʳ * (d - 1) := by
  rw [map_sub, inverse_determinant, map_one, neg_mul, mul_sub,
    Ring.inverse_mul_cancel _ (isUnit_universalDeterminant k ι), mul_one, neg_sub]

private theorem determinantOneIdeal_isHopf : Ideal.IsHopfIdeal k I := by
  obtain ⟨hDelta, hEpsilon, hInverse⟩ := linearOperations_quotient (k := k) (ι := ι)
  have hq {x : GLCoordinates k ι} (hx : x ∈ I) : q x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  refine { toIsCoideal := { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_ }
           antipode_mem := ?_ }
  · intro x hx
    change (generalLinearRepresentation (k := k) (ι := ι)).epsilon x = 0
    rw [hEpsilon, AlgHom.comp_apply, hq hx, map_zero]
  · intro x hx
    change ((map q q).comp (generalLinearRepresentation (k := k) (ι := ι)).delta) x = 0
    rw [hDelta, AlgHom.comp_apply, hq hx, map_zero]
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change ((q).comp (generalLinearRepresentation (k := k) (ι := ι)).inverse) x = 0
    rw [hInverse, AlgHom.comp_apply, hq hx, map_zero]

variable (k ι)

@[instance_reducible]
def specialLinearHopf : HopfAlgebra k (SLCoordinates k ι) :=
  (specialLinearRepresentation (k := k) (ι := ι)).hopf

def specialLinearGroup : AffineAlgebraicGroup k :=
  letI := specialLinearHopf k ι
  spectrum k (SLCoordinates k ι)

theorem specialLinearGroupSpecification : SpecialLinearGroup.{u} := by
  intro k ι _ _ _
  let model := generalLinearRepresentation (k := k) (ι := ι)
  let Q := specialLinearRepresentation (k := k) (ι := ι)
  obtain ⟨hDelta, hEpsilon, hInverse⟩ := linearOperations_quotient (k := k) (ι := ι)
  exact ⟨model.operations, Q.operations, determinantOneIdeal_isHopf, delta_det_sub_one,
    by rw [map_sub, map_one]; exact sub_eq_zero.mpr epsilon_determinant, inverse_det_sub_one,
    hDelta, hEpsilon, hInverse, Q.represents _ (fun _ _ => rfl)⟩

end SpecialLinear

section Powers

variable {ι : Type u}

private def additivePowerRepresentation : Representation (MvPolynomial ι k) (additivePowerPoints k ι) where
  equiv _ :=
    { toFun := fun f i => Multiplicative.ofAdd (f (MvPolynomial.X i))
      invFun := fun p => MvPolynomial.aeval (fun i => Multiplicative.toAdd (p i))
      left_inv := fun _ => MvPolynomial.algHom_ext (MvPolynomial.aeval_X _)
      right_inv := fun _ => funext fun i => congrArg Multiplicative.ofAdd (MvPolynomial.aeval_X _ i) }
  naturality _ _ := rfl

@[instance_reducible]
def additivePowerHopf (k ι : Type u) [Field k] : HopfAlgebra k (MvPolynomial ι k) :=
  (additivePowerRepresentation (k := k) (ι := ι)).hopf

def additivePowerGroup (k ι : Type u) [Field k] [Fintype ι] : AffineAlgebraicGroup k :=
  letI := additivePowerHopf k ι
  spectrum k (MvPolynomial ι k)

theorem additivePowerSpecification : AdditivePower.{u} := by
  intro k ι _ _
  let model := additivePowerRepresentation (k := k) (ι := ι)
  refine ⟨model.operations, ?_, ?_, ?_, model.represents _ (fun _ _ _ => rfl)⟩
  · intro i
    exact MvPolynomial.aeval_X _ i
  · intro i
    exact MvPolynomial.aeval_X _ i
  · intro i
    exact MvPolynomial.aeval_X _ i

variable [Fintype ι] [DecidableEq ι]

private def exponentEvaluation {R : Type u} [CommRing R] (a : ι → Rˣ) :
    Multiplicative (ι → ℤ) →* Rˣ where
  toFun m := ∏ i, a i ^ m.toAdd i
  map_one' := by change (∏ i, a i ^ (0 : ℤ)) = 1; simp
  map_mul' x y := by
    change (∏ i, a i ^ (x.toAdd i + y.toAdd i)) =
      (∏ i, a i ^ x.toAdd i) * (∏ i, a i ^ y.toAdd i)
    simp [zpow_add, Finset.prod_mul_distrib]

private theorem basis_expansion (m : Multiplicative (ι → ℤ)) :
    (∏ i, Multiplicative.ofAdd (Pi.single i (1 : ℤ)) ^ m.toAdd i) = m := by
  apply Multiplicative.toAdd.injective
  change (∑ i, m.toAdd i • Pi.single i (1 : ℤ)) = m.toAdd
  ext j
  simp only [Finset.sum_apply, zsmul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ h
    simp [Pi.single_eq_of_ne h.symm]
  · simp

private def exponentsEquiv (R : Type u) [CommRing R] :
    (Multiplicative (ι → ℤ) →* Rˣ) ≃* (ι → Rˣ) where
  toFun f i := f (Multiplicative.ofAdd (Pi.single i 1))
  invFun := exponentEvaluation
  left_inv f := by
    apply MonoidHom.ext
    intro m
    change (∏ i, f (Multiplicative.ofAdd (Pi.single i 1)) ^ m.toAdd i) = f m
    simp only [← map_zpow, ← map_prod, basis_expansion]
  right_inv a := by
    funext i
    let m : ι → ℤ := Pi.single i 1
    change (∏ j, a j ^ m j) = a i
    rw [Finset.prod_eq_single i]
    · simp [m]
    · intro j _ h
      simp [m, Pi.single_eq_of_ne h]
    · simp
  map_mul' _ _ := rfl

private abbrev laurentPowerHopf (k ι : Type u) [Field k] : HopfAlgebraCategory k :=
  CommHopfAlgCat.of k (LaurentPowerCoordinates k ι)

def multiplicativePowerGroup (k ι : Type u) [Field k] [Fintype ι] : AffineAlgebraicGroup k :=
  Specs.StandardGroups.multiplicativePowerGroup k ι

private def laurentPowerMulEquiv (R : TestAlgebra k) :
    (convolutionPoints (laurentPowerHopf k ι)).obj R ≃* (multiplicativePowerPoints k ι).obj R :=
  (AddMonoidAlgebra.liftMulEquiv k R (ι → ℤ)).symm.trans
    (MonoidHom.toHomUnitsMulEquiv.trans (exponentsEquiv R))

private theorem laurentPowerMulEquiv_eval (R : TestAlgebra k)
    (f : LaurentPowerCoordinates k ι →ₐ[k] R) (i : ι) :
    ((show ι → Rˣ from laurentPowerMulEquiv R (toConv f)) i).val = f (laurentVariable k ι i) :=
  rfl

private def laurentPowerIso :
    convolutionPoints (laurentPowerHopf k ι) ≅ multiplicativePowerPoints k ι := by
  refine NatIso.ofComponents (fun R => (laurentPowerMulEquiv R).toGrpIso) ?_
  intro R S a
  apply GrpCat.ext
  intro f
  funext i
  apply Units.ext
  rfl

omit [Fintype ι] in
private theorem laurentVariable_groupLike (i : ι) :
    IsGroupLikeElem k (laurentVariable k ι i) :=
  AddMonoidAlgebra.isGroupLikeElem_single_one (Pi.single i 1 : ι → ℤ)

omit [Fintype ι] in
private theorem laurentVariable_antipode (i : ι) :
    antipode k (laurentVariable k ι i) = AddMonoidAlgebra.single (-Pi.single i (1 : ℤ)) 1 := by
  unfold laurentVariable
  rw [AddMonoidAlgebra.antipode_single, antipode_one]

theorem multiplicativePowerSpecification : MultiplicativePower.{u} := by
  intro k ι _ _ _
  refine ⟨(fun i => (laurentVariable_groupLike (k := k) i).comul_eq_tmul_self),
    (fun i => (laurentVariable_groupLike (k := k) i).counit_eq_one),
    laurentVariable_antipode, ?_⟩
  exact representsOfConvolutionIso laurentPowerIso _ laurentPowerMulEquiv_eval

end Powers

section TensorPowers

variable {ι κ : Type u}

/-- Splitting Laurent exponents into their restrictions to the two index sets. -/
private def splitExponents : (ι ⊕ κ → ℤ) ≃+ ((κ → ℤ) × (ι → ℤ)) where
  toEquiv := (Equiv.sumArrowEquivProdArrow ι κ ℤ).trans (Equiv.prodComm _ _)
  map_add' _ _ := rfl

/-- Laurent polynomials on a disjoint union are the tensor product of those on the two sets. -/
def tensorLaurentEquiv (k ι κ : Type u) [Field k] :
    (LaurentPowerCoordinates k ι ⊗[k] LaurentPowerCoordinates k κ) ≃ₐ[k]
      LaurentPowerCoordinates k (ι ⊕ κ) :=
  (((AddMonoidAlgebra.scalarTensorEquiv k (M := κ → ℤ) (LaurentPowerCoordinates k ι)).restrictScalars k).trans
    (AddMonoidAlgebra.curryAlgEquiv k).symm).trans
    (AddMonoidAlgebra.domCongr k k splitExponents).symm

private theorem tensorLaurentEquiv_symm_single (a : ι ⊕ κ → ℤ) :
    (tensorLaurentEquiv k ι κ).symm (AddMonoidAlgebra.single a 1) =
      AddMonoidAlgebra.single (fun i => a (Sum.inl i)) 1 ⊗ₜ[k]
        AddMonoidAlgebra.single (fun j => a (Sum.inr j)) 1 := by
  change (AddMonoidAlgebra.scalarTensorEquiv k (M := κ → ℤ) (LaurentPowerCoordinates k ι)).symm
    (AddMonoidAlgebra.curryAlgEquiv k
      (AddMonoidAlgebra.domCongr k k splitExponents (AddMonoidAlgebra.single a 1))) = _
  rw [AddMonoidAlgebra.domCongr_single]
  change (AddMonoidAlgebra.scalarTensorEquiv k (M := κ → ℤ) (LaurentPowerCoordinates k ι)).symm
    (AddMonoidAlgebra.curryAlgEquiv k
      (AddMonoidAlgebra.single ((fun j : κ => a (Sum.inr j)), (fun i : ι => a (Sum.inl i))) (1 : k))) = _
  rw [AddMonoidAlgebra.curryAlgEquiv_single, AddMonoidAlgebra.scalarTensorEquiv_symm_single]

private theorem tensorLaurentEquiv_left [DecidableEq ι] [DecidableEq κ] (i : ι) :
    tensorLaurentEquiv k ι κ (laurentVariable k ι i ⊗ₜ[k] 1) =
      laurentVariable k (ι ⊕ κ) (Sum.inl i) := by
  apply (tensorLaurentEquiv k ι κ).symm.injective
  simp only [AlgEquiv.symm_apply_apply, laurentVariable, tensorLaurentEquiv_symm_single]
  let a : ι ⊕ κ → ℤ := Pi.single (Sum.inl i) 1
  have hi : (fun j : ι => a (Sum.inl j)) = Pi.single i 1 := by
    funext j
    simp [a, Pi.single_apply]
  have hj : (fun j : κ => a (Sum.inr j)) = 0 := by
    funext j
    simp [a]
  change _ = AddMonoidAlgebra.single (fun j : ι => a (Sum.inl j)) 1 ⊗ₜ[k]
    AddMonoidAlgebra.single (fun j : κ => a (Sum.inr j)) 1
  rw [hi, hj]
  rfl

private theorem tensorLaurentEquiv_right [DecidableEq ι] [DecidableEq κ] (j : κ) :
    tensorLaurentEquiv k ι κ (1 ⊗ₜ[k] laurentVariable k κ j) =
      laurentVariable k (ι ⊕ κ) (Sum.inr j) := by
  apply (tensorLaurentEquiv k ι κ).symm.injective
  simp only [AlgEquiv.symm_apply_apply, laurentVariable, tensorLaurentEquiv_symm_single]
  let a : ι ⊕ κ → ℤ := Pi.single (Sum.inr j) 1
  have hi : (fun i : ι => a (Sum.inl i)) = 0 := by
    funext i
    simp [a]
  have hj : (fun i : κ => a (Sum.inr i)) = Pi.single j 1 := by
    funext i
    simp [a, Pi.single_apply]
  change _ = AddMonoidAlgebra.single (fun i : ι => a (Sum.inl i)) 1 ⊗ₜ[k]
    AddMonoidAlgebra.single (fun i : κ => a (Sum.inr i)) 1
  rw [hi, hj]
  rfl


section PrimitiveTensor

local instance (priority := high) : Bialgebra k (MvPolynomial ι k) :=
  (additivePowerHopf k ι).toBialgebra

local instance (priority := high) : Coalgebra k (MvPolynomial ι k) :=
  (additivePowerHopf k ι).toBialgebra.toCoalgebra

local instance (priority := high) : CoalgebraStruct k (MvPolynomial ι k) :=
  (additivePowerHopf k ι).toBialgebra.toCoalgebra.toCoalgebraStruct

private theorem polynomial_comul (i : ι) :
    Coalgebra.comul (R := k) (MvPolynomial.X i : MvPolynomial ι k) =
      MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i :=
  MvPolynomial.aeval_X _ i

private theorem polynomial_counit (i : ι) :
    Coalgebra.counit (R := k) (MvPolynomial.X i : MvPolynomial ι k) = 0 :=
  MvPolynomial.aeval_X _ i

private theorem comul_sum_generator (p : ι ⊕ κ) :
    let a := (MvPolynomial.tensorEquivSum k ι κ k).symm (MvPolynomial.X p)
    Coalgebra.comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a := by
  cases p with
  | inl i =>
    rw [← MvPolynomial.tensorEquivSum_X_tmul_one (R := k) (S := k) (ι := κ) i,
      AlgEquiv.symm_apply_apply]
    simp only [TensorProduct.comul_tmul, polynomial_comul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def, TensorProduct.add_tmul, map_add,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  | inr j =>
    rw [← MvPolynomial.tensorEquivSum_one_tmul_X (R := k) (S := k) (σ := ι) j,
      AlgEquiv.symm_apply_apply]
    simp only [TensorProduct.comul_tmul, polynomial_comul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def, TensorProduct.tmul_add, map_add,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]

private theorem counit_sum_generator (p : ι ⊕ κ) :
    Coalgebra.counit (R := k)
      ((MvPolynomial.tensorEquivSum k ι κ k).symm (MvPolynomial.X p)) = 0 := by
  cases p with
  | inl i =>
    rw [← MvPolynomial.tensorEquivSum_X_tmul_one (R := k) (S := k) (ι := κ) i,
      AlgEquiv.symm_apply_apply]
    simp only [TensorProduct.counit_tmul, polynomial_counit, smul_zero]
  | inr j =>
    rw [← MvPolynomial.tensorEquivSum_one_tmul_X (R := k) (S := k) (σ := ι) j,
      AlgEquiv.symm_apply_apply]
    simp only [TensorProduct.counit_tmul, polynomial_counit, zero_smul]

/-- The tensor product of polynomial Hopf algebras on primitive generators. -/
def tensorPolynomialHopfEquiv (k ι κ : Type u) [Field k] :
    (MvPolynomial ι k ⊗[k] MvPolynomial κ k) ≃ₐc[k] MvPolynomial (ι ⊕ κ) k := by
  let e := (MvPolynomial.tensorEquivSum k ι κ k).symm
  refine (BialgEquiv.ofAlgEquiv e ?_ ?_).symm
  · apply MvPolynomial.algHom_ext
    intro p
    change Coalgebra.counit (R := k) (e (MvPolynomial.X p)) =
      Coalgebra.counit (R := k) (MvPolynomial.X p : MvPolynomial (ι ⊕ κ) k)
    exact (counit_sum_generator p).trans (polynomial_counit p).symm
  · apply MvPolynomial.algHom_ext
    intro p
    change map e.toAlgHom e.toAlgHom (Coalgebra.comul (R := k) (MvPolynomial.X p)) =
      Coalgebra.comul (R := k) (e (MvPolynomial.X p))
    rw [comul_sum_generator, polynomial_comul]
    simp only [map_add, map_tmul, map_one]
    rfl

end PrimitiveTensor

private theorem tensorLaurent_groupLike (d : ι ⊕ κ → ℤ) :
    IsGroupLikeElem k ((tensorLaurentEquiv k ι κ).symm (AddMonoidAlgebra.single d 1)) := by
  rw [tensorLaurentEquiv_symm_single]
  let x : LaurentPowerCoordinates k ι := AddMonoidAlgebra.single (fun i => d (Sum.inl i)) 1
  let y : LaurentPowerCoordinates k κ := AddMonoidAlgebra.single (fun j => d (Sum.inr j)) 1
  have hx : IsGroupLikeElem k x := AddMonoidAlgebra.isGroupLikeElem_single_one _
  have hy : IsGroupLikeElem k y := AddMonoidAlgebra.isGroupLikeElem_single_one _
  change IsGroupLikeElem k (x ⊗ₜ[k] y)
  constructor
  · simp only [TensorProduct.counit_tmul, hy.counit_eq_one, hx.counit_eq_one, one_smul]
  · simp only [TensorProduct.comul_tmul, hx.comul_eq_tmul_self, hy.comul_eq_tmul_self,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]

private theorem laurentMonomial_ext {B : Type u} [CommRing B] [Algebra k B]
    {f g : LaurentPowerCoordinates k ι →ₐ[k] B}
    (h : ∀ d : ι → ℤ, f (AddMonoidAlgebra.single d 1) = g (AddMonoidAlgebra.single d 1)) :
    f = g := by
  apply (AddMonoidAlgebra.lift k B (ι → ℤ)).symm.injective
  exact MonoidHom.ext fun d => h d.toAdd

/-- The tensor product of Laurent Hopf algebras on group-like generators. -/
def tensorLaurentHopfEquiv (k ι κ : Type u) [Field k] :
    (LaurentPowerCoordinates k ι ⊗[k] LaurentPowerCoordinates k κ) ≃ₐc[k]
      LaurentPowerCoordinates k (ι ⊕ κ) := by
  let e := (tensorLaurentEquiv k ι κ).symm
  refine (BialgEquiv.ofAlgEquiv e ?_ ?_).symm
  · apply laurentMonomial_ext (ι := ι ⊕ κ)
    intro d
    let x : LaurentPowerCoordinates k (ι ⊕ κ) := AddMonoidAlgebra.single d 1
    have hx : IsGroupLikeElem k x := AddMonoidAlgebra.isGroupLikeElem_single_one d
    change Coalgebra.counit (R := k) (e x) = Coalgebra.counit (R := k) x
    exact (tensorLaurent_groupLike d).counit_eq_one.trans hx.counit_eq_one.symm
  · let T := LaurentPowerCoordinates k ι ⊗[k] LaurentPowerCoordinates k κ
    apply laurentMonomial_ext (k := k) (ι := ι ⊕ κ) (B := T ⊗[k] T)
    intro d
    let x : LaurentPowerCoordinates k (ι ⊕ κ) := AddMonoidAlgebra.single d 1
    have hx : IsGroupLikeElem k x := AddMonoidAlgebra.isGroupLikeElem_single_one d
    change map e.toAlgHom e.toAlgHom (Coalgebra.comul (R := k) x) = Coalgebra.comul (R := k) (e x)
    rw [hx.comul_eq_tmul_self, (tensorLaurent_groupLike d).comul_eq_tmul_self, map_tmul]
    rfl

theorem tensorPowerHopfSpecification : TensorPowerHopf.{u} := by
  intro k ι κ _
  refine ⟨additivePowerRepresentation.operations, additivePowerRepresentation.operations,
    additivePowerRepresentation.operations, (fun i => MvPolynomial.aeval_X _ i),
    (fun j => MvPolynomial.aeval_X _ j), (fun p => MvPolynomial.aeval_X _ p),
    ⟨tensorPolynomialHopfEquiv k ι κ, ?_⟩, ⟨tensorLaurentHopfEquiv k ι κ, ?_⟩⟩
  · ext x
    rfl
  · exact tensorLaurentEquiv_symm_single

theorem tensorPowerCoordinatesSpecification : TensorPowerCoordinates.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro k ι _ _
    exact ⟨⟨MvPolynomial.isEmptyAlgEquiv k ι⟩, ⟨AddMonoidAlgebra.uniqueAlgEquiv k (ι → ℤ)⟩⟩
  · intro k ι _ _ _
    refine ⟨MvPolynomial.uniqueAlgEquiv k ι,
      AddMonoidAlgebra.domCongr k k (AddEquiv.funUnique ι ℤ), ?_, ?_⟩
    · intro i
      exact MvPolynomial.eval₂_X _ _ _
    · intro i
      rw [laurentVariable, AddMonoidAlgebra.domCongr_single]
      let a : ι → ℤ := Pi.single i 1
      change AddMonoidAlgebra.single (a default) (1 : k) = LaurentPolynomial.T 1
      dsimp only [a]
      rw [Unique.eq_default i, Pi.single_eq_same]
      rfl
  · intro k ι κ _ _ _
    exact ⟨MvPolynomial.tensorEquivSum k ι κ k, tensorLaurentEquiv k ι κ,
      (fun i => MvPolynomial.tensorEquivSum_X_tmul_one i),
      (fun j => MvPolynomial.tensorEquivSum_one_tmul_X j),
      tensorLaurentEquiv_left, tensorLaurentEquiv_right⟩

end TensorPowers

section PointComparisons

variable (k) (ι : Type u) [Fintype ι] [DecidableEq ι]

/-- The additive group represents the additive groups of the test algebras. -/
def additiveGroupPointsIso :
    (groupPointsFunctor k).obj (additiveGroup k).val ≅ additivePoints k :=
  letI := additiveHopf k
  spectrumPointsIso (additiveRepresentation k).convolutionIso

/-- The multiplicative group represents the unit groups of the test algebras. -/
def multiplicativeGroupPointsIso :
    (groupPointsFunctor k).obj (multiplicativeGroup k).val ≅ multiplicativePoints k :=
  letI := multiplicativeHopf k
  spectrumPointsIso (multiplicativeRepresentation k).convolutionIso

/-- The determinant localization represents invertible matrices naturally. -/
def generalLinearGroupPointsIso :
    (groupPointsFunctor k).obj (generalLinearGroup k ι).val ≅ generalLinearPoints k ι :=
  letI := generalLinearHopf k ι
  spectrumPointsIso (generalLinearRepresentation (k := k) (ι := ι)).convolutionIso

/-- The determinant-one quotient represents determinant-one matrices naturally. -/
def specialLinearGroupPointsIso :
    (groupPointsFunctor k).obj (specialLinearGroup k ι).val ≅ specialLinearPoints k ι :=
  letI := specialLinearHopf k ι
  spectrumPointsIso (specialLinearRepresentation (k := k) (ι := ι)).convolutionIso

/-- The polynomial coordinate algebra represents the product of the additive point groups. -/
def additivePowerGroupPointsIso :
    (groupPointsFunctor k).obj (additivePowerGroup k ι).val ≅ additivePowerPoints k ι :=
  letI := additivePowerHopf k ι
  spectrumPointsIso (additivePowerRepresentation (k := k) (ι := ι)).convolutionIso

/-- The Laurent coordinate algebra represents the product of the unit point groups. -/
def multiplicativePowerGroupPointsIso :
    (groupPointsFunctor k).obj (multiplicativePowerGroup k ι).val ≅ multiplicativePowerPoints k ι :=
  spectrumPointsIso laurentPowerIso

end PointComparisons

end StandardGroups
end
end LinearAlgebraicGroups
