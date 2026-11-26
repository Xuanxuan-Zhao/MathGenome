import Specs.LinearAlgebraicGroups.Albert.SplitForms
import LinearAlgebraicGroups.Albert.AutomorphismType
import LinearAlgebraicGroups.Albert.RemoveParameters
import LinearAlgebraicGroups.Albert.SplitModel
import LinearAlgebraicGroups.Albert.AutomorphismScheme
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsSepClosed

/-! Isomorphisms of the split Albert algebra with a faithfully flat form. -/

namespace LinearAlgebraicGroups.Albert.SplitForms

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SplitSpecification SplitFormsSpecification
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open scoped TensorProduct CategoryTheory.MonObj

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1024
set_option maxHeartbeats 1000000

universe u v w

section Coordinates

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {ι₀ : Type u} [Fintype ι₀] [DecidableEq ι₀]

variable (K : ParaQuadratic R N) (J : ParaQuadratic R M)
variable (b : Module.Basis ι₀ R N) (c : Module.Basis ι₀ R M)

open private basisChange_natural matrixAction_natural basisOperationTest_natural
  coordinates_zero_iff matrixActionEquiv quadratic_eq_of_basis
  evaluateMatrix matrixCoordinateEquiv
  spectrumOverProperties from LinearAlgebraicGroups.Albert.AutomorphismScheme

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

private def basisIso (S : Type u) [CommRing S] [Algebra R S] :
    (S ⊗[R] N) ≃ₗ[S] (S ⊗[R] M) :=
  (b.baseChange S).equiv (c.baseChange S) (Equiv.refl ι₀)

private def matrixIso (S : Type u) [CommRing S] [Algebra R S] :
    Matrix.GeneralLinearGroup ι₀ S ≃ ((S ⊗[R] N) ≃ₗ[S] (S ⊗[R] M)) :=
  (matrixActionEquiv b S).toEquiv.trans <|
    (LinearMap.GeneralLinearGroup.generalLinearEquiv S _).toEquiv.trans
      { toFun := fun g => g.trans (basisIso b c S)
        invFun := fun g => g.trans (basisIso b c S).symm
        left_inv := fun g => by apply LinearEquiv.ext; intro x; exact (basisIso b c S).symm_apply_apply _
        right_inv := fun g => by apply LinearEquiv.ext; intro x; exact (basisIso b c S).apply_symm_apply _ }

omit [Fintype ι₀] [DecidableEq ι₀] in
private theorem basisIso_repr (x : S ⊗[R] N) :
    (c.baseChange S).repr (basisIso b c S x) = (b.baseChange S).repr x := by
  simp [basisIso, Module.Basis.equiv]

omit [Fintype ι₀] [DecidableEq ι₀] in
private theorem basisIso_natural (f : S →ₐ[R] T) (x : S ⊗[R] N) :
    f.toLinearMap.rTensor M (basisIso b c S x) =
      basisIso b c T (f.toLinearMap.rTensor N x) := by
  apply (c.baseChange T).repr.injective
  apply Finsupp.ext
  intro i
  rw [basisChange_natural, basisIso_repr, basisIso_repr, basisChange_natural]

private theorem matrixIso_natural (f : S →ₐ[R] T) (g : Matrix.GeneralLinearGroup ι₀ S)
    (x : S ⊗[R] N) :
    f.toLinearMap.rTensor M (matrixIso b c S g x) =
      matrixIso b c T (Matrix.GeneralLinearGroup.map f.toRingHom g) (f.toLinearMap.rTensor N x) := by
  change f.toLinearMap.rTensor M (basisIso b c S (matrixAction b S g x)) =
    basisIso b c T (matrixAction b T (Matrix.GeneralLinearGroup.map f.toRingHom g)
      (f.toLinearMap.rTensor N x))
  rw [basisIso_natural, matrixAction_natural]

private def discrepancy (S : Type u) [CommRing S] [Algebra R S]
    (g : Matrix.GeneralLinearGroup ι₀ S) (a : OperationEquationIndex ι₀) : S :=
  let e := matrixIso b c S g
  (c.baseChange S).repr
    (match a.2 with
     | .inl _ => e (1 ⊗ₜ[R] K.unit) - 1 ⊗ₜ[R] J.unit
     | .inr (i, j) =>
         let x := basisOperationTest b S i
         let y := b.baseChange S j
         e (K.op S x y) - J.op S (e x) (e y)) a.1

private theorem discrepancy_natural (f : S →ₐ[R] T)
    (g : Matrix.GeneralLinearGroup ι₀ S) (a : OperationEquationIndex ι₀) :
    f (discrepancy K J b c S g a) =
      discrepancy K J b c T (Matrix.GeneralLinearGroup.map f.toRingHom g) a := by
  rcases a with ⟨k, _ | ⟨i,j⟩⟩
  · change f ((c.baseChange S).repr
      (matrixIso b c S g (1 ⊗ₜ[R] K.unit) - 1 ⊗ₜ[R] J.unit) k) = _
    rw [← basisChange_natural c f]
    simp only [map_sub, matrixIso_natural, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      map_one, discrepancy]
  · let x := basisOperationTest b S i
    let y := b.baseChange S j
    let e := matrixIso b c S g
    change f ((c.baseChange S).repr (e (K.op S x y) - J.op S (e x) (e y)) k) = _
    rw [← basisChange_natural c f]
    simp only [e, x, y, discrepancy, map_sub, matrixIso_natural, K.natural, J.natural,
      basisOperationTest_natural, Module.Basis.baseChange_apply, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, map_one]

omit [DecidableEq ι₀] in
private theorem checkQuadraticOnBasis
    (e : (S ⊗[R] N) ≃ₗ[S] (S ⊗[R] M))
    (h : ∀ i j, e (K.op S (basisOperationTest b S i) (b.baseChange S j)) =
      J.op S (e (basisOperationTest b S i)) (e (b.baseChange S j))) :
    ∀ x y, e (K.op S x y) = J.op S (e x) (e y) := by
  let post : Module.End S (S ⊗[R] N) →ₗ[S] ((S ⊗[R] N) →ₗ[S] (S ⊗[R] M)) :=
    (e.toLinearMap.compRight S : _)
  let pre : Module.End S (S ⊗[R] M) →ₗ[S] ((S ⊗[R] N) →ₗ[S] (S ⊗[R] M)) :=
    (LinearMap.llcomp S (S ⊗[R] N) (S ⊗[R] M) (S ⊗[R] M)).flip e.toLinearMap
  let Q : QuadraticMap S (S ⊗[R] N) ((S ⊗[R] N) →ₗ[S] (S ⊗[R] M)) :=
    post.compQuadraticMap (K.op S)
  let Q' : QuadraticMap S (S ⊗[R] N) ((S ⊗[R] N) →ₗ[S] (S ⊗[R] M)) :=
    pre.compQuadraticMap ((J.op S).comp e.toLinearMap)
  have eq i : Q (basisOperationTest b S i) = Q' (basisOperationTest b S i) :=
    (b.baseChange S).ext (h i)
  have eq' : Q = Q' := quadratic_eq_of_basis
    (N := ((S ⊗[R] N) →ₗ[S] (S ⊗[R] M))) (b.baseChange S) Q Q'
    (fun i => eq (.inl i)) (fun i j => eq (.inr (i, j)))
  exact fun x y => DFunLike.congr_fun (DFunLike.congr_fun eq' x) y

private theorem discrepancy_iff (g : Matrix.GeneralLinearGroup ι₀ S) :
    (∀ a, discrepancy K J b c S g a = 0) ↔
      let e := matrixIso b c S g
      e (1 ⊗ₜ[R] K.unit) = 1 ⊗ₜ[R] J.unit ∧
        ∀ x y, e (K.op S x y) = J.op S (e x) (e y) := by
  let e := matrixIso b c S g
  constructor
  · intro h
    refine ⟨sub_eq_zero.mp ((coordinates_zero_iff c _).mp (fun i => h (i, .inl ()))), ?_⟩
    exact checkQuadraticOnBasis K J b e fun i j =>
      sub_eq_zero.mp ((coordinates_zero_iff c _).mp (fun a => h (a, .inr (i,j))))
  · rintro ⟨hu, hop⟩ ⟨k, _ | ⟨i,j⟩⟩
    · change (c.baseChange S).repr (e (1 ⊗ₜ[R] K.unit) - 1 ⊗ₜ[R] J.unit) k = 0
      rw [hu, sub_self, map_zero]
      rfl
    · let x := basisOperationTest b S i
      let y := b.baseChange S j
      change (c.baseChange S).repr (e (K.op S x y) - J.op S (e x) (e y)) k = 0
      rw [hop, sub_self, map_zero]
      rfl

local notation "C" => MatrixCoordinates R ι₀

private def isomorphismIdeal : Ideal C :=
  Ideal.span (Set.range (discrepancy K J b c C (evaluateMatrix (AlgHom.id R C))))

private theorem evaluateMatrix_natural (a : C →ₐ[R] S) (f : S →ₐ[R] T) :
    evaluateMatrix (f.comp a) = Matrix.GeneralLinearGroup.map f.toRingHom (evaluateMatrix a) :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

private theorem isomorphismIdeal_iff (a : C →ₐ[R] S) :
    (∀ z ∈ isomorphismIdeal K J b c, a z = 0) ↔
      let e := matrixIso b c S (evaluateMatrix a)
      e (1 ⊗ₜ[R] K.unit) = 1 ⊗ₜ[R] J.unit ∧
        ∀ x y, e (K.op S x y) = J.op S (e x) (e y) := by
  change isomorphismIdeal K J b c ≤ RingHom.ker a.toRingHom ↔ _
  rw [isomorphismIdeal, Ideal.span_le]
  refine Iff.trans ?_ (discrepancy_iff K J b c _)
  rw [Set.range_subset_iff]
  have hm : Matrix.GeneralLinearGroup.map a.toRingHom (evaluateMatrix (AlgHom.id R C)) =
      evaluateMatrix a := (evaluateMatrix_natural (AlgHom.id R C) a).symm
  exact forall_congr' fun i => by
    change a (discrepancy K J b c C (evaluateMatrix (AlgHom.id R C)) i) = 0 ↔ _
    rw [discrepancy_natural, hm]

private abbrev IsomorphismAlgebra := C ⧸ isomorphismIdeal K J b c

private def isomorphismMatrixEquiv :
    (C →ₐ[R] S) ≃ ((S ⊗[R] N) ≃ₗ[S] (S ⊗[R] M)) :=
  matrixCoordinateEquiv.trans (matrixIso b c S)

private def isomorphismPointOfHom (a : IsomorphismAlgebra K J b c →ₐ[R] S) :
    IsomorphismPoints K J S := by
  let I := isomorphismIdeal K J b c
  let f := a.comp (Ideal.Quotient.mkₐ R I)
  refine ⟨isomorphismMatrixEquiv b c f, (isomorphismIdeal_iff K J b c f).mp ?_⟩
  intro z hz
  change a (Ideal.Quotient.mk I z) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]

private def homOfIsomorphismPoint (p : IsomorphismPoints K J S) :
    IsomorphismAlgebra K J b c →ₐ[R] S := by
  let e : (C →ₐ[R] S) ≃ ((S ⊗[R] N) ≃ₗ[S] (S ⊗[R] M)) := isomorphismMatrixEquiv b c
  let a := e.symm p.val
  refine Ideal.Quotient.liftₐ _ a ((isomorphismIdeal_iff K J b c a).mpr ?_)
  change (e a) (1 ⊗ₜ[R] K.unit) = 1 ⊗ₜ[R] J.unit ∧
    ∀ x y, (e a) (K.op S x y) = J.op S (e a x) (e a y)
  rw [e.apply_symm_apply p.val]
  exact p.property

private theorem homOfIsomorphismPoint_comp (p : IsomorphismPoints K J S) :
    (homOfIsomorphismPoint K J b c p).comp (Ideal.Quotient.mkₐ R (isomorphismIdeal K J b c)) =
      (isomorphismMatrixEquiv b c).symm p.val :=
  Ideal.Quotient.liftₐ_comp _ _ _

private def isomorphismPointEquiv :
    (IsomorphismAlgebra K J b c →ₐ[R] S) ≃ IsomorphismPoints K J S where
  toFun := isomorphismPointOfHom K J b c
  invFun := homOfIsomorphismPoint K J b c
  left_inv a := by
    apply Ideal.Quotient.algHom_ext
    rw [homOfIsomorphismPoint_comp]
    exact (isomorphismMatrixEquiv b c).symm_apply_apply _
  right_inv p := by
    apply Subtype.ext
    change isomorphismMatrixEquiv b c
      ((homOfIsomorphismPoint K J b c p).comp (Ideal.Quotient.mkₐ R (isomorphismIdeal K J b c))) = p.val
    rw [homOfIsomorphismPoint_comp]
    exact (isomorphismMatrixEquiv b c).apply_symm_apply _

private theorem isomorphismPointEquiv_natural (f : S →ₐ[R] T)
    (a : IsomorphismAlgebra K J b c →ₐ[R] S) (x : S ⊗[R] N) :
    (isomorphismPointEquiv K J b c (f.comp a)).val (f.toLinearMap.rTensor N x) =
      f.toLinearMap.rTensor M ((isomorphismPointEquiv K J b c a).val x) := by
  let m := a.comp (Ideal.Quotient.mkₐ R (isomorphismIdeal K J b c))
  change matrixIso b c T (evaluateMatrix (f.comp m)) (f.toLinearMap.rTensor N x) =
    f.toLinearMap.rTensor M (matrixIso b c S (evaluateMatrix m) x)
  rw [evaluateMatrix_natural, matrixIso_natural]

/-- Affine representability of the quadratic isomorphism functor. -/
theorem affineRepresentability : AffineRepresentability.{u,v,w} := by
  intro R _ M _ _ N _ _ K J ι₀ _ b c
  classical
  let A := IsomorphismAlgebra K J b c
  let q := op (CommAlgCat.of R A)
  let F := algSpec (CommRingCat.of R)
  letI : F.Full := algSpec.instFull
  letI : F.Faithful := algSpec.instFaithful
  have hA : Algebra.FiniteType R A := by dsimp [A, IsomorphismAlgebra]; infer_instance
  obtain ⟨ha, hf⟩ := spectrumOverProperties (Iso.refl (F.obj q))
  refine ⟨F.obj q, ha, hf, ?_, ⟨?_⟩⟩
  · change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    infer_instance
  let h (S : CommAlgCat R) : (F.obj (op S) ⟶ F.obj q) ≃ (A →ₐ[R] S) :=
    (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.symm.trans
      { toFun := fun p => p.unop.hom
        invFun := fun f => (CommAlgCat.ofHom f).op
        left_inv := fun p => rfl
        right_inv := fun _ => rfl }
  refine
    { points := fun S => (h S).trans (isomorphismPointEquiv K J b c)
      natural := ?_ }
  intro S T f p x
  change (isomorphismPointEquiv K J b c (h T (F.map f.op ≫ p))).val
    (f.hom.toLinearMap.rTensor N x) = _
  have hp : h T (F.map f.op ≫ p) = f.hom.comp (h S p) := by
    have e : F.map f.op ≫ p = F.map (f.op ≫ F.preimage p) := by simp
    rw [e]
    have hh (U : CommAlgCat R) (q' : op U ⟶ q) :
        h U (F.map q') = q'.unop.hom := by
      exact congrArg (fun d => d.unop.hom)
        ((algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.symm_apply_apply q')
    rw [hh]
    conv_rhs => rw [← F.map_preimage p, hh]
    rfl
  rw [hp]
  exact isomorphismPointEquiv_natural K J b c f.hom (h S p) x

end Coordinates

open HermitianSpecification CubicSpecification QuadraticOperatorSpecification
open _root_.LinearAlgebraicGroups.Composition
open Composition.PeirceSpecification (ZornIsomorphism)
open private SplitSpecification.coordinateEquiv zorn_hermitian_transport
  from LinearAlgebraicGroups.Albert.SplitModel

private theorem reducedModel_ground {R : Type u} [CommRing R] {A : Type v}
    [NonAssocRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} {h : Composition.Specification.OctonionNormConditions n}
    {weights : Fin 3 → Rˣ} {J : ParaQuadratic R (Coordinates R A)}
    (hJ : IsReducedModel h weights J) :
    J.unit = cubicUnit ∧ ∀ x y, J.groundOp x y = applyOperator n weights x y := by
  obtain ⟨W, hu, hg, hs, _⟩ := weighted_hermitian_quadratic_jordan weights h
  let W' := ParaQuadratic.ofJordan W
  have hW : J.IsIso W' (LinearEquiv.refl R _) := by
    refine ⟨hJ.1.trans hu.symm, ?_⟩
    intro S _ _ x y
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id, LinearMap.id_apply]
    letI := h.projective
    apply (coordinatesBaseChange (A := A) S).injective
    exact (hJ.2 S x y).trans (hs S x y).symm
  have hWg := (J.isIso_iff_ground W' _).mp hW
  refine ⟨hJ.1, fun x y => ?_⟩
  have he : J.groundOp x y = W'.groundOp x y := by
    simpa only [LinearEquiv.refl_apply] using hWg.2 x y
  refine he.trans ?_
  change W.groundOp x y = _
  exact hg x y

private theorem splitReducedModelInCoordinates {R : Type u} [CommRing R] {A : Type v}
    [NonAssocRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} {h : Composition.Specification.OctonionNormConditions n}
    {weights : Fin 3 → Rˣ} {J : ParaQuadratic R (Coordinates R A)}
    (hJ : IsReducedModel h weights J) (f : ZornIsomorphism n) :
    ∃ K : ParaQuadratic R (SplitRank.octonion.Model R),
      IsSplitModel K .octonion ∧
      J.IsIso K ((SplitSpecification.coordinateEquiv f.toLinearEquiv).symm.trans
        (RemoveParametersSpecification.removeZornWeights weights)) := by
  let F := SplitSpecification.coordinateEquiv f.toLinearEquiv
  let G := RemoveParametersSpecification.removeZornWeights weights
  obtain ⟨hJu, hJo⟩ := reducedModel_ground hJ
  obtain ⟨hFu, hFo⟩ := zorn_hermitian_transport f weights
  obtain ⟨hGu, _, _, _, _, _, _, hGo, _⟩ := zorn_weight_removal.{u,u} R weights
  obtain ⟨K, hKu, hKo⟩ := split_model_exists R .octonion
  let K' := ParaQuadratic.ofJordan K
  refine ⟨K', ⟨LinearEquiv.refl R _, hKu, hKo⟩, (J.isIso_iff_ground K' _).mpr ⟨?_, ?_⟩⟩
  · change G (F.symm J.unit) = K.unit
    rw [hJu, ← hFu, F.symm_apply_apply, hGu, hKu]
  · intro x y
    change G (F.symm (J.groundOp x y)) = K.groundOp (G (F.symm x)) (G (F.symm y))
    have hxy : F.symm (applyOperator n weights x y) =
        applyOperator (Zorn.norm R) weights (F.symm x) (F.symm y) := by
      apply F.injective
      rw [F.apply_symm_apply, hFo, F.apply_symm_apply, F.apply_symm_apply]
    rw [hJo, hKo, hxy]
    exact hGo _ _

/-- The parameter change gives an isomorphism over the original ring. -/
theorem splitReducedModel : SplitReducedModel.{u} := by
  intro R _ h weights J hJ
  let f : ZornIsomorphism (LowerRankSpecification.zornNorm R) :=
    ⟨LinearEquiv.refl R _, rfl, fun _ _ => rfl, fun _ => rfl⟩
  obtain ⟨K, hKs, hIso⟩ := splitReducedModelInCoordinates hJ f
  have hid : SplitSpecification.coordinateEquiv f.toLinearEquiv = LinearEquiv.refl R _ := by
    apply LinearEquiv.ext
    intro x
    rfl
  rw [hid, LinearEquiv.refl_symm, LinearEquiv.refl_trans] at hIso
  exact ⟨K, hKs, hIso⟩

/-- A split octonion input can be put in Zorn coordinates over the original ring. -/
theorem splitReducedModelOfSplitOctonion : SplitReducedModelOfSplitOctonion.{u,v} := by
  intro R _ A _ _ _ _ n h weights J hSplit hJ
  obtain ⟨d, hu, hm, hn⟩ := hSplit
  let e := (Zorn.coordinates R).trans d.symm
  have he (x : Zorn R) : d (e x) = Zorn.coordinates R x := d.apply_symm_apply _
  let f : ZornIsomorphism n :=
    ⟨e, d.injective (by rw [he, Zorn.coordinates_one, hu]),
      fun x y => d.injective (by rw [he, hm, he, he, Zorn.coordinates_mul]),
      fun x => (hn (e x)).trans ((congrArg _ (he x)).trans (Zorn.norm_formula R x).symm)⟩
  obtain ⟨K, hKs, hIso⟩ := splitReducedModelInCoordinates hJ f
  exact ⟨K, f, hKs, hIso⟩


section Torsor

variable {k : Type} [Field k] {M N : Type}
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {K : ParaQuadratic k N} {J : ParaQuadratic k M}

local notation "Base" => Spec (CommRingCat.of k)

private theorem points_ext {S T : CommAlgCat k} (f : S ⟶ T)
    {a b : T ⊗[k] N →ₗ[T] T ⊗[k] M}
    (eq : ∀ x, a (f.hom.toLinearMap.rTensor N x) = b (f.hom.toLinearMap.rTensor N x)) :
    a = b := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul t n =>
      have h := eq (1 ⊗ₜ[k] n)
      rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at h
      have hs : t ⊗ₜ[k] n = t • (1 ⊗ₜ[k] n : T ⊗[k] N) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem isomPoints_ext {S T : CommAlgCat k} (f : S ⟶ T)
    {p q : IsomorphismPoints K J T}
    (eq : ∀ x, p.val (f.hom.toLinearMap.rTensor N x) = q.val (f.hom.toLinearMap.rTensor N x)) :
    p = q :=
  Subtype.ext (LinearEquiv.toLinearMap_injective (points_ext f eq))

private def isoPointCompose (S : CommAlgCat k)
    (p : IsomorphismPoints K J S) (g : IsomorphismPoints K K S) : IsomorphismPoints K J S :=
  ⟨g.val.trans p.val,
    by simpa only [LinearEquiv.trans_apply, g.property.1] using p.property.1,
    fun x y => by simp only [LinearEquiv.trans_apply, g.property.2, p.property.2]⟩

private def isoPointDifference (S : CommAlgCat k)
    (p q : IsomorphismPoints K J S) : IsomorphismPoints K K S :=
  ⟨q.val.trans p.val.symm,
    p.val.injective (by simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      q.property.1, p.property.1]),
    fun x y => p.val.injective (by simp only [LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, q.property.2, p.property.2])⟩

private theorem isoPointCompose_difference (S : CommAlgCat k)
    (p q : IsomorphismPoints K J S) : isoPointCompose S p (isoPointDifference S p q) = q := by
  apply Subtype.ext
  ext x
  exact p.val.apply_symm_apply _

private theorem isoPointDifference_compose (S : CommAlgCat k)
    (p : IsomorphismPoints K J S) (g : IsomorphismPoints K K S) :
    isoPointDifference S p (isoPointCompose S p g) = g := by
  apply Subtype.ext
  ext x
  exact p.val.symm_apply_apply _

private theorem affineHom_ext {X Y : Over Base} [IsAffine X.left] (a b : X ⟶ Y)
    (h : ∀ (S : CommAlgCat k) (p : Points X S), p ≫ a = p ≫ b) : a = b := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr (show IsAffine X.left by infer_instance)
  have he := h A.unop e.hom
  exact (cancel_epi e.hom).mp he

private theorem affineHom_exists {X Y : Over Base} [IsAffine X.left]
    (actionPoints : ∀ S : CommAlgCat k, Points X S → Points Y S)
    (hnat : ∀ {S T : CommAlgCat k} (f : S ⟶ T) (p : Points X S),
      actionPoints T ((algSpec (CommRingCat.of k)).map f.op ≫ p) = (algSpec (CommRingCat.of k)).map f.op ≫ actionPoints S p) :
    ∃ a : X ⟶ Y, ∀ S (p : Points X S), p ≫ a = actionPoints S p := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr (show IsAffine X.left by infer_instance)
  refine ⟨e.inv ≫ actionPoints A.unop e.hom, fun S p => ?_⟩
  let full := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := full.homEquiv.symm (p ≫ e.inv)
  have hf : (algSpec (CommRingCat.of k)).map f = p ≫ e.inv := full.homEquiv.apply_symm_apply _
  have hp : (algSpec (CommRingCat.of k)).map f ≫ e.hom = p := by rw [hf, Category.assoc, e.inv_hom_id, Category.comp_id]
  calc
    p ≫ e.inv ≫ actionPoints A.unop e.hom =
        (algSpec (CommRingCat.of k)).map f ≫ actionPoints A.unop e.hom := by rw [hf, Category.assoc]
    _ = actionPoints S ((algSpec (CommRingCat.of k)).map f ≫ e.hom) :=
      (hnat f.unop e.hom).symm
    _ = actionPoints S p := congrArg (actionPoints S) hp

private theorem affineProduct {X Y : Over Base} [IsAffine X.left] [IsAffine Y.left] :
    IsAffine (X ⨯ Y).left := by
  let e := Over.prodLeftIsoPullback X Y
  exact IsAffine.of_isIso e.hom

private theorem torsor_of_isomorphismRepresentation
    {G : SpinSpecification.GroupScheme k} [IsAffine G.X.left] {X : Over Base} [IsAffine X.left]
    (I : IsomorphismRepresentation K J X)
    (hG : AutomorphismDescentSpecification.RepresentsAutomorphisms K G) :
    ∃ a : ∀ S : CommAlgCat k, Points G.X S →*
          (S ⊗[k] N ≃ₗ[S] S ⊗[k] N),
      (∀ S, Function.Injective (a S) ∧ Set.range (a S) =
        {g | g (1 ⊗ₜ[k] K.unit) = 1 ⊗ₜ[k] K.unit ∧
            ∀ x y, g (K.op S x y) = K.op S (g x) (g y)}) ∧
      (∀ {S T : CommAlgCat k} (f : S ⟶ T) (g : Points G.X S) (x),
        let m := f.hom.toLinearMap.rTensor N
        m (a S g x) = a T ((algSpec (CommRingCat.of k)).map f.op ≫ g) (m x)) ∧
      ∃ act : X ⨯ G.X ⟶ X,
        IsRightAction G act ∧
        (∀ (S : CommAlgCat k) (p : Points X S) (g : Points G.X S) (x),
          (I.points S (prod.lift p g ≫ act)).val x = (I.points S p).val (a S g x)) ∧
        IsIso (prod.lift (prod.fst : X ⨯ G.X ⟶ X) act : X ⨯ G.X ⟶ X ⨯ X) := by
  obtain ⟨a, ha, hn⟩ := hG
  let A (S : CommAlgCat k) : Points G.X S ≃ IsomorphismPoints K K S :=
    Equiv.ofBijective (fun g => ⟨a S g, by
      have h : a S g ∈ Set.range (a S) := Set.mem_range_self g
      rw [(ha S).2] at h
      exact h⟩)
      ⟨fun g g' h => (ha S).1 (congrArg Subtype.val h),
        fun p => by
          have hp : p.val ∈ Set.range (a S) := by
            rw [(ha S).2]
            exact p.property
          obtain ⟨g, hg⟩ := hp
          exact ⟨g, Subtype.ext hg⟩⟩
  let actionPoints (S : CommAlgCat k) (p : Points (X ⨯ G.X) S) : Points X S :=
    (I.points S).symm (isoPointCompose S (I.points S (p ≫ prod.fst)) (A S (p ≫ prod.snd)))
  let δ (S : CommAlgCat k) (p : Points (X ⨯ X) S) : Points G.X S :=
    (A S).symm (isoPointDifference S (I.points S (p ≫ prod.fst)) (I.points S (p ≫ prod.snd)))
  have ha_nat {S T : CommAlgCat k} (f : S ⟶ T) (p : Points G.X S) (x : S ⊗[k] N) :
      (A T ((algSpec (CommRingCat.of k)).map f.op ≫ p)).val (f.hom.toLinearMap.rTensor N x) =
        f.hom.toLinearMap.rTensor N ((A S p).val x) :=
    (hn f p x).symm
  have actionProp (S : CommAlgCat k) (p : Points (X ⨯ G.X) S) :
      I.points S (actionPoints S p) = isoPointCompose S (I.points S (p ≫ prod.fst)) (A S (p ≫ prod.snd)) :=
    (I.points S).apply_symm_apply _
  have δprop (S : CommAlgCat k) (p : Points (X ⨯ X) S) :
      A S (δ S p) = isoPointDifference S (I.points S (p ≫ prod.fst)) (I.points S (p ≫ prod.snd)) :=
    (A S).apply_symm_apply _
  letI : IsAffine (X ⨯ G.X).left := affineProduct
  letI : IsAffine (X ⨯ X).left := affineProduct
  obtain ⟨act, hact⟩ := affineHom_exists actionPoints (by
    intro S T f p
    apply (I.points T).injective
    apply isomPoints_ext f
    intro x
    rw [actionProp, I.natural, actionProp]
    simp only [isoPointCompose, LinearEquiv.trans_apply, Category.assoc]
    rw [ha_nat, I.natural])
  obtain ⟨diff, hdiff⟩ := affineHom_exists δ (by
    intro S T f p
    apply (A T).injective
    apply isomPoints_ext f
    intro x
    rw [δprop, ha_nat, δprop]
    simp only [isoPointDifference, LinearEquiv.trans_apply, Category.assoc]
    apply (I.points T ((algSpec (CommRingCat.of k)).map f.op ≫ p ≫ prod.fst)).val.injective
    rw [LinearEquiv.apply_symm_apply, I.natural, I.natural, LinearEquiv.apply_symm_apply])
  let r : X ⨯ X ⟶ X ⨯ G.X := prod.lift prod.fst diff
  have ht (S : CommAlgCat k) (p : Points (X ⨯ G.X) S) :
      I.points S (p ≫ act) = isoPointCompose S (I.points S (p ≫ prod.fst)) (A S (p ≫ prod.snd)) :=
    (congrArg (I.points S) (hact S p)).trans (actionProp _ _)
  have hr (S : CommAlgCat k) (p : Points (X ⨯ X) S) :
      A S (p ≫ diff) = isoPointDifference S (I.points S (p ≫ prod.fst)) (I.points S (p ≫ prod.snd)) :=
    (congrArg (A S) (hdiff S p)).trans (δprop _ _)
  have evalAct (S : CommAlgCat k) (p : Points (X ⨯ G.X) S) (x : S ⊗[k] N) :
      (I.points S (p ≫ act)).val x =
        (I.points S (p ≫ prod.fst)).val (a S (p ≫ prod.snd) x) := by
    have h := DFunLike.congr_fun (congrArg Subtype.val (ht S p)) x
    simpa only [isoPointCompose, LinearEquiv.trans_apply, A, Equiv.ofBijective_apply] using h
  have hAct (S : CommAlgCat k) (p : Points X S) (g : Points G.X S) (x : S ⊗[k] N) :
      (I.points S (prod.lift p g ≫ act)).val x = (I.points S p).val (a S g x) := by
    simpa only [prod.lift_fst, prod.lift_snd] using evalAct S (prod.lift p g) x
  refine ⟨a, ha, hn, act, ?_, hAct, ⟨⟨r, ?_, ?_⟩⟩⟩
  · constructor
    · apply affineHom_ext
      intro S p
      simp only [← Category.assoc, Limits.prod.comp_lift, Category.comp_id, MonObj.comp_one]
      apply (I.points S).injective
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [hAct, map_one]
      rfl
    · let Y := (X ⨯ G.X) ⨯ G.X
      letI : IsAffine Y.left := affineProduct
      change (prod.lift (prod.fst ≫ act) (prod.snd : Y ⟶ G.X) ≫ act) = _
      apply affineHom_ext
      intro S p
      simp only [← Category.assoc, Limits.prod.comp_lift, MonObj.comp_mul]
      apply (I.points S).injective
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      simp only [evalAct, prod.lift_fst, prod.lift_snd, map_mul, LinearEquiv.mul_apply]
  · apply affineHom_ext
    intro S p
    apply prod.hom_ext
    · simp [r]
    · apply (A S).injective
      simp only [r, Category.assoc, prod.lift_snd, Category.comp_id]
      rw [← Category.assoc p (prod.lift _ _), hr]
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd]
      rw [ht, isoPointDifference_compose]
  · apply affineHom_ext
    intro S p
    apply prod.hom_ext
    · simp [r]
    · apply (I.points S).injective
      simp only [r, Category.assoc, prod.lift_snd, Category.comp_id]
      rw [← Category.assoc p (prod.lift _ _), ht]
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd]
      rw [hr, isoPointCompose_difference]

end Torsor


section BaseChange

variable {k : Type} [Field k]
local notation "Base" => Spec (CommRingCat.of k)

private theorem torsor_trivialization {G X U : Over Base}
    (act : X ⨯ G ⟶ X) [IsIso (prod.lift (prod.fst : X ⨯ G ⟶ X) act : X ⨯ G ⟶ X ⨯ X)]
    (p : U ⟶ X) :
    TrivializesAt act p := by
  let t : X ⨯ G ⟶ X ⨯ X := prod.lift prod.fst act
  let d : X ⨯ X ⟶ G := inv t ≫ prod.snd
  have first : inv t ≫ prod.fst = prod.fst := by
    calc
      inv t ≫ prod.fst = inv t ≫ t ≫ prod.fst := by simp [t]
      _ = prod.fst := by simp
  have dt : prod.lift prod.fst act ≫ d = prod.snd := by simp [d, ← Category.assoc, t]
  have td : (prod.lift prod.fst d : X ⨯ X ⟶ X ⨯ G) ≫ act = prod.snd := by
    have hh : (prod.lift prod.fst d : X ⨯ X ⟶ X ⨯ G) = inv t := by
      apply prod.hom_ext
      · simpa only [prod.lift_fst] using first.symm
      · simp [d]
    rw [hh, ← show t ≫ prod.snd = act by simp [t], ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  let P := Over.pullback U.hom
  let projection (Y : Over Base) : (Over.map U.hom).obj (P.obj Y) ⟶ Y :=
    (Over.mapPullbackAdj U.hom).counit.app Y
  let cover (Y : Over Base) : (Over.map U.hom).obj (P.obj Y) ⟶ U :=
    Over.homMk (P.obj Y).hom rfl
  let a : (Over.map U.hom).obj (P.obj G) ⟶ X := prod.lift (cover G ≫ p) (projection G) ≫ act
  let b : (Over.map U.hom).obj (P.obj X) ⟶ G := prod.lift (cover X ≫ p) (projection X) ≫ d
  let A : P.obj G ⟶ P.obj X := (Over.mapPullbackAdj U.hom).homEquiv _ _ a
  let B : P.obj X ⟶ P.obj G := (Over.mapPullbackAdj U.hom).homEquiv _ _ b
  have cover_comp {Y Z : Over Base} (e : P.obj Y ⟶ P.obj Z) :
      (Over.map U.hom).map e ≫ cover Z = cover Y := by
    apply Over.OverMorphism.ext
    exact Over.w e
  have projection_A : (Over.map U.hom).map A ≫ projection X = a := by
    exact ((Over.mapPullbackAdj U.hom).homEquiv _ _).symm_apply_apply a
  have projection_B : (Over.map U.hom).map B ≫ projection G = b := by
    exact ((Over.mapPullbackAdj U.hom).homEquiv _ _).symm_apply_apply b
  refine ⟨⟨A, B, ?_, ?_⟩, projection_A⟩
  · apply ((Over.mapPullbackAdj U.hom).homEquiv _ _).symm.injective
    change (Over.map U.hom).map (A ≫ B) ≫ projection G = (Over.map U.hom).map (𝟙 _) ≫ projection G
    rw [Functor.map_comp, Category.assoc, projection_B, (Over.map U.hom).map_id, Category.id_comp]
    dsimp only [b]
    rw [← Category.assoc, Limits.prod.comp_lift, ← Category.assoc ((Over.map U.hom).map A) (cover X),
      cover_comp A, projection_A]
    dsimp only [a]
    rw [show (prod.lift (cover G ≫ p) (prod.lift (cover G ≫ p) (projection G) ≫ act)) =
        prod.lift (cover G ≫ p) (projection G) ≫ prod.lift prod.fst act by
          rw [Limits.prod.comp_lift, prod.lift_fst]]
    rw [Category.assoc, dt, prod.lift_snd]
  · apply ((Over.mapPullbackAdj U.hom).homEquiv _ _).symm.injective
    change (Over.map U.hom).map (B ≫ A) ≫ projection X = (Over.map U.hom).map (𝟙 _) ≫ projection X
    rw [Functor.map_comp, Category.assoc, projection_A, (Over.map U.hom).map_id, Category.id_comp]
    dsimp only [a]
    rw [← Category.assoc, Limits.prod.comp_lift, ← Category.assoc ((Over.map U.hom).map B) (cover G),
      cover_comp B, projection_B]
    dsimp only [b]
    rw [show (prod.lift (cover X ≫ p) (prod.lift (cover X ≫ p) (projection X) ≫ d)) =
        prod.lift (cover X ≫ p) (projection X) ≫ prod.lift prod.fst d by
          rw [Limits.prod.comp_lift, prod.lift_fst]]
    rw [Category.assoc, td, prod.lift_snd]

private theorem cover_properties {S : Type} [CommRing S] [Algebra k S] [Module.FaithfullyFlat k S] :
    (Surjective (TestScheme (CommAlgCat.of k S)).hom ∧
      Flat (TestScheme (CommAlgCat.of k S)).hom) ∧
        QuasiCompact (TestScheme (CommAlgCat.of k S)).hom := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k S))
  have hff : (algebraMap k S).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  refine ⟨⟨?_, ?_⟩, inferInstanceAs (QuasiCompact f)⟩
  · exact (surjective_iff f).mpr
      (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := k) (B := S))
  · exact (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hff.flat

private theorem smooth_of_trivialization {G X U : Over Base} (hG : Smooth G.hom)
    (hc : (Surjective U.hom ∧ Flat U.hom) ∧ QuasiCompact U.hom)
    (e : (Over.pullback U.hom).obj G ≅ (Over.pullback U.hom).obj X) :
    Smooth X.hom := by
  let Q : MorphismProperty Scheme := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have h : Q U.hom := hc
  apply MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := Q)
    (IsPullback.of_hasPullback X.hom U.hom).flip h
  letI : IsIso e.inv.left := inferInstance
  change Smooth ((Over.pullback U.hom).obj X).hom
  rw [← Over.w e.inv]
  exact MorphismProperty.RespectsIso.precomp (P := @Smooth) e.inv.left _
    (MorphismProperty.pullback_snd (P := @Smooth) _ _ hG)

private theorem isomorphismPoint_baseChange {M N : Type}
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {K : ParaQuadratic k N} {J : ParaQuadratic k M} {S : Type} [CommRing S] [Algebra k S]
    (p : IsomorphismPoints K J S) : (K.baseChange S).IsIso (J.baseChange S) p.val := by
  apply (ParaQuadratic.isIso_iff_ground _ _ _).mpr
  refine ⟨p.property.1, fun x y => ?_⟩
  rw [ParaQuadratic.groundOp_baseChange, ParaQuadratic.groundOp_baseChange]
  exact p.property.2 x y

open LowerRankSpecification

private theorem untwistedModel_component {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (K : ParaQuadratic R (SplitRank.octonion.Model R))
    (hu : K.unit = cubicUnit)
    (hop : ∀ x y, coordinatesBaseChange (A := Zorn R) S (K.op S x y) =
      applyOperator (Composition.Specification.normBaseChange S (zornNorm R))
        (baseChangedWeights S (untwisted R))
        (coordinatesBaseChange S x) (coordinatesBaseChange S y)) :
    OnComponent K S .octonion := by
  obtain ⟨e, _, he⟩ := (LowerRank.native_base_changes R S).2.2.2
  let e' : Coordinates S (S ⊗[R] Zorn R) ≃ₗ[S] Coordinates S (Zorn S) :=
    (LinearEquiv.refl S _).prodCongr (LinearEquiv.piCongrRight fun _ => e)
  let d := coordinatesBaseChange (R := R) (A := Zorn R) S
  have hw : baseChangedWeights S (untwisted R) = untwisted S := by
    funext i
    exact map_one (Units.map (algebraMap R S).toMonoidHom)
  refine ⟨d.trans e', ?_, fun x y => ?_⟩
  · change e' (d (1 ⊗ₜ[R] K.unit)) = cubicUnit
    rw [hu, show d (1 ⊗ₜ[R] (cubicUnit : Coordinates R (Zorn R))) = cubicUnit
      from extendCoordinates_unit (R := R) (A := Zorn R) S]
    exact he.1
  · change e' (d (K.op S x y)) = applyOperator (zornNorm S) (untwisted S) (e' (d x)) (e' (d y))
    rw [hop, hw]
    exact (he.2.2.2.2.1 _ _).symm

end BaseChange

/-- A nonzero polynomial has a nonzero evaluation over the separable closure. -/
private theorem exists_aeval_ne_zero {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin n) k) (hf : f ≠ 0) :
    ∃ a : Fin n → SeparableClosure k, MvPolynomial.aeval a f ≠ 0 := by
  let E := SeparableClosure k
  haveI : Infinite E := by
    by_contra h
    haveI : Finite E := not_infinite_iff_finite.mp h
    haveI : IsAlgClosed E := IsSepClosed.isAlgClosed_of_perfectField E
    exact h inferInstance
  by_contra! h
  apply hf
  apply MvPolynomial.map_injective (algebraMap k E) (RingHom.injective _)
  rw [map_zero]
  apply MvPolynomial.funext
  intro a
  rw [MvPolynomial.eval_map, map_zero]
  exact h a

/-- A nonempty affine smooth scheme over a field has a finite separable point (Stacks 056U). -/
private theorem finiteSeparablePoint (k A : Type) [Field k] [CommRing A]
    [Algebra k A] [Nontrivial A] [Algebra.Smooth k A] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧ Nonempty (A →ₐ[k] L) := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  haveI : m.IsPrime := hm.isPrime
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := m)
  let P := MvPolynomial (Fin n) k
  let B := Localization.Away f
  haveI : Nontrivial B := by
    have h : (Ideal.map (algebraMap A B) m).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
        ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf)
    exact nontrivial_of_ne 0 1 (fun e => h.one_notMem (e ▸ (Ideal.map (algebraMap A B) m).zero_mem))
  haveI : Algebra.Etale P B := inferInstance
  haveI : Algebra.HasGoingDown P B := Algebra.HasGoingDown.of_flat
  let c := PrimeSpectrum.comap (algebraMap P B)
  have hopen : IsOpen (Set.range c) := by
    rw [← Set.image_univ]
    exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _ isOpen_univ
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum B) := inferInstance
  obtain ⟨U, hU, hq, hsub⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show c q ∈ Set.range c from Set.mem_range_self q) hopen
  rcases hU with ⟨_, ⟨g, rfl⟩, rfl⟩
  have hg : g ≠ 0 := by
    intro e
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hq (e ▸ (c q).asIdeal.zero_mem)
  obtain ⟨a, ha⟩ := exists_aeval_ne_zero g hg
  let D := IntermediateField.adjoin k (Set.range a)
  haveI : Finite (Set.range a) := (Set.finite_range a).to_subtype
  haveI : FiniteDimensional k D := IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsSeparable.isSeparable k x).isIntegral
  let eval : P →ₐ[k] D := MvPolynomial.aeval fun i => ⟨a i, IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩
  have heval : (IntermediateField.val D).comp eval = MvPolynomial.aeval a := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [eval]
  let p : PrimeSpectrum P := ⟨RingHom.ker eval.toRingHom, RingHom.ker_isPrime _⟩
  have hp : p ∈ Set.range c := hsub ((PrimeSpectrum.mem_basicOpen _ _).mpr fun hg' =>
    ha (by simpa only [← heval, AlgHom.comp_apply, RingHom.mem_ker, map_zero] using
      congrArg (IntermediateField.val D) (show eval g = 0 from hg')))
  letI : p.asIdeal.IsPrime := p.isPrime
  let K := p.asIdeal.ResidueField
  let i : K →ₐ[k] D :=
    Ideal.ResidueField.liftₐ p.asIdeal eval le_rfl (fun x hx =>
      isUnit_iff_ne_zero.mpr fun he => hx he)
  haveI : FiniteDimensional k K := FiniteDimensional.of_injective i.toLinearMap
    (RingHom.injective i.toRingHom)
  haveI : Algebra.IsSeparable k K :=
    Algebra.IsSeparable.of_algHom k (SeparableClosure k) ((IntermediateField.val D).comp i)
  let C := K ⊗[P] B
  letI : Algebra K C := Algebra.TensorProduct.leftAlgebra
  letI : Algebra k C := Algebra.TensorProduct.leftAlgebra
  letI : IsScalarTower k K C := inferInstanceAs (IsScalarTower k K (K ⊗[P] B))
  haveI : Nontrivial C := (PrimeSpectrum.nontrivial_iff_mem_rangeComap (S := B) p).mpr hp
  haveI : Algebra.Etale K C := inferInstance
  haveI : Module.Finite K C := Algebra.FormallyUnramified.finite_of_free K C
  obtain ⟨r, hr⟩ := Ideal.exists_maximal C
  haveI : r.IsPrime := hr.isPrime
  let L := C ⧸ r
  letI : Field L := Ideal.Quotient.field r
  letI : Algebra K L := Ideal.Quotient.algebra K
  letI : Algebra k L := Ideal.Quotient.algebra k
  letI : IsScalarTower k K L := Ideal.Quotient.isScalarTower k K r
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : Module.Finite K L := inferInstance
  haveI : FiniteDimensional k L := Module.Finite.trans K L
  haveI : Algebra.IsSeparable k L := Algebra.IsSeparable.trans k K L
  let j : B →ₐ[P] C := Algebra.TensorProduct.includeRight
  let map : A →ₐ[k] L :=
    ((Ideal.Quotient.mkₐ K r).restrictScalars k).comp
      ((j.restrictScalars k).comp (IsScalarTower.toAlgHom k A B))
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ⟨map⟩⟩

section SeparableSplitting

variable {k : Type} [Field k]
local notation "Base" => Spec (CommRingCat.of k)

private theorem finiteSeparableSchemePoint {X : Over Base} [IsAffine X.left]
    [Smooth X.hom] (hx : Surjective X.hom) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧ Nonempty (Points X (CommAlgCat.of k L)) := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (show IsAffine X.left by infer_instance)
  have hSmooth : Smooth ((algSpec (CommRingCat.of k)).obj A).hom := by
    rw [← Over.w e.hom]
    exact MorphismProperty.RespectsIso.precomp (P := @Smooth) e.hom.left _ inferInstance
  have hSurj : Surjective ((algSpec (CommRingCat.of k)).obj A).hom := by
    rw [← Over.w e.hom]
    letI := hx
    infer_instance
  letI : Nontrivial A.unop :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp
      ⟨((surjective_iff _).mp hSurj (IsLocalRing.closedPoint k)).choose⟩
  letI : Algebra.Smooth k A.unop :=
    RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hSmooth)
  obtain ⟨L, _, _, hfinite, hsep, ⟨φ⟩⟩ := finiteSeparablePoint k A.unop
  exact ⟨L, inferInstance, inferInstance, hfinite, hsep,
    ⟨(algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op ≫ e.hom⟩⟩

private theorem point_from_components {M N S : Type} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [CommRing S] [Algebra k S]
    {J : ParaQuadratic k M} {K : ParaQuadratic k N}
    (hK : OnComponent K S .octonion) (hJ : OnComponent J S .octonion) :
    Nonempty (IsomorphismPoints K J S) := by
  obtain ⟨eK, hKu, hKo⟩ := hK
  obtain ⟨eJ, hJu, hJo⟩ := hJ
  refine ⟨⟨eK.trans eJ.symm, ?_, fun x y => ?_⟩⟩
  · apply eJ.injective
    simpa only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using hKu.trans hJu.symm
  · apply eJ.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hJo, hKo]

/-- The isomorphism torsor is smooth and has a point over a finite separable extension. -/
theorem separableSplitting : SeparableSplitting := by
  intro k _ M _ _ J hJ
  obtain ⟨W, hu, hground, hop, _⟩ :=
    weighted_hermitian_quadratic_jordan (LowerRankSpecification.untwisted k) (Zorn.isOctonion k)
  let K := ParaQuadratic.ofJordan W
  have hK : IsSplitModel K .octonion := ⟨LinearEquiv.refl _ _, hu, hground⟩
  have components (S : Type) [CommRing S] [Algebra k S] : OnComponent K S .octonion :=
    untwistedModel_component K hu (hop S)
  have hKa : IsAlbert K :=
    (albert_iff_split_octonion_after_cover K).mpr ⟨k, inferInstance, inferInstance, inferInstance, components k⟩
  obtain ⟨D, allForms⟩ := AutomorphismType.automorphismType
  obtain ⟨G, hGa, _, hRep, hGs, _⟩ := allForms K hKa
  haveI : IsAffine G.X.left := hGa
  haveI : Module.Finite k M := (freudenthal_finite_projective J hJ.1).1
  let N := SplitRank.octonion.Model k
  obtain ⟨hNfin, hNfree, hNrank⟩ := split_model_rank k .octonion
  haveI : Module.Finite k N := hNfin
  haveI : Module.Free k N := hNfree
  let closed := IsLocalRing.closedPoint k
  have hm : Module.finrank k M = 27 := by
    have h := hJ.2 closed
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h
  have hn : Module.finrank k N = 27 := by
    have h := hNrank closed
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h
  obtain ⟨X, hXa, hXft, hXqc, ⟨I⟩⟩ :=
    affineRepresentability K J (Module.finBasisOfFinrankEq k N hn) (Module.finBasisOfFinrankEq k M hm)
  haveI : IsAffine X.left := hXa
  obtain ⟨a, ha, hNat, act, hRight, hAct, hIso⟩ := torsor_of_isomorphismRepresentation I hRep
  haveI := hIso
  obtain ⟨S, _, _, hSf, hJs⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  haveI := hSf
  obtain ⟨iso⟩ := point_from_components (components S) hJs
  let p := (I.points (CommAlgCat.of k S)).symm iso
  have hCover := cover_properties (k := k) (S := S)
  obtain ⟨triv, _⟩ := torsor_trivialization act p
  have hXs : Smooth X.hom := smooth_of_trivialization hGs hCover triv
  haveI := hXs
  have hXsurj : Surjective X.hom := by
    apply (surjective_iff _).mpr
    intro x
    obtain ⟨y, hy⟩ := (surjective_iff _).mp hCover.1.1 x
    exact ⟨p.left y, by simpa only [← Scheme.Hom.comp_apply, Over.w p] using hy⟩
  refine ⟨K, G, X, I, hK, hGa, hGs, hXa, hXft, hXqc, inferInstance, hXsurj, hXs,
    a, ha, hNat, ⟨act, hRight, hAct, hIso,
      fun S q => ⟨torsor_trivialization act q, isomorphismPoint_baseChange (I.points S q)⟩⟩,
    ⟨S, inferInstance, inferInstance, hSf, ⟨p⟩⟩, ?_⟩
  obtain ⟨L, _, _, hFin, hSep, ⟨pL⟩⟩ := finiteSeparableSchemePoint hXsurj
  refine ⟨L, inferInstance, inferInstance, hFin, hSep, ⟨pL⟩,
    (J.isSplitModel_baseChange_iff L .octonion).mpr ?_⟩
  obtain ⟨e, hEu, hEo⟩ := components L
  obtain ⟨φ, hφu, hφo⟩ := I.points (CommAlgCat.of k L) pL
  refine ⟨φ.symm.trans e, ?_, fun x y => ?_⟩
  · exact (congrArg e (φ.symm_apply_eq.mpr hφu.symm)).trans hEu
  · have hinv : φ.symm (J.op L x y) = K.op L (φ.symm x) (φ.symm y) := by
      apply φ.injective
      rw [φ.apply_symm_apply, hφo, φ.apply_symm_apply, φ.apply_symm_apply]
    exact (congrArg e hinv).trans (hEo _ _)

end SeparableSplitting

end
end LinearAlgebraicGroups.Albert.SplitForms
