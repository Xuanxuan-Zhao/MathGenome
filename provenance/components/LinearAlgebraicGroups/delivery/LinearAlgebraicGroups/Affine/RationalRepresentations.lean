import Specs.LinearAlgebraicGroups.Affine.RationalRepresentations
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Affine.ComoduleFiniteness
import LinearAlgebraicGroups.Affine.SmoothnessCriteria
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Coalgebra HopfAlgebra WithConv Opposite
open scoped TensorProduct BigOperators

universe u

namespace LinearAlgebraicGroups
namespace RationalRepresentations

noncomputable section

/-- A rational representation in a finite basis is a group scheme map
to a group representing the general linear point functor. -/
abbrev Representation {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    (G : AffineGroupCategory k) (L : Specs.GroupScheme k)
    (_ : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k ι) : Type u :=
  G.val ⟶ L

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι]
  (A : HopfAlgebraCategory k) (b : Module.Basis ι k V)

omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem tensorCoordinate_tmul {C : Type u} [AddCommGroup C] [Module k C]
    (i : ι) (x : V) (a : C) :
    tensorCoordinate b i (x ⊗ₜ[k] a) = b.coord i x • a := by
  simp [tensorCoordinate]

omit [DecidableEq ι] in
private theorem tensor_eq_sum_basis {C : Type u} [AddCommGroup C] [Module k C]
    (t : V ⊗[k] C) : (∑ i, b i ⊗ₜ[k] tensorCoordinate b i t) = t := by
  refine TensorProduct.inductionOn (motive := fun t ↦ (∑ i, b i ⊗ₜ[k] tensorCoordinate b i t) = t) t ?_ ?_
  · intro x a
    simp_rw [tensorCoordinate_tmul, ← TensorProduct.smul_tmul, Module.Basis.coord_apply]
    rw [← TensorProduct.sum_tmul, b.sum_repr]
  · intro x y hx hy
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

omit [DecidableEq ι] in
private theorem tensorCoordinate_sum_basis {C : Type u} [AddCommGroup C] [Module k C]
    (a : ι → C) (i : ι) :
    tensorCoordinate b i (∑ j, b j ⊗ₜ[k] a j) = a i := by
  simp

omit [DecidableEq ι] in
theorem coaction_apply_basis (ρ : RightComodule k A V) (j : ι) :
    ρ.coaction (b j) = ∑ i, b i ⊗ₜ[k] coefficients A b ρ i j :=
  (tensor_eq_sum_basis b _).symm

omit [DecidableEq ι] in
private theorem coassoc_basis (d : V →ₗ[k] V ⊗[k] A) (M : Matrix ι ι A)
    (hd : ∀ j, d (b j) = ∑ i, b i ⊗ₜ[k] M i j) (j : ι) :
    TensorProduct.assoc k V A A (d.rTensor A (d (b j))) =
      ∑ i, b i ⊗ₜ[k] (∑ l, M i l ⊗ₜ[k] M l j) := by
  conv_lhs => rw [hd j]
  simp only [map_sum, LinearMap.rTensor_tmul, hd, TensorProduct.sum_tmul,
    TensorProduct.assoc_tmul, TensorProduct.tmul_sum]
  exact Finset.sum_comm

omit [DecidableEq ι] in
private theorem counit_basis (d : V →ₗ[k] V ⊗[k] A) (M : Matrix ι ι A)
    (hd : ∀ j, d (b j) = ∑ i, b i ⊗ₜ[k] M i j) (j : ι) :
    TensorProduct.rid k V ((Coalgebra.counit (R := k) (A := A)).lTensor V (d (b j))) =
      ∑ i, counit (R := k) (M i j) • b i := by
  rw [hd]
  simp

theorem coefficients_isCoactionMatrix (ρ : RightComodule k A V) :
    IsCoactionMatrix A (coefficients A b ρ) := by
  constructor
  · intro i j
    have h := ρ.coassoc (b j)
    rw [coassoc_basis A b _ _ (coaction_apply_basis A b ρ)] at h
    rw [show LinearMap.lTensor V (Coalgebra.comul (R := k) (A := A))
        (ρ.coaction (b j)) = ∑ l, b l ⊗ₜ[k] comul (R := k) (coefficients A b ρ l j) by
      rw [coaction_apply_basis A b ρ j]
      simp] at h
    simpa only [tensorCoordinate_sum_basis] using
      (congrArg (tensorCoordinate b i) h).symm
  · intro i j
    have h := ρ.counit (b j)
    rw [counit_basis A b _ _ (coaction_apply_basis A b ρ)] at h
    simpa [Matrix.one_apply, Module.Basis.coord_apply, Finsupp.single_apply, mul_ite, eq_comm]
      using congrArg (b.coord i) h

omit [DecidableEq ι] in
theorem coefficients_injective : Function.Injective (coefficients A b) := by
  intro σ ρ h
  have he : σ.coaction = ρ.coaction := b.ext fun j ↦ by
    rw [coaction_apply_basis A b σ, coaction_apply_basis A b ρ, h]
  cases σ
  cases ρ
  cases he
  rfl

/-- The unique coaction with the given matrix coefficients. -/
def coactionOfMatrix (M : Matrix ι ι A) (h : IsCoactionMatrix A M) : RightComodule k A V := by
  let d : V →ₗ[k] V ⊗[k] A := b.constr k fun j ↦ ∑ i, b i ⊗ₜ[k] M i j
  have hd : ∀ j, d (b j) = ∑ i, b i ⊗ₜ[k] M i j := b.constr_basis k _
  refine ⟨d, ?_, ?_⟩
  · have he : (TensorProduct.assoc k V A A).toLinearMap.comp ((d.rTensor A).comp d) =
        (LinearMap.lTensor V (Coalgebra.comul (R := k) (A := A))).comp d := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [coassoc_basis A b d M hd, hd]
      simp only [map_sum, LinearMap.lTensor_tmul, h.comul]
    exact DFunLike.congr_fun he
  · have he : (TensorProduct.rid k V).toLinearMap.comp
        (((Coalgebra.counit (R := k) (A := A)).lTensor V).comp d) = LinearMap.id := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      rw [counit_basis A b d M hd]
      simp [h.counit, Matrix.one_apply, eq_comm, ite_smul]
    exact DFunLike.congr_fun he

@[simp] theorem coefficients_coactionOfMatrix (M : Matrix ι ι A) (h : IsCoactionMatrix A M) :
    coefficients A b (coactionOfMatrix A b M h) = M := by
  ext i j
  change tensorCoordinate b i ((b.constr k (fun j ↦ ∑ l, b l ⊗ₜ[k] M l j)) (b j)) = M i j
  rw [b.constr_basis, tensorCoordinate_sum_basis]

theorem coactionMatrixComparison : Specs.RationalRepresentations.CoactionMatrixComparison.{u} := by
  intro k V ι _ _ _ _ _ A b
  exact ⟨coefficients_isCoactionMatrix A b, coefficients_injective A b,
    fun M h ↦ ⟨coactionOfMatrix A b M h, coefficients_coactionOfMatrix A b M h⟩⟩

section PointMatrices

open Algebra.TensorProduct

omit [Fintype ι] [DecidableEq ι] in
private theorem algHom_tmul_sum {B D : Type u} [CommRing B] [Algebra k B]
    [CommRing D] [Algebra k D] {J : Type u} [Fintype J]
    (f g : B →ₐ[k] D) (a c : J → B) :
    lift f g (fun _ _ ↦ Commute.all _ _) (∑ j, a j ⊗ₜ[k] c j) =
      ∑ j, f (a j) * g (c j) := by
  simp

private theorem antipode_mul_matrix (M : Matrix ι ι A) (h : IsCoactionMatrix A M) :
    ((antipodeAlgHom k A).mapMatrix M) * M = 1 := by
  ext i j
  have h' := mul_antipode_rTensor_comul_apply (R := k) (M i j)
  rw [h.comul, h.counit] at h'
  simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite] using h'

private theorem mul_antipode_matrix (M : Matrix ι ι A) (h : IsCoactionMatrix A M) :
    M * ((antipodeAlgHom k A).mapMatrix M) = 1 := by
  ext i j
  have h' := mul_antipode_lTensor_comul_apply (R := k) (M i j)
  rw [h.comul, h.counit] at h'
  simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite] using h'

private def unitMatrix (M : Matrix ι ι A) (h : IsCoactionMatrix A M) :
    Matrix.GeneralLinearGroup ι A :=
  ⟨M, (antipodeAlgHom k A).mapMatrix M, mul_antipode_matrix A M h, antipode_mul_matrix A M h⟩

/-- A coaction matrix gives a group representation on every test algebra. -/
def matrixPointHom (M : Matrix ι ι A) (h : IsCoactionMatrix A M) :
    convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints k ι where
  app R := letI := convolutionGroup A R; GrpCat.ofHom
    { toFun := fun f ↦ Matrix.GeneralLinearGroup.map f.ofConv.toRingHom (unitMatrix A M h)
      map_one' := by
        apply Units.ext
        ext i j
        change (1 : WithConv (A →ₐ[k] R)) (M i j) = (1 : Matrix ι ι R) i j
        rw [AlgHom.convOne_apply, h.counit]
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      map_mul' := fun f g ↦ by
        apply Units.ext
        ext i j
        change (f * g) (M i j) = ((f.ofConv.mapMatrix M) * (g.ofConv.mapMatrix M)) i j
        rw [AlgHom.convMul_apply, h.comul, Matrix.mul_apply, algHom_tmul_sum]
        rfl }
  naturality R S c := by
    apply GrpCat.ext
    intro f
    apply Units.ext
    ext i j
    rfl

private def pointMatrix (α : convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints k ι) :
    Matrix ι ι A :=
  (α.app (CommAlgCat.of k A) (toConv (AlgHom.id k A))).val

private theorem pointMatrix_evaluation
    (α : convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints k ι)
    (R : TestAlgebra k) (f : WithConv (A →ₐ[k] R)) :
    (α.app R f).val = f.ofConv.mapMatrix (pointMatrix A α) := by
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
    (α.naturality (CommAlgCat.ofHom f.ofConv))) (toConv (AlgHom.id k A))
  exact congrArg Units.val h

private theorem pointMatrix_injective :
    Function.Injective (pointMatrix A (ι := ι)) := by
  intro α β h
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro f
  exact Units.ext ((pointMatrix_evaluation A α R f).trans
    ((congrArg f.ofConv.mapMatrix h).trans (pointMatrix_evaluation A β R f).symm))

private theorem pointMatrix_isCoactionMatrix
    (α : convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints k ι) :
    IsCoactionMatrix A (pointMatrix A α) := by
  constructor
  · intro i j
    let R := CommAlgCat.of k (A ⊗[k] A)
    let f : WithConv (A →ₐ[k] R) := toConv includeLeft
    let g : WithConv (A →ₐ[k] R) := toConv includeRight
    have hfg : (f * g).ofConv = Bialgebra.comulAlgHom k A := by
      ext x
      rw [show (f * g).ofConv x = (f * g) x from rfl, AlgHom.convMul_apply]
      have hid : lift f.ofConv g.ofConv (fun _ _ ↦ Commute.all _ _) = AlgHom.id k R := by
        exact lift_includeLeft_includeRight
      rw [hid]
      rfl
    have h := congrArg Units.val ((α.app R).hom.map_mul f g)
    change (α.app R (f * g)).val = (α.app R f).val * (α.app R g).val at h
    rw [pointMatrix_evaluation A α R (f * g), pointMatrix_evaluation A α R f,
      pointMatrix_evaluation A α R g, hfg] at h
    change comul (R := k) (pointMatrix A α i j) = _
    have h' := congrArg (fun M : Matrix ι ι R ↦ M i j) h
    change comul (R := k) (pointMatrix A α i j) =
      ∑ l, (pointMatrix A α i l ⊗ₜ[k] 1) * (1 ⊗ₜ[k] pointMatrix A α l j) at h'
    simpa only [tmul_mul_tmul, mul_one, one_mul] using h'
  · intro i j
    let R := CommAlgCat.of k k
    have h := congrArg Units.val ((α.app R).hom.map_one)
    change (α.app R 1).val = (1 : Matrix ι ι k) at h
    rw [pointMatrix_evaluation A α R 1] at h
    exact congrArg (fun M : Matrix ι ι k ↦ M i j) h

@[simp] private theorem pointMatrix_matrixPointHom (M : Matrix ι ι A) (h : IsCoactionMatrix A M) :
    pointMatrix A (matrixPointHom A M h) = M := by
  ext i j
  change AlgHom.id k A (M i j) = M i j
  rfl

/-- The equivalence is determined by evaluating at the coordinate algebra's universal point. -/
def pointsCoactionEquiv :
    (convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints k ι) ≃ RightComodule k A V where
  toFun α := coactionOfMatrix A b (pointMatrix A α) (pointMatrix_isCoactionMatrix A α)
  invFun ρ := matrixPointHom A (coefficients A b ρ) (coefficients_isCoactionMatrix A b ρ)
  left_inv α := pointMatrix_injective A (by simp)
  right_inv ρ := coefficients_injective A b (by simp)

private def representationPointsEquiv (G : AffineGroupCategory k) (L : Specs.GroupScheme k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k ι) :
    Representation G L l ≃ (convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints k ι) :=
  (groupHomEquiv G.val L G.property).trans
    (Iso.homCongr e.symm l)

theorem representationCoactionComparison :
    Specs.RationalRepresentations.RepresentationCoactionComparison.{u} := by
  intro k V ι _ _ _ _ _ A b G L e l
  refine ⟨(representationPointsEquiv A G L e l).trans (pointsCoactionEquiv A b), ?_⟩
  intro f
  let α := representationPointsEquiv A G L e l f
  change coefficients A b (coactionOfMatrix A b (pointMatrix A α)
    (pointMatrix_isCoactionMatrix A α)) = _
  rw [coefficients_coactionOfMatrix]
  rfl

end PointMatrices

theorem evaluationComparison : Specs.RationalRepresentations.EvaluationComparison.{u} := by
  intro k V ι _ _ _ _ _ A b G L e l f ρ h R g j
  let α := representationPointsEquiv A G L e l f
  have hg := pointMatrix_evaluation A α R (toConv g)
  change (l.hom.app R (((groupPointsFunctor k).map f).app R
    (e.hom.app R (toConv g)))).val = g.mapMatrix (universalMatrix A G L e l f) at hg
  unfold evaluate
  rw [LinearMap.comp_apply, coaction_apply_basis A b ρ, h, hg]
  simp

section Subspaces

variable {W : Type u} [AddCommGroup W] [Module k W]

private theorem evaluate_natural {R : Type u} [CommRing R] [Algebra k R]
    (g : A →ₐ[k] R) (f : V →ₗ[k] W) :
    (f.rTensor R).comp (g.toLinearMap.lTensor V) =
      (g.toLinearMap.lTensor W).comp (f.rTensor A) := by
  apply TensorProduct.ext'
  intro x a
  simp

@[simp] theorem evaluate_id (ρ : RightComodule k A V) :
    evaluate A ρ (AlgHom.id k A) = ρ.coaction := by
  unfold evaluate
  rw [show (AlgHom.id k A).toLinearMap.lTensor V = LinearMap.id by
    apply TensorProduct.ext'
    intro x a
    rfl]
  simp

theorem equivariantMaps : Specs.RationalRepresentations.EquivariantMaps.{u} := by
  intro k V W _ _ _ _ _ A ρ σ f
  constructor
  · intro h
    simpa using h (CommAlgCat.of k A) (AlgHom.id k A)
  · intro h R g
    unfold evaluate
    rw [← LinearMap.comp_assoc, evaluate_natural A g f, LinearMap.comp_assoc, h,
      LinearMap.comp_assoc]

theorem stableSubspaces : Specs.RationalRepresentations.StableSubspaces.{u} := by
  intro k V _ _ _ A ρ W
  constructor
  · intro h x
    simpa using h (CommAlgCat.of k A) (AlgHom.id k A) x
  · intro h R g x
    obtain ⟨y, hy⟩ := h x
    refine ⟨g.toLinearMap.lTensor W y, ?_⟩
    calc
      W.subtype.rTensor R (g.toLinearMap.lTensor W y) =
          g.toLinearMap.lTensor V (W.subtype.rTensor A y) :=
        DFunLike.congr_fun (evaluate_natural A g W.subtype) y
      _ = evaluate A ρ g x := by rw [hy]; rfl

@[simp] theorem trivialLinearMap_apply (x : V) :
    trivialLinearMap A x = x ⊗ₜ[k] (1 : A) := rfl

@[simp] theorem invariantDifference_apply (ρ : RightComodule k A V) (x : V) :
    invariantDifference A ρ x = ρ.coaction x - x ⊗ₜ[k] (1 : A) := rfl

theorem invariantKernel : Specs.RationalRepresentations.InvariantKernel.{u} := by
  intro k V _ _ _ A ρ x
  rw [invariants, invariantDifference, LinearMap.mem_ker, LinearMap.sub_apply, trivialLinearMap_apply, sub_eq_zero]
  constructor
  · intro h
    simpa using h (CommAlgCat.of k A) (AlgHom.id k A)
  · intro h R g
    simp [evaluate, h]

end Subspaces

section Operations

open Algebra.TensorProduct

private theorem isCoactionMatrix_tensor {J : Type u} [Fintype J] [DecidableEq J]
    {M : Matrix ι ι A} {N : Matrix J J A} (hM : IsCoactionMatrix A M) (hN : IsCoactionMatrix A N) :
    IsCoactionMatrix A (fun (i j : ι × J) ↦ M i.1 j.1 * N i.2 j.2) := by
  constructor
  · intro i j
    simp only [Bialgebra.comul_mul, hM.comul, hN.comul, Finset.sum_mul, Finset.mul_sum,
      tmul_mul_tmul, Fintype.sum_prod_type]
    exact Finset.sum_comm
  · intro i j
    simp only [Bialgebra.counit_mul, hM.counit, hN.counit, Matrix.one_apply, Prod.ext_iff]
    split <;> split <;> simp_all

/-- Tensor product of right comodules, with coefficients in the product basis. -/
def tensorCoaction {W J : Type u} [AddCommGroup W] [Module k W] [Fintype J] [DecidableEq J]
    (c : Module.Basis J k W) (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    RightComodule k A (V ⊗[k] W) :=
  coactionOfMatrix A (b.tensorProduct c) _
    (isCoactionMatrix_tensor A (coefficients_isCoactionMatrix A b ρ)
      (coefficients_isCoactionMatrix A c σ))

theorem tensorProductComparison : Specs.RationalRepresentations.TensorProductComparison.{u} := by
  intro k V W ι J _ _ _ _ _ _ _ _ _ A b c ρ σ
  refine ⟨tensorCoaction A b c ρ σ, ?_⟩
  intro i j
  let M : Matrix (ι × J) (ι × J) A :=
    fun i j ↦ coefficients A b ρ i.1 j.1 * coefficients A c σ i.2 j.2
  have hM : IsCoactionMatrix A M :=
    isCoactionMatrix_tensor A (coefficients_isCoactionMatrix A b ρ)
      (coefficients_isCoactionMatrix A c σ)
  exact congrArg (fun N : Matrix (ι × J) (ι × J) A ↦ N i j)
    (coefficients_coactionOfMatrix A (b.tensorProduct c) M hM)

/-- Inverse-transpose on units, in the standard matrix bases. -/
private def inverseTranspose (R : Type u) [CommRing R] :
    Matrix.GeneralLinearGroup ι R →* Matrix.GeneralLinearGroup ι R where
  toFun f := ⟨f.inv.transpose, f.val.transpose,
    by rw [← Matrix.transpose_mul, f.val_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, f.inv_val, Matrix.transpose_one]⟩
  map_one' := by apply Units.ext; exact Matrix.transpose_one
  map_mul' f g := by apply Units.ext; exact Matrix.transpose_mul _ _

private def dualPoints :
    Specs.StandardGroups.generalLinearPoints k ι ⟶ Specs.StandardGroups.generalLinearPoints k ι where
  app R := GrpCat.ofHom (inverseTranspose R)
  naturality R S h := by
    apply GrpCat.ext
    intro g
    apply Units.ext
    ext i j
    rfl

/-- The contragredient coaction on the dual space. -/
def dualCoaction (ρ : RightComodule k A V) : RightComodule k A (Module.Dual k V) :=
  let M := coefficients A b ρ
  let α := matrixPointHom A M (coefficients_isCoactionMatrix A b ρ) ≫ dualPoints (k := k) (ι := ι)
  coactionOfMatrix A b.dualBasis (pointMatrix A α) (pointMatrix_isCoactionMatrix A α)

theorem dualComparison : Specs.RationalRepresentations.DualComparison.{u} := by
  intro k V ι _ _ _ _ _ A b ρ
  refine ⟨dualCoaction A b ρ, ?_⟩
  intro i j
  simp only [dualCoaction, coefficients_coactionOfMatrix]
  change AlgHom.id k A ((antipodeAlgHom k A) (coefficients A b ρ j i)) = _
  rfl

private theorem isCoactionMatrix_extension (K : Type u) [Field K] [Algebra k K]
    {M : Matrix ι ι A} (hM : IsCoactionMatrix A M) :
    IsCoactionMatrix (scalarExtension A K) (fun i j ↦ (1 : K) ⊗ₜ[k] M i j) := by
  constructor
  · intro i j
    rw [TensorProduct.comul_tmul, Bialgebra.comul_one, hM.comul]
    simp [TensorProduct.tmul_sum, Algebra.TensorProduct.one_def,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  · intro i j
    rw [TensorProduct.counit_tmul, Bialgebra.counit_one, hM.counit]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- The coaction on the extended space over the extended coordinate Hopf algebra. -/
def scalarExtensionCoaction (K : Type u) [Field K] [Algebra k K]
    (ρ : RightComodule k A V) :
    RightComodule K (scalarExtension A K) (K ⊗[k] V) :=
  coactionOfMatrix (scalarExtension A K) (b.baseChange K) _
    (isCoactionMatrix_extension A K (coefficients_isCoactionMatrix A b ρ))

theorem fieldExtensionComparison : Specs.RationalRepresentations.FieldExtensionComparison.{u} := by
  intro k K V ι _ _ _ _ _ _ _ A b ρ
  let B := scalarExtension A K
  let M : Matrix ι ι B := fun i j ↦ (1 : K) ⊗ₜ[k] coefficients A b ρ i j
  let σ := scalarExtensionCoaction A b K ρ
  have hσ : coefficients B (b.baseChange K) σ = M := by
    exact coefficients_coactionOfMatrix B (b.baseChange K) M
      (isCoactionMatrix_extension A K (coefficients_isCoactionMatrix A b ρ))
  refine ⟨σ, fun i j ↦ congrArg (fun N : Matrix ι ι B ↦ N i j) hσ, ?_, ?_⟩
  · let d : (K ⊗[k] (V ⊗[k] A)) ≃ₗ[K] ((K ⊗[k] V) ⊗[K] B) :=
      TensorProduct.AlgebraTensorModule.distribBaseChange k K V A
    have he : invariantDifference B σ =
        d.toLinearMap.comp ((invariantDifference A ρ).baseChange K) := by
      apply (b.baseChange K).ext
      intro j
      simp only [invariantDifference_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [coaction_apply_basis B (b.baseChange K) σ, hσ]
      simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
      rw [invariantDifference_apply A ρ, coaction_apply_basis A b ρ j]
      simp [d, M, TensorProduct.tmul_sum, TensorProduct.tmul_sub]
      rfl
    unfold invariants
    rw [he, LinearMap.ker_comp_of_ker_eq_bot _ (LinearEquiv.ker d)]
    exact Module.Flat.ker_lTensor_eq K K _
  · intro R g i j
    change g (coefficients B (b.baseChange K) σ i j) = _
    rw [hσ]
    rfl

end Operations

theorem affineRepresentationComparison : Specs.RationalRepresentations.AffineRepresentationComparison.{u} := by
  intro k V ι _ _ _ _ _ h G b
  let A := ((affineHopfSpec k).inv.obj G).unop
  let L := StandardGroups.generalLinearGroup k ι
  obtain ⟨e, he⟩ := coordinateHopfPoints k G
  let l := StandardGroups.generalLinearGroupPointsIso (k := k) (ι := ι)
  obtain ⟨E, hE⟩ := representationCoactionComparison A b G L.val e l
  exact ⟨L, e, l, E, he, hE⟩

/-- Rational representations on a finite-dimensional vector space, using its
standard choice of a basis indexed by its dimension to realize the group GL(V). -/
abbrev RationalRepresentation (G : AffineGroupCategory k) (V : Type u)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] :=
  Representation G (StandardGroups.generalLinearGroup k (ULift.{u} (Fin (Module.finrank k V)))).val
    (StandardGroups.generalLinearGroupPointsIso (k := k) (ι := ULift.{u} (Fin (Module.finrank k V))))

/-- Coactions on the space of a representation over the coordinate Hopf algebra of G. -/
def rationalRepresentationCoactionEquiv (G : AffineGroupCategory k) (V : Type u)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    RationalRepresentation G V ≃ RightComodule k (coordinateHopf G) V :=
  let A := coordinateHopf G
  let L := StandardGroups.generalLinearGroup k (ULift.{u} (Fin (Module.finrank k V)))
  let e := hopfSpecPointIso A ≪≫
    (groupPointsFunctor k).mapIso ((affineGroupInclusion k).mapIso (coordinateHopfSpecIso G))
  let l := StandardGroups.generalLinearGroupPointsIso (k := k) (ι := ULift.{u} (Fin (Module.finrank k V)))
  (representationPointsEquiv A G L.val e l).trans (pointsCoactionEquiv A ((Module.finBasis k V).reindex Equiv.ulift.symm))

theorem coordinateComoduleUnion : Specs.RationalRepresentations.CoordinateComoduleUnion.{u} := by
  intro k V _ _ _ A ρ
  exact ⟨ρ.directed_finiteSubcomodules, ρ.iUnion_finiteSubcomodules⟩

section GeometricPoints

open Algebra.TensorProduct

/-- The closed points of a reduced finite-type algebra over an algebraically closed field
detect every nonzero element. -/
private theorem eq_zero_of_algHom_eq_zero {F B : Type u} [Field F] [IsAlgClosed F]
    [CommRing B] [Algebra F B] [Algebra.FiniteType F B] [IsReduced B]
    (x : B) (h : ∀ f : B →ₐ[F] F, f x = 0) : x = 0 := by
  let : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := F)
  have hx : x ∈ (⊥ : Ideal B).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    intro I hI
    let : I.IsMaximal := hI.2
    let : Field (B ⧸ I) := Ideal.Quotient.field I
    let : Module.Finite F (B ⧸ I) := finite_of_finite_type_of_isJacobsonRing F (B ⧸ I)
    let e : F ≃ₐ[F] B ⧸ I :=
      AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ I)) IsAlgClosed.algebraMap_bijective_of_isIntegral
    have he := h (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ F I))
    exact Ideal.Quotient.eq_zero_iff_mem.mp (e.symm.injective (by simpa using he))
  rwa [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced, Ideal.mem_bot] at hx

private theorem coordinateReduced {k : Type u} [Field k] (G : Specs.AffineAlgebraicGroup k)
    (A : HopfAlgebraCategory k)
    (e : ((affineHopfSpec k).obj (op A)).val ≅ G.val)
    (hG : Smooth G.val.X.hom) :
    Algebra.FiniteType k A ∧ IsReduced (AlgebraicClosure k ⊗[k] A) := by
  let D := ((affineHopfSpec k).obj (op A)).val
  let f := D.X.hom
  let e' := (Grp.forget (SchemeOver k)).mapIso e
  let w := (Over.forget (Spec (CommRingCat.of k))).mapIso e'
  have hw : w.hom ≫ G.val.X.hom = f := Over.w e'.hom
  have hft : LocallyOfFiniteType f := by
    rw [← hw]
    exact @locallyOfFiniteType_comp _ _ _ w.hom G.val.X.hom inferInstance G.property.2.1
  refine ⟨(hopfSpec_locallyOfFiniteType_iff k A).mp hft, ?_⟩
  have hs : Smooth f := by
    rw [← hw]
    exact @smooth_comp _ _ w.hom _ G.val.X.hom inferInstance hG
  have hr : GeometricallyReduced f := (@groupSmoothnessCriteria k _ D hft).1.mp hs
  let K := AlgebraicClosure k
  let g := fieldSpecMap k K
  have hp : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  let hred : AlgebraicGeometry.IsReduced (pullback f g) :=
    hr.geometrically_isReduced g _ _ hp
  let w' : pullback f g ≅ Spec (CommRingCat.of (K ⊗[k] A)) :=
    pullbackSymmetry f g ≪≫ pullbackSpecIso k K A
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (K ⊗[k] A))) :=
    isReduced_of_isOpenImmersion w'.inv
  exact (affine_isReduced_iff _).mp this

private theorem closure_point_separates {k : Type u} [Field k] (A : HopfAlgebraCategory k)
    [Algebra.FiniteType k A] [IsReduced (AlgebraicClosure k ⊗[k] A)]
    (a : A) (h : ∀ f : A →ₐ[k] AlgebraicClosure k, f a = 0) : a = 0 := by
  let K := AlgebraicClosure k
  have hz : (1 : K) ⊗ₜ[k] a = 0 := by
    apply eq_zero_of_algHom_eq_zero (F := K)
    intro f
    exact h ((f.restrictScalars k).comp includeRight)
  exact (Algebra.TensorProduct.includeRight_injective (B := A)
    (FaithfulSMul.algebraMap_injective k K)) (by simpa using hz)

private theorem tensorCoordinate_evaluation {V ι : Type u} [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) {C D : Type u} [AddCommGroup C] [Module k C]
    [AddCommGroup D] [Module k D] (g : C →ₗ[k] D) (t : V ⊗[k] C) (i : ι) :
    tensorCoordinate b i (g.lTensor V t) = g (tensorCoordinate b i t) := by
  induction t <;> simp_all

theorem geometricStability : Specs.RationalRepresentations.GeometricStability.{u} := by
  intro k V _ _ _ G A e hG ρ W
  classical
  constructor
  · intro h x
    obtain ⟨hft, hred⟩ := coordinateReduced G A e hG
    have hex (R : Type u) [AddCommGroup R] [Module k R] :
        Function.Exact (W.subtype.rTensor R) (W.mkQ.rTensor R) :=
      rTensor_exact R (LinearMap.exact_subtype_mkQ W) W.mkQ_surjective
    rw [← (hex A).linearMap_ker_eq, LinearMap.mem_ker]
    let t := W.mkQ.rTensor A (ρ.coaction x)
    let b := Module.Basis.ofVectorSpace k (V ⧸ W)
    have ht (g : A →ₐ[k] AlgebraicClosure k) : g.toLinearMap.lTensor (V ⧸ W) t = 0 := by
      have h' := DFunLike.congr_fun (evaluate_natural A g W.mkQ) (ρ.coaction x)
      simp only [LinearMap.comp_apply] at h'
      change g.toLinearMap.lTensor (V ⧸ W) (W.mkQ.rTensor A (ρ.coaction x)) = 0
      rw [← h']
      change W.mkQ.rTensor (AlgebraicClosure k) (evaluate A ρ g x) = 0
      exact (hex (AlgebraicClosure k) _).mpr (h g x)
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i
    rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
    change tensorCoordinate b i t = 0
    apply closure_point_separates A
    intro g
    change g.toLinearMap (tensorCoordinate b i t) = 0
    rw [← tensorCoordinate_evaluation b g.toLinearMap, ht g, map_zero]
  · intro h g x
    exact (stableSubspaces A ρ W).mpr h (CommAlgCat.of k (AlgebraicClosure k)) g x

end GeometricPoints

section FieldExtensionPoints

open Algebra.TensorProduct

variable (K : Type u) [Field K] [Algebra k K]

private def restrictCoordinateEquiv (R : TestAlgebra K) :
    (scalarExtension A K →ₐ[K] R) ≃ (A →ₐ[k] (restrictTestAlgebra k K).obj R) :=
  letI : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' rfl
  (liftEquivRight k K A R).symm

private theorem restrictCoordinatePoint_mul (R : TestAlgebra K)
    (f g : WithConv (scalarExtension A K →ₐ[K] R)) :
    toConv (restrictCoordinatePoint A K R (f * g).ofConv) =
      toConv (restrictCoordinatePoint A K R f.ofConv) *
        toConv (restrictCoordinatePoint A K R g.ofConv) := by
  apply WithConv.ofConv_injective
  ext a
  change (f * g) ((1 : K) ⊗ₜ[k] a) =
    (toConv (restrictCoordinatePoint A K R f.ofConv) *
      toConv (restrictCoordinatePoint A K R g.ofConv)) a
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul, Bialgebra.comul_one]
  generalize comul (R := k) a = t
  induction t with
  | tmul x y => rfl
  | add t s ht hs => simp [TensorProduct.tmul_add, ht, hs]

private def restrictCoordinatePointMulEquiv (R : TestAlgebra K) :
    (convolutionPoints (scalarExtension A K)).obj R ≃*
      (convolutionPoints A).obj ((restrictTestAlgebra k K).obj R) where
  toEquiv := (WithConv.equiv _).trans ((restrictCoordinateEquiv A K R).trans (WithConv.equiv _).symm)
  map_mul' := restrictCoordinatePoint_mul A K R

private def scalarExtensionPointIso :
    convolutionPoints (scalarExtension A K) ≅ restrictTestAlgebra k K ⋙ convolutionPoints A :=
  NatIso.ofComponents (fun R ↦ (restrictCoordinatePointMulEquiv A K R).toGrpIso) (by
    intro R S a
    apply GrpCat.ext
    intro f
    rfl)

private def groupBaseChangePointIso (G : Specs.GroupScheme k) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj G) ≅
      restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj G :=
  NatIso.ofComponents (fun R ↦ (baseChangePointGroupEquiv K G R).toGrpIso) (by
    intro R S a
    apply GrpCat.ext
    intro p
    exact (baseChangePointsNaturality k K G.X a p))

theorem fieldExtensionPoints : Specs.RationalRepresentations.FieldExtensionPoints.{u} := by
  intro k K _ _ _ A G s
  let e := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso s
  let c := groupBaseChangePointIso K G.val
  let d := scalarExtensionPointIso A K ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra k K) e ≪≫ c.symm
  have hd (R : TestAlgebra K) (g : WithConv (scalarExtension A K →ₐ[K] R)) :
      (baseChangePoint k K G.val.X R (d.hom.app R g)).left =
        Spec.map (CommRingCat.ofHom (restrictCoordinatePoint A K R g.ofConv).toRingHom) ≫
          s.hom.hom.hom.left := by
    change ((c.hom.app R) ((c.inv.app R)
      ((e.hom.app ((restrictTestAlgebra k K).obj R))
        (toConv (restrictCoordinatePoint A K R g.ofConv)))) :
          Points G.val.X ((restrictTestAlgebra k K).obj R)).left = _
    rw [← GrpCat.comp_apply, c.inv_hom_id_app]
    rfl
  refine ⟨d, hd, ?_⟩
  intro L f R g
  let p : Points ((baseChange k K).obj G.val.X) R := d.hom.app R g
  have h := baseChangePointsSchemeNaturality k K (X := G.val.X) (Y := L.X) f.hom.hom R p
  change (baseChangePoint k K L.X R
    (p ≫ (baseChange k K).map f.hom.hom)).left = _
  rw [h]
  change (baseChangePoint k K G.val.X R p).left ≫ f.hom.hom.left = _
  rw [hd]
  exact Category.assoc _ _ _

end FieldExtensionPoints

end
end RationalRepresentations
end LinearAlgebraicGroups
