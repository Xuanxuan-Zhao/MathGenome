import Specs.LinearAlgebraicGroups.Representation.TensorAndDual
import LinearAlgebraicGroups.Affine.RationalRepresentations
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Coalgebra HopfAlgebra Opposite WithConv
open scoped TensorProduct

universe u
noncomputable section

namespace LinearAlgebraicGroups.RationalRepresentations

open private isCoactionMatrix_tensor from LinearAlgebraicGroups.Affine.RationalRepresentations
open private antipode_mul_matrix from LinearAlgebraicGroups.Affine.RationalRepresentations
open private mul_antipode_matrix from LinearAlgebraicGroups.Affine.RationalRepresentations

variable {k V W ι J : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
  (A : HopfAlgebraCategory k)

private theorem tensorCoefficients (b : Module.Basis ι k V) (c : Module.Basis J k W)
    (ρ : RightComodule k A V) (σ : RightComodule k A W) (i j : ι × J) :
    coefficients A (b.tensorProduct c) (tensorCoaction A b c ρ σ) i j =
      coefficients A b ρ i.1 j.1 * coefficients A c σ i.2 j.2 := by
  let M : Matrix (ι × J) (ι × J) A :=
    fun i j ↦ coefficients A b ρ i.1 j.1 * coefficients A c σ i.2 j.2
  have hM : IsCoactionMatrix A M :=
    isCoactionMatrix_tensor A (coefficients_isCoactionMatrix A b ρ)
      (coefficients_isCoactionMatrix A c σ)
  exact congrArg (fun N : Matrix (ι × J) (ι × J) A ↦ N i j)
    (coefficients_coactionOfMatrix A (b.tensorProduct c) M hM)

private theorem tensorCoaction_eq (b : Module.Basis ι k V) (c : Module.Basis J k W)
    (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    (tensorCoaction A b c ρ σ).coaction = tensorCoactionMap A ρ σ := by
  apply (b.tensorProduct c).ext
  rintro ⟨i, j⟩
  rw [coaction_apply_basis, Fintype.sum_prod_type]
  simp only [Module.Basis.tensorProduct_apply, tensorCoefficients, tensorCoactionMap,
    LinearMap.comp_apply, TensorProduct.map_tmul, coaction_apply_basis A b ρ,
    coaction_apply_basis A c σ, TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    LinearEquiv.coe_coe, TensorProduct.tensorTensorTensorComm_tmul, LinearMap.lTensor_tmul,
    LinearMap.mul'_apply]
  exact Finset.sum_comm

/-- The diagonal coaction on the tensor product of finite-dimensional representations. -/
def tensorProductCoaction [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    RightComodule k A (V ⊗[k] W) := by
  classical
  exact tensorCoaction A (Module.Basis.ofVectorSpace k V) (Module.Basis.ofVectorSpace k W) ρ σ

theorem tensorProductCoaction_coaction [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    (tensorProductCoaction A ρ σ).coaction = tensorCoactionMap A ρ σ := by
  unfold tensorProductCoaction
  classical
  exact tensorCoaction_eq A _ _ ρ σ

private theorem tensorCoaction_natural {V' W' : Type u}
    [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (ρ' : RightComodule k A V') (σ' : RightComodule k A W')
    (f : V →ₗ[k] V') (g : W →ₗ[k] W')
    (hf : IsEquivariant A ρ ρ' f) (hg : IsEquivariant A σ σ' g) :
    ((TensorProduct.map f g).rTensor A).comp (tensorCoactionMap A ρ σ) =
      (tensorCoactionMap A ρ' σ').comp (TensorProduct.map f g) := by
  apply TensorProduct.ext'
  intro v w
  have hv := DFunLike.congr_fun hf v
  have hw := DFunLike.congr_fun hg w
  change f.rTensor A (ρ.coaction v) = ρ'.coaction (f v) at hv
  change g.rTensor A (σ.coaction w) = σ'.coaction (g w) at hw
  simp only [tensorCoactionMap, LinearMap.comp_apply, TensorProduct.map_tmul, ← hv, ← hw]
  generalize ρ.coaction v = x
  generalize σ.coaction w = y
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, TensorProduct.add_tmul]
    exact congrArg₂ (· + ·) h₁ h₂
  | tmul v a =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, TensorProduct.tmul_add]
      exact congrArg₂ (· + ·) h₁ h₂
    | tmul w b => simp

theorem tensorProductOperation : Specs.RationalOperations.TensorProductOperation.{u} := by
  intro k V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ A ρ σ ρ' σ'
  refine ⟨tensorProductCoaction A ρ σ, tensorProductCoaction A ρ' σ',
    tensorProductCoaction_coaction A ρ σ, tensorProductCoaction_coaction A ρ' σ', ?_⟩
  intro f g hf hg
  rw [IsEquivariant, tensorProductCoaction_coaction, tensorProductCoaction_coaction]
  exact tensorCoaction_natural A ρ σ ρ' σ' f g hf hg

/-- The trivial representation on the base field. -/
def unitCoaction : RightComodule k A k where
  coaction := trivialLinearMap A
  coassoc x := by simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def]
  counit x := by simp [Bialgebra.counit_one]

theorem tensorUnitOperation : Specs.RationalOperations.TensorUnit.{u} := by
  intro k V _ _ _ _ A ρ
  let ε := unitCoaction A
  refine ⟨ε, tensorProductCoaction A ε ρ, tensorProductCoaction A ρ ε,
    rfl, tensorProductCoaction_coaction A ε ρ, tensorProductCoaction_coaction A ρ ε, ?_, ?_⟩
  · rw [IsEquivariant, tensorProductCoaction_coaction]
    apply TensorProduct.ext'
    intro a v
    simp only [tensorCoactionMap, LinearMap.comp_apply, TensorProduct.map_tmul, ε, unitCoaction,
      trivialLinearMap_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul, map_smul]
    induction ρ.coaction v using TensorProduct.inductionOn with
    | add x y hx hy => simp [TensorProduct.tmul_add, smul_add, hx, hy]
    | tmul w b => simp [TensorProduct.smul_tmul']
  · rw [IsEquivariant, tensorProductCoaction_coaction]
    apply TensorProduct.ext'
    intro v a
    simp only [tensorCoactionMap, LinearMap.comp_apply, TensorProduct.map_tmul, ε, unitCoaction,
      trivialLinearMap_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_smul]
    induction ρ.coaction v using TensorProduct.inductionOn with
    | add x y hx hy => simp [TensorProduct.add_tmul, smul_add, hx, hy]
    | tmul w b => simp [TensorProduct.smul_tmul']

private theorem dualCoefficients (b : Module.Basis ι k V) (ρ : RightComodule k A V) (i j : ι) :
    coefficients A b.dualBasis (dualCoaction A b ρ) i j =
      antipode k (coefficients A b ρ j i) := by
  simp only [dualCoaction, coefficients_coactionOfMatrix]
  rfl

private theorem coevaluation_one_in_basis [FiniteDimensional k V] (b : Module.Basis ι k V) :
    coevaluation k V 1 = ∑ i, b i ⊗ₜ[k] b.dualBasis i := by
  classical
  let e := (TensorProduct.comm k V (Module.Dual k V)).trans (dualTensorHomEquiv k V V)
  have h {I : Type u} [Fintype I] [DecidableEq I] (c : Module.Basis I k V) :
      e (∑ i, c i ⊗ₜ[k] c.dualBasis i) = LinearMap.id := by
    ext x
    simp [e, Module.Basis.coe_dualBasis, Module.Basis.coord_apply]
  rw [coevaluation_apply_one]
  apply e.injective
  rw [h b]
  simpa only [← Module.Basis.coe_dualBasis] using h (Module.Basis.ofVectorSpace k V)

theorem dualityOperation : Specs.RationalOperations.Duality.{u} := by
  intro k V ι _ _ _ _ _ _ A b ρ
  let σ := dualCoaction A b ρ
  let ε := unitCoaction A
  let l := tensorCoaction A b.dualBasis b σ ρ
  let r := tensorCoaction A b b.dualBasis ρ σ
  let M := coefficients A b ρ
  have hM := coefficients_isCoactionMatrix A b ρ
  refine ⟨σ, ε, l, r, dualCoefficients A b ρ, ?_, rfl,
    tensorCoaction_eq A b.dualBasis b σ ρ, tensorCoaction_eq A b b.dualBasis ρ σ, ?_, ?_⟩
  · intro R g
    let m : Matrix.GeneralLinearGroup ι R := (matrixPointHom A M hM).app R (toConv g)
    refine ⟨m, rfl, ?_⟩
    ext i j
    change g (coefficients A b.dualBasis σ i j) = g (antipode k (coefficients A b ρ j i))
    rw [dualCoefficients]
  · unfold IsEquivariant
    apply (b.dualBasis.tensorProduct b).ext
    rintro ⟨i, j⟩
    simp only [LinearMap.comp_apply]
    rw [coaction_apply_basis A _ l, Fintype.sum_prod_type]
    simp only [Module.Basis.tensorProduct_apply, map_sum, LinearMap.rTensor_tmul, contractLeft_apply,
      tensorCoefficients, l, σ, dualCoefficients, ε, unitCoaction, trivialLinearMap_apply,
      Module.Basis.coe_dualBasis, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
      TensorProduct.ite_tmul]
    have h := congrArg (fun N : Matrix ι ι A ↦ N i j) (antipode_mul_matrix A M hM)
    change (∑ m, antipode k (M i m) * M m j) = (1 : Matrix ι ι A) i j at h
    simp [← TensorProduct.tmul_sum, M, h, Matrix.one_apply, eq_comm]
    by_cases hij : i = j <;> simp [hij]
  · unfold IsEquivariant
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, ε, unitCoaction, trivialLinearMap_apply,
      LinearMap.rTensor_tmul, coevaluation_one_in_basis b, map_sum, TensorProduct.sum_tmul]
    simp only [← Module.Basis.tensorProduct_apply, coaction_apply_basis A _ r,
      tensorCoefficients, r, σ, dualCoefficients]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    simp_rw [← TensorProduct.tmul_sum]
    have h (p q : ι) : (∑ i, M p i * antipode k (M i q)) = (1 : Matrix ι ι A) p q :=
      congrArg (fun N : Matrix ι ι A ↦ N p q) (mul_antipode_matrix A M hM)
    simp only [Module.Basis.tensorProduct_apply]
    change _ = ∑ p, ∑ q, (b p ⊗ₜ[k] b.dualBasis q) ⊗ₜ[k]
      (∑ i, M p i * antipode k (M i q))
    simp [h, Matrix.one_apply, TensorProduct.tmul_ite]

section Restriction

variable {A B : HopfAlgebraCategory k}

private theorem map_coactionMatrix (a : A ⟶ B) {M : Matrix ι ι A}
    (hM : IsCoactionMatrix A M) : IsCoactionMatrix B (a.hom.toAlgHom.mapMatrix M) := by
  constructor
  · intro i j
    change comul (R := k) (a.hom (M i j)) = ∑ l, a.hom (M i l) ⊗ₜ[k] a.hom (M l j)
    rw [← CoalgHomClass.map_comp_comul_apply a.hom, hM.comul]
    simp
  · intro i j
    change counit (R := k) (a.hom (M i j)) = _
    rw [CoalgHomClass.counit_comp_apply a.hom, hM.counit]

/-- Restriction of the group action is corestriction by the pullback of coordinates. -/
def restrictCoaction [FiniteDimensional k V] (a : A ⟶ B) (ρ : RightComodule k A V) :
    RightComodule k B V := by
  classical
  let b := Module.Basis.ofVectorSpace k V
  exact coactionOfMatrix B b _ (map_coactionMatrix a (coefficients_isCoactionMatrix A b ρ))

theorem restrictCoaction_coaction [FiniteDimensional k V] (a : A ⟶ B) (ρ : RightComodule k A V) :
    (restrictCoaction a ρ).coaction = (a.hom.toAlgHom.toLinearMap.lTensor V).comp ρ.coaction := by
  classical
  let b := Module.Basis.ofVectorSpace k V
  have h : coefficients B b (restrictCoaction a ρ) = a.hom.toAlgHom.mapMatrix (coefficients A b ρ) :=
    coefficients_coactionOfMatrix B b _ (map_coactionMatrix a (coefficients_isCoactionMatrix A b ρ))
  apply b.ext
  intro j
  rw [LinearMap.comp_apply, coaction_apply_basis B b, h, coaction_apply_basis A b ρ]
  simp

theorem restrictionOperation : Specs.RationalOperations.Restriction.{u} := by
  intro k V _ _ _ _ A B a ρ
  exact ⟨restrictCoaction a ρ, restrictCoaction_coaction a ρ⟩

open private pointMatrix_evaluation from LinearAlgebraicGroups.Affine.RationalRepresentations

theorem schemeRestrictionOperation : Specs.RationalOperations.SchemeRestriction.{u} := by
  intro k V ι _ _ _ _ _ A B G H s t f L b l
  let := affineHopfSpecEquivalence k
  obtain ⟨a', ha'⟩ := (affineHopfSpec k).map_surjective (t.hom ≫ f ≫ s.inv)
  let a : A ⟶ B := a'.unop
  have ha : t.hom ≫ f = (affineHopfSpec k).map a.op ≫ s.hom := by
    change _ = (affineHopfSpec k).map a' ≫ s.hom
    rw [ha']
    simp
  obtain ⟨η, hη, hηnat⟩ := hopfSpecPoints k
  let e := η A ≪≫ (groupPointsFunctor k).mapIso ((affineGroupInclusion k).mapIso s)
  let d := η B ≪≫ (groupPointsFunctor k).mapIso ((affineGroupInclusion k).mapIso t)
  obtain ⟨E, hE⟩ := representationCoactionComparison A b G L e l
  obtain ⟨F, hF⟩ := representationCoactionComparison B b H L d l
  refine ⟨a, E, F, e, d, ha, ?_, ?_, hE, hF, ?_⟩
  · intro R g
    change ((η A).hom.app R g : Points _ R).left ≫ s.hom.hom.hom.hom.left = _
    rw [hη]
    rfl
  · intro R g
    change ((η B).hom.app R g : Points _ R).left ≫ t.hom.hom.hom.hom.left = _
    rw [hη]
    rfl
  · have haOver := congrArg (fun m ↦ (Grp.forget (SchemeOver k)).map
      ((affineGroupInclusion k).map m)) ha
    simp only [Functor.map_comp] at haOver
    change t.hom.hom.hom.hom ≫ f.hom.hom.hom =
      ((hopfSpec (CommRingCat.of k)).map a.op).hom.hom ≫ s.hom.hom.hom.hom at haOver
    have hpt (R : TestAlgebra k) (g : WithConv (B →ₐ[k] R)) :
        ((groupPointsFunctor k).map f.hom).app R (d.hom.app R g) =
          e.hom.app R (toConv (g.ofConv.comp a.hom.toAlgHom)) := by
      change (((η B).hom.app R g : Points _ R) ≫ t.hom.hom.hom.hom) ≫ f.hom.hom.hom =
        ((η A).hom.app R (toConv (g.ofConv.comp a.hom.toAlgHom)) : Points _ R) ≫
          s.hom.hom.hom.hom
      rw [hηnat a R g]
      change _ = (((η B).hom.app R g : Points _ R) ≫
        ((hopfSpec (CommRingCat.of k)).map a.op).hom.hom) ≫ s.hom.hom.hom.hom
      let p : Points ((hopfSpec (CommRingCat.of k)).obj (op B)).X R := (η B).hom.app R g
      change (p ≫ t.hom.hom.hom.hom) ≫ f.hom.hom.hom =
        (p ≫ ((hopfSpec (CommRingCat.of k)).map a.op).hom.hom) ≫ s.hom.hom.hom.hom
      exact (Category.assoc p _ _).trans
        ((congrArg (p ≫ ·) haOver).trans (Category.assoc p _ _).symm)
    intro ψ
    let R := CommAlgCat.of k B
    let α := e.hom ≫ (groupPointsFunctor k).map ψ ≫ l.hom
    have hψ : universalMatrix B H L d l (f.hom ≫ ψ) =
        a.hom.toAlgHom.mapMatrix (universalMatrix A G L e l ψ) := by
      change (l.hom.app R (((groupPointsFunctor k).map ψ).app R
        (((groupPointsFunctor k).map f.hom).app R
          (d.hom.app R (toConv (AlgHom.id k B)))))).val = _
      rw [hpt]
      exact pointMatrix_evaluation A α R (toConv a.hom.toAlgHom)
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, coaction_apply_basis B b, hF, hψ, ← hE,
      coaction_apply_basis A b]
    simp

end Restriction

theorem invariantVectorsOperation : Specs.RationalOperations.InvariantVectors.{u} := by
  intro k V _ _ _ A ρ v
  refine ⟨?_, invariantKernel A ρ v⟩
  simp [invariants, sub_eq_zero]

end LinearAlgebraicGroups.RationalRepresentations
