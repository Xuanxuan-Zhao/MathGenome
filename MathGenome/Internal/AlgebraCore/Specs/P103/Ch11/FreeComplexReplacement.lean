import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Complexes
import Mathlib.Algebra.Module.Projective
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.TotalComplexAssembly
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomologySequence
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FlatnessTests

/-! Nonnegative free replacements, paper.tex 3135–3168.
No finite generation, commutativity, or nonzero-ring hypothesis is imposed.
The opposite-ring specialization is the right-module statement. -/
namespace P103.Specs.Ch11.FreeComplexReplacement
open CategoryTheory P103.Specs.Ch10.Complexes
noncomputable section
universe u v
variable {R : Type u} [Ring R]

/-- The actual degreewise kernel, with differential restricted from the source. -/
def kernelComplex {Q D : ChainComplex (ModuleCat.{v} R) ℕ} (f : Q ⟶ D) :
    ChainComplex (ModuleCat.{v} R) ℕ where
  X n := ModuleCat.of R (LinearMap.ker (f.f n).hom)
  d i j := ModuleCat.ofHom
    (((Q.d i j).hom.comp (LinearMap.ker (f.f i).hom).subtype).codRestrict
      (LinearMap.ker (f.f j).hom) (by
        intro x
        change (f.f j).hom ((Q.d i j).hom x.val) = 0
        have h := congrArg ModuleCat.Hom.hom (f.comm i j)
        change (D.d i j).hom.comp (f.f i).hom =
          (f.f j).hom.comp (Q.d i j).hom at h
        rw [← LinearMap.comp_apply, ← h, LinearMap.comp_apply, x.property, map_zero]))
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (Q.d i j).hom x.val = 0
    rw [Q.shape i j h]
    rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (Q.d_comp_d i j k)) x.val

/-- Freeness and the two independently specified conclusions of the replacement. -/
def IsFreeReplacement {Q D : ChainComplex (ModuleCat.{v} R) ℕ} (f : Q ⟶ D) : Prop :=
  (∀ n, Module.Free R (Q.X n)) ∧
  (∀ n, Function.Surjective (f.f n).hom) ∧
  QuasiIsomorphism f ∧ Acyclic (kernelComplex f)

def exists_free_replacementType : Prop :=
  ∀ (R : Type u) [Ring R] (D : ChainComplex (ModuleCat.{max u v} R) ℕ),
    ∃ (Q : ChainComplex (ModuleCat.{max u v} R) ℕ) (f : Q ⟶ D),
      IsFreeReplacement f

def exists_right_free_replacementType : Prop :=
  ∀ (R : Type u) [Ring R] (D : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℕ),
    ∃ (Q : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℕ) (f : Q ⟶ D),
      IsFreeReplacement f

open P103.Specs.Ch10.TotalComplexAssembly

/-- A tensor bicomplex is specified on the shared balanced tensor groups.
The term equivalences and both elementary-tensor formulas fix the objects,
differentials, and orientation, without assuming any exactness conclusion. -/
structure TensorModel (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{v} R) ℤ) where
  complex : ChainBicomplex.{0,v} ℤ
  termEquiv : ∀ p q, (complex.X p).X q ≃ₗ[ℤ]
    P103.BalancedTensor.Tensor R (C.X p) (D.X q)
  horizontal : ∀ p p' q (x : C.X p) (y : D.X q),
    termEquiv p' q (((complex.d p p').f q).hom
      ((termEquiv p q).symm (P103.BalancedTensor.tmul R x y))) =
      P103.BalancedTensor.tmul R ((C.d p p').hom x) y
  vertical : ∀ p q q' (x : C.X p) (y : D.X q),
    termEquiv p q' (((complex.X p).d q q').hom
      ((termEquiv p q).symm (P103.BalancedTensor.tmul R x y))) =
      P103.BalancedTensor.tmul R x ((D.d q q').hom y)

/-- The induced tensor map, characterized on all elementary tensors. -/
def IsTensorMap {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{v} R) ℤ}
    (M : TensorModel C D) (N : TensorModel C' D')
    (f : C ⟶ C') (g : D ⟶ D') (φ : M.complex ⟶ N.complex) : Prop :=
  ∀ p q (x : C.X p) (y : D.X q),
    N.termEquiv p q (((φ.f p).f q).hom
      ((M.termEquiv p q).symm (P103.BalancedTensor.tmul R x y))) =
      P103.BalancedTensor.tmul R ((f.f p).hom x) ((g.f q).hom y)

/-- Assembly for any explicit componentwise short exact kernel model. -/
def total_quasiIsomorphism_of_exactType : Prop :=
  ∀ (R : Type u) [Ring R] (E K L : ChainBicomplex.{u,v} R)
    (i : E ⟶ K) (p : K ⟶ L),
    (∀ a b, Function.Injective ((i.f a).f b).hom ∧
      Function.Exact ((i.f a).f b).hom ((p.f a).f b).hom ∧
      Function.Surjective ((p.f a).f b).hom) →
    ∀ a b : ℤ, SupportedQuadrant E a b →
      (ColumnsAcyclic E ∨ RowsAcyclic E) →
      (∀ n, Function.Surjective
        ((HomologicalComplex₂.total.map p (ComplexShape.down ℤ)).f n).hom) ∧
      QuasiIsomorphism (HomologicalComplex₂.total.map p (ComplexShape.down ℤ))

/-- Tensor-total comparison for a replacement of the left-module complex D.
The models describe the actual balanced tensor bicomplexes extended by zero;
the total and its signs are the upstream canonical direct-sum construction. -/
def tensor_comparison_leftType : Prop :=
  ∀ (R : Type u) [Ring R]
    (C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℕ)
    (Q D : ChainComplex (ModuleCat.{max u v} R) ℕ) (f : Q ⟶ D),
    (∀ p, P103.Specs.Ch02.FlatnessTests.RightFlat.{u,max u v,v} R (C.X p)) →
    IsFreeReplacement f →
    ∃ (M : TensorModel (extendNonnegativeChain C) (extendNonnegativeChain Q))
      (N : TensorModel (extendNonnegativeChain C) (extendNonnegativeChain D))
      (φ : M.complex ⟶ N.complex),
      IsTensorMap M N (𝟙 _) (HomologicalComplex.extendMap f nonnegativeChainEmbedding) φ ∧
      (∀ n, Function.Surjective
        ((HomologicalComplex₂.total.map φ (ComplexShape.down ℤ)).f n).hom) ∧
      QuasiIsomorphism (HomologicalComplex₂.total.map φ (ComplexShape.down ℤ))

/-- Tensor-total comparison for a replacement of the right-module complex C. -/
def tensor_comparison_rightType : Prop :=
  ∀ (R : Type u) [Ring R]
    (Q C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{max u v} R) ℕ) (f : Q ⟶ C),
    (∀ q, P103.Specs.Ch02.FlatnessTests.Flat.{u,max u v,v} R (D.X q)) →
    IsFreeReplacement f →
    ∃ (M : TensorModel (extendNonnegativeChain Q) (extendNonnegativeChain D))
      (N : TensorModel (extendNonnegativeChain C) (extendNonnegativeChain D))
      (φ : M.complex ⟶ N.complex),
      IsTensorMap M N (HomologicalComplex.extendMap f nonnegativeChainEmbedding) (𝟙 _) φ ∧
      (∀ n, Function.Surjective
        ((HomologicalComplex₂.total.map φ (ComplexShape.down ℤ)).f n).hom) ∧
      QuasiIsomorphism (HomologicalComplex₂.total.map φ (ComplexShape.down ℤ))

end
end P103.Specs.Ch11.FreeComplexReplacement
