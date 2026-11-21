import Mathlib.Algebra.Lie.BaseChange
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Independent interfaces for LA-J02-Descent, source lines 4583–4691, especially
4619–4650. Semilinear descent and classification have no characteristic or
dimension restriction on the Lie algebra. The final splitting theorem retains
characteristic zero and finite dimension. Canonical structures and theorem
types below are independent of the candidate implementation.
-/

universe u v w w'

open scoped TensorProduct

namespace LieAlgebrasAndRepresentations.GaloisDescent

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
variable (V : Type w) [AddCommGroup V] [Module L V]

/-- An additive Galois action, semilinear with respect to the given field action. -/
structure SemilinearAction where
  act : Gal(L/K) → (V ≃+ V)
  one_act : ∀ x, act 1 x = x
  mul_act : ∀ g h x, act (g * h) x = act g (act h x)
  map_smul : ∀ (g : Gal(L/K)) (a : L) (x : V),
    act g (a • x) = g a • act g x

namespace SemilinearAction

variable {K L V}
variable [Module K V] [IsScalarTower K L V]

/-- Fixed vectors, as a vector space over the original field. -/
def fixed (ρ : SemilinearAction K L V) : Submodule K V where
  carrier := {x | ∀ g, ρ.act g x = x}
  zero_mem' := by intro g; exact map_zero _
  add_mem' := by
    intro x y hx hy g
    rw [map_add, hx g, hy g]
  smul_mem' := by
    intro a x hx g
    rw [← IsScalarTower.algebraMap_smul L a x, ρ.map_smul, AlgEquiv.commutes, hx g]

/-- The canonical scalar-extension map, `a ⊗ x ↦ a • x`. -/
noncomputable def descentMap (ρ : SemilinearAction K L V) :
    L ⊗[K] ρ.fixed →ₗ[L] V :=
  TensorProduct.AlgebraTensorModule.lift <|
    { toFun := fun a =>
        { toFun := fun x => a • (x : V)
          map_add' := by intros; exact smul_add _ _ _
          map_smul' := by intros; exact smul_comm _ _ _ }
      map_add' := by intros; ext; exact add_smul _ _ _
      map_smul' := by intros; ext; exact mul_smul _ _ _ }

end SemilinearAction

section Lie
variable (W : Type w) [LieRing W] [LieAlgebra L W]

/-- Restrict scalars along `K → L` on the same underlying bracket and module. -/
@[instance_reducible]
def restrictLieAlgebra [Module K W] [IsScalarTower K L W] : LieAlgebra K W where
  lie_smul a x y := by
    rw [← IsScalarTower.algebraMap_smul L a y, lie_smul,
      IsScalarTower.algebraMap_smul]

/-- A Galois descent datum on a Lie algebra. -/
structure LieDescentData extends SemilinearAction K L W where
  map_lie : ∀ g x y, act g ⁅x, y⁆ = ⁅act g x, act g y⁆

namespace LieDescentData
variable {K L W} [LieAlgebra K W] [IsScalarTower K L W]

/-- Fixed points inherit their bracket, including alternation in characteristic two. -/
def fixedLie (ρ : LieDescentData K L W) : LieSubalgebra K W :=
  { ρ.toSemilinearAction.fixed with
    lie_mem' := by
      intro x y hx hy g
      rw [ρ.map_lie, hx g, hy g] }

end LieDescentData
end Lie

section Cocycles
variable {K L} {W : Type w} [LieRing W] [LieAlgebra L W]

/-- Composition of Lie automorphisms, with the right factor applied first. -/
instance lieAutGroup : Group (W ≃ₗ⁅L⁆ W) where
  mul b c := c.trans b
  mul_assoc _ _ _ := by ext; rfl
  one_mul _ := by ext; rfl
  mul_one _ := by ext; rfl
  inv b := b.symm
  inv_mul_cancel b := by ext; exact b.symm_apply_apply _

@[simp] theorem lieAut_mul_apply (b c : W ≃ₗ⁅L⁆ W) (x : W) :
    (b * c) x = b (c x) := rfl
@[simp] theorem lieAut_inv_apply (b : W ≃ₗ⁅L⁆ W) (x : W) :
    b⁻¹ x = b.symm x := rfl

namespace LieDescentData

variable (τ : LieDescentData K L W)

/-- The Galois action on the coefficient group, by semilinear conjugation. -/
def coefficientAction (g : Gal(L/K)) (b : W ≃ₗ⁅L⁆ W) : W ≃ₗ⁅L⁆ W where
  toFun x := τ.act g (b (τ.act g⁻¹ x))
  invFun x := τ.act g (b.symm (τ.act g⁻¹ x))
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    simp only [τ.map_smul, map_smul, RingHom.id_apply]
    rw [← AlgEquiv.mul_apply, mul_inv_cancel]
    rfl
  map_lie' := by intros; simp only [τ.map_lie, b.map_lie]
  left_inv x := by
    simp only [← τ.mul_act, inv_mul_cancel, mul_inv_cancel, τ.one_act, b.symm_apply_apply]
  right_inv x := by
    simp only [← τ.mul_act, inv_mul_cancel, mul_inv_cancel, τ.one_act, b.apply_symm_apply]

/-- Nonabelian 1-cocycles for the actual coefficient Galois action. -/
structure Cocycle where
  val : Gal(L/K) → (W ≃ₗ⁅L⁆ W)
  law : ∀ g h, val (g * h) = val g * τ.coefficientAction g (val h)

/-- The coboundary convention for changing a trivialization by `b`. -/
def Cohomologous (c d : τ.Cocycle) : Prop :=
  ∃ b : W ≃ₗ⁅L⁆ W, ∀ g,
    d.val g = b * c.val g * (τ.coefficientAction g b)⁻¹

/-- Nonabelian first Galois cohomology is a set of cocycles modulo coboundaries. -/
def H1 := Quot τ.Cohomologous

/-- Equivalence of descent data by an extension-field Lie automorphism. -/
def Equivalent (ρ σ : LieDescentData K L W) : Prop :=
  ∃ b : W ≃ₗ⁅L⁆ W, ∀ g x, σ.act g x = b (ρ.act g (b.symm x))

end LieDescentData
end Cocycles

section CoefficientAction
variable {K L} (A : Type w) [LieRing A] [LieAlgebra K A]

/-- The canonical action on a scalar extension changes only the first tensor factor. -/
def scalarAction : LieDescentData K L (L ⊗[K] A) where
  act g := (TensorProduct.congr g.toLinearEquiv (LinearEquiv.refl K A)).toAddEquiv
  one_act x := by
    induction x using TensorProduct.inductionOn with
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  mul_act g h x := by
    induction x using TensorProduct.inductionOn with
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  map_smul g a x := by
    induction x using TensorProduct.inductionOn with
    | tmul b x =>
      change (g (a * b)) ⊗ₜ[K] x = g a • ((g b) ⊗ₜ[K] x)
      rw [map_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  map_lie g x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
        change (g (a * b)) ⊗ₜ[K] ⁅x, y⁆ = (g a * g b) ⊗ₜ[K] ⁅x, y⁆
        rw [map_mul]
      | add y z hy hz => simp only [lie_add, map_add, hy, hz]
    | add x y hx hy => simp only [add_lie, map_add, hx, hy]

@[simp] theorem scalarAction_tmul (g : Gal(L/K)) (a : L) (x : A) :
    (scalarAction (K := K) (L := L) A).act g (a ⊗ₜ[K] x) = g a ⊗ₜ[K] x := rfl

end CoefficientAction

end LieAlgebrasAndRepresentations.GaloisDescent

namespace Specs.LieAlgebrasAndRepresentations.GaloisDescent
open _root_.LieAlgebrasAndRepresentations.GaloisDescent

/-- Full fixed-point descent, including the specified canonical map. -/
def fixed_point_descent_type : Prop :=
  ∀ {K : Type u} {L : Type v} {V : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [AddCommGroup V] [Module L V] [Module K V]
    [IsScalarTower K L V] (ρ : SemilinearAction K L V) [IsGalois K L],
    Function.Bijective ρ.descentMap

def invariant_span_type : Prop :=
  ∀ {K : Type u} {L : Type v} {V : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [AddCommGroup V] [Module L V] [Module K V]
    [IsScalarTower K L V] (ρ : SemilinearAction K L V),
    Submodule.span L (ρ.fixed : Set V) = ⊤

/-- Lie descent with the canonical scalar-extension map. The base-field
Lie algebra is constructed by restriction of scalars. -/
def fixed_lie_descent_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {W : Type w} [LieRing W] [LieAlgebra L W]
    [Module K W] [IsScalarTower K L W] (ρ : LieDescentData K L W) [IsGalois K L],
    letI := restrictLieAlgebra K L W
    ∃ e : (L ⊗[K] ρ.fixedLie) ≃ₗ⁅L⁆ W,
      ∀ a x, e (a ⊗ₜ[K] x) = a • (x : W)


/-- An arbitrary semilinear action is a coefficient action twisted by a cocycle;
conjugating the action changes its cocycle by the stated coboundary. -/
def cocycle_classification_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {W : Type w} [LieRing W] [LieAlgebra L W]
    (τ : LieDescentData K L W),
    ∃ e : LieDescentData K L W ≃ τ.Cocycle,
      (∀ ρ g x, (e ρ).val g x = ρ.act g (τ.act g⁻¹ x)) ∧
      ∀ ρ σ, LieDescentData.Equivalent ρ σ ↔ τ.Cohomologous (e ρ) (e σ)

/-- Equality in nonabelian `H¹` means precisely coboundary equivalence. -/
def h1_eq_iff_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {W : Type w} [LieRing W] [LieAlgebra L W]
    (τ : LieDescentData K L W) (c d : τ.Cocycle),
    (Quot.mk τ.Cohomologous c : τ.H1) = Quot.mk τ.Cohomologous d ↔ τ.Cohomologous c d

/-- The equivalence relation on actions agrees with isomorphism of fixed Lie algebras. -/
def equivalent_iff_fixed_isomorphic_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {W : Type w} [LieRing W]
    [LieAlgebra K W] [LieAlgebra L W] [IsScalarTower K L W] [IsGalois K L]
    (ρ σ : LieDescentData K L W),
    LieDescentData.Equivalent ρ σ ↔ Nonempty (ρ.fixedLie ≃ₗ⁅K⁆ σ.fixedLie)

/-- The original algebra is recovered by fixing the coefficient action. -/
def scalar_fixed_equiv_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (A : Type w) [LieRing A] [LieAlgebra K A] [IsGalois K L],
    ∃ e : A ≃ₗ⁅K⁆ (scalarAction (K := K) (L := L) A).fixedLie,
      ∀ x, (e x : L ⊗[K] A) = 1 ⊗ₜ[K] x

/-- Every abstract form split by `L` occurs among the fixed algebras on `A_L`. -/
def forms_recovered_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (A : Type w) (B : Type w')
    [LieRing A] [LieAlgebra K A] [LieRing B] [LieAlgebra K B] [IsGalois K L]
    (_e : (L ⊗[K] B) ≃ₗ⁅L⁆ (L ⊗[K] A)),
    ∃ ρ : LieDescentData K L (L ⊗[K] A), Nonempty (B ≃ₗ⁅K⁆ ρ.fixedLie)

/-- All cohomology classes occur, and equality of their representatives is
exactly base-field Lie isomorphism of the corresponding forms. This applies
in particular to `W = L ⊗[K] A` and `τ = scalarAction A`. -/
def forms_classified_by_h1_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {W : Type w} [LieRing W] [LieAlgebra L W]
    [LieAlgebra K W] [IsScalarTower K L W] [IsGalois K L]
    (τ : LieDescentData K L W),
    ∃ classify : LieDescentData K L W → τ.H1,
      Function.Surjective classify ∧ ∀ ρ σ,
        classify ρ = classify σ ↔ Nonempty (ρ.fixedLie ≃ₗ⁅K⁆ σ.fixedLie)

/-- Stronger finite-coefficient form: an isomorphism over any algebraic Galois
extension is defined over a finite Galois subextension. -/
def finite_galois_isomorphism_type : Prop :=
  ∀ {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    {A : Type w} {B : Type w'} [LieRing A] [LieAlgebra K A]
    [LieRing B] [LieAlgebra K B] [FiniteDimensional K A] [FiniteDimensional K B]
    (_e : (Ω ⊗[K] A) ≃ₗ⁅Ω⁆ (Ω ⊗[K] B)),
    ∃ F : FiniteGaloisIntermediateField K Ω,
      Nonempty ((F ⊗[K] A) ≃ₗ⁅F⁆ (F ⊗[K] B))

/-- The required characteristic-zero finite Galois splitting assertion. -/
def finite_galois_splitting_type : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K]
    {A : Type w} {B : Type w'} [LieRing A] [LieAlgebra K A]
    [LieRing B] [LieAlgebra K B] [FiniteDimensional K A] [FiniteDimensional K B]
    (_h : Nonempty (((AlgebraicClosure K) ⊗[K] A) ≃ₗ⁅AlgebraicClosure K⁆
      ((AlgebraicClosure K) ⊗[K] B))),
    ∃ F : FiniteGaloisIntermediateField K (AlgebraicClosure K),
      Nonempty ((F ⊗[K] A) ≃ₗ⁅F⁆ (F ⊗[K] B))

end Specs.LieAlgebrasAndRepresentations.GaloisDescent
