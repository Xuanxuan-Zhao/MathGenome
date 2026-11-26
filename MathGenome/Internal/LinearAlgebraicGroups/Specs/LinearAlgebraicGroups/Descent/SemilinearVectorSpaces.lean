import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! Semilinear descent along a finite Galois field extension (F01). -/

open scoped TensorProduct

namespace LinearAlgebraicGroups.Descent

universe u v w x y z

/-- An additive action of the Galois group, with each operator semilinear
relative to its action on the extension field. -/
structure SemilinearAction (k : Type u) (K : Type v) (V : Type w)
    [Field k] [Field K] [Algebra k K] [AddCommGroup V] [Module K V] where
  act : Gal(K/k) → V ≃+ V
  one_act : ∀ a, act 1 a = a
  mul_act : ∀ g h a, act (g * h) a = act g (act h a)
  map_smul : ∀ (g : Gal(K/k)) (r : K) (a : V), act g (r • a) = g r • act g a

namespace SemilinearAction

variable {k : Type u} {K : Type v} {V : Type w} {W : Type x}
variable [Field k] [Field K] [Algebra k K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- An individual action operator as a semilinear map. -/
def operator (ρ : SemilinearAction k K V) (g : Gal(K/k)) :
    V →ₛₗ[(g : K →+* K)] V :=
  { (ρ.act g).toAddMonoidHom with map_smul' := ρ.map_smul g }

private noncomputable def tensorOperator (ρ : SemilinearAction k K V)
    (τ : SemilinearAction k K W) (g : Gal(K/k)) :
    (V ⊗[K] W) →ₛₗ[(g : K →+* K)] (V ⊗[K] W) :=
  TensorProduct.map (ρ.operator g) (τ.operator g)

private theorem tensorOperator_tmul (ρ : SemilinearAction k K V)
    (τ : SemilinearAction k K W) (g : Gal(K/k)) (a : V) (b : W) :
    tensorOperator ρ τ g (a ⊗ₜ[K] b) = ρ.act g a ⊗ₜ[K] τ.act g b :=
  TensorProduct.map_tmul _ _ _ _

/-- The diagonal action on the tensor product over the extension field. -/
noncomputable def tensor (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W) :
    SemilinearAction k K (V ⊗[K] W) := by
  have hone (a : V ⊗[K] W) : tensorOperator ρ τ 1 a = a := by
    induction a using TensorProduct.inductionOn with
    | tmul a b => rw [tensorOperator_tmul, ρ.one_act, τ.one_act]
    | add a b ha hb => rw [map_add, ha, hb]
  have hmul (g h : Gal(K/k)) (a : V ⊗[K] W) :
      tensorOperator ρ τ (g * h) a = tensorOperator ρ τ g (tensorOperator ρ τ h a) := by
    induction a using TensorProduct.inductionOn with
    | tmul a b => simp only [tensorOperator_tmul, ρ.mul_act, τ.mul_act]
    | add a b ha hb => simp only [map_add, ha, hb]
  exact
    { act := fun g =>
        { (tensorOperator ρ τ g).toAddMonoidHom with
          invFun := tensorOperator ρ τ g⁻¹
          left_inv := fun a => by
            change tensorOperator ρ τ g⁻¹ (tensorOperator ρ τ g a) = a
            rw [← hmul, inv_mul_cancel, hone]
          right_inv := fun a => by
            change tensorOperator ρ τ g (tensorOperator ρ τ g⁻¹ a) = a
            rw [← hmul, mul_inv_cancel, hone] }
      one_act := hone
      mul_act := hmul
      map_smul := fun g r a => (tensorOperator ρ τ g).map_smulₛₗ r a }

@[simp] theorem tensor_act_tmul (ρ : SemilinearAction k K V)
    (τ : SemilinearAction k K W) (g : Gal(K/k)) (a : V) (b : W) :
    (ρ.tensor τ).act g (a ⊗ₜ[K] b) = ρ.act g a ⊗ₜ[K] τ.act g b :=
  tensorOperator_tmul ρ τ g a b

/-- Galois acts on the tensor unit by its given action on the field. -/
def unit : SemilinearAction k K K where
  act g := g.toAddEquiv
  one_act _ := rfl
  mul_act _ _ _ := rfl
  map_smul g r a := map_mul g r a

/-- On scalar extension the Galois action changes only the field factor. -/
noncomputable def scalarExtension (U : Type x) [AddCommGroup U] [Module k U] :
    SemilinearAction k K (K ⊗[k] U) where
  act g := (TensorProduct.congr g.toLinearEquiv (LinearEquiv.refl k U)).toAddEquiv
  one_act a := by
    induction a using TensorProduct.inductionOn with
    | tmul r x => rfl
    | add a b ha hb => rw [map_add, ha, hb]
  mul_act g h a := by
    induction a using TensorProduct.inductionOn with
    | tmul r x => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  map_smul g r a := by
    induction a using TensorProduct.inductionOn with
    | tmul s x =>
      change (g (r * s)) ⊗ₜ[k] x = g r • ((g s) ⊗ₜ[k] x)
      rw [TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add a b ha hb => simp only [smul_add, map_add, ha, hb]

/-- Equivariance of an extension-field linear map. -/
def Equivariant (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W)
    (f : V →ₗ[K] W) : Prop :=
  ∀ g a, f (ρ.act g a) = τ.act g (f a)

variable [Module k V] [IsScalarTower k K V] [Module k W] [IsScalarTower k K W]

/-- The fixed vectors with the base-field structure induced by the scalar tower. -/
def fixed (ρ : SemilinearAction k K V) : Submodule k V where
  carrier := {a | ∀ g, ρ.act g a = a}
  zero_mem' g := map_zero _
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  smul_mem' r a ha g := by
    rw [← IsScalarTower.algebraMap_smul K r a, ρ.map_smul, AlgEquiv.commutes, ha g]

/-- The canonical map from the scalar extension of the fixed space. -/
noncomputable def descentMap (ρ : SemilinearAction k K V) :
    (K ⊗[k] ρ.fixed) →ₗ[K] V :=
  ρ.fixed.subtype.liftBaseChange K

/-- Restriction of an equivariant linear map to the fixed subspaces. -/
def restrict (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W)
    (f : V →ₗ[K] W) (hf : ρ.Equivariant τ f) : ρ.fixed →ₗ[k] τ.fixed :=
  (((f.restrictScalars k).comp ρ.fixed.subtype).codRestrict τ.fixed) fun a g => by
    change τ.act g (f a) = f a
    rw [← hf g, a.property g]

/-- The canonical map taking a tensor of fixed vectors to their pure tensor. -/
noncomputable def tensorComparison (ρ : SemilinearAction k K V)
    (τ : SemilinearAction k K W) : (ρ.fixed ⊗[k] τ.fixed) →ₗ[k] (ρ.tensor τ).fixed :=
  TensorProduct.lift
    { toFun := fun a =>
        (((TensorProduct.mk K V W a).restrictScalars k).comp τ.fixed.subtype).codRestrict
          (ρ.tensor τ).fixed fun b g => by
            change (ρ.tensor τ).act g ((a : V) ⊗ₜ[K] (b : W)) = _
            rw [tensor_act_tmul]
            exact congrArg₂ (TensorProduct.tmul K) (a.property g) (b.property g)
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        apply Subtype.ext
        exact TensorProduct.add_tmul _ _ _
      map_smul' := by
        intro r a
        apply LinearMap.ext
        intro b
        apply Subtype.ext
        exact TensorProduct.smul_tmul' _ _ _ }

/-- The base field maps into the fixed subspace of the tensor unit. -/
def unitComparison : k →ₗ[k] (unit (k := k) (K := K)).fixed :=
  (Algebra.linearMap k K).codRestrict _ fun a g => g.commutes a

/-- A base-field vector maps to the fixed vector given by tensoring with 1. -/
noncomputable def scalarExtensionComparison (U : Type x) [AddCommGroup U] [Module k U] :
    U →ₗ[k] (scalarExtension (k := k) (K := K) U).fixed :=
  (TensorProduct.mk k K U 1).codRestrict _ fun a g => by
    change g 1 ⊗ₜ[k] a = 1 ⊗ₜ[k] a
    rw [map_one]

end SemilinearAction
end LinearAlgebraicGroups.Descent

namespace Specs.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces

open _root_.LinearAlgebraicGroups.Descent
open SemilinearAction

universe u v w x y z

def mem_fixed_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : SemilinearAction k K V) (a : V),
    a ∈ ρ.fixed ↔ ∀ g : Gal(K/k), ρ.act g a = a

def descentMap_tmul_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : SemilinearAction k K V) (r : K) (a : ρ.fixed),
    ρ.descentMap (r ⊗ₜ[k] a) = r • (a : V)

def descent_bijective_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : SemilinearAction k K V) [FiniteDimensional k K] [IsGalois k K],
    Function.Bijective ρ.descentMap

def descent_restrictScalars_type : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {A : Type w} [AddCommGroup A] [Module K A] (ρ : SemilinearAction k K A),
    letI := Module.compHom A (algebraMap k K)
    letI := IsScalarTower.of_compHom k K A
    Function.Bijective ρ.descentMap

def descent_equivariant_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : SemilinearAction k K V),
    (scalarExtension ρ.fixed).Equivariant ρ ρ.descentMap

def scalarExtension_act_tmul_type : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (U : Type x) [AddCommGroup U] [Module k U] (g : Gal(K/k)) (r : K) (a : U),
    (scalarExtension (k := k) (K := K) U).act g (r ⊗ₜ[k] a) = g r ⊗ₜ[k] a

def scalarExtension_bijective_type : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (U : Type x) [AddCommGroup U] [Module k U],
    Function.Bijective (scalarExtensionComparison (k := k) (K := K) U)

def scalarExtension_equivariant_type : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {U : Type w} {T : Type x} [AddCommGroup U] [Module k U] [AddCommGroup T] [Module k T]
    (f : U →ₗ[k] T),
    (scalarExtension U).Equivariant (scalarExtension T) (f.baseChange K)

def scalarExtensionComparison_natural_type : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {U : Type w} {T : Type x} [AddCommGroup U] [Module k U] [AddCommGroup T] [Module k T]
    (f : U →ₗ[k] T)
    (hf : (scalarExtension (K := K) U).Equivariant (scalarExtension T) (f.baseChange K)),
    ((scalarExtension (K := K) U).restrict (scalarExtension T) (f.baseChange K) hf).comp
        (scalarExtensionComparison U) =
      (scalarExtensionComparison T).comp f

def hom_equivalence_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} {W : Type x}
    [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]
    (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W)
    [FiniteDimensional k K] [IsGalois k K],
    ∃ e : {f : V →ₗ[K] W // ρ.Equivariant τ f} ≃ (ρ.fixed →ₗ[k] τ.fixed),
      (∀ f, e f = ρ.restrict τ f.1 f.2) ∧
      ∀ f, (e.symm f).1.comp ρ.descentMap = τ.descentMap.comp (f.baseChange K)

def restrict_id_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : SemilinearAction k K V),
    ρ.restrict ρ LinearMap.id (fun _ _ => rfl) = LinearMap.id

def restrict_comp_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} {W : Type x}
    [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]
    (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W)
    {X : Type y} [AddCommGroup X] [Module K X] [Module k X] [IsScalarTower k K X]
    (υ : SemilinearAction k K X) (f : V →ₗ[K] W) (hf : ρ.Equivariant τ f)
    (g : W →ₗ[K] X) (hg : τ.Equivariant υ g),
    ρ.restrict υ (g.comp f)
        (fun s a => (congrArg g (hf s a)).trans (hg s (f a))) =
      (τ.restrict υ g hg).comp (ρ.restrict τ f hf)

def tensorComparison_tmul_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} {W : Type x}
    [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]
    (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W) (a : ρ.fixed) (b : τ.fixed),
    (ρ.tensorComparison τ (a ⊗ₜ[k] b) : V ⊗[K] W) = (a : V) ⊗ₜ[K] (b : W)

def tensor_bijective_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} {W : Type x}
    [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]
    (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W)
    [FiniteDimensional k K] [IsGalois k K],
    Function.Bijective (ρ.tensorComparison τ)

def tensor_equivariant_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} {W : Type x}
    [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W)
    {X : Type y} [AddCommGroup X] [Module K X] {Y : Type z} [AddCommGroup Y] [Module K Y]
    (υ : SemilinearAction k K X) (ω : SemilinearAction k K Y)
    (f : V →ₗ[K] X) (_hf : ρ.Equivariant υ f) (g : W →ₗ[K] Y) (_hg : τ.Equivariant ω g),
    (ρ.tensor τ).Equivariant (υ.tensor ω) (TensorProduct.map f g)

def tensor_natural_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} {W : Type x}
    [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]
    (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W)
    {X : Type y} [AddCommGroup X] [Module K X] [Module k X] [IsScalarTower k K X]
    {Y : Type z} [AddCommGroup Y] [Module K Y] [Module k Y] [IsScalarTower k K Y]
    (υ : SemilinearAction k K X) (ω : SemilinearAction k K Y)
    (f : V →ₗ[K] X) (hf : ρ.Equivariant υ f) (g : W →ₗ[K] Y) (hg : τ.Equivariant ω g)
    (hfg : (ρ.tensor τ).Equivariant (υ.tensor ω) (TensorProduct.map f g)),
    ((ρ.tensor τ).restrict (υ.tensor ω) (TensorProduct.map f g) hfg).comp
        (ρ.tensorComparison τ) =
      (υ.tensorComparison ω).comp (TensorProduct.map (ρ.restrict υ f hf) (τ.restrict ω g hg))

def unitComparison_apply_type : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] (a : k),
    (unitComparison (K := K) a : K) = algebraMap k K a

def unit_bijective_type : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K],
    Function.Bijective (unitComparison (k := k) (K := K))

def finiteDimensional_fixed_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : SemilinearAction k K V) [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional K V],
    FiniteDimensional k ρ.fixed ∧ Module.finrank k ρ.fixed = Module.finrank K V

def tensorComparison_assoc_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} {W : Type x}
    [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]
    (ρ : SemilinearAction k K V) (τ : SemilinearAction k K W)
    {X : Type y} [AddCommGroup X] [Module K X] [Module k X] [IsScalarTower k K X]
    (υ : SemilinearAction k K X) (a : (ρ.fixed ⊗[k] τ.fixed) ⊗[k] υ.fixed),
    TensorProduct.assoc K V W X
      (↑((ρ.tensor τ).tensorComparison υ (TensorProduct.map (ρ.tensorComparison τ)
        LinearMap.id a))) =
    (↑(ρ.tensorComparison (τ.tensor υ) (TensorProduct.map LinearMap.id
      (τ.tensorComparison υ) (TensorProduct.assoc k ρ.fixed τ.fixed υ.fixed a))) :
        V ⊗[K] (W ⊗[K] X))

def tensorComparison_lid_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : SemilinearAction k K V) (a : k ⊗[k] ρ.fixed),
    TensorProduct.lid K V
      (↑((unit (k := k) (K := K)).tensorComparison ρ
        (TensorProduct.map unitComparison LinearMap.id a))) =
    ((TensorProduct.lid k ρ.fixed) a : V)

def tensorComparison_rid_type : Prop :=
  ∀ {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : SemilinearAction k K V) (a : ρ.fixed ⊗[k] k),
    TensorProduct.rid K V
      (↑(ρ.tensorComparison (unit (k := k) (K := K))
        (TensorProduct.map LinearMap.id unitComparison a))) =
    ((TensorProduct.rid k ρ.fixed) a : V)

end Specs.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
