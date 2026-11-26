import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ComoduleFiniteness
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RelativeFrobenius
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.LinearAlgebra.Dual.Defs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Coalgebra TensorProduct WithConv
open scoped TensorProduct

universe u v w z

namespace LinearAlgebraicGroups.FiniteDistributions

noncomputable section

/-- The linear dual with convolution. For a finite coordinate coalgebra this is
the distribution algebra of the corresponding finite group scheme. -/
abbrev Dist (k : Type u) (C : Type v) [Field k] [AddCommGroup C] [Module k C] :=
  WithConv (Module.Dual k C)

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
variable {D : Type z} [AddCommGroup D] [Module k D] [Coalgebra k D]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- A left module structure on the given vector space, presented by its algebra action. -/
abbrev LeftAction (k : Type u) (C : Type v) (V : Type w)
    [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C] [AddCommGroup V] [Module k V] :=
  Dist k C →ₐ[k] Module.End k V

/-- A module over the distribution algebra whose restricted scalars are the given
vector space structure. -/
structure CompatibleModule (k : Type u) (C : Type v) (V : Type w)
    [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C] [AddCommGroup V] [Module k V] where
  module : Module (Dist k C) V
  tower : letI := module; IsScalarTower k (Dist k C) V

/-- Scalar multiplication with its module structure supplied explicitly. -/
def CompatibleModule.smul (M : CompatibleModule k C V) (a : Dist k C) (x : V) : V :=
  letI := M.module
  a • x

/-- Contraction of the right tensor factor with a functional. -/
def pair (f : Dist k C) : V ⊗[k] C →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp (f.ofConv.lTensor V)

omit [Coalgebra k C] in
@[simp] theorem pair_tmul (f : Dist k C) (x : V) (a : C) :
    pair f (x ⊗ₜ[k] a) = f.ofConv a • x := rfl

/-- The scalar action prescribed by a right coaction. -/
def PairsWith (ρ : RightComodule k C V) (μ : LeftAction k C V) : Prop :=
  ∀ (f : Dist k C) (x : V), μ f x = pair f (ρ.coaction x)

def IsComoduleMap {W : Type z} [AddCommGroup W] [Module k W]
    (ρ : RightComodule k C V) (σ : RightComodule k C W) (f : V →ₗ[k] W) : Prop :=
  ∀ x, f.rTensor C (ρ.coaction x) = σ.coaction (f x)

def IsModuleMap {W : Type z} [AddCommGroup W] [Module k W]
    (μ : LeftAction k C V) (ν : LeftAction k C W) (f : V →ₗ[k] W) : Prop :=
  ∀ a x, f (μ a x) = ν a (f x)

section FiniteCategories

variable (k C)

/-- Finite-dimensional right comodules with their underlying vector spaces. -/
structure FiniteRightComodule where
  space : ModuleCat.{w} k
  finite : Module.Finite k space
  comodule : RightComodule k C space

/-- Left distribution modules finite-dimensional over the base field. -/
structure FiniteLeftModule where
  space : ModuleCat.{w} k
  finite : Module.Finite k space
  action : CompatibleModule k C space

variable {k C}

instance : Category (FiniteRightComodule.{u,v,w} k C) where
  Hom X Y := { f : X.space →ₗ[k] Y.space // IsComoduleMap X.comodule Y.comodule f }
  id X := ⟨LinearMap.id, by intro x; simp⟩
  comp f g := ⟨g.1.comp f.1, by
    intro x
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, f.2 x, g.2 (f.1 x)]
    rfl⟩

instance : Category (FiniteLeftModule.{u,v,w} k C) where
  Hom X Y := { f : X.space →ₗ[k] Y.space //
    ∀ a x, f (X.action.smul a x) = Y.action.smul a (f x) }
  id X := ⟨LinearMap.id, fun _ _ => rfl⟩
  comp f g := ⟨g.1.comp f.1, fun a x => by
    change g.1 (f.1 _) = _
    rw [f.2 a x, g.2 a (f.1 x)]
    rfl⟩

/-- Forget the coaction. -/
def forgetFiniteRightComodule : FiniteRightComodule.{u,v,w} k C ⥤ ModuleCat.{w} k where
  obj X := X.space
  map f := ModuleCat.ofHom f.1

/-- Forget the distribution module structure. -/
def forgetFiniteLeftModule : FiniteLeftModule.{u,v,w} k C ⥤ ModuleCat.{w} k where
  obj X := X.space
  map f := ModuleCat.ofHom f.1

end FiniteCategories

/-- Precomposition by the coordinate map is covariant on distribution algebras. -/
abbrev distributionMap (g : C →ₗc[k] D) : Dist k D →ₐ[k] Dist k C :=
  g.convPrecomp

/-- The Frobenius twist at the scalar Frobenius iterated `r` times. -/
abbrev twistCoordinates (k : Type u) [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k) : HopfAlgebraCategory k :=
  Specs.RelativeFrobenius.extendAlong (iterateFrobenius k p r) A

/-- Pullback formula for the iterated relative Frobenius. -/
def FrobeniusFormula (k : Type u) [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k) (f : twistCoordinates k p r A ⟶ A) : Prop :=
  ∀ (c : k) (a : A),
    f.hom (Specs.RelativeFrobenius.scalarTensor (iterateFrobenius k p r) A c a) =
      c • a ^ (p ^ r)

end

end LinearAlgebraicGroups.FiniteDistributions

namespace LinearAlgebraicGroups.Specs.FiniteDistributions
open LinearAlgebraicGroups.FiniteDistributions

noncomputable section

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
variable {D : Type z} [AddCommGroup D] [Module k D] [Coalgebra k D]
variable {V : Type w} [AddCommGroup V] [Module k V]

def DistributionMultiplication : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k) [Module.Finite k A],
    Module.Finite k (Dist k A) ∧
    (∀ (f g : Dist k A) (a : A), (f * g).ofConv a =
      LinearMap.mul' k k (TensorProduct.map f.ofConv g.ofConv (Coalgebra.comul a))) ∧
    (∀ a : A, (1 : Dist k A).ofConv a = Coalgebra.counit a)

/-- The same vector space is used on the two sides. Thus this also
restricts to any finite-dimensional vector space. -/
def ComoduleModuleComparison : Prop :=
  ∀ (k : Type u) [Field k] (C : Type v) [AddCommGroup C] [Module k C]
    [Coalgebra k C] [Module.Finite k C] (V : Type w) [AddCommGroup V] [Module k V],
    ∃ e : RightComodule k C V ≃ LeftAction k C V,
      ∀ ρ μ, e ρ = μ ↔ PairsWith ρ μ

def ModuleStructureComparison : Prop :=
  ∀ (k : Type u) [Field k] (C : Type v) [AddCommGroup C] [Module k C] [Coalgebra k C]
    (V : Type w) [AddCommGroup V] [Module k V],
    ∃ e : LeftAction k C V ≃ CompatibleModule k C V,
      ∀ μ a x, letI := (e μ).module; a • x = μ a x

def MorphismComparison : Prop :=
  ∀ {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    [Module.Finite k C] {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type z} [AddCommGroup W] [Module k W]
    (ρ : RightComodule k C V) (σ : RightComodule k C W)
    (μ : LeftAction k C V) (ν : LeftAction k C W),
    PairsWith ρ μ → PairsWith σ ν →
    ∀ f : V →ₗ[k] W, IsComoduleMap ρ σ f ↔ IsModuleMap μ ν f

def FiniteCategoriesComparison : Prop :=
  ∀ (k : Type u) [Field k] (C : Type v) [AddCommGroup C] [Module k C]
    [Coalgebra k C] [Module.Finite k C],
    ∃ F : FiniteRightComodule.{u,v,w} k C ⥤ FiniteLeftModule.{u,v,w} k C,
      F.IsEquivalence ∧ F ⋙ forgetFiniteLeftModule = forgetFiniteRightComodule

def SubobjectComparison : Prop :=
  ∀ {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    [Module.Finite k C] {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : RightComodule k C V) (μ : LeftAction k C V), PairsWith ρ μ →
    ∀ W : Submodule k V, ρ.IsSubcomodule W ↔ ∀ (a : Dist k C) (x : W), μ a x ∈ W

/-- The restricted coaction gives the action along the map of distribution
algebras, also when the ambient group is not finite. -/
def RestrictionComparison : Prop :=
  ∀ {k : Type u} [Field k]
    {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    {D : Type z} [AddCommGroup D] [Module k D] [Coalgebra k D]
    {V : Type w} [AddCommGroup V] [Module k V]
    (g : C →ₗc[k] D) (ρ : RightComodule k C V) (μ : LeftAction k C V), PairsWith ρ μ →
    ∃ σ : RightComodule k D V, σ.coaction = g.toLinearMap.lTensor V ∘ₗ ρ.coaction ∧
      PairsWith σ (μ.comp (distributionMap g))

def RelativeFrobenius : Prop :=
  ∀ (k : Type u) [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k),
    ∃! f : twistCoordinates k p r A ⟶ A, FrobeniusFormula k p r A f

def FrobeniusKernel : Prop :=
  ∀ (k : Type u) [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k) (f : twistCoordinates k p r A ⟶ A),
    FrobeniusFormula k p r A f →
    ∃ h : (Specs.kernelIdeal f).IsHopfIdeal k,
      letI := h
      let Q := hopfQuotient A (Specs.kernelIdeal f)
      let i := specGroupMap (hopfQuotientMap A (Specs.kernelIdeal f))
      IsPullback i (specGroupMap (hopfUnit Q)) (specGroupMap f)
        (specGroupMap (hopfCounit (twistCoordinates k p r A))) ∧
      Specs.IsNormalSubgroup i ∧
      (Algebra.FiniteType k A → Module.Finite k Q)

def FiniteSpectrum : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k),
    IsFinite (specGroup A).X.hom ↔ Module.Finite k A

/-- Every finite group scheme is covered by the finite coordinate Hopf algebra
formulation, including finite group schemes with nonreduced coordinates. -/
def FiniteGroupPresentation : Prop :=
  ∀ (k : Type u) [Field k] (K : GroupScheme k), IsFinite K.X.hom ↔
    ∃ A : HopfAlgebraCategory k, Module.Finite k A ∧ Nonempty (specGroup A ≅ K)

end
end LinearAlgebraicGroups.Specs.FiniteDistributions
