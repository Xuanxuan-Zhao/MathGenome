import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence

open CategoryTheory LinearAlgebraicGroups
open LinearAlgebraicGroups.WeightDecomposition (weightSpace tensorCoactionMap)
open scoped DirectSum TensorProduct

universe u

namespace RepTheorySurvey.Invariants.Specs.TorusWeights

noncomputable section

abbrev coordinates (k M : Type u) [Field k] [CommGroup M] :=
  LinearAlgebraicGroups.Specs.DiagonalizableGroups.groupAlgebra k M

variable {k M V W : Type u} [Field k] [CommGroup M]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

local notation "H" => coordinates k M
local notation "e" => MonoidAlgebra.of k M

/-- The Laurent basis and its Hopf algebra operations in multiplicative notation. -/
def CharacterBasis : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M],
    ∃ b : Module.Basis M k (coordinates k M),
      (∀ m, b m = MonoidAlgebra.of k M m) ∧
      (∀ m, Coalgebra.comul (R := k) (b m) = b m ⊗ₜ[k] b m ∧
        Coalgebra.counit (R := k) (b m) = 1) ∧
      ∀ m n, b (m * n) = b m * b n

/-- The chosen character lattice gives the standard split torus as a group scheme.
The coordinate algebra comparison is contravariant. -/
def SplitTorus : Prop :=
  ∀ (k M ι : Type u) [Field k] [CommGroup M] [Fintype ι]
    (_lattice : M ≃* Multiplicative (ι → ℤ)),
    ∃ _ : Group.FG M,
      Nonempty ((LinearAlgebraicGroups.Specs.DiagonalizableGroups.diagonalGroup k M).val ≅
        (LinearAlgebraicGroups.Specs.StandardGroups.multiplicativePowerGroup k ι).val)

abbrev RepresentationComparison : Prop :=
  LinearAlgebraicGroups.Specs.WeightDecomposition.DiagonalRepresentationComparison.{u}

/-- The coaction comparison on the standard split torus itself, after identifying
its character lattice. The universal matrix uses the actual group scheme representation. -/
def SplitRepresentationComparison : Prop :=
  ∀ {k M ι V J : Type u} [Field k] [CommGroup M] [Fintype ι]
    [AddCommGroup V] [Module k V] [Fintype J] [DecidableEq J]
    (_lattice : M ≃* Multiplicative (ι → ℤ)) (b : Module.Basis J k V)
    (L : LinearAlgebraicGroups.Specs.GroupScheme k)
    (l : (groupPointsFunctor k).obj L ≅ LinearAlgebraicGroups.Specs.StandardGroups.generalLinearPoints k J),
    let D := LinearAlgebraicGroups.Specs.StandardGroups.multiplicativePowerGroup k ι
    let G : AffineGroupCategory k := ⟨D.val, D.property.1⟩
    ∃ (points : convolutionPoints (coordinates k M) ≅ (groupPointsFunctor k).obj G.val)
      (E : LinearAlgebraicGroups.Specs.RationalRepresentations.representation G L l ≃
        RightComodule k (coordinates k M) V),
      ∀ f, LinearAlgebraicGroups.RationalRepresentations.coefficients (coordinates k M) b (E f) =
        LinearAlgebraicGroups.RationalRepresentations.universalMatrix (coordinates k M) G L points l f

/-- Equivariance holds on every algebra-valued point exactly when the coactions commute. -/
def EquivarianceOnPoints : Prop :=
  ∀ {k M V W : Type u} [Field k] [CommGroup M]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RightComodule k (coordinates k M) V) (σ : RightComodule k (coordinates k M) W)
    (f : V →ₗ[k] W),
    (∀ (R : TestAlgebra k) (g : coordinates k M →ₐ[k] R),
      (f.rTensor R).comp (RationalRepresentations.evaluate (coordinates k M) ρ g) =
        (RationalRepresentations.evaluate (coordinates k M) σ g).comp f) ↔ isComoduleMap ρ σ f

abbrev InternalWeightSum : Prop :=
  LinearAlgebraicGroups.Specs.WeightDecomposition.InternalWeightSum.{u}

abbrev FiniteWeights : Prop :=
  LinearAlgebraicGroups.Specs.WeightDecomposition.FiniteWeights.{u}

abbrev InvariantWeight : Prop :=
  LinearAlgebraicGroups.Specs.WeightDecomposition.Invariants.{u}

/-- A comodule map is exactly a linear map preserving every weight. -/
def DegreePreserving : Prop :=
  ∀ {k M V W : Type u} [Field k] [CommGroup M]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RightComodule k (coordinates k M) V) (σ : RightComodule k (coordinates k M) W)
    (f : V →ₗ[k] W),
    isComoduleMap ρ σ f ↔ ∀ m, weightSpace ρ m ≤ (weightSpace σ m).comap f

/-- The coaction on a direct sum sends each inclusion to a pure character tensor. -/
def gradedCoactionMap (X : M → ModuleCat.{u} k) :
    (⨁ m, X m) →ₗ[k] (⨁ m, X m) ⊗[k] H := by
  classical
  exact DirectSum.toModule k M _ fun m ↦
    ((TensorProduct.mk k _ H).flip (e m)).comp (DirectSum.lof k M (fun j ↦ X j) m)

def GradedCoaction : Prop :=
  ∀ {k M : Type u} [Field k] [CommGroup M] (X : M → ModuleCat.{u} k),
    ∃ ρ : RightComodule k (coordinates k M) (⨁ m, X m), ρ.coaction = gradedCoactionMap X

/-- Finite-dimensional comodules over the character Hopf algebra. -/
structure FiniteComodule (k M : Type u) [Field k] [CommGroup M] where
  space : ModuleCat.{u} k
  finiteDimensional : FiniteDimensional k space
  coaction : RightComodule k (coordinates k M) space

attribute [instance] FiniteComodule.finiteDimensional

/-- Morphisms are linear maps commuting with the coactions. -/
abbrev ComoduleHom (X Y : FiniteComodule k M) :=
  { f : X.space →ₗ[k] Y.space // isComoduleMap X.coaction Y.coaction f }

instance : Category (FiniteComodule k M) where
  Hom := ComoduleHom
  id _ := ⟨LinearMap.id, by ext x; simp⟩
  comp f g := ⟨g.val.comp f.val, by
    have hf := f.property
    have hg := g.property
    unfold isComoduleMap at hf hg ⊢
    rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc,
      hg, LinearMap.comp_assoc]⟩

/-- A finitely supported family of finite-dimensional vector spaces. -/
structure FiniteGrading (k M : Type u) [Field k] [CommGroup M] where
  piece : M → ModuleCat.{u} k
  finiteDimensional : ∀ m, FiniteDimensional k (piece m)
  finiteSupport : {m | ∃ x : piece m, x ≠ 0}.Finite

attribute [instance] FiniteGrading.finiteDimensional

instance : Category (FiniteGrading k M) where
  Hom X Y := ∀ m, X.piece m →ₗ[k] Y.piece m
  id _ _ := LinearMap.id
  comp f g m := (g m).comp (f m)

def forgetComodule : FiniteComodule k M ⥤ ModuleCat.{u} k where
  obj X := X.space
  map f := ModuleCat.ofHom f.val

def sumGrading : FiniteGrading k M ⥤ ModuleCat.{u} k := by
  classical
  refine
    { obj := fun X ↦ ModuleCat.of k (⨁ m, X.piece m)
      map := fun f ↦ ModuleCat.ofHom (DirectSum.lmap f)
      map_id := ?_
      map_comp := ?_ }
  · intro X
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro m
    apply LinearMap.ext
    intro x
    simp [DirectSum.lmap_lof]
    rfl
  · intro X Y Z f g
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro m
    apply LinearMap.ext
    intro x
    simp [DirectSum.lmap_lof]
    rfl

/-- The weight functor and the homogeneous-coaction functor form an equivalence
and the canonical sum of the weight inclusions gives the forgetful isomorphism. -/
def GradedEquivalence : Prop := by
  classical
  exact ∀ (k M : Type u) [Field k] [CommGroup M],
    ∃ (E : FiniteComodule k M ≌ FiniteGrading k M)
      (h : ∀ X m, (E.functor.obj X).piece m = ModuleCat.of k (weightSpace X.coaction m))
      (N : E.functor ⋙ sumGrading ≅ forgetComodule)
      (P : sumGrading ≅ E.inverse ⋙ forgetComodule),
      (∀ (X Y : FiniteComodule k M) (f : X ⟶ Y) m (x : (E.functor.obj X).piece m),
        (((eqToHom (h Y m)).hom (E.functor.map f m x) : weightSpace Y.coaction m) :
          Y.space) = f.val (((eqToHom (h X m)).hom x : weightSpace X.coaction m) : X.space)) ∧
      (∀ X m (x : (E.functor.obj X).piece m),
        (N.hom.app X).hom (DirectSum.lof k M (fun j ↦ (E.functor.obj X).piece j) m x) =
          (((eqToHom (h X m)).hom x : weightSpace X.coaction m) : X.space)) ∧
      (∀ Y m (y : Y.piece m), (E.inverse.obj Y).coaction.coaction
          ((P.hom.app Y).hom (DirectSum.lof k M (fun j ↦ Y.piece j) m y)) =
          (P.hom.app Y).hom (DirectSum.lof k M (fun j ↦ Y.piece j) m y) ⊗ₜ[k]
            MonoidAlgebra.of k M m)

abbrev pairs (M : Type u) [CommGroup M] (m : M) := {p : M × M // p.1 * p.2 = m}

/-- A tensor weight is the direct sum of the indicated pairs of weight spaces.
The equivalence uses the tensor of the two inclusions on each summand. -/
structure TensorWeightIso
    (ρ : RightComodule k H V) (σ : RightComodule k H W) where
  coaction : RightComodule k H (V ⊗[k] W)
  coaction_eq : coaction.coaction = tensorCoactionMap ρ σ
  equiv : ∀ m, (⨁ p : pairs M m, weightSpace ρ p.val.1 ⊗[k] weightSpace σ p.val.2)
    ≃ₗ[k] weightSpace coaction m
  equiv_lof : by
    classical
    exact ∀ m (p : pairs M m) (z : weightSpace ρ p.val.1 ⊗[k] weightSpace σ p.val.2),
      (equiv m (DirectSum.lof k (pairs M m) _ p z) : V ⊗[k] W) =
        TensorProduct.mapIncl (weightSpace ρ p.val.1) (weightSpace σ p.val.2) z

def TensorWeightDecomposition : Prop :=
  ∀ {k M V W : Type u} [Field k] [CommGroup M]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : RightComodule k (coordinates k M) V) (σ : RightComodule k (coordinates k M) W),
    Nonempty (TensorWeightIso ρ σ)


/-- Tensoring comodule maps acts on each summand by the tensor of its weight restrictions. -/
def TensorWeightNaturality : Prop := by
  classical
  exact ∀ {k M V W V' W' : Type u} [Field k] [CommGroup M]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    {ρ : RightComodule k (coordinates k M) V} {σ : RightComodule k (coordinates k M) W}
    {ρ' : RightComodule k (coordinates k M) V'} {σ' : RightComodule k (coordinates k M) W'}
    (T : TensorWeightIso ρ σ) (T' : TensorWeightIso ρ' σ')
    (f : V →ₗ[k] V') (g : W →ₗ[k] W') (_ : isComoduleMap ρ ρ' f) (_ : isComoduleMap σ σ' g),
    isComoduleMap T.coaction T'.coaction (TensorProduct.map f g) ∧
      ∃ (F : ∀ m, weightSpace ρ m →ₗ[k] weightSpace ρ' m)
        (G : ∀ m, weightSpace σ m →ₗ[k] weightSpace σ' m),
        (∀ m (x : weightSpace ρ m), (F m x : V') = f x) ∧
        (∀ m (y : weightSpace σ m), (G m y : W') = g y) ∧
        ∀ m, (weightSpace T'.coaction m).subtype.comp ((T'.equiv m).toLinearMap.comp
          (DirectSum.lmap (fun p : pairs M m ↦ TensorProduct.map (F p.val.1) (G p.val.2)))) =
          (TensorProduct.map f g).comp ((weightSpace T.coaction m).subtype.comp (T.equiv m).toLinearMap)

/-- The unique direct sum expression recovers the coaction by applying the
homogeneous formula before including the weight vectors into the original space. -/
def CoactionExpansion : Prop := by
  classical
  exact ∀ {k M V : Type u} [Field k] [CommGroup M] [AddCommGroup V] [Module k V]
    (ρ : RightComodule k (coordinates k M) V) (v : V),
    ∃! x : ⨁ m, weightSpace ρ m,
      DirectSum.coeLinearMap (weightSpace ρ) x = v ∧
      (DirectSum.coeLinearMap (weightSpace ρ)).rTensor (coordinates k M)
        (gradedCoactionMap (fun m ↦ ModuleCat.of k (weightSpace ρ m)) x) = ρ.coaction v

end

end RepTheorySurvey.Invariants.Specs.TorusWeights
