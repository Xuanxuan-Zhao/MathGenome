import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagLineBundle

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Coalgebra WithConv
open scoped TensorProduct CategoryTheory.MonObj

universe u

noncomputable section

namespace LinearAlgebraicGroups.Specs.InductionAdjunction

open FlagLineBundle
open CharacterDescent (Character)
open QuotientEmbedding (Presentation)
open LinearAlgebraicGroups.RationalRepresentations (evaluate IsEquivariant)

variable {k : Type u} [Field k]

/-- The space of equivariant linear maps, expressed as the equalizer of the two
maps obtained by composing with the source and target coactions. -/
def equivariantHom {C V W : Type u}
    [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (δ : V →ₗ[k] V ⊗[k] C) (σ : W →ₗ[k] W ⊗[k] C) :
    Submodule k (V →ₗ[k] W) where
  carrier := {f | (f.rTensor C).comp δ = σ.comp f}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change ((f + g).rTensor C).comp δ = σ.comp (f + g)
    rw [LinearMap.rTensor_add, LinearMap.add_comp, LinearMap.comp_add]
    exact congrArg₂ (· + ·) hf hg
  smul_mem' := by
    intro a f hf
    change ((a • f).rTensor C).comp δ = σ.comp (a • f)
    rw [LinearMap.rTensor_smul, LinearMap.smul_comp, LinearMap.comp_smul]
    exact congrArg (a • ·) hf

/-- Evaluation at the identity identifies equivariant maps into the covariant
functions with equivariant functionals on the restriction to the subgroup.
Restriction changes the coaction by applying the Hopf map on the coefficient
factor, as in E01. The equivalences are natural under precomposition. -/
def Reciprocity {A D : HopfAlgebraCategory k} (q : A ⟶ D) (c : GroupLike k D)
    (ρ₁ : RightComodule k D k) (ρ : RightComodule k A (covariantFunctions q c)) : Prop :=
  let W := covariantFunctions q c
  let restrict {V : Type u} [AddCommGroup V] [Module k V] (τ : RightComodule k A V) :=
    (q.hom.toAlgHom.toLinearMap.lTensor V).comp τ.coaction
  ∃ E : ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (τ : RightComodule k A V),
      equivariantHom τ.coaction ρ.coaction ≃ₗ[k] equivariantHom (restrict τ) ρ₁.coaction,
    (∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (τ : RightComodule k A V) (f : equivariantHom τ.coaction ρ.coaction) (v : V),
        (E V τ f).val v = counit (R := k) ((f.val v : W) : A)) ∧
    (∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (τ : RightComodule k A V) (ℓ : equivariantHom (restrict τ) ρ₁.coaction)
      (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (v : V),
        letI := convolutionGroup A R
        g (((E V τ).symm ℓ).val v : A) =
          TensorProduct.lid k R ((ℓ.val.rTensor R) (evaluate A τ (g⁻¹).ofConv v))) ∧
    ∀ (V V' : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
      (τ : RightComodule k A V) (τ' : RightComodule k A V')
      (h : V' →ₗ[k] V), IsEquivariant A τ' τ h →
      ∀ f : equivariantHom τ.coaction ρ.coaction,
        ∃ f' : equivariantHom τ'.coaction ρ.coaction,
          f'.val = f.val.comp h ∧ (E V' τ' f').val = (E V τ f).val.comp h

/-- For every character, the induced module is the space of global sections
of the associated bundle, modeled by the finite-dimensional covariant
functions. Frobenius reciprocity uses these same sections and the same
opposite Borel character line. -/
def FlagInductionAdjunction : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G)
    (χ : Character P.torus.group),
    ∃ (p : BorelProjection P) (Q : Presentation P.negative)
      (a : ModObj G.val.X Q.scheme) (A D : HopfAlgebraCategory k)
      (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
      (q : A ⟶ D) (φ : DiagonalizableGroups.groupAlgebra k
        DiagonalizableGroups.IntegerCharacters ⟶ D)
      (c : GroupLike k D) (ρ₁ : RightComodule k D k)
      (L : AssociatedBundle Q a p χ) (E : BundleSection L ≃ covariantFunctions q c)
      (ρ : RightComodule k A (covariantFunctions q c)),
      Smooth Q.scheme.hom ∧ IsProper Q.scheme.hom ∧ HomogeneousQuotient.IsQuotientTorsor Q ∧
      (∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module.Finite k V)
        (j : Q.scheme ⟶ ProjectiveSpaces.projectiveSpace k V), IsClosedImmersion j.left) ∧
      μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul ∧
      specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion ∧
      specGroupMap φ = d.hom ≫ p.projection ≫ χ ∧
      (c : D) = characterCoordinate φ ∧ (∀ z, ρ₁.coaction z = z ⊗ₜ[k] (c : D)) ∧
      FiniteDimensional k (covariantFunctions q c) ∧
      (∀ s : BundleSection L,
        Q.projection ≫ s.val =
          prod.lift (𝟙 G.val.X)
            (e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) (E s : A)) ≫ L.trivialization) ∧
      ((covariantFunctions q c).subtype.rTensor A).comp ρ.coaction =
        (leftRegularCoaction A).comp (covariantFunctions q c).subtype ∧
      (∀ (R : TestAlgebra k) (h g : WithConv (A →ₐ[k] R)) (f : covariantFunctions q c),
        letI := convolutionGroup A R
        (Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ Commute.all _ _))
          (((covariantFunctions q c).subtype.rTensor A) (ρ.coaction f)) = (h⁻¹ * g) (f : A)) ∧
      Reciprocity q c ρ₁ ρ

end LinearAlgebraicGroups.Specs.InductionAdjunction
