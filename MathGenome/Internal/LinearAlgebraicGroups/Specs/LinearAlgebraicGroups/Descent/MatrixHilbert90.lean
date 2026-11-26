import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology

open CategoryTheory LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.StandardGroups
open LinearAlgebraicGroups.Descent.NonabelianCohomology

namespace LinearAlgebraicGroups.Descent.MatrixHilbert90

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The coefficient action is induced by applying the point functor to the
automorphisms of the extension field. -/
def coefficientAction (F : TestAlgebra k ⥤ GrpCat.{u}) :
    Gal(K/k) →* MulAut (F.obj (CommAlgCat.of k K)) where
  toFun σ := (F.mapIso (CommAlgCat.isoMk σ)).groupIsoToMulEquiv
  map_one' := by
    ext x : 1
    change F.map (𝟙 (CommAlgCat.of k K)) x = x
    rw [F.map_id]
    rfl
  map_mul' σ τ := by
    ext x : 1
    change F.map (CommAlgCat.ofHom τ.toAlgHom ≫ CommAlgCat.ofHom σ.toAlgHom) x = _
    rw [F.map_comp]
    rfl

/-- Galois acts on invertible matrices by acting on their entries. -/
abbrev glAction (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Gal(K/k) →* MulAut (Matrix.GeneralLinearGroup ι K) :=
  coefficientAction (generalLinearPoints k ι)

/-- Galois acts on determinant-one matrices by acting on their entries. -/
abbrev slAction (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Gal(K/k) →* MulAut (Matrix.SpecialLinearGroup ι K) :=
  coefficientAction (specialLinearPoints k ι)

/-- Every crossed homomorphism is represented by a coboundary. -/
def AllCoboundaries {Γ M : Type u} [Group Γ] [Group M] (ρ : Γ →* MulAut M) : Prop :=
  ∀ a : Γ → M, (∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) →
    ∃ b : M, ∀ σ, a σ = b⁻¹ * ρ σ b

/-- The continuous version, for the given topology on the acting group and
the discrete topology on the coefficient group. -/
def AllContinuousCoboundaries {Γ M : Type u} [Group Γ] [TopologicalSpace Γ] [Group M]
    (ρ : Γ →* MulAut M) : Prop :=
  letI : TopologicalSpace M := ⊥
  ∀ a : Cocycle ρ, ∃ b : M, ∀ σ, a σ = b⁻¹ * ρ σ b

/-- The pointed first cohomology set consists of its neutral class. -/
def AllClassesNeutral {Γ M : Type u} [Group Γ] [TopologicalSpace Γ] [Group M]
    (ρ : Γ →* MulAut M) : Prop :=
  letI : TopologicalSpace M := ⊥
  ∀ x : H1 ρ, x = basepoint ρ

namespace Specification

def FiniteGL : Prop :=
  ∀ {k K ι : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype ι] [DecidableEq ι] [Nonempty ι], AllCoboundaries (glAction (k := k) (K := K) ι)

def FiniteSL : Prop :=
  ∀ {k K ι : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype ι] [DecidableEq ι] [Nonempty ι], AllCoboundaries (slAction (k := k) (K := K) ι)

def ContinuousGL : Prop :=
  ∀ {k S ι : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [Fintype ι] [DecidableEq ι] [Nonempty ι],
    AllContinuousCoboundaries (glAction (k := k) (K := S) ι)

def ContinuousSL : Prop :=
  ∀ {k S ι : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [Fintype ι] [DecidableEq ι] [Nonempty ι],
    AllContinuousCoboundaries (slAction (k := k) (K := S) ι)

def FiniteGLH1 : Prop :=
  ∀ {k K ι : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype ι] [DecidableEq ι] [Nonempty ι], AllClassesNeutral (glAction (k := k) (K := K) ι)

def FiniteSLH1 : Prop :=
  ∀ {k K ι : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype ι] [DecidableEq ι] [Nonempty ι], AllClassesNeutral (slAction (k := k) (K := K) ι)

/-- The separable-closure statement on the representing group scheme, whose
points are identified with the matrix functor naturally in the test algebra. -/
def SchemeH1 {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (F : TestAlgebra k ⥤ GrpCat.{u}) : Prop :=
  ∀ (G : GroupScheme k), ((groupPointsFunctor k).obj G ≅ F) →
    ∀ x : groupH1 k G.X S, x = groupBasepoint k G.X S

def ContinuousGLH1 : Prop :=
  ∀ {k S ι : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [Fintype ι] [DecidableEq ι] [Nonempty ι],
    SchemeH1 (S := S) (generalLinearPoints k ι)

def ContinuousSLH1 : Prop :=
  ∀ {k S ι : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [Fintype ι] [DecidableEq ι] [Nonempty ι],
    SchemeH1 (S := S) (specialLinearPoints k ι)

end Specification
end LinearAlgebraicGroups.Descent.MatrixHilbert90
