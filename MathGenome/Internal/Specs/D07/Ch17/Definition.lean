import MathGenome.Internal.Specs.D07.Ch01.HomomorphismDefinition
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
Independent specification for K07.17.definition (paper.tex:4601–4619).
All vector spaces and groups are arbitrary. Only the matrix statements choose a
finite basis; its index type may be empty. Automorphism multiplication and
endomorphism multiplication both mean composition, with the right factor first.
-/
namespace Specs.D07.Ch17.Definition

universe u v w t

open scoped Matrix

/-- Assignment of the source's automorphism-valued representation type. -/
def LinearRepresentationType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V], Type (max v w)

abbrev linearRepresentationValue : LinearRepresentationType.{u, v, w} :=
  fun K G V _ _ _ _ => G →* (V ≃ₗ[K] V)

/-- Unbundled endomorphism data with exactly the two laws in the source can
be bundled, uniquely, as Mathlib's endomorphism-valued representation. -/
def EndomorphismCharacterization : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (r : G → Module.End K V),
    (r 1 = 1 ∧ ∀ g h, r (g * h) = r g * r h) ↔
      ∃! ρ : Representation K G V, (ρ : G → Module.End K V) = r

/-- Identity, composition and both inverse equations, without finite dimension. -/
def EndomorphismLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V),
    ρ 1 = LinearMap.id ∧
    (∀ g h, ρ (g * h) = (ρ g).comp (ρ h)) ∧
    (∀ g, ρ g * ρ g⁻¹ = 1 ∧ ρ g⁻¹ * ρ g = 1)

/-- The equivalence remembers the original linear maps in both directions;
the inverse of each resulting automorphism is exactly the action of g⁻¹. -/
def AutomorphismCorrespondence : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V],
    ∃ e : Representation K G V ≃ linearRepresentationValue K G V,
      (∀ ρ g, (e ρ g : Module.End K V) = ρ g) ∧
      (∀ σ g, e.symm σ g = (σ g : Module.End K V)) ∧
      (∀ ρ g, ((e ρ g).symm : Module.End K V) = ρ g⁻¹)

/-- Matrices in the chosen basis have the source's identity, product and
inverse laws. The inverse is stated by its two defining equations, so this
statement also applies to the zero by zero matrix ring. -/
def MatrixLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (ι : Type t)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (ρ : Representation K G V),
    LinearMap.toMatrix b b (ρ 1) = 1 ∧
    (∀ g h, LinearMap.toMatrix b b (ρ (g * h)) =
      LinearMap.toMatrix b b (ρ g) * LinearMap.toMatrix b b (ρ h)) ∧
    (∀ g,
      LinearMap.toMatrix b b (ρ g) * LinearMap.toMatrix b b (ρ g⁻¹) = 1 ∧
      LinearMap.toMatrix b b (ρ g⁻¹) * LinearMap.toMatrix b b (ρ g) = 1)

/-- A chosen finite basis gives the full correspondence, and identifies the
inverse direction with matrix action on coordinates. An arbitrary finite index
set expresses b₁,...,bₙ; no nonemptiness assumption is imposed on it. -/
def MatrixCorrespondence : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (ι : Type t)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V),
    ∃ e : Representation K G V ≃ (G →* Matrix.GeneralLinearGroup ι K),
      (∀ ρ g, (e ρ g : Matrix ι ι K) = LinearMap.toMatrix b b (ρ g)) ∧
      (∀ A g x, b.equivFun (e.symm A g x) =
        (A g : Matrix ι ι K) *ᵥ b.equivFun x)

/-- The same chosen basis identifies the source's GL(V)-valued
representations with matrix representations, with the prescribed matrix entries
and transported coordinate action in the reverse direction. -/
def AutomorphismMatrixCorrespondence : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (ι : Type t)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V),
    ∃ e : linearRepresentationValue K G V ≃ (G →* Matrix.GeneralLinearGroup ι K),
      (∀ σ g, (e σ g : Matrix ι ι K) =
        LinearMap.toMatrix b b (σ g : Module.End K V)) ∧
      (∀ A g x, b.equivFun (e.symm A g x) =
        (A g : Matrix ι ι K) *ᵥ b.equivFun x)

end Specs.D07.Ch17.Definition
