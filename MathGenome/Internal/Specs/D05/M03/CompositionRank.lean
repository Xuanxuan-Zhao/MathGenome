import MathGenome.Internal.Specs.D05.M03.Image
import MathGenome.Internal.Specs.D05.M03.RankNullity
import MathGenome.Internal.Specs.D05.M02.SubspaceDimension

/-!
Independent statements for K05.03.composition_rank (paper.tex:590–598).

Images are the canonical ranges. Each rank is `Module.finrank` of that image,
exactly the value in `Specs.D05.M03.Image.rank_value`. The two finiteness
conclusions ensure the composite rank is used only on a finite-dimensional
image. No ambient space is assumed finite-dimensional. The equality cases
require finiteness only of the image whose rank occurs on the right.
-/

namespace Specs.D05.M03.CompositionRank

/-- The composite image is the image of the first image. -/
def image_comp_eq_map : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (T : V →ₗ[K] W),
    LinearMap.range (T.comp S) = (LinearMap.range S).map T

/-- The composite image lies in the second image. -/
def image_comp_le : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (T : V →ₗ[K] W),
    LinearMap.range (T.comp S) ≤ LinearMap.range T

/-- A finite-dimensional first image suffices for finiteness of the composite. -/
def finite_image_comp_of_source : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (T : V →ₗ[K] W)
    [FiniteDimensional K (LinearMap.range S)],
    FiniteDimensional K (LinearMap.range (T.comp S))

/-- A finite-dimensional second image also suffices. -/
def finite_image_comp_of_target : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (T : V →ₗ[K] W)
    [FiniteDimensional K (LinearMap.range T)],
    FiniteDimensional K (LinearMap.range (T.comp S))

/-- Rank cannot increase by postcomposition. -/
def rank_comp_le_source : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (T : V →ₗ[K] W)
    [FiniteDimensional K (LinearMap.range S)],
    Module.finrank K (LinearMap.range (T.comp S)) ≤
      Module.finrank K (LinearMap.range S)

/-- Rank cannot increase by precomposition. -/
def rank_comp_le_target : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (T : V →ₗ[K] W)
    [FiniteDimensional K (LinearMap.range T)],
    Module.finrank K (LinearMap.range (T.comp S)) ≤
      Module.finrank K (LinearMap.range T)

/-- The displayed minimum bound, with both finite image hypotheses. -/
def rank_comp_le : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (T : V →ₗ[K] W)
    [FiniteDimensional K (LinearMap.range S)]
    [FiniteDimensional K (LinearMap.range T)],
    Module.finrank K (LinearMap.range (T.comp S)) ≤
      min (Module.finrank K (LinearMap.range S)) (Module.finrank K (LinearMap.range T))

/-- Injective postcomposition preserves the finite image rank. -/
def rank_comp_eq_of_injective : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (T : V →ₗ[K] W)
    [FiniteDimensional K (LinearMap.range S)],
    Function.Injective T →
      Module.finrank K (LinearMap.range (T.comp S)) =
        Module.finrank K (LinearMap.range S)

/-- Surjective precomposition preserves the finite image rank. -/
def rank_comp_eq_of_surjective : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (T : V →ₗ[K] W)
    [FiniteDimensional K (LinearMap.range T)],
    Function.Surjective S →
      Module.finrank K (LinearMap.range (T.comp S)) =
        Module.finrank K (LinearMap.range T)

/-- Composition on the output side by an isomorphism preserves rank. -/
def rank_comp_equiv_left : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : U →ₗ[K] V) (e : V ≃ₗ[K] W) [FiniteDimensional K (LinearMap.range S)],
    Module.finrank K (LinearMap.range (e.toLinearMap.comp S)) =
      Module.finrank K (LinearMap.range S)

/-- Composition on the input side by an isomorphism preserves rank. -/
def rank_comp_equiv_right : Prop :=
  ∀ {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : U ≃ₗ[K] V) (T : V →ₗ[K] W) [FiniteDimensional K (LinearMap.range T)],
    Module.finrank K (LinearMap.range (T.comp e.toLinearMap)) =
      Module.finrank K (LinearMap.range T)

end Specs.D05.M03.CompositionRank
