import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.ProjectiveResolutions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.InjectiveResolutions

/-!
Horseshoe construction, paper.tex 2521–2552. The given outside resolutions
are retained. A finite direct sum is represented by a product. The term
identifications specify the standard inclusion and projection, and therefore
also give splitting in every nonaugmented degree. The coefficient sequence
is only assumed short exact; no coefficient splitting is supplied.
All rings are unital, possibly noncommutative or zero. Substitution of the
opposite ring supplies the right-module statements. Diagram lifting and
naturality are allocated to the separate horseshoe-naturality goal.
-/
namespace P103.Specs.Ch10.Horseshoe
open CategoryTheory
universe u v
variable {R : Type u} [Ring R]
variable {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]

/-- A projective horseshoe over the specified coefficient maps and outside
resolutions. The equivalences are identifications of the prescribed terms,
not a replacement of the outside resolutions by arbitrary other ones. -/
structure ProjectiveData (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (L : P103.Specs.Ch10.ProjectiveResolutions.Resolution R A) (N : P103.Specs.Ch10.ProjectiveResolutions.Resolution R C) where
  middle : P103.Specs.Ch10.ProjectiveResolutions.Resolution R B
  projective : middle.IsProjective
  term : ∀ n, middle.complex.X n ≃ₗ[R] (L.complex.X n × N.complex.X n)
  inclusion : L.complex ⟶ middle.complex
  projection : middle.complex ⟶ N.complex
  inclusion_apply : ∀ n x, term n ((inclusion.f n).hom x) = (x, 0)
  projection_apply : ∀ n x, (projection.f n).hom x = (term n x).2
  augmentation_inclusion : middle.ε.comp (inclusion.f 0).hom = i.comp L.ε
  augmentation_projection : N.ε.comp (projection.f 0).hom = p.comp middle.ε

/-- The dual horseshoe retains the chosen injective resolutions. -/
structure InjectiveData (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (L : P103.Specs.Ch10.InjectiveResolutions.Resolution R A) (N : P103.Specs.Ch10.InjectiveResolutions.Resolution R C) where
  middle : P103.Specs.Ch10.InjectiveResolutions.Resolution R B
  term : ∀ n, middle.complex.X n ≃ₗ[R] (L.complex.X n × N.complex.X n)
  inclusion : L.complex ⟶ middle.complex
  projection : middle.complex ⟶ N.complex
  inclusion_apply : ∀ n x, term n ((inclusion.f n).hom x) = (x, 0)
  projection_apply : ∀ n x, (projection.f n).hom x = (term n x).2
  augmentation_inclusion : (inclusion.f 0).hom.comp L.η = middle.η.comp i
  augmentation_projection : (projection.f 0).hom.comp middle.η = N.η.comp p

def projectiveHorseshoeType : Prop :=
  ∀ (R : Type u) [Ring R] (A B C : Type v)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∀ (L : P103.Specs.Ch10.ProjectiveResolutions.Resolution R A) (N : P103.Specs.Ch10.ProjectiveResolutions.Resolution R C),
      L.IsProjective → N.IsProjective → Nonempty (ProjectiveData i p L N)

def injectiveHorseshoeType : Prop :=
  ∀ (R : Type u) [Ring R] (A B C : Type v)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∀ (L : P103.Specs.Ch10.InjectiveResolutions.Resolution R A) (N : P103.Specs.Ch10.InjectiveResolutions.Resolution R C),
      Nonempty (InjectiveData i p L N)



/-- Explicitly records short exactness and both degreewise splittings. -/
def DegreewiseSplit {U V W : Type*} [AddCommGroup U] [AddCommGroup V]
    [AddCommGroup W] [Module R U] [Module R V] [Module R W]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W) : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
    (∃ s : W →ₗ[R] V, g.comp s = LinearMap.id) ∧
    (∃ r : V →ₗ[R] U, r.comp f = LinearMap.id)

def projectiveDegreewiseSplitType : Prop :=
  ∀ (R : Type u) [Ring R] (A B C : Type v)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (L : P103.Specs.Ch10.ProjectiveResolutions.Resolution R A)
    (N : P103.Specs.Ch10.ProjectiveResolutions.Resolution R C)
    (H : ProjectiveData i p L N) (n : ℕ),
    DegreewiseSplit (H.inclusion.f n).hom (H.projection.f n).hom

def injectiveDegreewiseSplitType : Prop :=
  ∀ (R : Type u) [Ring R] (A B C : Type v)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (L : P103.Specs.Ch10.InjectiveResolutions.Resolution R A)
    (N : P103.Specs.Ch10.InjectiveResolutions.Resolution R C)
    (H : InjectiveData i p L N) (n : ℕ),
    DegreewiseSplit (H.inclusion.f n).hom (H.projection.f n).hom

end P103.Specs.Ch10.Horseshoe
