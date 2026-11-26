import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalArtinAlgebras
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerConditions

/-! Schlessinger's setup for covariant functors on local Artin algebras. -/

universe u w z

namespace CommutativeAlgebraNotes

open CategoryTheory SchlessingerConditionsSpec

/-- A covariant functor from local Artin k-algebras to sets with F(k) a singleton. -/
abbrev ArtinFunctor (k : Type u) [Field k] := ArtinFunctorModel.{u,w} k

/-- A complete Noetherian local k-algebra with specified residue field k. -/
abbrev CompleteLocalAlgebra (k : Type u) [Field k] := CompleteLocalAlgebraModel k

namespace LocalArtinAlgebra

variable {k : Type u} [Field k]

/-- The canonical map to the base field object. -/
abbrev residueHom (A : LocalArtinAlgebra.{u,u} k) : Hom A (field k) :=
  residueHomModel A

end LocalArtinAlgebra

namespace ArtinFunctor

open LocalArtinAlgebra

variable {k : Type u} [Field k]

/-- The set-theoretic fibre product of two maps. -/
abbrev CompatiblePairs {X Y Z : Type z} (f : X → Z) (g : Y → Z) :=
  CompatiblePairsModel f g

/-- The canonical comparison induced by the two projections from the algebra pullback. -/
abbrev comparison (F : ArtinFunctor.{u,w} k)
    {A₁ A A₂ : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A) (g : Hom A₂ A) :=
  comparisonModel F f g

/-- The tangent set F(k[ε]/(ε²)). -/
abbrev Tangent (F : ArtinFunctor.{u,w} k) := TangentModel F

/-- Surjectivity of the comparison whenever the second leg is small. -/
abbrev H1 (F : ArtinFunctor.{u,w} k) : Prop := H1Model F

/-- Bijectivity of the comparison over k with second source the dual numbers. -/
abbrev H2 (F : ArtinFunctor.{u,w} k) : Prop := H2Model F

/-- Bijectivity of the comparison for two copies of the same small extension. -/
abbrev H4 (F : ArtinFunctor.{u,w} k) : Prop := H4Model F

end ArtinFunctor

namespace CompleteLocalAlgebra

variable {k : Type u} [Field k]

/-- The functor of local k-algebra maps from R, acting by postcomposition. -/
abbrev hR (R : CompleteLocalAlgebra k) := homFunctorModel R

/-- The normalized functor h_R in the chosen set universe. -/
abbrev representable (R : CompleteLocalAlgebra k) : ArtinFunctor.{u,w} k :=
  representableModel R

/-- The Artin quotient R / m^(n+1). -/
abbrev truncation (R : CompleteLocalAlgebra k) (n : ℕ) := truncationModel R n

/-- The map from R to its Artin quotient. -/
abbrev toTruncation (R : CompleteLocalAlgebra k) (n : ℕ) := toTruncationModel R n

/-- The quotient transition from index n to index m for m ≤ n. -/
abbrev truncationMap (R : CompleteLocalAlgebra k) {m n : ℕ} (h : m ≤ n) :=
  truncationMapModel R h

theorem toTruncation_surjective (R : CompleteLocalAlgebra k) (n : ℕ) :
    Function.Surjective (R.toTruncation n) :=
  Ideal.Quotient.mk_surjective

@[simp]
theorem ker_toTruncation (R : CompleteLocalAlgebra k) (n : ℕ) :
    RingHom.ker (R.toTruncation n).val = IsLocalRing.maximalIdeal R ^ (n + 1) :=
  Ideal.Quotient.mkₐ_ker k _

@[simp]
theorem toTruncation_postcomp (R : CompleteLocalAlgebra k) {m n : ℕ} (h : m ≤ n) :
    (R.toTruncation n).postcomp (R.truncationMap h) = R.toTruncation m :=
  CompleteLocalAlgebra.Hom.ext (fun _ => rfl)

end CompleteLocalAlgebra

namespace ArtinFunctor

open LocalArtinAlgebra

variable {k : Type u} [Field k]

/-- The relative lifting map for a natural transformation from h_R and a morphism B → A. -/
abbrev liftingMap {R : CompleteLocalAlgebra k} {F : ArtinFunctor.{u,w} k}
    (τ : R.representable.toFunctor ⟶ F.toFunctor)
    {A B : LocalArtinAlgebra.{u,u} k} (g : Hom B A) :=
  liftingMapModel τ g

/-- Surjectivity of the relative lifting map along every small extension. -/
abbrev Smooth {R : CompleteLocalAlgebra k} {F : ArtinFunctor.{u,w} k}
    (τ : R.representable.toFunctor ⟶ F.toFunctor) : Prop :=
  SmoothModel τ

/-- A complete Noetherian local base and a smooth map from h_R that is a tangent bijection. -/
abbrev Hull (F : ArtinFunctor.{u,w} k) := HullModel F

/-- Existence of a natural isomorphism from h_R for a complete Noetherian local base. -/
abbrev Prorepresentable (F : ArtinFunctor.{u,w} k) : Prop := ProrepresentableModel F

/-- A family of elements on the positive-power quotients, compatible with all transitions. -/
abbrev CompatibleFamily (R : CompleteLocalAlgebra k) (F : ArtinFunctor.{u,w} k) :=
  CompatibleFamilyModel R F

end ArtinFunctor
end CommutativeAlgebraNotes
