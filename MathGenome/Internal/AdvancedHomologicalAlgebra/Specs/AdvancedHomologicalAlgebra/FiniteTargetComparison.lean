import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence

/-! HA-S03, source lines 511–535. Bounds are degreewise, exactly as in
HA-S01. The page maps are the actual representative-compatible HA-F06 maps.
The conclusion specifies the underlying cohomology isomorphism, its restriction
to every image filtration step, and compatibility of the inverses with the
inclusions. Indices `(p,n)` mean filtration and total cochain degree. -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace S03Specs
open FiniteFiltrationConvergence

/-- The target map is an isomorphism of filtered cohomology objects. -/
def TargetIsomorphisms {A : Type u} [Category.{v} A] [Abelian A]
    {X Y : FilteredComplex A} (f : FilteredMap X Y) : Prop :=
  ∀ n : ℤ, ∃ e : X.complex.homology n ≅ Y.complex.homology n,
    e.hom = HomologicalComplex.homologyMap f.hom n ∧
    ∀ p : ℤ, ∃ eStep : (cohomologyPiece X.filtration p n : A) ≅
        (cohomologyPiece Y.filtration p n : A),
      eStep.hom = cohomologyStepMap f p n ∧
      eStep.inv ≫ (cohomologyPiece X.filtration p n).arrow =
        (cohomologyPiece Y.filtration p n).arrow ≫ e.inv

/-- Comparison on any entire page implies comparison on the target with its
actual finite cohomology filtration. No uniform bound in n is assumed. -/
def FullStatement : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {X Y : FilteredComplex A} (f : FilteredMap X Y),
  DegreewiseFinite X.filtration → DegreewiseFinite Y.filtration →
  ∀ (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E) (r : ℤ),
    0 ≤ r → (∀ p n, IsIso (M.map r p n)) → TargetIsomorphisms f

end S03Specs
end AdvancedHomologicalAlgebra
