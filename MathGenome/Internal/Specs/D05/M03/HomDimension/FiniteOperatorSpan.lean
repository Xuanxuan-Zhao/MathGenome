import MathGenome.Internal.Specs.D05.M03.HomDimension

/-!
Independent statements for the finite-subfamily selection in paper.tex:1310,
also used in the simultaneous-triangularization and simultaneous-Schur proofs.
The family is an arbitrary set of endomorphisms over the original field. A
`Finset` is a finite subfamily, with its cardinality giving the length of a
possible enumeration. No commutation or spectral hypothesis is imposed.
-/

namespace Specs.D05.M03.HomDimension.FiniteOperatorSpan

/-- Adding an operator outside the current span strictly increases its dimension.
This is the progress fact in the dimension-bounded selection procedure. -/
def span_dimension_increases : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (s : Finset (Module.End K V)) (T : Module.End K V),
    T ∉ Submodule.span K (s : Set (Module.End K V)) →
      Module.finrank K (Submodule.span K (s : Set (Module.End K V))) <
        Module.finrank K (Submodule.span K (insert T (s : Set (Module.End K V))))

/-- Every possibly infinite family has a finite spanning subfamily, of size at
most the dimension of its span, which is at most `n²`. The same selected family
is empty whenever the entire span is zero (including the empty family and V=0).
-/
def finite_operator_span : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (n : ℕ), Module.finrank K V = n →
    ∀ F : Set (Module.End K V),
      ∃ s : Finset (Module.End K V),
        (s : Set (Module.End K V)) ⊆ F ∧
        Submodule.span K (s : Set (Module.End K V)) = Submodule.span K F ∧
        s.card ≤ Module.finrank K (Submodule.span K F) ∧
        Module.finrank K (Submodule.span K F) ≤ n ^ 2 ∧
        (Submodule.span K F = ⊥ → s = ∅)

end Specs.D05.M03.HomDimension.FiniteOperatorSpan
