import MathGenome.Internal.Specs.D05.M15.InteriorProduct.Higher
import MathGenome.Internal.Specs.D05.M15.ExteriorDerivation

/-! Degree counting and coefficient detection, paper.tex:3138–3146.
The two finite sums use the coordinate functionals of the specified finite basis.
The subtraction in the second identity is in the field (integer scalars), not
truncated natural subtraction. Detection has no finite-dimensional assumption,
and none of these statements imposes a characteristic restriction. -/
noncomputable section
namespace Specs.D05.M15.InteriorProduct.DegreeDetection
universe u v

/-- Wedge after contraction counts occupied positions. -/
def wedge_contraction : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (n : ℕ) (b : Module.Basis (Fin n) K V)
  (p : ℕ) (a : ⋀[K]^p V),
  (∑ j : Fin n, _root_.ExteriorAlgebra.ι K (b j) * interior (b.coord j) a) =
    (p : K) • (a : _root_.ExteriorAlgebra K V)

/-- Contraction after wedge counts unoccupied positions. -/
def contraction_wedge : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (n : ℕ) (b : Module.Basis (Fin n) K V)
  (p : ℕ) (a : ⋀[K]^p V),
  (∑ j : Fin n, interior (b.coord j) (_root_.ExteriorAlgebra.ι K (b j) * a)) =
    ((n : K) - (p : K)) • (a : _root_.ExteriorAlgebra K V)

/-- The induced derivation is a sum of creation followed by annihilation. -/
def derivation_formula : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (n : ℕ) (b : Module.Basis (Fin n) K V)
  (A : V →ₗ[K] V) (a : _root_.ExteriorAlgebra K V),
  ExteriorDerivation.induced A a =
    ∑ j : Fin n, _root_.ExteriorAlgebra.ι K (A (b j)) * interior (b.coord j) a

/-- Vanishing of all degree-k exterior contractions detects a homogeneous vector.
In particular this remains valid when the characteristic divides p. -/
def higher_detection : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (p k : ℕ), 1 ≤ k → k ≤ p →
  ∀ a : ⋀[K]^p V,
    (∀ α : ⋀[K]^k (Module.Dual K V), higherInterior (K := K) (V := V) α (a : _root_.ExteriorAlgebra K V) = 0) → a = 0

/-- Equivalent detection when the hypothesis is given as iterated single
contractions for every ordered k-tuple of covectors. -/
def iterated_detection : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (p k : ℕ), 1 ≤ k → k ≤ p →
  ∀ a : ⋀[K]^p V,
    (∀ f : Fin k → Module.Dual K V,
      (List.ofFn f).foldl (fun a φ => interior φ a)
        (a : _root_.ExteriorAlgebra K V) = 0) → a = 0

end Specs.D05.M15.InteriorProduct.DegreeDetection
