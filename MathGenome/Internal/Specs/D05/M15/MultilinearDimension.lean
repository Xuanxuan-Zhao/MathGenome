import MathGenome.Internal.Specs.D05.M02.Dimension
import MathGenome.Internal.Specs.D05.M03.BasisExtension
import MathGenome.Internal.Specs.D05.M15.Multilinear

/-!
Independent statements for K05.15.multilinear_dimension, paper.tex:2849–2850.

The finite slot type `I` represents the p inputs, which may be different spaces.
`κ i` indexes a supplied finite basis of the ith input. Basis tuples retain all
their indices. The coordinate and prescription results actually allow any target
space; the numerical dimension results assume all the stated finite dimensions.
An empty slot type is allowed throughout. A chosen slot is required in the
zero-input result, so that it makes no false assertion about nullary maps.
-/

namespace Specs.D05.M15.MultilinearDimension

open scoped BigOperators

/-- Agreement on all basis tuples determines a multilinear map. -/
def basis_values_determine : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*} {κ : I → Type*}
    [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W] [∀ i, Fintype (κ i)]
    (e : ∀ i, Module.Basis (κ i) K (V i)) (B C : MultilinearMap K V W),
    (∀ r : ∀ i, κ i, B (fun i => e i (r i)) = C (fun i => e i (r i))) → B = C

/-- Expanding each argument in its basis gives the coordinate formula. -/
def basis_expansion : Prop := by
  classical
  exact
    ∀ {K I : Type*} {V : I → Type*} {W : Type*} {κ : I → Type*}
      [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
      [AddCommGroup W] [Module K W] [∀ i, Fintype (κ i)]
      (e : ∀ i, Module.Basis (κ i) K (V i)) (B : MultilinearMap K V W)
      (v : ∀ i, V i),
      B v = ∑ r : ∀ i, κ i, (∏ i, (e i).repr (v i) (r i)) • B (fun i => e i (r i))

/-- Every arbitrary assignment of vectors to basis tuples extends uniquely. -/
def exists_unique_multilinear : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*} {κ : I → Type*}
    [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W] [∀ i, Fintype (κ i)]
    (e : ∀ i, Module.Basis (κ i) K (V i)) (w : (∀ i, κ i) → W),
    ∃! B : MultilinearMap K V W, ∀ r : ∀ i, κ i, B (fun i => e i (r i)) = w r

/-- The elementary maps form an actual basis. Both their coordinate formula and
their prescribed Kronecker-delta values on input basis tuples are specified. -/
def elementary_basis : Prop := by
  classical
  exact
    ∀ {K I L : Type*} {V : I → Type*} {W : Type*} {κ : I → Type*}
      [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
      [AddCommGroup W] [Module K W] [∀ i, Fintype (κ i)] [Fintype L]
      (e : ∀ i, Module.Basis (κ i) K (V i)) (f : Module.Basis L K W),
      ∃ b : Module.Basis ((∀ i, κ i) × L) K (MultilinearMap K V W),
        (∀ (r : ∀ i, κ i) (l : L) (v : ∀ i, V i),
          b (r, l) v = (∏ i, (e i).repr (v i) (r i)) • f l) ∧
        (∀ (r s : ∀ i, κ i) (l : L),
          b (r, l) (fun i => e i (s i)) = if s = r then f l else 0)

/-- Finite-dimensionality and the full intrinsic dimension formula. -/
def dimension_formula : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*}
    [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W]
    [∀ i, FiniteDimensional K (V i)] [FiniteDimensional K W],
    FiniteDimensional K (MultilinearMap K V W) ∧
      Module.finrank K (MultilinearMap K V W) =
        Module.finrank K W * ∏ i, Module.finrank K (V i)

/-- The empty-tuple convention has dimension dim W, with no input spaces
requiring a finite-dimensional hypothesis. -/
def nullary_dimension : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*}
    [Field K] [IsEmpty I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W],
    FiniteDimensional K (MultilinearMap K V W) ∧
      Module.finrank K (MultilinearMap K V W) = Module.finrank K W

/-- A zero input in a supplied slot forces all values to vanish, and both
sides of the dimension formula vanish. Supplying `i` enforces positive arity. -/
def zero_input : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*}
    [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W]
    [∀ i, FiniteDimensional K (V i)] [FiniteDimensional K W]
    (i : I), (∀ x : V i, x = 0) →
      (∀ (B : MultilinearMap K V W) (v : ∀ j, V j), B v = 0) ∧
      Module.finrank K (MultilinearMap K V W) = 0 ∧
      Module.finrank K W * ∏ j, Module.finrank K (V j) = 0

end Specs.D05.M15.MultilinearDimension
