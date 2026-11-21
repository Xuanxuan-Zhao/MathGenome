import MathGenome.Internal.Specs.D05.M03.LinearMap
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
Independent statements for K05.15.multilinear, paper.tex:2692–2701.

The Cartesian product is a dependent function type, so the input spaces may
differ. The type constructor and slotwise characterization apply to any index
type; the simultaneous expansion has finitely many slots. There is no dimension
or characteristic restriction. Finsets index occurrences, not sets of vectors.
In particular, repeated vectors are retained and all sums have finite support.
The nullary identification is an actual linear equivalence with evaluation and
constant-map formulas. Tensor constructions and the subsequent supplements are
separate obligations from this foundational paragraph.
-/

namespace Specs.D05.M15.Multilinear

open scoped BigOperators

universe u v w z

/-- The canonical type constructor for a family of input vector spaces. -/
def multilinearMap_type : Type (max (u + 1) (v + 1) (w + 1) (z + 1)) :=
  (K : Type u) → (I : Type v) → (V : I → Type w) → (W : Type z) →
    [Field K] → [∀ i, AddCommGroup (V i)] → [∀ i, Module K (V i)] →
    [AddCommGroup W] → [Module K W] → Type (max v w z)

/-- Reuse Mathlib's bundled multilinear maps on the same spaces and actions. -/
def multilinearMap_value : multilinearMap_type.{u, v, w, z} :=
  fun K _ V W _ _ _ _ _ => MultilinearMap K V W

/-- A function is multilinear exactly when it is additive and homogeneous in
each selected slot, with every other coordinate fixed. -/
def multilinearMap_iff_axioms : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*} [Field K]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W] [DecidableEq I]
    (b : (∀ i, V i) → W),
    (∃ B : MultilinearMap K V W, (B : (∀ i, V i) → W) = b) ↔
      (∀ (m : ∀ i, V i) (i : I) (x y : V i),
        b (Function.update m i (x + y)) =
          b (Function.update m i x) + b (Function.update m i y)) ∧
      (∀ (m : ∀ i, V i) (i : I) (a : K) (x : V i),
        b (Function.update m i (a • x)) = a • b (Function.update m i x))

/-- Fixing all other arguments gives a linear map in the chosen argument. -/
def slot_linear : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*} [Field K]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W] [DecidableEq I]
    (b : MultilinearMap K V W) (m : ∀ i, V i) (i : I),
    ∃ L : V i →ₗ[K] W, ∀ x, L x = b (Function.update m i x)

/-- The vector-space structure uses pointwise addition and scalar action.
The module witness acts on the canonical additive group of multilinear maps. -/
def pointwise_vector_space : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*} [Field K]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W],
    ∃ M : Module K (MultilinearMap K V W),
      (∀ (a : K) (b : MultilinearMap K V W) (m : ∀ i, V i),
        (letI := M; a • b) m = a • b m) ∧
      (∀ (b c : MultilinearMap K V W) (m : ∀ i, V i),
        (b + c) m = b m + c m) ∧
      (∀ m : ∀ i, V i, (0 : MultilinearMap K V W) m = 0)

/-- Empty products are singleton domains; evaluation identifies nullary maps
with their chosen value in W, and the inverse sends a vector to a constant map. -/
def nullary_equivalence : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*} [Field K] [IsEmpty I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W],
    ∃ E : W ≃ₗ[K] MultilinearMap K V W,
      (∀ (w : W) (m : ∀ i, V i), E w m = w) ∧
      (∀ b : MultilinearMap K V W, E.symm b = b 0)

/-- A zero in any particular slot forces the value to vanish. A slot must
actually be supplied, so this does not impose a false condition in degree zero. -/
def map_coord_zero : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*} [Field K]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W]
    (b : MultilinearMap K V W) (m : ∀ i, V i) (i : I),
    m i = 0 → b m = 0

/-- In positive arity the all-zero tuple also has value zero. -/
def map_zero : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*} [Field K] [Nonempty I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W] (b : MultilinearMap K V W), b 0 = 0

/-- Applying one scalar in each slot multiplies the coefficients; for an empty
slot family the coefficient is the empty product 1. -/
def map_scalar_product : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {W : Type*} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W]
    (b : MultilinearMap K V W) (a : I → K) (m : ∀ i, V i),
    b (fun i => a i • m i) = (∏ i, a i) • b m

/-- The complete finite expansion, with an arbitrary finite family in each
slot. A summand is indexed by a choice of one occurrence in every slot.
The formula also includes empty summation sets and zero slots. -/
def map_finite_combination : Prop := by
  classical
  exact
    ∀ {K I : Type*} {V : I → Type*} {W : Type*} {A : I → Type*}
      [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
      [AddCommGroup W] [Module K W]
      (b : MultilinearMap K V W) (s : ∀ i, Finset (A i))
      (a : ∀ i, A i → K) (e : ∀ i, A i → V i),
      b (fun i => ∑ j ∈ s i, a i j • e i j) =
        ∑ r ∈ Fintype.piFinset s, (∏ i, a i (r i)) • b (fun i => e i (r i))

end Specs.D05.M15.Multilinear
