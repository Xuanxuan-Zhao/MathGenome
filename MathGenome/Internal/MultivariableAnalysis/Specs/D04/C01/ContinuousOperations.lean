import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces

/-! Independent statements for chapters/01.tex, Continuous operations.
All domain sets are arbitrary, with no nonemptiness or positive dimension
assumptions. Scalar outputs use the standard one-coordinate Euclidean space.
Matrix continuity is explicitly related to relative continuity of its rows.
The quotient assertion applies to every subset where the denominator is nonzero,
and the pointwise assertion includes every such point of the original domain. -/
noncomputable section
open Set Topology
open scoped BigOperators

namespace Specs.D04.C01.ContinuousOperations.Model
open Specs.D04.C01.EuclideanInterfaces.Model

/-- The standard identification of a real number with its one real coordinate. -/
def scalarVector (r : ℝ) : E 1 := WithLp.toLp 2 (fun _ => r)

/-- An ordered, dimension-compatible product of the first k matrices.
The empty product is the identity. Factors after k are unused. -/
def matrixChainProduct (d : ℕ → ℕ)
    (F : (i : ℕ) → Matrix (Fin (d i)) (Fin (d (i + 1))) ℝ) :
    (k : ℕ) → Matrix (Fin (d 0)) (Fin (d k)) ℝ
  | 0 => 1
  | k + 1 => matrixChainProduct d F k * F k

end Specs.D04.C01.ContinuousOperations.Model

namespace Specs.D04.C01.ContinuousOperations
open Specs.D04.C01.EuclideanInterfaces.Model
open Model

def scalarVectorType := ℝ → E 1
def scalarVectorValue : scalarVectorType := fun r => WithLp.toLp 2 (fun _ => r)

def matrixChainProductType := (d : ℕ → ℕ) →
  ((i : ℕ) → Matrix (Fin (d i)) (Fin (d (i + 1))) ℝ) →
  (k : ℕ) → Matrix (Fin (d 0)) (Fin (d k)) ℝ
def matrixChainProductValue : matrixChainProductType := Model.matrixChainProduct

def relativeContinuous_coordinates_iffType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m),
    RelativeContinuous A f ↔ ∀ i : Fin m, Continuous (fun x => f x i)

def relativeContinuous_scalarVector_iffType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (f : A → ℝ),
    RelativeContinuous A (fun x => scalarVector (f x)) ↔ Continuous f

def relativeContinuous_compType : Prop :=
  ∀ {n m p : ℕ} (A : Set (E n)) (B : Set (E m))
    (f : A → E m) (g : B → E p)
    (hmap : ∀ x : A, f x ∈ B),
    RelativeContinuous A f → RelativeContinuous B g →
    RelativeContinuous A (fun x => g ⟨f x, hmap x⟩)

def relativeContinuous_iff_open_preimagesType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m),
    RelativeContinuous A f ↔
      ∀ O : Set (E m), Open O →
        RelativelyOpen A ((Subtype.val : A → E n) '' (f ⁻¹' O))

def relativeContinuous_addType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f g : A → E m),
    RelativeContinuous A f → RelativeContinuous A g →
    RelativeContinuous A (fun x => f x + g x)

def relativeContinuous_finset_sumType : Prop :=
  ∀ {n m : ℕ} {ι : Type} (A : Set (E n)) (s : Finset ι)
    (f : ι → A → E m),
    (∀ i ∈ s, RelativeContinuous A (f i)) →
    RelativeContinuous A (fun x => ∑ i ∈ s, f i x)

def relativeContinuous_const_smulType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (c : ℝ),
    RelativeContinuous A f → RelativeContinuous A (fun x => c • f x)

def relativeContinuous_smulType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (c : A → ℝ) (f : A → E m),
    RelativeContinuous A (fun x => scalarVector (c x)) →
    RelativeContinuous A f → RelativeContinuous A (fun x => c x • f x)

def relativeContinuous_innerType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f g : A → E m),
    RelativeContinuous A f → RelativeContinuous A g →
    RelativeContinuous A (fun x => scalarVector (inner ℝ (f x) (g x)))

def continuous_matrix_iff_relativeContinuous_rowsType : Prop :=
  ∀ {n r c : ℕ} (A : Set (E n))
    (F : A → Matrix (Fin r) (Fin c) ℝ),
    Continuous F ↔
      ∀ i : Fin r, RelativeContinuous A (fun x => WithLp.toLp 2 (F x i))

def relativeContinuous_matrix_mulType : Prop :=
  ∀ {n r s c : ℕ} (A : Set (E n))
    (F : A → Matrix (Fin r) (Fin s) ℝ)
    (G : A → Matrix (Fin s) (Fin c) ℝ),
    (∀ i : Fin r, RelativeContinuous A (fun x => WithLp.toLp 2 (F x i))) →
    (∀ i : Fin s, RelativeContinuous A (fun x => WithLp.toLp 2 (G x i))) →
    ∀ i : Fin r,
      RelativeContinuous A (fun x => WithLp.toLp 2 ((F x * G x) i))

def relativeContinuous_matrixChainProductType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (d : ℕ → ℕ)
    (F : (i : ℕ) → A → Matrix (Fin (d i)) (Fin (d (i + 1))) ℝ)
    (k : ℕ),
    (∀ j < k, ∀ i : Fin (d j),
      RelativeContinuous A (fun x => WithLp.toLp 2 (F j x i))) →
    ∀ i : Fin (d 0), RelativeContinuous A
      (fun x => WithLp.toLp 2 (matrixChainProduct d (fun j => F j x) k i))

def relativeContinuous_quotientType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (p q : A → ℝ),
    RelativeContinuous A (fun x => scalarVector (p x)) →
    RelativeContinuous A (fun x => scalarVector (q x)) →
    ∀ (B : Set (E n)) (hBA : B ⊆ A),
      (∀ x : B, q ⟨x.val, hBA x.property⟩ ≠ 0) →
      RelativeContinuous B (fun x => scalarVector
        (p ⟨x.val, hBA x.property⟩ / q ⟨x.val, hBA x.property⟩))

def relativeContinuousAt_quotientType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (p q : A → ℝ),
    RelativeContinuous A (fun x => scalarVector (p x)) →
    RelativeContinuous A (fun x => scalarVector (q x)) →
    ∀ a : A, q a ≠ 0 →
      RelativeContinuousAt A (fun x => scalarVector (p x / q x)) a

end Specs.D04.C01.ContinuousOperations
