import MathGenome.Internal.Specs.D05.M10.Cyclic
import MathGenome.Internal.Specs.D05.M13.RealNormalBlocks
import MathGenome.Internal.Specs.D05.Foundations.Crt
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Finset.Lattice.Fold

/-! The algebraic construction in paper.tex:2353–2377. The spectral/block
existence theorems are upstream; here their lines and planes are bridged to
invariant blocks, then grouped by polynomial. No cyclicity, vector annihilator,
CRT selector, or layer conclusion is part of the block hypotheses.
Indices j are zero based: j < m p corresponds to the paper's j+1 ≤ m_p.
The final orthogonal assembly and invariant-factor identification are allocated
to NormalClassification.OrthogonalCyclic. -/

noncomputable section
open Polynomial
namespace Specs.D05.M13.NormalClassification.CyclicLayers

local instance {α : Type*} : DecidableEq α := Classical.decEq α

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Exactly the algebraic data verified below for the spectral lines and real
normal planes. This also permits the same argument over other fields. -/
structure Block (T : Module.End K V) (H : Submodule K V) (p : K[X]) : Prop where
  monic : p.Monic
  irreducible : Irreducible p
  invariant : ∀ x ∈ H, T x ∈ H
  dimension : Module.finrank K H = p.natDegree
  kills : ∀ x ∈ H, aeval T p x = 0

def planePolynomial (a b : ℝ) : ℝ[X] := (X - C a) ^ 2 + C (b ^ 2)

def line_block : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) (a : K), v ≠ 0 → T v = a • v →
      Block T (K ∙ v) (X - C a)

def plane_block : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : Module.End ℝ V) (e f : V) (a b : ℝ),
    Orthonormal ℝ ![e, f] → 0 < b →
    Specs.D05.M13.RealNormalBlocks.PlaneAction T e f a b →
      Block T (Submodule.span ℝ (Set.range ![e, f])) (planePolynomial a b)

def block_cyclic : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (H : Submodule K V) (p : K[X]),
    Block T H p → ∀ v ∈ H, v ≠ 0 →
      Specs.D05.M10.Cyclic.cyclicSpace_value K V T v = H ∧
      Specs.D05.M10.Cyclic.vectorAnnihilator_value K V T v = p

/-- Group any finite list of block labels into fibers; repeated occurrences
are retained by an actual equivalence, rather than discarded as a set. -/
def group_labels : Prop :=
  ∀ {K ι : Type*} [Field K] [Fintype ι] (p : ι → K[X]),
    ∃ (P : Finset K[X]) (m : P → ℕ) (e : ι ≃ (Σ q : P, Fin (m q))),
      (∀ i, ((e i).1 : K[X]) = p i) ∧ ∀ q, 0 < m q

/-- On every component of one layer the selector acts by the indicated zero
or identity. This is stronger than extraction of the chosen vector alone. -/
def crt_selectors : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (T : Module.End K V) (H : ι → Submodule K V) (p : ι → K[X]),
    (∀ i, (p i).Monic) → (Pairwise fun i j => IsCoprime (p i) (p j)) →
    (∀ i x, x ∈ H i → aeval T (p i) x = 0) →
      ∃ e : ι → K[X], ∀ i k x, x ∈ H k →
        aeval T (e i) x = if k = i then x else 0

def single_layer : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (T : Module.End K V) (H : ι → Submodule K V) (p : ι → K[X]) (v : ι → V),
    (∀ i, Block T (H i) (p i)) → Function.Injective p →
    (∀ i, v i ∈ H i ∧ v i ≠ 0) →
      Specs.D05.M10.Cyclic.cyclicSpace_value K V T (∑ i, v i) = ⨆ i, H i ∧
      Specs.D05.M10.Cyclic.vectorAnnihilator_value K V T (∑ i, v i) = ∏ i, p i ∧
      (∀ x : ∀ i, H i, (∑ i, (x i : V)) = 0 → ∀ i, x i = 0) ∧
      ∃ e : ι → K[X], ∀ i, aeval T (e i) (∑ k, v k) = v i

variable {ι : Type*} [Fintype ι]

abbrev Available (m : ι → ℕ) (j : ℕ) := {i // j < m i}

def layerCount (m : ι → ℕ) : ℕ := Finset.univ.sup m

def layerVector (m : ι → ℕ) (v : ∀ i, Fin (m i) → V) (j : ℕ) : V := by
  classical
  exact ∑ i : Available m j, v i.1 ⟨j, i.2⟩

def layerPolynomial (m : ι → ℕ) (p : ι → K[X]) (j : ℕ) : K[X] := by
  classical
  exact ∏ i : Available m j, p i.1

def layerSpace (m : ι → ℕ) (H : ∀ i, Fin (m i) → Submodule K V)
    (j : ℕ) : Submodule K V := ⨆ i : Available m j, H i.1 ⟨j, i.2⟩

def choose_vectors : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (T : Module.End K V) (m : ι → ℕ) (p : ι → K[X])
    (H : ∀ i, Fin (m i) → Submodule K V),
    (∀ i k, Block T (H i k) (p i)) →
      ∃ v : ∀ i, Fin (m i) → V, ∀ i k, v i k ∈ H i k ∧ v i k ≠ 0

/-- All conclusions for a layer, including directness and explicit extraction. -/
def LayerResult (T : Module.End K V) (m : ι → ℕ) (p : ι → K[X])
    (H : ∀ i, Fin (m i) → Submodule K V) (v : ∀ i, Fin (m i) → V) (j : ℕ) : Prop :=
        Specs.D05.M10.Cyclic.cyclicSpace_value K V T (layerVector m v j) = layerSpace m H j ∧
        Specs.D05.M10.Cyclic.vectorAnnihilator_value K V T (layerVector m v j) =
          layerPolynomial m p j ∧
        (layerPolynomial m p j).Monic ∧ 0 < (layerPolynomial m p j).natDegree ∧
        (∀ x : ∀ i : Available m j, H i.1 ⟨j, i.2⟩,
          (∑ i, (x i : V)) = 0 → ∀ i, x i = 0) ∧
        ∃ e : Available m j → K[X], ∀ i,
          aeval T (e i) (layerVector m v j) = v i.1 ⟨j, i.2⟩

def cyclic_layers : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (T : Module.End K V) (m : ι → ℕ) (p : ι → K[X])
    (H : ∀ i, Fin (m i) → Submodule K V) (v : ∀ i, Fin (m i) → V),
    (∀ i k, Block T (H i k) (p i)) → Function.Injective p →
    (∀ i k, v i k ∈ H i k ∧ v i k ≠ 0) →
      ∀ j < layerCount m,
        LayerResult T m p H v j

def descending_factors : Prop :=
  ∀ {K ι : Type*} [Field K] [Fintype ι] (m : ι → ℕ) (p : ι → K[X]) (j : ℕ),
    layerPolynomial m p (j + 1) ∣ layerPolynomial m p j

/-- The complete grouping-and-choice construction starting from a finite family
of algebraic blocks. The equivalence records every original block occurrence. -/
def grouped_layers : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (T : Module.End K V) (H : ι → Submodule K V) (p : ι → K[X]),
    (∀ i, Block T (H i) (p i)) →
      ∃ (P : Finset K[X]) (m : P → ℕ) (e : ι ≃ (Σ q : P, Fin (m q)))
        (v : ∀ q, Fin (m q) → V),
        (∀ i, ((e i).1 : K[X]) = p i) ∧ (∀ q, 0 < m q) ∧
        (∀ q k, v q k ∈ H (e.symm ⟨q, k⟩) ∧ v q k ≠ 0) ∧
        (∀ j < layerCount m,
          LayerResult T m (fun q => (q : K[X])) (fun q k => H (e.symm ⟨q, k⟩)) v j) ∧
        ∀ j, layerPolynomial m (fun q => (q : K[X])) (j + 1) ∣
          layerPolynomial m (fun q => (q : K[X])) j

/-- On the zero space there are no available nonzero blocks, so the actual
finite lists of layer vectors and factors are empty. -/
def zero_layers : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Subsingleton V] [Fintype ι]
    (T : Module.End K V) (m : ι → ℕ) (p : ι → K[X])
    (H : ∀ i, Fin (m i) → Submodule K V) (v : ∀ i, Fin (m i) → V),
    (∀ i k, Block T (H i k) (p i)) →
      layerCount m = 0 ∧
      List.ofFn (fun j : Fin (layerCount m) => layerVector m v j) = [] ∧
      List.ofFn (fun j : Fin (layerCount m) => layerPolynomial m p j) = []

end Specs.D05.M13.NormalClassification.CyclicLayers
