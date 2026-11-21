import MathGenome.Internal.Specs.D05.M10.Companion
import MathGenome.Internal.Specs.D05.M10.InvariantFactorComputation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.List.OfFn

/-! Independent statements for the companion-presentation stage of
K05.10.invariant_factors, paper.tex:1519–1527. All matrices and equivalences
are over the original polynomial ring. No rational decomposition, Smith
certificate, or uniqueness assertion is assumed. -/
noncomputable section
open Polynomial Matrix
open scoped BigOperators
namespace Specs.D05.M10.InvariantFactors.CompanionPresentation
open D05.M10.Smith D05.M10.InvariantFactorComputation

/-- The diagonal entries of a single companion presentation, including padding. -/
def companionEntries {K : Type*} [Field K] (d : K[X]) (i : ℕ) : K[X] :=
  if i < d.natDegree - 1 then 1 else if i < d.natDegree then d else 0

/-- Polynomial matrix equivalence uses actual invertible matrices over K[X]. -/
def Equivalent {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M N : Matrix I I K[X]) : Prop :=
  ∃ U V : (Matrix I I K[X])ˣ, (U : Matrix I I K[X]) * M * (V : Matrix I I K[X]) = N

abbrev BlockIndex {K : Type*} [Field K] {s : ℕ} (d : Fin s → K[X]) :=
  Σ i, Fin (d i).natDegree

/-- The literal direct sum of the prescribed companion matrices. -/
def companionBlocks {K : Type*} [Field K] {s : ℕ} (d : Fin s → K[X]) :
    Matrix (BlockIndex d) (BlockIndex d) K :=
  Matrix.blockDiagonal' (fun i => Specs.D05.M10.Companion.companionMatrix_value K (d i))

/-- Eliminating each block leaves one annihilator and degree-minus-one units. -/
def blockDiagonalPresentation {K : Type*} [Field K] {s : ℕ} (d : Fin s → K[X]) :
    Matrix (BlockIndex d) (BlockIndex d) K[X] :=
  Matrix.diagonal (fun ij => if ij.2.val + 1 = (d ij.1).natDegree then d ij.1 else 1)

/-- The sorted diagonal: units first, then the given ordered factors, then zeros. -/
def chainEntries {K : Type*} [Field K] {s : ℕ} (d : Fin s → K[X])
    (t i : ℕ) : K[X] :=
  if hi : i < t then 1 else if h : i < t + s then d ⟨i - t, by omega⟩ else 0

/-- An elementary-operation witness for xI-C(d) ~ diag(1,...,1,d). -/
def companion_reduction : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]), d.Monic → 0 < d.natDegree →
    ∃ ops : List (Operation K d.natDegree d.natDegree),
      SmithReduction (Specs.D05.M10.Companion.companionMatrix_value K d).charmatrix
        ops d.natDegree (companionEntries d)

/-- The same single-block reduction as invertible polynomial-matrix equivalence. -/
def companion_equivalence : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]), d.Monic → 0 < d.natDegree →
    Equivalent (Specs.D05.M10.Companion.companionMatrix_value K d).charmatrix
      (rectDiagonal d.natDegree d.natDegree (companionEntries d))

/-- No divisibility hypothesis is needed to combine the block reductions. -/
def block_equivalence : Prop :=
  ∀ {K : Type*} [Field K] {s : ℕ} (d : Fin s → K[X]),
    (∀ i, (d i).Monic) → (∀ i, 0 < (d i).natDegree) →
      Equivalent (companionBlocks d).charmatrix (blockDiagonalPresentation d)

/-- For any divisibility-chain rational representation, its nonunit Smith
entries are exactly that chain. The existential enumeration only orders the
basis of the direct sum; t counts precisely the redundant unit relations.
The final assertion quantifies over EVERY Smith reduction of this presentation.
The empty family and zero-dimensional presentation are included. -/
def block_smith : Prop := by
  classical
  exact ∀ {K : Type*} [Field K] {s : ℕ} (d : Fin s → K[X]),
    (∀ i, (d i).Monic) → (∀ i, 0 < (d i).natDegree) →
    (∀ i j, i ≤ j → d i ∣ d j) →
    ∃ (t : ℕ) (e : Fin (t + s) ≃ BlockIndex d),
      t = ∑ i, ((d i).natDegree - 1) ∧
      t + s = ∑ i, (d i).natDegree ∧
      Equivalent ((companionBlocks d).charmatrix.submatrix e e)
        (rectDiagonal (t+s) (t+s) (chainEntries d t)) ∧
      ComputesMinors ((companionBlocks d).charmatrix.submatrix e e) (t+s)
        (chainEntries d t) ∧
      ∀ (ops : List (Operation K (t+s) (t+s))) (r : ℕ) (f : ℕ → K[X]),
        SmithReduction ((companionBlocks d).charmatrix.submatrix e e) ops r f →
        r = t+s ∧ f = chainEntries d t ∧
          (List.ofFn (fun i : Fin (t+s) => f i.val)).filter
            (fun p => decide (¬ IsUnit p)) = List.ofFn d

/-- Basis-enumeration independent form, useful when a rational block matrix
has already been written using any chosen Fin n coordinate order. -/
def block_smith_any_enumeration : Prop := by
  classical
  exact ∀ {K : Type*} [Field K] {s n : ℕ} (d : Fin s → K[X]),
    (∀ i, (d i).Monic) → (∀ i, 0 < (d i).natDegree) →
    (∀ i j, i ≤ j → d i ∣ d j) →
    ∀ e : Fin n ≃ BlockIndex d,
    ∃ t, t = ∑ i, ((d i).natDegree - 1) ∧ n = t+s ∧
      ComputesMinors ((companionBlocks d).charmatrix.submatrix e e) n (chainEntries d t) ∧
      ∀ (ops : List (Operation K n n)) (r : ℕ) (f : ℕ → K[X]),
        SmithReduction ((companionBlocks d).charmatrix.submatrix e e) ops r f →
        r = n ∧ f = chainEntries d t ∧
          (List.ofFn (fun i : Fin n => f i.val)).filter
            (fun p => decide (¬ IsUnit p)) = List.ofFn d

end Specs.D05.M10.InvariantFactors.CompanionPresentation
