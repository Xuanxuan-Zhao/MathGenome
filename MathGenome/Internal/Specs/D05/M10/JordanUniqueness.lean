import MathGenome.Internal.Specs.D05.M10.JordanExistence
import MathGenome.Internal.Specs.D05.M10.Generalized
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.EquivFin

/-! K05.10.jordan_uniqueness, paper.tex:1562–1565.
The block data are actual chain bases, not assumed kernel-dimension certificates.
For general operators the chains live in the canonical generalized eigenspaces.
All fields and all finite dimensions, including zero, are allowed. -/
noncomputable section
open scoped BigOperators Classical
namespace Specs.D05.M10.JordanUniqueness

/-- A disjoint union of positive-length nilpotent chains, with the actual basis. -/
structure Chains {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (N : Module.End K V) where
  blocks : ℕ
  length : Fin blocks → ℕ
  positive : ∀ i, 0 < length i
  basis : Module.Basis (Σ i, Fin (length i)) K V
  zero : ∀ i (j : Fin (length i)), j.val = 0 → N (basis ⟨i, j⟩) = 0
  step : ∀ i (j k : Fin (length i)), j.val = k.val + 1 →
    N (basis ⟨i, j⟩) = basis ⟨i, k⟩

/-- The upstream Jordan chain convention, with eigenvalues attached to blocks. -/
structure JordanBasis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) where
  blocks : ℕ
  length : Fin blocks → ℕ
  eigenvalue : Fin blocks → K
  positive : ∀ i, 0 < length i
  basis : Module.Basis (Σ i, Fin (length i)) K V
  zero : ∀ i (j : Fin (length i)), j.val = 0 →
    T (basis ⟨i, j⟩) = eigenvalue i • basis ⟨i, j⟩
  step : ∀ i (j k : Fin (length i)), j.val = k.val + 1 →
    T (basis ⟨i, j⟩) = eigenvalue i • basis ⟨i, j⟩ + basis ⟨i, k⟩

/-- Intrinsic nullity, with natural-number subtraction in the counting formulas. -/
def nullity {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (N : Module.End K V) (j : ℕ) : ℕ := Module.finrank K (LinearMap.ker (N ^ j))

def blocksAtLeast {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {N : Module.End K V} (c : Chains N) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => j ≤ c.length i)).card

def blocksExactly {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {N : Module.End K V} (c : Chains N) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => c.length i = j)).card

/-- The actual nilpotent restriction to the shared generalized eigenspace. -/
def nilpotentPart {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K) :
    Module.End K (Generalized.generalizedEigenspace_value K V T μ) :=
  (T - μ • 1).restrict
    (p := T.genEigenspace μ (Module.finrank K V))
    (q := T.genEigenspace μ (Module.finrank K V)) (by
      intro x hx
      rw [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hx ⊢
      rw [← Module.End.mul_apply, ← pow_succ, pow_succ',
        Module.End.mul_apply, hx, map_zero])

/-- Data at every scalar. A zero generalized eigenspace has an empty block family. -/
abbrev SpectralData {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) := ∀ μ : K, Chains (nilpotentPart T μ)

/-- The single-block case is recorded separately from additivity over blocks. -/
def single_block_nullity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (c : Chains N),
    ∀ (h : c.blocks = 1) (j : ℕ),
      nullity N j = min j (c.length ⟨0, by rw [h]; omega⟩)

def kernel_dimensions : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (c : Chains N) (j : ℕ),
    nullity N j = ∑ i, min j (c.length i)

def blocks_at_least : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (c : Chains N) (j : ℕ),
    0 < j → blocksAtLeast c j = nullity N j - nullity N (j - 1)

def blocks_exactly : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (c : Chains N) (j : ℕ),
    0 < j → blocksExactly c j =
      (nullity N j - nullity N (j - 1)) - (nullity N (j + 1) - nullity N j)

def kernels_eventually_full : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V), IsNilpotent N →
    ∀ j, Module.finrank K V ≤ j → LinearMap.ker (N ^ j) = ⊤

/-- Equality is a permutation of block occurrences, retaining repeated sizes. -/
def nilpotent_uniqueness : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (c d : Chains N),
    ∃ e : Fin c.blocks ≃ Fin d.blocks, ∀ i, d.length (e i) = c.length i

def spectral_data_exists : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V), Nonempty (SpectralData T)

/-- Kernel formulas on each actual G_μ give the intrinsic spectral block counts. -/
def spectral_counts : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (d : SpectralData T) (μ : K) (j : ℕ),
    0 < j → blocksExactly (d μ) j =
      (nullity (nilpotentPart T μ) j - nullity (nilpotentPart T μ) (j - 1)) -
      (nullity (nilpotentPart T μ) (j + 1) - nullity (nilpotentPart T μ) j)

def spectral_uniqueness : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (c d : SpectralData T) (μ : K),
    ∃ e : Fin (c μ).blocks ≃ Fin (d μ).blocks,
      ∀ i, (d μ).length (e i) = (c μ).length i

/-- Equal spectral block data are equivalent to similarity over K. The linear
isomorphism is explicit in the conclusion; no scalar extension is used. -/
def similarity_criterion : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : Module.End K V) (S : Module.End K W), T.charpoly.Splits → S.charpoly.Splits →
    ∀ (c : SpectralData T) (d : SpectralData S),
      (∀ μ j, blocksExactly (c μ) j = blocksExactly (d μ) j) ↔
      ∃ e : V ≃ₗ[K] W, ∀ x, e (T x) = S (e x)

/-- Existence uses exactly the upstream splitting hypothesis. -/
def jordan_basis_exists : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V), T.charpoly.Splits → Nonempty (JordanBasis T)

/-- Bridge from the chain representation to the shared superdiagonal matrices. -/
def jordan_basis_matrix : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (c : JordanBasis T),
    LinearMap.toMatrix c.basis c.basis T = JordanExistence.jordanMatrix c.length c.eigenvalue

/-- Uniqueness for arbitrary Jordan bases of the operator, with no prescribed
choice of generalized eigenspace decomposition. -/
def jordan_basis_uniqueness : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (c d : JordanBasis T),
    ∃ e : Fin c.blocks ≃ Fin d.blocks, ∀ i,
      d.eigenvalue (e i) = c.eigenvalue i ∧ d.length (e i) = c.length i

/-- The converse and forward similarity statements for arbitrary Jordan bases. -/
def jordan_similarity_criterion : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : Module.End K V) (S : Module.End K W) (c : JordanBasis T) (d : JordanBasis S),
    (∃ f : Fin c.blocks ≃ Fin d.blocks, ∀ i,
      d.eigenvalue (f i) = c.eigenvalue i ∧ d.length (f i) = c.length i) ↔
    ∃ e : V ≃ₗ[K] W, ∀ x, e (T x) = S (e x)

end Specs.D05.M10.JordanUniqueness
