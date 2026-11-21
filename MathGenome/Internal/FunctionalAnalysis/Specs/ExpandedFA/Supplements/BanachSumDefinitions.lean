import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02HilbertSum
import Mathlib.Tactic.Linarith

/-! Independent definitions for paper.tex:6234–6269. The finite exponent uses
`ℝ≥0∞` with `1 ≤ p` and `p ≠ ∞`; thus arbitrary real exponents are allowed.
The same native `lp` norm and module structures as the Hilbert sum are retained.
The c₀ carrier is the finite-positive-level-set submodule of the bounded product.
No completeness, countability or nonemptiness is required for these definitions. -/

open scoped ENNReal Classical
noncomputable section
universe u v w
namespace ExpandedFA.Supplements.BanachSumDefinitions.Spec

variable {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]

abbrev Space (p : ℝ≥0∞) : Type (max u v) := lp E p
abbrev BoundedProduct : Type (max u v) := lp E ∞

def PowerSummable (p : ℝ≥0∞) (x : ∀ i, E i) : Prop :=
  BddAbove (Set.range fun A : Finset I => ∑ i ∈ A, ‖x i‖ ^ p.toReal)

def powerSum (p : ℝ≥0∞) (x : ∀ i, E i) : ℝ :=
  ⨆ A : Finset I, ∑ i ∈ A, ‖x i‖ ^ p.toReal

def VanishesAtInfinity (x : ∀ i, E i) : Prop :=
  ∀ ε : ℝ, 0 < ε → Set.Finite {i | ε ≤ ‖x i‖}

def finiteSupport (p : ℝ≥0∞) : Set (Space E p) :=
  {x | Set.Finite {i | x i ≠ 0}}

def ofFiniteSupport (p : ℝ≥0∞) (x : ∀ i, E i)
    (hx : Set.Finite {i | x i ≠ 0}) : Space E p :=
  ⟨x, (memℓp_zero hx).of_exponent_ge (bot_le : 0 ≤ p)⟩

def truncate (p : ℝ≥0∞) (A : Finset I) (x : ∀ i, E i) : Space E p :=
  ∑ i ∈ A, lp.single p i (x i)

variable {E}

/-- Closure of the defining c₀ condition; no uniform bound is presumed. -/
theorem vanishes_zero : VanishesAtInfinity E (0 : ∀ i, E i) := by
  intro ε hε
  simp [Pi.zero_apply, norm_zero, not_le.mpr hε]

theorem vanishes_add {x y : ∀ i, E i}
    (hx : VanishesAtInfinity E x) (hy : VanishesAtInfinity E y) :
    VanishesAtInfinity E (x + y) := by
  intro ε hε
  apply ((hx (ε / 2) (half_pos hε)).union (hy (ε / 2) (half_pos hε))).subset
  intro i hi
  change ε ≤ ‖x i + y i‖ at hi
  change ε / 2 ≤ ‖x i‖ ∨ ε / 2 ≤ ‖y i‖
  by_contra h
  push Not at h
  have hn := norm_add_le (x i) (y i)
  linarith

variable (E) {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

theorem vanishes_smul {x : ∀ i, E i} (hx : VanishesAtInfinity E x) (a : 𝕜) :
    VanishesAtInfinity E (a • x) := by
  by_cases ha : a = 0
  · subst a
    simpa using (vanishes_zero (E := E))
  intro ε hε
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  apply (hx (ε / ‖a‖) (div_pos hε ha')).subset
  intro i hi
  change ε ≤ ‖a • x i‖ at hi
  change ε / ‖a‖ ≤ ‖x i‖
  rw [div_le_iff₀ ha']
  simpa [norm_smul, mul_comm] using hi

/-- The c₀ sum with its inherited supremum norm. -/
def c0Submodule : Submodule 𝕜 (BoundedProduct E) where
  carrier := {x | VanishesAtInfinity E (fun i => x i)}
  zero_mem' := vanishes_zero
  add_mem' hx hy := vanishes_add hx hy
  smul_mem' a _ hx := vanishes_smul E hx a

abbrev C0Space : Type (max u v) := c0Submodule (𝕜 := 𝕜) E

/-- Coordinate projection for p ≥ 1, including the bounded product at p = ∞. -/
def coordinate (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : I) : Space E p →L[𝕜] E i :=
  lp.evalCLM 𝕜 E p i

def inclusion (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : I) : E i →L[𝕜] Space E p :=
  lp.singleContinuousLinearMap 𝕜 E p i

/-- c₀ is a normed subspace of the bounded product. -/
def c0ToBounded : C0Space (𝕜 := 𝕜) E →L[𝕜] BoundedProduct E :=
  (c0Submodule (𝕜 := 𝕜) E).subtypeL

def c0Coordinate (i : I) : C0Space (𝕜 := 𝕜) E →L[𝕜] E i :=
  (coordinate (𝕜 := 𝕜) E ∞ i).comp (c0ToBounded E)

/-- Every finite-support bounded family satisfies the c₀ condition. -/
theorem vanishes_of_finiteSupport (x : ∀ i, E i) (hx : Set.Finite {i | x i ≠ 0}) :
    VanishesAtInfinity E x := by
  intro ε hε
  apply hx.subset
  intro i hi hzero
  have : ε ≤ 0 := by simpa [hzero] using hi
  exact (not_le.mpr hε) this

def c0OfFiniteSupport (x : ∀ i, E i) (hx : Set.Finite {i | x i ≠ 0}) :
    C0Space (𝕜 := 𝕜) E :=
  ⟨ofFiniteSupport E ∞ x hx, vanishes_of_finiteSupport E x hx⟩

def c0Inclusion (i : I) : E i →L[𝕜] C0Space (𝕜 := 𝕜) E :=
  (inclusion (𝕜 := 𝕜) E ∞ i).codRestrict (c0Submodule E) (by
    intro a
    apply vanishes_of_finiteSupport E
    apply (Set.finite_singleton i).subset
    intro j hj
    by_contra hji
    exact hj (lp.single_apply_ne ∞ i a hji))

def c0Truncate (A : Finset I) (x : ∀ i, E i) : C0Space (𝕜 := 𝕜) E :=
  ∑ i ∈ A, c0Inclusion E i (x i)

/-- Actual isometric linear identification with the upstream Hilbert sum.
It uses the identical normed space, not just an abstract equivalent family. -/
def hilbertIdentification : Space E 2 ≃ₗᵢ[𝕜] ExpandedFA.P1.C02HilbertSum.Spec.Space E :=
  LinearIsometryEquiv.refl 𝕜 _

/-! Expected definition types and complete proposition types. -/

def Space_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ℝ≥0∞ → Type (max u v)

def BoundedProduct_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  Type (max u v)

def PowerSummable_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ℝ≥0∞ → (∀ i, E i) → Prop

def powerSum_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ℝ≥0∞ → (∀ i, E i) → ℝ

def VanishesAtInfinity_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  (∀ i, E i) → Prop

def finiteSupport_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  (p : ℝ≥0∞) → Set (Space E p)

def ofFiniteSupport_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  (p : ℝ≥0∞) → (x : ∀ i, E i) → Set.Finite {i | x i ≠ 0} → Space E p

def truncate_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  (p : ℝ≥0∞) → Finset I → (∀ i, E i) → Space E p

def c0Submodule_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  Submodule 𝕜 (BoundedProduct E)

def C0Space_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  Type (max u v)

def coordinate_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  (p : ℝ≥0∞) → [Fact (1 ≤ p)] → (i : I) → Space E p →L[𝕜] E i

def inclusion_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  (p : ℝ≥0∞) → [Fact (1 ≤ p)] → (i : I) → E i →L[𝕜] Space E p

def c0ToBounded_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  C0Space (𝕜 := 𝕜) E →L[𝕜] BoundedProduct E

def c0Coordinate_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  (i : I) → C0Space (𝕜 := 𝕜) E →L[𝕜] E i

def c0OfFiniteSupport_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  (x : ∀ i, E i) → Set.Finite {i | x i ≠ 0} → C0Space (𝕜 := 𝕜) E

def c0Inclusion_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  (i : I) → E i →L[𝕜] C0Space (𝕜 := 𝕜) E

def c0Truncate_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  Finset I → (∀ i, E i) → C0Space (𝕜 := 𝕜) E

def hilbertIdentification_type :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  Space E 2 ≃ₗᵢ[𝕜] ExpandedFA.P1.C02HilbertSum.Spec.Space E

def memℓp_iff_powerSummable_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
  ∀ x : ∀ i, E i, Memℓp x p ↔ PowerSummable E p x

def exists_coordinates_iff_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
  ∀ x : ∀ i, E i, (∃ y : Space E p, (fun i => y i) = x) ↔ PowerSummable E p x

def norm_rpow_eq_sup_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ x : Space E p, ‖x‖ ^ p.toReal = powerSum E p (fun i => x i)

def norm_eq_root_sup_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ x : Space E p, ‖x‖ = (powerSum E p (fun i => x i)) ^ (1 / p.toReal)

def bounded_exists_coordinates_iff_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ∀ x : ∀ i, E i,
  (∃ y : BoundedProduct E, (fun i => y i) = x) ↔ BddAbove (Set.range fun i => ‖x i‖)

def bounded_norm_eq_sup_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ∀ x : BoundedProduct E, ‖x‖ = ⨆ i, ‖x i‖

def c0_exists_coordinates_iff_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ x : ∀ i, E i,
  (∃ y : C0Space (𝕜 := 𝕜) E, (fun i => (y.val : BoundedProduct E) i) = x) ↔
    VanishesAtInfinity E x

def c0_norm_eq_sup_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ x : C0Space (𝕜 := 𝕜) E, ‖x‖ = ⨆ i, ‖x.val i‖

def ofFiniteSupport_apply_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ∀ (p : ℝ≥0∞) (x : ∀ i, E i) (hx : Set.Finite {i | x i ≠ 0}) (i : I),
  ofFiniteSupport E p x hx i = x i

def truncate_apply_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ∀ (p : ℝ≥0∞) (A : Finset I) (x : ∀ i, E i) (j : I),
  truncate E p A x j = (if j ∈ A then x j else 0)

def truncate_finiteSupport_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)],
  ∀ (p : ℝ≥0∞) (A : Finset I) (x : ∀ i, E i),
  truncate E p A x ∈ finiteSupport E p

def coordinate_apply_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : I) (x : Space E p),
  coordinate (𝕜 := 𝕜) E p i x = x i

def inclusion_apply_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : I) (a : E i) (j : I),
  inclusion (𝕜 := 𝕜) E p i a j = Pi.single i a j

def c0Coordinate_apply_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ (i : I) (x : C0Space (𝕜 := 𝕜) E),
  c0Coordinate E i x = x.val i

def c0Inclusion_apply_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ (i : I) (a : E i) (j : I),
  (c0Inclusion (𝕜 := 𝕜) E i a).val j = Pi.single i a j

def c0Truncate_apply_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ (A : Finset I) (x : ∀ i, E i) (j : I),
  (c0Truncate (𝕜 := 𝕜) E A x).val j = (if j ∈ A then x j else 0)

def c0Truncate_finiteSupport_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ (A : Finset I) (x : ∀ i, E i),
  Set.Finite {i | (c0Truncate (𝕜 := 𝕜) E A x).val i ≠ 0}

def c0OfFiniteSupport_apply_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ (x : ∀ i, E i) (hx : Set.Finite {i | x i ≠ 0}) (i : I),
  (c0OfFiniteSupport (𝕜 := 𝕜) E x hx).val i = x i

def hilbertIdentification_apply_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ x : Space E 2, hilbertIdentification (𝕜 := 𝕜) E x = x

def empty_index_type : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
  ∀ [IsEmpty I],
  (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : Space E p), x = 0 ∧ ‖x‖ = 0) ∧
  (∀ x : C0Space (𝕜 := 𝕜) E, x = 0 ∧ ‖x‖ = 0)

end ExpandedFA.Supplements.BanachSumDefinitions.Spec
