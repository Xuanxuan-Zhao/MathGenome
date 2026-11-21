import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Independent interface for Definition fa2:p1:c02:hilbert-sum (paper.tex 484–496).
The scalar convention is Mathlib's conjugate-first, linear-second convention.
No countability or nonzero-summand hypothesis is imposed. The native `lp H 2`
is shared with the later Banach-sum interface: it keeps its existing norm,
module structure and inner product. The membership/norm assertions are more
general than Hilbert spaces and therefore also apply without completeness.
Coordinate/truncation definitions support the separately allocated structure
and density results; those propositions are not assumed here. -/
open scoped ENNReal Classical

noncomputable section

universe u v w
namespace ExpandedFA.P1.C02HilbertSum.Spec

variable {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)]

/-- The canonical dependent `lp` realization, at exponent two. -/
abbrev Space : Type (max u v) := lp H 2

/-- Finiteness of the supremum of the nonnegative finite squared sums. -/
def SquareSummable (x : ∀ i, H i) : Prop :=
  BddAbove (Set.range fun A : Finset I => ∑ i ∈ A, ‖x i‖ ^ 2)

/-- Used on square-summable families, this real supremum is the nonnegative sum.
For arbitrary families finiteness is asserted separately by `SquareSummable`. -/
def squaredSum (x : ∀ i, H i) : ℝ :=
  ⨆ A : Finset I, ∑ i ∈ A, ‖x i‖ ^ 2

/-- Finitely supported elements of the direct sum. -/
def finiteSupport : Set (Space H) :=
  {x | Set.Finite ({i | x i ≠ 0})}

/-- Include any finitely supported family into the sum. -/
def ofFiniteSupport (x : ∀ i, H i) (hx : Set.Finite ({i | x i ≠ 0})) :
    Space H :=
  ⟨x, (memℓp_zero hx).of_exponent_ge (by positivity)⟩

/-- Truncation is also defined for families not in the sum. -/
def truncate (A : Finset I) (x : ∀ i, H i) : Space H := by
  classical
  exact ∑ i ∈ A, lp.single 2 i (x i)

variable {𝕜 : Type*} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)]

/-- Canonical coordinate projection, with the norm inherited from `lp`. -/
def coordinate (i : I) : Space H →L[𝕜] H i :=
  lp.evalCLM 𝕜 H 2 i

/-- Canonical coordinate inclusion. Classical equality introduces no hypothesis on `I`. -/
def inclusion (i : I) : H i →L[𝕜] Space H := by
  classical
  exact lp.singleContinuousLinearMap 𝕜 H 2 i

/-! Closed expected types and propositions, independent of the implementation. -/

def Space_type :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)],
  Type (max u v)

def SquareSummable_type :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)],
  (∀ i, H i) → Prop

def squaredSum_type :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)],
  (∀ i, H i) → ℝ

def finiteSupport_type :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)],
  Set (Space H)

def ofFiniteSupport_type :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)],
  (x : ∀ i, H i) → Set.Finite {i | x i ≠ 0} → Space H

def truncate_type :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)],
  Finset I → (∀ i, H i) → Space H

def coordinate_type :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)],
  (i : I) → Space H →L[𝕜] H i

def inclusion_type :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)],
  (i : I) → H i →L[𝕜] Space H

def memℓp_iff_squareSummable_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ x : ∀ i, H i, Memℓp x 2 ↔ SquareSummable H x

def exists_coordinates_iff_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ x : ∀ i, H i,
    (∃ y : Space H, (fun i => y i) = x) ↔ SquareSummable H x

def norm_sq_eq_tsum_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ x : Space H, ‖x‖ ^ 2 = ∑' i, ‖x i‖ ^ 2

def norm_sq_eq_sup_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ x : Space H, ‖x‖ ^ 2 = squaredSum H (fun i => x i)

def ofFiniteSupport_apply_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ (x : ∀ i, H i) (hx : Set.Finite {i | x i ≠ 0}) (i : I),
    ofFiniteSupport H x hx i = x i

def truncate_apply_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ (A : Finset I) (x : ∀ i, H i) (j : I),
    truncate H A x j = (if j ∈ A then x j else 0)

def norm_sq_truncate_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ (A : Finset I) (x : ∀ i, H i),
    ‖truncate H A x‖ ^ 2 = ∑ i ∈ A, ‖x i‖ ^ 2

def truncate_finiteSupport_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ (A : Finset I) (x : ∀ i, H i),
    truncate H A x ∈ finiteSupport H

def ofFiniteSupport_mem_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ (x : ∀ i, H i) (hx : Set.Finite {i | x i ≠ 0}),
    ofFiniteSupport H x hx ∈ finiteSupport H

def mem_finiteSupport_iff_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ x : Space H,
    x ∈ finiteSupport H ↔ ∃ A : Finset I, truncate H A (fun i => x i) = x

def coordinate_apply_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)],
  ∀ (i : I) (x : Space H), coordinate (𝕜 := 𝕜) H i x = x i

def inclusion_apply_self_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)],
  ∀ (i : I) (a : H i), inclusion (𝕜 := 𝕜) H i a i = a

def inclusion_apply_ne_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)],
  ∀ (i j : I) (a : H i), j ≠ i → inclusion (𝕜 := 𝕜) H i a j = 0

def norm_inclusion_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)],
  ∀ (i : I) (a : H i), ‖inclusion (𝕜 := 𝕜) H i a‖ = ‖a‖

def inner_eq_tsum_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)],
  ∀ x y : Space H, inner 𝕜 x y = ∑' i, inner 𝕜 (x i) (y i)

def hasSum_inner_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
  {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)],
  ∀ x y : Space H,
    HasSum (fun i => inner 𝕜 (x i) (y i)) (inner 𝕜 x y)

end ExpandedFA.P1.C02HilbertSum.Spec
