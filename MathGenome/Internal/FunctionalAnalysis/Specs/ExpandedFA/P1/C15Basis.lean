import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.Algebra.Module.Basic

/-! Independent interface for paper.tex, fa2:p1:c15:basis (lines 3810–3823).
`e i` denotes the source's `e_{i+1}`: `range N` is exactly its first N terms.
No completeness or continuity of the coordinates is included in either predicate.
The normed-field formulation specializes in particular to ℝ and ℂ.
The definition and algebraic claims hold even without completeness, so include
all Banach spaces of the manuscript. No continuity of coordinates is assumed. -/

open Filter Topology
open scoped BigOperators

noncomputable section

universe u v

namespace ExpandedFA.P1.C15Basis.Spec

variable {𝕜 : Type u} {E : Type v} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Natural-order partial sums, rather than the net of all finite subsums. -/
def orderedPartialSum (e : ℕ → E) (a : ℕ → 𝕜) (N : ℕ) : E :=
  ∑ i ∈ Finset.range N, a i • e i

/-- The raw unique norm-convergent expansion property. -/
def IsRawSchauderBasis (e : ℕ → E) : Prop :=
  (∀ i, e i ≠ 0) ∧ ∀ x : E, ∃! a : ℕ → 𝕜,
    Tendsto (orderedPartialSum e a) atTop (𝓝 x)

noncomputable def rawCoordinates {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e)
    (x : E) : ℕ → 𝕜 := Classical.choose (h.2 x).exists

def rawPartialSum {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e)
    (N : ℕ) (x : E) : E := orderedPartialSum e (rawCoordinates h x) N

/-- A finite ordered list of length d, including d = 0. -/
def finiteSynthesis {d : ℕ} (e : Fin d → E) (a : Fin d → 𝕜) : E :=
  ∑ i, a i • e i

def IsRawFiniteBasis {d : ℕ} (e : Fin d → E) : Prop :=
  (∀ i, e i ≠ 0) ∧ ∀ x : E, ∃! a : Fin d → 𝕜, finiteSynthesis e a = x

noncomputable def finiteCoordinates {d : ℕ} {e : Fin d → E}
    (h : IsRawFiniteBasis (𝕜 := 𝕜) e) (x : E) : Fin d → 𝕜 :=
  Classical.choose (h.2 x).exists

/-- For N ≥ d all indices are retained; for N = 0 none are retained. -/
def finitePartialSum {d : ℕ} {e : Fin d → E}
    (h : IsRawFiniteBasis (𝕜 := 𝕜) e) (N : ℕ) (x : E) : E :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < N), finiteCoordinates h x i • e i

def emptyFamily : Fin 0 → E := Fin.elim0

end ExpandedFA.P1.C15Basis.Spec

/-! Expected declaration types and definition values. These are types and values,
not axioms, and this module imports no candidate implementation. -/
namespace ExpandedFA.P1.C15Basis.Spec.Expected

def orderedPartialSumType : Type _ :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], (ℕ → E) → (ℕ → 𝕜) → ℕ → E

def orderedPartialSumValue : orderedPartialSumType := @orderedPartialSum

def IsRawSchauderBasisType : Type _ :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], (ℕ → E) → Prop

def IsRawSchauderBasisValue : IsRawSchauderBasisType := @IsRawSchauderBasis

def rawCoordinatesType : Type _ :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e), E → ℕ → 𝕜

def rawCoordinatesValue : rawCoordinatesType := @rawCoordinates

def rawPartialSumType : Type _ :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e), ℕ → E → E

def rawPartialSumValue : rawPartialSumType := @rawPartialSum

def finiteSynthesisType : Type _ :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ}, (Fin d → E) → (Fin d → 𝕜) → E

def finiteSynthesisValue : finiteSynthesisType := @finiteSynthesis

def IsRawFiniteBasisType : Type _ :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ}, (Fin d → E) → Prop

def IsRawFiniteBasisValue : IsRawFiniteBasisType := @IsRawFiniteBasis

def finiteCoordinatesType : Type _ :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f), E → Fin d → 𝕜

def finiteCoordinatesValue : finiteCoordinatesType := @finiteCoordinates

def finitePartialSumType : Type _ :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f), ℕ → E → E

def finitePartialSumValue : finitePartialSumType := @finitePartialSum

def emptyFamilyType : Type _ :=
  ∀ {E : Type v}, Fin 0 → E

def emptyFamilyValue : emptyFamilyType := @emptyFamily

def rawCoordinates_tendsto : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e), ∀ (x : E), Tendsto (orderedPartialSum e (rawCoordinates h x)) atTop (𝓝 x)

def rawCoordinates_unique : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e), ∀ (x : E) (a : ℕ → 𝕜), Tendsto (orderedPartialSum e a) atTop (𝓝 x) → a = rawCoordinates h x

def rawCoordinates_add : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e), ∀ (x y : E), rawCoordinates h (x + y) = fun i => rawCoordinates h x i + rawCoordinates h y i

def rawCoordinates_smul : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e), ∀ (c : 𝕜) (x : E), rawCoordinates h (c • x) = fun i => c * rawCoordinates h x i

def rawPartialSum_zero : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e), ∀ (x : E), rawPartialSum h 0 x = 0

def rawPartialSum_tendsto : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e), ∀ (x : E), Tendsto (fun N => rawPartialSum h N x) atTop (𝓝 x)

def finiteCoordinates_expansion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f), ∀ (x : E), finiteSynthesis f (finiteCoordinates hf x) = x

def finiteCoordinates_unique : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f), ∀ (x : E) (a : Fin d → 𝕜), finiteSynthesis f a = x → a = finiteCoordinates hf x

def finiteCoordinates_add : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f), ∀ (x y : E), finiteCoordinates hf (x + y) = fun i => finiteCoordinates hf x i + finiteCoordinates hf y i

def finiteCoordinates_smul : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f), ∀ (c : 𝕜) (x : E), finiteCoordinates hf (c • x) = fun i => c * finiteCoordinates hf x i

def finitePartialSum_zero : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f), ∀ (x : E), finitePartialSum hf 0 x = 0

def finitePartialSum_of_le : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f), ∀ (N : ℕ), d ≤ N → ∀ (x : E), finitePartialSum hf N x = x

def emptyFamily_isRawFiniteBasis : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ [Subsingleton E], IsRawFiniteBasis (𝕜 := 𝕜) (emptyFamily (E := E))

def subsingleton_of_emptyFamily_basis : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], IsRawFiniteBasis (𝕜 := 𝕜) (emptyFamily (E := E)) → Subsingleton E

def emptyPartialSum_eq_zero : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ (hf : IsRawFiniteBasis (𝕜 := 𝕜) (emptyFamily (E := E))) (N : ℕ) (x : E), finitePartialSum hf N x = 0

def rawLinearMaps_exist : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e), (∀ i : ℕ, ∃ L : E →ₗ[𝕜] 𝕜, ∀ x, L x = rawCoordinates h x i) ∧ (∀ N : ℕ, ∃ P : E →ₗ[𝕜] E, ∀ x, P x = rawPartialSum h N x)

def finiteLinearMaps_exist : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E], ∀ {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f), (∀ i : Fin d, ∃ L : E →ₗ[𝕜] 𝕜, ∀ x, L x = finiteCoordinates hf x i) ∧ (∀ N : ℕ, ∃ P : E →ₗ[𝕜] E, ∀ x, P x = finitePartialSum hf N x)

end ExpandedFA.P1.C15Basis.Spec.Expected
