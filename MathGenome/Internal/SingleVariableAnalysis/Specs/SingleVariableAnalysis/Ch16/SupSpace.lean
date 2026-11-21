import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Compact
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.SupNorm

/-!
Independent specification of K03.16.sup_space, paper.tex:3816–3823.
The spaces below are exactly the canonical continuous maps on the real subset
with its induced topology. No new topology, operations, or norm are installed.
`CompactSpace K` means compactness of the subtype; `compactSubtype` makes this
available from the manuscript's `IsCompact K`. Norm statements permit empty K;
only maximum attainment requires nonemptiness. Uniform convergence uses the
upstream epsilon–tail predicates, with the same natural indexing convention.
-/
namespace Specs.SingleVariableAnalysis.Ch16.SupSpace

open scoped Topology

def compactSubtype : Prop := ∀ {K : Set ℝ}, IsCompact K → CompactSpace K

def realContinuousSpaceType : Type 1 := Set ℝ → Type

def realContinuousSpaceValue : realContinuousSpaceType := fun K => C(K, ℝ)

def realSupSpace_representation : Prop :=
  ∀ (K : Set ℝ),
    (∀ f : C(K, ℝ), Continuous (f : K → ℝ)) ∧
    (∀ u : K → ℝ, Continuous u → ∃! f : C(K, ℝ), (f : K → ℝ) = u)

def realSupSpace_pointwise : Prop :=
  ∀ (K : Set ℝ) (f g : C(K, ℝ)) (c : ℝ) (x : K),
    (f + g) x = f x + g x ∧ (c • f) x = c * f x ∧
    (-f) x = -f x ∧ (f - g) x = f x - g x ∧ (0 : C(K, ℝ)) x = 0

def realSupSpace_norm_maximum : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K], K.Nonempty →
    ∀ f : C(K, ℝ), ∃ x : K, ‖f‖ = |f x| ∧
      ∀ y : K, |f y| ≤ |f x|

def realSupSpace_norm_laws : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (f g : C(K, ℝ)) (c : ℝ),
    0 ≤ ‖f‖ ∧ (‖f‖ = 0 ↔ f = 0) ∧ ‖f + g‖ ≤ ‖f‖ + ‖g‖ ∧
    ‖c • f‖ = |c| * ‖f‖ ∧ ‖-f‖ = ‖f‖ ∧ ‖(0 : C(K, ℝ))‖ = 0

def realSupSpace_distance : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (f g : C(K, ℝ)),
    dist f g = ‖f - g‖

def realSupSpace_norm_converges_iff_uniform : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℝ)) (f : C(K, ℝ)),
    Filter.Tendsto (fun n => ‖F n - f‖) Filter.atTop (𝓝 0) ↔
      Ch12.Uniform.realUniformConvergesValue (fun n x => F n x) f

def realSupSpace_tendsto_iff_uniform : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℝ)) (f : C(K, ℝ)),
    Filter.Tendsto F Filter.atTop (𝓝 f) ↔
      Ch12.Uniform.realUniformConvergesValue (fun n x => F n x) f

def realSupSpace_sup_error_eq_norm : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℝ)) (f : C(K, ℝ)) (n : ℕ),
    Ch12.SupNorm.realSupErrorValue (fun m x => F m x) f n =
      ENNReal.ofReal ‖F n - f‖

def realSupSpace_empty : Prop :=
  (∀ f : C((∅ : Set ℝ), ℝ), f = 0) ∧
    (∀ f : C((∅ : Set ℝ), ℝ), ‖f‖ = 0)

def complexContinuousSpaceType : Type 1 := Set ℝ → Type

def complexContinuousSpaceValue : complexContinuousSpaceType := fun K => C(K, ℂ)

def complexSupSpace_representation : Prop :=
  ∀ (K : Set ℝ),
    (∀ f : C(K, ℂ), Continuous (f : K → ℂ)) ∧
    (∀ u : K → ℂ, Continuous u → ∃! f : C(K, ℂ), (f : K → ℂ) = u)

def complexSupSpace_pointwise : Prop :=
  ∀ (K : Set ℝ) (f g : C(K, ℂ)) (c : ℂ) (x : K),
    (f + g) x = f x + g x ∧ (c • f) x = c * f x ∧
    (-f) x = -f x ∧ (f - g) x = f x - g x ∧ (0 : C(K, ℂ)) x = 0

def complexSupSpace_norm_maximum : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K], K.Nonempty →
    ∀ f : C(K, ℂ), ∃ x : K, ‖f‖ = ‖f x‖ ∧
      ∀ y : K, ‖f y‖ ≤ ‖f x‖

def complexSupSpace_norm_laws : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (f g : C(K, ℂ)) (c : ℂ),
    0 ≤ ‖f‖ ∧ (‖f‖ = 0 ↔ f = 0) ∧ ‖f + g‖ ≤ ‖f‖ + ‖g‖ ∧
    ‖c • f‖ = ‖c‖ * ‖f‖ ∧ ‖-f‖ = ‖f‖ ∧ ‖(0 : C(K, ℂ))‖ = 0

def complexSupSpace_distance : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (f g : C(K, ℂ)),
    dist f g = ‖f - g‖

def complexSupSpace_norm_converges_iff_uniform : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℂ)) (f : C(K, ℂ)),
    Filter.Tendsto (fun n => ‖F n - f‖) Filter.atTop (𝓝 0) ↔
      Ch12.Uniform.complexUniformConvergesValue (fun n x => F n x) f

def complexSupSpace_tendsto_iff_uniform : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℂ)) (f : C(K, ℂ)),
    Filter.Tendsto F Filter.atTop (𝓝 f) ↔
      Ch12.Uniform.complexUniformConvergesValue (fun n x => F n x) f

def complexSupSpace_sup_error_eq_norm : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℂ)) (f : C(K, ℂ)) (n : ℕ),
    Ch12.SupNorm.complexSupErrorValue (fun m x => F m x) f n =
      ENNReal.ofReal ‖F n - f‖

def complexSupSpace_empty : Prop :=
  (∀ f : C((∅ : Set ℝ), ℂ), f = 0) ∧
    (∀ f : C((∅ : Set ℝ), ℂ), ‖f‖ = 0)

end Specs.SingleVariableAnalysis.Ch16.SupSpace
