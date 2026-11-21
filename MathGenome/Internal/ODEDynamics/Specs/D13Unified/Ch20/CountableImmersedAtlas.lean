import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent specification for the countable immersed atlas construction.
The topology on the union is an output, and is not required to be the subspace topology. -/
noncomputable section
open Set Function
open scoped ContDiff Manifold
namespace D13Unified.Ch20.CountableImmersedAtlas

variable (S E : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nested parametrizations, together with the supplied open smooth coordinate inclusions. -/
structure Data (k : ℕ∞) where
  one_le : 1 ≤ k
  U : ℕ → Set S
  open_U : ∀ m, IsOpen (U m)
  f : ℕ → S → E
  regular : ∀ m, ContDiffOn ℝ (k : ℕ∞ω) (f m) (U m)
  injective : ∀ m, InjOn (f m) (U m)
  differential : ∀ m x, x ∈ U m → Function.Injective (fderiv ℝ (f m) x)
  change : ∀ m n : ℕ, m ≤ n → OpenPartialHomeomorph S S
  change_source : ∀ m n h, (change m n h).source = U m
  change_target : ∀ m n h, (change m n h).target ⊆ U n
  change_regular : ∀ m n h,
    ContDiffOn ℝ (k : ℕ∞ω) (change m n h) (change m n h).source
  change_symm_regular : ∀ m n h,
    ContDiffOn ℝ (k : ℕ∞ω) (change m n h).symm (change m n h).target
  intertwine : ∀ m n h x, x ∈ U m → f n (change m n h x) = f m x
  nonempty : Set.Nonempty {x : E | ∃ m ξ, ξ ∈ U m ∧ f m ξ = x}

variable {S E} {k : ℕ∞}
/-- The actual union, as a type without an imposed topology in the conclusion. -/
def Point (D : Data S E k) := {x : E // ∃ m ξ, ξ ∈ D.U m ∧ D.f m ξ = x}

/-- A countable compatible atlas on the union, modelled on the whole parameter space S.
Injectivity of the differential is asserted for the actual coordinate expression of inclusion. -/
structure Atlas (D : Data S E k) where
  topology : TopologicalSpace (Point D)
  chart : ℕ → @OpenPartialHomeomorph (Point D) S topology inferInstance
  source_eq : ∀ m, (chart m).source = {x | x.val ∈ D.f m '' D.U m}
  target_eq : ∀ m, (chart m).target = D.U m
  inverse_eq : ∀ m ξ, ξ ∈ D.U m → ((chart m).symm ξ).val = D.f m ξ
  cover : ⋃ m, (chart m).source = univ
  transitions : ∀ m n,
    ContDiffOn ℝ (k : ℕ∞ω) ((chart m).symm.trans (chart n))
      ((chart m).symm.trans (chart n)).source
  inclusion_continuous : @Continuous (Point D) E topology inferInstance Subtype.val
  inclusion_injective : Function.Injective (fun x : Point D => x.val)
  inclusion_regular : ∀ m,
    ContDiffOn ℝ (k : ℕ∞ω) (fun ξ => ((chart m).symm ξ).val) (D.U m)
  inclusion_differential : ∀ m ξ, ξ ∈ D.U m →
    Function.Injective (fderiv ℝ (fun ξ => ((chart m).symm ξ).val) ξ)
  hausdorff : @T2Space (Point D) topology
  second_countable : @SecondCountableTopology (Point D) topology
  chartedSpace : @ChartedSpace S inferInstance (Point D) topology
  atlas_eq : @atlas S inferInstance (Point D) topology chartedSpace = range chart
  atlas_countable : (@atlas S inferInstance (Point D) topology chartedSpace).Countable
  manifold : @IsManifold ℝ inferInstance S inferInstance inferInstance S inferInstance
    (modelWithCornersSelf ℝ S) (k : ℕ∞ω) (Point D) topology chartedSpace
  dimension : ∀ x : Point D,
    Module.finrank ℝ (TangentSpace (modelWithCornersSelf ℝ S) x) = Module.finrank ℝ S

/-- The full gluing assertion. No atlas, topology, or coherence certificate is assumed. -/
def gluingExpected : Prop :=
  ∀ (S E : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ∞) (D : Data S E k), Nonempty (Atlas D)

end D13Unified.Ch20.CountableImmersedAtlas
