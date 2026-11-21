import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.ClosedLattice
import MathGenome.Internal.PointSetTopology.D10Topology.Ch16.SupNormAlgebras
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
Uniform closure of a unital real function algebra is a unital lattice algebra.

The absolute-value lemma reused below is the scalar approximation part of
Mathlib's StoneWeierstrass module, not its point-separating density theorem.
Its proof uses `comp_attachBound_mem_closure`, which pulls back interval
polynomial approximants along `attachBound`. Interval approximation in
`ContinuousMap.Weierstrass` is proved using Bernstein polynomials, independently
of general Stone–Weierstrass. These lemmas require only `CompactSpace X`.

The normed-ring structure on compact-domain continuous maps supplies continuous
multiplication, including on an empty domain. We also record the product error
estimate and a global bound on the norms of a uniformly convergent sequence.
-/

noncomputable section
open Set Filter
open scoped Topology
universe u
namespace D10Topology.Ch16

/-- The two-term estimate controlling products of uniform approximants. -/
theorem product_error_bound {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (a b f g : C(X, ℝ)) :
    ‖a * b - f * g‖ ≤ ‖a‖ * ‖b - g‖ + ‖g‖ * ‖a - f‖ := by
  calc
    ‖a * b - f * g‖ = ‖a * (b - g) + g * (a - f)‖ := by congr 1; ring
    _ ≤ ‖a * (b - g)‖ + ‖g * (a - f)‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖b - g‖ + ‖g‖ * ‖a - f‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)

theorem uniform_limits_mul : Specs.D10Topology.Ch16.ClosedLattice.uniform_limits_mul := by
  intro X _ _ F G f g hF hG
  have hFn : Tendsto F atTop (𝓝 f) := (tendsto_iff_uniform F f atTop).mpr hF
  have hGn : Tendsto G atTop (𝓝 g) := (tendsto_iff_uniform G g atTop).mpr hG
  have hb := Metric.isBounded_range_of_tendsto F hFn
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  refine ⟨⟨M, fun n => hM _ (mem_range_self n)⟩, ?_⟩
  exact (tendsto_iff_uniform (fun n => F n * G n) (f * g) atTop).mp (hFn.mul hGn)

theorem uniformClosure_subalgebra :
    Specs.D10Topology.Ch16.ClosedLattice.uniformClosure_subalgebra := by
  intro X _ _ A hA
  refine ⟨A.topologicalClosure, ?_, ?_⟩
  · rw [uniformClosure_eq_norm_closure]
    rfl
  · exact A.le_topologicalClosure hA

/-- Equip a function algebra containing 1 with Mathlib's unital interface,
without changing its carrier or its functions. -/
private def asUnitalSubalgebra {X : Type u} [TopologicalSpace X]
    (A : RealFunctionAlgebra X) (hA : IsUnital A) : Subalgebra ℝ C(X, ℝ) where
  carrier := A
  zero_mem' := A.zero_mem
  one_mem' := hA
  add_mem' := A.add_mem
  mul_mem' := A.mul_mem
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact A.smul_mem c hA

theorem uniformClosure_lattice :
    Specs.D10Topology.Ch16.ClosedLattice.uniformClosure_lattice := by
  intro X _ _ A hA f g hf hg
  obtain ⟨B, hB, hunit⟩ := uniformClosure_subalgebra A hA
  let S := asUnitalSubalgebra B hunit
  have hS : (S : Set C(X, ℝ)) =
      Specs.D10Topology.Ch16.SupNormAlgebras.uniformClosure (A : Set C(X, ℝ)) := hB
  have hclosed : IsClosed (S : Set C(X, ℝ)) := by
    rw [hS, uniformClosure_eq_norm_closure]
    exact isClosed_closure
  have hfS : f ∈ S := by rw [← hS] at hf; exact hf
  have hgS : g ∈ S := by rw [← hS] at hg; exact hg
  have habs : |f| ∈ S := by
    have h := ContinuousMap.abs_mem_subalgebra_closure S ⟨f, hfS⟩
    change |f| ∈ closure (S : Set C(X, ℝ)) at h
    rwa [hclosed.closure_eq] at h
  rw [← hS]
  exact ⟨habs,
    ContinuousMap.inf_mem_closed_subalgebra S hclosed ⟨f, hfS⟩ ⟨g, hgS⟩,
    ContinuousMap.sup_mem_closed_subalgebra S hclosed ⟨f, hfS⟩ ⟨g, hgS⟩⟩

end D10Topology.Ch16
