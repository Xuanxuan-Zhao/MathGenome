import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Dini
import Mathlib.Topology.UniformSpace.Dini

/-!
# Dini's theorem

K03.12.dini, paper.tex:1228–1237. The compact domain is a type `K`;
subsets are represented by their subtypes, with relative continuity.
The hypotheses allow the empty domain and impose monotonicity only in
the sequence index, never in the spatial variable.

We reuse Mathlib's `Monotone.tendstoUniformly_of_forall_tendsto` and
`Antitone.tendstoUniformly_of_forall_tendsto`, specialized to the canonical
reals. Their proof uses monotone shrinking errors, continuity, and compactness
to make the local tail estimates uniform. The decreasing result uses the
order dual. The upstream sequence and uniform equivalences translate the
filter limits to exactly the manuscript's epsilon predicates.
-/

namespace SingleVariableAnalysis

universe u

/-- Increasing pointwise convergence to a continuous real limit on a compact domain
is uniform. -/
theorem dini_monotone {K : Type u} [TopologicalSpace K]
    (hK : IsCompact (Set.univ : Set K))
    (F : ℕ → K → ℝ) (f : K → ℝ)
    (hF : ∀ n, Continuous (F n)) (hf : Continuous f)
    (hmono : ∀ x, Monotone (fun n => F n x))
    (hpoint : RealPointwiseConverges F f) : RealUniformConverges F f := by
  let : CompactSpace K := isCompact_univ_iff.mp hK
  apply (realUniformConverges_iff F f).mpr
  exact Monotone.tendstoUniformly_of_forall_tendsto hF
    (fun _ _ h x => hmono x h) hf
    (fun x => (realSequenceConverges_iff _ _).mp (hpoint x))

/-- Decreasing pointwise convergence to a continuous real limit on a compact domain
is uniform. -/
theorem dini_antitone {K : Type u} [TopologicalSpace K]
    (hK : IsCompact (Set.univ : Set K))
    (F : ℕ → K → ℝ) (f : K → ℝ)
    (hF : ∀ n, Continuous (F n)) (hf : Continuous f)
    (hanti : ∀ x, Antitone (fun n => F n x))
    (hpoint : RealPointwiseConverges F f) : RealUniformConverges F f := by
  let : CompactSpace K := isCompact_univ_iff.mp hK
  apply (realUniformConverges_iff F f).mpr
  exact Antitone.tendstoUniformly_of_forall_tendsto hF
    (fun _ _ h x => hanti x h) hf
    (fun x => (realSequenceConverges_iff _ _).mp (hpoint x))

/-- Dini's theorem with either of the two monotonicity directions. -/
theorem dini {K : Type u} [TopologicalSpace K]
    (hK : IsCompact (Set.univ : Set K))
    (F : ℕ → K → ℝ) (f : K → ℝ)
    (hF : ∀ n, Continuous (F n)) (hf : Continuous f)
    (hmono : (∀ x, Monotone (fun n => F n x)) ∨
      (∀ x, Antitone (fun n => F n x)))
    (hpoint : RealPointwiseConverges F f) : RealUniformConverges F f := by
  rcases hmono with hmono | hanti
  · exact dini_monotone hK F f hF hf hmono hpoint
  · exact dini_antitone hK F f hF hf hanti hpoint

end SingleVariableAnalysis
