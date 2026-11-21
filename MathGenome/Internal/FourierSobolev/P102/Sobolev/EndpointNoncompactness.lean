import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.EndpointNoncompactness
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalConcentration
import MathGenome.Internal.FourierSobolev.P102.Sobolev.HolderConcentration

/-! Final assembly of the concentration examples in paper.tex:1929–1937.
The upstream construction uses the original family
`r ^ (1 - d / p) • φ (r⁻¹ • (x - x₀))` in canonical Sobolev spaces,
with its full norm uniformly bounded and its Euclidean gradient norm fixed
and positive. The endpoint results retain the actual smooth representatives.
-/
namespace P102.Sobolev.EndpointNoncompactness

/-- At 1 ≤ p < d the bounded Sobolev family has fixed positive Lp* norm,
vanishes a.e., and has no convergent subsequence in the actual Lp* space. -/
theorem subcritical_noncompactness : Expected.Subcritical :=
  subcritical_concentration

/-- At finite p > d the representatives converge uniformly to zero while
the endpoint Hölder seminorm stays positive, excluding Hölder convergence. -/
theorem supercritical_noncompactness : Expected.Supercritical :=
  supercritical_concentration

/-- At d = p = 1 fixed-height shrinking bumps admit no uniformly convergent
subsequence, despite their uniformly bounded full Sobolev norms. -/
theorem dimension_one_noncompactness : Expected.DimensionOne :=
  dimension_one_concentration

/-- Local endpoint examples apply in particular to every nonempty bounded
Lipschitz open set. The three general endpoint results suffice. -/
theorem lipschitz_from_endpoint_results
    (hsub : Expected.Subcritical) (hsuper : Expected.Supercritical)
    (hone : Expected.DimensionOne) : Expected.Lipschitz := by
  constructor
  · intro m e Ω _hL hΩ 𝕜 _ p hp _
    exact ⟨fun hpd => hsub (m + 1) 𝕜 Ω hΩ p hp hpd,
      fun hdp => hsuper (m + 1) (by omega) 𝕜 Ω hΩ p hp hdp⟩
  · intro e Ω _hL hΩ 𝕜 _
    exact hone 𝕜 Ω hΩ

/-- The endpoint failures for the bounded Lipschitz sets in Rellich's theorem,
including the separate one-dimensional supremum-norm endpoint. -/
theorem lipschitz_noncompactness : Expected.Lipschitz :=
  lipschitz_from_endpoint_results subcritical_noncompactness
    supercritical_noncompactness dimension_one_noncompactness

end P102.Sobolev.EndpointNoncompactness
