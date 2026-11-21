import MathGenome.Internal.LinearPDE.P201Specs.Heat.CompactSpectralExpansion
import MathGenome.Internal.LinearPDE.P201.Heat.SpectralSemigroup
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.PositiveMinMax
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
open scoped InnerProductSpace NNReal
universe u v
namespace P201.Heat
open ExpandedFA.Semigroups ExpandedFA.Unbounded
open CompactSpectralExpansionExpected

namespace CoerciveForm
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (d : CoerciveForm V H)

omit [CompleteSpace V] [CompleteSpace H] in
/-- The graph identity alone fixes the shifted inverse and makes it injective. -/
theorem shifted_inverse_injective (K : H →L[ℝ] H)
    (hK : ∀ x f : H, (x, f - x) ∈ d.operator.graph ↔ K f = x) :
    Function.Injective K := by
  intro f g hfg
  obtain ⟨x, hx, hv⟩ := d.operator.mem_graph_iff.mp ((hK (K f) f).mpr rfl)
  obtain ⟨y, hy, hw⟩ := d.operator.mem_graph_iff.mp ((hK (K g) g).mpr rfl)
  have hxy : x = y := Subtype.ext (hx.trans (hfg.trans hy.symm))
  rw [hxy] at hv
  have he : f - K f = g - K g := hv.symm.trans hw
  rw [hfg] at he
  simpa using congrArg (· + K g) he

/-- Symmetry and nonnegativity of B pass to its actual shifted inverse. -/
theorem shifted_inverse_positive (K : H →L[ℝ] H)
    (hK : ∀ x f : H, (x, f - x) ∈ d.operator.graph ↔ K f = x) :
    K.IsPositive := by
  obtain ⟨hd, hs, hn⟩ := d.operator_nonnegativeSelfAdjoint
  have hf : d.operator.IsFormalAdjoint d.operator := by
    have h := LinearPMap.adjoint_isFormalAdjoint hd
    change d.operator.adjoint = d.operator at hs
    rwa [hs] at h
  refine ⟨?_, ?_⟩
  · intro f g
    obtain ⟨x, hx, hv⟩ := d.operator.mem_graph_iff.mp ((hK (K f) f).mpr rfl)
    obtain ⟨y, hy, hw⟩ := d.operator.mem_graph_iff.mp ((hK (K g) g).mpr rfl)
    have he := hf x y
    rw [hv, hw, hx, hy, inner_sub_left, inner_sub_right] at he
    dsimp only [Prod.fst] at he
    change inner ℝ (K f) g = inner ℝ f (K g)
    linarith
  · intro f
    obtain ⟨x, hx, hv⟩ := d.operator.mem_graph_iff.mp ((hK (K f) f).mpr rfl)
    have he := hn x
    change 0 ≤ inner ℝ (x : H) (d.operator x) at he
    rw [hv, hx, inner_sub_right] at he
    change 0 ≤ inner ℝ (K f) f
    exact le_trans (real_inner_self_nonneg) (sub_nonneg.mp he)

omit [CompleteSpace V] [CompleteSpace H] in
/-- A positive eigenvalue of the shifted inverse gives an eigenvector in
B's exact domain, with eigenvalue κ⁻¹-1. -/
theorem shifted_inverse_eigenvector (K : H →L[ℝ] H)
    (hK : ∀ x f : H, (x, f - x) ∈ d.operator.graph ↔ K f = x)
    (e : H) (κ : ℝ) (hκ : 0 < κ) (he : K e = κ • e) :
    (e, (κ⁻¹ - 1) • e) ∈ d.operator.graph := by
  have hk : K (κ⁻¹ • e) = e := by
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hκ.ne', one_smul]
  have hg := (hK e (κ⁻¹ • e)).mpr hk
  simpa only [sub_smul, one_smul] using hg

/-- Generator eigenvectors evolve by the real scalar exponential. We use
classical uniqueness from the general self-adjoint smoothing theorem. -/
theorem heat_eigenvector_orbit (S : C0Semigroup ℝ H)
    (hS : SpectralSemigroupExpected.HeatSemigroup d S)
    (x : H) (μ : ℝ) (hx : (x, μ • x) ∈ d.operator.graph) (t : ℝ≥0) :
    S.operators t x = Real.exp (-(t : ℝ) * μ) • x := by
  obtain ⟨R, hR⟩ := SelfAdjointSmoothing.real_selfadjoint_smoothing d.operator
    d.operator_nonnegativeSelfAdjoint
  obtain ⟨_, _, _, _, _, _, huniq⟩ := hS
  have hRS := huniq R hR.1 t
  obtain ⟨y, hy, hv⟩ := d.operator.mem_graph_iff.mp hx
  change (y : H) = x at hy
  change d.operator y = μ • x at hv
  let f : ℝ → H := fun r => Real.exp (-r * μ) • x
  have hsol : SelfAdjointSmoothing.ClassicalSolution d.operator x f := by
    refine ⟨by simp [f], ?_, ?_⟩
    · exact (by fun_prop : Continuous f).continuousWithinAt
    · intro r hr
      have hdom : f r ∈ d.operator.domain := by
        change Real.exp (-r * μ) • x ∈ d.operator.domain
        rw [← hy]
        exact d.operator.domain.smul_mem _ y.property
      refine ⟨hdom, ?_⟩
      have hval : d.operator ⟨f r, hdom⟩ = Real.exp (-r * μ) • (μ • x) := by
        have he : (⟨f r, hdom⟩ : d.operator.domain) = Real.exp (-r * μ) • y :=
          Subtype.ext (by simp [f, hy])
        rw [he, d.operator.map_smul, hv]
      have hder := (((hasDerivAt_id r).neg.mul_const μ).exp).smul_const x
      change HasDerivAt f ((Real.exp (-r * μ) * (-1 * μ)) • x) r at hder
      convert hder using 1
      rw [hval, smul_smul, ← neg_smul]
      congr 1
      ring
  have he := hR.2.2.2.2.2.1 x f hsol (t : ℝ) t.coe_nonneg
  rw [Real.toNNReal_coe] at he
  rw [hRS] at he
  exact he.symm

/-- The compact embedding case supplies precisely the compact resolvent used
by the expansion, through the actual shifted-form solution map. -/
theorem compact_resolvent_of_compact_inclusion (hj : IsCompactOperator d.j) :
    CompactResolvent d := by
  obtain ⟨_, _, _, K, _, hgraph, hcompact⟩ := form_operator_representation d
  exact ⟨d.j.comp K, hcompact hj, hgraph⟩

/-- Compactness produces a finite or countable complete basis on H itself:
injectivity of the resolvent removes the entire kernel complement. -/
theorem compact_eigenexpansion (S : C0Semigroup ℝ H)
    (hS : SpectralSemigroupExpected.HeatSemigroup d S)
    (hc : CompactResolvent d) : EigenExpansion d S := by
  classical
  obtain ⟨K, hcompact, hK⟩ := hc
  have hp := d.shifted_inverse_positive K hK
  have hinj := d.shifted_inverse_injective K hK
  have hc' : ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue
      K.toLinearMap := hcompact.isCompact_closure_image_closedBall 1
  obtain ⟨I, e, κ, hdata⟩ :=
    ExpandedFA.CompactSpectral.PositiveMinMax.ordered_positive_spectrum ℝ H K hp hc'
  obtain ⟨hI, he, hκ, hmono, heig, hsumK, hspan, hfinite, hrank, heigenspace⟩ := hdata
  have hker : K.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  rw [hker, Submodule.bot_orthogonal_eq_top] at hspan
  let b : HilbertBasis I ℝ H := HilbertBasis.mk he hspan.ge
  have hb (i : I) : b i = e i := congrFun (HilbertBasis.coe_mk he hspan.ge) i
  let eigenvalue : I → ℝ := fun i => (κ i)⁻¹ - 1
  have hg (i : I) : (b i, eigenvalue i • b i) ∈ d.operator.graph := by
    rw [hb]
    exact d.shifted_inverse_eigenvector K hK (e i) (κ i) (hκ i) (heig i)
  have hnon (i : I) : 0 ≤ eigenvalue i := by
    obtain ⟨x, hx, hv⟩ := d.operator.mem_graph_iff.mp (hg i)
    have hn := d.operator_nonnegativeSelfAdjoint.2.2 x
    change 0 ≤ inner ℝ (x : H) (d.operator x) at hn
    rw [hv, hx] at hn
    simpa only [Prod.fst, Prod.snd, inner_smul_right,
      real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow, mul_one] using hn
  have horbit (i : I) (t : ℝ≥0) :
      S.operators t (b i) = Real.exp (-(t : ℝ) * eigenvalue i) • b i :=
    d.heat_eigenvector_orbit S hS (b i) (eigenvalue i) (hg i) t
  have hsum (g : H) (t : ℝ≥0) :
      HasSum (fun i => (Real.exp (-(t : ℝ) * eigenvalue i) *
        inner ℝ (b i) g) • b i) (S.operators t g) := by
    have hs := (S.operators t).hasSum (b.hasSum_repr g)
    simpa only [map_smul, horbit, smul_smul, b.repr_apply_apply, mul_comm] using hs
  refine ⟨I, b, eigenvalue, hnon, hg, hsum, ?_, ?_⟩
  · intro hdim
    have := hdim
    have : Finite I := b.orthonormal.linearIndependent.finite
    let : Fintype I := Fintype.ofFinite I
    exact ⟨inferInstance, fun g t => (hsum g t).tsum_eq.symm.trans (tsum_fintype _)⟩
  · intro hzero
    have := hzero
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have hz : b ⟨n, hn⟩ = 0 := Subsingleton.elim _ _
    have hnorm := b.orthonormal.norm_eq_one ⟨n, hn⟩
    simp [hz] at hnorm

end CoerciveForm

/-- The full heat semigroup and compact-resolvent spectral expansion theorem. -/
theorem compact_spectral_expansion : CompactSpectralExpansionExpected.FullTheorem.{u, v} := by
  intro V H _ _ _ _ _ _ d
  obtain ⟨S, hS⟩ := spectral_semigroup d
  exact ⟨S, hS, d.compact_eigenexpansion S hS⟩

end P201.Heat
