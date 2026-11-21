import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Contractible

open Set Filter
open scoped Topology
noncomputable section

namespace D12Complex.SimplyConnectedNoncontinuation
open NoncontinuationExample

abbrev reciprocal : Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation.reciprocal_type :=
  NoncontinuationExample.reciprocal

abbrev segmentPath : Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation.segmentPath_type :=
  NoncontinuationExample.segmentPath

theorem reciprocal_holomorphic :
    Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation.reciprocal_holomorphic_type := by
  refine ⟨isOpen_ne, ?_⟩
  intro z hz
  exact (differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id |>.inv
    (sub_ne_zero.mpr (Ne.symm hz))

theorem no_continuous_extension :
    Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation.no_continuous_extension_type := by
  intro f hf heq
  have hc : ContinuousAt (fun z : ℂ => (1 - z) * f z) 1 :=
    (continuousAt_const.sub continuousAt_id).mul hf
  have hzero : Tendsto (fun z : ℂ => (1 - z) * f z) (𝓝[≠] 1) (𝓝 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have heq' : (fun z : ℂ => (1 - z) * f z) =ᶠ[𝓝[≠] 1] (fun _ => 1) := heq
  have hone : Tendsto (fun z : ℂ => (1 - z) * f z) (𝓝[≠] 1) (𝓝 1) :=
    tendsto_const_nhds.congr' heq'.symm
  exact zero_ne_one (tendsto_nhds_unique hzero hone)

private lemma plane_domain : IsDomain (univ : Set ℂ) :=
  ⟨univ_nonempty, isOpen_univ, isPreconnected_univ⟩

private lemma continuous_segmentPath (r : ℝ) : Continuous (segmentPath r) :=
  Complex.continuous_ofReal.comp (continuous_const.mul continuous_subtype_val)

private lemma segmentPath_zero (r : ℝ) : segmentPath r 0 = 0 := by
  simp [segmentPath, NoncontinuationExample.segmentPath]

private lemma segmentPath_one (r : ℝ) : segmentPath r 1 = (r : ℂ) := by
  simp [segmentPath, NoncontinuationExample.segmentPath]

private lemma segmentPath_ne_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (t : unitInterval) : segmentPath r t ≠ 1 := by
  intro h
  have heq : r * (t : ℝ) = 1 := by
    simpa [segmentPath, NoncontinuationExample.segmentPath] using congrArg Complex.re h
  have hle : r * (t : ℝ) ≤ r := by
    simpa using mul_le_mul_of_nonneg_left t.property.2 hr
  linarith

theorem continuation_before_one :
    Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation.continuation_before_one_type := by
  intro r hr hr1
  let Φ : GermFamily (segmentPath r) := fun t =>
    HolomorphicGerm.ofFunction reciprocal reciprocal_holomorphic (segmentPath_ne_one hr hr1 t)
  refine ⟨Φ 0, Φ, rfl, plane_domain, continuous_segmentPath r,
    fun _ => mem_univ _, rfl, ?_⟩
  intro s
  exact ⟨{z : ℂ | z ≠ 1}, reciprocal, univ, isOpen_univ, mem_univ s,
    reciprocal_holomorphic, fun t _ => ⟨segmentPath_ne_one hr hr1 t, rfl⟩⟩

/-- Multiplication by the entire function 1-z acts on the actual quotient germs. -/
private def multiplyGerm {a : ℂ} (g : HolomorphicGerm a) : HolomorphicGerm a :=
  ⟨((fun z : ℂ => 1 - z) : Germ (𝓝 a) ℂ) * g.val, by
    obtain ⟨U, f, ha, hf, hfg⟩ := g.property
    refine ⟨U, fun z => (1 - z) * f z, ha,
      ⟨hf.1, fun z hz => ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).mul (hf.2 z hz)⟩,
      ?_⟩
    rw [← hfg]
    rfl⟩

private lemma multiplyGerm_locallyRepresented {γ : unitInterval → ℂ} {Φ : GermFamily γ}
    (hΦ : LocallyRepresented γ Φ) :
    LocallyRepresented γ (fun t => multiplyGerm (Φ t)) := by
  intro s
  obtain ⟨U, f, I, ho, hs, hf, hr⟩ := hΦ s
  refine ⟨U, fun z => (1 - z) * f z, I, ho, hs,
    ⟨hf.1, fun z hz => ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).mul (hf.2 z hz)⟩,
    fun t ht => ⟨(hr t ht).1, ?_⟩⟩
  change ((fun z : ℂ => 1 - z) : Germ (𝓝 (γ t)) ℂ) * (Φ t).val = _
  rw [(hr t ht).2]
  rfl

private lemma one_holomorphic : HolomorphicOn (univ : Set ℂ) (fun _ => (1 : ℂ)) :=
  ⟨isOpen_univ, fun _ _ => differentiableAt_const _⟩

/-- Uniqueness transports the initial identity to every point of the path. -/
private lemma product_identity {γ : unitInterval → ℂ} {φ : HolomorphicGerm (γ 0)}
    {Φ : GermFamily γ} (hΦ : IsContinuation univ γ φ Φ) (hstart : γ 0 = 0)
    (hφ : φ.val = ((fun z : ℂ => reciprocal z) : Germ (𝓝 (γ 0)) ℂ)) (t : unitInterval) :
    (multiplyGerm (Φ t)).val = ((fun _ : ℂ => (1 : ℂ)) : Germ (𝓝 (γ t)) ℂ) := by
  let Ψ : GermFamily γ := fun t =>
    HolomorphicGerm.ofFunction (fun _ => (1 : ℂ)) one_holomorphic (mem_univ _)
  have hinit : multiplyGerm (Φ 0) = Ψ 0 := by
    apply Subtype.ext
    change ((fun z : ℂ => 1 - z) : Germ (𝓝 (γ 0)) ℂ) * (Φ 0).val = _
    rw [hΦ.2.2.2.1, hφ]
    apply Germ.coe_eq.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (γ 0), z ≠ 1 := by
      rw [hstart]
      exact isOpen_ne.mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm hz))
  have hmul : IsContinuation univ γ (Ψ 0) (fun t => multiplyGerm (Φ t)) :=
    ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, hinit, multiplyGerm_locallyRepresented hΦ.2.2.2.2⟩
  have hone : IsContinuation univ γ (Ψ 0) Ψ := by
    refine ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, rfl, ?_⟩
    intro s
    exact ⟨univ, fun _ => (1 : ℂ), univ, isOpen_univ, mem_univ _,
      one_holomorphic, fun _ _ => ⟨mem_univ _, rfl⟩⟩
  exact congrArg Subtype.val
    (ContinuationOperations.continuation_unique univ γ (Ψ 0) _ Ψ hmul hone t)

theorem no_continuation_to_one :
    Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation.no_continuation_to_one_type := by
  intro γ φ hstart hend hφ ⟨Φ, hΦ⟩
  obtain ⟨U, f, ha, hf, hrep⟩ := (Φ 1).property
  have heq := product_identity hΦ hstart hφ 1
  change ((fun z : ℂ => 1 - z) : Germ (𝓝 (γ 1)) ℂ) * (Φ 1).val = _ at heq
  rw [← hrep] at heq
  have hid : ∀ᶠ z in 𝓝 (γ 1), (1 - z) * f z = 1 := Germ.coe_eq.mp heq
  have hc : ContinuousAt f (γ 1) := (hf.2 _ ha).continuousAt
  rw [hend] at hc hid
  exact no_continuous_extension f hc (hid.filter_mono nhdsWithin_le_nhds)

theorem no_entire_extension :
    Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation.no_entire_extension_type := by
  rintro ⟨f, hf, heq⟩
  let Φ : GermFamily (segmentPath 1) := fun t =>
    HolomorphicGerm.ofFunction f hf (mem_univ _)
  have hφ : (Φ 0).val =
      ((fun z : ℂ => reciprocal z) : Germ (𝓝 (segmentPath 1 0)) ℂ) := by
    change (f : Germ (𝓝 (segmentPath 1 0)) ℂ) = _
    simpa [segmentPath, NoncontinuationExample.segmentPath, reciprocal] using heq
  apply no_continuation_to_one (segmentPath 1) (Φ 0) (segmentPath_zero 1)
    (by simpa using segmentPath_one 1) hφ
  refine ⟨Φ, plane_domain, continuous_segmentPath 1, fun _ => mem_univ _, rfl, ?_⟩
  intro s
  exact ⟨univ, f, univ, isOpen_univ, mem_univ _, hf,
    fun _ _ => ⟨mem_univ _, rfl⟩⟩

theorem simply_connected_counterexample :
    Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation.simply_connected_counterexample_type := by
  refine ⟨inferInstance, plane_domain, continuous_segmentPath 1, segmentPath_zero 1, ?_, ?_⟩
  · simpa using segmentPath_one 1
  · let φ : HolomorphicGerm (segmentPath 1 0) :=
      HolomorphicGerm.ofFunction reciprocal reciprocal_holomorphic
        (by rw [segmentPath_zero]; norm_num)
    refine ⟨φ, rfl, no_continuation_to_one (segmentPath 1) φ (segmentPath_zero 1) ?_ rfl⟩
    simpa using segmentPath_one 1

end D12Complex.SimplyConnectedNoncontinuation
