import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero

/-!
# Compact support and vanishing at infinity

The native Mathlib spaces `CompactlySupportedContinuousMap X 𝕜` and
`ZeroAtInftyContinuousMap X 𝕜` are the single canonical Cc and C0 interfaces.
These bridges identify their functions with the literal conditions in Chapter 19.
All statements hold for arbitrary topological domains and thus include the LCH
case, without adding countability or nonemptiness assumptions.
-/

namespace D11.Ch19

universe u v

/-- The single canonical Cc interface, a reducible alias of Mathlib's native type. -/
abbrev Cc (X : Type u) [TopologicalSpace X] (E : Type v) [Zero E] [TopologicalSpace E] :=
  CompactlySupportedContinuousMap X E

/-- The single canonical C0 interface, a reducible alias of Mathlib's native type. -/
abbrev Czero (X : Type u) [TopologicalSpace X] (E : Type v) [Zero E] [TopologicalSpace E] :=
  ZeroAtInftyContinuousMap X E

/-- Topological support is the closure of the nonzero set. -/
theorem support_eq (X : Type u) [TopologicalSpace X] (E : Type v) [Zero E]
    (f : X → E) : tsupport f = closure {x | f x ≠ 0} := rfl

/-- The native compact-support predicate agrees with the paper definition. -/
theorem compactSupport_iff (X : Type u) [TopologicalSpace X] (E : Type v) [Zero E]
    (f : X → E) : HasCompactSupport f ↔ IsCompact (closure {x | f x ≠ 0}) := Iff.rfl

/-- A continuous function tends to zero along the cocompact filter iff all its
positive closed norm levels are compact. -/
theorem zeroAtInfinity_iff (X : Type u) [TopologicalSpace X]
    (E : Type v) [NormedAddCommGroup E] (f : X → E) (hf : Continuous f) :
    Filter.Tendsto f (Filter.cocompact X) (nhds 0) ↔
      ∀ ε : ℝ, 0 < ε → IsCompact {x | ε ≤ ‖f x‖} := by
  constructor
  · intro h ε hε
    have hev : {x | ‖f x‖ < ε} ∈ Filter.cocompact X := by
      simpa only [Filter.Eventually, dist_zero_right] using (Metric.tendsto_nhds.mp h ε hε)
    obtain ⟨K, hK, hsub⟩ := Filter.mem_cocompact.mp hev
    refine hK.of_isClosed_subset
      (isClosed_le continuous_const hf.norm : IsClosed {x | ε ≤ ‖f x‖}) ?_
    intro x hx
    by_contra hn
    have hxlt : ‖f x‖ < ε := hsub hn
    exact (not_lt_of_ge hx) hxlt
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hc := (h ε hε).compl_mem_cocompact
    change ∀ᶠ x in Filter.cocompact X, dist (f x) 0 < ε
    filter_upwards [hc] with x hx
    have hxne : ¬ ε ≤ ‖f x‖ := hx
    simpa only [dist_zero_right] using (lt_of_not_ge hxne)

/-- Exactly the paper's Cc functions, represented uniquely in the native type. -/
theorem cc_iff (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f : X → 𝕜) :
    (∃! g : CompactlySupportedContinuousMap X 𝕜, (g : X → 𝕜) = f) ↔
      Continuous f ∧ IsCompact (closure {x | f x ≠ 0}) := by
  constructor
  · rintro ⟨g, rfl, _⟩
    exact ⟨g.continuous, g.hasCompactSupport⟩
  · rintro ⟨hf, hc⟩
    let g : CompactlySupportedContinuousMap X 𝕜 := ⟨⟨f, hf⟩, hc⟩
    refine ⟨g, rfl, ?_⟩
    intro h hh
    exact DFunLike.coe_injective hh

/-- Exactly the paper's C0 functions, represented uniquely in the native type. -/
theorem czero_iff (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f : X → 𝕜) :
    (∃! g : ZeroAtInftyContinuousMap X 𝕜, (g : X → 𝕜) = f) ↔
      Continuous f ∧ ∀ ε : ℝ, 0 < ε → IsCompact {x | ε ≤ ‖f x‖} := by
  constructor
  · rintro ⟨g, rfl, _⟩
    exact ⟨g.continuous, (zeroAtInfinity_iff X 𝕜 g g.continuous).mp (zero_at_infty g)⟩
  · rintro ⟨hf, hc⟩
    let g : ZeroAtInftyContinuousMap X 𝕜 :=
      ⟨⟨f, hf⟩, (zeroAtInfinity_iff X 𝕜 f hf).mpr hc⟩
    refine ⟨g, rfl, ?_⟩
    intro h hh
    exact DFunLike.coe_injective hh

end D11.Ch19
