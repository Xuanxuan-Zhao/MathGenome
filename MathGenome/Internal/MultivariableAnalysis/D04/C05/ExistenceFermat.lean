import MathGenome.Internal.MultivariableAnalysis.D04.C05.ExtremaInterfaces
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CompactContinuity
import MathGenome.Internal.MultivariableAnalysis.D04.C02.ChainRule
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ExistenceFermat
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Compact existence and first-order necessity, d04:05:existence-fermat.
We pull the relative extremum back along a feasible curve and apply the
scalar Fermat theorem or its positive-ray inequality after the chain rule.
All dimensions, including zero, and arbitrary feasible sets are allowed. -/
noncomputable section
open Set Filter Topology
namespace D04

theorem compact_global_extrema {n : ℕ} (S : Set (E n)) (f : E n → ℝ)
    (hS : Compact S) (hne : S.Nonempty) (hf : ContinuousOn f S) :
    ∃ a b : E n, GlobalMinimumOn S f a ∧ GlobalMaximumOn S f b := by
  have hK := (compact_iff_isCompact S).mp hS
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hf
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hf
  exact ⟨a, b, ⟨ha, hmin⟩, ⟨hb, hmax⟩⟩

theorem compact_global_extrema_subtype {n : ℕ} (S : Set (E n)) (f : S → ℝ)
    (hS : Compact S) (hne : S.Nonempty) (hf : Continuous f) :
    ∃ a b : S, ∀ x : S, f a ≤ f x ∧ f x ≤ f b := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp ((compact_iff_isCompact S).mp hS)
  obtain ⟨a, ha⟩ := hne
  have hu : (univ : Set S).Nonempty := ⟨⟨a, ha⟩, mem_univ _⟩
  obtain ⟨b, _, hmin⟩ := isCompact_univ.exists_isMinOn hu hf.continuousOn
  obtain ⟨c, _, hmax⟩ := isCompact_univ.exists_isMaxOn hu hf.continuousOn
  exact ⟨b, c, fun x => ⟨hmin (mem_univ x), hmax (mem_univ x)⟩⟩

theorem fermat_minimum {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hf : TotalDifferentiableAt U f a) (hm : LocalMinimumOn U f a) :
    totalDerivative f a = 0 := by
  obtain ⟨A, hA⟩ := hf
  have hmin := ((localMinimumOn_iff U f a).mp hm).2.isLocalMin (hA.1.mem_nhds hA.2.1)
  rw [totalDerivative_eq U f A a hA]
  exact hmin.hasFDerivAt_eq_zero
    ((hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA)

theorem fermat_maximum {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hf : TotalDifferentiableAt U f a) (hm : LocalMaximumOn U f a) :
    totalDerivative f a = 0 := by
  obtain ⟨A, hA⟩ := hf
  have hmax := ((localMaximumOn_iff U f a).mp hm).2.isLocalMax (hA.1.mem_nhds hA.2.1)
  rw [totalDerivative_eq U f A a hA]
  exact hmax.hasFDerivAt_eq_zero
    ((hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA)

theorem feasible_curve_minimum {n : ℕ} (U S : Set (E n)) (f : E n → ℝ) (a : E n)
    (γ : ℝ → E n) (v : E n) (hf : TotalDifferentiableAt U f a)
    (hm : LocalMinimumOn S f a) (h0 : γ 0 = a) (hγ : HasDerivAt γ v 0)
    (hS : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S) : totalDerivative f a v = 0 := by
  obtain ⟨A, hA⟩ := hf
  have ht : Tendsto γ (𝓝 0) (𝓝[S] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa [h0] using hγ.continuousAt.tendsto, hS⟩
  have hmin : IsLocalMin (f ∘ γ) 0 := by
    simpa [IsLocalMin, IsMinFilter, Function.comp_def, h0] using
      ht.eventually ((localMinimumOn_iff S f a).mp hm).2
  rw [totalDerivative_eq U f A a hA]
  exact hmin.hasDerivAt_eq_zero
    (((hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA).comp_hasDerivAt_of_eq 0 hγ h0.symm)

theorem feasible_curve_maximum {n : ℕ} (U S : Set (E n)) (f : E n → ℝ) (a : E n)
    (γ : ℝ → E n) (v : E n) (hf : TotalDifferentiableAt U f a)
    (hm : LocalMaximumOn S f a) (h0 : γ 0 = a) (hγ : HasDerivAt γ v 0)
    (hS : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S) : totalDerivative f a v = 0 := by
  obtain ⟨A, hA⟩ := hf
  have ht : Tendsto γ (𝓝 0) (𝓝[S] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa [h0] using hγ.continuousAt.tendsto, hS⟩
  have hmax : IsLocalMax (f ∘ γ) 0 := by
    simpa [IsLocalMax, IsMaxFilter, Function.comp_def, h0] using
      ht.eventually ((localMaximumOn_iff S f a).mp hm).2
  rw [totalDerivative_eq U f A a hA]
  exact hmax.hasDerivAt_eq_zero
    (((hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA).comp_hasDerivAt_of_eq 0 hγ h0.symm)

private theorem one_mem_right_tangent : (1 : ℝ) ∈ posTangentConeAt (Ici 0) 0 := by
  apply mem_posTangentConeAt_of_frequently_mem
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi 0 := self_mem_nhdsWithin
  exact (ht.mono fun t ht => by simpa using ht.le).frequently

theorem feasible_right_curve_minimum {n : ℕ} (U S : Set (E n)) (f : E n → ℝ)
    (a : E n) (γ : ℝ → E n) (v : E n) (hf : TotalDifferentiableAt U f a)
    (hm : LocalMinimumOn S f a) (h0 : γ 0 = a)
    (hγ : HasDerivWithinAt γ v (Ici 0) 0)
    (hS : ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, γ t ∈ S) : 0 ≤ totalDerivative f a v := by
  obtain ⟨A, hA⟩ := hf
  have ht : Tendsto γ (𝓝[Ici 0] 0) (𝓝[S] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa [h0] using hγ.continuousWithinAt.tendsto, hS⟩
  have hmin : IsLocalMinOn (f ∘ γ) (Ici 0) 0 := by
    simpa [IsLocalMinOn, IsMinFilter, Function.comp_def, h0] using
      ht.eventually ((localMinimumOn_iff S f a).mp hm).2
  have hd : HasDerivWithinAt (f ∘ γ) (A v) (Ici 0) 0 :=
    ((hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA).comp_hasDerivWithinAt_of_eq 0 hγ h0.symm
  rw [totalDerivative_eq U f A a hA]
  simpa using hmin.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt one_mem_right_tangent

theorem feasible_right_curve_maximum {n : ℕ} (U S : Set (E n)) (f : E n → ℝ)
    (a : E n) (γ : ℝ → E n) (v : E n) (hf : TotalDifferentiableAt U f a)
    (hm : LocalMaximumOn S f a) (h0 : γ 0 = a)
    (hγ : HasDerivWithinAt γ v (Ici 0) 0)
    (hS : ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, γ t ∈ S) : totalDerivative f a v ≤ 0 := by
  obtain ⟨A, hA⟩ := hf
  have ht : Tendsto γ (𝓝[Ici 0] 0) (𝓝[S] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa [h0] using hγ.continuousWithinAt.tendsto, hS⟩
  have hmax : IsLocalMaxOn (f ∘ γ) (Ici 0) 0 := by
    simpa [IsLocalMaxOn, IsMaxFilter, Function.comp_def, h0] using
      ht.eventually ((localMaximumOn_iff S f a).mp hm).2
  have hd : HasDerivWithinAt (f ∘ γ) (A v) (Ici 0) 0 :=
    ((hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA).comp_hasDerivWithinAt_of_eq 0 hγ h0.symm
  rw [totalDerivative_eq U f A a hA]
  simpa using hmax.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt one_mem_right_tangent

end D04
