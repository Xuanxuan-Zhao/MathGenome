import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.IndexOperationsHomotopy
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.WindingIndex
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.HomotopyIntegrals
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Integral-based index operations and homotopy invariance (D12.04.04). -/
noncomputable section
open Set
open scoped unitInterval

namespace D12Complex.IndexOperationsHomotopy

abbrev pathIndex : Specs.D12Complex.Ch04.IndexOperationsHomotopy.pathIndex_type :=
  PiecewiseC1Path.index

/-- Cancellation of coefficients can only remove active traces. -/
theorem add_trace_subset (Γ Δ : IntegralChain) : (Γ + Δ).trace ⊆ Γ.trace ∪ Δ.trace := by
  rintro z ⟨γ, hγ, hz⟩
  by_cases h : Γ γ = 0
  · right
    refine ⟨γ, Finsupp.mem_support_iff.mpr ?_, hz⟩
    simpa [Finsupp.mem_support_iff, h] using hγ
  · exact Or.inl ⟨γ, Finsupp.mem_support_iff.mpr h, hz⟩

theorem neg_trace (Γ : IntegralChain) : (-Γ).trace = Γ.trace := by
  ext z
  simp [IntegralChain.trace, Finsupp.mem_support_iff]

theorem chain_integral_add (Γ Δ : IntegralChain) (f : ℂ → ℂ) :
    (Γ + Δ).integral f = Γ.integral f + Δ.integral f := by
  unfold IntegralChain.integral
  apply Finsupp.sum_add_index'
  · intro γ; simp
  · intro γ m n; simp [add_mul]

theorem chain_integral_neg (Γ : IntegralChain) (f : ℂ → ℂ) :
    (-Γ).integral f = -Γ.integral f := by
  have h := chain_integral_add Γ (-Γ) f
  rw [add_neg_cancel, IntegralChain.zero_integral] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem chain_index_add :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.chain_index_add_type := by
  intro Γ Δ a hΓ hΔ
  have hadd : a ∉ (Γ + Δ).trace := fun h => (add_trace_subset Γ Δ h).elim hΓ hΔ
  rw [IntegralChain.index_eq_integral _ _ hadd, IntegralChain.index_eq_integral _ _ hΓ,
    IntegralChain.index_eq_integral _ _ hΔ, chain_integral_add, mul_add]

theorem chain_index_neg :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.chain_index_neg_type := by
  intro Γ a hΓ
  rw [IntegralChain.index_eq_integral _ _ (by simpa [neg_trace] using hΓ),
    IntegralChain.index_eq_integral _ _ hΓ, chain_integral_neg, mul_neg]

theorem chain_index_sub :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.chain_index_sub_type := by
  intro Γ Δ a hΓ hΔ
  rw [sub_eq_add_neg, chain_index_add Γ (-Δ) a hΓ (by simpa [neg_trace] using hΔ),
    chain_index_neg Δ a hΔ, sub_eq_add_neg]

theorem chain_zero_index :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.chain_zero_index_type :=
  IntegralChain.zero_index

theorem cycle_zero_index :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.cycle_zero_index_type :=
  IntegralCycle.zero_index

@[simp] theorem single_trace (γ : PiecewiseC1Path) :
    IntegralChain.trace (Finsupp.single γ (1 : ℤ)) = γ.trace := by
  ext z
  simp [IntegralChain.trace, Finsupp.support_single]

theorem path_index_eq_integral :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.path_index_eq_integral_type := by
  intro γ a ha
  rw [PiecewiseC1Path.index, IntegralChain.index_eq_integral _ _ (by simpa using ha)]
  simp [IntegralChain.integral]

theorem reciprocal_continuousOn (γ : PiecewiseC1Path) (a : ℂ) (ha : a ∉ γ.trace) :
    ContinuousOn (fun z : ℂ => 1 / (z - a)) γ.trace := by
  simpa using IntegralChain.reciprocal_continuousOn_trace
    (Finsupp.single γ 1) a (by simpa using ha)

theorem path_index_const :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.path_index_const_type := by
  intro u v huv z a ha
  have htrace : a ∉ (PiecewiseC1Path.const u v huv z).trace := by
    simpa [PiecewiseC1Path.trace, PiecewiseC1Path.const, PiecewiseC1Path.path,
      ComplexPath.const_trace] using ha
  rw [path_index_eq_integral _ _ htrace, PiecewiseC1Path.const_integral, mul_zero]

theorem path_index_degenerate :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.path_index_degenerate_type := by
  intro γ a hab ha
  rw [path_index_eq_integral _ _ ha, γ.integral_degenerate hab, mul_zero]

/-- Reversal preserves avoidance, independently of regularity of the kernel. -/
theorem reversal_avoids (γ η : PiecewiseC1Path) (a : ℂ)
    (ha : η.path.a = γ.path.a) (hb : η.path.b = γ.path.b)
    (hEq : EqOn η (fun t => γ (γ.path.a + γ.path.b - t)) (Icc η.path.a η.path.b))
    (hγ : a ∉ γ.trace) : a ∉ η.trace := by
  rintro ⟨t, ht, heq⟩
  apply hγ
  refine ⟨γ.path.a + γ.path.b - t, ?_, ?_⟩
  · rw [ha, hb] at ht
    constructor <;> linarith [ht.1, ht.2]
  · exact (hEq ht).symm.trans heq

theorem path_index_reversal :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.path_index_reversal_type := by
  intro γ η a ha hb hEq hγ
  rw [path_index_eq_integral _ _ (reversal_avoids γ η a ha hb hEq hγ),
    path_index_eq_integral _ _ hγ,
    PiecewiseC1Path.integral_reversal γ η _ ha hb hEq (reciprocal_continuousOn γ a hγ),
    mul_neg]

/-- All points of the concatenation belong to one of the input traces. -/
theorem concatenation_avoids (γ₁ γ₂ η : PiecewiseC1Path) (c p₁ q₁ p₂ q₂ : ℝ) (a : ℂ)
    (_hc : c ∈ Icc η.path.a η.path.b) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (ha₁ : p₁ + q₁ * η.path.a = γ₁.path.a) (hb₁ : p₁ + q₁ * c = γ₁.path.b)
    (ha₂ : p₂ + q₂ * c = γ₂.path.a) (hb₂ : p₂ + q₂ * η.path.b = γ₂.path.b)
    (h₁ : EqOn η (fun t => γ₁ (p₁ + q₁ * t)) (Icc η.path.a c))
    (h₂ : EqOn η (fun t => γ₂ (p₂ + q₂ * t)) (Icc c η.path.b))
    (hγ₁ : a ∉ γ₁.trace) (hγ₂ : a ∉ γ₂.trace) : a ∉ η.trace := by
  rintro ⟨t, ht, heq⟩
  rcases le_total t c with htc | hct
  · apply hγ₁
    refine ⟨p₁ + q₁ * t, ⟨?_, ?_⟩, (h₁ ⟨ht.1, htc⟩).symm.trans heq⟩
    · rw [← ha₁]; exact add_le_add_right (mul_le_mul_of_nonneg_left ht.1 hq₁) _
    · rw [← hb₁]; exact add_le_add_right (mul_le_mul_of_nonneg_left htc hq₁) _
  · apply hγ₂
    refine ⟨p₂ + q₂ * t, ⟨?_, ?_⟩, (h₂ ⟨hct, ht.2⟩).symm.trans heq⟩
    · rw [← ha₂]; exact add_le_add_right (mul_le_mul_of_nonneg_left hct hq₂) _
    · rw [← hb₂]; exact add_le_add_right (mul_le_mul_of_nonneg_left ht.2 hq₂) _

theorem path_index_concatenation :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.path_index_concatenation_type := by
  intro γ₁ γ₂ η c p₁ q₁ p₂ q₂ a hc hq₁ hq₂ hcompat ha₁ hb₁ ha₂ hb₂ h₁ h₂ hγ₁ hγ₂
  rw [path_index_eq_integral _ _
      (concatenation_avoids γ₁ γ₂ η c p₁ q₁ p₂ q₂ a hc hq₁ hq₂ ha₁ hb₁ ha₂ hb₂ h₁ h₂ hγ₁ hγ₂),
    path_index_eq_integral _ _ hγ₁, path_index_eq_integral _ _ hγ₂,
    PiecewiseC1Path.integral_concatenation γ₁ γ₂ η c p₁ q₁ p₂ q₂ _ hc hq₁ hq₂ hcompat
      ha₁ hb₁ ha₂ hb₂ h₁ h₂ (reciprocal_continuousOn γ₁ a hγ₁)
      (reciprocal_continuousOn γ₂ a hγ₂), mul_add]

theorem closed_reversal_exists :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.closed_reversal_exists_type := by
  intro γ a hclosed hγ
  obtain ⟨η, ha, hb, hEq⟩ := γ.exists_reversal
  have hEq' : EqOn η (fun t => γ (γ.path.a + γ.path.b - t)) (Icc η.path.a η.path.b) := by
    simpa [ha, hb] using hEq
  refine ⟨η, ha, hb, hEq, ?_, reversal_avoids γ η a ha hb hEq' hγ,
    path_index_reversal γ η a ha hb hEq' hγ⟩
  change η η.path.b = η η.path.a
  rw [ha, hb, hEq ⟨γ.path.ordered, le_rfl⟩, hEq ⟨le_rfl, γ.path.ordered⟩]
  have hc : γ γ.path.a = γ γ.path.b := hclosed.symm
  simpa only [add_sub_cancel_right, add_sub_cancel_left] using hc

theorem closed_concatenation_exists :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.closed_concatenation_exists_type := by
  intro γ₁ γ₂ a hc₁ hc₂ hcompat hγ₁ hγ₂
  obtain ⟨η, ha, hb, h₁, h₂⟩ := PiecewiseC1Path.exists_concatenation γ₁ γ₂ hcompat
  have hc : (1 : ℝ) ∈ Icc η.path.a η.path.b := by simp [ha, hb]
  have hq₁ := sub_nonneg.mpr γ₁.path.ordered
  have hq₂ := sub_nonneg.mpr γ₂.path.ordered
  have he₁ : γ₁.path.a + (γ₁.path.b - γ₁.path.a) * η.path.a = γ₁.path.a := by rw [ha]; ring
  have he₂ : γ₁.path.a + (γ₁.path.b - γ₁.path.a) * 1 = γ₁.path.b := by ring
  have he₃ : (γ₂.path.a - (γ₂.path.b - γ₂.path.a)) + (γ₂.path.b - γ₂.path.a) * 1 = γ₂.path.a := by ring
  have he₄ : (γ₂.path.a - (γ₂.path.b - γ₂.path.a)) + (γ₂.path.b - γ₂.path.a) * η.path.b = γ₂.path.b := by rw [hb]; ring
  have ht₁ : EqOn η (fun t => γ₁ (γ₁.path.a + (γ₁.path.b - γ₁.path.a) * t)) (Icc η.path.a 1) := by
    simpa [ha] using h₁
  have ht₂ : EqOn η (fun t => γ₂ ((γ₂.path.a - (γ₂.path.b - γ₂.path.a)) +
      (γ₂.path.b - γ₂.path.a) * t)) (Icc 1 η.path.b) := by
    intro t ht
    rw [hb] at ht
    rw [h₂ ht]
    exact congrArg (γ₂ : ℝ → ℂ) (by ring)
  refine ⟨η, ha, hb, h₁, h₂, ?_,
    concatenation_avoids γ₁ γ₂ η 1 _ _ _ _ a hc hq₁ hq₂ he₁ he₂ he₃ he₄ ht₁ ht₂ hγ₁ hγ₂,
    path_index_concatenation γ₁ γ₂ η 1 _ _ _ _ a hc hq₁ hq₂ hcompat he₁ he₂ he₃ he₄ ht₁ ht₂ hγ₁ hγ₂⟩
  change η η.path.b = η η.path.a
  rw [ha, hb, h₂ (by norm_num), h₁ (by norm_num)]
  have hc₁' : γ₁ γ₁.path.b = γ₁ γ₁.path.a := hc₁
  have hc₂' : γ₂ γ₂.path.b = γ₂ γ₂.path.a := hc₂
  change γ₁ γ₁.path.b = γ₂ γ₂.path.a at hcompat
  simpa only [sub_self, mul_zero, add_zero, mul_one, add_sub_cancel, show (2 : ℝ) - 1 = 1 from by norm_num] using
    hc₂'.trans (hcompat.symm.trans hc₁')

theorem free_loop_index :
    Specs.D12Complex.Ch04.IndexOperationsHomotopy.free_loop_index_type := by
  intro γ₀ γ₁ a hγ₀ hγ₁ hc₀ hc₁ H hH hb ht hs
  have hf : HolomorphicOn ({a}ᶜ : Set ℂ) (fun z => 1 / (z - a)) := by
    refine ⟨isClosed_singleton.isOpen_compl, ?_⟩
    intro z hz
    exact (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const a)
      (sub_ne_zero.mpr (by simpa using hz))
  have htrace (γ : PiecewiseC1Path) (hγ : a ∉ γ.trace) : γ.trace ⊆ ({a}ᶜ : Set ℂ) := by
    intro z hz
    exact fun h => hγ (h ▸ hz)
  rw [path_index_eq_integral _ _ hγ₀, path_index_eq_integral _ _ hγ₁,
    HomotopyIntegrals.free_loop_integral _ _ hf γ₀ γ₁ (htrace γ₀ hγ₀) (htrace γ₁ hγ₁)
      hc₀ hc₁ H (by simpa using hH) hb ht hs]

end D12Complex.IndexOperationsHomotopy
