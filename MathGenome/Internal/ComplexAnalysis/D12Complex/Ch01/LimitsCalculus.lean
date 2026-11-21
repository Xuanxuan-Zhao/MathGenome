import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.LimitsCalculus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
Limits and first derivative calculus (paper.tex:165–203).
Only elementary complex topology and derivative calculus are used here;
no analytic regularity of holomorphic functions is needed.
-/

open scoped Topology
open Filter

namespace D12Complex

/-- Complex convergence is precisely convergence of its two real coordinates. -/
theorem complex_tendsto_iff_coordinates (ι : Type) (l : Filter ι) (f : ι → ℂ) (L : ℂ) :
    Tendsto f l (𝓝 L) ↔
      Tendsto (fun z => (f z).re) l (𝓝 L.re) ∧
      Tendsto (fun z => (f z).im) l (𝓝 L.im) := by
  constructor
  · intro h
    exact ⟨Complex.continuous_re.continuousAt.tendsto.comp h,
      Complex.continuous_im.continuousAt.tendsto.comp h⟩
  · rintro ⟨hr, hi⟩
    have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hi).mul_const Complex.I)
    simpa only [Function.comp_def, Complex.re_add_im] using h

/-- Coordinate criterion for the original domain-restricted punctured limit. -/
theorem puncturedLimitWithin_iff_coordinates (s : Set ℂ) (f : ℂ → ℂ) (a L : ℂ) :
    PuncturedLimitWithin s f a L ↔
      Tendsto (fun z => (f z).re) (𝓝[s \ {a}] a) (𝓝 L.re) ∧
      Tendsto (fun z => (f z).im) (𝓝[s \ {a}] a) (𝓝 L.im) := by
  rw [puncturedLimitWithin_iff_tendsto, complex_tendsto_iff_coordinates]

/-- Every sequence is required to stay in the domain and avoid the center.
The converse also covers a center that is not an accumulation point of the domain. -/
theorem puncturedLimitWithin_iff_sequences (s : Set ℂ) (f : ℂ → ℂ) (a L : ℂ) :
    PuncturedLimitWithin s f a L ↔
      ∀ u : ℕ → ℂ, (∀ n, u n ∈ s ∧ u n ≠ a) →
        Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 L) := by
  rw [puncturedLimitWithin_iff_tendsto]
  constructor
  · intro h u hu ht
    exact h.comp (tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hu⟩)
  · intro h
    apply tendsto_iff_seq_tendsto.mpr
    intro u hu
    obtain ⟨ht, hm⟩ := tendsto_nhdsWithin_iff.mp hu
    obtain ⟨N, hN⟩ := eventually_atTop.mp hm
    have hv := h (fun n => u (n + N))
      (fun n => hN (n + N) (Nat.le_add_left N n))
      (ht.comp (tendsto_add_atTop_nat N))
    exact (tendsto_add_atTop_iff_nat N).mp hv

/-- The unrestricted version of the sequence criterion. -/
theorem puncturedLimit_iff_sequences (f : ℂ → ℂ) (a L : ℂ) :
    PuncturedLimit f a L ↔
      ∀ u : ℕ → ℂ, (∀ n, u n ≠ a) →
        Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 L) := by
  simp only [PuncturedLimit, puncturedLimitWithin_iff_sequences, Set.mem_univ, true_and]

/-- Existence of the punctured increment derivative implies continuity including f(a). -/
theorem complexDifferentiableAt_continuous (f : ℂ → ℂ) (a : ℂ)
    (hf : ComplexDifferentiableAt f a) : ContinuousAtPoint f a := by
  exact (continuousAtPoint_iff f a).mpr
    (((complexDifferentiableAt_iff f a).mp hf).continuousAt)

theorem hasComplexDerivativeAt_linear (f g : ℂ → ℂ) (A B a α β : ℂ)
    (hf : HasComplexDerivativeAt f A a) (hg : HasComplexDerivativeAt g B a) :
    HasComplexDerivativeAt (fun z => α * f z + β * g z) (α * A + β * B) a := by
  apply (hasComplexDerivativeAt_iff _ _ _).mpr
  exact (((hasComplexDerivativeAt_iff f A a).mp hf).const_mul α).add
    (((hasComplexDerivativeAt_iff g B a).mp hg).const_mul β)

theorem hasComplexDerivativeAt_mul (f g : ℂ → ℂ) (A B a : ℂ)
    (hf : HasComplexDerivativeAt f A a) (hg : HasComplexDerivativeAt g B a) :
    HasComplexDerivativeAt (fun z => f z * g z) (A * g a + f a * B) a := by
  exact (hasComplexDerivativeAt_iff _ _ _).mpr
    (((hasComplexDerivativeAt_iff f A a).mp hf).mul
      ((hasComplexDerivativeAt_iff g B a).mp hg))

theorem hasComplexDerivativeAt_div (f g : ℂ → ℂ) (A B a : ℂ)
    (hf : HasComplexDerivativeAt f A a) (hg : HasComplexDerivativeAt g B a)
    (hne : g a ≠ 0) :
    HasComplexDerivativeAt (fun z => f z / g z)
      ((A * g a - f a * B) / (g a) ^ 2) a := by
  exact (hasComplexDerivativeAt_iff _ _ _).mpr
    (((hasComplexDerivativeAt_iff f A a).mp hf).div
      ((hasComplexDerivativeAt_iff g B a).mp hg) hne)

theorem hasComplexDerivativeAt_comp (f g : ℂ → ℂ) (A B a : ℂ)
    (hf : HasComplexDerivativeAt f A a) (hg : HasComplexDerivativeAt g B (f a)) :
    HasComplexDerivativeAt (g ∘ f) (B * A) a := by
  exact (hasComplexDerivativeAt_iff _ _ _).mpr
    (((hasComplexDerivativeAt_iff g B (f a)).mp hg).comp a
      ((hasComplexDerivativeAt_iff f A a).mp hf))

/-- Continuity alone supplies the local nonvanishing needed in the quotient argument. -/
theorem complexDifferentiableAt_nonzero_near (g : ℂ → ℂ) (a : ℂ)
    (hg : ComplexDifferentiableAt g a) (hne : g a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z - a‖ < r → g z ≠ 0 := by
  have hc := ((complexDifferentiableAt_iff g a).mp hg).continuousAt
  have hn : ∀ᶠ z in 𝓝 a, g z ≠ 0 := hc.eventually_ne hne
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨r, hr, fun z hz => hb (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)⟩

theorem holomorphicOn_linear (Ω : Set ℂ) (f g : ℂ → ℂ) (α β : ℂ)
    (hf : HolomorphicOn Ω f) (hg : HolomorphicOn Ω g) :
    HolomorphicOn Ω (fun z => α * f z + β * g z) := by
  exact ⟨hf.1, fun a ha => ((hf.2 a ha).const_mul α).add ((hg.2 a ha).const_mul β)⟩

theorem holomorphicOn_mul (Ω : Set ℂ) (f g : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (hg : HolomorphicOn Ω g) :
    HolomorphicOn Ω (fun z => f z * g z) := by
  exact ⟨hf.1, fun a ha => (hf.2 a ha).mul (hg.2 a ha)⟩

theorem holomorphicOn_div (Ω : Set ℂ) (f g : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (hg : HolomorphicOn Ω g) (hne : ∀ z ∈ Ω, g z ≠ 0) :
    HolomorphicOn Ω (fun z => f z / g z) := by
  exact ⟨hf.1, fun a ha => (hf.2 a ha).div (hg.2 a ha) (hne a ha)⟩

/-- The natural domain of a quotient is itself open. -/
theorem holomorphicOn_div_nonzeroSet (Ω : Set ℂ) (f g : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (hg : HolomorphicOn Ω g) :
    HolomorphicOn {z ∈ Ω | g z ≠ 0} (fun z => f z / g z) := by
  have hc : ContinuousOn g Ω := fun a ha => (hg.2 a ha).continuousAt.continuousWithinAt
  have ho : IsOpen {z ∈ Ω | g z ≠ 0} :=
    hc.isOpen_inter_preimage hg.1 (isClosed_singleton (x := (0 : ℂ))).isOpen_compl
  exact ⟨ho, fun a ha => (hf.2 a ha.1).div (hg.2 a ha.1) ha.2⟩

theorem holomorphicOn_div_local (Ω : Set ℂ) (f g : ℂ → ℂ) (a : ℂ)
    (hf : HolomorphicOn Ω f) (hg : HolomorphicOn Ω g) (ha : a ∈ Ω) (hne : g a ≠ 0) :
    ∃ U : Set ℂ, a ∈ U ∧ U ⊆ Ω ∧ (∀ z ∈ U, g z ≠ 0) ∧
      HolomorphicOn U (fun z => f z / g z) := by
  exact ⟨{z ∈ Ω | g z ≠ 0}, ⟨ha, hne⟩, fun _ hz => hz.1,
    fun _ hz => hz.2, holomorphicOn_div_nonzeroSet Ω f g hf hg⟩

theorem holomorphicOn_comp (Ω V : Set ℂ) (f g : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (hg : HolomorphicOn V g) (hm : Set.MapsTo f Ω V) :
    HolomorphicOn Ω (g ∘ f) := by
  exact ⟨hf.1, fun a ha => (hg.2 (f a) (hm ha)).comp a (hf.2 a ha)⟩

end D12Complex
