import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.CauchyMeasureComplete
import MathGenome.Internal.RealAnalysis.D11.Ch07.SubsequenceUniqueness
import MathGenome.Internal.RealAnalysis.D11.Ch01.BorelCantelli
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
Completeness for global convergence in measure (paper.tex:2204–2241).

Geometric exceptional jumps and Borel–Cantelli give a subsequence which is
pointwise Cauchy off a measurable null envelope. Resetting the subsequence
to zero there gives an everywhere convergent measurable sequence, hence a
finite measurable limit on the original sigma-algebra. For the full sequence,
continuity from below transfers the Cauchy deviation bounds through the a.e.
subsequence limit. Uniqueness is the upstream ordinary-a.e. uniqueness theorem.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace D11.Ch07.CauchyMeasureComplete
open D11.Ch07.ConvergenceDefinitions
open D11.Ch07.SubsequenceUniqueness
open D11.Ch04.AeCommonException

variable {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]

/-- Extract successive differences with summable deviation measures. -/
theorem exists_fast_subsequence (μ : Measure X) (f : ℕ → X → E)
    (hc : cauchyInMeasure μ f) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ j, μ (deviationSet (f (ns (j + 1))) (f (ns j)) ((1 / 2 : ℝ) ^ j)) <
        ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
  have hp : ∀ j : ℕ, 0 < (1 / 2 : ℝ) ^ j := fun _ => pow_pos (by norm_num) _
  choose K hK using fun j => hc _ (hp j) _ (hp j)
  let ns : ℕ → ℕ := fun j => Nat.rec (K 0) (fun j prev => max (K (j + 1)) (prev + 1)) j
  have hstep : ∀ j, ns (j + 1) = max (K (j + 1)) (ns j + 1) := fun _ => rfl
  have hmono : StrictMono ns := strictMono_nat_of_lt_succ fun j => by
    rw [hstep]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hge : ∀ j, K j ≤ ns j := by
    intro j
    cases j with
    | zero => exact le_rfl
    | succ j => exact le_max_left _ _
  exact ⟨ns, hmono, fun j => hK j _ (hge j) _ ((hge j).trans (hmono.monotone (Nat.le_succ j)))⟩

/-- Summable exceptional jumps produce a measurable, everywhere finite version. -/
theorem exists_measurable_ae_limit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure X) (f : ℕ → X → E) (hf : ∀ n, Measurable (f n))
    (hc : cauchyInMeasure μ f) :
    ∃ (g : X → E) (N : Set X) (ns : ℕ → ℕ),
      Measurable g ∧ MeasurableSet N ∧ μ N = 0 ∧
      (∀ x ∈ N, g x = 0) ∧ StrictMono ns ∧
      (∀ x ∉ N, Tendsto (fun j => f (ns j) x) atTop (𝓝 (g x))) := by
  classical
  obtain ⟨ns, hns, hbound⟩ := exists_fast_subsequence μ f hc
  let B j := deviationSet (f (ns (j + 1))) (f (ns j)) ((1 / 2 : ℝ) ^ j)
  have hsum : (∑' j, μ (B j)) ≠ ∞ :=
    ne_top_of_le_ne_top summable_geometric_two.tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum (fun j => (hbound j).le))
  obtain ⟨N, ⟨hN, hμN⟩, hgood⟩ := (almostEverywhere_iff_native μ _).mpr
    (ae_eventually_notMem hsum)
  let w (j : ℕ) (x : X) : E := if x ∈ N then 0 else f (ns j) x
  have hw : ∀ x, CauchySeq (fun j => w j x) := by
    intro x
    by_cases hx : x ∈ N
    · simpa only [w, ite_eq_left hx] using cauchySeq_const (0 : E)
    · apply cauchySeq_of_summable_dist
      apply summable_geometric_two.of_norm_bounded_eventually_nat
      filter_upwards [hgood x hx] with j hj
      have hj' : ‖f (ns (j + 1)) x - f (ns j) x‖ ≤ (1 / 2 : ℝ) ^ j :=
        le_of_not_gt hj
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
      simpa only [w, ite_eq_right hx, dist_eq_norm, norm_sub_rev] using hj'
  let g (x : X) := limUnder atTop (fun j => w j x)
  have hlim : ∀ x, Tendsto (fun j => w j x) atTop (𝓝 (g x)) :=
    fun x => (hw x).tendsto_limUnder
  refine ⟨g, N, ns, ?_, hN, hμN, ?_, hns, ?_⟩
  · apply measurable_of_tendsto_metrizable _ (tendsto_pi_nhds.mpr hlim)
    intro j
    exact measurable_const.piecewise hN (hf (ns j))
  · intro x hx
    exact tendsto_nhds_unique (hlim x) (by simpa only [w, ite_eq_left hx] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 0)))
  · intro x hx
    simpa only [w, ite_eq_right hx] using hlim x

/-- An eventual pointwise membership assertion transfers an eventual uniform
bound on set measures to the limiting set. This is continuity from below. -/
theorem measure_le_of_ae_eventually_mem (μ : Measure X) (A : Set X)
    (S : ℕ → Set X) (c : ℝ≥0∞)
    (hA : ∀ᵐ x ∂μ, x ∈ A → ∀ᶠ j in atTop, x ∈ S j)
    (hS : ∀ᶠ j in atTop, μ (S j) ≤ c) : μ A ≤ c := by
  let T (k : ℕ) : Set X := ⋂ j ≥ k, S j
  have hmono : Monotone T := by
    intro k l hkl x hx
    simp only [T, mem_iInter] at hx ⊢
    intro j hj
    exact hx j (hkl.trans hj)
  have hsub : ∀ᵐ x ∂μ, x ∈ A → x ∈ ⋃ k, T k := by
    filter_upwards [hA] with x hx hxA
    obtain ⟨k, hk⟩ := eventually_atTop.mp (hx hxA)
    exact mem_iUnion.mpr ⟨k, by simpa only [T, mem_iInter] using hk⟩
  refine (measure_mono_ae hsub).trans ?_
  rw [hmono.measure_iUnion]
  apply iSup_le
  intro k
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hS
  refine (measure_mono ?_).trans (hJ (max k J) (le_max_right _ _))
  exact fun x hx => (mem_iInter.mp (mem_iInter.mp hx (max k J))) (le_max_left _ _)

/-- A Cauchy sequence with an a.e. convergent subsequence converges globally
in measure, regardless of the total mass. -/
theorem inMeasure_of_cauchy_of_ae_subsequence (μ : Measure X)
    (f : ℕ → X → E) (g : X → E) (hc : cauchyInMeasure μ f)
    (ns : ℕ → ℕ) (hns : StrictMono ns)
    (hlim : aeConverges μ (fun j => f (ns j)) g) : inMeasureConverges μ f g := by
  intro ε hε
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  obtain ⟨c, hc0, hcδ⟩ := exists_between hδ
  have hctop : c ≠ ∞ := ne_top_of_lt hcδ
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc0.ne' hctop
  obtain ⟨K, hK⟩ := hc (ε / 2) (half_pos hε) c.toReal hcr
  refine ⟨K, fun n hn => le_trans ?_ hcδ.le⟩
  apply measure_le_of_ae_eventually_mem μ (deviationSet (f n) g ε)
    (fun j => deviationSet (f n) (f (ns j)) (ε / 2)) c
  · filter_upwards [(almostEverywhere_iff_native μ _).mp hlim] with x hx hxA
    have hh : ε / 2 < ‖f n x - g x‖ := (half_lt_self hε).trans hxA
    exact ((tendsto_const_nhds.sub hx).norm).eventually (lt_mem_nhds hh)
  · filter_upwards [eventually_ge_atTop K] with j hj
    have h := hK (ns j) (hj.trans (hns.id_le j)) n hn
    simpa only [ENNReal.ofReal_toReal hctop] using h.le

/-- Completeness for finite real or complex measurable scalar functions,
with a zero-on-null measurable representative and ordinary a.e. uniqueness. -/
theorem complete_in_measure : Specs.D11.Ch07.CauchyMeasureComplete.complete_in_measure := by
  intro X 𝕜 m inst m𝕜 b𝕜 μ f hf hc
  obtain ⟨g, N, ns, hg, hN, hμN, hg0, hns, hlim⟩ :=
    exists_measurable_ae_limit μ f hf hc
  have hae : aeConverges μ (fun j => f (ns j)) g := ⟨N, ⟨hN, hμN⟩, hlim⟩
  have hconv := inMeasure_of_cauchy_of_ae_subsequence μ f g hc ns hns hae
  exact ⟨g, N, ns, hg, hN, hμN, hg0, hns, hlim, hae, hconv,
    fun h hh => limit_unique μ f g h hconv hh⟩

end D11.Ch07.CauchyMeasureComplete
