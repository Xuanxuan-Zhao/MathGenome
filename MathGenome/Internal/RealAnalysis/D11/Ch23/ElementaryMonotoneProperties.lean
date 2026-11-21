import MathGenome.Internal.RealAnalysis.D11.Ch23.ElementaryIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.ElementaryMonotoneProperties
import Mathlib.Topology.Algebra.Ring.Real

/-! Monotone convergence and extended nonnegative series for an elementary
integral, before any representing measure is constructed. -/

universe u
open Filter Topology
open scoped BigOperators

namespace D11.Ch23

namespace IsElementaryIntegral

variable {X : Type u} {V : Submodule ℝ (X → ℝ)} {L : V →ₗ[ℝ] ℝ}

/-- Positivity and linearity give pointwise order preservation. -/
theorem mono (hL : IsElementaryIntegral V L) {f g : V}
    (hfg : ∀ x, (f : X → ℝ) x ≤ (g : X → ℝ) x) : L f ≤ L g := by
  have h := hL.nonneg (g - f) (fun x => sub_nonneg.mpr (hfg x))
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- Order continuity on the differences gives increasing convergence.
This stronger helper needs neither positivity of the sequence nor lattice closure. -/
theorem monotone_convergence (hL : IsElementaryIntegral V L)
    (f : V) (s : ℕ → V)
    (hmono : ∀ x, Monotone (fun n => (s n : X → ℝ) x))
    (hlim : ∀ x, Tendsto (fun n => (s n : X → ℝ) x) atTop (𝓝 ((f : X → ℝ) x))) :
    Monotone (fun n => L (s n)) ∧ Tendsto (fun n => L (s n)) atTop (𝓝 (L f)) := by
  refine ⟨fun i j hij => hL.mono (fun x => hmono x hij), ?_⟩
  have hzero := hL.tendsto_zero (fun n => f - s n)
    (fun x i j hij => sub_le_sub_left (hmono x hij) _)
    (fun x => by simpa using (tendsto_const_nhds (x := (f : X → ℝ) x)).sub (hlim x))
  have h := (tendsto_const_nhds (x := L f)).sub hzero
  simpa only [map_sub, sub_sub_cancel, sub_zero] using h

end IsElementaryIntegral

/-- The first assertion of the source lemma, including monotonicity of L(s n). -/
theorem elementary_monotone_convergence {X : Type u} (V : Submodule ℝ (X → ℝ))
    (_hV : IsVectorLattice V) (L : V →ₗ[ℝ] ℝ) (hL : IsElementaryIntegral V L)
    (f : V) (s : ℕ → V) (_hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (_hs : ∀ n x, 0 ≤ (s n : X → ℝ) x)
    (hmono : ∀ x, Monotone (fun n => (s n : X → ℝ) x))
    (hlim : ∀ x, Tendsto (fun n => (s n : X → ℝ) x) atTop (𝓝 ((f : X → ℝ) x))) :
    Monotone (fun n => L (s n)) ∧ Tendsto (fun n => L (s n)) atTop (𝓝 (L f)) :=
  hL.monotone_convergence f s hmono hlim

/-- Real partial sums, evaluated at a point, agree with partial sums of values. -/
private lemma partial_sum_apply {X : Type u} {V : Submodule ℝ (X → ℝ)}
    (s : ℕ → V) (n : ℕ) (x : X) :
    ((∑ i ∈ Finset.range n, s i : V) : X → ℝ) x =
      ∑ i ∈ Finset.range n, (s i : X → ℝ) x := by
  simp

/-- A nonnegative series dominating a finite number has truncations converging
to that number, even when the series diverges to infinity. -/
private lemma tendsto_min_partial_sum (a : ℝ) (ha : 0 ≤ a) (b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hab : ENNReal.ofReal a ≤ ∑' n, ENNReal.ofReal (b n)) :
    Tendsto (fun n => min a (∑ i ∈ Finset.range n, b i)) atTop (𝓝 a) := by
  have h := (tendsto_const_nhds (x := ENNReal.ofReal a)).min (ENNReal.tendsto_nat_tsum (fun n => ENNReal.ofReal (b n)))
  have h' : Tendsto (fun n => min (ENNReal.ofReal a)
      (∑ i ∈ Finset.range n, ENNReal.ofReal (b i))) atTop (𝓝 (ENNReal.ofReal a)) := by
    simpa only [min_eq_left hab] using h
  have hr := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h'
  simpa only [Function.comp_def, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hb i),
    ← ENNReal.ofReal_min, ENNReal.toReal_ofReal (le_min ha
      (Finset.sum_nonneg (fun i _ => hb i))), ENNReal.toReal_ofReal ha] using hr

/-- The comparison assertion, allowing infinite pointwise sums and infinite sums
of integral values. Lattice closure supplies f min (finite partial sum). -/
theorem elementary_series_comparison {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (L : V →ₗ[ℝ] ℝ) (hL : IsElementaryIntegral V L)
    (f : V) (s : ℕ → V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (hs : ∀ n x, 0 ≤ (s n : X → ℝ) x)
    (hdom : ∀ x, ENNReal.ofReal ((f : X → ℝ) x) ≤
      ∑' n, ENNReal.ofReal ((s n : X → ℝ) x)) :
    ENNReal.ofReal (L f) ≤ ∑' n, ENNReal.ofReal (L (s n)) := by
  let p : ℕ → V := fun n => ∑ i ∈ Finset.range n, s i
  let g : ℕ → V := fun n =>
    ⟨fun x => min ((f : X → ℝ) x) ((p n : X → ℝ) x),
      hV.min_mem f.property (p n).property⟩
  have hp (x : X) : Monotone (fun n => (p n : X → ℝ) x) := by
    intro i j hij
    simp only [p, partial_sum_apply]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) (fun i _ _ => hs i x)
  have hgmono (x : X) : Monotone (fun n => (g n : X → ℝ) x) := by
    intro i j hij
    exact min_le_min_left _ (hp x hij)
  have hglim (x : X) : Tendsto (fun n => (g n : X → ℝ) x) atTop
      (𝓝 ((f : X → ℝ) x)) := by
    simpa only [g, p, partial_sum_apply] using
      tendsto_min_partial_sum _ (hf x) (fun n => (s n : X → ℝ) x) (fun n => hs n x) (hdom x)
  have hlim := (hL.monotone_convergence f g hgmono hglim).2
  have hbound (n : ℕ) : ENNReal.ofReal (L (g n)) ≤ ∑' i, ENNReal.ofReal (L (s i)) := by
    calc
      ENNReal.ofReal (L (g n)) ≤ ENNReal.ofReal (L (p n)) :=
        ENNReal.ofReal_le_ofReal (hL.mono (fun x => min_le_right _ _))
      _ = ∑ i ∈ Finset.range n, ENNReal.ofReal (L (s i)) := by
        simp only [p, map_sum]
        exact ENNReal.ofReal_sum_of_nonneg (fun i _ => hL.nonneg (s i) (hs i))
      _ ≤ ∑' i, ENNReal.ofReal (L (s i)) := ENNReal.sum_le_tsum _
  exact le_of_tendsto' (ENNReal.continuous_ofReal.tendsto (L f) |>.comp hlim) hbound

/-- The equality assertion, in the same extended-series convention as comparison. -/
theorem elementary_series_equality {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (L : V →ₗ[ℝ] ℝ) (hL : IsElementaryIntegral V L)
    (f : V) (s : ℕ → V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (hs : ∀ n x, 0 ≤ (s n : X → ℝ) x)
    (heq : ∀ x, ENNReal.ofReal ((f : X → ℝ) x) =
      ∑' n, ENNReal.ofReal ((s n : X → ℝ) x)) :
    ENNReal.ofReal (L f) = ∑' n, ENNReal.ofReal (L (s n)) := by
  apply le_antisymm
  · exact elementary_series_comparison V hV L hL f s hf hs (fun x => (heq x).le)
  · rw [ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro n
    have hp : ∀ x, ((∑ i ∈ Finset.range n, s i : V) : X → ℝ) x ≤ (f : X → ℝ) x := by
      intro x
      apply (ENNReal.ofReal_le_ofReal_iff (hf x)).mp
      rw [partial_sum_apply, ENNReal.ofReal_sum_of_nonneg (fun i _ => hs i x), heq x]
      exact ENNReal.sum_le_tsum _
    calc
      ∑ i ∈ Finset.range n, ENNReal.ofReal (L (s i)) =
          ENNReal.ofReal (L (∑ i ∈ Finset.range n, s i)) := by
        rw [map_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => hL.nonneg (s i) (hs i))]
      _ ≤ ENNReal.ofReal (L f) := ENNReal.ofReal_le_ofReal (hL.mono hp)

end D11.Ch23
