import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Equicontinuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Compactness.LocallyCompact

/-!
K03.16.ascoli_hypotheses, paper.tex:3856–3862.
The two real sequences and their canonical complex embeddings are scalar
counterexamples in the manuscript's continuous-function spaces. Natural index n represents positive index n+1.
Subsequences use arbitrary strictly increasing maps ℕ → ℕ; their proposed
limits are arbitrary finite scalar-valued functions, with no assumed continuity.
The discrete example uses a type synonym of ℕ with exactly the specified 0/1
distance, so it does not change the usual metric on ℕ elsewhere.
-/
namespace Specs.SingleVariableAnalysis.Ch16.AscoliHypotheses

open scoped Topology

noncomputable def constants (K : Set ℝ) (n : ℕ) : C(K, ℝ) :=
  ContinuousMap.const K (n + 1 : ℝ)

abbrev sineDomain : Set ℝ := Set.Icc 0 (2 * Real.pi)

noncomputable def sines (n : ℕ) : C(sineDomain, ℝ) :=
  ⟨fun x => Real.sin ((n + 1 : ℝ) * x.val),
    Real.continuous_sin.comp (continuous_const.mul continuous_subtype_val)⟩

noncomputable def peak (n : ℕ) : ℝ := Real.pi / (2 * (n + 1 : ℝ))

def constantsEquicontinuous : Prop :=
  ∀ (K : Set ℝ), IsCompact K → K.Nonempty →
    Equicontinuity.pointwiseEquicontinuousFamilyValue K (Set.range (constants K)) ∧
    Equicontinuity.uniformlyEquicontinuousFamilyValue K (Set.range (constants K))

def constantsUnbounded : Prop :=
  ∀ (K : Set ℝ), IsCompact K → K.Nonempty →
    (∀ x : K, ∀ M : ℝ, ∃ n : ℕ, M < |constants K n x|) ∧
    ¬ Equicontinuity.pointwiseBoundedFamilyValue K (Set.range (constants K)) ∧
    ¬ Equicontinuity.uniformlyBoundedFamilyValue K (Set.range (constants K))

def constantsNoUniformSubsequence : Prop :=
  ∀ (K : Set ℝ), IsCompact K → K.Nonempty →
    ∀ (k : ℕ → ℕ), StrictMono k → ∀ f : K → ℝ,
      ¬ Ch12.Uniform.realUniformConvergesValue (fun j x => constants K (k j) x) f

def sinePeaks : Prop :=
  (∀ n : ℕ, peak n ∈ sineDomain ∧
    Real.sin ((n + 1 : ℝ) * peak n) = 1 ∧ Real.sin ((n + 1 : ℝ) * 0) = 0) ∧
    Filter.Tendsto peak Filter.atTop (𝓝 0)

def sinesBounded : Prop :=
  (∀ n : ℕ, ∀ x : sineDomain, |sines n x| ≤ 1) ∧
    Equicontinuity.uniformlyBoundedFamilyValue sineDomain (Set.range sines)

def sinesNotEquicontinuous : Prop :=
  (¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ y : sineDomain, |y.val| < δ → ∀ n : ℕ, |sines n y - Real.sin 0| < ε)) ∧
    ¬ Equicontinuity.pointwiseEquicontinuousFamilyValue sineDomain (Set.range sines)

def sinesNoUniformSubsequence : Prop :=
  ∀ (k : ℕ → ℕ), StrictMono k → ∀ f : sineDomain → ℝ,
    ¬ Ch12.Uniform.realUniformConvergesValue (fun j x => sines (k j) x) f

/-- The same constants viewed in the other permitted scalar field. -/
noncomputable def complexConstants (K : Set ℝ) (n : ℕ) : C(K, ℂ) :=
  ⟨fun x => (constants K n x : ℂ),
    Complex.continuous_ofReal.comp (constants K n).continuous⟩

/-- The same sine sequence viewed in the other permitted scalar field. -/
noncomputable def complexSines (n : ℕ) : C(sineDomain, ℂ) :=
  ⟨fun x => (sines n x : ℂ),
    Complex.continuous_ofReal.comp (sines n).continuous⟩

def complexConstantsCounterexample : Prop :=
  ∀ (K : Set ℝ), IsCompact K → K.Nonempty →
    Equicontinuity.pointwiseEquicontinuousFamilyValue K (Set.range (complexConstants K)) ∧
    Equicontinuity.uniformlyEquicontinuousFamilyValue K (Set.range (complexConstants K)) ∧
    (∀ x : K, ∀ M : ℝ, ∃ n : ℕ, M < ‖complexConstants K n x‖) ∧
    ¬ Equicontinuity.pointwiseBoundedFamilyValue K (Set.range (complexConstants K)) ∧
    ¬ Equicontinuity.uniformlyBoundedFamilyValue K (Set.range (complexConstants K)) ∧
    (∀ (k : ℕ → ℕ), StrictMono k → ∀ f : K → ℂ,
      ¬ Ch12.Uniform.complexUniformConvergesValue (fun j x => complexConstants K (k j) x) f)

def complexSinesCounterexample : Prop :=
  (∀ n : ℕ, ∀ x : sineDomain, ‖complexSines n x‖ ≤ 1) ∧
    Equicontinuity.uniformlyBoundedFamilyValue sineDomain (Set.range complexSines) ∧
    (¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : sineDomain, |y.val| < δ → ∀ n : ℕ, ‖complexSines n y‖ < ε)) ∧
    ¬ Equicontinuity.pointwiseEquicontinuousFamilyValue sineDomain (Set.range complexSines) ∧
    (∀ (k : ℕ → ℕ), StrictMono k → ∀ f : sineDomain → ℂ,
      ¬ Ch12.Uniform.complexUniformConvergesValue (fun j x => complexSines (k j) x) f)

/-- A type synonym, with the same elements as ℕ, to isolate its new metric. -/
def DiscreteNat : Type := ℕ

instance : DecidableEq DiscreteNat := inferInstanceAs (DecidableEq ℕ)
instance : Infinite DiscreteNat := inferInstanceAs (Infinite ℕ)

/-- The exact distance from the source remark; all metric axioms are proved. -/
instance discreteNatMetric : MetricSpace DiscreteNat where
  dist m n := if m = n then 0 else 1
  dist_self m := by simp
  dist_comm m n := by simp [eq_comm]
  dist_triangle m n p := by
    by_cases h : m = p
    · subst p; simp; positivity
    · by_cases hmn : m = n
      · subst n; simp
      · by_cases hnp : n = p
        · subst p; simp
        · simp [h, hmn, hnp]
  eq_of_dist_eq_zero := by
    intro m n h
    by_contra hne
    simp [hne] at h

def discreteCounterexample : Prop :=
  (∀ m n : DiscreteNat, dist m n = if m = n then 0 else 1) ∧
    (∀ n : DiscreteNat, IsCompact ({n} : Set DiscreteNat) ∧ ({n} : Set DiscreteNat) ∈ 𝓝 n) ∧
    LocallyCompactSpace DiscreteNat ∧ Bornology.IsBounded (Set.univ : Set DiscreteNat) ∧
    (∀ t : Finset DiscreteNat, ∃ n : DiscreteNat, ∀ m ∈ t, n ∉ Metric.ball m (1 / 2)) ∧
    ¬ TotallyBounded (Set.univ : Set DiscreteNat)

end Specs.SingleVariableAnalysis.Ch16.AscoliHypotheses
