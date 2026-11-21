import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.HittingProbability
import Mathlib.Basic.Real.ENatENNReal

open MeasureTheory
open scoped ENNReal

namespace P207.Walk
noncomputable section

/-- States are exactly the integers from zero through `N`, inclusive. -/
abbrev RuinState (N : ℕ) := Fin (N + 1)

def ruinRight {N : ℕ} (i : RuinState N) : RuinState N :=
  ⟨min (i.val + 1) N, Nat.lt_succ_of_le (min_le_right _ _)⟩

def ruinLeft {N : ℕ} (i : RuinState N) : RuinState N :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- The independent move law: true is right, false is left. -/
def ruinCoin (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add hp.le (sub_nonneg.mpr hp1.le)]
    simp)

/-- Nearest-neighbor kernel, with both endpoints absorbing. -/
def ruinKernel (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Markov.StochasticMatrix (RuinState N) :=
  fun i => if i.val = 0 ∨ i.val = N then PMF.pure i
    else (ruinCoin p hp hp1).map (fun b => if b then ruinRight i else ruinLeft i)

def ruinBoundary (N : ℕ) : Set (RuinState N) := {i | i.val = 0 ∨ i.val = N}

/-- The shared first-entrance time; time zero and infinity are retained. -/
def ruinTime (N : ℕ) : (ℕ → RuinState N) → WithTop ℕ :=
  Markov.hittingTime (ruinBoundary N)

namespace RuinAbsorptionSpec

def kernelType := (N : ℕ) → (p : ℝ) → (hp : 0 < p) → (hp1 : p < 1) →
  Markov.StochasticMatrix (RuinState N)
def kernelValue : kernelType := ruinKernel

def timeType := (N : ℕ) → (ℕ → RuinState N) → WithTop ℕ
def timeValue : timeType := ruinTime

/-- An exact mass formula certifies the intended nearest-neighbor kernel. -/
def kernel_boundary : Prop := ∀ N p hp hp1 (i : RuinState N),
  i ∈ ruinBoundary N → ruinKernel N p hp hp1 i = PMF.pure i

def kernel_interior : Prop := ∀ N p hp hp1 (i j : RuinState N),
  i ∉ ruinBoundary N →
  ruinKernel N p hp hp1 i j =
    (if j = ruinRight i then ENNReal.ofReal p else 0) +
    (if j = ruinLeft i then ENNReal.ofReal (1 - p) else 0)

/-- Every initial state is covered, including both endpoints and `N = 1`. -/
def absorption_ae_finite : Prop := ∀ (N : ℕ), 1 ≤ N →
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : RuinState N),
    ∀ᵐ ω ∂Markov.statePathLaw (ruinKernel N p hp hp1) i, ruinTime N ω < ⊤

/-- Extended expectation, with infinite time assigned infinite value. -/
def absorption_finite_mean : Prop := ∀ (N : ℕ), 1 ≤ N →
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : RuinState N),
    (∫⁻ ω, ENat.toENNReal (ruinTime N ω)
      ∂Markov.statePathLaw (ruinKernel N p hp hp1) i) < ∞

end RuinAbsorptionSpec
end
end P207.Walk
