import Mathlib.Probability.Martingale.Upcrossing

/-! Endpoint-inclusive greedy upcrossings for `paper.tex`, §5.3.
The value `n + 1` is a sentinel, never a completed buy or sale. A path is
represented by `ℕ → ℝ`; only its restriction to `0, …, n` is used.
`greedySale … 0 = 0` is the initial search origin, not a completed sale.
Buy `k` and sale `k + 1` form the `(k + 1)`st upcrossing. -/
namespace P207

noncomputable def greedySale (x : ℕ → ℝ) (a b : ℝ) (n k : ℕ) : ℕ :=
  MeasureTheory.upperCrossingTime a b (fun i (_ : Unit) => x i) (n + 1) k ()

noncomputable def greedyBuy (x : ℕ → ℝ) (a b : ℝ) (n k : ℕ) : ℕ :=
  MeasureTheory.lowerCrossingTime a b (fun i (_ : Unit) => x i) (n + 1) k ()

/-- Number of completed greedy sales through and including time `n`. -/
noncomputable def greedyUpcrossings (x : ℕ → ℝ) (a b : ℝ) (n : ℕ) : ℕ :=
  sSup {k | greedySale x a b n k ≤ n}

/-- An ordered list of `m` disjoint completed upcrossings through time `n`.
For `m = 0` both functions have empty domain and all conditions are vacuous. -/
def UpcrossingPairs (x : ℕ → ℝ) (a b : ℝ) (n m : ℕ) : Prop :=
  ∃ s t : Fin m → ℕ,
    (∀ j, s j < t j ∧ t j ≤ n ∧ x (s j) ≤ a ∧ b ≤ x (t j)) ∧
    ∀ i j, i < j → t i < s j

namespace GreedyUpcrossingsSpec

def saleType := (ℕ → ℝ) → ℝ → ℝ → ℕ → ℕ → ℕ
noncomputable def saleValue : saleType := greedySale
def buyType := (ℕ → ℝ) → ℝ → ℝ → ℕ → ℕ → ℕ
noncomputable def buyValue : buyType := greedyBuy
def countType := (ℕ → ℝ) → ℝ → ℝ → ℕ → ℕ
noncomputable def countValue : countType := greedyUpcrossings
def pairsType := (ℕ → ℝ) → ℝ → ℝ → ℕ → ℕ → Prop
def pairsValue : pairsType := UpcrossingPairs

/-- The least available buy, starting strictly after a completed sale. -/
def buyRule : Prop :=
  ∀ (x : ℕ → ℝ) (a b : ℝ) (n k s : ℕ), a < b → s ≤ n →
    (greedyBuy x a b n k ≤ s ↔
      ∃ r, (if k = 0 then 0 ≤ r else greedySale x a b n k < r) ∧
        r ≤ s ∧ x r ≤ a)

/-- The least sell strictly after the buy. -/
def saleRule : Prop :=
  ∀ (x : ℕ → ℝ) (a b : ℝ) (n k t : ℕ), a < b → t ≤ n →
    (greedySale x a b n (k + 1) ≤ t ↔
      ∃ r, greedyBuy x a b n k < r ∧ r ≤ t ∧ b ≤ x r)

/-- A count of `m` means precisely that greedy sale `m` has occurred by `n`. -/
def completed : Prop :=
  ∀ (x : ℕ → ℝ) (a b : ℝ) (n m : ℕ), a < b →
    (m ≤ greedyUpcrossings x a b n ↔ greedySale x a b n m ≤ n)

/-- Actual bridge from the source's inclusive cutoff to the library's strict cutoff. -/
def libraryBridge : Prop :=
  ∀ (x : ℕ → ℝ) (a b : ℝ) (n : ℕ),
    greedyUpcrossings x a b n =
      MeasureTheory.upcrossingsBefore a b (fun i (_ : Unit) => x i) (n + 1) ()

/-- The same bridge along any sample path, without changing the sample space. -/
def processBridge : Prop :=
  ∀ (Ω : Type*) (f : ℕ → Ω → ℝ) (a b : ℝ) (n : ℕ) (ω : Ω),
    greedyUpcrossings (fun i => f i ω) a b n =
      MeasureTheory.upcrossingsBefore a b f (n + 1) ω

/-- The greedy count is attained and is the largest admissible list length. -/
def largest : Prop :=
  ∀ (x : ℕ → ℝ) (a b : ℝ) (n : ℕ), a < b →
    UpcrossingPairs x a b n (greedyUpcrossings x a b n) ∧
    ∀ m, UpcrossingPairs x a b n m → m ≤ greedyUpcrossings x a b n

def zeroHorizon : Prop :=
  ∀ (x : ℕ → ℝ) (a b : ℝ), a < b → greedyUpcrossings x a b 0 = 0

def emptyList : Prop := ∀ (x : ℕ → ℝ) (a b : ℝ) (n : ℕ),
  UpcrossingPairs x a b n 0

/-- No value of the extension of the finite path beyond `n` affects the count. -/
def locality : Prop :=
  ∀ (x y : ℕ → ℝ) (a b : ℝ) (n : ℕ), a < b →
    (∀ i, i ≤ n → x i = y i) →
    greedyUpcrossings x a b n = greedyUpcrossings y a b n

end GreedyUpcrossingsSpec
end P207
