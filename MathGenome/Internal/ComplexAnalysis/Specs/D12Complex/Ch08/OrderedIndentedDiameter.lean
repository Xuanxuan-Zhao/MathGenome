import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Data.Finset.Sort

/-! Ordered, clockwise-indented real intervals; supporting paper.tex:2147–2162.
The traversal predicate records actual values on every closed unit interval.
No path existence or regularity certificate is a hypothesis of the main result. -/
noncomputable section
open Set
namespace Specs.D12Complex.Ch08.OrderedIndentedDiameter
open _root_.D12Complex

def Admissible (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ) : Prop :=
  l < u ∧ (∀ a, 0 < ε a ∧ l < a.val - ε a ∧ a.val + ε a < u) ∧
    ∀ a b, a.val < b.val → a.val + ε a < b.val - ε b

def Gaps {s : Finset ℝ} (l u : ℝ) (ε : s → ℝ) {n : ℕ}
    (e : Fin n ≃ s) (start stop : Fin (n+1) → ℝ) : Prop :=
  StrictMono (fun i => (e i).val) ∧
  start 0 = l ∧ stop (Fin.last n) = u ∧
  (∀ i, stop i.castSucc = (e i).val - ε (e i)) ∧
  (∀ i, start i.succ = (e i).val + ε (e i)) ∧
  ∀ j, start j < stop j

def Traversal {s : Finset ℝ} (ε : s → ℝ) {n : ℕ} (e : Fin n ≃ s)
    (start stop : Fin (n+1) → ℝ) (γ : PiecewiseC1Path) : Prop :=
  γ.path.a = 0 ∧ γ.path.b = (2*n+1 : ℕ) ∧
  (∀ j : Fin (n+1), ∀ t ∈ Icc (2*(j.val:ℝ)) (2*(j.val:ℝ)+1),
    γ t = ((start j + (stop j-start j)*(t-2*(j.val:ℝ)) : ℝ) : ℂ)) ∧
  (∀ i : Fin n, ∀ t ∈ Icc (2*(i.val:ℝ)+1) (2*(i.val:ℝ)+2),
    γ t = circleMap ((e i).val : ℂ) (ε (e i))
      (Real.pi*(2*(i.val:ℝ)+2-t)))

def Retained (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ) : Set ℝ :=
  Icc l u \ ⋃ a : s, Ioo (a.val - ε a) (a.val + ε a)

def TraceSet (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ) : Set ℂ :=
  Complex.ofReal '' Retained s l u ε ∪
    ⋃ a : s, circleMap (a.val : ℂ) (ε a) '' Icc 0 Real.pi

def ordered_gaps_type : Prop :=
  ∀ (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ), Admissible s l u ε →
    ∃ (n : ℕ) (e : Fin n ≃ s) (start stop : Fin (n+1) → ℝ),
      Gaps l u ε e start stop

def path_exists_type : Prop :=
  ∀ (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ) (n : ℕ) (e : Fin n ≃ s)
    (start stop : Fin (n+1) → ℝ), Gaps l u ε e start stop →
    ∃ γ : PiecewiseC1Path, Traversal ε e start stop γ ∧
      γ.path.source = (l : ℂ) ∧ γ.path.target = (u : ℂ)

def trace_of_traversal_type : Prop :=
  ∀ (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ) (n : ℕ) (e : Fin n ≃ s)
    (start stop : Fin (n+1) → ℝ) (γ : PiecewiseC1Path),
    Admissible s l u ε → Gaps l u ε e start stop → Traversal ε e start stop γ →
      γ.trace = TraceSet s l u ε

def ordered_indented_diameter_exists_type : Prop :=
  ∀ (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ), Admissible s l u ε →
    ∃ (n : ℕ) (e : Fin n ≃ s) (start stop : Fin (n+1) → ℝ)
      (γ : PiecewiseC1Path), Gaps l u ε e start stop ∧
      Traversal ε e start stop γ ∧ γ.path.source = (l : ℂ) ∧
      γ.path.target = (u : ℂ) ∧ γ.trace = TraceSet s l u ε
end Specs.D12Complex.Ch08.OrderedIndentedDiameter
