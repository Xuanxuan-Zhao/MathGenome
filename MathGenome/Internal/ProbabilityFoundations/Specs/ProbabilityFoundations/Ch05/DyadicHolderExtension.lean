import Mathlib.Topology.MetricSpace.Holder

/-! Deterministic dyadic-grid hypotheses for the chaining step in
`paper.tex`, proof of Kolmogorov--Chentsov, lines 1365–1376. -/
universe u

noncomputable section

namespace ProbabilityFoundations.Ch05.Dyadic

/-- Mesh size of the dyadic grid of `[0,T]`. -/
def mesh (T : ℝ) (n : ℕ) : ℝ := T / (2 : ℝ) ^ n

/-- The union of all finite dyadic grids, including both endpoints. -/
def domain (T : ℝ) : Set ℝ :=
  {x | ∃ n j : ℕ, j ≤ 2 ^ n ∧ x = (j : ℝ) * mesh T n}

/-- The canonical inclusion of a grid point into the dyadic domain. -/
def point (T : ℝ) (n j : ℕ) (hj : j ≤ 2 ^ n) : domain T :=
  ⟨(j : ℝ) * mesh T n, n, j, hj, rfl⟩

/-- Every adjacent increment at every level has the prescribed bound. -/
def AdjacentBound {S : Type*} [MetricSpace S] (T γ A : ℝ) (f : domain T → S) : Prop :=
  ∀ (n j : ℕ) (hj : j < 2 ^ n),
    dist (f (point T n j hj.le)) (f (point T n (j + 1) hj)) ≤ A * mesh T n ^ γ

/-- A global Hölder estimate, with a finite real constant. -/
def Bound {S X : Type*} [MetricSpace S] [MetricSpace X]
    (γ K : ℝ) (f : X → S) : Prop :=
  ∀ x y, dist (f x) (f y) ≤ K * dist x y ^ γ

end ProbabilityFoundations.Ch05.Dyadic

namespace Specs.ProbabilityFoundations.Ch05.DyadicHolderExtension
open ProbabilityFoundations.Ch05.Dyadic

/-- The adjacent-increment hypothesis implies a global finite Hölder bound on `D`. -/
def chaining : Prop :=
  ∀ {S : Type u} [MetricSpace S] (T : ℝ), 0 < T →
    ∀ (γ A : ℝ), 0 < γ → 0 ≤ A → ∀ (f : domain T → S),
    AdjacentBound T γ A f → ∃ K : ℝ, 0 ≤ K ∧ Bound γ K f

/-- Every such map into a complete metric space extends uniquely and retains
one and the same Hölder constant on the dyadics and the whole interval.
Uniqueness is among all continuous extensions, whether or not a bound is supplied. -/
def extension : Prop :=
  ∀ {S : Type u} [MetricSpace S] [CompleteSpace S] (T : ℝ) (_hT : 0 < T),
    ∀ (γ A : ℝ), 0 < γ → 0 ≤ A → ∀ (f : domain T → S),
    AdjacentBound T γ A f →
    ∃ (K : ℝ) (F : Set.Icc (0 : ℝ) T → S),
      0 ≤ K ∧ Bound γ K f ∧ Continuous F ∧
      (∀ x : domain T, ∀ hx : (x : ℝ) ∈ Set.Icc (0 : ℝ) T, F ⟨x, hx⟩ = f x) ∧
      Bound γ K F ∧
      ∀ G : Set.Icc (0 : ℝ) T → S, Continuous G →
        (∀ x : domain T, ∀ hx : (x : ℝ) ∈ Set.Icc (0 : ℝ) T, G ⟨x, hx⟩ = f x) → G = F

end Specs.ProbabilityFoundations.Ch05.DyadicHolderExtension
