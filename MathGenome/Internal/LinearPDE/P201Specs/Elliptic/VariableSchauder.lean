import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ConstantSchauder

/-!
Independent statements for `pde:elliptic-variable-estimate`, paper.tex:2015–2127.
These are a priori estimates: the solution is already locally C²,α, including
one-sided regularity at the portion of the boundary under consideration.
No sign condition on the zeroth-order coefficient and no connectedness or
nonemptiness condition on the open set is imposed.

The coordinate sums below are the shared scalar Hölder norms. All pairs are
used in each seminorm. Finiteness is imposed separately before using real
suprema. Constants are uniform over coefficient fields with the indicated
norm bound and are chosen before the solution, source and boundary lift.
-/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201Specs.Elliptic.VariableSchauder
open NewtonHessian PoissonSchauder ConstantSchauder

/-- Symmetry and a specified uniform lower ellipticity bound. Upper bounds
are supplied by the coefficient Hölder norm; there is no condition on c. -/
def UniformlyEllipticOn {n : ℕ} (ell : ℝ)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (s : Set (Space n)) : Prop :=
  (∀ x ∈ s, ∀ i j, a x i j = a x j i) ∧
  ∀ x ∈ s, ∀ ξ : Space n,
    ell * ‖ξ‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * ξ i * ξ j

/-- Componentwise bounded Hölder coefficients on the observation set. -/
def CoefficientsHolderOn {n : ℕ} (α : ℝ)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ) (s : Set (Space n)) : Prop :=
  (∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
  (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s

/-- Local coefficient regularity does not impose global norm bounds. -/
def CoefficientsHolderLoc {n : ℕ} (α : ℝ)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ) (Ω : Domain n) : Prop :=
  (∀ i j : Fin n, IsHolderLoc α (fun x => a x i j) Ω) ∧
  (∀ i : Fin n, IsHolderLoc α (fun x => b x i) Ω) ∧ IsHolderLoc α c Ω

/-- One explicit finite-dimensional norm controlling all coefficients. -/
def coefficientNormOn {n : ℕ} (α : ℝ)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
    (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s

/-- The unscaled C²,α norm using the actual derivatives within the set.
In particular this norm does not see arbitrary representatives outside Ω̄. -/
def c2HolderUpToNormOn {n : ℕ} (α : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) : ℝ :=
  scaledWithinSolutionNorm α 1 u s

/-- C²,α graph boundary at the points of a specified ambient open portion.
The graph charts are the shared one-sided geometric charts. Shrinking a
chart makes the bounded graph norm equivalent to the usual local C²,α
condition. This includes m=0, i.e. intervals in dimension one. -/
def HasC2HolderBoundaryOn {m : ℕ} (α : ℝ) (Ω : Domain (m + 1))
    (U : Set (Space (m + 1))) : Prop :=
  ∀ p ∈ frontier (Ω : Set (Space (m + 1))), p ∈ U →
    ∃ C : P102.Sobolev.Geometry.BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω :
        Set (P102.U4.GraphPieces.Ambient m)),
      graphFrame m (C.frame (P102.U4.GraphPieces.graph C.graphFunction C.center)) = p ∧
      IsC2HolderOn α C.graphFunction (ball C.center C.radius)

/-- Boundary regularity on the whole boundary. Boundedness of Ω remains a
separate hypothesis, and connectedness is not part of this definition. -/
def HasC2HolderBoundary {m : ℕ} (α : ℝ) (Ω : Domain (m + 1)) : Prop :=
  HasC2HolderBoundaryOn α Ω univ

/-- Local up-to-boundary C²,α regularity on Ω̄ ∩ U. The neighborhoods include
the flat/curved boundary, but do not approach the ends of the open portion.
No boundedness of the solution or its derivatives on all of Ω̄ ∩ U is built
into this local regularity condition. -/
def IsC2HolderLocUpToOn {n : ℕ} (α : ℝ) (u : Space n → ℝ)
    (Ω : Domain n) (U : Domain n) : Prop :=
  ContDiffOn ℝ 2 u (closure (Ω : Set (Space n)) ∩ (U : Set (Space n))) ∧
  ∀ x ∈ closure (Ω : Set (Space n)) ∩ (U : Set (Space n)),
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ (U : Set (Space n)) ∧
      IsC2HolderUpToOn α u (closure (Ω : Set (Space n)) ∩ ball x r)

/-- Nested interior estimate for already locally C²,α solutions.
Ω′ is bounded and Ω̄′ ⊆ Ω″ ⊆ Ω; Ω and Ω″ may be unbounded or disconnected.
The C²,α norm is the canonical interior norm in actual classical derivatives. -/
def InteriorEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ Ω Ω' Ω'' : Domain n, Bornology.IsBounded (Ω' : Set (Space n)) →
      closure (Ω' : Set (Space n)) ⊆ (Ω'' : Set (Space n)) → Ω'' ≤ Ω →
      ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
            (b : Space n → Space n) (c : Space n → ℝ),
            UniformlyEllipticOn ell a Ω → CoefficientsHolderLoc α a b c Ω →
            CoefficientsHolderOn α a b c Ω'' → coefficientNormOn α a b c Ω'' ≤ K →
            ∀ u f : Space n → ℝ, IsC2HolderLocOn α u Ω → IsHolderLoc α f Ω →
              (∀ x ∈ Ω, nondivergenceOperator a b c u x = f x) →
              IsBoundedOn u Ω'' → IsHolderOn α f Ω'' →
              IsC2HolderOn α u Ω' ∧
              c2HolderNormOn α u Ω' ≤
                C * (supNormOn u Ω'' + holderNormOn α f Ω'')

/-- Global a priori estimate on a bounded C²,α open set. u and G are
C²,α on the closure in the one-sided sense. Equality with G is imposed
only on the actual boundary, and the equation only in the interior. -/
def GlobalEstimateStatement : Prop :=
  ∀ m : ℕ, ∀ α : ℝ, 0 < α → α < 1 → ∀ Ω : Domain (m + 1),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasC2HolderBoundary α Ω →
    ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
          (b : Space (m + 1) → Space (m + 1)) (c : Space (m + 1) → ℝ),
          UniformlyEllipticOn ell a (closure (Ω : Set (Space (m + 1)))) →
          CoefficientsHolderOn α a b c (closure (Ω : Set (Space (m + 1)))) →
          coefficientNormOn α a b c (closure (Ω : Set (Space (m + 1)))) ≤ K →
          ∀ u f G : Space (m + 1) → ℝ,
            IsC2HolderUpToOn α u (closure (Ω : Set (Space (m + 1)))) →
            IsHolderOn α f (closure (Ω : Set (Space (m + 1)))) →
            IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1)))) →
            (∀ x ∈ Ω, nondivergenceOperator a b c u x = f x) →
            (∀ x ∈ frontier (Ω : Set (Space (m + 1))), u x = G x) →
            c2HolderUpToNormOn α u (closure (Ω : Set (Space (m + 1)))) ≤
              C * (supNormOn u (closure (Ω : Set (Space (m + 1)))) +
                holderNormOn α f (closure (Ω : Set (Space (m + 1)))) +
                c2HolderUpToNormOn α G (closure (Ω : Set (Space (m + 1)))))

/-- Local estimate up to any C²,α boundary portion U, away from its ends:
V is a bounded open set with V̄ ⊆ U, and the norm is on Ω̄ ∩ V. Ω need not be
bounded and its boundary outside U need not be regular. Only local
C²,α regularity of u up to the portion is assumed; the source, lift, and
coefficient norms on the outer portion are finite. -/
def LocalBoundaryEstimateStatement : Prop :=
  ∀ m : ℕ, ∀ α : ℝ, 0 < α → α < 1 → ∀ Ω U : Domain (m + 1),
    HasC2HolderBoundaryOn α Ω U → ∀ V : Domain (m + 1),
      Bornology.IsBounded (V : Set (Space (m + 1))) →
      closure (V : Set (Space (m + 1))) ⊆ (U : Set (Space (m + 1))) →
      ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
            (b : Space (m + 1) → Space (m + 1)) (c : Space (m + 1) → ℝ),
            UniformlyEllipticOn ell a
              (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
            CoefficientsHolderOn α a b c
              (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
            coefficientNormOn α a b c
              (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) ≤ K →
            ∀ u f G : Space (m + 1) → ℝ,
              IsC2HolderLocUpToOn α u Ω U →
              IsBoundedOn u
                (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
              IsHolderOn α f
                (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
              IsC2HolderUpToOn α G
                (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
              (∀ x ∈ (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1))),
                nondivergenceOperator a b c u x = f x) →
              (∀ x ∈ frontier (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1))),
                u x = G x) →
              IsC2HolderUpToOn α u (closure (Ω : Set (Space (m + 1))) ∩ (V : Set (Space (m + 1)))) ∧
              c2HolderUpToNormOn α u (closure (Ω : Set (Space (m + 1))) ∩ (V : Set (Space (m + 1)))) ≤
                C * (supNormOn u
                    (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) +
                  holderNormOn α f
                    (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) +
                  c2HolderUpToNormOn α G
                    (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))))

end P201Specs.Elliptic.VariableSchauder
