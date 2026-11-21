import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.MorreyEmbedding

/-! Independent interfaces for the higher-order clauses of
`fa2:p4:sobolev-embedding`, paper.tex:17817–17825, and its logarithmic
counterexample at 17859–17861. This draft also records the derivative reduction
needed to iterate the accepted first-order inequalities. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.Sobolev.Higher
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Reindex a derivative of order at most n after taking the fixed derivative α.
The target is the existing canonical derivative index, not a second jet model. -/
def shiftIndex {d m n : ℕ} (α : Fin d → ℕ)
    (h : (∑ i, α i) + n ≤ m) (β : DerivativeIndex d n) : DerivativeIndex d m :=
  ⟨fun i => ⟨α i + natIndex β i, Nat.lt_succ_of_le
    ((Finset.single_le_sum (f := fun j : Fin d => α j + natIndex β j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (show (∑ j : Fin d, (α j + natIndex β j)) ≤ m by
        rw [Finset.sum_add_distrib]
        exact (Nat.add_le_add_left β.property _).trans h))⟩,
    by simpa only [Finset.sum_add_distrib, natIndex] using
      (Nat.add_le_add_left β.property (∑ i, α i)).trans h⟩

/-- The same multi-index, included into a larger order bound. -/
def orderIndex {d m n : ℕ} (h : n ≤ m) (β : DerivativeIndex d n) : DerivativeIndex d m :=
  shiftIndex 0 (by simpa using h) β

/-- The ordinary higher-order Sobolev exponent; used under m*p < d. -/
def targetExponent (d m : ℕ) (p : ℝ≥0) : ℝ≥0 := d * p / (d - m * p)

/-- The first-order extension property at the exponents used in iteration.
This includes whole space and the stated C¹ domains with compact boundary.
No higher-order extension theorem on a C¹ boundary is assumed. -/
def FirstOrderExtensionDomain (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p,
      C1Extension.IsExtension Ω E

/-- A norm-controlled inclusion of actual Sobolev a.e. classes into Lq. -/
def LpInclusion (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (m : ℕ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∃ C : ℝ≥0, ∀ u : SpaceValue 𝕜 d Ω m p,
    MemLp (u.val (zeroIndex d m)) q (volume.restrict (Ω : Set (Domain d))) ∧
    eLpNorm (u.val (zeroIndex d m)) q (volume.restrict (Ω : Set (Domain d))) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖

/-- One common Cᵏ representative and its continuous derivative jet on Ω̄.
The functions Fβ separately specify the boundary values of the derivatives;
no derivatives of a zero extension at the boundary are used. -/
def HolderJet {𝕜 : Type} [RCLike 𝕜] {d m : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω m p)
    (k : ℕ) (hk : k ≤ m) (a C : ℝ) : Prop :=
  ∃ F : DerivativeIndex d k → Domain d → 𝕜,
    ContDiffOn ℝ k (F (zeroIndex d k)) (Ω : Set (Domain d)) ∧
    (∀ β, ContinuousOn (F β) (closure (Ω : Set (Domain d)))) ∧
    (∀ β, u.val (shiftIndex 0 (by simpa using hk) β)
      =ᵐ[volume.restrict (Ω : Set (Domain d))] F β) ∧
    (∀ β, EqOn (F β)
      (Smoothing.classicalDerivative β (F (zeroIndex d k))) (Ω : Set (Domain d))) ∧
    (∀ β, ∀ x ∈ closure (Ω : Set (Domain d)), ‖F β x‖ ≤ C * ‖u‖) ∧
    (∀ β, (∑ i, natIndex β i) = k →
      ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
        ‖F β x - F β y‖ ≤ C * ‖u‖ * Morrey.euclideanNorm (x - y) ^ a)

/-- The source's radial power of a logarithm, with harmless value zero at 0. -/
def logarithmicProfile {d : ℕ} (a : ℝ) (x : Domain d) : ℝ :=
  if x = 0 then 0 else (Real.log (1 / Morrey.euclideanNorm x)) ^ a

/-- Work on a ball of radius < 1, so the displayed logarithm is positive.
This suffices for the source's 'near zero' endpoint counterexample. -/
def logarithmicDomain (d : ℕ) : Opens (Domain d) :=
  ⟨{x | Morrey.euclideanNorm x < Real.exp (-1)},
    isOpen_lt (continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))) continuous_const⟩

end ExpandedFA.Sobolev.Higher

namespace Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.Higher WeakDerivativeSpaces

/-- Taking any weak derivative leaves exactly the remaining Sobolev order,
with no loss in the canonical sum norm. All exponents, including ∞, and all
open sets, including empty and zero-dimensional ones, are retained. -/
def DerivativeReduction : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (m n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (α : Fin d → ℕ) (h : (∑ i, α i) + n ≤ m),
  ∃ D : SpaceValue 𝕜 d Ω m p →L[𝕜] SpaceValue 𝕜 d Ω n p,
    ∀ u, (∀ β, (D u).val β = u.val (shiftIndex α h β)) ∧ ‖D u‖ ≤ ‖u‖

/-- Every component whose remaining Sobolev order is at least one has the
first-order Morrey bound whenever p>d. This helper is not the full iterative
higher-order conclusion below. -/
def DerivativeMorrey : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)], (d : ℝ≥0∞) < p →
  ∀ E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p,
    C1Extension.IsExtension Ω E → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : ℕ) (α : Fin d → ℕ) (h : (∑ i, α i) + 1 ≤ m)
        (u : SpaceValue 𝕜 d Ω m p),
      ∃ f : Domain d → 𝕜, Continuous f ∧
        u.val (shiftIndex α h (zeroIndex d 1))
          =ᵐ[volume.restrict (Ω : Set (Domain d))] f ∧
        ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
          ‖f x - f y‖ ≤ C * ‖u‖ * Morrey.euclideanNorm (x - y) ^ Morrey.exponent d p

/-- A first-order bound raises the integrability of every derivative of
order at most m, giving a genuine Wᵐ,q graph from a Wᵐ⁺¹,p graph. -/
def LpGainStep : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (Ω : Opens (Domain d)) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (C : ℝ≥0),
    (∀ u : SpaceValue 𝕜 d Ω 1 p,
      MemLp (u.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖) →
    ∀ u : SpaceValue 𝕜 d Ω (m+1) p, ∃ v : SpaceValue 𝕜 d Ω m q,
      (∀ β, v.val β =ᵐ[volume.restrict (Ω : Set (Domain d))]
        u.val (orderIndex (Nat.le_succ m) β)) ∧
      ENNReal.ofReal ‖v‖ ≤ (Fintype.card (DerivativeIndex d m) : ℝ≥0∞) *
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖

/-- m=0 is retained; then the target is simply p. -/
def SubcriticalWholeSpace : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))], 1 ≤ p → m * p < d →
  LpInclusion 𝕜 (⊤ : Opens (Domain d)) m p (targetExponent d m p)

def SubcriticalBoundedExtension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    FirstOrderExtensionDomain 𝕜 Ω →
    ∀ (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))], 1 ≤ p → m * p < d →
      LpInclusion 𝕜 Ω m p (targetExponent d m p)

/-- Only finite target exponents are asserted at the critical threshold. -/
def CriticalBoundedExtension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    FirstOrderExtensionDomain 𝕜 Ω →
    ∀ (p q : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))], 1 ≤ p → 1 ≤ q → m * p = d →
      LpInclusion 𝕜 Ω m p q

/-- The nonintegral gap m-d/p=k+a. Infinity is included using 1/∞=0. -/
def NonintegralHolder : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m k : ℕ)
    (Ω : Opens (Domain d)),
    (Ω = ⊤ ∨ (Bornology.IsBounded (Ω : Set (Domain d)) ∧
      FirstOrderExtensionDomain 𝕜 Ω)) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℝ), 0 < a → a < 1 →
      (m : ℝ) - (d : ℝ) / p.toReal = k + a →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ hk : k ≤ m,
        ∀ u : SpaceValue 𝕜 d Ω m p, HolderJet u k hk a C

/-- At a positive integral gap k the last derivative is order k-1, with
any exponent strictly between zero and one. There is no Lipschitz claim. -/
def IntegralHolder : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m k : ℕ)
    (Ω : Opens (Domain d)),
    (Ω = ⊤ ∨ (Bornology.IsBounded (Ω : Set (Domain d)) ∧
      FirstOrderExtensionDomain 𝕜 Ω)) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ k →
      (m : ℝ) - (d : ℝ) / p.toReal = k →
      ∀ a : ℝ, 0 < a → a < 1 → ∃ C : ℝ, 0 ≤ C ∧
        ∃ hk : k - 1 ≤ m, ∀ u : SpaceValue 𝕜 d Ω m p, HolderJet u (k-1) hk a C

/-- Each derivative has the exponent prescribed by its remaining order.
At gap r in (0,1) the endpoint a=r is allowed; at r=1 only a<1 is
allowed; at r>1 the derivative is Lipschitz. -/
def DerivativeHolderEmbeddings : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (Ω : Opens (Domain d)),
    (Ω = ⊤ ∨ (Bornology.IsBounded (Ω : Set (Domain d)) ∧
      FirstOrderExtensionDomain 𝕜 Ω)) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (β : DerivativeIndex d m) (a : ℝ),
      0 < a → a ≤ 1 →
      (a < (m : ℝ) - (∑ i, natIndex β i) - (d : ℝ) / p.toReal ∨
        (a = (m : ℝ) - (∑ i, natIndex β i) - (d : ℝ) / p.toReal ∧ a < 1)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d Ω m p,
        ∃ f : Domain d → 𝕜, ContinuousOn f (closure (Ω : Set (Domain d))) ∧
          (u.val β =ᵐ[volume.restrict (Ω : Set (Domain d))] f) ∧
          (∀ x ∈ closure (Ω : Set (Domain d)), ‖f x‖ ≤ C * ‖u‖) ∧
          ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
            ‖f x - f y‖ ≤ C * ‖u‖ * Morrey.euclideanNorm (x - y) ^ a

/-- The logarithmic profile itself, rather than an unspecified unbounded
function, is a W¹ᵈ class on the ball and is not essentially bounded there. -/
def LogarithmicCounterexample : Prop := ∀ d : ℕ, 1 < d →
  ∀ a : ℝ, 0 < a → a < 1 - 1 / (d : ℝ) →
  ∀ [Fact (1 ≤ (d : ℝ≥0∞))],
    (∃ u : SpaceValue ℝ d (logarithmicDomain d) 1 d,
      u.val (zeroIndex d 1)
        =ᵐ[volume.restrict (logarithmicDomain d : Set (Domain d))] logarithmicProfile a) ∧
    ¬ MemLp (logarithmicProfile (d := d) a) ∞
      (volume.restrict (logarithmicDomain d : Set (Domain d)))

/-- Bridge to the source's stated geometric domains, without any extra
regularity of their boundary beyond the accepted C¹ hypothesis. -/
def C1ExtensionDomains : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), C1Extension.IsC1Domain Ω →
    IsCompact (frontier (Ω : Set (Domain d))) → FirstOrderExtensionDomain 𝕜 Ω

/-- The canonical underlying Lp inclusion, also covering the zero-order
infinity endpoint where the higher-order exponent formula is just infinity. -/
def SameExponentInclusion : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)], LpInclusion 𝕜 Ω m p p

/-- Full parent obligation; none of these analytic clauses is assumed. -/
def HigherEmbeddings : Prop := SubcriticalWholeSpace ∧ SubcriticalBoundedExtension ∧
  CriticalBoundedExtension ∧ NonintegralHolder ∧ IntegralHolder ∧
  DerivativeHolderEmbeddings ∧ LogarithmicCounterexample ∧ C1ExtensionDomains

end Specs.ExpandedFA.Sobolev.HigherSobolevEmbeddings
