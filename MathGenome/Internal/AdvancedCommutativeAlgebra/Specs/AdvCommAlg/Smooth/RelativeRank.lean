import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.StandardPresentation
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.Topology.LocallyConstant.Basic

/-! SM-09, the local relative-rank assertion (paper.tex:1229–1241,
1246–1248). The fibers are cotangent fibers over the residue field at the
specified prime. All commutative rings are allowed; the spectrum of the
zero ring is empty. No nontriviality hypothesis is imposed on an algebra
or a principal chart, and both c = 0 and c = n are included. -/
namespace Specs.AdvCommAlg.Smooth.RelativeRank

universe u v
noncomputable section
open scoped TensorProduct

def relativeRankType := ∀ (A : Type u) (B : Type v),
  [CommRing A] → [CommRing B] → [Algebra A B] → PrimeSpectrum B → ℕ

/-- The dimension of κ(q) ⊗[B] Ω[B/A]. Finiteness for smooth algebras is
asserted separately, so the natural-valued dimension has its usual meaning. -/
def relativeRankValue : relativeRankType.{u,v} := fun A B _ _ _ q =>
  Module.finrank q.asIdeal.ResidueField
    (q.asIdeal.ResidueField ⊗[B] KaehlerDifferential A B)

def finiteFiber : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B → ∀ q : PrimeSpectrum B,
    Module.Finite q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[B] KaehlerDifferential A B)

def locallyConstantRank : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B → IsLocallyConstant (relativeRankValue A B)

/-- Every specified standard smooth presentation on every principal chart.
The prime of B is the contraction of the chart prime along B → B_g. -/
def principalChartRank : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B → ∀ (g : B) {n c : ℕ}
    (P : Algebra.Presentation A (Localization.Away g) (Fin n) (Fin c)),
    presentationStandardSmooth P → ∀ q : PrimeSpectrum (Localization.Away g),
      relativeRankValue A B (q.comap (algebraMap B (Localization.Away g))) = n - c

end
end Specs.AdvCommAlg.Smooth.RelativeRank
