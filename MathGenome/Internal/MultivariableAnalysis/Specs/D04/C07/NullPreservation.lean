import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! Independent statements for paper.tex, d04:07:null-preservation.
The maps are ambient extensions restricted to the displayed open domains.
An open partial homeomorphism records the underlying homeomorphism of a
C¹ diffeomorphism; both directions retain their C¹ hypotheses. -/
noncomputable section
open Set Topology
open scoped NNReal
namespace Specs.D04.C07.NullPreservation
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C06.NullCovers.Model
open Specs.D04.C06.JordanRegions.Model

def c1_locally_lipschitzType : Prop := ∀ {n : ℕ} (U : Set (E n)) (F : E n → E n),
  IsOpen U → CrOn 1 U F → ∀ x ∈ U,
  ∃ (L : ℝ≥0) (W : Set (E n)), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ LipschitzOnWith L F W

def c1_null_imageType : Prop := ∀ {n : ℕ}, 0 < n →
  ∀ (U : Set (E n)) (F : E n → E n), IsOpen U → CrOn 1 U F →
  ∀ S : Set (E n), S ⊆ U → Null S → Null (F '' S)

def c1_contentZero_imageType : Prop := ∀ {n : ℕ}, 0 < n →
  ∀ (U : Set (E n)) (F : E n → E n), IsOpen U → CrOn 1 U F →
  ∀ K : Set (E n), K ⊆ U → IsCompact K → ContentZero K → ContentZero (F '' K)

/-- Ambient frontier equality; compact containment is explicit. -/
def diffeomorph_frontierType : Prop := ∀ {n : ℕ}
  (e : OpenPartialHomeomorph (E n) (E n)) (S : Set (E n)),
  IsCompact (closure S) → closure S ⊆ e.source → frontier (e '' S) = e '' frontier S

def diffeomorph_jordanType : Prop := ∀ {n : ℕ}, 0 < n →
  ∀ (e : OpenPartialHomeomorph (E n) (E n)),
  CrOn 1 e.source e → CrOn 1 e.target e.symm →
  ∀ S : Set (E n), Jordan S → IsCompact (closure S) → closure S ⊆ e.source →
  Bornology.IsBounded (e '' S) ∧ Jordan (e '' S) ∧ frontier (e '' S) = e '' frontier S
end Specs.D04.C07.NullPreservation
