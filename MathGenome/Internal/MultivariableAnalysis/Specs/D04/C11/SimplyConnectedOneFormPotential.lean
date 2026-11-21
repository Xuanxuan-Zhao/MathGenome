import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.LocalAndStarShapedPotentials

/-! Independent statements for paper.tex, d04:11:simply-connected.
Contractions are continuous maps on the closed square. The endpoint tracks
agree, but need not be stationary. The empty domain and dimension zero are
included, using the Chapter 1 convention for path connectedness. -/
noncomputable section
open Set
open scoped unitInterval
namespace Specs.D04.C11.SimplyConnectedOneFormPotential
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C11.LocalAndStarShapedPotentials.Model
open Specs.D04.C11.PotentialPathIndependencePeriods.Model
namespace Model

def FreeLoopContractions {n : ℕ} (U : Set (E n)) : Prop :=
  ∀ (a : U) (γ : Path a a), ∃ b : U,
    ∃ H : (γ : C(I, U)).Homotopy (ContinuousMap.const I b),
      ∀ s : I, H (s, 0) = H (s, 1)

end Model
open Model

def FreeLoopContractionsType := {n : ℕ} → Set (E n) → Prop
def FreeLoopContractionsValue : FreeLoopContractionsType := @Model.FreeLoopContractions

def free_iff_basedType : Prop := ∀ {n : ℕ} (U : Set (E n)),
  SimplyConnected U ↔ PathConnected U ∧ FreeLoopContractions U

def simply_connected_zeroPeriodsType : Prop := ∀ {n : ℕ}
  (U : Set (E n)) (F : E n → E n),
  IsOpen U → IsPreconnected U → FreeLoopContractions U →
  CrOn 1 U F → SymmetricPartials U F → ZeroPeriods U F

def simply_connected_potentialType : Prop := ∀ {n : ℕ}
  (U : Set (E n)) (F : E n → E n),
  IsOpen U → IsPreconnected U → FreeLoopContractions U →
  CrOn 1 U F → (∀ x ∈ U, (jacobian F x).IsSymm) → HasPotential U F

end Specs.D04.C11.SimplyConnectedOneFormPotential
