import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition
import Mathlib.MeasureTheory.Measure.Map

/-!
Independent specifications for paper.tex:5946–5953, the modular function.
The measure has exactly the Borel domain and the shared Radon/Haar predicates.
Right translation of sets determines the convention: μ(Ea) = Δ(a) μ(E).
All scalars are real, hence finite; strict positivity is explicit.
-/
namespace Specs.D11.Ch21.ModularFunction

open MeasureTheory
universe u
noncomputable section

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

/-- A candidate scalar for right translation of Borel sets. -/
def IsModularFactor {G : Type u} [TopologicalSpace G] [Group G]
    (μ : @Measure G (borel G)) (a : G) (c : ℝ) : Prop :=
  0 < c ∧ ∀ E : Set G, MeasurableSet[borel G] E →
    μ ((fun x => x * a) '' E) = ENNReal.ofReal c * μ E

def rightTranslatedMeasure_type :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G],
    @Measure G (borel G) → G → @Measure G (borel G)

/-- The inverse translation in the pushforward makes its value on E be μ(Ea). -/
def rightTranslatedMeasure_value : rightTranslatedMeasure_type.{u} := fun μ a =>
  μ.map (fun x => x * a⁻¹)

def modularFunction_type :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G],
    @Measure G (borel G) → G → ℝ

/-- For Haar μ the set is a singleton, as asserted and proved separately. -/
def modularFunction_value : modularFunction_type.{u} := fun μ a =>
  sInf {c : ℝ | IsModularFactor μ a c}

def rightTranslatedMeasure_apply : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (μ : @Measure G (borel G)) (a : G) (E : Set G),
    MeasurableSet[borel G] E →
    rightTranslatedMeasure_value μ a E = μ ((fun x => x * a) '' E)

def rightTranslatedMeasure_leftHaar : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ a : G,
    HaarDefinition.leftHaarValue (rightTranslatedMeasure_value μ a)

def scalar_exists_unique : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ a : G, ∃! c : ℝ, IsModularFactor μ a c

def modularFunction_spec : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ a : G,
    IsModularFactor μ a (modularFunction_value μ a)

def modularFunction_unique : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ (a : G) (c : ℝ),
    IsModularFactor μ a c → c = modularFunction_value μ a

/-- In particular every positive change of Haar normalization leaves Δ unchanged. -/
def modularFunction_independent : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ ν : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → HaarDefinition.leftHaarValue ν →
    ∀ a : G, modularFunction_value μ a = modularFunction_value ν a

/-- Explicit invariance under every finite positive real rescaling of μ. -/
def modularFunction_smul : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ (c : ℝ), 0 < c → ∀ a : G,
    modularFunction_value (ENNReal.ofReal c • μ) a = modularFunction_value μ a

end
end Specs.D11.Ch21.ModularFunction
