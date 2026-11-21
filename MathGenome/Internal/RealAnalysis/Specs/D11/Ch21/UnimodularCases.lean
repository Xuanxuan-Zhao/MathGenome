import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.ModularFunction

/-!
Independent statements for paper.tex:5964–5970. Measures have exactly the
Borel domain and the shared nonzero Radon Haar predicates. No countability
or sigma-finiteness assumption is made. Unimodularity uses the shared
right-set convention μ(Ea) = Δ(a) μ(E).
-/
namespace Specs.D11.Ch21.UnimodularCases

open Set MeasureTheory
universe u
noncomputable section

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

def isUnimodular_type :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G], Prop

/-- The modular function is identically one for every left Haar normalization. -/
def isUnimodular_value : isUnimodular_type.{u} := fun G _ _ _ _ _ =>
  ∀ μ : @Measure G (borel G), HaarDefinition.leftHaarValue μ →
    ∀ a : G, ModularFunction.modularFunction_value μ a = 1

/-- For any left Haar measure, Δ ≡ 1 is equivalent to right Haar invariance. -/
def modular_eq_one_iff_rightHaar : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ →
      ((∀ a : G, ModularFunction.modularFunction_value μ a = 1) ↔
        HaarDefinition.rightHaarValue μ)

def isUnimodular_iff : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G],
    isUnimodular_value G ↔
      ∀ μ : @Measure G (borel G), HaarDefinition.leftHaarValue μ →
        HaarDefinition.rightHaarValue μ

def abelian_unimodular : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G], isUnimodular_value G

def compact_unimodular : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G], isUnimodular_value G

/-- Every compact Haar probability is invariant under both translations. -/
def compact_probability_biinvariant : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → μ univ = 1 →
      ∀ (a : G) (E : Set G), MeasurableSet[borel G] E →
        μ ((fun x => a * x) '' E) = μ E ∧
        μ ((fun x => x * a) '' E) = μ E

/-- The unique compact Haar probability has both Haar invariances. -/
def unique_biinvariant_probability : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G],
    ∃! μ : @Measure G (borel G),
      HaarDefinition.leftHaarValue μ ∧ HaarDefinition.rightHaarValue μ ∧ μ univ = 1

end
end Specs.D11.Ch21.UnimodularCases
