import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.FritzJohn
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.MFCQTangency

/-! Theorem `thm:fritz-john`, paper.tex §v06-04 (2864–2911).
The unconditional Fritz John rule is retained separately from the MFCQ/LICQ
normalization. The shared definitions include the open domain, all constraints,
complementarity, signs and joint nonzeroness. Finite index types may be empty.
The algebraic positivity and normalization assertions need no extra regularity. -/
noncomputable section
universe u v w
namespace VariationalNotes.Ch06.KKTNecessitySpecs
open Specs

/-- Every Fritz John multiplier is normal under MFCQ. -/
def objectiveMultiplier_pos_of_mfcq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    ∀ (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ),
    MFCQ U g h x → FritzJohn U f g h x lam0 lam nu → 0 < lam0

/-- Division by the positive objective coefficient gives the stated KKT system. -/
def normalize_fritzJohn : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    ∀ (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ),
    FritzJohn U f g h x lam0 lam nu → 0 < lam0 →
    KKT U f g h x (fun i => lam i / lam0) (fun j => nu j / lam0)

/-- Qualified existence with precisely MFCQ. -/
def kkt_of_mfcq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → IsLocalMinOn f (feasibleSet U g h) x →
    MFCQ U g h x → ∃ (lam : I → ℝ) (nu : J → ℝ), KKT U f g h x lam nu

/-- LICQ suffices, including empty constraint families. -/
def kkt_of_licq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → IsLocalMinOn f (feasibleSet U g h) x →
    LICQ U g h x → ∃ (lam : I → ℝ) (nu : J → ℝ), KKT U f g h x lam nu

/-- The complete theorem: unconditional Fritz John existence and the qualified
normality and KKT conclusions, without qualification on the first assertion. -/
def fritzJohn_and_kkt : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → x ∈ feasibleSet U g h →
    IsLocalMinOn f (feasibleSet U g h) x →
    (∃ (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ), FritzJohn U f g h x lam0 lam nu) ∧
    (MFCQ U g h x →
      (∀ (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ),
        FritzJohn U f g h x lam0 lam nu → 0 < lam0) ∧
      ∃ (lam : I → ℝ) (nu : J → ℝ), KKT U f g h x lam nu) ∧
    (LICQ U g h x →
      (∀ (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ),
        FritzJohn U f g h x lam0 lam nu → 0 < lam0) ∧
      ∃ (lam : I → ℝ) (nu : J → ℝ), KKT U f g h x lam nu)

end VariationalNotes.Ch06.KKTNecessitySpecs
