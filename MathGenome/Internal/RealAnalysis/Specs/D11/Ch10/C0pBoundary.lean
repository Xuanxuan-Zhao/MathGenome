import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Independent statements for the two examples at paper.tex:3575–3582.
All norms are the previously fixed source norms. The quotient unit ball is
specified by representatives and their source norms, so it does not depend
on a candidate's choice of normed-space instances. The accepted quotient
construction identifies exactly this ball and these norms with the normed
ordinary a.e. quotient. No locally-null quotient is used.
-/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace Specs.D11.Ch10.C0pBoundary
open Specs.D11.Ch10.LpDefinition Specs.D11.Ch10.QuotientConstruction

/-- The indicator of one of the two distinct counting points. -/
def pointIndicator {𝕜 : Type} [Zero 𝕜] [One 𝕜] (a x : Bool) : 𝕜 :=
  if x = a then 1 else 0

/-- A single atom whose nonempty set has infinite mass. -/
def infiniteAtom : Measure Unit := (∞ : ℝ≥0∞) • Measure.dirac ()

variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The ordinary quotient unit ball, given by its raw representatives. -/
def atomUnitBall : Set (QuotientLp (𝕜 := 𝕜) infiniteAtom 1) :=
  {q | ∃ f : Raw (𝕜 := 𝕜) infiniteAtom 1,
    classOf f = q ∧ sourceNorm infiniteAtom 1 f.val ≤ 1}

/-- Pairing with the constant-one infinity class. Integrability of its
representative products is a conclusion below; totalization is not used
to infer any pairing value. A.e. invariance makes this quotient lift valid. -/
def atomPairing : QuotientLp (𝕜 := 𝕜) infiniteAtom 1 → 𝕜 :=
  Quotient.lift (fun f : Raw (𝕜 := 𝕜) infiniteAtom 1 =>
    ∫ x, f.val x * (1 : 𝕜) ∂infiniteAtom)
    (by
      intro f g h
      apply integral_congr_ae
      have heq : f.val =ᵐ[infiniteAtom] g.val := by
        change ∀ᵐ x ∂infiniteAtom, f.val x = g.val x
        rw [ae_iff]
        exact h
      exact heq.mono (fun _ hx => congrArg (fun z => z * (1 : 𝕜)) hx))

/-- Exact finite source norms and strict failure of the triangle inequality,
for every exponent in the displayed range and both scalar fields. -/
def two_point_failure : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (p : ℝ), 0 < p → p < 1 →
    let f : Bool → 𝕜 := pointIndicator false
    let g : Bool → 𝕜 := pointIndicator true
    f ≠ g ∧ f ∈ rawLp_value Measure.count p ∧
    g ∈ rawLp_value Measure.count p ∧
    (f + g) ∈ rawLp_value Measure.count p ∧
    powerNorm_value Measure.count p f = 1 ∧
    powerNorm_value Measure.count p g = 1 ∧
    powerNorm_value Measure.count p (f + g) = (2 : ℝ≥0∞) ^ (1 / p) ∧
    (2 : ℝ) < (2 : ℝ) ^ (1 / p) ∧
    powerNorm_value Measure.count p f + powerNorm_value Measure.count p g <
      powerNorm_value Measure.count p (f + g)

/-- Checks the actual measure and its ordinary null sets. -/
def infinite_atom_mass : Prop :=
  infiniteAtom {()} = ∞ ∧ ∀ s : Set Unit, infiniteAtom s = 0 ↔ s = ∅

/-- All raw L1 functions vanish at every point; consequently all ordinary
L1 classes are the zero class. -/
def infinite_atom_L1 : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    (∀ f : Unit → 𝕜, f ∈ rawLp_value infiniteAtom 1 ↔ f = 0) ∧
    (∀ q : QuotientLp (𝕜 := 𝕜) infiniteAtom 1,
      q = classOf (0 : Raw (𝕜 := 𝕜) infiniteAtom 1))

/-- Constant one defines a nonzero ordinary infinity class with source norm
one. Its integrable products with all L1 representatives have zero integral.
Its pairing supremum over the quotient L1 unit ball is zero, strictly below
its infinity norm. The representative norm is the quotient norm by the
accepted `norm_classOf` formula, rather than by a new convention. -/
def infinite_atom_endpoint : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    ∃ oneRaw : Raw (𝕜 := 𝕜) infiniteAtom ∞,
      oneRaw.val = (fun _ => 1) ∧
      sourceNorm infiniteAtom ∞ oneRaw.val = 1 ∧
      classOf oneRaw ≠ classOf (0 : Raw (𝕜 := 𝕜) infiniteAtom ∞) ∧
      (∀ g : Raw (𝕜 := 𝕜) infiniteAtom 1,
        Integrable (fun x => g.val x * oneRaw.val x) infiniteAtom ∧
        (∫ x, g.val x * oneRaw.val x ∂infiniteAtom) = 0) ∧
      sSup ((fun q => ‖atomPairing q‖ₑ) '' (atomUnitBall (𝕜 := 𝕜))) = 0 ∧
      sSup ((fun q => ‖atomPairing q‖ₑ) '' (atomUnitBall (𝕜 := 𝕜))) <
        sourceNorm infiniteAtom ∞ oneRaw.val

end Specs.D11.Ch10.C0pBoundary
