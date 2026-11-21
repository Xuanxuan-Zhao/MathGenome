import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces

/-! Zero extension for the Euclidean, full-norm Sobolev model of §8.1.
No boundary regularity, connectedness, or nonemptiness is assumed. The statements
hold for every open set, hence in particular for the source's bounded open sets. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ENNReal
namespace VariationalNotes.Sobolev

/-- Zero extension of a Euclidean-valued Lp class, defined independently of any
Sobolev extension operator. -/
def fieldZeroExtension {ι : Type*} [Fintype ι] {d : ℕ}
    (Ω : Opens (Domain d)) (p : Exponent)
    (u : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)) :
    Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure (⊤ : Opens (Domain d))) :=
  (show MemLp ((Ω : Set (Domain d)).indicator u) p.ennreal
      (domainMeasure (⊤ : Opens (Domain d))) by
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
      (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr
      (Lp.memLp u)).toLp _

namespace ZeroExtensionExpected

def FieldRepresentative : Prop :=
  ∀ {ι : Type} [Fintype ι] {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (u : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)),
    (fieldZeroExtension Ω p u : Domain d → EuclideanSpace ℝ ι) =ᵐ[volume]
      (Ω : Set (Domain d)).indicator u

def FieldNorm : Prop :=
  ∀ {ι : Type} [Fintype ι] {d : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (u : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)),
    ‖fieldZeroExtension Ω p u‖ = ‖u‖

/-- A linear isometric embedding with zero-extended value and full weak-gradient
matrix, for every finite real p ≥ 1, including p = 1 and the empty domain. -/
def Extension : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent),
    ∃ E : W1pZero Ω m p →ₗᵢ[ℝ] W1p (⊤ : Opens (Domain d)) m p,
      (∀ u, value ⊤ m p (E u) = fieldZeroExtension Ω p (value Ω m p u.val)) ∧
      (∀ u, gradient ⊤ m p (E u) = fieldZeroExtension Ω p (gradient Ω m p u.val)) ∧
      (∀ u, ‖E u‖ =
        (‖value Ω m p u.val‖ ^ p.real + ‖gradient Ω m p u.val‖ ^ p.real) ^ (1 / p.real))

end ZeroExtensionExpected
end VariationalNotes.Sobolev
