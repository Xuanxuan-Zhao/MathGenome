import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceGenerators
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.LawsAndTransfer
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceJointLaws

/-!
The law assertion of Theorem 2.2 (paper.tex:513–516,536–542).
The canonical finite measure product uses the specified product sigma-algebra.
Mathlib's rectangle uniqueness theorem applies to arbitrary measurable target
spaces, including empty and singleton index families. The ambient probability
space need not be complete.
-/

open MeasureTheory

namespace ProbabilityFoundations.Ch02

universe u v w

/-- A finite measurable family is mutually independent iff its joint law is
the finite product of the marginal probability laws. -/
theorem independentRandomElements_iff_jointLaw_eq_pi
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i)) :
    IndependentRandomElements P X ↔
      Ch01.jointLaw P X = Measure.pi (fun i => Ch01.law P (X i)) := by
  rw [independentRandomElements_iff_iIndepFun]
  exact ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)

/-- On any index set, mutual independence is equivalent to the product-law
identity for every finite subfamily, including the empty one. -/
theorem independentRandomElements_iff_finite_jointLaws_eq_pi
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i)) :
    IndependentRandomElements P X ↔
      ∀ s : Finset I,
        Ch01.jointLaw P (fun i : s => X i) =
          Measure.pi (fun i : s => Ch01.law P (X i)) := by
  rw [independentRandomElements_iff_iIndepFun, ProbabilityTheory.iIndepFun_iff_finset]
  apply forall_congr'
  intro s
  exact ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i : s => (hX i).aemeasurable)

end ProbabilityFoundations.Ch02
