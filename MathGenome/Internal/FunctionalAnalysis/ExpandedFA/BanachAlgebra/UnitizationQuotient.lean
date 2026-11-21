import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.UnitizationQuotient
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Conventions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientNorm
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
The ℓ¹ unitization and the quotient of a possibly nonunital Banach algebra.
The quotient uses the accepted distance norm on the original submodule
quotient. In particular, the whole ideal and the zero input are included.
-/

noncomputable section

namespace ExpandedFA.BanachAlgebra.UnitizationQuotient

open Specs.ExpandedFA.BanachAlgebra.UnitizationQuotient

universe u

theorem unitization_formulas : UnitizationFormulas.{u} := by
  intro A _ _ _ _
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩
  · constructor
    · intro x y h
      have hs := congrArg (fun z => (WithLp.ofLp z).fst) h
      have ha := congrArg (fun z => (WithLp.ofLp z).snd) h
      exact Prod.ext ha hs
    · intro x
      exact ⟨⟨(WithLp.ofLp x).snd, (WithLp.ofLp x).fst⟩, rfl⟩
  · intro a b s t
    apply (WithLp.equiv 1 (Unitization ℂ A)).injective
    apply Unitization.ext <;> simp [pair, Unitization.snd_mul, add_comm, add_assoc]
  · intro a s
    simpa [pair, add_comm] using WithLp.unitization_norm_def (pair a s)
  · intro a b s t
    rfl
  · intro c a s
    rfl

theorem unitization_banach : UnitizationBanach.{u} := by
  intro A _ _ _ _ hA
  let : CompleteSpace A := hA
  exact ⟨inferInstance, inferInstance, inferInstance⟩

section Quotient

variable {A : Type u} [NonUnitalNormedRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  (I : Submodule ℂ A) (hideal : IsTwoSidedIdeal I)

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] in
include hideal in
private theorem product_congr {a b c d : A}
    (hab : a - b ∈ I) (hcd : c - d ∈ I) :
    I.mkQ (a * c) = I.mkQ (b * d) := by
  apply (Submodule.Quotient.eq I).mpr
  have hid : a * c - b * d = a * (c - d) + (a - b) * d := by
    rw [mul_sub, sub_mul]
    abel
  rw [hid]
  exact I.add_mem (hideal.1 a (c - d) hcd) (hideal.2 (a - b) d hab)

/-- Multiplication descends using both absorbing properties of the ideal. -/
private def quotientProduct (x y : A ⧸ I) : A ⧸ I :=
  Quotient.liftOn₂ x y (fun a b => I.mkQ (a * b)) (by
    intro a b c d hab hcd
    exact product_congr I hideal ((I.quotientRel_def).mp hab) ((I.quotientRel_def).mp hcd))

private theorem quotientProduct_mk (a b : A) :
    quotientProduct I hideal (I.mkQ a) (I.mkQ b) = I.mkQ (a * b) := rfl

/-- Approximate lifts in each variable give the product norm estimate;
no minimum-norm representative is assumed. -/
private theorem quotientProduct_norm (x y : A ⧸ I) :
    ‖quotientProduct I hideal x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hcont := ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
    Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
  simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at hcont
  obtain ⟨δ₁, δ₂, ⟨hδ₁, hδ₂⟩, hbound⟩ := hcont
  obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hδ₁
  obtain ⟨b, rfl, hb⟩ := Submodule.Quotient.norm_mk_lt y hδ₂
  simp only [Real.dist_eq, abs_sub_lt_iff] at hbound
  specialize hbound ‖a‖ ‖b‖
    ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le I a]⟩
    ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le I b]⟩
  calc
    ‖quotientProduct I hideal (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)‖
        ≤ ‖a‖ * ‖b‖ :=
      (Submodule.Quotient.norm_mk_le I (a * b)).trans (norm_mul_le a b)
    _ ≤ _ := (sub_lt_iff_lt_add'.mp hbound.1).le

private theorem quotientProduct_laws : QuotientAlgebraLaws I (quotientProduct I hideal) := by
  refine ⟨quotientProduct_mk I hideal, ?_, ?_, ?_, ?_, ?_, ?_,
    quotientProduct_norm I hideal⟩
  · intro x y z
    obtain ⟨a, rfl⟩ := I.mkQ_surjective x
    obtain ⟨b, rfl⟩ := I.mkQ_surjective y
    obtain ⟨c, rfl⟩ := I.mkQ_surjective z
    simp only [quotientProduct_mk, mul_assoc]
  · intro x y z
    obtain ⟨a, rfl⟩ := I.mkQ_surjective x
    obtain ⟨b, rfl⟩ := I.mkQ_surjective y
    obtain ⟨c, rfl⟩ := I.mkQ_surjective z
    rw [← map_add, quotientProduct_mk, add_mul, map_add]
    rfl
  · intro x y z
    obtain ⟨a, rfl⟩ := I.mkQ_surjective x
    obtain ⟨b, rfl⟩ := I.mkQ_surjective y
    obtain ⟨c, rfl⟩ := I.mkQ_surjective z
    rw [← map_add, quotientProduct_mk, mul_add, map_add]
    rfl
  · intro x
    obtain ⟨a, rfl⟩ := I.mkQ_surjective x
    change I.mkQ (0 * a) = 0 ∧ I.mkQ (a * 0) = 0
    simp
  · intro c x y
    obtain ⟨a, rfl⟩ := I.mkQ_surjective x
    obtain ⟨b, rfl⟩ := I.mkQ_surjective y
    rw [← map_smul, quotientProduct_mk, smul_mul_assoc, map_smul]
    rfl
  · intro c x y
    obtain ⟨a, rfl⟩ := I.mkQ_surjective x
    obtain ⟨b, rfl⟩ := I.mkQ_surjective y
    rw [← map_smul, quotientProduct_mk, mul_smul_comm, map_smul]
    rfl

/-- Package the descended multiplication with exactly the native quotient
additive group and metric. -/
private abbrev quotientNormedRing (hclosed : IsClosed (I : Set A)) :
    NonUnitalNormedRing (A ⧸ I) := by
  letI : IsClosed (I : Set A) := hclosed
  have hlaws := quotientProduct_laws I hideal
  exact
    { Submodule.Quotient.normedAddCommGroup I with
      mul := quotientProduct I hideal
      mul_assoc := hlaws.2.1
      right_distrib := hlaws.2.2.1
      left_distrib := hlaws.2.2.2.1
      zero_mul := fun x => (hlaws.2.2.2.2.1 x).1
      mul_zero := fun x => (hlaws.2.2.2.2.1 x).2
      dist_eq := dist_eq_norm_neg_add
      norm_mul_le := quotientProduct_norm I hideal }

end Quotient

theorem quotient_banach : QuotientBanach.{u} := by
  intro A _ _ _ _ I hideal hclosed hA
  refine ⟨⟨quotientProduct I hideal, quotientProduct_laws I hideal, ?_⟩, ?_, ?_⟩
  · exact ⟨quotientNormedRing I hideal hclosed, rfl, rfl, rfl, rfl⟩
  · exact P1.C02QuotientComplete.quotient_complete ℂ A I hclosed
      ((P1.C01Banach.isBanachSpace_iff_completeSpace A).mpr hA)
  · intro a
    exact (P1.C02QuotientNorm.distanceSeminorm_mk ℂ A I a).1

end ExpandedFA.BanachAlgebra.UnitizationQuotient
