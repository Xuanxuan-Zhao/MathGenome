import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.ConvexProgramModels
import Mathlib.Tactic.Linarith

noncomputable section
open Set
open scoped BigOperators
universe u v w z
namespace VariationalNotes.Ch04

abbrev ConvexProgram := ConvexProgramSpecs.ConvexProgram
abbrev Multipliers := ConvexProgramSpecs.Multipliers

abbrev commonDomain := @ConvexProgramSpecs.commonDomain

abbrev affinePolyhedron := @ConvexProgramSpecs.affinePolyhedron

abbrev feasibleSet := @ConvexProgramSpecs.feasibleSet

abbrev admissible := @ConvexProgramSpecs.admissible

abbrev lagrangianReal := @ConvexProgramSpecs.lagrangianReal

abbrev lagrangian := @ConvexProgramSpecs.lagrangian

/-- Primal value of the finite convex program; distinguished from the
perturbation model's primal value in the same chapter. -/
abbrev convexProgramPrimalValue := @ConvexProgramSpecs.primalValue

abbrev dualFunction := @ConvexProgramSpecs.dualFunction

abbrev dualValue := @ConvexProgramSpecs.dualValue

abbrev IsDualMaximizer := @ConvexProgramSpecs.IsDualMaximizer

abbrev complementarity := @ConvexProgramSpecs.complementarity

abbrev IsPrimalMinimizer := @ConvexProgramSpecs.IsPrimalMinimizer

abbrev IsLagrangianMinimizer := @ConvexProgramSpecs.IsLagrangianMinimizer

abbrev KKTConditions := @ConvexProgramSpecs.KKTConditions

theorem commonDomain_finite : ConvexProgramSpecs.commonDomain_finite.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p x hx
  have finite_real (r : WithTop ℝ) (h : r < ⊤) :
      r = (WithTop.untopD (α := ℝ) 0 r : WithTop ℝ) := by
    obtain ⟨t, rfl⟩ := WithTop.ne_top_iff_exists.mp h.ne
    rfl
  exact ⟨finite_real _ hx.1, fun i => finite_real _ (hx.2 i)⟩

theorem affinePolyhedron_isPolyhedron : ConvexProgramSpecs.affinePolyhedron_isPolyhedron.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p
  classical
  let ai : A → X →ᵃ[ℝ] ℝ := fun l => p.a l - AffineMap.const ℝ X (p.b l)
  let ej : J → X →ᵃ[ℝ] ℝ := fun j => p.e j - AffineMap.const ℝ X (p.d j)
  let nej : J → X →ᵃ[ℝ] ℝ := fun j => AffineMap.const ℝ X (p.d j) - p.e j
  refine ⟨Finset.univ.image ai ∪ (Finset.univ.image ej ∪ Finset.univ.image nej), ?_⟩
  ext x
  simp only [ConvexProgramSpecs.affinePolyhedron, mem_ofPred_eq, Finset.forall_mem_union,
    Finset.forall_mem_image, Finset.mem_univ, forall_const, ai, ej, nej,
    AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply, sub_nonpos]
  constructor
  · rintro ⟨ha, he⟩
    exact ⟨ha, ⟨fun j => (he j).le, fun j => (he j).ge⟩⟩
  · rintro ⟨ha, he, hne⟩
    exact ⟨ha, fun j => le_antisymm (@he j) (@hne j)⟩

theorem lagrangian_on_domain : ConvexProgramSpecs.lagrangian_on_domain.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p m x hx
  simp only [ConvexProgramSpecs.lagrangian, ite_eq_left hx]

theorem lagrangian_outside_domain : ConvexProgramSpecs.lagrangian_outside_domain.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p m x hx
  simp only [ConvexProgramSpecs.lagrangian, ite_eq_right hx]

theorem lagrangian_formula : ConvexProgramSpecs.lagrangian_formula.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p m x hx
  rw [lagrangian_on_domain p m x hx]
  obtain ⟨hf, hg⟩ := commonDomain_finite p x hx
  simp only [ConvexProgramSpecs.lagrangianReal, WithTop.coe_add, WithTop.coe_sum, WithTop.coe_mul]
  rw [hf]
  simp only [WithTop.untopD_coe]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  rw [hg i]
  rfl

theorem lagrangian_le_objective : ConvexProgramSpecs.lagrangian_le_objective.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p m x hm hx
  obtain ⟨hf, hg⟩ := commonDomain_finite p x hx.1
  have hgi (i : I) : (WithTop.untopD (α := ℝ) 0 (p.g i x)) ≤ 0 := by
    have h := hx.2.2 i
    rw [hg i] at h
    exact WithTop.coe_le_coe.mp h
  have hs : (∑ i, m.lam i * (WithTop.untopD (α := ℝ) 0 (p.g i x))) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hm.1 i) (hgi i))
  have ha : (∑ l, m.mu l * (p.a l x - p.b l)) ≤ 0 :=
    Finset.sum_nonpos (fun l _ => mul_nonpos_of_nonneg_of_nonpos (hm.2 l)
      (sub_nonpos.mpr (hx.2.1.1 l)))
  have he : (∑ j, m.nu j * (p.e j x - p.d j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hx.2.1.2 j, sub_self, mul_zero]
  dsimp [ConvexProgramSpecs.lagrangianReal]
  rw [he, add_zero]
  linarith

theorem weak_duality_point : ConvexProgramSpecs.weak_duality_point.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p m x hm hx
  have hf := (commonDomain_finite p x hx.1).1
  have hle := lagrangian_le_objective p m x hm hx
  change (⨅ y : ConvexProgramSpecs.commonDomain p, (ConvexProgramSpecs.lagrangianReal p m y : EReal)) ≤ _
  apply (iInf_le _ ⟨x, hx.1⟩).trans
  rw [hf]
  exact EReal.coe_le_coe hle

theorem weak_duality : ConvexProgramSpecs.weak_duality.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p m hm
  apply le_iInf
  intro x
  exact weak_duality_point p m x hm x.property

theorem dualValue_le_primalValue : ConvexProgramSpecs.dualValue_le_primalValue.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p
  apply iSup_le
  intro m
  exact weak_duality p m m.property

theorem dualFunction_eq_inf_extended : ConvexProgramSpecs.dualFunction_eq_inf_extended.{u,v,w,z} := by
  intro X _ _ I A J _ _ _ p m
  classical
  apply le_antisymm
  · apply le_iInf
    intro x
    by_cases hx : x ∈ ConvexProgramSpecs.commonDomain p
    · rw [lagrangian_on_domain p m x hx]
      exact iInf_le (fun y : ConvexProgramSpecs.commonDomain p => (ConvexProgramSpecs.lagrangianReal p m y : EReal)) ⟨x, hx⟩
    · rw [lagrangian_outside_domain p m x hx]
      exact le_top
  · apply le_iInf
    intro x
    have h := iInf_le (fun y : X =>
      VariationalNotes.ConvexAnalysis.Specs.toEReal (ConvexProgramSpecs.lagrangian p m y)) x.val
    rw [lagrangian_on_domain p m x.val x.property] at h
    exact h

end VariationalNotes.Ch04
