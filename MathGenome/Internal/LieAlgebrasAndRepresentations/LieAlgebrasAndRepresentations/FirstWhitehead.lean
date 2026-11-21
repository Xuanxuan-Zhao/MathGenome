import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FirstWhitehead
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomologySequence

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open CategoryTheory
open AdvancedHomologicalAlgebra.CE AdvancedHomologicalAlgebra.CE.Ext
open LieAlgebrasAndRepresentations.SimpleCoefficientVanishing
open P103.Specs.Ch10.Complexes
open scoped TensorProduct
universe u v w

namespace LieAlgebrasAndRepresentations.FirstWhitehead
variable (k : Type u) (g : Type v) (M : Type w)
  [Field k] [LieRing g] [LieAlgebra k g]
  [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]

attribute [local instance] CentralActionHomotopy.coefficientModule
attribute [local instance 100] LieRing.ofAssociativeRing

lemma inclusion_smul (x : g) (m : M) :
    Shared.Lie.inclusion k g x • m = ⁅x,m⁆ := by
  change ModuleCasimir.action k g M (Shared.Lie.inclusion k g x) m = _
  have h := UniversalEnvelopingAlgebra.lift_ι_apply k (LieModule.toEnd k g M) x
  exact congrArg (fun f : Module.End k M => f m) h

variable [FiniteDimensional k g]

/-- The unsigned CE differential in degrees zero and one. -/
lemma coboundary_zero (f : W k g 0 →ₗ[k] M) (x : g) :
    coboundary k g M (boundary k g) 0 f (wedge k g 1 (fun _ => x)) =
      ⁅x, f (wedge k g 0 Fin.elim0)⁆ := by
  change (homEquiv k g M 0).symm f
    (boundary k g 0 ((1 : U k g) ⊗ₜ[k] wedge k g 1 (fun _ => x))) = _
  rw [boundary_one_formula k g _ (boundary_formula k g),
    homEquiv_symm_tmul, one_mul, inclusion_smul]

lemma coboundary_one (f : W k g 1 →ₗ[k] M) (x y : g) :
    coboundary k g M (boundary k g) 1 f (wedge k g 2 ![x,y]) =
      ⁅x, f (wedge k g 1 (fun _ => y))⁆ -
      ⁅y, f (wedge k g 1 (fun _ => x))⁆ -
      f (wedge k g 1 (fun _ => ⁅x,y⁆)) := by
  change (homEquiv k g M 1).symm f
    (boundary k g 1 ((1 : U k g) ⊗ₜ[k] wedge k g 2 ![x,y])) = _
  rw [boundary_two_formula k g _ (boundary_formula k g)]
  simp only [map_sub, homEquiv_symm_tmul, one_mul, one_smul, inclusion_smul]

/-- Encode an ordinary linear map as an exterior degree-one cochain. -/
def oneCochain (a : g →ₗ[k] M) : W k g 1 →ₗ[k] M :=
  a.comp (exteriorPower.oneEquiv k g).toLinearMap

@[simp] lemma oneCochain_wedge (a : g →ₗ[k] M) (x : Fin 1 → g) :
    oneCochain k g M a (wedge k g 1 x) = a (x 0) := by
  simp [oneCochain]

lemma oneCochain_cycle (a : g →ₗ[k] M)
    (ha : ∀ x y, a ⁅x,y⁆ = ⁅x,a y⁆ - ⁅y,a x⁆) :
    coboundary k g M (boundary k g) 1 (oneCochain k g M a) = 0 := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  change coboundary k g M (boundary k g) 1 (oneCochain k g M a)
    (wedge k g 2 x) = 0
  rw [hx, coboundary_one]
  simp only [oneCochain_wedge]
  rw [ha, sub_self]

/-- The canonical CE quotient vanishes exactly when all crossed homomorphisms
are inner. This also fixes the sign and includes zero coefficients. -/
lemma vanishing_iff_inner :
    Subsingleton (Homology (ceCochain k g M) 1) ↔
      ∀ a : g →ₗ[k] M,
        (∀ x y, a ⁅x,y⁆ = ⁅x,a y⁆ - ⁅y,a x⁆) →
        ∃ m : M, ∀ x, a x = ⁅x,m⁆ := by
  constructor
  · intro h a ha
    let z : cycles (ceCochain k g M) 1 :=
      ⟨oneCochain k g M a, by
        apply (P103.Ch10.HomologySequence.cycle_iff _
          (show (ComplexShape.up ℕ).Rel 1 2 from rfl) _).mpr
        exact oneCochain_cycle k g M a ha⟩
    have hz : z ∈ cycleBoundaries (ceCochain k g M) 1 :=
      (Submodule.Quotient.mk_eq_zero _).mp (h.elim _ 0)
    have hz' : z.val ∈ boundaries (ceCochain k g M) 1 := hz
    obtain ⟨f, hf⟩ := (P103.Ch10.HomologySequence.boundary_iff _
      (show (ComplexShape.up ℕ).Rel 0 1 from rfl) _).mp hz' 
    change coboundary k g M (boundary k g) 0 f = oneCochain k g M a at hf
    refine ⟨f (wedge k g 0 Fin.elim0), fun x => ?_⟩
    have hx := LinearMap.congr_fun hf (wedge k g 1 (fun _ => x))
    rw [coboundary_zero, oneCochain_wedge] at hx
    exact hx.symm
  · intro h
    apply Submodule.Quotient.subsingleton_iff.mpr
    apply top_unique
    intro z _
    let a : g →ₗ[k] M := z.val.comp (exteriorPower.oneEquiv k g).symm.toLinearMap
    have haz (x : g) : a x = z.val (wedge k g 1 (fun _ => x)) := rfl
    have ha : ∀ x y, a ⁅x,y⁆ = ⁅x,a y⁆ - ⁅y,a x⁆ := by
      intro x y
      have hz : coboundary k g M (boundary k g) 1 z.val = 0 :=
        (P103.Ch10.HomologySequence.cycle_iff _
          (show (ComplexShape.up ℕ).Rel 1 2 from rfl) _).mp z.property
      have he := LinearMap.congr_fun hz (wedge k g 2 ![x,y])
      rw [coboundary_one] at he
      simp only [LinearMap.zero_apply] at he
      simpa only [haz] using (sub_eq_zero.mp he).symm
    obtain ⟨m, hm⟩ := h a ha
    let f : W k g 0 →ₗ[k] M := (exteriorPower.zeroEquiv k g).toLinearMap.smulRight m
    change z.val ∈ boundaries (ceCochain k g M) 1
    apply (P103.Ch10.HomologySequence.boundary_iff _
      (show (ComplexShape.up ℕ).Rel 0 1 from rfl) _).mpr
    refine ⟨f, ?_⟩
    change coboundary k g M (boundary k g) 0 f = z.val
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change coboundary k g M (boundary k g) 0 f (wedge k g 1 x) =
      z.val (wedge k g 1 x)
    have hx : x = fun _ => x 0 := by ext i; fin_cases i; rfl
    rw [hx, coboundary_zero]
    change ⁅x 0, (exteriorPower.zeroEquiv k g (wedge k g 0 Fin.elim0)) • m⁆ = _
    rw [exteriorPower.zeroEquiv_ιMulti, one_smul, ← haz, hm]

variable [CharZero k]

/-- Perfectness handles every trivial coefficient module, without requiring
it to be one-dimensional or nonzero. -/
lemma inner_of_trivial [LieModule.IsTrivial g M]
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g)
    (a : g →ₗ[k] M) (ha : ∀ x y, a ⁅x,y⁆ = ⁅x,a y⁆ - ⁅y,a x⁆) :
    ∃ m : M, ∀ x, a x = ⁅x,m⁆ := by
  have hb (x y : g) : a ⁅x,y⁆ = 0 := by
    simp [ha, trivial_lie_zero]
  have hle : (⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆).toSubmodule ≤ a.ker := by
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span]
    apply Submodule.span_le.mpr
    rintro z ⟨x, y, rfl⟩
    exact hb x y
  rw [semisimple_perfect k g hg] at hle
  refine ⟨0, fun x => ?_⟩
  have hx : a x = 0 := hle (by trivial)
  simpa using hx

lemma inner_of_irreducible [FiniteDimensional k M] [LieModule.IsIrreducible k g M]
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g)
    (a : g →ₗ[k] M) (ha : ∀ x y, a ⁅x,y⁆ = ⁅x,a y⁆ - ⁅y,a x⁆) :
    ∃ m : M, ∀ x, a x = ⁅x,m⁆ := by
  classical
  by_cases ht : LieModule.IsTrivial g M
  · letI := ht
    exact inner_of_trivial k g M hg a ha
  · exact (vanishing_iff_inner k g M).mp
      (SimpleCoefficientVanishing.cohomology_vanishes k g M hg ht 1) a ha


/-- Induction on dimension implements the composition-series argument directly
on cocycles: after an inner correction in the quotient, the remaining cocycle
has values in the submodule. -/
lemma inner_of_finrank
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g)
    (n : ℕ) :
    ∀ (N : Type w) [AddCommGroup N] [Module k N] [FiniteDimensional k N]
      [LieRingModule g N] [LieModule k g N],
      Module.finrank k N = n → ∀ a : g →ₗ[k] N,
        (∀ x y, a ⁅x,y⁆ = ⁅x,a y⁆ - ⁅y,a x⁆) →
        ∃ m : N, ∀ x, a x = ⁅x,m⁆ := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro N _ _ _ _ _ hn a ha
    by_cases hz : Subsingleton N
    · letI := hz
      exact ⟨0, fun _ => Subsingleton.elim _ _⟩
    haveI : Nontrivial N := not_subsingleton_iff_nontrivial.mp hz
    by_cases hs : LieModule.IsIrreducible k g N
    · letI := hs
      exact inner_of_irreducible k g N hg a ha
    have hex : ∃ S : LieSubmodule k g N, S ≠ ⊥ ∧ S ≠ ⊤ := by
      by_contra! h
      apply hs
      exact LieModule.IsIrreducible.mk (fun S hS => h S hS)
    obtain ⟨S, hS0, hS1⟩ := hex
    have hdimS : Module.finrank k S < n := by
      rw [← hn]
      exact Submodule.finrank_lt (by
        intro he
        apply hS1
        exact LieSubmodule.toSubmodule_injective he)
    haveI : Nontrivial S := (LieSubmodule.nontrivial_iff_ne_bot k g N).mpr hS0
    have hdimQ : Module.finrank k (N ⧸ S) < n := by
      have hsum : Module.finrank k (N ⧸ S) + Module.finrank k S = n := by
        simpa only [hn] using! (Submodule.finrank_quotient_add_finrank S.toSubmodule)
      have hpos : 0 < Module.finrank k S := Module.finrank_pos
      omega
    let π := LieSubmodule.Quotient.mk' S
    let aq : g →ₗ[k] N ⧸ S := π.toLinearMap.comp a
    have haq : ∀ x y, aq ⁅x,y⁆ = ⁅x,aq y⁆ - ⁅y,aq x⁆ := by
      intro x y
      change π (a ⁅x,y⁆) = ⁅x,π (a y)⁆ - ⁅y,π (a x)⁆
      rw [ha, map_sub, π.map_lie, π.map_lie]
    obtain ⟨q, hq⟩ := ih _ hdimQ (N ⧸ S) rfl aq haq
    obtain ⟨m, hm⟩ := LieSubmodule.Quotient.surjective_mk' S q
    let b : g →ₗ[k] N := a - (LieModule.toEnd k g N).toLinearMap.flip m
    have hb (x : g) : b x ∈ S := by
      apply (LieSubmodule.Quotient.mk_eq_zero S).mp
      change π (a x - ⁅x,m⁆) = 0
      rw [map_sub, π.map_lie, hm]
      exact sub_eq_zero.mpr (hq x)
    let bs : g →ₗ[k] S := b.codRestrict S.toSubmodule hb
    have hbs : ∀ x y, bs ⁅x,y⁆ = ⁅x,bs y⁆ - ⁅y,bs x⁆ := by
      intro x y
      apply Subtype.ext
      change a ⁅x,y⁆ - ⁅⁅x,y⁆,m⁆ =
        ⁅x,a y - ⁅y,m⁆⁆ - ⁅y,a x - ⁅x,m⁆⁆
      rw [ha, lie_lie, lie_sub, lie_sub]
      abel
    obtain ⟨s, hs⟩ := ih _ hdimS S rfl bs hbs
    refine ⟨m + s.val, fun x => ?_⟩
    have hx := congrArg Subtype.val (hs x)
    change a x - ⁅x,m⁆ = ⁅x,s.val⁆ at hx
    rw [lie_add, ← hx]
    abel

/-- Whitehead's first lemma in its crossed-homomorphism formulation. -/
theorem cocycle_inner :
    Specs.LieAlgebrasAndRepresentations.FirstWhitehead.cocycle_inner_type.{u,v,w} := by
  intro k g M _ _ _ _ _ _ _ _ _ _ hg a ha
  exact inner_of_finrank k g hg (Module.finrank k M) M rfl a ha

/-- First cohomology of the actual exterior CE complex vanishes. -/
theorem cohomology_vanishes :
    Specs.LieAlgebrasAndRepresentations.FirstWhitehead.cohomology_vanishes_type.{u,v,w} := by
  intro k g M _ _ _ _ _ _ _ _ _ _ hg
  exact (vanishing_iff_inner k g M).mpr (cocycle_inner k g M hg)

end LieAlgebrasAndRepresentations.FirstWhitehead
