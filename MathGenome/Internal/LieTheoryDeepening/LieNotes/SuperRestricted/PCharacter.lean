import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.PCharacter
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.ReducedPbw
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Batteries.Tactic.OpenPrivate

/-! Existence and uniqueness of the p-character, and restriction of simple reduced modules. -/

namespace LieNotes.SuperRestricted.PCharacter

open _root_.Shared.Lie (U inclusion)
open _root_.Specs.LieNotes.SuperRestricted.PCharacter
open ReducedEnveloping RestrictedCenter RestrictedLie ReducedPbw

open private adjoin_range_inclusion from MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedCenter

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
  {G : Type v} [LieRing G] [LieAlgebra k G] {M : Type w} [AddCommGroup M]

section EnvelopingAction

variable [Module k M]

private theorem central_action_scalar [IsAlgClosed k] [Module.Finite k M]
    [LieRingModule G M] [LieModule k G M] [IsSimpleOrder (LieSubmodule k G M)]
    (power : RestrictedPower k p G) (x : G) :
    ∃ c : k, UniversalEnvelopingAlgebra.lift k (LieModule.toEnd k G M)
      (pCenterElement power x) = algebraMap k (Module.End k M) c := by
  let : Nontrivial M := (LieSubmodule.nontrivial_iff k G M).mp inferInstance
  let ρ : U k G →ₐ[k] Module.End k M := UniversalEnvelopingAlgebra.lift k (LieModule.toEnd k G M)
  let T := ρ (pCenterElement power x)
  obtain ⟨c, hc⟩ := T.exists_eigenvalue
  let N : LieSubmodule k G M :=
    { T.eigenspace c with
      lie_mem := by
        intro y m hm
        change m ∈ T.eigenspace c at hm
        have hcomm := (pCenterElement_commute power x (inclusion k G y)).map ρ
        have hι : ρ (inclusion k G y) = LieModule.toEnd k G M y :=
          UniversalEnvelopingAlgebra.lift_ι_apply k _ y
        change LieModule.toEnd k G M y m ∈ T.eigenspace c
        rw [← hι, Module.End.mem_eigenspace_iff]
        have he := congrArg (fun e : Module.End k M => e m) hcomm.eq
        change T (ρ (inclusion k G y) m) = ρ (inclusion k G y) (T m) at he
        rw [he, Module.End.mem_eigenspace_iff.mp hm, map_smul] }
  have hN : N = ⊤ := (eq_bot_or_eq_top N).resolve_left fun h =>
    hc (congrArg LieSubmodule.toSubmodule h)
  refine ⟨c, LinearMap.ext fun m => ?_⟩
  have hm : m ∈ N := hN ▸ LieSubmodule.mem_top m
  exact Module.End.mem_eigenspace_iff.mp (show m ∈ T.eigenspace c from hm)

private theorem factor_of_basis_relations {n : ℕ} (b : Module.Basis (Fin n) k G)
    (power : RestrictedPower k p G) (χ : G →ₗ[k] k) (ρ : U k G →ₐ[k] Module.End k M)
    (h : ∀ i, ρ (pCenterElement power (b i)) = algebraMap k (Module.End k M) (χ (b i) ^ p)) :
    ∃ F : ReducedEnvelopingAlgebra power χ →ₐ[k] Module.End k M,
      F.comp (quotientMap power χ) = ρ := by
  have hkill (a : U k G) (ha : a ∈ reducedRelations power χ) : ρ a = 0 := by
    rw [reducedRelations_eq_span_basis power b χ, TwoSidedIdeal.mem_asIdeal] at ha
    apply (TwoSidedIdeal.mem_ker ρ).mp
    refine (TwoSidedIdeal.span_le.mpr ?_) ha
    rintro _ ⟨i, rfl⟩
    apply (TwoSidedIdeal.mem_ker ρ).mpr
    rw [map_sub, AlgHom.commutes, h i, sub_self]
  exact ⟨Ideal.Quotient.liftₐ (reducedRelations power χ) ρ hkill,
    Ideal.Quotient.liftₐ_comp _ _ _⟩

private theorem character_unique [Nontrivial M] (power : RestrictedPower k p G)
    (ρ : U k G →ₐ[k] Module.End k M) {χ ψ : G →ₗ[k] k}
    (F : ReducedEnvelopingAlgebra power χ →ₐ[k] Module.End k M)
    (H : ReducedEnvelopingAlgebra power ψ →ₐ[k] Module.End k M)
    (hF : F.comp (quotientMap power χ) = ρ) (hH : H.comp (quotientMap power ψ) = ρ) :
    ψ = χ := by
  let : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have scalar_of_factor (η : G →ₗ[k] k)
      (A : ReducedEnvelopingAlgebra power η →ₐ[k] Module.End k M)
      (hA : A.comp (quotientMap power η) = ρ) (x : G) :
      ρ (pCenterElement power x) = algebraMap k (Module.End k M) (η x ^ p) := by
    rw [← hA, AlgHom.comp_apply, (quotientMap_spec power η).2.2, AlgHom.commutes]
  ext x
  apply frobenius_inj k p
  apply (algebraMap k (Module.End k M)).injective
  exact (scalar_of_factor ψ H hH x).symm.trans (scalar_of_factor χ F hF x)

end EnvelopingAction

/-- Every finite-dimensional simple ordinary Lie module has a unique p-character. -/
theorem existsUnique_pCharacter : existsUnique_pCharacterType.{u,v,w} := by
  intro k _ _ p _ _ G _ _ _ power M _ _ _ _ _ _
  let : Nontrivial M := (LieSubmodule.nontrivial_iff k G M).mp inferInstance
  let b := Module.finBasis k G
  let ρ : U k G →ₐ[k] Module.End k M := UniversalEnvelopingAlgebra.lift k (LieModule.toEnd k G M)
  have hroot (i : Fin (Module.finrank k G)) :
      ∃ a : k, ρ (pCenterElement power (b i)) = algebraMap k (Module.End k M) (a ^ p) := by
    obtain ⟨c, hc⟩ := central_action_scalar (M := M) power (b i)
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c (NeZero.pos p)
    exact ⟨a, ha.symm ▸ hc⟩
  choose a ha using hroot
  let χ : G →ₗ[k] k := b.constr k a
  have hχ (i : Fin (Module.finrank k G)) : χ (b i) = a i := b.constr_basis k _ _
  obtain ⟨F, hF⟩ := factor_of_basis_relations b power χ ρ fun i => by rw [hχ, ha]
  refine ⟨χ, ⟨F, hF⟩, ?_⟩
  rintro ψ ⟨H, hH⟩
  exact character_unique power ρ F H hF hH

private theorem stable_under_enveloping [Module k M]
    (ρ : U k G →ₐ[k] Module.End k M) (N : Submodule k M)
    (hN : ∀ (x : G) (m : M), m ∈ N → ρ (inclusion k G x) m ∈ N)
    (a : U k G) (m : M) (hm : m ∈ N) : ρ a m ∈ N := by
  have ha : a ∈ Algebra.adjoin k (Set.range (inclusion k G)) := by
    rw [adjoin_range_inclusion]
    exact Algebra.mem_top
  revert m hm
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact hN y
  | algebraMap c =>
    intro m hm
    rw [AlgHom.commutes]
    exact N.smul_mem c hm
  | add a b _ _ ha hb =>
    intro m hm
    rw [map_add, LinearMap.add_apply]
    exact N.add_mem (ha m hm) (hb m hm)
  | mul a b _ _ ha hb =>
    intro m hm
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hb m hm)

/-- Simple modules over the reduced quotient restrict to finite-dimensional simple Lie modules. -/
theorem simple_restrict_pCharacter : simple_restrict_pCharacterType.{u,v,w} := by
  intro k _ p _ _ G _ _ _ power χ Q M _ _ _
  let : Module k M := Module.restrictScalars k Q M
  let : IsScalarTower k Q M := IsScalarTower.restrictScalars k Q M
  let A : Q →ₐ[k] Module.End k M := Algebra.lsmul k k M
  let ρ := A.comp (quotientMap power χ)
  let f := ρ.toLieHom.comp (inclusion k G)
  let : LieRingModule G M := LieRingModule.compLieHom M f
  let : LieModule k G M := LieModule.compLieHom M f
  let : Nontrivial M := IsSimpleModule.nontrivial Q M
  have hρ : UniversalEnvelopingAlgebra.lift k (LieModule.toEnd k G M) = ρ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x m
    rw [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  have hcyclic (m : M) (hm : m ≠ 0) : Function.Surjective fun a : Q => A a m :=
    IsSimpleModule.toSpanSingleton_surjective Q hm
  refine ⟨?_, ?_, ?_⟩
  · let : Module.Finite k Q := (reducedFinrank power χ).1
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    exact Module.Finite.of_surjective ((LinearMap.applyₗ m).comp A.toLinearMap) (hcyclic m hm)
  · apply IsSimpleOrder.of_forall_eq_top
    intro N hN
    have hN' : N.toSubmodule ≠ ⊥ := fun h => hN ((LieSubmodule.toSubmodule_inj N ⊥).mp h)
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'
    apply top_unique
    intro v _
    obtain ⟨a, rfl⟩ := hcyclic m hm0 v
    obtain ⟨b, rfl⟩ := (quotientMap_spec power χ).1 a
    exact stable_under_enveloping ρ N.toSubmodule (fun x _ hn => N.lie_mem (x := x) hn) b m hm
  · intro ψ
    change (∃ F : ReducedEnvelopingAlgebra power ψ →ₐ[k] Module.End k M,
        F.comp (quotientMap power ψ) = UniversalEnvelopingAlgebra.lift k (LieModule.toEnd k G M)) ↔
      ψ = χ
    rw [hρ]
    constructor
    · rintro ⟨F, hF⟩
      exact character_unique power ρ A F rfl hF
    · rintro rfl
      exact ⟨A, rfl⟩

end LieNotes.SuperRestricted.PCharacter
