import MathGenome.Internal.Specs.D07.Ch15.SolvableGroups
import MathGenome.Internal.D07.Ch15.SolvableClosure
import MathGenome.Internal.D07.Ch06.SimpleGroupsBoundary
import Mathlib.GroupTheory.QuotientGroup.Simple
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.Atoms.Finite

/-!
Solvability and prime cyclic subnormal series, K07.15.solvable_groups.
The finite forward direction repeatedly takes a maximal subgroup containing
the commutator. This subgroup is normal; its quotient is simple and solvable,
hence finite cyclic of prime order. Well-founded induction on subgroups builds
the chain, including the zero-length trivial case. The reverse direction uses
the accepted extension theorem, with normality only in the adjacent term.
-/

namespace D07.Ch15.SolvableGroups

open Specs.D07.Ch15.SolvableGroups

universe u

theorem derived_zero : DerivedZero.{u} := fun _ _ => rfl

theorem derived_successor : DerivedSuccessor.{u} := fun _ _ _ => rfl

theorem solvable_iff_derived_terminates : SolvableIffDerivedTerminates.{u} :=
  fun G _ => Group.isSolvable_def G

theorem abelian_derived_one : AbelianDerivedOne.{u} := by
  intro G _ hcomm
  let : IsMulCommutative G := ⟨⟨hcomm⟩⟩
  exact le_bot_iff.mp (Abelianization.commutator_subset_ker (MonoidHom.id G))

theorem abelian_solvable : AbelianSolvable.{u} := by
  intro G _ hcomm
  exact ⟨⟨1, abelian_derived_one G hcomm⟩⟩

theorem symmetric_five_not_solvable : SymmetricFiveNotSolvable :=
  Equiv.Perm.not_isSolvable_fin_5

theorem symmetric_not_solvable : SymmetricNotSolvable := by
  intro n hn
  apply Equiv.Perm.not_isSolvable
  simpa using hn

/-- A maximal subgroup containing the commutator gives a prime cyclic quotient. -/
theorem exists_prime_cyclic_quotient (G : Type u) [Group G] [Finite G]
    [Nontrivial G] [Group.IsSolvable G] :
    ∃ M : Subgroup G, M ≠ ⊤ ∧ ∃ hM : M.Normal,
      letI := hM
      IsCyclic (G ⧸ M) ∧ (Nat.card (G ⧸ M)).Prime := by
  classical
  obtain ⟨M, hcoatom, hcomm⟩ := (eq_top_or_exists_le_coatom (commutator G)).resolve_left
    (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial G))
  have : M.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp
    (Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl le_top).trans hcomm)))
  have : IsSimpleGroup (G ⧸ M) := Group.isSimpleGroup_of_isCoatom hcoatom
  have hQcomm : ∀ x y : G ⧸ M, x * y = y * x :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  obtain ⟨hcyclic, hprime⟩ :=
    (D07.Ch06.SimpleGroupsBoundary.finite_simple_abelian_classification (G ⧸ M)).mp
      ⟨inferInstance, hQcomm⟩
  exact ⟨M, hcoatom.1, inferInstance, hcyclic, hprime⟩

/-- Build a subnormal prime cyclic chain inside an arbitrary solvable subgroup.
Induction is on the finite ambient subgroup lattice; the last step is the
prime cyclic quotient furnished by `exists_prime_cyclic_quotient`. -/
theorem exists_series_to_subgroup (G : Type u) [Group G] [Finite G]
    (H : Subgroup G) : Group.IsSolvable H →
    ∃ (n : ℕ) (K : ℕ → Subgroup G),
      K 0 = ⊥ ∧ K n = H ∧ ∀ i < n, PrimeCyclicStep (K i) (K (i + 1)) := by
  classical
  induction H using WellFoundedLT.induction with
  | ind H ih =>
    intro hsolv
    by_cases hbot : H = ⊥
    · exact ⟨0, fun _ => ⊥, rfl, hbot.symm, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
    have : Group.IsSolvable H := hsolv
    have : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hbot
    obtain ⟨M, hM, hnormal, hcyclic, hprime⟩ := exists_prime_cyclic_quotient H
    let N : Subgroup G := M.map H.subtype
    have hNH : N < H := by
      simpa only [Subgroup.map_top, Subgroup.range_subtype] using
        (Subgroup.map_subtype_lt_map_subtype (G' := H)).mpr (lt_top_iff_ne_top.mpr hM)
    have hNsolv : Group.IsSolvable N :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hNH.le) (Subgroup.inclusion_injective hNH.le)
    have hNof : N.subgroupOf H = M :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective M
    have hstep : PrimeCyclicStep N H := by
      refine ⟨hNH.le, ?_⟩
      rw [hNof]
      exact ⟨hnormal, hcyclic, hprime⟩
    obtain ⟨n, K, hK0, hKn, hKstep⟩ := ih N hNH hNsolv
    let J : ℕ → Subgroup G := fun i => if i ≤ n then K i else H
    refine ⟨n + 1, J, ?_, ?_, ?_⟩
    · simpa [J] using hK0
    · simp [J]
    · intro i hi
      by_cases hin : i < n
      · simpa [J, Nat.le_of_lt hin, Nat.succ_le_of_lt hin] using
          hKstep i hin
      · have hieq : i = n := le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_gt hin)
        subst i
        simpa [J, hKn] using hstep

theorem finite_solvable_iff_prime_cyclic_series :
    FiniteSolvableIffPrimeCyclicSeries.{u} := by
  intro G _ _
  constructor
  · intro hsolv
    obtain ⟨n, H, h0, hn, hstep⟩ := exists_series_to_subgroup G ⊤
      (D07.Ch15.SolvableClosure.subgroup_solvable G ⊤ hsolv)
    exact ⟨n, H, h0, hn, hstep⟩
  · rintro ⟨n, H, h0, hn, hstep⟩
    let hNormal : ∀ i < n, ((H i).subgroupOf (H (i + 1))).Normal :=
      fun i hi => (hstep i hi).2.choose
    apply D07.Ch15.SolvableClosure.subnormal_series_solvable G n H h0 hn
      (fun i hi => (hstep i hi).1) hNormal
    intro i hi
    have := hNormal i hi
    have : IsCyclic (H (i + 1) ⧸ (H i).subgroupOf (H (i + 1))) :=
      (hstep i hi).2.choose_spec.1
    infer_instance

end D07.Ch15.SolvableGroups
