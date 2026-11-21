import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Density.FiniteQuotient
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Density.FiniteRankModule
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Data.Finset.Max

universe u v

namespace RM03.Density.ProperExample

open FiniteRankModule

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

/-- Pointwise convergence on the discrete vector space. -/
@[instance_reducible]
def finiteTopology : TopologicalSpace (Module.End k V) :=
  letI : TopologicalSpace V := ⊥
  TopologicalSpace.induced (fun T : Module.End k V ↦ (T : V → V)) inferInstance

/-- The linear operator shifting the basis forward by one. -/
noncomputable def shift (b : Module.Basis ℕ k V) : Module.End k V :=
  b.constr k (fun i ↦ b (i + 1))

@[simp]
theorem shift_apply (b : Module.Basis ℕ k V) (i : ℕ) :
    shift k V b (b i) = b (i + 1) :=
  b.constr_basis k _ i

private theorem coord_shift_succ (b : Module.Basis ℕ k V) (i : ℕ) (x : V) :
    b.coord (i + 1) (shift k V b x) = b.coord i x := by
  have h : (b.coord (i + 1)).comp (shift k V b) = b.coord i := by
    apply b.ext
    intro j
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  exact LinearMap.congr_fun h x

/-- The highest nonzero coordinate of a vector shifts beyond every coordinate of its scalar multiple. -/
private theorem shift_sub_scalar_injective (b : Module.Basis ℕ k V) (c : k) :
    Function.Injective (shift k V b - algebraMap k (Module.End k V) c) := by
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro x hx
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, b.repr x j ≠ 0 := by
    by_contra! hz
    exact hne (b.repr.injective (Finsupp.ext fun j ↦ by simpa using hz j))
  have hs : (b.repr x).support.Nonempty := ⟨j, Finsupp.mem_support_iff.mpr hj⟩
  let i := (b.repr x).support.max' hs
  have hi : b.repr x i ≠ 0 :=
    Finsupp.mem_support_iff.mp (Finset.max'_mem _ hs)
  have hi' : b.repr x (i + 1) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    exact (Nat.not_succ_le_self i) (Finset.le_max' _ _ hmem)
  have hcoord := congrArg (b.coord (i + 1)) hx
  simp only [LinearMap.sub_apply, Module.algebraMap_end_apply, map_sub, map_smul,
    map_zero] at hcoord
  rw [coord_shift_succ, Module.Basis.coord_apply, Module.Basis.coord_apply,
    hi', smul_zero, sub_zero] at hcoord
  exact hi hcoord

theorem shift_sub_scalar_infinite_rank (b : Module.Basis ℕ k V) (c : k) :
    ¬ FiniteDimensional k (shift k V b - algebraMap k (Module.End k V) c).range := by
  intro h
  let f := shift k V b - algebraMap k (Module.End k V) c
  have : FiniteDimensional k V := FiniteDimensional.of_injective f.rangeRestrict
    (fun _ _ heq ↦ shift_sub_scalar_injective k V b c (congrArg Subtype.val heq))
  exact (Module.Finite.finite_basis b).false

theorem shift_not_mem (b : Module.Basis ℕ k V) :
    shift k V b ∉ scalarPlusFiniteRank k V := by
  intro h
  obtain ⟨c, f, hf, heq⟩ := (mem_scalarPlusFiniteRank k V _).mp h
  apply shift_sub_scalar_infinite_rank k V b c
  rw [heq, add_sub_cancel_left]
  exact (mem_finiteRankIdeal k V f).mp hf

local notation "R" => scalarPlusFiniteRank k V

theorem scalarPlusFiniteRank_lt_top (b : Module.Basis ℕ k V) : R < ⊤ := by
  refine lt_top_iff_ne_top.mpr (fun h ↦ shift_not_mem k V b ?_)
  rw [h]
  trivial

theorem action_image_dense (b : Module.Basis ℕ k V) :
    letI : TopologicalSpace (Module.End k V) := finiteTopology k V
    ∃ e : RightEnd R V ≃ₐ[k] Module.End k V,
      (∀ (T : RightEnd R V) (x : V), e T x = T x) ∧
      e '' Set.range (action R V) = (R : Set (Module.End k V)) ∧
      Dense (R : Set (Module.End k V)) := by
  let : TopologicalSpace (Module.End k V) := finiteTopology k V
  let : TopologicalSpace (RightEnd R V) := RM03.Density.finiteTopology R V
  let : TopologicalSpace V := ⊥
  have : IsSimpleModule R V := simple k V b
  obtain ⟨e, heval, haction⟩ := rightEndEquiv_exists k V b
  have hImage : e '' Set.range (action R V) = (R : Set (Module.End k V)) := by
    rw [← Set.range_comp']
    simp_rw [haction]
    exact Subtype.range_coe
  have he : Continuous e := by
    rw [continuous_induced_rng]
    have hcomp : (fun T : Module.End k V ↦ (T : V → V)) ∘ e =
        fun T : RightEnd R V ↦ (T : V → V) :=
      funext fun T ↦ funext (heval T)
    rw [hcomp]
    exact continuous_induced_dom
  refine ⟨e, heval, hImage, ?_⟩
  rw [← hImage]
  exact e.surjective.denseRange.dense_image he (action_dense R V)

end RM03.Density.ProperExample
