import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ParallelClasses
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.RankTwoBound
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic.NormNum

namespace FiniteCombinatorics.Matroid
open Set Submodule
universe u v w

/-- Distinct ground elements of a simple matroid form an independent pair. -/
theorem indep_pair_of_simple {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (hn : ∀ e ∈ M.E, M.IsNonloop e)
    (hp : ∀ e ∈ M.E, ∀ f ∈ M.E, ParallelRelated M e f → e = f)
    {e f : α} (he : e ∈ M.E) (hf : f ∈ M.E) (hef : e ≠ f) :
    M.Indep {e, f} := by
  by_contra h
  have hc := ((hn e he).closure_eq_closure_iff_eq_or_dep (hn f hf)).mpr (Or.inr h)
  exact hef (hp e he f hf ((parallelClosure M (hn e he) (hn f hf)).mpr hc))

/-- Send each column to its point in the projectivization of the column span. -/
theorem rankTwoBoundOfRepresents : Expected.rankTwoBoundOfRepresents.{u,v,w} := by
  intro α K _ _ V _ _ M _ v hv hn hp hr
  classical
  let W := span K (v '' M.E)
  let col : M.E → W := fun e => ⟨v e, subset_span (mem_image_of_mem v e.property)⟩
  have hcol : ∀ e, col e ≠ 0 := by
    intro e h
    have hne := ((hv {e.val}).mp (hn e e.property).indep).2
    have hzero : v e.val = 0 := congrArg Subtype.val h
    exact ((linearIndepOn_singleton_iff K).mp hne) hzero
  let point : M.E → Projectivization K W := fun e => Projectivization.mk K (col e) (hcol e)
  have hinj : Function.Injective point := by
    intro e f h
    by_contra hef
    have hne : e.val ≠ f.val := fun h => hef (Subtype.ext h)
    have hi := indep_pair_of_simple M hn hp e.property f.property hne
    have hli := ((hv {e.val, f.val}).mp hi).2
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K (col e) (col f)
      (hcol e) (hcol f)).mp h
    have hval : v e.val = c • v f.val := (congrArg Subtype.val hc).symm
    apply hli.notMem_span (by simp : e.val ∈ ({e.val, f.val} : Set α))
    rw [hval]
    exact (span K (v '' ({e.val, f.val} \ {e.val}))).smul_mem c
      (subset_span ⟨f.val, by simp [hne.symm], rfl⟩)
  have hdim : Module.finrank K W = 2 := by
    have h := representsRank K M v hv M.E Subset.rfl
    rw [hr] at h
    exact_mod_cast h.symm
  let : Module.Finite K W := Module.Finite.span_of_finite K (M.ground_finite.image v)
  let : Finite W := Cardinal.lt_aleph0_iff_finite.mp
    (cardinal_lt_aleph0_of_finiteDimensional K W)
  have hcard := Nat.card_le_card_of_injective point hinj
  rw [Projectivization.card_of_finrank_two K W hdim] at hcard
  simpa only [Nat.card_coe_set_eq] using hcard

theorem rankTwoBound : Expected.rankTwoBound.{u,v,w} := by
  intro α K _ _ M _ hrep hn hp hr
  obtain ⟨V, hV, hmod, v, hv⟩ := hrep
  exact rankTwoBoundOfRepresents K M v hv hn hp hr

end FiniteCombinatorics.Matroid
