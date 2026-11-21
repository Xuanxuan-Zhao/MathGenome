import MathGenome.Internal.Specs.D07.Ch16.MapsSubmodules
import MathGenome.Internal.D07.Ch16.Definition
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear maps, submodules, and span

K07.16.maps_submodules, paper.tex:2945–2957. The canonical Mathlib
objects are used over arbitrary associative unital rings and unital
left modules, with no basis or finiteness assumptions.
-/

universe u v w t

namespace D07.Ch16.MapsSubmodules

open Specs.D07.Ch16.MapsSubmodules
open scoped BigOperators

theorem linearMapCharacterization : LinearMapCharacterization.{u, v, w} := by
  intro R _ M _ _ N _ _ f
  constructor
  · rintro ⟨ha, hs⟩
    exact ⟨{ toFun := f, map_add' := ha, map_smul' := hs }, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.map_add, g.map_smul⟩

theorem submoduleCharacterization : SubmoduleCharacterization.{u, v} := by
  intro R _ M _ _ S
  constructor
  · rintro ⟨A, hA, hs⟩
    refine ⟨{
      carrier := A
      zero_mem' := A.zero_mem
      add_mem' := fun hx hy => A.add_mem hx hy
      smul_mem' := hs }, hA⟩
  · rintro ⟨P, rfl⟩
    exact ⟨P.toAddSubgroup, rfl, fun r _ hx => P.smul_mem r hx⟩

/-- Only nonemptiness and scalar closure are needed for these two consequences. -/
theorem zeroNegFromClosure : ZeroNegFromClosure.{u, v} := by
  intro R _ M _ _ S hne hs
  obtain ⟨m, hm⟩ := hne
  constructor
  · simpa only [zero_smul] using hs 0 m hm
  · intro x hx
    simpa only [neg_one_smul] using hs (-1) x hx

theorem submoduleNonemptyTest : SubmoduleNonemptyTest.{u, v} := by
  intro R _ M _ _ S
  constructor
  · rintro ⟨hne, ha, hs⟩
    refine ⟨{
      carrier := S
      zero_mem' := (zeroNegFromClosure R M S hne hs).1
      add_mem' := fun hx hy => ha _ hx _ hy
      smul_mem' := hs }, rfl⟩
  · rintro ⟨P, rfl⟩
    exact ⟨⟨0, P.zero_mem⟩, fun _ hx _ hy => P.add_mem hx hy,
      fun r _ hx => P.smul_mem r hx⟩

theorem kernelSubmodule : KernelSubmodule.{u, v, w} := by
  intro R _ M _ _ N _ _ f
  rfl

theorem imageSubmodule : ImageSubmodule.{u, v, w} := by
  intro R _ M _ _ N _ _ f
  exact LinearMap.coe_range f

theorem intersectionSubmodule : IntersectionSubmodule.{u, v, t} := by
  intro R _ M _ _ ι P
  exact Submodule.coe_iInf P

/-- A finite representation exists even when the generating set is infinite;
the reverse direction is closure of span under finite sums and scalar action. -/
theorem spanFiniteSums : SpanFiniteSums.{u, v} := by
  intro R _ M _ _ S x
  constructor
  · intro hx
    obtain ⟨c, F, hF, _, heq⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hx
    exact ⟨F, c, hF, heq⟩
  · rintro ⟨F, c, hF, rfl⟩
    exact Submodule.sum_mem _ fun m hm =>
      Submodule.smul_mem _ _ (Submodule.subset_span (hF hm))

theorem spanClosure : SpanClosure.{u, v} := by
  intro R _ M _ _ S
  exact ⟨(Submodule.span R S).zero_mem,
    fun _ hx _ hy => (Submodule.span R S).add_mem hx hy,
    fun r _ hx => (Submodule.span R S).smul_mem r hx⟩

theorem spanUniversalProperty : SpanUniversalProperty.{u, v} := by
  intro R _ M _ _ S
  exact ⟨Submodule.subset_span, fun _ => Submodule.span_le⟩

end D07.Ch16.MapsSubmodules
