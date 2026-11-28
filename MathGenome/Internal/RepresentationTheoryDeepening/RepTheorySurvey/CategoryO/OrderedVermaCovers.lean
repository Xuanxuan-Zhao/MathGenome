import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.OrderedVermaCovers
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ProjectiveCovers
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ProjectiveFiltrations
import Mathlib.Data.List.OfFn

/-! Ordered Verma flags for projective covers in finite category O. -/

noncomputable section

open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open scoped Classical

namespace RepTheorySurvey.CategoryO.OrderedVermaCovers

open Specs.RepTheorySurvey.CategoryO
open Specs.RepTheorySurvey.CategoryO.ProjectiveCovers (simpleIndex)
open Specs.RepTheorySurvey.CategoryO.OrderedVermaCovers (ExistenceType FlagOfCoverType)
open ProjectiveFiltrations (Layer VermaFlag componentTerm summandTerm)
open TruncatedProjectives (GroupedFiltration)

universe u

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable {D : Setup g}

/-- A linear equivalence carries a flag to the flag of the images of its terms. -/
private theorem map_flag {X Y : Type u} [AddCommGroup X] [Module (U g) X]
    [AddCommGroup Y] [Module (U g) Y] (e : X ≃ₗ[U g] Y)
    {l : List D.Weight} {A C : Submodule (U g) X} (h : VermaFlag D l A C) :
    VermaFlag D l (A.map e.toLinearMap) (C.map e.toLinearMap) := by
  induction h with
  | nil A => exact .nil _
  | @cons ν l A B C hAB hfactor _ ih =>
    obtain ⟨factor⟩ := hfactor
    let eB := e.submoduleMap B
    have heB : (A.comap B.subtype).map eB.toLinearMap =
        (A.map e.toLinearMap).comap (B.map e.toLinearMap).subtype := by
      ext z
      rw [Submodule.mem_map_equiv]
      change e.symm (z : Y) ∈ A ↔ (z : Y) ∈ A.map e.toLinearMap
      rw [Submodule.mem_map_equiv]
    let eqv := Submodule.Quotient.equiv _ _ eB heB
    exact .cons (Submodule.map_mono hAB) ⟨eqv.symm.trans factor⟩ ih

private theorem refined_weights_ordered {μ Λ : D.Weight} (F : GroupedFiltration D μ Λ)
    (r : Fin F.length → ℕ) :
    (List.ofFn (fun i => List.replicate (r i) (F.weight i))).flatten.Pairwise
      (fun ν ξ => weightLE_value D ν ξ → ν = ξ) := by
  apply List.pairwise_flatten.mpr
  refine ⟨?_, List.pairwise_ofFn.mpr ?_⟩
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact List.pairwise_replicate.mpr (Or.inr fun _ => rfl)
  · intro i j hij x hx y hy
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
    intro h
    exact False.elim ((not_lt_of_ge hij.le) (F.higher_first i j h (ne_of_lt hij)))

/-- The cover of a simple has an ordered refinement of the projected
truncated Verma filtration. -/
theorem exists_ordered_verma_cover : ExistenceType.{u} := by
  intro g _ _ _ D μ
  let k := simpleIndex D μ
  obtain ⟨Λ, hΛ, hμ, hP, p₀, S, T, hS, _, _, hST, hInd, hp⟩ :=
    ProjectiveCovers.exists_projectiveCover D μ
  obtain ⟨hL, _, _⟩ := simpleQuotient_in_O D μ
  obtain ⟨F⟩ := TruncatedProjectives.groupedFiltration D μ Λ hμ
  let e := S.projection T hST
  have he : e.comp e = e := Submodule.isIdempotentElem_projection hST
  let f : e.range ≃ₗ[U g] S := LinearEquiv.ofEq _ _ (Submodule.range_projection hST)
  have hf : f.toLinearMap.comp e.rangeRestrict = S.projectionOnto T hST := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  obtain ⟨hmono, hbot, htop, r, _, _, hgroup, hflag⟩ :=
    ProjectiveFiltrations.summandFlag D μ Λ hμ F hP k e he
  let term := summandTerm D F hP k e
  have hterm (i : Fin (F.length + 1)) :
      (term i).map f.toLinearMap = (componentTerm D F hP k i).map (S.projectionOnto T hST) := by
    change ((componentTerm D F hP k i).map e.rangeRestrict).map f.toLinearMap = _
    rw [← Submodule.map_comp, hf]
  refine ⟨Λ, hΛ, hμ, hP, p₀, S, T, hST, hS, hL, F, r, hInd, hp,
    ?_, ?_, ?_, ?_, ?_, refined_weights_ordered F r⟩
  · intro i j hij
    dsimp only
    rw [← hterm i, ← hterm j]
    exact Submodule.map_mono (hmono hij)
  · dsimp only
    rw [← hterm, show term 0 = ⊥ from hbot, Submodule.map_bot]
  · dsimp only
    rw [← hterm, show term (Fin.last F.length) = ⊤ from htop, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr f.surjective
  · intro i
    dsimp only
    rw [← hterm i.castSucc, ← hterm i.succ]
    exact map_flag f (hgroup i)
  · simpa only [Submodule.map_bot, Submodule.map_top, LinearMap.range_eq_top.mpr f.surjective]
      using map_flag f hflag

/-- An isomorphism over the simple quotient transports the ordered flag to
any projective cover. -/
theorem ordered_verma_flag_of_cover : FlagOfCoverType.{u} := by
  intro g _ _ _ D μ X p hp
  obtain ⟨Λ, _, _, _, p₀, S, _, _, hS, hL, F, r, _, hp₀, _, _, _, _, hflag, horder⟩ :=
    exists_ordered_verma_cover D μ
  let X₀ : category_value.{u, u} D := ⟨ModuleCat.of (U g) S, hS⟩
  let Lμ : category_value.{u, u} D := ⟨simpleQuotient_value D μ, hL⟩
  obtain ⟨e, _⟩ := ProjectiveCovers.unique_over_target D X₀ X Lμ (p₀.domRestrict S) p hp₀ hp
  refine ⟨(List.ofFn (fun i => List.replicate (r i) (F.weight i))).flatten, ?_, horder⟩
  simpa only [Submodule.map_bot, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
    using map_flag e hflag

end RepTheorySurvey.CategoryO.OrderedVermaCovers
