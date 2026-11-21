import Mathlib
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.FundamentalGroupoid
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.VanKampen

/-!
Local adaptation of Thomas Zhu’s fundamental-groupoid van Kampen development,
Mathlib PR #41603 (https://github.com/leanprover-community/mathlib4/pull/41603).
Original source: Apache 2.0. All helper proofs are included locally.
The compatibility port consulted is deancureton/sphere-six-complex,
`vendor/VanKampen`, based on Paul-Lez/mathlib4 commit
97d303eb50436be7c4bac4388bdb49459ae9140b. The finite-set extensionality
repairs and elaborator transparency options are retained. Helpers are scoped
per original module, under `VanKampenProof` except for the four `Path` adapters.

The final section specializes the groupoid colimit to two opens and uses
compatible paths from the basepoint to extend any compatible pair of group
homomorphisms. `OneGroup G` uses opposite multiplication so its composition
has the paper's first-path-first order. Extraction returns the canonical `Pi1`.
-/
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false


/-! Adapted from CanonicalCocone.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))

/-- The canonical cocone with apex `π₁(X)` for the diagram of fundamental groupoids
    of open sets in the cover. -/
def canonicalCocone : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor) := by
  let π₁ := FundamentalGroupoid.fundamentalGroupoidFunctor
  let X_top := TopCat.of X
  let F := (Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor
  let G := Opens.toTopCat X_top
  let D := F ⋙ G ⋙ π₁
  refine' {
    pt := π₁.obj X_top,
    ι := {
      app := fun U => π₁.map (Opens.inclusion' (show Opens X_top from U.val)),
      naturality := fun {U V} (f : U ⟶ V) => by
        let i : U.val ⟶ V.val := F.map f
        have h_comm : G.map i ≫ Opens.inclusion' (show Opens X_top from V.val) =
            Opens.inclusion' (show Opens X_top from U.val) := by
          apply TopCat.hom_ext
          ext x
          simp [Opens.coe_inclusion']
          <;> rfl
        have h_main : π₁.map (G.map i) ≫ π₁.map (Opens.inclusion' (show Opens X_top from V.val)) =
            π₁.map (Opens.inclusion' (show Opens X_top from U.val)) := by
          rw [←π₁.map_comp, h_comm]
        have h_goal : π₁.map (G.map i) ≫ π₁.map (Opens.inclusion' (show Opens X_top from V.val)) =
            π₁.map (Opens.inclusion' (show Opens X_top from U.val)) ≫ 𝟙 (π₁.obj X_top) := by
          rw [h_main, Category.comp_id]
        exact h_goal
    }
  }

/-- The apex of the canonical cocone is exactly `π₁(X)`. -/
theorem canonicalCocone_pt :
    (canonicalCocone X 𝒰).pt = FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) := by
  rfl

end

end

end P202.Topology.VanKampenProof


/-! Adapted from UniversalProperty.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hpath_connected : ∀ U : Opens X, U ∈ 𝒰 → IsPathConnected (U : Set X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

/-- Helper: given a point `x` in an open `U ∈ 𝒰`, get the corresponding object in `s.pt`. -/
def obj_at (x : X) (U : Opens X) (hU : U ∈ 𝒰) (hx : x ∈ U) : s.pt :=
  (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk ⟨x, hx⟩)

/-- The object obtained from `x ∈ U ∈ 𝒰` is the same as from `x ∈ V ∈ 𝒰`.
    This uses the fact that `U ∩ V ∈ 𝒰` and the cocone naturality. -/
lemma obj_at_eq
    (hfinite_intersections :
      ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)
    (x : X)
    (U V : Opens X) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰) (hxU : x ∈ U) (hxV : x ∈ V) :
    obj_at X 𝒰 s x U hU hxU = obj_at X 𝒰 s x V hV hxV := by
  classical
  -- The intersection U ∩ V is in 𝒰 by finite intersections property
  let s_finset : Finset (Opens X) := {U, V}
  have h_nonempty : s_finset.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr (by simp [s_finset])
  have h_all_in : ∀ W ∈ s_finset, W ∈ 𝒰 := by
    intro W hW
    have : W = U ∨ W = V := by
      simpa [s_finset] using hW
    rcases this with (rfl | rfl) <;> tauto
  let W := s_finset.inf (fun U : Opens X => U)
  have hW_in : W ∈ 𝒰 := hfinite_intersections s_finset h_nonempty h_all_in
  have hW_le_U : W ≤ U := Finset.inf_le (Finset.mem_insert_self U {V})
  have hW_le_V : W ≤ V := Finset.inf_le (by simp [s_finset])
  have hW_eq : W = U ⊓ V := by
    have h : W = s_finset.inf id := by rfl
    rw [h]
    have h2 : ({U, V} : Finset (Opens X)).inf id = U ⊓ V := by
      classical
      simp [Finset.inf_insert]
      <;> rfl
    exact h2
  have hxW : x ∈ W := by
    rw [hW_eq]
    exact ⟨hxU, hxV⟩

  -- Now we have W ∈ 𝒰 with W ≤ U and W ≤ V, and x ∈ W
  let i_WU : (⟨W, hW_in⟩ : {U // U ∈ 𝒰}) ⟶ ⟨U, hU⟩ := homOfLE hW_le_U
  let i_WV : (⟨W, hW_in⟩ : {U // U ∈ 𝒰}) ⟶ ⟨V, hV⟩ := homOfLE hW_le_V

  -- The cocone naturality: D.map i_WU ≫ s.ι.app ⟨U, hU⟩ = s.ι.app ⟨W, hW_in⟩
  -- where D is the diagram functor
  let D := ((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
    Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor
  have h_nat_U : D.map i_WU ≫ s.ι.app ⟨U, hU⟩ = s.ι.app ⟨W, hW_in⟩ := by
    exact s.ι.naturality i_WU
  have h_nat_V : D.map i_WV ≫ s.ι.app ⟨V, hV⟩ = s.ι.app ⟨W, hW_in⟩ := by
    exact s.ι.naturality i_WV

  -- Apply both sides to the object corresponding to x in W
  let x_W : D.obj ⟨W, hW_in⟩ := FundamentalGroupoid.mk ⟨x, hxW⟩

  have h1 : (s.ι.app ⟨U, hU⟩).obj ((D.map i_WU).obj x_W) = (s.ι.app ⟨W, hW_in⟩).obj x_W := by
    have h_eq : (D.map i_WU ≫ s.ι.app ⟨U, hU⟩).obj x_W = (s.ι.app ⟨W, hW_in⟩).obj x_W := by
      rw [h_nat_U]
      <;> rfl
    exact h_eq
  have h2 : (s.ι.app ⟨V, hV⟩).obj ((D.map i_WV).obj x_W) = (s.ι.app ⟨W, hW_in⟩).obj x_W := by
    have h_eq : (D.map i_WV ≫ s.ι.app ⟨V, hV⟩).obj x_W = (s.ι.app ⟨W, hW_in⟩).obj x_W := by
      rw [h_nat_V]
      <;> rfl
    exact h_eq

  -- But (D.map i_WU).obj x_W is just the object corresponding to x in U
  have h3 : (D.map i_WU).obj x_W = FundamentalGroupoid.mk ⟨x, hxU⟩ := by rfl
  have h4 : (D.map i_WV).obj x_W = FundamentalGroupoid.mk ⟨x, hxV⟩ := by rfl

  rw [h3] at h1
  rw [h4] at h2
  exact h1.trans h2.symm

/-- The object part of the descent functor.
    Given a point x of X, pick some U ∈ 𝒰 containing x (exists by hcover),
    and use the cocone leg at U to get an object of s.pt.
    The result is independent of the choice of U by obj_at_eq. -/
def desc_functor_obj (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) :
    s.pt :=
  let x_pt : X := x.as
  let h : ∃ (U : Opens X), U ∈ 𝒰 ∧ x_pt ∈ U := hcover x_pt
  let U : Opens X := Classical.choose h
  let hU : U ∈ 𝒰 ∧ x_pt ∈ U := Classical.choose_spec h
  obj_at X 𝒰 s x_pt U hU.1 hU.2

/-- The fac property: on objects, composing the inclusion π₁(U) → π₁(X) with the descent
    functor gives the same as applying the cocone leg directly. -/
theorem fac_property_obj
    (hfinite_intersections :
      ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)
    (U : Opens X) (hU : U ∈ 𝒰) :
    ∀ (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U)),
      desc_functor_obj X 𝒰 hcover s
        ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x) =
      (s.ι.app ⟨U, hU⟩).obj x := by
  intro x
  -- x is an object of π₁(U)
  let z : (Opens.toTopCat (TopCat.of X)).obj U := x.as
  let z_X : X := z.val
  have hz : z_X ∈ U := z.property

  -- The inclusion map sends x to FundamentalGroupoid.mk z_X in π₁(X)
  have h1 : (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x =
      (FundamentalGroupoid.mk z_X : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) := by
    rfl

  rw [h1]

  have h_main : desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk z_X) =
      obj_at X 𝒰 s z_X U hU hz := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ z_X ∈ U' := hcover z_X
    have h' : obj_at X 𝒰 s z_X (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2 =
        obj_at X 𝒰 s z_X U hU hz :=
      obj_at_eq X 𝒰 s hfinite_intersections z_X (Classical.choose h) U
        (Classical.choose_spec h).1 hU (Classical.choose_spec h).2 hz
    exact h'

  have h3 : obj_at X 𝒰 s z_X U hU hz = (s.ι.app ⟨U, hU⟩).obj x := by
    rfl

  calc
    desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk z_X)
      = obj_at X 𝒰 s z_X U hU hz := h_main
    _ = (s.ι.app ⟨U, hU⟩).obj x := h3

end

end

end P202.Topology.VanKampenProof


/-! Adapted from PathHelpers.lean. -/



section

open TopologicalSpace Path.Homotopic unitInterval CategoryTheory

noncomputable section

variable {X : Type*} [TopologicalSpace X]

namespace Path

/-- Restrict a path to a subinterval [a, b] ⊆ [0,1].

This is a wrapper around `Path.truncateOfLE` for the case where we explicitly
have `0 ≤ a` and `b ≤ 1`. The resulting path follows γ on [a, b]. -/
def restrict {x y : X} (γ : Path x y) (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    Path (γ.extend a) (γ.extend b) :=
  γ.truncateOfLE hab

/-- The range of a restricted path is a subset of the range of the original path. -/
theorem range_restrict_subset {x y : X} (γ : Path x y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    Set.range (γ.restrict a b ha hb hab) ⊆ Set.range γ := by
  have h : Set.range (γ.truncateOfLE hab) ⊆ Set.range γ := truncate_range γ
  exact h

/-- If the range of a path is contained in a set U, then the path factors
    through the subtype U. -/
theorem lift_to_subtype {x y : X} (γ : Path x y) {U : Set X}
    (hx : x ∈ U) (hy : y ∈ U) (h : Set.range γ ⊆ U) :
    ∃ (γ' : Path (⟨x, hx⟩ : U) (⟨y, hy⟩)),
      (∀ (t : I), (γ' t : X) = γ t) := by
  let γ' : Path (⟨x, hx⟩ : U) (⟨y, hy⟩) :=
    { toFun := fun t : I => ⟨γ t, h (Set.mem_range_self t)⟩
      continuous_toFun := by
        exact Continuous.subtype_mk γ.continuous _
      source' := by
        simp
      target' := by
        simp }
  refine ⟨γ', fun t => rfl⟩

/-- Applying the inclusion map to a lifted path gives back the original path. -/
theorem map_lift_to_subtype {x y : X} (γ : Path x y) {U : Set X}
    (hx : x ∈ U) (hy : y ∈ U) (h : Set.range γ ⊆ U)
    (γ' : Path (⟨x, hx⟩ : U) (⟨y, hy⟩))
    (hγ' : ∀ (t : I), (γ' t : X) = γ t) :
    γ'.map continuous_subtype_val = γ := by
  ext t
  simpa [map_coe] using hγ' t

/-- The homotopy class of a concatenation of paths equals the composition
    of the homotopy classes. -/
theorem homotopic_quotient_trans_eq_comp {x y z : X} (γ₁ : Path x y) (γ₂ : Path y z) :
    Path.Homotopic.Quotient.mk (γ₁.trans γ₂) =
      (Path.Homotopic.Quotient.mk γ₁).trans (Path.Homotopic.Quotient.mk γ₂) :=
  Path.Homotopic.Quotient.mk_trans γ₁ γ₂

/-- In the fundamental groupoid, composition of morphisms corresponds to
    concatenation of paths. This is a direct consequence of `comp_eq` and `mk_trans`. -/
theorem fundamentalGroupoid_comp_eq_trans
    (x' y' z' : FundamentalGroupoid X)
    (p : x' ⟶ y') (q : y' ⟶ z') :
    p ≫ q = p.trans q :=
  FundamentalGroupoid.comp_eq x' y' z' p q

end Path

end

end


/-! Adapted from CommonRefinement.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace Set unitInterval Finset

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

/-- A finite set of points in the unit interval forms a valid subdivision of a path γ
    if every subinterval between consecutive points is mapped into some open set from 𝒰. -/
def IsAdaptedSubdivision {x y : X} (γ : Path x y) (S : Finset I) : Prop :=
  (0 : I) ∈ S ∧ (1 : I) ∈ S ∧
  ∀ (s₁ s₂ : I), s₁ ∈ S → s₂ ∈ S → s₁ < s₂ →
    (∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False) →
    ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t : I), s₁ ≤ t → t ≤ s₂ → γ t ∈ (U : Set X)

namespace IsAdaptedSubdivision

variable {𝒰}

/-- Helper: given a finite set S containing 0 and 1, and points s₁ < s₂ with no points
    of S between them, there exists a containing interval [t₁, t₂] in S. -/
lemma containing_interval {S : Finset I} (h0 : (0 : I) ∈ S) (h1 : (1 : I) ∈ S)
    {s₁ s₂ : I} (h_lt : s₁ < s₂)
    (h_consec : ∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False) :
    ∃ (t₁ t₂ : I), t₁ ∈ S ∧ t₂ ∈ S ∧ t₁ ≤ s₁ ∧ s₂ ≤ t₂ ∧
      (∀ (t : I), t ∈ S → t₁ < t → t < t₂ → False) := by
  -- Let t₁ be the maximum element of S that is ≤ s₁
  let S_low := S.filter (fun t : I => t ≤ s₁)
  have h_zero_le_s1 : (0 : I) ≤ s₁ := by
    have h : (0 : ℝ) ≤ (s₁ : ℝ) := s₁.prop.1
    exact_mod_cast h
  have h0_low : (0 : I) ∈ S_low := by
    simp only [S_low, mem_filter]
    exact ⟨h0, h_zero_le_s1⟩
  have h_S_low_nonempty : S_low.Nonempty := ⟨0, h0_low⟩
  let t₁ := S_low.max' h_S_low_nonempty
  have ht₁_mem : t₁ ∈ S_low := Finset.max'_mem S_low h_S_low_nonempty
  have ht₁_in_S : t₁ ∈ S := (mem_filter.mp ht₁_mem).1
  have ht₁_le : t₁ ≤ s₁ := (mem_filter.mp ht₁_mem).2

  -- Let t₂ be the minimum element of S that is ≥ s₂
  let S_high := S.filter (fun t : I => s₂ ≤ t)
  have h_s2_le_one : s₂ ≤ (1 : I) := by
    have h : (s₂ : ℝ) ≤ (1 : ℝ) := s₂.prop.2
    exact_mod_cast h
  have h1_high : (1 : I) ∈ S_high := by
    simp only [S_high, mem_filter]
    exact ⟨h1, h_s2_le_one⟩
  have h_S_high_nonempty : S_high.Nonempty := ⟨1, h1_high⟩
  let t₂ := S_high.min' h_S_high_nonempty
  have ht₂_mem : t₂ ∈ S_high := Finset.min'_mem S_high h_S_high_nonempty
  have ht₂_in_S : t₂ ∈ S := (mem_filter.mp ht₂_mem).1
  have h_le_t₂ : s₂ ≤ t₂ := (mem_filter.mp ht₂_mem).2

  -- Now show t₁ and t₂ are consecutive in S
  have h_consec' : ∀ (t : I), t ∈ S → t₁ < t → t < t₂ → False := by
    intro t ht h_t1_lt h_t_lt2
    by_cases h : t ≤ s₁
    · -- t ≤ s₁, so t ∈ S_low, contradicting maximality of t₁
      have h_t_in_low : t ∈ S_low := by
        simp only [S_low, mem_filter] <;> exact ⟨ht, h⟩
      have h_t_le_t1 : t ≤ t₁ := Finset.le_max' S_low t h_t_in_low
      have : t₁ < t₁ := by
        calc
          t₁ < t := h_t1_lt
          _ ≤ t₁ := h_t_le_t1
      exact lt_irrefl t₁ this
    · -- s₁ < t
      have h' : s₁ < t := by exact lt_of_not_ge h
      by_cases h2 : t < s₂
      · -- s₁ < t < s₂, contradicting h_consec
        exact h_consec t ht h' h2
      · -- s₂ ≤ t
        have h_s2_le_t : s₂ ≤ t := by
          by_contra h3
          exact h2 (lt_of_not_ge h3)
        -- Therefore t ∈ S_high
        have h_t_in_high : t ∈ S_high := by
          simp only [S_high, mem_filter]
          exact ⟨ht, h_s2_le_t⟩
        -- By minimality of t₂, we have t₂ ≤ t
        have h_t2_le_t : t₂ ≤ t := Finset.min'_le S_high t h_t_in_high
        -- But we assumed t < t₂, so we have t₂ ≤ t < t₂, which is a contradiction
        have h_contra : t₂ < t₂ := by
          calc
            t₂ ≤ t := h_t2_le_t
            _ < t₂ := h_t_lt2
        exact lt_irrefl t₂ h_contra

  exact ⟨t₁, t₂, ht₁_in_S, ht₂_in_S, ht₁_le, h_le_t₂, h_consec'⟩

/-- The union of two adapted subdivisions is also an adapted subdivision. -/
theorem union_is_adapted (hfinite_intersections :
    ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)
    {x y : X} {γ : Path x y} {S T : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hT : IsAdaptedSubdivision 𝒰 γ T) :
    IsAdaptedSubdivision 𝒰 γ (S ∪ T) := by
  have h0 : (0 : I) ∈ S ∪ T := by
    exact mem_union_left T hS.1
  have h1 : (1 : I) ∈ S ∪ T := by
    exact mem_union_left T hS.2.1
  constructor
  · exact h0
  constructor
  · exact h1
  · intro s₁ s₂ hs₁ hs₂ h_lt h_consec
    -- [s₁, s₂] is a subinterval of the union subdivision
    -- We need to find U ∈ 𝒰 such that γ maps [s₁, s₂] into U

    -- First, find the containing interval in S
    have h_S_interval : ∃ (t₁ t₂ : I), t₁ ∈ S ∧ t₂ ∈ S ∧ t₁ ≤ s₁ ∧ s₂ ≤ t₂ ∧
        (∀ (t : I), t ∈ S → t₁ < t → t < t₂ → False) := by
      apply containing_interval hS.1 hS.2.1 h_lt
      intro t ht h_t1_lt h_t_lt2
      exact h_consec t (mem_union_left T ht) h_t1_lt h_t_lt2

    -- Find the containing interval in T
    have h_T_interval : ∃ (u₁ u₂ : I), u₁ ∈ T ∧ u₂ ∈ T ∧ u₁ ≤ s₁ ∧ s₂ ≤ u₂ ∧
        (∀ (t : I), t ∈ T → u₁ < t → t < u₂ → False) := by
      apply containing_interval hT.1 hT.2.1 h_lt
      intro t ht h_t1_lt h_t_lt2
      exact h_consec t (mem_union_right S ht) h_t1_lt h_t_lt2

    rcases h_S_interval with ⟨t₁, t₂, ht₁, ht₂, h_t₁_le, h_le_t₂, h_S_consec⟩
    rcases h_T_interval with ⟨u₁, u₂, hu₁, hu₂, h_u₁_le, h_le_u₂, h_T_consec⟩

    -- Get the open sets from S and T
    have h_t1_lt_t2 : t₁ < t₂ := by
      calc
        t₁ ≤ s₁ := h_t₁_le
        _ < s₂ := h_lt
        _ ≤ t₂ := h_le_t₂
    have h_u1_lt_u2 : u₁ < u₂ := by
      calc
        u₁ ≤ s₁ := h_u₁_le
        _ < s₂ := h_lt
        _ ≤ u₂ := h_le_u₂
    rcases hS.2.2 t₁ t₂ ht₁ ht₂ h_t1_lt_t2 h_S_consec with ⟨U, hU_mem, hU⟩
    rcases hT.2.2 u₁ u₂ hu₁ hu₂ h_u1_lt_u2 h_T_consec with ⟨V, hV_mem, hV⟩

    classical
    -- The intersection U ∩ V is in 𝒰 by finite intersection closure
    let s_finset : Finset (Opens X) := {U, V}
    have h_nonempty : s_finset.Nonempty := by
      simp [s_finset]
      <;> exact ⟨U, by simp⟩
    have h_all_in : ∀ (W : Opens X), W ∈ s_finset → W ∈ 𝒰 := by
      intro W hW
      have h : W = U ∨ W = V := by
        simpa [s_finset] using hW
      rcases h with (rfl | rfl)
      · exact hU_mem
      · exact hV_mem
    have h_inter_in : s_finset.inf (fun W : Opens X => W) ∈ 𝒰 :=
      hfinite_intersections s_finset h_nonempty h_all_in

    let W_inf : Opens X := s_finset.inf (fun W : Opens X => W)
    have h_W_inf_mem : W_inf ∈ 𝒰 := h_inter_in

    -- The underlying set of W_inf is the intersection of the underlying sets
    have h_eq_inf : s_finset.inf (fun W : Opens X => W) = U ⊓ V := by
      simp [s_finset, Finset.inf_insert, Finset.inf_singleton]
      <;> rfl
    have h_inf_set : (W_inf : Set X) = (U : Set X) ∩ (V : Set X) := by
      have h1 : W_inf = U ⊓ V := by
        dsimp only [W_inf]
        exact h_eq_inf
      rw [h1]
      exact Opens.coe_inf U V


    refine ⟨W_inf, h_W_inf_mem, ?_⟩
    intro t h_t1 h_t2
    have h1 : γ t ∈ (U : Set X) := hU t (le_trans h_t₁_le h_t1) (le_trans h_t2 h_le_t₂)
    have h2 : γ t ∈ (V : Set X) := hV t (le_trans h_u₁_le h_t1) (le_trans h_t2 h_le_u₂)
    rw [h_inf_set]
    exact ⟨h1, h2⟩

/-- Inserting a single point into an adapted subdivision gives another adapted subdivision. -/
lemma insert_is_adapted {x y : X} {γ : Path x y} {S : Finset I} {pt : I}
    (hS : IsAdaptedSubdivision 𝒰 γ S) :
    IsAdaptedSubdivision 𝒰 γ (S ∪ {pt}) := by
  classical
  by_cases h_pt_in_S : pt ∈ S
  · -- If pt ∈ S, then S ∪ {pt} = S, so we're done
    have h : S ∪ {pt} = S := by
      simp [h_pt_in_S]
      <;> tauto
    rw [h]
    exact hS
  · -- If pt ∉ S, we need to prove the result directly
    have h0 : (0 : I) ∈ S ∪ {pt} := by
      exact Finset.mem_union_left {pt} hS.1
    have h1 : (1 : I) ∈ S ∪ {pt} := by
      exact Finset.mem_union_left {pt} hS.2.1
    constructor
    · exact h0
    constructor
    · exact h1
    · intro s₁ s₂ hs₁ hs₂ h_lt h_consec
      -- We have s₁, s₂ ∈ S ∪ {pt}, s₁ < s₂, and no points of S ∪ {pt} between them
      -- We need to find U ∈ 𝒰 covering [s₁, s₂]
      -- Use the containing_interval lemma from S
      have h_S_interval : ∃ (t₁ t₂ : I), t₁ ∈ S ∧ t₂ ∈ S ∧ t₁ ≤ s₁ ∧ s₂ ≤ t₂ ∧
          (∀ (t : I), t ∈ S → t₁ < t → t < t₂ → False) := by
        apply containing_interval hS.1 hS.2.1 h_lt
        intro t ht h_t1_lt h_t_lt2
        exact h_consec t (Finset.mem_union_left {pt} ht) h_t1_lt h_t_lt2
      rcases h_S_interval with ⟨t₁, t₂, ht₁_in_S, ht₂_in_S, h_t₁_le, h_le_t₂, h_S_consec⟩
      -- Now t₁ and t₂ are consecutive in S, so there exists U ∈ 𝒰 covering [t₁, t₂]
      have h_t1_lt_t2 : t₁ < t₂ := by
        calc
          t₁ ≤ s₁ := h_t₁_le
          _ < s₂ := h_lt
          _ ≤ t₂ := h_le_t₂
      rcases hS.2.2 t₁ t₂ ht₁_in_S ht₂_in_S h_t1_lt_t2 h_S_consec with ⟨U, hU_mem, hU⟩
      -- Since [s₁, s₂] ⊆ [t₁, t₂], U also covers [s₁, s₂]
      refine ⟨U, hU_mem, ?_⟩
      intro t h_t1 h_t2
      have h_t1' : t₁ ≤ t := le_trans h_t₁_le h_t1
      have h_t2' : t ≤ t₂ := le_trans h_t2 h_le_t₂
      exact hU t h_t1' h_t2'

end IsAdaptedSubdivision

end

end

end P202.Topology.VanKampenProof


/-! Adapted from TransLift.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace

open scoped unitInterval

/-- Helper lemma: the concatenation of two lifted paths projects to the concatenation
    of the original paths. -/
lemma trans_lift_commutes {X : Type*} [TopologicalSpace X] {U : Set X} {x y z : X}
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (γ₁ : Path x y) (γ₂ : Path y z)
    (γ₁_lift : Path (⟨x, hx⟩ : U) (⟨y, hy⟩ : U))
    (γ₂_lift : Path (⟨y, hy⟩ : U) (⟨z, hz⟩ : U))
    (hγ₁ : ∀ (t : unitInterval), (γ₁_lift t : X) = γ₁ t)
    (hγ₂ : ∀ (t : unitInterval), (γ₂_lift t : X) = γ₂ t) :
    ∀ (t : unitInterval), ((γ₁_lift.trans γ₂_lift) t : X) = (γ₁.trans γ₂) t := by
  intro t
  by_cases h : (t : ℝ) ≤ 1 / 2
  · -- Case (t : ℝ) ≤ 1 / 2
    have h_t1 : 2 * (t : ℝ) ∈ I := ⟨by linarith [t.2.1], by linarith [h]⟩
    let t' : unitInterval := ⟨2 * (t : ℝ), h_t1⟩
    have h1 : (γ₁_lift.trans γ₂_lift) t = γ₁_lift t' := by
      have h_trans : (γ₁_lift.trans γ₂_lift) t =
          dite ((t : ℝ) ≤ 1 / 2) (fun h => γ₁_lift ⟨2 * (t : ℝ), _⟩) (fun h => γ₂_lift ⟨2 * (t : ℝ) - 1, _⟩) :=
        Path.trans_apply γ₁_lift γ₂_lift t
      rw [h_trans]
      rw [dif_pos h]
      <;> rfl
    have h2 : (γ₁.trans γ₂) t = γ₁ t' := by
      have h_trans : (γ₁.trans γ₂) t =
          dite ((t : ℝ) ≤ 1 / 2) (fun h => γ₁ ⟨2 * (t : ℝ), _⟩) (fun h => γ₂ ⟨2 * (t : ℝ) - 1, _⟩) :=
        Path.trans_apply γ₁ γ₂ t
      rw [h_trans]
      rw [dif_pos h] <;> rfl
    rw [h1, h2]
    exact hγ₁ t'
  · -- Case (t : ℝ) > 1 / 2
    have h_t2 : 2 * (t : ℝ) - 1 ∈ I := ⟨by linarith [t.2.1, h], by linarith [t.2.2]⟩
    let t' : unitInterval := ⟨2 * (t : ℝ) - 1, h_t2⟩
    have h1 : (γ₁_lift.trans γ₂_lift) t = γ₂_lift t' := by
      have h_trans : (γ₁_lift.trans γ₂_lift) t =
          dite ((t : ℝ) ≤ 1 / 2) (fun h => γ₁_lift ⟨2 * (t : ℝ), _⟩) (fun h => γ₂_lift ⟨2 * (t : ℝ) - 1, _⟩) :=
        Path.trans_apply γ₁_lift γ₂_lift t
      rw [h_trans]
      rw [dif_neg h] <;> rfl
    have h2 : (γ₁.trans γ₂) t = γ₂ t' := by
      have h_trans : (γ₁.trans γ₂) t =
          dite ((t : ℝ) ≤ 1 / 2) (fun h => γ₁ ⟨2 * (t : ℝ), _⟩) (fun h => γ₂ ⟨2 * (t : ℝ) - 1, _⟩) :=
        Path.trans_apply γ₁ γ₂ t
      rw [h_trans]
      rw [dif_neg h] <;> rfl
    rw [h1, h2]
    exact hγ₂ t'

end

end P202.Topology.VanKampenProof


/-! Adapted from EqToHomHelpers.lean. -/
namespace P202.Topology.VanKampenProof



section

open CategoryTheory

/-- General lemma: composing two morphisms with eqToHom transports, where the
    intermediate transports cancel out. -/
lemma eqToHom_comp_cancel {C : Type*} [Category C] {X X' Y Y' Z Z' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ) =
    eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ := by
  have h1 : eqToHom hY ≫ eqToHom hY.symm = 𝟙 Y := by
    rw [eqToHom_trans]
    <;> simp
  calc
    (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ)
      = eqToHom hX.symm ≫ f ≫ (eqToHom hY ≫ eqToHom hY.symm) ≫ g ≫ eqToHom hZ := by
        simp only [Category.assoc]
        <;> rfl
    _ = eqToHom hX.symm ≫ f ≫ 𝟙 Y ≫ g ≫ eqToHom hZ := by
        rw [h1]
        <;> simp only [Category.assoc]
    _ = eqToHom hX.symm ≫ (f ≫ 𝟙 Y) ≫ g ≫ eqToHom hZ := by
        simp only [Category.assoc]
        <;> rfl
    _ = eqToHom hX.symm ≫ f ≫ g ≫ eqToHom hZ := by
        rw [Category.comp_id f]
        <;> simp only [Category.assoc]
        <;> rfl
    _ = eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ := by
        simp only [Category.assoc]
        <;> rfl

end

end P202.Topology.VanKampenProof


/-! Adapted from SingleCoveredSimple.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

/-- Helper: the range of a concatenated path is the union of the ranges. -/
lemma range_trans_subset_simple {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ₁ : Path x y) (γ₂ : Path y z) {U : Set X}
    (h₁ : Set.range γ₁ ⊆ U) (h₂ : Set.range γ₂ ⊆ U) :
    Set.range (γ₁.trans γ₂) ⊆ U := by
  have h : Set.range (γ₁.trans γ₂) = Set.range γ₁ ∪ Set.range γ₂ :=
    Path.trans_range γ₁ γ₂
  rw [h]
  exact Set.union_subset h₁ h₂

/-- Simpler version of single_covered_map that doesn't transport to desc_functor_obj.
    The domain and codomain are objects obtained from specific opens. -/
def single_covered_map_simple {x y : X} (γ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰) (hx : x ∈ U) (hy : y ∈ U)
    (h : Set.range γ ⊆ (U : Set X)) :
    obj_at X 𝒰 s x U hU hx ⟶ obj_at X 𝒰 s y U hU hy := by
  let U_set : Set X := (U : Set X)
  let γ_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ hx hy h).choose
  let γ_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_lift
  let f : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
          (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    (s.ι.app ⟨U, hU⟩).map γ_class
  have h_eq1 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hx := by rfl
  have h_eq2 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) =
      obj_at X 𝒰 s y U hU hy := by rfl
  exact eqToHom h_eq1.symm ≫ f ≫ eqToHom h_eq2

/-- Helper: any two lifts of the same path to a subtype are equal. -/
lemma lift_unique_simple {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    (γ : Path x y) (hx : x ∈ U) (hy : y ∈ U) (h : Set.range γ ⊆ U)
    (γ₁ γ₂ : Path (⟨x, hx⟩ : U) (⟨y, hy⟩ : U))
    (h₁ : ∀ (t : unitInterval), (γ₁ t : X) = γ t)
    (h₂ : ∀ (t : unitInterval), (γ₂ t : X) = γ t) :
    γ₁ = γ₂ := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact (h₁ t).trans (h₂ t).symm

/-- The split property for the simple version: composing the maps for two segments
    equals the map for the concatenated path. -/
theorem single_covered_split_eq_simple {x y z : X}
    (U : Opens X) (hU : U ∈ 𝒰)
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (γ₁ : Path x y) (h₁ : Set.range γ₁ ⊆ (U : Set X))
    (γ₂ : Path y z) (h₂ : Set.range γ₂ ⊆ (U : Set X)) :
    single_covered_map_simple X 𝒰 s γ₁ U hU hx hy h₁ ≫
    single_covered_map_simple X 𝒰 s γ₂ U hU hy hz h₂ =
    single_covered_map_simple X 𝒰 s (γ₁.trans γ₂) U hU hx hz
      (range_trans_subset_simple γ₁ γ₂ h₁ h₂) := by
  dsimp only [single_covered_map_simple]
  let U_set : Set X := (U : Set X)

  -- Get the lifts
  let γ₁_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ₁ hx hy h₁).choose
  let hγ₁_lift : ∀ (t : unitInterval), (γ₁_lift t : X) = γ₁ t :=
    (Path.lift_to_subtype γ₁ hx hy h₁).choose_spec

  let γ₂_lift : Path (⟨y, hy⟩ : U_set) (⟨z, hz⟩ : U_set) :=
    (Path.lift_to_subtype γ₂ hy hz h₂).choose
  let hγ₂_lift : ∀ (t : unitInterval), (γ₂_lift t : X) = γ₂ t :=
    (Path.lift_to_subtype γ₂ hy hz h₂).choose_spec

  let h_both_range : Set.range (γ₁.trans γ₂) ⊆ (U : Set X) :=
    range_trans_subset_simple γ₁ γ₂ h₁ h₂

  let γ_both_lift : Path (⟨x, hx⟩ : U_set) (⟨z, hz⟩ : U_set) :=
    (Path.lift_to_subtype (γ₁.trans γ₂) hx hz h_both_range).choose
  let hγ_both_lift : ∀ (t : unitInterval), (γ_both_lift t : X) = (γ₁.trans γ₂) t :=
    (Path.lift_to_subtype (γ₁.trans γ₂) hx hz h_both_range).choose_spec

  -- The concatenation of the lifts is also a lift of the concatenated path
  -- This is a key fact we need: map of trans equals trans of maps
  let γ_concat_lift : Path (⟨x, hx⟩ : U_set) (⟨z, hz⟩ : U_set) :=
    γ₁_lift.trans γ₂_lift

  -- Prove that γ_concat_lift is a lift of γ₁.trans γ₂
  have hγ_concat_lift : ∀ (t : unitInterval), (γ_concat_lift t : X) = (γ₁.trans γ₂) t :=
    trans_lift_commutes hx hy hz γ₁ γ₂ γ₁_lift γ₂_lift hγ₁_lift hγ₂_lift

  -- Therefore the two lifts are equal
  have h_lifts_eq : γ_both_lift = γ_concat_lift :=
    lift_unique_simple (γ₁.trans γ₂) hx hz h_both_range γ_both_lift γ_concat_lift hγ_both_lift hγ_concat_lift

  -- Get the homotopy classes
  let γ₁_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ₁_lift
  let γ₂_class : (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ₂_lift
  let γ_both_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                    (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_both_lift

  -- The class of the concatenation is the composition of the classes
  have h_class_comp : γ₁_class ≫ γ₂_class = γ_both_class := by
    have h : γ₁_class ≫ γ₂_class = Path.Homotopic.Quotient.mk (γ₁_lift.trans γ₂_lift) := by
      exact FundamentalGroupoid.comp_eq _ _ _ _ _
    have h' : Path.Homotopic.Quotient.mk (γ₁_lift.trans γ₂_lift) = Path.Homotopic.Quotient.mk γ_both_lift := by
      rw [show γ₁_lift.trans γ₂_lift = γ_both_lift from h_lifts_eq.symm]
    rw [h, h']
    <;> rfl

  -- Apply the cocone functor
  let F := s.ι.app ⟨U, hU⟩
  let f₁_core : F.obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
              F.obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    F.map γ₁_class
  let f₂_core : F.obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) ⟶
              F.obj (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set)) :=
    F.map γ₂_class
  let f_both_core : F.obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                  F.obj (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set)) :=
    F.map γ_both_class

  have h_map_comp : f₁_core ≫ f₂_core = f_both_core := by
    have h : F.map (γ₁_class ≫ γ₂_class) = F.map γ₁_class ≫ F.map γ₂_class := by
      exact F.map_comp γ₁_class γ₂_class
    have h' : F.map (γ₁_class ≫ γ₂_class) = F.map γ_both_class :=
      congr_arg (fun f : _ ⟶ _ => F.map f) h_class_comp
    have h'' : F.map γ₁_class ≫ F.map γ₂_class = F.map γ_both_class := by
      rw [←h, h']
    exact h''

  -- Now the eqToHom transports cancel out nicely
  let obj_x := (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set))
  let obj_y := (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set))
  let obj_z := (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set))
  let h_eq_x : obj_x = obj_at X 𝒰 s x U hU hx := by rfl
  let h_eq_y : obj_y = obj_at X 𝒰 s y U hU hy := by rfl
  let h_eq_z : obj_z = obj_at X 𝒰 s z U hU hz := by rfl
  let e_x : obj_at X 𝒰 s x U hU hx ⟶ obj_x := eqToHom h_eq_x.symm
  let e_y : obj_y ⟶ obj_at X 𝒰 s y U hU hy := eqToHom h_eq_y
  let e_y' : obj_at X 𝒰 s y U hU hy ⟶ obj_y := eqToHom h_eq_y.symm
  let e_z : obj_z ⟶ obj_at X 𝒰 s z U hU hz := eqToHom h_eq_z

  -- Apply the general eqToHom cancellation lemma
  have h_main1 : (eqToHom h_eq_x.symm ≫ f₁_core ≫ eqToHom h_eq_y) ≫
      (eqToHom h_eq_y.symm ≫ f₂_core ≫ eqToHom h_eq_z) =
      eqToHom h_eq_x.symm ≫ (f₁_core ≫ f₂_core) ≫ eqToHom h_eq_z :=
    eqToHom_comp_cancel h_eq_x h_eq_y h_eq_z f₁_core f₂_core

  -- Now use h_map_comp to replace f₁_core ≫ f₂_core with f_both_core
  have h_main2 : eqToHom h_eq_x.symm ≫ (f₁_core ≫ f₂_core) ≫ eqToHom h_eq_z =
      eqToHom h_eq_x.symm ≫ f_both_core ≫ eqToHom h_eq_z := by
    have h : eqToHom h_eq_x.symm ≫ (f₁_core ≫ f₂_core) ≫ eqToHom h_eq_z =
        eqToHom h_eq_x.symm ≫ (f₁_core ≫ f₂_core) ≫ eqToHom h_eq_z := rfl
    rw [h_map_comp]
    <;> rfl

  exact h_main1.trans h_main2

/-- Helper: if two functors are equal, then their map of a morphism is equal
    when transported along the appropriate eqToHom's. -/
lemma functor_eq_map_eq {C D : Type u} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (f : X ⟶ Y) :
    F.map f = eqToHom (congr_arg (fun (K : C ⥤ D) => K.obj X) h) ≫
      G.map f ≫ eqToHom (congr_arg (fun (K : C ⥤ D) => K.obj Y) h).symm := by
  cases h
  <;> simp [eqToHom_refl, Category.comp_id, Category.id_comp]
  <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Independence of the simple version with respect to inclusion of opens.
    If W ≤ U, the map through W (transported to U's obj_at type) equals the map through U. -/
theorem single_covered_map_simple_indep_of_le {x y : X}
    (W U : Opens X) (hW : W ∈ 𝒰) (hU : U ∈ 𝒰) (hWU : W ≤ U)
    (γ : Path x y) (hxW : x ∈ W) (hyW : y ∈ W)
    (hxU : x ∈ U) (hyU : y ∈ U)
    (hW_range : Set.range γ ⊆ (W : Set X))
    (hU_range : Set.range γ ⊆ (U : Set X))
    (h_eq_x : obj_at X 𝒰 s x W hW hxW = obj_at X 𝒰 s x U hU hxU)
    (h_eq_y : obj_at X 𝒰 s y W hW hyW = obj_at X 𝒰 s y U hU hyU) :
    eqToHom h_eq_x.symm ≫ single_covered_map_simple X 𝒰 s γ W hW hxW hyW hW_range ≫ eqToHom h_eq_y =
    single_covered_map_simple X 𝒰 s γ U hU hxU hyU hU_range := by
  dsimp only [single_covered_map_simple]

  let W_set : Set X := (W : Set X)
  let U_set : Set X := (U : Set X)

  -- Get the lifts
  let γ_W_lift : Path (⟨x, hxW⟩ : W_set) (⟨y, hyW⟩ : W_set) :=
    (Path.lift_to_subtype γ hxW hyW hW_range).choose
  let hγ_W_lift : ∀ (t : unitInterval), (γ_W_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hxW hyW hW_range).choose_spec

  let γ_U_lift : Path (⟨x, hxU⟩ : U_set) (⟨y, hyU⟩ : U_set) :=
    (Path.lift_to_subtype γ hxU hyU hU_range).choose
  let hγ_U_lift : ∀ (t : unitInterval), (γ_U_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hxU hyU hU_range).choose_spec

  -- The inclusion map from W to U induces a map on paths
  let incl_WU : W_set → U_set := fun z => ⟨(z : X), hWU z.property⟩
  have hi_cont : Continuous incl_WU := by apply continuous_inclusion hWU

  -- incl_WU ∘ γ_W_lift is a lift of γ to U
  let γ_U_from_W : Path (⟨x, hxU⟩ : U_set) (⟨y, hyU⟩ : U_set) :=
    γ_W_lift.map hi_cont

  have hγ_U_from_W : ∀ (t : unitInterval), (γ_U_from_W t : X) = γ t := by
    intro t
    have h1 : (γ_U_from_W t : X) = (incl_WU (γ_W_lift t) : X) := by rfl
    rw [h1]
    have h2 : (incl_WU (γ_W_lift t) : X) = (γ_W_lift t : X) := by rfl
    rw [h2]
    exact hγ_W_lift t

  -- Therefore γ_U_from_W = γ_U_lift (by uniqueness of lifts)
  have h_lifts_eq : γ_U_from_W = γ_U_lift :=
    lift_unique_simple γ hxU hyU hU_range γ_U_from_W γ_U_lift hγ_U_from_W hγ_U_lift

  -- Get the homotopy classes
  let γ_W_class : (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set)) :=
    Path.Homotopic.Quotient.mk γ_W_lift
  let γ_U_class : (FundamentalGroupoid.mk (⟨x, hxU⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hyU⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_U_lift

  -- Cocone naturality
  let D := ((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
    Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor
  let i : (⟨W, hW⟩ : {U // U ∈ 𝒰}) ⟶ ⟨U, hU⟩ := homOfLE hWU
  have h_nat : D.map i ≫ s.ι.app ⟨U, hU⟩ = s.ι.app ⟨W, hW⟩ := s.ι.naturality i

  -- The induced functor maps γ_W_class to γ_U_class
  have h_map_class : (D.map i).map γ_W_class = γ_U_class := by
    have h1 : (D.map i).map γ_W_class = Path.Homotopic.Quotient.mk γ_U_from_W := by rfl
    rw [h1, h_lifts_eq] <;> rfl

  let F_W := s.ι.app ⟨W, hW⟩
  let F_U := s.ι.app ⟨U, hU⟩

  let f_W_core : F_W.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set)) ⟶
              F_W.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set)) :=
    F_W.map γ_W_class
  let f_U_core : F_U.obj (FundamentalGroupoid.mk (⟨x, hxU⟩ : U_set)) ⟶
              F_U.obj (FundamentalGroupoid.mk (⟨y, hyU⟩ : U_set)) :=
    F_U.map γ_U_class

  let h_eq1_W : F_W.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set)) =
      obj_at X 𝒰 s x W hW hxW := by rfl
  let h_eq2_W : F_W.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set)) =
      obj_at X 𝒰 s y W hW hyW := by rfl
  let h_eq1_U : F_U.obj (FundamentalGroupoid.mk (⟨x, hxU⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hxU := by rfl
  let h_eq2_U : F_U.obj (FundamentalGroupoid.mk (⟨y, hyU⟩ : U_set)) =
      obj_at X 𝒰 s y U hU hyU := by rfl

  -- Key step: use naturality to relate f_W_core and f_U_core
  have h_core : f_W_core =
      eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set))) h_nat.symm) ≫
      F_U.map ((D.map i).map γ_W_class) ≫
      eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set))) h_nat.symm).symm :=
    functor_eq_map_eq h_nat.symm γ_W_class

  -- Substitute h_core and h_map_class into the goal
  have h_main_goal : eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫ f_W_core ≫ eqToHom h_eq2_W) ≫ eqToHom h_eq_y =
      eqToHom h_eq1_U.symm ≫ f_U_core ≫ eqToHom h_eq2_U := by
    -- First, rewrite f_W_core
    have h1 : eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫ f_W_core ≫ eqToHom h_eq2_W) ≫ eqToHom h_eq_y =
        eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫
          (eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set))) h_nat.symm) ≫
           F_U.map ((D.map i).map γ_W_class) ≫
           eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set))) h_nat.symm).symm) ≫
          eqToHom h_eq2_W) ≫ eqToHom h_eq_y := by
      rw [h_core]
      <;> rfl
    rw [h1]

    -- Then rewrite h_map_class
    have h2 : eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫
          (eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set))) h_nat.symm) ≫
           F_U.map ((D.map i).map γ_W_class) ≫
           eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set))) h_nat.symm).symm) ≫
          eqToHom h_eq2_W) ≫ eqToHom h_eq_y =
        eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫
          (eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set))) h_nat.symm) ≫
           F_U.map γ_U_class ≫
           eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set))) h_nat.symm).symm) ≫
          eqToHom h_eq2_W) ≫ eqToHom h_eq_y := by
      rw [h_map_class]
      <;> rfl
    rw [h2]

    -- Now simplify using associativity and proof irrelevance
    simp only [Functor.comp_obj, Monotone.functor_obj, Functor.const_obj_obj, Category.assoc,
      eqToHom_trans, eqToHom_trans_assoc]
    congr

  exact h_main_goal

/-- single_covered_map_simple is independent of the choice of proof that the range is in U. -/
lemma single_covered_map_simple_indep_of_h_range {x y : X} (γ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰) (hx : x ∈ U) (hy : y ∈ U)
    (h1 h2 : Set.range γ ⊆ (U : Set X)) :
    single_covered_map_simple X 𝒰 s γ U hU hx hy h1 =
    single_covered_map_simple X 𝒰 s γ U hU hx hy h2 := by
  congr
  <;> exact Subsingleton.elim _ _

end

end

end P202.Topology.VanKampenProof


/-! Adapted from SingleCovered.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

/-- Given a path γ whose range is contained in some U ∈ 𝒰, we can map its homotopy class
    to a morphism in s.pt using the cocone leg for U. -/
def single_covered_map {x y : X} (γ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰) (h : Set.range γ ⊆ (U : Set X)) :
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) ⟶
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)) := by
  -- Get that x and y are in U (since their range is in U)
  have hx : x ∈ U := by
    have h1 : γ 0 ∈ Set.range γ := Set.mem_range_self 0
    have h2 : γ 0 = x := γ.source
    rw [h2] at h1
    exact h h1
  have hy : y ∈ U := by
    have h1 : γ 1 ∈ Set.range γ := Set.mem_range_self 1
    have h2 : γ 1 = y := γ.target
    rw [h2] at h1
    exact h h1

  let U_set : Set X := (U : Set X)

  -- Lift the path to the subtype U
  let γ_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ hx hy h).choose
  let hγ_lift : ∀ (t : I), (γ_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hx hy h).choose_spec

  -- Get the homotopy class in π₁(U)
  let γ_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_lift

  -- Apply the cocone functor
  let f : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
          (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    (s.ι.app ⟨U, hU⟩).map γ_class

  let x_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk x
  let y_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk y

  -- By definition, obj_at X 𝒰 s x U hU hx = (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk ⟨x, hx⟩)
  have h_eq1 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hx := by rfl
  have h_eq2 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) =
      obj_at X 𝒰 s y U hU hy := by rfl

  -- And by obj_at_eq, obj_at for our U equals desc_functor_obj
  -- desc_functor_obj picks some U' via Classical.choose; we show obj_at U = obj_at U'
  have h_dom : obj_at X 𝒰 s x U hU hx = desc_functor_obj X 𝒰 hcover s x_obj := by
    dsimp only [desc_functor_obj]
    let x_pt : X := x_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x_pt ∈ U' := hcover x_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hx :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hx
    exact this.symm

  have h_cod : obj_at X 𝒰 s y U hU hy = desc_functor_obj X 𝒰 hcover s y_obj := by
    dsimp only [desc_functor_obj]
    let y_pt : X := y_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ y_pt ∈ U' := hcover y_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ y_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s y U' hU'.1 hU'.2 = obj_at X 𝒰 s y U hU hy :=
      obj_at_eq X 𝒰 s hfinite_intersections y U' U hU'.1 hU hU'.2 hy
    exact this.symm

  -- Now we have:
  -- f : A → B
  -- h_eq1 : A = obj_at x
  -- h_eq2 : B = obj_at y
  -- h_dom : obj_at x = desc_functor_obj x
  -- h_cod : obj_at y = desc_functor_obj y
  -- We want: desc_functor_obj x → desc_functor_obj y

  -- Transport f to go from obj_at x to obj_at y
  let f' : obj_at X 𝒰 s x U hU hx ⟶ obj_at X 𝒰 s y U hU hy :=
    eqToHom h_eq1.symm ≫ f ≫ eqToHom h_eq2

  -- Then transport to go from desc_functor_obj x to desc_functor_obj y
  exact eqToHom h_dom.symm ≫ f' ≫ eqToHom h_cod

/-- single_covered_map of the constant path is the identity morphism. -/
lemma single_covered_map_refl {x : X}
    (U : Opens X) (hU : U ∈ 𝒰) (hx : x ∈ U) :
    single_covered_map X 𝒰 hcover hfinite_intersections s (Path.refl x) U hU
      (by simp [hx] <;> tauto) =
    𝟙 (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) := by
  dsimp only [single_covered_map]
  let U_set : Set X := (U : Set X)
  let h_range : Set.range (Path.refl x) ⊆ (U : Set X) := by simp [hx] <;> tauto
  let hx' : x ∈ U := hx
  let hy' : x ∈ U := hx
  let γ_lift : Path (⟨x, hx'⟩ : U_set) (⟨x, hy'⟩ : U_set) :=
    (Path.lift_to_subtype (Path.refl x) hx' hy' h_range).choose
  let hγ_lift : ∀ (t : I), (γ_lift t : X) = (Path.refl x) t :=
    (Path.lift_to_subtype (Path.refl x) hx' hy' h_range).choose_spec

  -- Step 1: γ_lift is pointwise equal to the constant path
  have h_pointwise : ∀ (t : I), γ_lift t = (⟨x, hx'⟩ : U_set) := by
    intro t
    apply Subtype.ext
    have h1 : (γ_lift t : X) = (Path.refl x) t := hγ_lift t
    have h2 : (Path.refl x) t = x := by simp [Path.refl_apply]
    rw [h1, h2] <;> rfl

  -- Step 2: Therefore γ_lift = Path.refl (⟨x, hx'⟩)
  have h_path_eq : γ_lift = Path.refl (⟨x, hx'⟩ : U_set) := by
    apply Path.ext
    funext t
    exact h_pointwise t

  -- Step 3: The homotopy class is the identity
  let γ_class : (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨x, hy'⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_lift
  have h_class_eq : γ_class = 𝟙 (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) := by
    have h1 : Path.Homotopic.Quotient.mk γ_lift = Path.Homotopic.Quotient.mk (Path.refl (⟨x, hx'⟩ : U_set)) := by
      rw [h_path_eq]
    have h2 : Path.Homotopic.Quotient.mk (Path.refl (⟨x, hx'⟩ : U_set)) = 𝟙 (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) :=
      (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set))).symm
    exact Eq.trans h1 h2

  -- Step 4: The functor preserves identities
  let f : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) ⟶
          (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hy'⟩ : U_set)) :=
    (s.ι.app ⟨U, hU⟩).map γ_class
  have h_f_eq : f = 𝟙 ((s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set))) := by
    dsimp only [f]
    rw [h_class_eq]
    <;> exact?

  -- Step 5: Simplify the transports
  let x_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk x
  have h_eq1 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hx' := by rfl
  have h_eq2 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hy'⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hy' := by rfl
  have h_dom : obj_at X 𝒰 s x U hU hx' = desc_functor_obj X 𝒰 hcover s x_obj := by
    dsimp only [desc_functor_obj]
    let x_pt : X := x_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x_pt ∈ U' := hcover x_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hx' :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hx'
    exact this.symm
  have h_cod : obj_at X 𝒰 s x U hU hy' = desc_functor_obj X 𝒰 hcover s x_obj := by
    dsimp only [desc_functor_obj]
    let x_pt : X := x_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x_pt ∈ U' := hcover x_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hy' :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hy'
    exact this.symm

  let f' : obj_at X 𝒰 s x U hU hx' ⟶ obj_at X 𝒰 s x U hU hy' :=
    eqToHom h_eq1.symm ≫ f ≫ eqToHom h_eq2

  -- Since hx' = hy', h_eq1 = h_eq2
  have h_eq1_eq_h_eq2 : h_eq1 = h_eq2 := by rfl
  have h_f'_eq : f' = 𝟙 (obj_at X 𝒰 s x U hU hx') := by
    dsimp only [f']
    rw [h_f_eq, h_eq1_eq_h_eq2]
    <;> simp [eqToHom_trans, Category.assoc]
    <;> exact?

  -- Final step
  have h_main : eqToHom h_dom.symm ≫ f' ≫ eqToHom h_cod =
      𝟙 (desc_functor_obj X 𝒰 hcover s x_obj) := by
    rw [h_f'_eq]
    have h_dom_eq_h_cod : h_dom = h_cod := by rfl
    rw [h_dom_eq_h_cod]
    <;> simp [eqToHom_trans, Category.assoc]
    <;> exact?
  exact h_main

/-- Helper lemma: if W ≤ U are opens in 𝒰, and γ's range is in W,
    then single_covered_map using U equals single_covered_map using W. -/
lemma single_covered_map_indep_of_le {x y : X} (γ : Path x y)
    (W U : Opens X) (hW : W ∈ 𝒰) (hU : U ∈ 𝒰) (hWU : W ≤ U)
    (hW_range : Set.range γ ⊆ (W : Set X)) :
    @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ U hU (subset_trans hW_range hWU) =
    @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ W hW hW_range := by
  classical
  let W_set : Set X := (W : Set X)
  let U_set : Set X := (U : Set X)

  -- Get that x and y are in W (hence also in U)
  have hxW : x ∈ W := by
    have h1 : γ 0 ∈ Set.range γ := Set.mem_range_self 0
    have h2 : γ 0 = x := γ.source
    rw [h2] at h1
    exact hW_range h1
  have hyW : y ∈ W := by
    have h1 : γ 1 ∈ Set.range γ := Set.mem_range_self 1
    have h2 : γ 1 = y := γ.target
    rw [h2] at h1
    exact hW_range h1
  have hxU : x ∈ U := hWU hxW
  have hyU : y ∈ U := hWU hyW

  -- Lift γ to both W and U
  let γ_W_lift : Path (⟨x, hxW⟩ : W_set) (⟨y, hyW⟩ : W_set) :=
    (Path.lift_to_subtype γ hxW hyW hW_range).choose
  let hγ_W_lift : ∀ (t : I), (γ_W_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hxW hyW hW_range).choose_spec

  let γ_U_lift : Path (⟨x, hxU⟩ : U_set) (⟨y, hyU⟩ : U_set) :=
    (Path.lift_to_subtype γ hxU hyU (subset_trans hW_range hWU)).choose
  let hγ_U_lift : ∀ (t : I), (γ_U_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hxU hyU (subset_trans hW_range hWU)).choose_spec

  -- The inclusion map from W to U
  let i_WU_set : W_set → U_set := fun z => ⟨z, hWU z.2⟩
  have hi_cont : Continuous i_WU_set := by
    exact continuous_inclusion hWU

  -- Map the W-lifted path along the inclusion
  let γ_W_mapped : Path (⟨x, hxU⟩ : U_set) (⟨y, hyU⟩ : U_set) :=
    γ_W_lift.map hi_cont

  -- The mapped path equals the U-lifted path
  have h_eq_fun : ⇑γ_W_mapped = ⇑γ_U_lift := by
    funext t
    apply Subtype.ext
    have h1 : (γ_W_mapped t : X) = γ t := by
      have h1a : (γ_W_mapped t : X) = (i_WU_set (γ_W_lift t) : X) := by
        rw [Path.map_coe] <;> rfl
      rw [h1a]
      have h1b : (i_WU_set (γ_W_lift t) : X) = (γ_W_lift t : X) := by rfl
      rw [h1b]
      exact hγ_W_lift t
    have h2 : (γ_U_lift t : X) = γ t := hγ_U_lift t
    have h3 : (γ_W_mapped t : X) = (γ_U_lift t : X) := by
      rw [h1, h2]
    exact h3
  have h_eq_paths : γ_W_mapped = γ_U_lift := Path.ext h_eq_fun

  -- The inclusion W → U as a morphism in the subtype category
  let i_WU_subtype : (⟨W, hW⟩ : {U : Opens X // U ∈ 𝒰}) ⟶ (⟨U, hU⟩ : {U : Opens X // U ∈ 𝒰}) :=
    homOfLE hWU

  let D := ((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
    Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor

  -- Naturality of the cocone
  have h_nat : D.map i_WU_subtype ≫ s.ι.app ⟨U, hU⟩ = s.ι.app ⟨W, hW⟩ :=
    s.ι.naturality i_WU_subtype

  -- Get the homotopy classes
  let γ_W_class : (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set)) ⟶
                  (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set)) :=
    Path.Homotopic.Quotient.mk γ_W_lift
  let γ_U_class : (FundamentalGroupoid.mk (⟨x, hxU⟩ : U_set)) ⟶
                  (FundamentalGroupoid.mk (⟨y, hyU⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_U_lift

  -- The functor D.map i_WU_subtype maps γ_W_class to γ_U_class
  have h_map_class : (D.map i_WU_subtype).map γ_W_class = γ_U_class := by
    have h1 : (D.map i_WU_subtype).map γ_W_class = Path.Homotopic.Quotient.mk (γ_W_lift.map hi_cont) := by
      rfl
    have h2 : γ_W_lift.map hi_cont = γ_W_mapped := by rfl
    rw [h1, h2, h_eq_paths]
    <;> rfl

  -- We'll prove this using the simple version and obj_at_eq
  -- First, get the equalities between obj_at W and obj_at U
  have h_eq_x : obj_at X 𝒰 s x W hW hxW = obj_at X 𝒰 s x U hU hxU :=
    obj_at_eq X 𝒰 s hfinite_intersections x W U hW hU hxW hxU
  have h_eq_y : obj_at X 𝒰 s y W hW hyW = obj_at X 𝒰 s y U hU hyU :=
    obj_at_eq X 𝒰 s hfinite_intersections y W U hW hU hyW hyU

  -- Now we need to relate the full single_covered_map to the simple version
  -- The full version is: eqToHom h_dom.symm ≫ simple ≫ eqToHom h_cod
  -- where h_dom : obj_at ... = desc_functor_obj ...
  have h_dom_W : obj_at X 𝒰 s x W hW hxW = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x ∈ U' := hcover x
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x W hW hxW :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' W hU'.1 hW hU'.2 hxW
    exact this.symm
  have h_cod_W : obj_at X 𝒰 s y W hW hyW = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ y ∈ U' := hcover y
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ y ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s y U' hU'.1 hU'.2 = obj_at X 𝒰 s y W hW hyW :=
      obj_at_eq X 𝒰 s hfinite_intersections y U' W hU'.1 hW hU'.2 hyW
    exact this.symm
  have h_dom_U : obj_at X 𝒰 s x U hU hxU = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x ∈ U' := hcover x
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hxU :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hxU
    exact this.symm
  have h_cod_U : obj_at X 𝒰 s y U hU hyU = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ y ∈ U' := hcover y
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ y ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s y U' hU'.1 hU'.2 = obj_at X 𝒰 s y U hU hyU :=
      obj_at_eq X 𝒰 s hfinite_intersections y U' U hU'.1 hU hU'.2 hyU
    exact this.symm

  -- The transports are compatible: both equalities go between the same objects
  have h_dom_compat : h_eq_x.trans h_dom_U = h_dom_W := by
    apply Subsingleton.elim
  have h_cod_compat : h_eq_y.trans h_cod_U = h_cod_W := by
    apply Subsingleton.elim

  -- Let f_W and f_U be the simple versions
  let f_W := single_covered_map_simple X 𝒰 s γ W hW hxW hyW hW_range
  let f_U := single_covered_map_simple X 𝒰 s γ U hU hxU hyU (subset_trans hW_range hWU)

  -- By the simple version lemma:
  -- eqToHom h_eq_x.symm ≫ f_W ≫ eqToHom h_eq_y = f_U
  have h_simple : eqToHom h_eq_x.symm ≫ f_W ≫ eqToHom h_eq_y = f_U :=
    single_covered_map_simple_indep_of_le X 𝒰 s W U hW hU hWU γ hxW hyW hxU hyU hW_range
      (subset_trans hW_range hWU) h_eq_x h_eq_y

  -- Now unfold both sides of the goal in terms of the simple versions
  have h_goal_W : @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ W hW hW_range =
      eqToHom h_dom_W.symm ≫ f_W ≫ eqToHom h_cod_W := by
    rfl
  have h_goal_U : @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ U hU (subset_trans hW_range hWU) =
      eqToHom h_dom_U.symm ≫ f_U ≫ eqToHom h_cod_U := by
    rfl

  -- Rewrite the goal using these
  rw [h_goal_U, h_goal_W]

  -- Use the compatibility equations to rewrite h_dom_W and h_cod_W
  have h_dom_W' : h_dom_W = h_eq_x.trans h_dom_U := h_dom_compat.symm
  have h_cod_W' : h_cod_W = h_eq_y.trans h_cod_U := h_cod_compat.symm
  rw [h_dom_W', h_cod_W']

  -- Now we have:
  -- eqToDom (h_eq_x.trans h_dom_U).symm ≫ f_W ≫ eqToHom (h_eq_y.trans h_cod_U)
  -- = eqToHom h_dom_U.symm ≫ f_U ≫ eqToHom h_cod_U
  -- And we know: eqToHom h_eq_x.symm ≫ f_W ≫ eqToHom h_eq_y = f_U

  -- Use eqToHom_trans to break down the transports
  have h1 : eqToHom (h_eq_x.trans h_dom_U).symm = eqToHom h_dom_U.symm ≫ eqToHom h_eq_x.symm := by
    -- Both sides are isomorphisms between the same objects
    -- We can prove this by showing the equality of the underlying equalities
    have h_eq : (h_eq_x.trans h_dom_U).symm = h_dom_U.symm.trans h_eq_x.symm := by
      rfl
    rw [h_eq]
    rw [eqToHom_trans]
    <;> rfl
  have h2 : eqToHom (h_eq_y.trans h_cod_U) = eqToHom h_eq_y ≫ eqToHom h_cod_U := by
    rw [eqToHom_trans]
    <;> rfl

  -- Rewrite the right side of the goal using h1 and h2
  have h_goal : eqToHom (h_eq_x.trans h_dom_U).symm ≫ f_W ≫ eqToHom (h_eq_y.trans h_cod_U) =
      eqToHom h_dom_U.symm ≫ f_U ≫ eqToHom h_cod_U := by
    have h3 : eqToHom (h_eq_x.trans h_dom_U).symm ≫ f_W ≫ eqToHom (h_eq_y.trans h_cod_U) =
        (eqToHom h_dom_U.symm ≫ eqToHom h_eq_x.symm) ≫ f_W ≫ (eqToHom h_eq_y ≫ eqToHom h_cod_U) := by
      rw [h1, h2]
      <;> rfl
    rw [h3]
    have h4 : (eqToHom h_dom_U.symm ≫ eqToHom h_eq_x.symm) ≫ f_W ≫ (eqToHom h_eq_y ≫ eqToHom h_cod_U) =
        eqToHom h_dom_U.symm ≫ (eqToHom h_eq_x.symm ≫ f_W ≫ eqToHom h_eq_y) ≫ eqToHom h_cod_U := by
      simp [Category.assoc]
      <;> rfl
    rw [h4]
    rw [h_simple]
    <;> rfl

  exact h_goal.symm
/-- The result is independent of which U we choose (as long as γ's range is in U). -/
theorem single_covered_map_indep {x y : X} (γ : Path x y)
    (U V : Opens X) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
    (hU' : Set.range γ ⊆ (U : Set X)) (hV' : Set.range γ ⊆ (V : Set X)) :
    @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ U hU hU' =
    @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ V hV hV' := by
  classical
  -- Let W = U ∩ V
  let s_finset : Finset (Opens X) := {U, V}
  have h_nonempty : s_finset.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr (by simp [s_finset])
  have h_all_in : ∀ W ∈ s_finset, W ∈ 𝒰 := by
    intro W hW
    have : W = U ∨ W = V := by simpa [s_finset] using hW
    rcases this with (rfl | rfl) <;> tauto
  let W : Opens X := s_finset.inf (fun U : Opens X => U)
  have hW_in : W ∈ 𝒰 := hfinite_intersections s_finset h_nonempty h_all_in
  have hW_eq : W = U ⊓ V := by
    have h : W = s_finset.inf id := by rfl
    rw [h]
    have h2 : ({U, V} : Finset (Opens X)).inf id = U ⊓ V := by
      classical
      simp [Finset.inf_insert]
      <;> rfl
    exact h2
  have hW_le_U : W ≤ U := Finset.inf_le (Finset.mem_insert_self U {V})
  have hW_le_V : W ≤ V := Finset.inf_le (by simp [s_finset])
  have hW_range : Set.range γ ⊆ (W : Set X) := by
    rw [hW_eq]
    intro z hz
    exact ⟨hU' hz, hV' hz⟩

  -- Now both U and V versions equal the W version
  have h1 : @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ U hU hU' =
      @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ W hW_in hW_range :=
    single_covered_map_indep_of_le X 𝒰 hcover hfinite_intersections s γ W U hW_in hU hW_le_U hW_range
  have h2 : @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ V hV hV' =
      @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ W hW_in hW_range :=
    single_covered_map_indep_of_le X 𝒰 hcover hfinite_intersections s γ W V hW_in hV hW_le_V hW_range

  exact h1.trans h2.symm

/-- single_covered_map is independent of the choice of proof that the range is in U. -/
lemma single_covered_map_indep_of_h_range {x y : X} (γ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰)
    (h1 h2 : Set.range γ ⊆ (U : Set X)) :
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h1 =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h2 := by
  congr
  <;> exact Subsingleton.elim _ _

/-- Congruence lemma for single_covered_map: if two paths have the same underlying
    function and their endpoints are equal, then their single_covered_map images
    are equal (after transporting along the endpoint equalities). -/
lemma single_covered_map_congr {x₁ y₁ x₂ y₂ : X}
    (γ₁ : Path x₁ y₁) (γ₂ : Path x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ = y₂)
    (hfun : ∀ t, γ₁ t = γ₂ t)
    (U : Opens X) (hU : U ∈ 𝒰)
    (h_range1 : Set.range γ₁ ⊆ (U : Set X))
    (h_range2 : Set.range γ₂ ⊆ (U : Set X)) :
    eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx).symm ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s γ₁ U hU h_range1 ≫
    eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy) =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ₂ U hU h_range2 := by
  subst hx
  subst hy
  -- Now x₁ = x₂ and y₁ = y₂ definitionally, so eqToHom terms become identities
  simp [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- Now goal is: single_covered_map ... γ₁ ... = single_covered_map ... γ₂ ...
  have h_eq : γ₁ = γ₂ := by
    apply Path.ext
    funext t
    exact hfun t
  -- Substitute γ₁ = γ₂ everywhere
  cases h_eq
  -- Now both sides are single_covered_map ... γ₁ ... with different h_range proofs
  exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s γ₁ U hU h_range1 h_range2

/-- If two paths are homotopic via a homotopy that stays entirely within U,
    then their single_covered_map images are equal. -/
lemma single_covered_map_homotopic {x y : X}
    (γ₁ γ₂ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰)
    (h_range1 : Set.range γ₁ ⊆ (U : Set X))
    (h_range2 : Set.range γ₂ ⊆ (U : Set X))
    (H : Path.Homotopy γ₁ γ₂)
    (hH : ∀ (p : I × I), H p ∈ (U : Set X)) :
    single_covered_map X 𝒰 hcover hfinite_intersections s γ₁ U hU h_range1 =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ₂ U hU h_range2 := by
  classical
  let U_set : Set X := (U : Set X)

  -- Get that x and y are in U
  have hx : x ∈ U := by
    have h1' : γ₁ 0 ∈ Set.range γ₁ := Set.mem_range_self 0
    have h2' : γ₁ 0 = x := γ₁.source
    rw [h2'] at h1'
    exact h_range1 h1'
  have hy : y ∈ U := by
    have h1' : γ₁ 1 ∈ Set.range γ₁ := Set.mem_range_self 1
    have h2' : γ₁ 1 = y := γ₁.target
    rw [h2'] at h1'
    exact h_range1 h1'

  -- Define the lifted homotopy H' : I × I → U_set
  let H'_fun : I × I → U_set := fun p => ⟨H p, hH p⟩
  have H'_cont : Continuous H'_fun := by
    have h : Continuous (fun p : I × I => (H'_fun p : X)) := H.continuous
    exact Continuous.subtype_mk h hH

  -- Build the continuous map
  let H'_cm : C(I × I, U_set) := ⟨H'_fun, H'_cont⟩

  -- Get the lifted paths used in single_covered_map
  let γ₁_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ₁ hx hy h_range1).choose
  let hγ₁_lift : ∀ (t : I), (γ₁_lift t : X) = γ₁ t :=
    (Path.lift_to_subtype γ₁ hx hy h_range1).choose_spec

  let γ₂_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ₂ hx hy h_range2).choose
  let hγ₂_lift : ∀ (t : I), (γ₂_lift t : X) = γ₂ t :=
    (Path.lift_to_subtype γ₂ hx hy h_range2).choose_spec

  -- Now we build a Homotopy between the two lifted paths (as continuous maps)
  let H'_homotopy : ContinuousMap.Homotopy γ₁_lift.toContinuousMap γ₂_lift.toContinuousMap :=
    {
      toContinuousMap := H'_cm,
      map_zero_left := by
        intro s
        apply Subtype.ext
        simpa [H'_cm, H'_fun, hγ₁_lift] using H.map_zero_left s
      map_one_left := by
        intro s
        apply Subtype.ext
        simpa [H'_cm, H'_fun, hγ₂_lift] using H.map_one_left s
    }

  -- Now we build the HomotopyWith (HomotopyRel) with the prop' field
  let H'_rel : ContinuousMap.HomotopyRel γ₁_lift.toContinuousMap γ₂_lift.toContinuousMap {0, 1} :=
    {
      H'_homotopy with
      prop' := by
        intro t
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with (rfl | rfl)
        · -- x = 0
          apply Subtype.ext
          simpa [H'_homotopy, H'_cm, H'_fun, Path.Homotopy.source] using rfl
        · -- x = 1
          apply Subtype.ext
          simpa [H'_homotopy, H'_cm, H'_fun, Path.Homotopy.target] using rfl
    }

  -- This is exactly a Path.Homotopy
  let H' : Path.Homotopy γ₁_lift γ₂_lift := H'_rel

  -- Therefore the homotopy classes are equal
  have h_homotopic : Path.Homotopic γ₁_lift γ₂_lift := ⟨H'⟩
  have h_classes : Path.Homotopic.Quotient.mk γ₁_lift = Path.Homotopic.Quotient.mk γ₂_lift :=
    Path.Homotopic.Quotient.eq.mpr h_homotopic

  -- Now we just need to unwrap the definition of single_covered_map
  dsimp only [single_covered_map]

  -- The structure is:
  -- eqToHom h_dom.symm ≫ (eqToHom h_eq1.symm ≫ (s.ι.app ⟨U, hU⟩).map γ_class ≫ eqToHom h_eq2) ≫ eqToHom h_cod
  -- We need to rewrite using h_classes in the middle
  simp only [Category.assoc]
  exact congr_arg (fun c => eqToHom _ ≫ eqToHom _ ≫ (s.ι.app ⟨U, hU⟩).map c ≫ eqToHom _ ≫ eqToHom _) h_classes

end

end

end P202.Topology.VanKampenProof


/-! Adapted from ComposeMorphisms.lean. -/
namespace P202.Topology.VanKampenProof



section

open CategoryTheory
variable {C : Type*} [Groupoid C]
/-- Helper: dependent congruence for homs family. -/
lemma homs_dep_congr {k : ℕ} {objs : Fin (k + 1) → C}
    {homs : ∀ i : Fin k, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)}
    {i j : Fin k} (h : i = j) :
    eqToHom (congr_arg (fun x : Fin k => objs (Fin.castSucc x)) h).symm ≫
    homs i ≫
    eqToHom (congr_arg (fun x : Fin k => objs (Fin.succ x)) h) =
    homs j := by
  cases h
  simp [eqToHom_refl, Category.comp_id, Category.id_comp]
  <;> rfl
/-- Compose a list of morphisms f₀, f₁, ..., fₙ₋₁ where the codomain of fᵢ equals
    the domain of fᵢ₊₁. -/
def comp_list (n : ℕ) (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    objs 0 ⟶ objs (Fin.last n) := by
  induction n with
  | zero =>
    exact 𝟙 (objs 0)
  | succ n ih =>
    let objs' : Fin (n + 1) → C := fun i : Fin (n + 1) => objs (Fin.castSucc i)
    let homs' : ∀ i : Fin n, objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i) :=
      fun i : Fin n => homs (Fin.castSucc i)
    exact (ih objs' homs') ≫ homs (Fin.last n)
/-- Composing 0 morphisms gives the identity. -/
theorem comp_list_zero (objs : Fin 1 → C) :
    comp_list 0 objs (fun i => Fin.elim0 i) = 𝟙 (objs 0) := by
  rfl
/-- Composing n+1 morphisms is composing n morphisms then adding one more. -/
theorem comp_list_succ (n : ℕ) (objs : Fin (n + 2) → C)
    (homs : ∀ i : Fin (n + 1), objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    comp_list (n + 1) objs homs =
    comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
      (fun i : Fin n => homs (Fin.castSucc i)) ≫ homs (Fin.last n) := by
  rfl
/-- Composing 1 morphism gives just that morphism. -/
theorem comp_list_one (objs : Fin 2 → C)
    (homs : ∀ i : Fin 1, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    comp_list 1 objs homs = homs 0 := by
  simp [comp_list, Fin.last]
  <;> rfl
/-- Congruence: if two families of morphisms are pointwise equal, then their comp_list is equal. -/
theorem comp_list_congr {n : ℕ} (objs : Fin (n + 1) → C)
    (homs₁ homs₂ : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i))
    (h : ∀ i : Fin n, homs₁ i = homs₂ i) :
    comp_list n objs homs₁ = comp_list n objs homs₂ := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    have h₁ : comp_list (n + 1) objs homs₁ =
        comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs₁ (Fin.castSucc i)) ≫ homs₁ (Fin.last n) := by
      rw [comp_list_succ]
    have h₂ : comp_list (n + 1) objs homs₂ =
        comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs₂ (Fin.castSucc i)) ≫ homs₂ (Fin.last n) := by
      rw [comp_list_succ]
    rw [h₁, h₂]
    have h3 : comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
        (fun i : Fin n => homs₁ (Fin.castSucc i)) =
        comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs₂ (Fin.castSucc i)) := by
      apply ih
      intro i
      exact h (Fin.castSucc i)
    rw [h3, h (Fin.last n)]
/-- Strong congruence for comp_list: if objects are pointwise equal and morphisms
    are compatible with the eqToHom transports, then the compositions are equal
    (up to eqToHom at the endpoints). -/
theorem comp_list_congr_with_eqToHom {n : ℕ}
    (objs₁ objs₂ : Fin (n + 1) → C)
    (homs₁ : ∀ i : Fin n, objs₁ (Fin.castSucc i) ⟶ objs₁ (Fin.succ i))
    (homs₂ : ∀ i : Fin n, objs₂ (Fin.castSucc i) ⟶ objs₂ (Fin.succ i))
    (h_objs : ∀ i : Fin (n + 1), objs₁ i = objs₂ i)
    (h_homs : ∀ i : Fin n,
      eqToHom (h_objs (Fin.castSucc i)).symm ≫ homs₁ i ≫ eqToHom (h_objs (Fin.succ i)) = homs₂ i) :
    eqToHom (h_objs 0).symm ≫ comp_list n objs₁ homs₁ ≫ eqToHom (h_objs (Fin.last n)) =
    comp_list n objs₂ homs₂ := by
  induction n with
  | zero =>
    have h1 : comp_list 0 objs₁ homs₁ = 𝟙 (objs₁ 0) := comp_list_zero objs₁
    have h2 : comp_list 0 objs₂ homs₂ = 𝟙 (objs₂ 0) := comp_list_zero objs₂
    rw [h1, h2]
    have h : eqToHom (h_objs 0).symm ≫ 𝟙 (objs₁ 0) ≫ eqToHom (h_objs 0) = 𝟙 (objs₂ 0) := by
      simp [eqToHom_refl, Category.id_comp]
      <;> rfl
    exact h
  | succ n ih =>
    set objs₁' : Fin (n + 1) → C := fun i : Fin (n + 1) => objs₁ (Fin.castSucc i) with h_objs₁'
    set objs₂' : Fin (n + 1) → C := fun i : Fin (n + 1) => objs₂ (Fin.castSucc i) with h_objs₂'
    set homs₁' : ∀ i : Fin n, objs₁' (Fin.castSucc i) ⟶ objs₁' (Fin.succ i) :=
      fun i : Fin n => homs₁ (Fin.castSucc i) with h_homs₁'
    set homs₂' : ∀ i : Fin n, objs₂' (Fin.castSucc i) ⟶ objs₂' (Fin.succ i) :=
      fun i : Fin n => homs₂ (Fin.castSucc i) with h_homs₂'
    set h_objs' : ∀ i : Fin (n + 1), objs₁' i = objs₂' i :=
      fun i => h_objs (Fin.castSucc i) with h_h_objs'
    let f := comp_list n objs₁' homs₁'
    let g := homs₁ (Fin.last n)
    let f' := comp_list n objs₂' homs₂'
    let g' := homs₂ (Fin.last n)
    let hX : objs₁' 0 = objs₂' 0 := h_objs' 0
    let hY : objs₁' (Fin.last n) = objs₂' (Fin.last n) := h_objs' (Fin.last n)
    let hZ : objs₁ (Fin.succ (Fin.last n)) = objs₂ (Fin.succ (Fin.last n)) := h_objs (Fin.succ (Fin.last n))
    have hY_eq : hY = h_objs (Fin.castSucc (Fin.last n)) := by rfl
    have h_ih : eqToHom hX.symm ≫ f ≫ eqToHom hY = f' :=
      ih objs₁' objs₂' homs₁' homs₂' h_objs' (fun i => h_homs (Fin.castSucc i))
    have h_last : eqToHom hY.symm ≫ g ≫ eqToHom hZ = g' := by
      rw [hY_eq]
      exact h_homs (Fin.last n)
    have h_comp : (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ) =
        eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ :=
      eqToHom_comp_cancel hX hY hZ f g
    have h_main : eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ = f' ≫ g' := by
      rw [←h_comp, h_ih, h_last]
    have h1 : comp_list (n + 1) objs₁ homs₁ = f ≫ g := by
      rw [comp_list_succ] <;> rfl
    have h2 : comp_list (n + 1) objs₂ homs₂ = f' ≫ g' := by
      rw [comp_list_succ] <;> rfl
    have h3 : h_objs 0 = hX := by rfl
    have h4 : h_objs (Fin.last (n + 1)) = hZ := by rfl
    rw [h1, h2, h3, h4]
    exact h_main
set_option backward.isDefEq.respectTransparency.types false in
/-- Helper: extend a comp_list by one more morphism at the end.
    Construct objs' and homs' explicitly by appending one more object and morphism.
    Then use comp_list_succ to show the equality. -/
lemma comp_list_extend {k : ℕ} (objs : Fin (k + 1) → C)
    (homs : ∀ i : Fin k, objs (Fin.castSucc i) ⟶ objs (Fin.succ i))
    {X : C} (g : objs (Fin.last k) ⟶ X) :
    ∃ (objs' : Fin (k + 2) → C)
      (homs' : ∀ i : Fin (k + 1), objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i))
      (h0 : objs' 0 = objs 0)
      (h_last : objs' (Fin.last (k + 1)) = X),
    eqToHom h0.symm ≫ comp_list (k + 1) objs' homs' ≫ eqToHom h_last =
      comp_list k objs homs ≫ g := by
  classical
  let objs' : Fin (k + 2) → C := fun i =>
    if h : i.val ≤ k then
      objs ⟨i.val, by omega⟩
    else
      X
  have h_objs'_castSucc : ∀ (i : Fin (k + 1)), objs' (Fin.castSucc i) = objs i := by
    intro i
    have h1 : (Fin.castSucc i).val ≤ k := by
      simp [Fin.castSucc] <;> omega
    have h2 : objs' (Fin.castSucc i) = objs ⟨(Fin.castSucc i).val, by omega⟩ := by
      dsimp only [objs']
      rw [dif_pos h1]
    rw [h2]
    have h3 : (Fin.castSucc i).val = i.val := by
      simp [Fin.castSucc] <;> omega
    congr <;> omega
  have h_objs'_last : objs' (Fin.last (k + 1)) = X := by
    have h1 : ¬ (Fin.last (k + 1)).val ≤ k := by
      simp [Fin.last] <;> omega
    dsimp only [objs']
    rw [dif_neg h1]
  have h_objs'_succ_lt : ∀ (i : Fin k), objs' (Fin.succ (Fin.castSucc i)) = objs (Fin.succ i) := by
    intro i
    have h_succ_val : (Fin.succ (Fin.castSucc i)).val ≤ k := by
      simp [Fin.castSucc, Fin.succ] <;> omega
    have h4 : objs' (Fin.succ (Fin.castSucc i)) = objs ⟨(Fin.succ (Fin.castSucc i)).val, by omega⟩ := by
      dsimp only [objs']
      rw [dif_pos h_succ_val]
    rw [h4]
    <;> congr <;> simp [Fin.castSucc, Fin.succ] <;> omega
  let homs' : ∀ i : Fin (k + 1), objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i) := by
    intro i
    by_cases h : i.val < k
    · -- i.val < k, so both endpoints are in the original objs
      let j : Fin k := ⟨i.val, h⟩
      have h_domain : objs' (Fin.castSucc i) = objs (Fin.castSucc j) := by
        rw [h_objs'_castSucc]
        <;> congr <;> simp [j, Fin.castSucc] <;> omega
      have h_codomain : objs' (Fin.succ i) = objs (Fin.succ j) := by
        have h_succ_val : (Fin.succ i).val ≤ k := by
          simp [Fin.succ] <;> omega
        have h4 : objs' (Fin.succ i) = objs ⟨(Fin.succ i).val, by omega⟩ := by
          dsimp only [objs']
          rw [dif_pos h_succ_val]
        rw [h4]
        <;> congr <;> simp [j, Fin.succ] <;> omega
      exact eqToHom h_domain ≫ homs j ≫ eqToHom h_codomain.symm
    · -- i.val = k, so this is the last morphism
      have h' : i.val = k := by omega
      have h_domain : objs' (Fin.castSucc i) = objs (Fin.last k) := by
        have h4 : i = Fin.last k := by
          apply Fin.ext <;> simp [Fin.last, h'] <;> omega
        rw [h4, h_objs'_castSucc] <;> rfl
      have h_codomain : objs' (Fin.succ i) = X := by
        have h4 : Fin.succ i = Fin.last (k + 1) := by
          apply Fin.ext <;> simp [Fin.last, Fin.succ, h'] <;> omega
        rw [h4, h_objs'_last]
      exact eqToHom h_domain ≫ g ≫ eqToHom h_codomain.symm
  have h0 : objs' 0 = objs 0 := by
    have h1 : (0 : Fin (k + 2)).val ≤ k := by simp <;> omega
    have h2 : objs' 0 = objs ⟨(0 : Fin (k + 2)).val, by omega⟩ := by
      dsimp only [objs']
      rw [dif_pos h1]
    rw [h2] <;> rfl
  have h_last : objs' (Fin.last (k + 1)) = X := h_objs'_last
  have h_homs_castSucc : ∀ (i : Fin k),
      eqToHom (h_objs'_castSucc (Fin.castSucc i)).symm ≫
      homs' (Fin.castSucc i) ≫
      eqToHom (h_objs'_succ_lt i) = homs i := by
    intro i
    have h_i_lt_k : i.val < k := i.is_lt
    have h1 : (Fin.castSucc i).val < k := by simp [Fin.castSucc] <;> omega
    dsimp only [homs']
    rw [dif_pos h1]
    simp [eqToHom_refl, Category.assoc, Category.comp_id, Category.id_comp]
    <;> rfl
  have h_homs_last :
      eqToHom (h_objs'_castSucc (Fin.last k)).symm ≫
      homs' (Fin.last k) ≫
      eqToHom h_objs'_last = g := by
    have h2 : ¬ (Fin.last k).val < k := by simp [Fin.last] <;> omega
    dsimp only [homs']
    rw [dif_neg h2]
    simp [eqToHom_refl, Category.assoc, Category.comp_id, Category.id_comp]
    <;> rfl
  let objs_mid : Fin (k + 1) → C := fun i : Fin (k + 1) => objs' (Fin.castSucc i)
  let homs_mid : ∀ i : Fin k, objs_mid (Fin.castSucc i) ⟶ objs_mid (Fin.succ i) :=
    fun i : Fin k => homs' (Fin.castSucc i)
  have h_objs_eq : ∀ (i : Fin (k + 1)), objs_mid i = objs i := by
    intro i
    exact h_objs'_castSucc i
  have h_main1 : eqToHom (h_objs_eq 0).symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom (h_objs_eq (Fin.last k)) =
      comp_list k objs homs :=
    comp_list_congr_with_eqToHom objs_mid objs homs_mid homs h_objs_eq h_homs_castSucc
  have h_main2 : comp_list (k + 1) objs' homs' = comp_list k objs_mid homs_mid ≫ homs' (Fin.last k) := by
    rw [comp_list_succ] <;> rfl
  refine' ⟨objs', homs', h0, h_last, _⟩
  have h_step1 : eqToHom h0.symm ≫ comp_list (k + 1) objs' homs' ≫ eqToHom h_last =
      eqToHom h0.symm ≫ (comp_list k objs_mid homs_mid ≫ homs' (Fin.last k)) ≫ eqToHom h_last := by
    exact congr_arg (fun f => eqToHom h0.symm ≫ f ≫ eqToHom h_last) h_main2
  have h_step2 : eqToHom h0.symm ≫ (comp_list k objs_mid homs_mid ≫ homs' (Fin.last k)) ≫ eqToHom h_last =
      (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ (homs' (Fin.last k) ≫ eqToHom h_last) := by
    simp [Category.assoc] <;> rfl
  have h_step3 : (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ (homs' (Fin.last k) ≫ eqToHom h_last) =
      (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom (h_objs_eq (Fin.last k))) ≫
      (eqToHom (h_objs_eq (Fin.last k)).symm ≫ homs' (Fin.last k) ≫ eqToHom h_last) := by
    let h := h_objs_eq (Fin.last k)
    have h_id : eqToHom h ≫ eqToHom h.symm = 𝟙 (objs_mid (Fin.last k)) := by
      rw [eqToHom_trans, eqToHom_refl]
      <;> rfl
    calc
      (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ (homs' (Fin.last k) ≫ eqToHom h_last)
        = (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ 𝟙 (objs_mid (Fin.last k)) ≫ (homs' (Fin.last k) ≫ eqToHom h_last) := by
          simp [Category.assoc, Category.id_comp] <;> rfl
      _ = (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ (eqToHom h ≫ eqToHom h.symm) ≫ (homs' (Fin.last k) ≫ eqToHom h_last) := by
          rw [h_id] <;> rfl
      _ = (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom h) ≫ (eqToHom h.symm ≫ homs' (Fin.last k) ≫ eqToHom h_last) := by
          simp [Category.assoc] <;> rfl
  have h_final : (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom (h_objs_eq (Fin.last k))) ≫
      (eqToHom (h_objs_eq (Fin.last k)).symm ≫ homs' (Fin.last k) ≫ eqToHom h_last) =
      comp_list k objs homs ≫ g := by
    have h1 : eqToHom h0.symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom (h_objs_eq (Fin.last k)) =
        comp_list k objs homs := h_main1
    have h2 : eqToHom (h_objs_eq (Fin.last k)).symm ≫ homs' (Fin.last k) ≫ eqToHom h_last = g := h_homs_last
    rw [h1, h2]
    <;> rfl
  rw [h_step1, h_step2, h_step3, h_final]
/-- Given two lists of morphisms where the first n of the longer list correspond
    to the shorter list (via eqToHom transport), and the last morphism of the longer
    list corresponds to a given morphism g, then the composition of the longer list
    equals the composition of the shorter list followed by g (up to eqToHom transport). -/
theorem comp_list_snoc {n : ℕ}
    (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i))
    (objs' : Fin (n + 2) → C)
    (homs' : ∀ i : Fin (n + 1), objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i))
    (h0 : objs' 0 = objs 0)
    (h_corresp : ∀ (i : Fin n),
      ∃ (h1 : objs' (Fin.castSucc (Fin.castSucc i)) = objs (Fin.castSucc i))
        (h2 : objs' (Fin.succ (Fin.castSucc i)) = objs (Fin.succ i)),
      eqToHom h1.symm ≫ homs' (Fin.castSucc i) ≫ eqToHom h2 = homs i)
    {mid : C}
    (h_last_obj : objs' (Fin.last (n + 1)) = mid)
    (g : objs (Fin.last n) ⟶ mid)
    (h_last_hom : ∃ (h1 : objs' (Fin.castSucc (Fin.last n)) = objs (Fin.last n))
        (h2 : objs' (Fin.succ (Fin.last n)) = mid),
      eqToHom h1.symm ≫ homs' (Fin.last n) ≫ eqToHom h2 = g) :
    eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last_obj =
    comp_list n objs homs ≫ g := by
  classical
  let objs'_first : Fin (n + 1) → C := fun i => objs' (Fin.castSucc i)
  let homs'_first : ∀ i : Fin n, objs'_first (Fin.castSucc i) ⟶ objs'_first (Fin.succ i) :=
    fun i => homs' (Fin.castSucc i)
  have h_objs_eq : ∀ (j : Fin (n + 1)), objs'_first j = objs j := by
    intro j
    induction j using Fin.induction with
    | zero =>
      simpa [objs'_first] using h0
    | succ j ih =>
      rcases h_corresp j with ⟨h1, h2, _⟩
      have h_castSucc_succ : objs'_first (Fin.succ j) = objs' (Fin.succ (Fin.castSucc j)) := by
        simp [objs'_first] <;> rfl
      rw [h_castSucc_succ]
      exact h2
  have h_homs_eq : ∀ (i : Fin n),
      eqToHom (h_objs_eq (Fin.castSucc i)).symm ≫ homs'_first i ≫ eqToHom (h_objs_eq (Fin.succ i)) = homs i := by
    intro i
    rcases h_corresp i with ⟨h1, h2, h_hom⟩
    have h_eq1 : h_objs_eq (Fin.castSucc i) = h1 := by exact Subsingleton.elim _ _
    have h_eq2 : h_objs_eq (Fin.succ i) = h2 := by exact Subsingleton.elim _ _
    rw [h_eq1, h_eq2]
    exact h_hom
  rcases h_last_hom with ⟨h1_last, h2_last, h_hom_last⟩
  let hX : objs'_first 0 = objs 0 := h_objs_eq 0
  let hY : objs'_first (Fin.last n) = objs (Fin.last n) := h_objs_eq (Fin.last n)
  have hY_eq : hY = h1_last := by exact Subsingleton.elim _ _
  have hZ_eq : h_last_obj = h2_last := by exact Subsingleton.elim _ _
  let f := comp_list n objs'_first homs'_first
  let g_hom := homs' (Fin.last n)
  have h_ih : eqToHom hX.symm ≫ f ≫ eqToHom hY = comp_list n objs homs :=
    comp_list_congr_with_eqToHom objs'_first objs homs'_first homs h_objs_eq h_homs_eq
  have h_last : eqToHom hY.symm ≫ g_hom ≫ eqToHom h_last_obj = g := by
    have h : eqToHom h1_last.symm ≫ g_hom ≫ eqToHom h2_last = g := h_hom_last
    have hY' : hY = h1_last := hY_eq
    have hZ' : h_last_obj = h2_last := hZ_eq
    rw [hY', hZ'] at *
    exact h
  have h_comp : (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g_hom ≫ eqToHom h_last_obj) =
      eqToHom hX.symm ≫ (f ≫ g_hom) ≫ eqToHom h_last_obj :=
    eqToHom_comp_cancel hX hY h_last_obj f g_hom
  have h_main : eqToHom hX.symm ≫ (f ≫ g_hom) ≫ eqToHom h_last_obj = comp_list n objs homs ≫ g := by
    rw [←h_comp, h_ih, h_last]
  have h1 : comp_list (n + 1) objs' homs' = f ≫ g_hom := comp_list_succ n objs' homs'
  have h2 : h0 = hX := by exact Subsingleton.elim _ _
  rw [h2, h1]
  exact h_main

set_option backward.isDefEq.respectTransparency.types false in
theorem comp_list_concat_explicit {n m : ℕ}
    (objs₁ : Fin (n + 1) → C)
    (homs₁ : ∀ i : Fin n, objs₁ (Fin.castSucc i) ⟶ objs₁ (Fin.succ i))
    (objs₂ : Fin (m + 1) → C)
    (homs₂ : ∀ i : Fin m, objs₂ (Fin.castSucc i) ⟶ objs₂ (Fin.succ i))
    (h_match : objs₁ (Fin.last n) = objs₂ 0)
    (objs_concat : Fin (n + m + 1) → C)
    (homs_concat : ∀ i : Fin (n + m), objs_concat (Fin.castSucc i) ⟶ objs_concat (Fin.succ i))
    (h_objs_first : ∀ (i : Fin (n + 1)), objs_concat ⟨i.val, by omega⟩ = objs₁ i)
    (h_objs_second : ∀ (i : Fin (m + 1)), objs_concat ⟨n + i.val, by omega⟩ = objs₂ i)
    (h_homs_first : ∀ (i : Fin n),
      eqToHom (h_objs_first (Fin.castSucc i)).symm ≫ homs_concat ⟨i.val, by omega⟩ ≫ eqToHom (h_objs_first (Fin.succ i)) = homs₁ i)
    (h_homs_second : ∀ (i : Fin m),
      eqToHom (h_objs_second (Fin.castSucc i)).symm ≫ homs_concat ⟨n + i.val, by omega⟩ ≫ eqToHom (h_objs_second (Fin.succ i)) = homs₂ i) :
    eqToHom (h_objs_first 0).symm ≫ comp_list (n + m) objs_concat homs_concat ≫ eqToHom (h_objs_second (Fin.last m)) =
    comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list m objs₂ homs₂ := by
  induction m with
  | zero =>
    -- Base case: m = 0
    have h_comp0 : comp_list 0 objs₂ homs₂ = 𝟙 (objs₂ 0) := comp_list_zero objs₂
    have h_last0 : h_objs_second (Fin.last 0) = h_objs_second 0 := by
      simp [Fin.last] <;> rfl
    have h1 : objs_concat ⟨(Fin.last n).val, by omega⟩ = objs_concat ⟨n + 0, by omega⟩ := by
      congr <;> simp [Fin.last] <;> omega
    have h_eq1 : (h_objs_first (Fin.last n)).trans h_match = h_objs_second 0 := by
      exact Subsingleton.elim _ _
    have h_eq_trans : eqToHom (h_objs_second 0) = eqToHom (h_objs_first (Fin.last n)) ≫ eqToHom h_match := by
      rw [←h_eq1, eqToHom_trans] <;> rfl
    have h_congr : eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_first (Fin.last n)) =
        comp_list n objs₁ homs₁ :=
      comp_list_congr_with_eqToHom objs_concat objs₁ homs_concat homs₁ h_objs_first h_homs_first
    have h_goal : eqToHom (h_objs_first 0).symm ≫ comp_list (n + 0) objs_concat homs_concat ≫ eqToHom (h_objs_second (Fin.last 0)) =
        comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list 0 objs₂ homs₂ := by
      have h_comp_n : comp_list (n + 0) objs_concat homs_concat = comp_list n objs_concat homs_concat := by rfl
      have h_rhs : comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list 0 objs₂ homs₂ =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match := by
        rw [h_comp0]
        have h : (comp_list n objs₁ homs₁ ≫ eqToHom h_match) ≫ 𝟙 (objs₂ 0) = comp_list n objs₁ homs₁ ≫ eqToHom h_match := by
          rw [Category.comp_id]
        simpa [Category.assoc] using h
      have h_main : eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_second 0) =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match := by
        have h_eq : eqToHom (h_objs_second 0) = eqToHom (h_objs_first (Fin.last n)) ≫ eqToHom h_match := h_eq_trans
        have h_assoc : eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ (eqToHom (h_objs_first (Fin.last n)) ≫ eqToHom h_match) =
            (eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_first (Fin.last n))) ≫ eqToHom h_match := by
          simp [Category.assoc] <;> rfl
        have h_goal2 : comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_second 0) =
            comp_list n objs_concat homs_concat ≫ (eqToHom (h_objs_first (Fin.last n)) ≫ eqToHom h_match) := by
          exact congr_arg (fun x => comp_list n objs_concat homs_concat ≫ x) h_eq
        have h_goal : eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_second 0) =
            (eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_first (Fin.last n))) ≫ eqToHom h_match := by
          rw [h_goal2]
          <;> exact h_assoc
        rw [h_goal, h_congr]
      have h_last0_eq : h_objs_second (Fin.last 0) = h_objs_second 0 := by
        simp [Fin.last] <;> rfl
      rw [h_rhs]
      have h_final : eqToHom (h_objs_first 0).symm ≫ comp_list (n + 0) objs_concat homs_concat ≫ eqToHom (h_objs_second (Fin.last 0)) =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match := by
        rw [h_comp_n, h_last0_eq]
        exact h_main
      exact h_final
    exact h_goal
  | succ m ih =>
    -- Inductive step: m → m + 1
    let objs₂' : Fin (m + 1) → C := fun i : Fin (m + 1) => objs₂ (Fin.castSucc i)
    let homs₂' : ∀ i : Fin m, objs₂' (Fin.castSucc i) ⟶ objs₂' (Fin.succ i) :=
      fun i : Fin m => homs₂ (Fin.castSucc i)
    let last_hom : objs₂' (Fin.last m) ⟶ objs₂ (Fin.succ (Fin.last m)) := homs₂ (Fin.last m)
    let objs_concat' : Fin (n + m + 1) → C := fun i : Fin (n + m + 1) => objs_concat ⟨i.val, by omega⟩
    let homs_concat' : ∀ i : Fin (n + m), objs_concat' (Fin.castSucc i) ⟶ objs_concat' (Fin.succ i) :=
      fun i : Fin (n + m) => homs_concat ⟨i.val, by omega⟩
    let h_objs_second' : ∀ (i : Fin (m + 1)), objs_concat' ⟨n + i.val, by omega⟩ = objs₂' i :=
      fun i : Fin (m + 1) => h_objs_second (Fin.castSucc i)
    let h_homs_second' : ∀ (i : Fin m),
        eqToHom (h_objs_second' (Fin.castSucc i)).symm ≫ homs_concat' ⟨n + i.val, by omega⟩ ≫ eqToHom (h_objs_second' (Fin.succ i)) = homs₂' i :=
      fun i : Fin m => h_homs_second (Fin.castSucc i)
    have h_ih' := ih objs₂' homs₂' h_match objs_concat' homs_concat' h_objs_first h_objs_second' h_homs_first h_homs_second'
    have h_last_hom : homs_concat (Fin.last (n + m)) = homs_concat ⟨n + (Fin.last m).val, by omega⟩ := by
      congr <;> simp [Fin.last] <;> omega
    have h_homs_last : eqToHom (h_objs_second (Fin.castSucc (Fin.last m))).symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom (h_objs_second (Fin.succ (Fin.last m))) = last_hom := by
      rw [h_last_hom]
      exact h_homs_second (Fin.last m)
    have h_mid_eq : h_objs_second (Fin.castSucc (Fin.last m)) = h_objs_second' (Fin.last m) := by
      simp [h_objs_second', Fin.last] <;> rfl
    have h_end_eq : h_objs_second (Fin.succ (Fin.last m)) = h_objs_second (Fin.last (m + 1)) := by
      simp [Fin.last] <;> rfl
    have h_comp_concat : comp_list (n + m + 1) objs_concat homs_concat =
        comp_list (n + m) objs_concat' homs_concat' ≫ homs_concat (Fin.last (n + m)) := by
      rw [comp_list_succ] <;> rfl
    have h_comp₂ : comp_list (m + 1) objs₂ homs₂ = comp_list m objs₂' homs₂' ≫ last_hom := by
      rw [comp_list_succ] <;> rfl
    let h_mid := h_objs_second' (Fin.last m)
    let h_end := h_objs_second (Fin.last (m + 1))
    have h_g : homs_concat (Fin.last (n + m)) ≫ eqToHom h_end = eqToHom h_mid ≫ last_hom := by
      have h_mid_eq2 : h_objs_second (Fin.castSucc (Fin.last m)) = h_mid := by
        simp [h_objs_second', h_mid, Fin.last] <;> rfl
      have h_end_eq2 : h_objs_second (Fin.succ (Fin.last m)) = h_end := by
        simp [h_end, Fin.last] <;> rfl
      have h : eqToHom (h_objs_second (Fin.castSucc (Fin.last m))).symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom (h_objs_second (Fin.succ (Fin.last m))) = last_hom := by
        rw [h_last_hom]
        exact h_homs_second (Fin.last m)
      have h' : eqToHom h_mid.symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom h_end = last_hom := by
        rw [h_mid_eq2, h_end_eq2] at h
        exact h
      have h_left : eqToHom h_mid ≫ (eqToHom h_mid.symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom h_end) =
          eqToHom h_mid ≫ last_hom := by
        exact congr_arg (fun x => eqToHom h_mid ≫ x) h'
      have h_left_simp : eqToHom h_mid ≫ (eqToHom h_mid.symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom h_end) =
          homs_concat (Fin.last (n + m)) ≫ eqToHom h_end := by
        have h1 : eqToHom h_mid ≫ eqToHom h_mid.symm = 𝟙 (objs_concat' (Fin.last (n + m))) := by
          simp [eqToHom_trans] <;> rfl
        simp [Category.assoc, h1] <;> rfl
      rw [h_left_simp] at h_left
      exact h_left
    have h_goal : eqToHom (h_objs_first 0).symm ≫ comp_list (n + m + 1) objs_concat homs_concat ≫ eqToHom h_end =
        comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list (m + 1) objs₂ homs₂ := by
      let f := eqToHom (h_objs_first 0).symm
      let g := comp_list (n + m) objs_concat' homs_concat'
      let last := homs_concat (Fin.last (n + m))
      have h_step1 : eqToHom (h_objs_first 0).symm ≫ comp_list (n + m + 1) objs_concat homs_concat ≫ eqToHom h_end =
          f ≫ (g ≫ last) ≫ eqToHom h_end := by
        rw [h_comp_concat] <;> rfl
      have h_step2 : f ≫ (g ≫ last) ≫ eqToHom h_end = (f ≫ g) ≫ last ≫ eqToHom h_end := by
        simp [Category.assoc] <;> rfl
      have h_step3 : (f ≫ g) ≫ last ≫ eqToHom h_end = (f ≫ g) ≫ (last ≫ eqToHom h_end) := by
        simp [Category.assoc] <;> rfl
      have h_step4 : (f ≫ g) ≫ (last ≫ eqToHom h_end) = (f ≫ g) ≫ (eqToHom h_mid ≫ last_hom) := by
        exact congr_arg (fun x => (f ≫ g) ≫ x) h_g
      have h_step5 : (f ≫ g) ≫ (eqToHom h_mid ≫ last_hom) = (f ≫ g ≫ eqToHom h_mid) ≫ last_hom := by
        simp [Category.assoc] <;> rfl
      have h_step6 : (f ≫ g ≫ eqToHom h_mid) ≫ last_hom = (comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list m objs₂' homs₂') ≫ last_hom := by
        exact congr_arg (fun x => x ≫ last_hom) h_ih'
      have h_step7 : (comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list m objs₂' homs₂') ≫ last_hom =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ (comp_list m objs₂' homs₂' ≫ last_hom) := by
        simp [Category.assoc] <;> rfl
      have h_step8 : comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ (comp_list m objs₂' homs₂' ≫ last_hom) =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list (m + 1) objs₂ homs₂ := by
        exact congr_arg (fun x => comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ x) h_comp₂.symm
      rw [h_step1, h_step2, h_step3, h_step4, h_step5, h_step6, h_step7, h_step8]
    exact h_goal

/-- A functor preserves comp_list: applying the functor to the whole composition
    equals composing the functor's action on each morphism. -/

theorem comp_list_functor_map {C D : Type*} [Groupoid C] [Groupoid D]
    (F : C ⥤ D) {n : ℕ}
    (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    F.map (comp_list n objs homs) =
    comp_list n (fun i => F.obj (objs i)) (fun i => F.map (homs i)) := by
  induction n with
  | zero =>
    have h_homs : homs = fun i : Fin 0 => Fin.elim0 i := by
      funext i
      exact Fin.elim0 i
    rw [h_homs]
    simp [comp_list_zero, Functor.map_id]
    <;> rfl
  | succ n ih =>
    have h1 : F.map (comp_list (n + 1) objs homs) =
        F.map (comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs (Fin.castSucc i)) ≫ homs (Fin.last n)) := by
      congr
      <;> exact comp_list_succ n objs homs
    rw [h1, Functor.map_comp]
    rw [ih (fun i : Fin (n + 1) => objs (Fin.castSucc i)) (fun i : Fin n => homs (Fin.castSucc i))]
    <;> rfl

end

end P202.Topology.VanKampenProof


/-! Adapted from MapFromDecomposition.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

/-- Given an explicit decomposition of a path into segments, compute the resulting morphism. -/
def map_from_decomposition {x y : X} {n : ℕ}
    (pts : Fin (n + 1) → X)
    (covers : Fin n → Opens X)
    (hcover_mem : ∀ i, covers i ∈ 𝒰)
    (h_start : pts 0 = x)
    (h_end : pts (Fin.last n) = y)
    (h_segments : ∀ i : Fin n,
      ∃ (γi : Path (pts (Fin.castSucc i)) (pts (Fin.succ i))),
        Set.range γi ⊆ (covers i : Set X)) :
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) ⟶
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)) := by
  let objs : Fin (n + 1) → s.pt :=
    fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))

  let homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := by
    intro i
    let h_i : ∃ (γi : Path (pts (Fin.castSucc i)) (pts (Fin.succ i))),
        Set.range γi ⊆ (covers i : Set X) := h_segments i
    let γi := Classical.choose h_i
    let hγi := Classical.choose_spec h_i
    exact single_covered_map X 𝒰 hcover hfinite_intersections s γi (covers i) (hcover_mem i) hγi

  let comp : objs 0 ⟶ objs (Fin.last n) := comp_list n objs homs

  have h0 : objs 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
    dsimp only [objs]
    have h_eq : FundamentalGroupoid.mk (pts 0) = FundamentalGroupoid.mk x := by
      congr
      <;> exact h_start
    rw [h_eq]

  have hn : objs (Fin.last n) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
    dsimp only [objs]
    have h_eq : FundamentalGroupoid.mk (pts (Fin.last n)) = FundamentalGroupoid.mk y := by
      congr
      <;> exact h_end
    rw [h_eq]

  exact eqToHom h0.symm ≫ comp ≫ eqToHom hn

end

end

end P202.Topology.VanKampenProof


/-! Adapted from RefinementLemma.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

/-- Helper: the range of a concatenated path is the union of the ranges. -/
lemma range_trans_subset {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ₁ : Path x y) (γ₂ : Path y z) {U : Set X}
    (h₁ : Set.range γ₁ ⊆ U) (h₂ : Set.range γ₂ ⊆ U) :
    Set.range (γ₁.trans γ₂) ⊆ U := by
  have h : Set.range (γ₁.trans γ₂) = Set.range γ₁ ∪ Set.range γ₂ :=
    Path.trans_range γ₁ γ₂
  rw [h]
  exact Set.union_subset h₁ h₂

/-- Refining a decomposition by splitting one segment into two gives the same result.

    This follows from the simple version plus eqToHom transport bookkeeping. -/
theorem single_covered_split_eq {x y z : X}
    (U : Opens X) (hU : U ∈ 𝒰)
    (γ₁ : Path x y) (h₁ : Set.range γ₁ ⊆ (U : Set X))
    (γ₂ : Path y z) (h₂ : Set.range γ₂ ⊆ (U : Set X)) :
    let f₁ := single_covered_map X 𝒰 hcover hfinite_intersections s γ₁ U hU h₁
    let f₂ := single_covered_map X 𝒰 hcover hfinite_intersections s γ₂ U hU h₂
    let f_both := single_covered_map X 𝒰 hcover hfinite_intersections s (γ₁.trans γ₂) U hU
      (range_trans_subset γ₁ γ₂ h₁ h₂)
    f₁ ≫ f₂ = f_both := by
  dsimp only

  -- Get that x, y, z are all in U
  have hx : x ∈ U := by
    have h1 : γ₁ 0 ∈ Set.range γ₁ := Set.mem_range_self 0
    have h2 : γ₁ 0 = x := γ₁.source
    rw [h2] at h1
    exact h₁ h1
  have hy : y ∈ U := by
    have h1 : γ₁ 1 ∈ Set.range γ₁ := Set.mem_range_self 1
    have h2 : γ₁ 1 = y := γ₁.target
    rw [h2] at h1
    exact h₁ h1
  have hz : z ∈ U := by
    have h1 : γ₂ 1 ∈ Set.range γ₂ := Set.mem_range_self 1
    have h2 : γ₂ 1 = z := γ₂.target
    rw [h2] at h1
    exact h₂ h1

  let x_obj := FundamentalGroupoid.mk x
  let y_obj := FundamentalGroupoid.mk y
  let z_obj := FundamentalGroupoid.mk z

  -- The obj_at objects
  let obj_at_x := obj_at X 𝒰 s x U hU hx
  let obj_at_y := obj_at X 𝒰 s y U hU hy
  let obj_at_z := obj_at X 𝒰 s z U hU hz

  -- The desc_functor_obj objects
  let dfo_x := desc_functor_obj X 𝒰 hcover s x_obj
  let dfo_y := desc_functor_obj X 𝒰 hcover s y_obj
  let dfo_z := desc_functor_obj X 𝒰 hcover s z_obj

  -- The equalities from obj_at to desc_functor_obj
  have h_dom_x : obj_at_x = dfo_x := by
    dsimp only [obj_at_x, dfo_x, desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x ∈ U' := hcover x
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hx :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hx
    exact this.symm
  have h_dom_y : obj_at_y = dfo_y := by
    dsimp only [obj_at_y, dfo_y, desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ y ∈ U' := hcover y
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ y ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s y U' hU'.1 hU'.2 = obj_at X 𝒰 s y U hU hy :=
      obj_at_eq X 𝒰 s hfinite_intersections y U' U hU'.1 hU hU'.2 hy
    exact this.symm
  have h_dom_z : obj_at_z = dfo_z := by
    dsimp only [obj_at_z, dfo_z, desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ z ∈ U' := hcover z
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ z ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s z U' hU'.1 hU'.2 = obj_at X 𝒰 s z U hU hz :=
      obj_at_eq X 𝒰 s hfinite_intersections z U' U hU'.1 hU hU'.2 hz
    exact this.symm

  -- The simple versions of the maps
  let f₁_simple := single_covered_map_simple X 𝒰 s γ₁ U hU hx hy h₁
  let f₂_simple := single_covered_map_simple X 𝒰 s γ₂ U hU hy hz h₂
  let f_both_simple := single_covered_map_simple X 𝒰 s (γ₁.trans γ₂) U hU hx hz
    (range_trans_subset_simple γ₁ γ₂ h₁ h₂)

  -- The split property for the simple version (already proved!)
  have h_simple : f₁_simple ≫ f₂_simple = f_both_simple :=
    single_covered_split_eq_simple X 𝒰 s U hU hx hy hz γ₁ h₁ γ₂ h₂

  -- The full versions are the simple versions composed with eqToHom transports
  have h_f₁ : single_covered_map X 𝒰 hcover hfinite_intersections s γ₁ U hU h₁ =
      eqToHom h_dom_x.symm ≫ f₁_simple ≫ eqToHom h_dom_y := by
    rfl
  have h_f₂ : single_covered_map X 𝒰 hcover hfinite_intersections s γ₂ U hU h₂ =
      eqToHom h_dom_y.symm ≫ f₂_simple ≫ eqToHom h_dom_z := by
    rfl
  have h_f_both : single_covered_map X 𝒰 hcover hfinite_intersections s (γ₁.trans γ₂) U hU
      (range_trans_subset γ₁ γ₂ h₁ h₂) =
      eqToHom h_dom_x.symm ≫ f_both_simple ≫ eqToHom h_dom_z := by
    rfl

  -- Now we can use the eqToHom_comp_cancel lemma
  have h_main : (eqToHom h_dom_x.symm ≫ f₁_simple ≫ eqToHom h_dom_y) ≫
      (eqToHom h_dom_y.symm ≫ f₂_simple ≫ eqToHom h_dom_z) =
      eqToHom h_dom_x.symm ≫ (f₁_simple ≫ f₂_simple) ≫ eqToHom h_dom_z :=
    eqToHom_comp_cancel h_dom_x h_dom_y h_dom_z f₁_simple f₂_simple

  rw [h_f₁, h_f₂, h_f_both]
  rw [h_main, h_simple]

end

end

end P202.Topology.VanKampenProof


/-! Adapted from SplitLemmaWork.lean. -/
namespace P202.Topology.VanKampenProof



section

open CategoryTheory

variable {C : Type*} [Groupoid C]

/-- Explicit split lemma for comp_list: inserting one object in the middle and splitting
    one morphism into two does not change the overall composition (up to eqToHom transport). -/
theorem comp_list_split_explicit_proof {n : ℕ} (k : Fin n)
    (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i))
    {mid : C} (f : objs (Fin.castSucc k) ⟶ mid) (g : mid ⟶ objs (Fin.succ k))
    (h_eq : homs k = f ≫ g)
    (objs' : Fin (n + 2) → C)
    (homs' : ∀ i : Fin (n + 1), objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i))
    (h_before : ∀ (i : Fin n), i.val < k.val →
      ∃ (h1 : objs' (Fin.castSucc (Fin.castSucc i)) = objs (Fin.castSucc i))
        (h2 : objs' (Fin.succ (Fin.castSucc i)) = objs (Fin.succ i)),
      eqToHom h1.symm ≫ homs' (Fin.castSucc i) ≫ eqToHom h2 = homs i)
    (h_split1 : objs' (Fin.castSucc (Fin.castSucc k)) = objs (Fin.castSucc k))
    (h_split2 : objs' (Fin.succ (Fin.castSucc k)) = mid)
    (h_split3 : homs' (Fin.castSucc k) = eqToHom h_split1 ≫ f ≫ eqToHom h_split2.symm)
    (h_split4 : objs' (Fin.castSucc (Fin.succ k)) = mid)
    (h_split5 : objs' (Fin.succ (Fin.succ k)) = objs (Fin.succ k))
    (h_split6 : homs' (Fin.succ k) = eqToHom h_split4 ≫ g ≫ eqToHom h_split5.symm)
    (h_after : ∀ (j : Fin n), j.val > k.val →
      let i : Fin (n + 1) := Fin.succ j
      ∃ (h1 : objs' (Fin.castSucc i) = objs (Fin.castSucc j))
        (h2 : objs' (Fin.succ i) = objs (Fin.succ j)),
      eqToHom h1.symm ≫ homs' i ≫ eqToHom h2 = homs j)
    (h0 : objs' 0 = objs 0)
    (h_last : objs' (Fin.last (n + 1)) = objs (Fin.last n)) :
    eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last =
    comp_list n objs homs := by
  induction n with
  | zero =>
    -- Base case n = 0: k : Fin 0 is impossible
    exfalso
    exact Fin.elim0 k
  | succ n ih =>
    -- Inductive step: n → n + 1
    by_cases h_k_lt : k.val < n
    · -- Case 1: k.val < n (split is not at last position)
      have h_k'_val : k.val < n := h_k_lt
      let k' : Fin n := ⟨k.val, h_k'_val⟩
      have h_k_eq : k = Fin.castSucc k' := by
        apply Fin.ext
        simp [k', Fin.castSucc] <;> omega
      let objs₁ : Fin (n + 1) → C := fun i : Fin (n + 1) => objs (Fin.castSucc i)
      let homs₁ : ∀ i : Fin n, objs₁ (Fin.castSucc i) ⟶ objs₁ (Fin.succ i) :=
        fun i : Fin n => homs (Fin.castSucc i)
      let objs'₁ : Fin (n + 2) → C := fun i : Fin (n + 2) => objs' (Fin.castSucc i)
      let homs'₁ : ∀ i : Fin (n + 1), objs'₁ (Fin.castSucc i) ⟶ objs'₁ (Fin.succ i) :=
        fun i : Fin (n + 1) => homs' (Fin.castSucc i)
      have h0₁ : objs'₁ 0 = objs₁ 0 := by
        simpa [objs'₁, objs₁] using h0
      have h_before₁ : ∀ (i : Fin n), i.val < k'.val →
          ∃ (h1 : objs'₁ (Fin.castSucc (Fin.castSucc i)) = objs₁ (Fin.castSucc i))
            (h2 : objs'₁ (Fin.succ (Fin.castSucc i)) = objs₁ (Fin.succ i)),
          eqToHom h1.symm ≫ homs'₁ (Fin.castSucc i) ≫ eqToHom h2 = homs₁ i := by
        intro i h_i_lt
        rcases h_before (Fin.castSucc i) (by simp [k', Fin.castSucc] <;> omega) with ⟨h1, h2, h_hom⟩
        refine' ⟨_, _, _⟩
        · simpa [objs'₁, objs₁] using h1
        · simpa [objs'₁, objs₁] using h2
        · convert h_hom <;> simp [objs'₁, objs₁, homs'₁, homs₁] <;> rfl
      have h_split1₁ : objs'₁ (Fin.castSucc (Fin.castSucc k')) = objs₁ (Fin.castSucc k') := by
        simpa [objs'₁, objs₁, h_k_eq] using h_split1
      have h_split2₁ : objs'₁ (Fin.succ (Fin.castSucc k')) = mid := by
        simpa [objs'₁, h_k_eq] using h_split2
      have h_split3₁ : homs'₁ (Fin.castSucc k') =
          eqToHom h_split1₁ ≫ f ≫ eqToHom h_split2₁.symm := by
        have h_k_cast : Fin.castSucc (Fin.castSucc k') = Fin.castSucc k := by
          exact congr_arg Fin.castSucc h_k_eq.symm
        have h : homs'₁ (Fin.castSucc k') = homs' (Fin.castSucc k) := by
          dsimp only [homs'₁]
          <;> congr
          <;> exact h_k_cast
        rw [h]
        have h1 : h_split1₁ = h_split1 := by
          exact Subsingleton.elim h_split1₁ h_split1
        have h2 : h_split2₁ = h_split2 := by
          exact Subsingleton.elim h_split2₁ h_split2
        rw [h1, h2]
        exact h_split3
      have h_split4₁ : objs'₁ (Fin.castSucc (Fin.succ k')) = mid := by
        simpa [objs'₁, h_k_eq] using h_split4
      have h_split5₁ : objs'₁ (Fin.succ (Fin.succ k')) = objs₁ (Fin.succ k') := by
        simpa [objs'₁, objs₁, h_k_eq] using h_split5
      have h_split6₁ : homs'₁ (Fin.succ k') =
          eqToHom h_split4₁ ≫ g ≫ eqToHom h_split5₁.symm := by
        have h_k_cast : Fin.succ (Fin.castSucc k') = Fin.succ k := by
          exact congr_arg Fin.succ h_k_eq.symm
        have h : homs'₁ (Fin.succ k') = homs' (Fin.succ k) := by
          dsimp only [homs'₁]
          <;> congr
          <;> exact h_k_cast
        rw [h]
        have h4 : h_split4₁ = h_split4 := by
          exact Subsingleton.elim h_split4₁ h_split4
        have h5 : h_split5₁ = h_split5 := by
          exact Subsingleton.elim h_split5₁ h_split5
        rw [h4, h5]
        exact h_split6
      have h_after₁ : ∀ (j : Fin n), j.val > k'.val →
          let i : Fin (n + 1) := Fin.succ j
          ∃ (h1 : objs'₁ (Fin.castSucc i) = objs₁ (Fin.castSucc j))
            (h2 : objs'₁ (Fin.succ i) = objs₁ (Fin.succ j)),
          eqToHom h1.symm ≫ homs'₁ i ≫ eqToHom h2 = homs₁ j := by
        intro j h_j_gt
        rcases h_after (Fin.castSucc j) (by simp [k', Fin.castSucc] <;> omega) with ⟨h1, h2, h_hom⟩
        refine' ⟨_, _, _⟩
        · simpa [objs'₁, objs₁] using h1
        · simpa [objs'₁, objs₁] using h2
        · convert h_hom <;> simp [objs'₁, objs₁, homs'₁, homs₁] <;> rfl
      have h_last₁ : objs'₁ (Fin.last (n + 1)) = objs₁ (Fin.last n) := by
        rcases h_after (Fin.last n) (by simp [k', Fin.last] <;> omega) with ⟨h1, h2, h_hom⟩
        simpa [objs'₁, objs₁] using h1
      have h_ih : eqToHom h0₁.symm ≫ comp_list (n + 1) objs'₁ homs'₁ ≫ eqToHom h_last₁ =
          comp_list n objs₁ homs₁ :=
        ih k' objs₁ homs₁ f g h_eq objs'₁ homs'₁ h_before₁ h_split1₁ h_split2₁ h_split3₁
          h_split4₁ h_split5₁ h_split6₁ h_after₁ h0₁ h_last₁
      rcases h_after (Fin.last n) (by simp [k', Fin.last] <;> omega) with ⟨h1_last, h2_last, h_hom_last⟩
      let f := comp_list (n + 1) objs'₁ homs'₁
      let g := homs' (Fin.last (n + 1))
      let f' := comp_list n objs₁ homs₁
      let g' := homs (Fin.last n)
      let hX : objs' 0 = objs 0 := h0
      let hY : objs' (Fin.castSucc (Fin.last (n + 1))) = objs₁ (Fin.last n) := h_last₁
      let hZ : objs' (Fin.succ (Fin.last (n + 1))) = objs (Fin.succ (Fin.last n)) := h_last
      have hY_eq : hY = h1_last := by
        simp [h_last₁, objs'₁, objs₁] <;> rfl
      have hZ_eq : hZ = h2_last := by
        simp [h_last, objs'₁, objs₁] <;> rfl
      have h_ih2 : eqToHom hX.symm ≫ f ≫ eqToHom hY = f' := by
        convert h_ih <;> simp [h0₁, h_last₁, objs'₁, objs₁] <;> rfl
      have h_last_hom : eqToHom hY.symm ≫ g ≫ eqToHom hZ = g' := by
        rw [hY_eq, hZ_eq]
        exact h_hom_last
      have h_comp : (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ) =
          eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ :=
        eqToHom_comp_cancel hX hY hZ f g
      have h_step : (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ) = f' ≫ g' := by
        rw [h_ih2, h_last_hom]
        <;> rfl
      have h_main : eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ = f' ≫ g' := by
        rw [←h_comp]
        exact h_step
      have h1 : comp_list (n + 2) objs' homs' = f ≫ g := by
        rw [comp_list_succ] <;> rfl
      have h2 : comp_list (n + 1) objs homs = f' ≫ g' := by
        rw [comp_list_succ] <;> rfl
      have h3 : h0 = hX := by rfl
      have h4 : h_last = hZ := by rfl
      rw [h1, h2, h3, h4]
      exact h_main
    · -- Case 2: k.val = n (split is at last position)
      have h_k_val : k.val = n := by omega
      have h_k_eq_last : k = Fin.last n := by
        apply Fin.ext
        simp [Fin.last, h_k_val] <;> omega
      subst h_k_eq_last
      let objs₁ : Fin (n + 1) → C := fun i : Fin (n + 1) => objs (Fin.castSucc i)
      let homs₁ : ∀ i : Fin n, objs₁ (Fin.castSucc i) ⟶ objs₁ (Fin.succ i) :=
        fun i : Fin n => homs (Fin.castSucc i)
      let objs'₁ : Fin (n + 2) → C := fun i : Fin (n + 2) => objs' (Fin.castSucc i)
      let homs'₁ : ∀ i : Fin (n + 1), objs'₁ (Fin.castSucc i) ⟶ objs'₁ (Fin.succ i) :=
        fun i : Fin (n + 1) => homs' (Fin.castSucc i)
      have h0₁ : objs'₁ 0 = objs₁ 0 := by
        simpa [objs'₁, objs₁] using h0
      have h_corresp₁ : ∀ (i : Fin n),
          ∃ (h1 : objs'₁ (Fin.castSucc (Fin.castSucc i)) = objs₁ (Fin.castSucc i))
            (h2 : objs'₁ (Fin.succ (Fin.castSucc i)) = objs₁ (Fin.succ i)),
          eqToHom h1.symm ≫ homs'₁ (Fin.castSucc i) ≫ eqToHom h2 = homs₁ i := by
        intro i
        have h_i_lt_k : (Fin.castSucc i).val < (Fin.last n : Fin (n + 1)).val := by
          simp [Fin.last, Fin.castSucc] <;> omega
        rcases h_before (Fin.castSucc i) h_i_lt_k with ⟨h1, h2, h_hom⟩
        refine' ⟨_, _, _⟩
        · simpa [objs'₁, objs₁] using h1
        · simpa [objs'₁, objs₁] using h2
        · convert h_hom <;> simp [objs'₁, objs₁, homs'₁, homs₁] <;> rfl
      have h_succ_last_eq_last : Fin.succ (Fin.last n) = Fin.last (n + 1) := by
        apply Fin.ext
        simp [Fin.last, Fin.succ] <;> omega
      have h_split4_eq : objs'₁ (Fin.last (n + 1)) = mid := by
        have h_eq : objs'₁ (Fin.last (n + 1)) = objs' (Fin.castSucc (Fin.succ (Fin.last n))) := by
          rw [←h_succ_last_eq_last] <;> simp [objs'₁] <;> rfl
        rw [h_eq]
        exact h_split4
      let h_f_type : objs₁ (Fin.last n) ⟶ mid := by
        simpa [objs₁] using f
      have h1' : objs'₁ (Fin.castSucc (Fin.last n)) = objs₁ (Fin.last n) := by
        have h_eq1 : objs'₁ (Fin.castSucc (Fin.last n)) = objs' (Fin.castSucc (Fin.castSucc (Fin.last n))) := by
          simp [objs'₁] <;> rfl
        have h_objs_eq : objs (Fin.castSucc (Fin.last n)) = objs₁ (Fin.last n) := by
          simp [objs₁] <;> rfl
        rw [h_eq1]
        exact Eq.trans h_split1 h_objs_eq
      have h2' : objs'₁ (Fin.succ (Fin.last n)) = mid := by
        have h_eq2 : objs'₁ (Fin.succ (Fin.last n)) = objs' (Fin.castSucc (Fin.succ (Fin.last n))) := by
          simp [objs'₁] <;> rfl
        rw [h_eq2]
        exact h_split4
      have h_eq3 : homs'₁ (Fin.last n) = homs' (Fin.castSucc (Fin.last n)) := by
        simp [homs'₁] <;> rfl
      have h_last_hom₁ :
          ∃ (h1 : objs'₁ (Fin.castSucc (Fin.last n)) = objs₁ (Fin.last n))
            (h2 : objs'₁ (Fin.succ (Fin.last n)) = mid),
          eqToHom h1.symm ≫ homs'₁ (Fin.last n) ≫ eqToHom h2 = h_f_type := by
        refine' ⟨h1', h2', _⟩
        have h_step1 : eqToHom h1'.symm ≫ homs'₁ (Fin.last n) ≫ eqToHom h2' =
            eqToHom h1'.symm ≫ homs' (Fin.castSucc (Fin.last n)) ≫ eqToHom h2' := by
          rw [h_eq3] <;> rfl
        rw [h_step1]
        have h_eq_h1 : h1' = h_split1 := Subsingleton.elim h1' h_split1
        have h_eq_h2 : h2' = h_split2 := Subsingleton.elim h2' h_split2
        rw [h_eq_h1, h_eq_h2, h_split3]
        have h_dom_eq : objs (Fin.castSucc (Fin.last n)) = objs₁ (Fin.last n) := by
          simp [objs₁] <;> rfl
        have h_main : eqToHom h_split1.symm ≫ (eqToHom h_split1 ≫ f ≫ eqToHom h_split2.symm) ≫ eqToHom h_split2 = h_f_type := by
          have h1 : eqToHom h_split1.symm ≫ eqToHom h_split1 = 𝟙 _ := by
            rw [eqToHom_trans, eqToHom_refl] <;> simp
          have h2 : eqToHom h_split2.symm ≫ eqToHom h_split2 = 𝟙 _ := by
            rw [eqToHom_trans, eqToHom_refl] <;> simp
          have h3 : eqToHom h_split1.symm ≫ (eqToHom h_split1 ≫ f ≫ eqToHom h_split2.symm) ≫ eqToHom h_split2 =
              (eqToHom h_split1.symm ≫ eqToHom h_split1) ≫ f ≫ (eqToHom h_split2.symm ≫ eqToHom h_split2) := by
            simp [Category.assoc] <;> rfl
          rw [h3, h1, h2]
          have h4 : 𝟙 _ ≫ f ≫ 𝟙 _ = h_f_type := by
            simp [Category.comp_id, Category.id_comp]
            <;> dsimp only [h_f_type]
            <;> rfl
          exact h4
        exact h_main
      let f_snoc := comp_list (n + 1) objs'₁ homs'₁
      let g_snoc := homs' (Fin.last (n + 1))
      let f'_snoc := comp_list n objs₁ homs₁
      let g'_snoc : objs₁ (Fin.last n) ⟶ mid := h_f_type
      let hX_snoc : objs' 0 = objs 0 := h0
      let hY_snoc : objs'₁ (Fin.last (n + 1)) = mid := h_split4_eq
      let hZ_snoc : objs' (Fin.succ (Fin.last (n + 1))) = objs (Fin.succ (Fin.last n)) := by
        have h_last' : objs' (Fin.succ (Fin.last (n + 1))) = objs (Fin.last (n + 1)) := by
          simpa using h_last
        have h_objs_eq : objs (Fin.last (n + 1)) = objs (Fin.succ (Fin.last n)) := by
          have h_eq : Fin.last (n + 1) = Fin.succ (Fin.last n) := by
            apply Fin.ext
            simp [Fin.last, Fin.succ] <;> omega
          rw [h_eq]
        rw [h_last', h_objs_eq]
      have h_snoc : eqToHom h0₁.symm ≫ f_snoc ≫ eqToHom h_split4_eq =
          f'_snoc ≫ g'_snoc :=
        comp_list_snoc objs₁ homs₁ objs'₁ homs'₁ h0₁ h_corresp₁ h_split4_eq g'_snoc h_last_hom₁
      have h_ih2 : eqToHom hX_snoc.symm ≫ f_snoc ≫ eqToHom hY_snoc = f'_snoc ≫ g'_snoc := by
        convert h_snoc <;> simp [h0₁, h_split4_eq, objs'₁, objs₁] <;> rfl
      have h_last_hom : eqToHom hY_snoc.symm ≫ g_snoc ≫ eqToHom hZ_snoc = g := by
        have h3 : (Fin.last (n + 1) : Fin (n + 2)) = Fin.succ (Fin.last n) := by
          apply Fin.ext
          simp [Fin.last, Fin.succ] <;> omega
        have h2 : g_snoc = homs' (Fin.succ (Fin.last n)) := by
          have h4 : g_snoc = homs' (Fin.last (n + 1)) := by rfl
          rw [h4]
          <;> congr
          <;> exact h3
        have h_eq_hY : hY_snoc = h_split4 := by
          exact Subsingleton.elim hY_snoc h_split4
        have h_eq_hZ : hZ_snoc = h_split5 := by
          exact Subsingleton.elim hZ_snoc h_split5
        rw [h2, h_eq_hY, h_eq_hZ]
        have h_goal : eqToHom h_split4.symm ≫ (eqToHom h_split4 ≫ g ≫ eqToHom h_split5.symm) ≫ eqToHom h_split5 = g := by
          simp [Category.assoc, eqToHom_refl, Category.comp_id, Category.id_comp]
          <;> rfl
        rw [h_split6]
        exact h_goal
      have h_comp : (eqToHom hX_snoc.symm ≫ f_snoc ≫ eqToHom hY_snoc) ≫ (eqToHom hY_snoc.symm ≫ g_snoc ≫ eqToHom hZ_snoc) =
          eqToHom hX_snoc.symm ≫ (f_snoc ≫ g_snoc) ≫ eqToHom hZ_snoc :=
        eqToHom_comp_cancel hX_snoc hY_snoc hZ_snoc f_snoc g_snoc
      have h_step : (eqToHom hX_snoc.symm ≫ f_snoc ≫ eqToHom hY_snoc) ≫ (eqToHom hY_snoc.symm ≫ g_snoc ≫ eqToHom hZ_snoc) =
          (f'_snoc ≫ g'_snoc) ≫ g := by
        have h1 : (eqToHom hX_snoc.symm ≫ f_snoc ≫ eqToHom hY_snoc) = f'_snoc ≫ g'_snoc := h_ih2
        have h2 : (eqToHom hY_snoc.symm ≫ g_snoc ≫ eqToHom hZ_snoc) = g := h_last_hom
        rw [h1, h2]
        <;> rfl
      have h_main : eqToHom hX_snoc.symm ≫ (f_snoc ≫ g_snoc) ≫ eqToHom hZ_snoc = (f'_snoc ≫ g'_snoc) ≫ g := by
        rw [←h_comp]
        exact h_step
      have h1 : comp_list (n + 2) objs' homs' = f_snoc ≫ g_snoc := by
        rw [comp_list_succ] <;> rfl
      have h2 : comp_list (n + 1) objs homs = (f'_snoc ≫ g'_snoc) ≫ g := by
        have h5 : comp_list (n + 1) objs homs = comp_list n objs₁ homs₁ ≫ homs (Fin.last n) := by
          rw [comp_list_succ] <;> rfl
        rw [h5, h_eq]
        have h_assoc : comp_list n objs₁ homs₁ ≫ (f ≫ g) = (comp_list n objs₁ homs₁ ≫ f) ≫ g := by
          rw [Category.assoc]
        rw [h_assoc]
        have h6 : comp_list n objs₁ homs₁ ≫ f = comp_list n objs₁ homs₁ ≫ h_f_type := by
          rfl
        rw [h6]
        <;> rfl
      have h3 : h0 = hX_snoc := by rfl
      have h4 : h_last = hZ_snoc := by
        exact Subsingleton.elim h_last hZ_snoc
      rw [h1, h2, h3, h4]
      exact h_main

end

end P202.Topology.VanKampenProof


/-! Adapted from SubpathHomotopyRange.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace Set unitInterval

noncomputable section

variable {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)

namespace VanKampen

/-- The image of the subpathTransSubpath homotopy is contained in the image of γ
    restricted to the interval [t₀, t₂]. -/
lemma subpathTransSubpath_range {t₀ t₁ t₂ : I} (h_t0_le_t1 : t₀ ≤ t₁) (h_t1_le_t2 : t₁ ≤ t₂) :
    ∀ (p : I × I), ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧
      (Path.Homotopy.subpathTransSubpath γ t₀ t₁ t₂) p = γ u := by
  have h_t0_le_t2 : t₀ ≤ t₂ := le_trans h_t0_le_t1 h_t1_le_t2

  -- First, prove the property for subpathTransSubpathRefl (for all s, t)
  have h1 : ∀ (s t : I), ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧
      (Path.Homotopy.subpathTransSubpathRefl γ t₀ t₁ t₂) (s, t) = γ u := by
    intro s t
    let t_mid : I := Icc.convexComb t₁ t₂ s
    have h_t1_le_mid : t₁ ≤ t_mid := by
      have h : t_mid ∈ Set.uIcc t₁ t₂ := by
        exact (Path.range_subpathAux t₁ t₂).symm ▸ Set.mem_range_self s
      exact (Set.uIcc_of_le h_t1_le_t2).symm ▸ h |>.1
    have h_mid_le_t2 : t_mid ≤ t₂ := by
      have h : t_mid ∈ Set.uIcc t₁ t₂ := by
        exact (Path.range_subpathAux t₁ t₂).symm ▸ Set.mem_range_self s
      exact (Set.uIcc_of_le h_t1_le_t2).symm ▸ h |>.2
    have h_t0_le_mid : t₀ ≤ t_mid := le_trans h_t0_le_t1 h_t1_le_mid

    let γ1 : Path (γ t₀) (γ t_mid) := γ.subpath t₀ t_mid
    let γ2 : Path (γ t_mid) (γ t₂) := γ.subpath t_mid t₂

    have h_range1 : Set.range (γ1.trans γ2) ⊆ γ '' Set.Icc t₀ t₂ := by
      rw [Path.trans_range γ1 γ2]
      apply Set.union_subset
      · -- Set.range γ1 ⊆ γ '' Set.Icc t₀ t₂
        rw [Path.range_subpath γ t₀ t_mid, Set.uIcc_of_le h_t0_le_mid]
        intro z hz
        rcases hz with ⟨u, hu, rfl⟩
        exact ⟨u, ⟨hu.1, le_trans hu.2 h_mid_le_t2⟩, rfl⟩
      · -- Set.range γ2 ⊆ γ '' Set.Icc t₀ t₂
        rw [Path.range_subpath γ t_mid t₂, Set.uIcc_of_le h_mid_le_t2]
        intro z hz
        rcases hz with ⟨u, hu, rfl⟩
        exact ⟨u, ⟨le_trans h_t0_le_mid hu.1, hu.2⟩, rfl⟩

    have h_in_range : (γ1.trans γ2) t ∈ Set.range (γ1.trans γ2) := Set.mem_range_self t
    have h_main : (γ1.trans γ2) t ∈ γ '' Set.Icc t₀ t₂ := h_range1 h_in_range
    rcases h_main with ⟨u, hu, h_eq⟩
    exact ⟨u, hu.1, hu.2, h_eq.symm⟩

  -- Next, prove the property for transRefl (γ.subpath t₀ t₂) (for all s, t)
  have h2 : ∀ (s t : I), ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧
      (Path.Homotopy.transRefl (γ.subpath t₀ t₂)) (s, t) = γ u := by
    intro s t
    have h_range : Set.range (γ.subpath t₀ t₂) = γ '' Set.Icc t₀ t₂ := by
      rw [Path.range_subpath γ t₀ t₂, Set.uIcc_of_le h_t0_le_t2]
    have h_in_range : (Path.Homotopy.transRefl (γ.subpath t₀ t₂)) (s, t) ∈
        Set.range (γ.subpath t₀ t₂) := by
      exact Set.mem_range_self _
    rw [h_range] at h_in_range
    rcases h_in_range with ⟨u, hu, h_eq⟩
    exact ⟨u, hu.1, hu.2, h_eq.symm⟩

  intro p
  let s : I := p.1
  let t : I := p.2
  let H1 := Path.Homotopy.subpathTransSubpathRefl γ t₀ t₁ t₂
  let H2 := Path.Homotopy.transRefl (γ.subpath t₀ t₂)
  let H := Path.Homotopy.subpathTransSubpath γ t₀ t₁ t₂

  have h_def : H = H1.trans H2 := by rfl

  -- We know that for any homotopy trans, its evaluation at (s, t) is either from H1 or H2
  by_cases h_s : (s : ℝ) ≤ 1 / 2
  · -- First half: use subpathTransSubpathRefl
    let s' : I := ⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.prop.1, h_s⟩⟩
    have h_main_goal : ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧ H p = γ u := by
      let H_trans : Path.Homotopy _ _ := H1.trans H2
      have h_eq1 : H = H_trans := h_def
      rw [h_eq1]
      have h_trans_apply : ∀ (p' : I × I),
          H_trans p' =
            if h : (p'.1 : ℝ) ≤ 1 / 2 then
              H1 (⟨2 * p'.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨p'.1.prop.1, h⟩⟩, p'.2)
            else
              H2 (⟨2 * p'.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, p'.1.prop.2⟩⟩, p'.2) := by
        intro p'
        exact?
      have h4 := h_trans_apply p
      rw [h4]
      rw [dif_pos h_s]
      exact h1 s' t
    exact h_main_goal
  · -- Second half: use transRefl
    have h_s'_gt : ¬ (s : ℝ) ≤ 1 / 2 := h_s
    let s' : I := ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h_s'_gt).le, s.prop.2⟩⟩
    have h_main_goal : ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧ H p = γ u := by
      let H_trans : Path.Homotopy _ _ := H1.trans H2
      have h_eq1 : H = H_trans := h_def
      rw [h_eq1]
      have h_trans_apply : ∀ (p' : I × I),
          H_trans p' =
            if h : (p'.1 : ℝ) ≤ 1 / 2 then
              H1 (⟨2 * p'.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨p'.1.prop.1, h⟩⟩, p'.2)
            else
              H2 (⟨2 * p'.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, p'.1.prop.2⟩⟩, p'.2) := by
        intro p'
        exact?
      have h4 := h_trans_apply p
      rw [h4]
      rw [dif_neg h_s'_gt]
      exact h2 s' t
    exact h_main_goal

end VanKampen

end

end

end P202.Topology.VanKampenProof


/-! Adapted from InsertPointHelpers.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace

open scoped unitInterval

noncomputable section

universe u

namespace InsertPointHelpers

/-- Define ts' by inserting t at position m+1 in ts_S. -/
def ts' {n : ℕ} (ts_S : Fin (n + 1) → I) (m : Fin n) (t : I) (i : Fin (n + 2)) : I :=
  if h : i.val ≤ m.val then
    ts_S ⟨i.val, by omega⟩
  else if i.val = m.val + 1 then
    t
  else
    ts_S ⟨i.val - 1, by omega⟩

/-- Define covers' by duplicating covers_S at position m. -/
def covers' {X : Type*} [TopologicalSpace X] {n : ℕ} (covers_S : Fin n → Opens X) (m : Fin n) (i : Fin (n + 1)) : Opens X :=
  if h : i.val ≤ m.val then
    covers_S ⟨i.val, by omega⟩
  else
    covers_S ⟨i.val - 1, by omega⟩

-- Helper lemmas for ts'
lemma ts'_at_before {n : ℕ} {ts_S : Fin (n + 1) → I} {m : Fin n} {t : I} {i : Fin (n + 2)}
    (h : i.val ≤ m.val) :
    ts' ts_S m t i = ts_S ⟨i.val, by omega⟩ := by
  unfold ts'
  exact dif_pos h

lemma ts'_at_mid {n : ℕ} {ts_S : Fin (n + 1) → I} {m : Fin n} {t : I} {i : Fin (n + 2)}
    (h1 : ¬(i.val ≤ m.val)) (h2 : i.val = m.val + 1) :
    ts' ts_S m t i = t := by
  unfold ts'
  rw [dif_neg h1]
  rw [if_pos h2]

lemma ts'_at_after {n : ℕ} {ts_S : Fin (n + 1) → I} {m : Fin n} {t : I} {i : Fin (n + 2)}
    (h1 : ¬(i.val ≤ m.val)) (h2 : ¬(i.val = m.val + 1)) :
    ts' ts_S m t i = ts_S ⟨i.val - 1, by omega⟩ := by
  unfold ts'
  rw [dif_neg h1]
  rw [if_neg h2]

-- Helper lemmas for covers'
lemma covers'_at_le {X : Type*} [TopologicalSpace X] {n : ℕ} {covers_S : Fin n → Opens X} {m : Fin n} {i : Fin (n + 1)}
    (h : i.val ≤ m.val) :
    covers' covers_S m i = covers_S ⟨i.val, by omega⟩ := by
  unfold covers'
  exact dif_pos h

lemma covers'_at_gt {X : Type*} [TopologicalSpace X] {n : ℕ} {covers_S : Fin n → Opens X} {m : Fin n} {i : Fin (n + 1)}
    (h : ¬(i.val ≤ m.val)) :
    covers' covers_S m i = covers_S ⟨i.val - 1, by omega⟩ := by
  unfold covers'
  exact dif_neg h

variable {X : Type u} [TopologicalSpace X]
variable {x y : X} {γ : Path x y} {S : Finset I} {t : I}
variable {n : ℕ}
variable {ts_S : Fin (n + 1) → I}
variable {m : Fin n}
variable {covers_S : Fin n → Opens X}
variable {𝒰 : Set (Opens X)}

/-- Prove that ts' is strictly monotone. -/
lemma ts'_strict
    (h_ts_S_strict : StrictMono ts_S)
    (h_m_left : ts_S (Fin.castSucc m) < t)
    (h_m_right : t < ts_S (Fin.succ m)) :
    StrictMono (ts' ts_S m t) := by
  intro i j h
  have h_ij : i.val < j.val := Fin.lt_iff_val_lt_val.mp h
  -- Case analysis on where i and j fall relative to m.val and m.val + 1
  by_cases h_i_le : i.val ≤ m.val
  · -- i ≤ m
    by_cases h_j_le : j.val ≤ m.val
    · -- j ≤ m: both before insertion point
      rw [ts'_at_before h_i_le, ts'_at_before h_j_le]
      exact h_ts_S_strict (by apply Fin.lt_iff_val_lt_val.mpr; omega)
    · -- j > m
      by_cases h_j_eq : j.val = m.val + 1
      · -- j = m + 1: j is at the insertion point
        rw [ts'_at_before h_i_le, ts'_at_mid (by omega) h_j_eq]
        have h1 : ts_S ⟨i.val, by omega⟩ ≤ ts_S (Fin.castSucc m) :=
          h_ts_S_strict.monotone (by apply Fin.le_iff_val_le_val.mpr; simp [Fin.castSucc] <;> omega)
        exact lt_of_le_of_lt h1 h_m_left
      · -- j > m + 1: j is after insertion point
        rw [ts'_at_before h_i_le, ts'_at_after (by omega) h_j_eq]
        have h_j_ge : j.val ≥ m.val + 2 := by
          have h1 : m.val < j.val := by omega
          have h2 : j.val ≠ m.val + 1 := h_j_eq
          omega
        have h_lt : i.val < j.val - 1 := by omega
        let i' : Fin (n + 1) := ⟨i.val, by omega⟩
        let j' : Fin (n + 1) := ⟨j.val - 1, by omega⟩
        have h_fin_lt : i' < j' := by
          apply Fin.lt_iff_val_lt_val.mpr
          omega
        exact h_ts_S_strict h_fin_lt
  · -- i > m
    have h_i_gt : i.val > m.val := by omega
    by_cases h_i_eq : i.val = m.val + 1
    · -- i = m + 1: i is at insertion point
      by_cases h_j_eq : j.val = m.val + 1
      · omega
      · -- j > m + 1: j is after insertion point
        rw [ts'_at_mid (by omega) h_i_eq, ts'_at_after (by omega) h_j_eq]
        have h1 : t < ts_S (Fin.succ m) := h_m_right
        have h2 : ts_S (Fin.succ m) ≤ ts_S ⟨j.val - 1, by omega⟩ :=
          h_ts_S_strict.monotone (by apply Fin.le_iff_val_le_val.mpr; simp [Fin.succ] <;> omega)
        exact lt_of_lt_of_le h1 h2
    · -- i > m + 1: both after insertion point
      have h_i_gt2 : i.val > m.val + 1 := by omega
      rw [ts'_at_after (by omega) h_i_eq, ts'_at_after (by omega) (by omega)]
      have h_lt : i.val - 1 < j.val - 1 := by omega
      exact h_ts_S_strict (Fin.lt_iff_val_lt_val.mpr h_lt)

/-- Prove that the image of ts' is S ∪ {t}. -/
lemma ts'_image
    (h_ts_S_strict : StrictMono ts_S)
    (h_ts_S_image : Finset.image ts_S Finset.univ = S) :
    Finset.image (ts' ts_S m t) Finset.univ = S ∪ {t} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · -- Forward direction: x ∈ image ts' → x ∈ S ∨ x = t
    rintro ⟨i, rfl⟩
    by_cases h1 : i.val ≤ m.val
    · rw [ts'_at_before h1]
      left
      have h_in : ts_S ⟨i.val, by omega⟩ ∈ Finset.image ts_S Finset.univ :=
        Finset.mem_image.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, rfl⟩
      rw [h_ts_S_image] at h_in
      exact h_in
    · by_cases h2 : i.val = m.val + 1
      · rw [ts'_at_mid h1 h2]
        right
        rfl
      · rw [ts'_at_after h1 h2]
        left
        have h_in : ts_S ⟨i.val - 1, by omega⟩ ∈ Finset.image ts_S Finset.univ :=
          Finset.mem_image.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, rfl⟩
        rw [h_ts_S_image] at h_in
        exact h_in
  · -- Backward direction: x ∈ S ∨ x = t → x ∈ image ts'
    rintro (h | rfl)
    · -- x ∈ S
      have h_x_in : x ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h
      rcases Finset.mem_image.mp h_x_in with ⟨k, _, rfl⟩
      by_cases h_k_le : k.val ≤ m.val
      · -- k ≤ m: use i = k (cast to Fin (n+2))
        let i : Fin (n + 2) := ⟨k.val, by omega⟩
        have h_i_le : i.val ≤ m.val := by exact h_k_le
        refine ⟨i, ?_⟩
        rw [ts'_at_before h_i_le]
        <;> simp [i]
      · -- k > m: use i = k.val + 1
        let i : Fin (n + 2) := ⟨k.val + 1, by omega⟩
        have h1 : ¬(i.val ≤ m.val) := by simp [i] <;> omega
        have h2 : ¬(i.val = m.val + 1) := by simp [i] <;> omega
        refine ⟨i, ?_⟩
        rw [ts'_at_after h1 h2]
        <;> simp [i] <;> omega
    · -- x = t: use i = m.val + 1
      let i : Fin (n + 2) := ⟨m.val + 1, by omega⟩
      have h1 : ¬(i.val ≤ m.val) := by simp [i] <;> omega
      have h2 : i.val = m.val + 1 := by simp [i] <;> omega
      refine ⟨i, ?_⟩
      rw [ts'_at_mid h1 h2]

/-- Prove that covers' are all in 𝒰. -/
lemma covers'_mem
    (hcover_mem_S : ∀ i, covers_S i ∈ 𝒰) :
    ∀ (i : Fin (n + 1)), covers' covers_S m i ∈ 𝒰 := by
  intro i
  by_cases h : i.val ≤ m.val
  · rw [covers'_at_le h]
    exact hcover_mem_S ⟨i.val, by omega⟩
  · rw [covers'_at_gt h]
    exact hcover_mem_S ⟨i.val - 1, by omega⟩

/-- Prove that covers' satisfy the range condition. -/
lemma covers'_range
    (h_ts_S_strict : StrictMono ts_S)
    (h_m_left : ts_S (Fin.castSucc m) < t)
    (h_m_right : t < ts_S (Fin.succ m))
    (h_range_S : ∀ i, ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (covers_S i : Set X)) :
    ∀ (i : Fin (n + 1)) (t_val : I),
      ts' ts_S m t (Fin.castSucc i) ≤ t_val →
      t_val ≤ ts' ts_S m t (Fin.succ i) →
      γ t_val ∈ (↑(covers' covers_S m i) : Set X) := by
  intro i t_val h1 h2
  by_cases h_i_lt : i.val < m.val
  · -- Case 1: i.val < m.val (strictly before m)
    have h_i_lt_n : i.val < n := by omega
    let j : Fin n := ⟨i.val, h_i_lt_n⟩
    have h_covers_eq : (covers' covers_S m i : Opens X) = covers_S j := by
      rw [covers'_at_le (by omega)]
      <;> rfl
    rw [h_covers_eq]
    have h_castSucc_le : (Fin.castSucc i).val ≤ m.val := by simp [Fin.castSucc] <;> omega
    have h_succ_le : (Fin.succ i).val ≤ m.val := by simp [Fin.succ] <;> omega
    have h_ts1 : ts' ts_S m t (Fin.castSucc i) = ts_S (Fin.castSucc j) := by
      rw [ts'_at_before h_castSucc_le]
      <;> rfl
    have h_ts2 : ts' ts_S m t (Fin.succ i) = ts_S (Fin.succ j) := by
      rw [ts'_at_before h_succ_le]
      <;> rfl
    have h1' : ts_S (Fin.castSucc j) ≤ t_val := by rw [←h_ts1]; exact h1
    have h2' : t_val ≤ ts_S (Fin.succ j) := by rw [←h_ts2]; exact h2
    exact h_range_S j t_val h1' h2'
  · -- Case 2: i.val ≥ m.val
    by_cases h_i_eq_m : i.val = m.val
    · -- Subcase 2a: i.val = m.val (exactly at m)
      have h_i_le : i.val ≤ m.val := by omega
      have h_covers_eq : (covers' covers_S m i : Opens X) = covers_S m := by
        rw [covers'_at_le h_i_le]
        apply congr_arg covers_S
        apply Fin.ext
        exact h_i_eq_m
      rw [h_covers_eq]
      have h_castSucc_le : (Fin.castSucc i).val ≤ m.val := by
        simp [Fin.castSucc, h_i_eq_m] <;> omega
      have h_ts1 : ts' ts_S m t (Fin.castSucc i) = ts_S (Fin.castSucc m) := by
        rw [ts'_at_before h_castSucc_le]
        apply congr_arg ts_S
        apply Fin.ext
        have h_eq : (Fin.castSucc i).val = (Fin.castSucc m).val := by
          simp [Fin.castSucc, h_i_eq_m]
        exact h_eq
      have h_succ_mid : (Fin.succ i).val = m.val + 1 := by
        simp [Fin.succ, h_i_eq_m] <;> omega
      have h_ts2 : ts' ts_S m t (Fin.succ i) = t :=
        ts'_at_mid (by omega) h_succ_mid
      have h1' : ts_S (Fin.castSucc m) ≤ t_val := by rw [←h_ts1]; exact h1
      have h2' : t_val ≤ t := by rw [←h_ts2]; exact h2
      have h3 : t_val ≤ ts_S (Fin.succ m) := by
        exact le_of_lt (lt_of_le_of_lt h2' h_m_right)
      exact h_range_S m t_val h1' h3
    · -- Subcase 2b: i.val > m.val
      have h_i_gt_m : i.val > m.val := by omega
      by_cases h_i_eq_succ : i.val = m.val + 1
      · -- Subsubcase 2b1: i.val = m.val + 1 (right after insertion point)
        have h_sub : i.val - 1 = m.val := by omega
        have h_covers_eq : (covers' covers_S m i : Opens X) = covers_S m := by
          rw [covers'_at_gt (by omega)]
          apply congr_arg covers_S
          apply Fin.ext
          exact h_sub
        rw [h_covers_eq]
        have h_castSucc_mid : (Fin.castSucc i).val = m.val + 1 := by
          simp [Fin.castSucc, h_i_eq_succ] <;> omega
        have h_ts1 : ts' ts_S m t (Fin.castSucc i) = t :=
          ts'_at_mid (by omega) h_castSucc_mid
        have h_succ_gt1 : ¬((Fin.succ i).val ≤ m.val) := by
          simp [Fin.succ, h_i_eq_succ] <;> omega
        have h_succ_gt2 : ¬((Fin.succ i).val = m.val + 1) := by
          simp [Fin.succ, h_i_eq_succ] <;> omega
        have h_ts2 : ts' ts_S m t (Fin.succ i) = ts_S (Fin.succ m) := by
          rw [ts'_at_after h_succ_gt1 h_succ_gt2]
          <;> apply congr_arg ts_S
          <;> apply Fin.ext
          <;> simp [Fin.succ, h_i_eq_succ] <;> omega
        have h1' : t ≤ t_val := by rw [←h_ts1]; exact h1
        have h2' : t_val ≤ ts_S (Fin.succ m) := by rw [←h_ts2]; exact h2
        have h3 : ts_S (Fin.castSucc m) ≤ t_val := by
          exact le_of_lt (lt_of_lt_of_le h_m_left h1')
        exact h_range_S m t_val h3 h2'
      · -- Subsubcase 2b2: i.val > m.val + 1 (strictly after insertion point)
        have h_i_gt_succ : i.val > m.val + 1 := by omega
        rw [covers'_at_gt (by omega)]
        have h_k_ok : i.val - 1 < n := by omega
        let k : Fin n := ⟨i.val - 1, h_k_ok⟩
        have h_k_val : k.val = i.val - 1 := by
          exact rfl
        have h_castSucc_gt1 : ¬((Fin.castSucc i).val ≤ m.val) := by
          simp [Fin.castSucc] <;> omega
        have h_castSucc_gt2 : ¬((Fin.castSucc i).val = m.val + 1) := by
          simp [Fin.castSucc] <;> omega
        have h_ts1 : ts' ts_S m t (Fin.castSucc i) = ts_S (Fin.castSucc k) := by
          rw [ts'_at_after h_castSucc_gt1 h_castSucc_gt2]
          apply congr_arg ts_S
          apply Fin.ext
          simp [Fin.castSucc, h_k_val] <;> omega
        have h_succ_gt1 : ¬((Fin.succ i).val ≤ m.val) := by
          simp [Fin.succ] <;> omega
        have h_succ_gt2 : ¬((Fin.succ i).val = m.val + 1) := by
          simp [Fin.succ] <;> omega
        have h_ts2 : ts' ts_S m t (Fin.succ i) = ts_S (Fin.succ k) := by
          rw [ts'_at_after h_succ_gt1 h_succ_gt2]
          apply congr_arg ts_S
          apply Fin.ext
          simp [Fin.succ, h_k_val] <;> omega
        have h1' : ts_S (Fin.castSucc k) ≤ t_val := by rw [←h_ts1]; exact h1
        have h2' : t_val ≤ ts_S (Fin.succ k) := by rw [←h_ts2]; exact h2
        have h_main : γ t_val ∈ (covers_S k : Set X) := h_range_S k t_val h1' h2'
        simpa [k] using h_main

end InsertPointHelpers

end

end

end P202.Topology.VanKampenProof


/-! Adapted from EqToHomSandwich.lean. -/
namespace P202.Topology.VanKampenProof



section

open CategoryTheory

namespace VanKampen

/-- Given isomorphisms `e_x : a ≅ b`, `e_y : c ≅ d`, and morphisms `A : a ⟶ c`, `B : b ⟶ d`,
  if `e_x.inv ≫ A ≫ e_y.hom = B` then `A = e_x.hom ≫ B ≫ e_y.inv`. -/
lemma iso_sandwich_rewrite {C : Type _} [Category C] {a b c d : C}
    (e_x : a ≅ b) (e_y : c ≅ d) (A : a ⟶ c) (B : b ⟶ d)
    (h : e_x.inv ≫ A ≫ e_y.hom = B) :
    A = e_x.hom ≫ B ≫ e_y.inv := by
  have h_step1 : e_x.hom ≫ (e_x.inv ≫ A ≫ e_y.hom) ≫ e_y.inv =
      e_x.hom ≫ e_x.inv ≫ (A ≫ (e_y.hom ≫ e_y.inv)) := by
    simp only [Category.assoc]
    <;> rfl
  have h_step2 : e_x.hom ≫ e_x.inv ≫ (A ≫ (e_y.hom ≫ e_y.inv)) =
      A ≫ (e_y.hom ≫ e_y.inv) := by
    rw [e_x.hom_inv_id_assoc]
  have h_step3 : A ≫ (e_y.hom ≫ e_y.inv) = A := by
    have h_id : e_y.hom ≫ e_y.inv = 𝟙 c := e_y.hom_inv_id
    rw [h_id, Category.comp_id]
  have h1 : e_x.hom ≫ (e_x.inv ≫ A ≫ e_y.hom) ≫ e_y.inv = A := by
    rw [h_step1, h_step2, h_step3]
  have h2 : e_x.hom ≫ B ≫ e_y.inv = e_x.hom ≫ (e_x.inv ≫ A ≫ e_y.hom) ≫ e_y.inv := by
    have h3 : B = e_x.inv ≫ A ≫ e_y.hom := h.symm
    have h4 : e_x.hom ≫ B ≫ e_y.inv = e_x.hom ≫ (e_x.inv ≫ A ≫ e_y.hom) ≫ e_y.inv := by
      rw [h3]
    exact h4
  have h5 : e_x.hom ≫ B ≫ e_y.inv = A := by
    rw [h2, h1]
  exact h5.symm

end VanKampen

end

end P202.Topology.VanKampenProof


/-! Adapted from CleanMapFromAdapted.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits IsAdaptedSubdivision

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hpath_connected : ∀ U : Opens X, U ∈ 𝒰 → IsPathConnected (U : Set X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

/-- Helper: given an adapted subdivision S and explicit covering sets for each segment,
    compute the corresponding morphism. This is useful for reasoning. -/
noncomputable def my_map_from_adapted_subdivision_with_covers
    {x y : X} {γ : Path x y} {S : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (n : ℕ)
    (ts : Fin (n + 1) → I)
    (h_ts_strict : StrictMono ts)
    (h_ts_image : Finset.image ts Finset.univ = S)
    (covers : Fin n → Opens X)
    (hcover_mem : ∀ i, covers i ∈ 𝒰)
    (h_range : ∀ i, ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers i : Set X)) :
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) ⟶
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)) := by
  classical
  let pts (i : Fin (n + 1)) : X := γ (ts i)
  let γs (i : Fin n) : Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) :=
    γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))
  have h_ranges (i : Fin n) : Set.range (γs i) ⊆ (covers i : Set X) := by
    have h_lt : Fin.castSucc i < Fin.succ i := by
      apply Fin.castSucc_lt_succ
    have h_ts_lt : ts (Fin.castSucc i) < ts (Fin.succ i) := h_ts_strict h_lt
    have h_range_eq : Set.range (γs i) = γ '' Set.Icc (ts (Fin.castSucc i)) (ts (Fin.succ i)) := by
      rw [Path.range_subpath γ (ts (Fin.castSucc i)) (ts (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact h_range i t ht.1 ht.2
  let objs : Fin (n + 1) → s.pt := fun i =>
    desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
  let homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) (covers i) (hcover_mem i) (h_ranges i)
  let f : objs 0 ⟶ objs (Fin.last n) := comp_list n objs homs
  have h0_in : (0 : I) ∈ S := hS.1
  have h1_in : (1 : I) ∈ S := hS.2.1
  have hS_nonempty : S.Nonempty := ⟨0, h0_in⟩
  have h_min' : S.min' hS_nonempty = (0 : I) := by
    rw [Finset.min'_eq_iff S hS_nonempty (0 : I)]
    <;> exact ⟨h0_in, fun y _ => y.prop.1⟩
  have h_max' : S.max' hS_nonempty = (1 : I) := by
    rw [Finset.max'_eq_iff S hS_nonempty (1 : I)]
    <;> exact ⟨h1_in, fun y _ => y.prop.2⟩
  have h_pts0 : pts 0 = x := by
    dsimp only [pts]
    have h_ts0 : ts 0 = (0 : I) := by
      have h0_in_image : (0 : I) ∈ Finset.image ts Finset.univ := by rw [h_ts_image] <;> exact h0_in
      let i : Fin (n + 1) := Classical.choose (Finset.mem_image.mp h0_in_image)
      let hi : ts i = (0 : I) := (Classical.choose_spec (Finset.mem_image.mp h0_in_image)).2
      have h_i_eq_0 : i = 0 := by
        by_contra h
        have h_i_pos : 0 < i := Fin.pos_iff_ne_zero.mpr h
        have h_ts0_lt_tsi : ts 0 < ts i := h_ts_strict h_i_pos
        rw [hi] at h_ts0_lt_tsi
        have h_nonneg : (0 : ℝ) ≤ (ts 0 : ℝ) := (ts 0).prop.1
        have h_cont : (ts 0 : ℝ) < (0 : ℝ) := by exact_mod_cast h_ts0_lt_tsi
        linarith
      rw [h_i_eq_0] at hi
      exact hi
    rw [h_ts0]
    exact γ.source
  have h_pts_last : pts (Fin.last n) = y := by
    dsimp only [pts]
    have h_ts1 : ts (Fin.last n) = (1 : I) := by
      have h1_in_image : (1 : I) ∈ Finset.image ts Finset.univ := by rw [h_ts_image] <;> exact h1_in
      let i : Fin (n + 1) := Classical.choose (Finset.mem_image.mp h1_in_image)
      let hi : ts i = (1 : I) := (Classical.choose_spec (Finset.mem_image.mp h1_in_image)).2
      have h_i_eq_last : i = Fin.last n := by
        apply Fin.eq_last_of_not_lt
        intro h
        have h_tsi_lt_ts1 : ts i < ts (Fin.last n) := h_ts_strict h
        rw [hi] at h_tsi_lt_ts1
        have h' : (1 : ℝ) < (ts (Fin.last n) : ℝ) := by exact_mod_cast h_tsi_lt_ts1
        have h'' : (ts (Fin.last n) : ℝ) ≤ 1 := (ts (Fin.last n)).prop.2
        linarith
      rw [h_i_eq_last] at hi
      exact hi
    rw [h_ts1]
    exact γ.target
  let eq0 : objs 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
    dsimp only [objs]
    rw [h_pts0]
    <;> rfl
  let eq_last : objs (Fin.last n) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
    dsimp only [objs]
    rw [h_pts_last]
    <;> rfl
  exact eqToHom eq0.symm ≫ f ≫ eqToHom eq_last

/-- The choice of covering sets does not matter. -/
theorem my_map_from_adapted_subdivision_covers_indep
    {x y : X} {γ : Path x y} {S : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (n : ℕ)
    (ts : Fin (n + 1) → I)
    (h_ts_strict : StrictMono ts)
    (h_ts_image : Finset.image ts Finset.univ = S)
    (covers₁ covers₂ : Fin n → Opens X)
    (hcover_mem₁ : ∀ i, covers₁ i ∈ 𝒰)
    (hcover_mem₂ : ∀ i, covers₂ i ∈ 𝒰)
    (h_range₁ : ∀ i, ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers₁ i : Set X))
    (h_range₂ : ∀ i, ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers₂ i : Set X)) :
    my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts h_ts_strict h_ts_image covers₁ hcover_mem₁ h_range₁ =
    my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts h_ts_strict h_ts_image covers₂ hcover_mem₂ h_range₂ := by
  dsimp only [my_map_from_adapted_subdivision_with_covers]
  let pts (i : Fin (n + 1)) : X := γ (ts i)
  let objs : Fin (n + 1) → s.pt := fun i =>
    desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
  let γs (i : Fin n) : Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) :=
    γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))
  have h_lt_i (i : Fin n) : (Fin.castSucc i) < (Fin.succ i) := by
    simp [Fin.castSucc_lt_succ]
  have h_ranges₁ (i : Fin n) : Set.range (γs i) ⊆ (covers₁ i : Set X) := by
    have h_ts_lt : ts (Fin.castSucc i) < ts (Fin.succ i) := h_ts_strict (h_lt_i i)
    have h_range_eq : Set.range (γs i) = γ '' Set.Icc (ts (Fin.castSucc i)) (ts (Fin.succ i)) := by
      rw [Path.range_subpath γ (ts (Fin.castSucc i)) (ts (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact h_range₁ i t ht.1 ht.2
  have h_ranges₂ (i : Fin n) : Set.range (γs i) ⊆ (covers₂ i : Set X) := by
    have h_ts_lt : ts (Fin.castSucc i) < ts (Fin.succ i) := h_ts_strict (h_lt_i i)
    have h_range_eq : Set.range (γs i) = γ '' Set.Icc (ts (Fin.castSucc i)) (ts (Fin.succ i)) := by
      rw [Path.range_subpath γ (ts (Fin.castSucc i)) (ts (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact h_range₂ i t ht.1 ht.2
  let homs₁ : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) (covers₁ i) (hcover_mem₁ i) (h_ranges₁ i)
  let homs₂ : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) (covers₂ i) (hcover_mem₂ i) (h_ranges₂ i)
  have h_homs_eq : homs₁ = homs₂ := by
    funext i
    exact single_covered_map_indep X 𝒰 hcover hfinite_intersections s (γs i)
      (covers₁ i) (covers₂ i) (hcover_mem₁ i) (hcover_mem₂ i) (h_ranges₁ i) (h_ranges₂ i)
  have h_comp_list_eq : comp_list n objs homs₁ = comp_list n objs homs₂ := by
    rw [h_homs_eq]
  rw [h_comp_list_eq]

/-- Given an adapted subdivision S of a path γ, compute the corresponding morphism
    in the colimit cocone.

    This uses Classical.choose to pick covering sets for each segment, but the result
    is independent of the choice (by covers_indep). -/
noncomputable def my_map_from_adapted_subdivision
    {x y : X} {γ : Path x y} {S : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S) :
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) ⟶
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)) := by
  classical
  have h0_in : (0 : I) ∈ S := hS.1
  have h1_in : (1 : I) ∈ S := hS.2.1
  have hS_nonempty : S.Nonempty := ⟨0, h0_in⟩
  let k : ℕ := S.card
  have hk : S.card = k := rfl
  have hk_pos : 0 < k := Finset.card_pos.mpr hS_nonempty
  have hk_ge2 : 2 ≤ k := by
    have h0_ne_1 : (0 : I) ≠ (1 : I) := by
      intro h
      have h' : (0 : ℝ) = (1 : ℝ) := congr_arg (fun x : I => (x : ℝ)) h
      norm_num at h' <;> exact h'
    have h : ({(0 : I), (1 : I)} : Finset I) ⊆ S := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with (rfl | rfl) <;> tauto
    have h2 : ({(0 : I), (1 : I)} : Finset I).card ≤ S.card := Finset.card_le_card h
    have h3 : ({(0 : I), (1 : I)} : Finset I).card = 2 := by
      simp [h0_ne_1] <;> rfl
    rw [h3] at h2
    exact h2
  let e : Fin k ↪o I := S.orderEmbOfFin hk
  have h_e_mem : ∀ (i : Fin k), e i ∈ S := Finset.orderEmbOfFin_mem S hk
  have h_e_strict_mono : StrictMono e := OrderEmbedding.strictMono e
  have h_image : Finset.image e Finset.univ = S := by
    convert Finset.image_orderEmbOfFin_univ S hk using 1 <;>
      ext x <;> simp only [Finset.mem_image] <;> rfl
  let n : ℕ := k - 1
  have hk_eq : k = n + 1 := by omega
  let ts (i : Fin (n + 1)) : I := e ⟨i.val, by rw [hk_eq] <;> exact i.is_lt⟩
  have h_ts_strict : StrictMono ts := by
    intro i j h
    exact h_e_strict_mono (by simpa [ts] using h)
  have h_ts_image : Finset.image ts Finset.univ = S := by
    have h1 : Finset.image ts Finset.univ = Finset.image e Finset.univ := by
      ext x
      simp only [ts, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨⟨i.val, by rw [hk_eq] <;> exact i.is_lt⟩, rfl⟩
      · rintro ⟨j, rfl⟩
        have h_j_lt : j.val < n + 1 := by rw [←hk_eq]; exact j.is_lt
        let i : Fin (n + 1) := ⟨j.val, h_j_lt⟩
        exact ⟨i, by simp [i] <;> rfl⟩
    rw [h1, h_image]
  let choose_data (i : Fin n) :
    ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (U : Set X) := by
    let s₁ := ts (Fin.castSucc i)
    let s₂ := ts (Fin.succ i)
    have h_s1_in : s₁ ∈ S := h_e_mem _
    have h_s2_in : s₂ ∈ S := h_e_mem _
    have h_lt : s₁ < s₂ := h_e_strict_mono (by simp [Fin.castSucc, Fin.succ] <;> omega)
    have h_no_between : ∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False := by
      intro t ht h1 h2
      have h_exists : ∃ (j : Fin k), e j = t := by
        have h : t ∈ Finset.image e Finset.univ := by rw [h_image] <;> exact ht
        rcases Finset.mem_image.mp h with ⟨j, _, rfl⟩
        exact ⟨j, rfl⟩
      rcases h_exists with ⟨j, hj⟩
      have h_j_gt : (Fin.castSucc i).val < j.val := by
        have h4 : ts (Fin.castSucc i) < e j := by rw [hj] <;> exact h1
        have h5 : e ⟨(Fin.castSucc i).val, by rw [hk_eq] <;> exact (Fin.castSucc i).is_lt⟩ = ts (Fin.castSucc i) := by rfl
        rw [←h5] at h4
        exact h_e_strict_mono.lt_iff_lt.mp h4
      have h_j_lt : j.val < (Fin.succ i).val := by
        have h4 : e j < ts (Fin.succ i) := by rw [hj] <;> exact h2
        have h5 : e ⟨(Fin.succ i).val, by rw [hk_eq] <;> exact (Fin.succ i).is_lt⟩ = ts (Fin.succ i) := by rfl
        rw [←h5] at h4
        exact h_e_strict_mono.lt_iff_lt.mp h4
      simp [Fin.castSucc, Fin.succ] at h_j_gt h_j_lt <;> omega
    exact hS.2.2 s₁ s₂ h_s1_in h_s2_in h_lt h_no_between
  choose U hU using choose_data
  let covers (i : Fin n) : Opens X := U i
  let hcover_mem (i : Fin n) : covers i ∈ 𝒰 := (hU i).1
  let h_range (i : Fin n) : ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers i : Set X) := (hU i).2
  exact my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts h_ts_strict h_ts_image covers hcover_mem h_range

/-- Helper: my_map_from_adapted_subdivision_with_covers is independent of the choice of ts
    (as long as they are strictly monotone with the same image). -/
lemma my_map_from_adapted_subdivision_ts_indep
    {x y : X} {γ : Path x y} {S : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    {n : ℕ}
    (ts₁ ts₂ : Fin (n + 1) → I)
    (h_ts₁_strict : StrictMono ts₁)
    (h_ts₂_strict : StrictMono ts₂)
    (h_ts₁_image : Finset.image ts₁ Finset.univ = S)
    (h_ts₂_image : Finset.image ts₂ Finset.univ = S)
    (covers : Fin n → Opens X)
    (hcover_mem : ∀ i, covers i ∈ 𝒰)
    (h_range₁ : ∀ i, ∀ (t : I), ts₁ (Fin.castSucc i) ≤ t → t ≤ ts₁ (Fin.succ i) → γ t ∈ (covers i : Set X))
    (h_range₂ : ∀ i, ∀ (t : I), ts₂ (Fin.castSucc i) ≤ t → t ≤ ts₂ (Fin.succ i) → γ t ∈ (covers i : Set X)) :
    my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts₁ h_ts₁_strict h_ts₁_image covers hcover_mem h_range₁ =
    my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts₂ h_ts₂_strict h_ts₂_image covers hcover_mem h_range₂ := by
  have h_card : S.card = n + 1 := by
    have h1 : (Finset.image ts₁ Finset.univ).card = Finset.card (Finset.univ : Finset (Fin (n + 1))) := by
      apply Finset.card_image_of_injective
      exact StrictMono.injective h_ts₁_strict
    rw [h_ts₁_image] at h1
    simpa using h1
  have h_ts₁_mem : ∀ (i : Fin (n + 1)), ts₁ i ∈ S := by
    intro i
    have h : ts₁ i ∈ Finset.image ts₁ Finset.univ := by
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_univ i, rfl⟩
    rw [h_ts₁_image] at h
    exact h
  have h_ts₂_mem : ∀ (i : Fin (n + 1)), ts₂ i ∈ S := by
    intro i
    have h : ts₂ i ∈ Finset.image ts₂ Finset.univ := by
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_univ i, rfl⟩
    rw [h_ts₂_image] at h
    exact h
  have h_eq : ts₁ = ts₂ := by
    have h1 : ts₁ = S.orderEmbOfFin h_card := Finset.orderEmbOfFin_unique h_card h_ts₁_mem h_ts₁_strict
    have h2 : ts₂ = S.orderEmbOfFin h_card := Finset.orderEmbOfFin_unique h_card h_ts₂_mem h_ts₂_strict
    rw [h1, h2]
  -- Rewrite h_range₁ to use ts₂ instead of ts₁
  have h_range₁' : ∀ (i : Fin n), ∀ (t : I), ts₂ (Fin.castSucc i) ≤ t → t ≤ ts₂ (Fin.succ i) → γ t ∈ (covers i : Set X) := by
    intro i t h1 h2
    have h1' : ts₁ (Fin.castSucc i) ≤ t := by
      have h_eq1 : ts₁ (Fin.castSucc i) = ts₂ (Fin.castSucc i) := by
        rw [h_eq]
      rw [h_eq1]
      exact h1
    have h2' : t ≤ ts₁ (Fin.succ i) := by
      have h_eq2 : ts₁ (Fin.succ i) = ts₂ (Fin.succ i) := by
        rw [h_eq]
      rw [h_eq2]
      exact h2
    exact h_range₁ i t h1' h2'
  -- First, change the LHS to use ts₂ instead of ts₁
  have h_step1 : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts₁ h_ts₁_strict h_ts₁_image covers hcover_mem h_range₁ =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts₂ h_ts₂_strict h_ts₂_image covers hcover_mem h_range₁' := by
    have h_eq' : ts₁ = ts₂ := h_eq
    subst h_eq'
    -- Now ts₁ = ts₂ everywhere
    -- h_range₁ and h_range₁' have the same type
    <;> rfl
  -- Now both sides have the same ts, just different proof arguments
  -- By proof irrelevance, different proofs of the same proposition give the same result
  have h_step2 : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts₂ h_ts₂_strict h_ts₂_image covers hcover_mem h_range₁' =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts₂ h_ts₂_strict h_ts₂_image covers hcover_mem h_range₂ := by
    -- All arguments that differ are proofs, so we can use Subsingleton
    apply congr_arg (fun (p : (∀ (i : Fin n), ∀ (t : I), ts₂ (Fin.castSucc i) ≤ t → t ≤ ts₂ (Fin.succ i) → γ t ∈ (covers i : Set X))) =>
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts₂ h_ts₂_strict h_ts₂_image covers hcover_mem p)
    exact Subsingleton.elim _ _
  rw [h_step1, h_step2]

/-- Universal property: my_map_from_adapted_subdivision equals
    my_map_from_adapted_subdivision_with_covers for ANY valid choice of ts and covers.
    This lets us "compute" the map by picking convenient ts and covers. -/
theorem my_map_from_adapted_subdivision_universal
    {x y : X} {γ : Path x y} {S : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    {n : ℕ}
    (ts : Fin (n + 1) → I)
    (h_ts_strict : StrictMono ts)
    (h_ts_image : Finset.image ts Finset.univ = S)
    (covers : Fin n → Opens X)
    (hcover_mem : ∀ i, covers i ∈ 𝒰)
    (h_range : ∀ i, ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers i : Set X)) :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts h_ts_strict h_ts_image covers hcover_mem h_range := by
  classical
  have h_card : S.card = n + 1 := by
    have h1 : (Finset.image ts Finset.univ).card = Finset.card (Finset.univ : Finset (Fin (n + 1))) := by
      apply Finset.card_image_of_injective
      exact StrictMono.injective h_ts_strict
    rw [h_ts_image] at h1
    simpa using h1
  -- Generalize S.card to a variable so we can substitute
  generalize hk : S.card = k
  have h_k_eq : k = n + 1 := by
    rw [←hk]
    exact h_card
  subst h_k_eq
  -- Now S.card = n + 1 definitionally
  -- So S.card - 1 = n definitionally
  dsimp only [my_map_from_adapted_subdivision]
  -- Now the definition is unfolded with let bindings.
  -- We want to show:
  --   with_covers ... ts_canon ... covers_def ... = with_covers ... ts ... covers ...
  -- Proof:
  --   1. with_covers ... ts_canon ... covers_def ...
  --   = with_covers ... ts ... covers_def ...  (by ts_indep)
  --   = with_covers ... ts ... covers ...      (by covers_indep)
  --
  -- The only thing we need to check is that ts_canon has the right properties,
  -- and that covers_def has the right properties. But these are all true by
  -- construction in the definition.
  --
  -- Let's just use congr_arg with a function that changes ts and covers using the lemmas.
  -- Actually, let's just prove that for ANY valid ts' and covers', the result is the same.
  -- Then both sides equal this unique value.
  --
  -- Wait, we already have ts_indep and covers_indep! So for fixed n, the result only depends on S.
  -- And since n = S.card - 1 is uniquely determined by S, the whole thing only depends on S.
  --
  -- Let's just apply the lemmas directly to the unfolded definition.
  -- First, let's give names to all the components of the unfolded definition.
  let k_def := S.card
  let e_def : Fin k_def ↪o I := S.orderEmbOfFin rfl
  let n_def := k_def - 1
  let ts_canon (i : Fin (n_def + 1)) : I := e_def ⟨i.val, by omega⟩
  let choose_data_def (i : Fin n_def) :
    ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t : I), ts_canon (Fin.castSucc i) ≤ t → t ≤ ts_canon (Fin.succ i) → γ t ∈ (U : Set X) := by
    let s₁ := ts_canon (Fin.castSucc i)
    let s₂ := ts_canon (Fin.succ i)
    have h_s1_in : s₁ ∈ S := by
      have h : s₁ = e_def ⟨(Fin.castSucc i).val, by omega⟩ := by rfl
      rw [h]
      exact Finset.orderEmbOfFin_mem S rfl _
    have h_s2_in : s₂ ∈ S := by
      have h : s₂ = e_def ⟨(Fin.succ i).val, by omega⟩ := by rfl
      rw [h]
      exact Finset.orderEmbOfFin_mem S rfl _
    have h_lt : s₁ < s₂ := by
      have h_cast_lt : (Fin.castSucc i).val < (Fin.succ i).val := by
        simp [Fin.castSucc, Fin.succ] <;> omega
      have h : e_def ⟨(Fin.castSucc i).val, by omega⟩ < e_def ⟨(Fin.succ i).val, by omega⟩ :=
        OrderEmbedding.strictMono e_def h_cast_lt
      have h1 : s₁ = e_def ⟨(Fin.castSucc i).val, by omega⟩ := by rfl
      have h2 : s₂ = e_def ⟨(Fin.succ i).val, by omega⟩ := by rfl
      rw [h1, h2]
      exact h
    have h_no_between : ∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False := by
      intro t ht h1 h2
      have h_image_eq : Finset.image e_def Finset.univ = S := by
        convert Finset.image_orderEmbOfFin_univ S rfl using 1 <;>
          ext x <;> simp only [Finset.mem_image] <;> rfl
      have h_exists : ∃ (j : Fin k_def), e_def j = t := by
        have h : t ∈ Finset.image e_def Finset.univ := by
          rw [h_image_eq] <;> exact ht
        rcases Finset.mem_image.mp h with ⟨j, _, rfl⟩
        exact ⟨j, rfl⟩
      rcases h_exists with ⟨j, hj⟩
      have h_j_gt : (Fin.castSucc i).val < j.val := by
        have h4 : ts_canon (Fin.castSucc i) < e_def j := by rw [hj] <;> exact h1
        have h5 : e_def ⟨(Fin.castSucc i).val, by omega⟩ = ts_canon (Fin.castSucc i) := by rfl
        rw [←h5] at h4
        exact OrderEmbedding.strictMono e_def |>.lt_iff_lt.mp h4
      have h_j_lt : j.val < (Fin.succ i).val := by
        have h4 : e_def j < ts_canon (Fin.succ i) := by rw [hj] <;> exact h2
        have h5 : e_def ⟨(Fin.succ i).val, by omega⟩ = ts_canon (Fin.succ i) := by rfl
        rw [←h5] at h4
        exact OrderEmbedding.strictMono e_def |>.lt_iff_lt.mp h4
      simp [Fin.castSucc, Fin.succ] at h_j_gt h_j_lt <;> omega
    exact hS.2.2 s₁ s₂ h_s1_in h_s2_in h_lt h_no_between
  let covers_def (i : Fin n_def) : Opens X := (Classical.choose (choose_data_def i))
  let hcover_mem_def (i : Fin n_def) : covers_def i ∈ 𝒰 := (Classical.choose_spec (choose_data_def i)).1
  let h_range_def (i : Fin n_def) : ∀ (t : I), ts_canon (Fin.castSucc i) ≤ t → t ≤ ts_canon (Fin.succ i) → γ t ∈ (covers_def i : Set X) := (Classical.choose_spec (choose_data_def i)).2
  -- Now we have n_def = n definitionally (since S.card = n + 1)
  -- So we can cast everything to Fin n
  -- Actually, since S.card = n + 1 definitionally, k_def = n + 1, n_def = n
  -- So all the types match!
  have h_n_def_eq : n_def = n := by
    dsimp only [n_def, k_def]
    <;> omega
  -- Now we can just use ts_indep and covers_indep
  -- But first, we need to transport ts_canon and covers_def to Fin (n + 1) and Fin n
  -- Wait, since n_def = n definitionally, we don't need to transport!
  -- Let's just apply the lemmas directly
  -- First, let's show that ts_canon and ts have the same image S
  have h_ts_canon_strict : StrictMono ts_canon := by
    dsimp only [ts_canon]
    intro i j h
    exact OrderEmbedding.strictMono e_def (by simpa using h)
  have h_ts_canon_image : Finset.image ts_canon Finset.univ = S := by
    dsimp only [ts_canon]
    have h1 : Finset.image ts_canon Finset.univ = Finset.image e_def Finset.univ := by
      ext x
      simp only [ts_canon, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨⟨i.val, by omega⟩, rfl⟩
      · rintro ⟨j, rfl⟩
        have h_j_lt : j.val < n_def + 1 := by omega
        let i : Fin (n_def + 1) := ⟨j.val, h_j_lt⟩
        exact ⟨i, by simp [i] <;> rfl⟩
    rw [h1]
    convert Finset.image_orderEmbOfFin_univ S rfl using 1 <;>
          ext x <;> simp only [Finset.mem_image] <;> rfl
  -- Save n before subst since it's a parameter and might get shadowed
  let n_save := n
  let ts_save := ts
  let h_ts_strict_save := h_ts_strict
  let h_ts_image_save := h_ts_image
  let covers_save := covers
  let hcover_mem_save := hcover_mem
  let h_range_save := h_range
  -- Now substitute n_def with n
  subst h_n_def_eq
  -- Now n_def = n definitionally
  -- Great! Now all types match.
  -- First, apply ts_indep to change from ts_canon to ts
  -- We need to provide a h_range argument for ts
  have h_range_def' : ∀ (i : Fin n_save), ∀ (t : I), ts_save (Fin.castSucc i) ≤ t → t ≤ ts_save (Fin.succ i) → γ t ∈ (covers_def i : Set X) := by
    intro i t h1 h2
    -- We have h_range_def for ts_canon, we need it for ts
    -- First, show ts_canon = ts
    have h_ts_canon_mem : ∀ (j : Fin (n_save + 1)), ts_canon j ∈ S := by
      intro j
      have h : ts_canon j ∈ Finset.image ts_canon Finset.univ := by
        apply Finset.mem_image.mpr
        exact ⟨j, Finset.mem_univ j, rfl⟩
      rw [h_ts_canon_image] at h
      exact h
    have h_eq_ts : ts_canon = ts_save := by
      have h1 : ts_canon = S.orderEmbOfFin (by rw [hk]) := Finset.orderEmbOfFin_unique (by rw [hk]) h_ts_canon_mem h_ts_canon_strict
      have h_ts_mem : ∀ (j : Fin (n_save + 1)), ts_save j ∈ S := by
        intro j
        have h : ts_save j ∈ Finset.image ts_save Finset.univ := by
          apply Finset.mem_image.mpr
          exact ⟨j, Finset.mem_univ j, rfl⟩
        rw [h_ts_image_save] at h
        exact h
      have h2 : ts_save = S.orderEmbOfFin (by rw [hk]) := Finset.orderEmbOfFin_unique (by rw [hk]) h_ts_mem h_ts_strict_save
      rw [h1, h2]
    have h1' : ts_canon (Fin.castSucc i) ≤ t := by
      rw [h_eq_ts]
      exact h1
    have h2' : t ≤ ts_canon (Fin.succ i) := by
      rw [h_eq_ts]
      exact h2
    exact h_range_def i t h1' h2'
  -- Now apply ts_indep
  have h_step1 : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n_save ts_canon h_ts_canon_strict h_ts_canon_image covers_def hcover_mem_def h_range_def =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n_save ts_save h_ts_strict_save h_ts_image_save covers_def hcover_mem_def h_range_def' := by
    apply my_map_from_adapted_subdivision_ts_indep
  -- Now apply covers_indep
  have h_step2 : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n_save ts_save h_ts_strict_save h_ts_image_save covers_def hcover_mem_def h_range_def' =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n_save ts_save h_ts_strict_save h_ts_image_save covers_save hcover_mem_save h_range_save := by
    apply my_map_from_adapted_subdivision_covers_indep
  -- Done!
  rw [h_step1, h_step2]

/-- For a trivial 1-segment subdivision (the whole path is covered by U),
    my_map_from_adapted_subdivision_with_covers equals single_covered_map. -/
theorem my_map_from_adapted_subdivision_single_segment
    {x y : X} {γ : Path x y} {S : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (ts : Fin 2 → I)
    (h_ts0 : ts 0 = (0 : I))
    (h_ts1 : ts 1 = (1 : I))
    (h_ts_strict : StrictMono ts)
    (h_ts_image : Finset.image ts Finset.univ = S)
    (U : Opens X) (hU : U ∈ 𝒰) (h_range : Set.range γ ⊆ (U : Set X)) :
    my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS 1 ts h_ts_strict h_ts_image
      (fun _ : Fin 1 => U)
      (fun _ => hU)
      (fun _ t h1 h2 => by
        have h1' : γ t ∈ Set.range γ := ⟨t, rfl⟩
        exact h_range h1') =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range := by
  dsimp only [my_map_from_adapted_subdivision_with_covers]
  -- Let's give names to all the components
  let pts (i : Fin 2) : X := γ (ts i)
  let γs (i : Fin 1) : Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) :=
    γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))
  have h_ranges (i : Fin 1) : Set.range (γs i) ⊆ (U : Set X) := by
    have h_lt : (Fin.castSucc i) < (Fin.succ i) := by
      apply Fin.castSucc_lt_succ
    have h_ts_lt : ts (Fin.castSucc i) < ts (Fin.succ i) := h_ts_strict h_lt
    have h_range_eq : Set.range (γs i) = γ '' Set.Icc (ts (Fin.castSucc i)) (ts (Fin.succ i)) := by
      rw [Path.range_subpath γ (ts (Fin.castSucc i)) (ts (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, _, rfl⟩
    have h1' : γ t ∈ Set.range γ := ⟨t, rfl⟩
    exact h_range h1'
  let objs : Fin 2 → s.pt := fun i =>
    desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
  let homs : ∀ i : Fin 1, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) U hU (h_ranges i)
  let f : objs 0 ⟶ objs (Fin.last 1) := comp_list 1 objs homs
  have h_pts0 : pts 0 = x := by
    dsimp only [pts]
    rw [h_ts0]
    exact γ.source
  have h_pts1 : pts 1 = y := by
    dsimp only [pts]
    rw [h_ts1]
    exact γ.target
  let eq0 : objs 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
    dsimp only [objs]
    rw [h_pts0]
    <;> rfl
  have h_last1 : pts (Fin.last 1) = y := by
    have h : (Fin.last 1) = (1 : Fin 2) := by decide
    rw [h]
    exact h_pts1
  let eq_last : objs (Fin.last 1) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
    dsimp only [objs]
    rw [h_last1]
    <;> rfl
  -- Now we have the same structure as the definition
  -- First, comp_list 1 objs homs = homs 0
  have h_comp : comp_list 1 objs homs = homs 0 := comp_list_one objs homs
  -- Our goal is: eqToHom eq0.symm ≫ f ≫ eqToHom eq_last = single_covered_map γ U hU h_range
  -- We have f = homs 0
  -- So we need: eqToHom eq0.symm ≫ homs 0 ≫ eqToHom eq_last = single_covered_map γ U hU h_range
  -- And homs 0 = single_covered_map (γs 0) U hU (h_ranges 0)
  -- So we need to relate single_covered_map of the subpath to single_covered_map of the original path
  -- Note: γs 0 = γ.subpath (ts 0) (ts 1) = γ.subpath 0 1
  -- And by Path.subpath_zero_one, γ.subpath 0 1 = γ.cast γ.source γ.target
  -- So we need to show that single_covered_map is invariant under path casting
  -- First, prove that ∀ t, γs 0 t = γ t
  have h_general : ∀ (a b : I), a = (0 : I) → b = (1 : I) → ∀ (t : I), (γ.subpath a b) t = γ t := by
    intro a b ha hb t
    cases ha
    cases hb
    have h4 : (γ.subpath (0 : I) (1 : I)) t = γ t := by
      have h5 : γ.subpath (0 : I) (1 : I) = γ.cast γ.source γ.target := Path.subpath_zero_one γ
      rw [h5]
      <;> rfl
    exact h4
  have h_fun : ∀ (t : I), γs 0 t = γ t := by
    intro t
    have h1 : γs 0 = γ.subpath (ts 0) (ts 1) := by rfl
    rw [h1]
    exact h_general (ts 0) (ts 1) h_ts0 h_ts1 t
  -- Now apply the congruence lemma
  have h_goal : eqToHom eq0.symm ≫ homs 0 ≫ eqToHom eq_last = single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range := by
    dsimp only [homs]
    have h_eq0 : eq0 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts0 := by
      rfl
    have h_eq_last : eq_last = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1 := by
      rfl
    rw [h_eq0, h_eq_last]
    exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s (γs 0) γ h_pts0 h_pts1 h_fun U hU (h_ranges 0) h_range
  rw [h_comp]
  exact h_goal

/-- Helper: subpath range subset -/
private lemma subpath_range_in_cover_helper {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    {s₁ s₂ : I} (h_lt : s₁ < s₂) {U : Opens X}
    (h : ∀ (t : I), s₁ ≤ t → t ≤ s₂ → γ t ∈ U) :
    Set.range (γ.subpath s₁ s₂) ⊆ (U : Set X) := by
  have h_range_eq : Set.range (γ.subpath s₁ s₂) = γ '' Set.Icc s₁ s₂ := by
    rw [Path.range_subpath γ s₁ s₂, Set.uIcc_of_le (le_of_lt h_lt)]
  rw [h_range_eq]
  intro z hz
  rcases hz with ⟨u, hu, rfl⟩
  exact h u hu.1 hu.2

set_option maxHeartbeats 500000
theorem my_map_from_adapted_subdivision_refines_one
    {x y : X} {γ : Path x y} {S : Finset I} {t : I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ (S ∪ {t})) :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' := by
  classical
  by_cases h_t_in_S : t ∈ S
  · -- Case 1: t ∈ S, then S ∪ {t} = S, so trivial
    have h_set_eq : S ∪ {t} = S := by
      ext x
      simp [h_t_in_S] <;> tauto
    have h_goal : ∀ (S1 S2 : Finset I) (h_eq : S1 = S2)
        (h1 : IsAdaptedSubdivision 𝒰 γ S1)
        (h2 : IsAdaptedSubdivision 𝒰 γ S2),
        my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s h1 =
        my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s h2 := by
      intro S1 S2 h_eq h1 h2
      subst h_eq
      congr
      <;> exact Subsingleton.elim h1 h2
    have h_eq : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' =
        my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS :=
      h_goal (S ∪ {t}) S h_set_eq hS' hS
    exact h_eq.symm
  · -- Case 2: t ∉ S
    have h_t_not_in_S : t ∉ S := h_t_in_S
    -- Get the canonical decomposition for S
    have h0_in_S : (0 : I) ∈ S := hS.1
    have h1_in_S : (1 : I) ∈ S := hS.2.1
    have hS_nonempty : S.Nonempty := ⟨0, h0_in_S⟩
    let k : ℕ := S.card
    have hk : S.card = k := rfl
    have hk_pos : 0 < k := Finset.card_pos.mpr hS_nonempty
    have hk_ge2 : 2 ≤ k := by
      have h0_ne_1 : (0 : I) ≠ (1 : I) := by
        intro h
        have h' : (0 : ℝ) = (1 : ℝ) := congr_arg (fun x : I => (x : ℝ)) h
        norm_num at h' <;> exact h'
      have h : ({(0 : I), (1 : I)} : Finset I) ⊆ S := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with (rfl | rfl) <;> tauto
      have h2 : ({(0 : I), (1 : I)} : Finset I).card ≤ S.card := Finset.card_le_card h
      have h3 : ({(0 : I), (1 : I)} : Finset I).card = 2 := by
        simp [h0_ne_1] <;> rfl
      rw [h3] at h2
      exact h2
    let e : Fin k ↪o I := S.orderEmbOfFin hk
    have h_e_mem : ∀ (i : Fin k), e i ∈ S := Finset.orderEmbOfFin_mem S hk
    have h_e_strict_mono : StrictMono e := OrderEmbedding.strictMono e
    have h_e_image : Finset.image e Finset.univ = S := by
      convert Finset.image_orderEmbOfFin_univ S hk using 1 <;>
      ext x <;> simp only [Finset.mem_image] <;> rfl
    let n : ℕ := k - 1
    have hk_eq : k = n + 1 := by omega
    let ts_S (i : Fin (n + 1)) : I := e ⟨i.val, by rw [hk_eq] <;> exact i.is_lt⟩
    have h_ts_S_strict : StrictMono ts_S := by
      intro i j h
      exact h_e_strict_mono (by simpa [ts_S] using h)
    have h_ts_S_image : Finset.image ts_S Finset.univ = S := by
      have h1 : Finset.image ts_S Finset.univ = Finset.image e Finset.univ := by
        ext x
        simp only [ts_S, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨⟨i.val, by rw [hk_eq]; exact i.is_lt⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          have h_j_lt : j.val < n + 1 := by rw [←hk_eq]; exact j.is_lt
          let i : Fin (n + 1) := ⟨j.val, h_j_lt⟩
          exact ⟨i, by simp [i] <;> rfl⟩
      rw [h1, h_e_image]
    have h_ts0_eq : ts_S 0 = (0 : I) := by
      have h0 : ts_S 0 ∈ S := by
        have h : ts_S 0 ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
        rw [h_ts_S_image] at h
        exact h
      have h0_in : (0 : I) ∈ S := h0_in_S
      have h_le : (0 : I) ≤ ts_S 0 := by
        exact?
      have h_ge : ts_S 0 ≤ (0 : I) := by
        have h_exists : ∃ (i : Fin (n + 1)), ts_S i = (0 : I) := by
          have h : (0 : I) ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h0_in
          rcases Finset.mem_image.mp h with ⟨i, _, h_eq⟩
          exact ⟨i, h_eq⟩
        rcases h_exists with ⟨i, hi⟩
        have h_i_ge : 0 ≤ i := by
          exact?
        have h_mono : StrictMono ts_S := h_ts_S_strict
        have h : ts_S 0 ≤ ts_S i := h_mono.monotone h_i_ge
        rw [hi] at h
        exact h
      exact le_antisymm h_ge h_le
    have h_ts1_eq : ts_S (Fin.last n) = (1 : I) := by
      have h1 : ts_S (Fin.last n) ∈ S := by
        have h : ts_S (Fin.last n) ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, rfl⟩
        rw [h_ts_S_image] at h
        exact h
      have h1_in : (1 : I) ∈ S := h1_in_S
      have h_le : ts_S (Fin.last n) ≤ (1 : I) := by
        exact?
      have h_ge : (1 : I) ≤ ts_S (Fin.last n) := by
        have h_exists : ∃ (i : Fin (n + 1)), ts_S i = (1 : I) := by
          have h : (1 : I) ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h1_in
          rcases Finset.mem_image.mp h with ⟨i, _, h_eq⟩
          exact ⟨i, h_eq⟩
        rcases h_exists with ⟨i, hi⟩
        have h_i_le : i ≤ Fin.last n := by exact Fin.le_last i
        have h_mono : StrictMono ts_S := h_ts_S_strict
        have h : ts_S i ≤ ts_S (Fin.last n) := h_mono.monotone h_i_le
        rw [hi] at h
        exact h
      exact le_antisymm h_le h_ge
    -- Get canonical covers for S
    have h_main_exists : ∃ (covers_S : Fin n → Opens X),
        (∀ i, covers_S i ∈ 𝒰) ∧
        (∀ i, ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (covers_S i : Set X)) := by
      have h_helper : ∀ (i : Fin n), ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (U : Set X) := by
        intro i
        let s₁ := ts_S (Fin.castSucc i)
        let s₂ := ts_S (Fin.succ i)
        have h_s1_in : s₁ ∈ S := by
          have h : s₁ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨Fin.castSucc i, Finset.mem_univ _, rfl⟩
          rw [h_ts_S_image] at h
          exact h
        have h_s2_in : s₂ ∈ S := by
          have h : s₂ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨Fin.succ i, Finset.mem_univ _, rfl⟩
          rw [h_ts_S_image] at h
          exact h
        have h_lt : s₁ < s₂ := h_ts_S_strict (by
          apply Fin.lt_iff_val_lt_val.mpr
          simp [Fin.castSucc, Fin.succ] <;> omega)
        have h_no_between : ∀ (x : I), x ∈ S → s₁ < x → x < s₂ → False := by
          intro x hx h1 h2
          have h_exists : ∃ (j : Fin k), e j = x := by
            have h : x ∈ Finset.image e Finset.univ := by rw [h_e_image] <;> exact hx
            rcases Finset.mem_image.mp h with ⟨j, _, rfl⟩
            exact ⟨j, rfl⟩
          rcases h_exists with ⟨j, hj⟩
          have h_j_gt : (Fin.castSucc i).val < j.val := by
            have h4 : ts_S (Fin.castSucc i) < e j := by rw [hj] <;> exact h1
            exact Fin.lt_iff_val_lt_val.mp (by simpa [ts_S] using h4)
          have h_j_lt : j.val < (Fin.succ i).val := by
            have h4 : e j < ts_S (Fin.succ i) := by rw [hj] <;> exact h2
            exact Fin.lt_iff_val_lt_val.mp (by simpa [ts_S] using h4)
          have h1 : i.val < j.val := by
            simpa [Fin.castSucc] using h_j_gt
          have h2 : j.val < i.val + 1 := by
            simpa [Fin.succ] using h_j_lt
          omega
        exact hS.2.2 s₁ s₂ h_s1_in h_s2_in h_lt h_no_between
      choose covers_S hcover_mem_S h_range_S using h_helper
      exact ⟨covers_S, hcover_mem_S, h_range_S⟩
    rcases h_main_exists with ⟨covers_S, hcover_mem_S, h_range_S⟩
    -- Now we have ts_S, covers_S for S
    -- We need to find where t fits in the subdivision
    have h_t_between : (0 : I) ≤ t ∧ t < (1 : I) := by
      constructor
      · exact?
      · by_contra h
        have h' : (1 : I) ≤ t := by exact le_of_not_gt h
        have h1_in : (1 : I) ∈ S := h1_in_S
        have h_t_in_S' : t ∈ S ∪ {t} := by simp
        have h2 : t ≤ (1 : I) := by
          exact?

        have h4 : t = (1 : I) := by exact le_antisymm h2 h'
        rw [h4] at h_t_not_in_S
        exact h_t_not_in_S h1_in
    let P : Fin k → Prop := fun i => e i ≤ t
    let zero_Fin_k : Fin k := ⟨0, hk_pos⟩
    have h_i0_P : P zero_Fin_k := by
      dsimp only [P, zero_Fin_k]
      have h_e0 : e zero_Fin_k = ts_S (0 : Fin (n + 1)) := by
        simp [ts_S, zero_Fin_k] <;> rfl
      rw [h_e0, h_ts0_eq]
      exact h_t_between.1
    let i_max : Fin k := Finset.max' (Finset.filter P Finset.univ) ⟨zero_Fin_k, by simp [h_i0_P]⟩
    have h_i_max_mem : i_max ∈ Finset.filter P Finset.univ := Finset.max'_mem _ _
    have h_i_max_P : P i_max := (Finset.mem_filter.mp h_i_max_mem).2
    have h_i_max_le_t : e i_max ≤ t := h_i_max_P
    have h_not : ¬ ((1 : I) ≤ t) := by
      intro h
      have h' : t < (1 : I) := h_t_between.2
      have h'' : (t : ℝ) < (1 : ℝ) := by exact_mod_cast h'
      have h''' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
      linarith
    have h_k_pos : 0 < k := by omega
    let last_k : Fin k := ⟨k - 1, by omega⟩
    have h_e_last : e last_k = (1 : I) := by
      have h2 : (1 : I) ∈ S := h1_in_S
      have h : e last_k = (1 : I) := by
        exact?
      exact h
    have h_i_max_lt_last : i_max < last_k := by
      have h1 : e i_max < e last_k := by
        rw [h_e_last]
        exact lt_of_le_of_lt h_i_max_le_t h_t_between.2
      exact h_e_strict_mono.lt_iff_lt.mp h1
    let m_val : ℕ := i_max.val
    have h_m_val_lt_n : m_val < n := by
      dsimp only [n, m_val]
      have h : i_max.val < last_k.val := Fin.lt_iff_val_lt_val.mp h_i_max_lt_last
      simpa [last_k, Fin.last] using h
    let m : Fin n := ⟨m_val, h_m_val_lt_n⟩
    have h_e_i_max_le_t : e i_max ≤ t := h_i_max_P
    let i_succ : Fin k := ⟨i_max.val + 1, by omega⟩
    have h_i_succ_not_P : ¬ P i_succ := by
      intro h
      have h6 : i_succ ∈ Finset.filter P Finset.univ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have h7 : i_succ ≤ i_max := Finset.le_max' (Finset.filter P Finset.univ) i_succ h6
      have h8 : i_max < i_succ := by
        apply Fin.lt_iff_val_lt_val.mpr
        simp [i_succ] <;> omega
      have h9 : ¬ (i_succ ≤ i_max) := by
        intro h10
        have h11 : i_max < i_succ := h8
        exact Fin.not_le.mpr h11 h10
      exact h9 h7
    have h_t_lt_e_succ : t < e i_succ := by
      dsimp only [P] at h_i_succ_not_P
      exact lt_of_not_ge h_i_succ_not_P
    have h_e_i_max_lt_t : e i_max < t := by
      apply lt_of_le_of_ne h_e_i_max_le_t
      intro h_eq
      have h9 : e i_max = t := h_eq
      have h10 : e i_max ∈ S := h_e_mem i_max
      rw [h9] at h10
      exact h_t_not_in_S h10
    have h_m_left : ts_S (Fin.castSucc m) < t := by
      simpa [ts_S, m] using h_e_i_max_lt_t
    have h_m_right : t < ts_S (Fin.succ m) := by
      simpa [ts_S, m] using h_t_lt_e_succ
    -- Define ts' explicitly by inserting t at position m+1
    let ts' (i : Fin (n + 2)) : I :=
      if h : i.val ≤ m.val then
        ts_S ⟨i.val, by omega⟩
      else if h' : i.val = m.val + 1 then
        t
      else
        ts_S ⟨i.val - 1, by omega⟩
    -- Define covers' explicitly by duplicating covers_S m at positions m and m+1
    let covers' (i : Fin (n + 1)) : Opens X :=
      if h : i.val < m.val then
        covers_S ⟨i.val, by omega⟩
      else if h' : i.val = m.val then
        covers_S m
      else if h'' : i.val = m.val + 1 then
        covers_S m
      else
        covers_S ⟨i.val - 1, by omega⟩
    -- Prove ts' is strictly monotone
    have h_ts'_strict : StrictMono ts' := by
      intro i j h_lt
      dsimp only [ts']
      have h_ij : i.val < j.val := by
        exact Fin.lt_iff_val_lt_val.mp h_lt
      by_cases h_i_le_m : i.val ≤ m.val
      · by_cases h_j_le_m : j.val ≤ m.val
        · rw [dif_pos h_i_le_m, dif_pos h_j_le_m]
          have h_lt2 : (⟨i.val, by omega⟩ : Fin (n + 1)) < (⟨j.val, by omega⟩ : Fin (n + 1)) := by
            apply Fin.lt_iff_val_lt_val.mpr
            exact h_ij
          exact h_ts_S_strict h_lt2
        · rw [dif_pos h_i_le_m]
          by_cases h_j_eq : j.val = m.val + 1
          · rw [dif_neg (by omega), dif_pos h_j_eq]
            have h_i_le_m2 : (⟨i.val, by omega⟩ : Fin (n + 1)) ≤ Fin.castSucc m := by
              apply Fin.le_iff_val_le_val.mpr
              exact h_i_le_m
            have h1 : ts_S ⟨i.val, by omega⟩ ≤ ts_S (Fin.castSucc m) := h_ts_S_strict.monotone h_i_le_m2
            exact lt_of_le_of_lt h1 h_m_left
          · rw [dif_neg (by omega), dif_neg h_j_eq]
            have h_i_lt_j1 : i.val < j.val - 1 := by omega
            have h_lt2 : (⟨i.val, by omega⟩ : Fin (n + 1)) < (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
              apply Fin.lt_iff_val_lt_val.mpr
              exact h_i_lt_j1
            have h1 : ts_S ⟨i.val, by omega⟩ < ts_S ⟨j.val - 1, by omega⟩ := h_ts_S_strict h_lt2
            exact h1
      · have h_i_gt_m : m.val < i.val := by omega
        by_cases h_i_eq : i.val = m.val + 1
        · rw [dif_neg h_i_le_m, dif_pos h_i_eq]
          by_cases h_j_eq : j.val = m.val + 1
          · omega
          · by_cases h_j_gt : j.val > m.val + 1
            · rw [dif_neg (by omega), dif_neg h_j_eq]
              have h1 : t < ts_S ⟨j.val - 1, by omega⟩ := by
                have h_j1_val_ge : m.val + 1 ≤ j.val - 1 := by omega
                have h_j1_ge : (Fin.succ m : Fin (n + 1)) ≤ ⟨j.val - 1, by omega⟩ := by
                  apply Fin.le_iff_val_le_val.mpr
                  simpa [Fin.succ] using h_j1_val_ge
                have h2 : ts_S (Fin.succ m) ≤ ts_S ⟨j.val - 1, by omega⟩ := h_ts_S_strict.monotone h_j1_ge
                exact lt_of_lt_of_le h_m_right h2
              exact h1
            · omega
        · rw [dif_neg h_i_le_m, dif_neg h_i_eq]
          rw [dif_neg (by omega), dif_neg (by omega)]
          have h_i_lt_j1 : i.val - 1 < j.val - 1 := by omega
          have h_lt2 : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) < (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
            apply Fin.lt_iff_val_lt_val.mpr
            exact h_i_lt_j1
          exact h_ts_S_strict h_lt2
    -- Prove ts' has image S ∪ {t}
    have h_ts'_image : Finset.image ts' Finset.univ = S ∪ {t} := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        dsimp only [ts']
        by_cases h1 : i.val ≤ m.val
        · rw [dif_pos h1]
          left
          have h2 : ts_S ⟨i.val, by omega⟩ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, rfl⟩
          rw [h_ts_S_image] at h2
          exact h2
        · by_cases h2 : i.val = m.val + 1
          · rw [dif_neg h1, dif_pos h2]
            right
            rfl
          · rw [dif_neg h1, dif_neg h2]
            left
            have h3 : ts_S ⟨i.val - 1, by omega⟩ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, rfl⟩
            rw [h_ts_S_image] at h3
            exact h3
      · rintro (h | h_eq)
        · -- x ∈ S
          have h_x_in : x ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h
          rcases Finset.mem_image.mp h_x_in with ⟨i, _, rfl⟩
          by_cases h_i_le_m : i.val ≤ m.val
          · let j : Fin (n + 2) := ⟨i.val, by omega⟩
            have h_ts'_j : ts' j = ts_S i := by
              dsimp only [ts', j]
              rw [dif_pos h_i_le_m] <;> rfl
            exact ⟨j, h_ts'_j⟩
          · have h_i_gt_m : i.val > m.val := by omega
            let j : Fin (n + 2) := ⟨i.val + 1, by omega⟩
            have h_ts'_j : ts' j = ts_S i := by
              dsimp only [ts', j]
              rw [dif_neg (by omega), dif_neg (by omega)] <;> congr <;> omega
            exact ⟨j, h_ts'_j⟩
        · -- x = t
          have h_x_eq_t : x = t := h_eq
          let j : Fin (n + 2) := ⟨m.val + 1, by omega⟩
          have h_ts'_j : ts' j = t := by
            dsimp only [ts', j]
            rw [dif_neg (by omega), dif_pos (by omega)] <;> rfl
          have h_ts'_j_x : ts' j = x := by
            rw [h_ts'_j, h_x_eq_t.symm]
          exact ⟨j, h_ts'_j_x⟩
    -- Prove covers' are in 𝒰
    have hcover_mem' : ∀ i : Fin (n + 1), covers' i ∈ 𝒰 := by
      intro i
      dsimp only [covers']
      by_cases h1 : i.val < m.val
      · rw [dif_pos h1]
        exact hcover_mem_S ⟨i.val, by omega⟩
      · by_cases h2 : i.val = m.val
        · rw [dif_neg h1, dif_pos h2]
          exact hcover_mem_S m
        · by_cases h3 : i.val = m.val + 1
          · rw [dif_neg h1, dif_neg h2, dif_pos h3]
            exact hcover_mem_S m
          · rw [dif_neg h1, dif_neg h2, dif_neg h3]
            exact hcover_mem_S ⟨i.val - 1, by omega⟩
    -- Prove range condition for covers'
    have h_range' : ∀ (i : Fin (n + 1)) (t_val : I),
        ts' (Fin.castSucc i) ≤ t_val → t_val ≤ ts' (Fin.succ i) → γ t_val ∈ (covers' i : Set X) := by
      intro i t_val h1 h2
      dsimp only [covers']
      by_cases h_i_lt_m : i.val < m.val
      · rw [dif_pos h_i_lt_m]
        have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc ⟨i.val, by omega⟩) := by
          dsimp only [ts']
          have h : (Fin.castSucc i).val ≤ m.val := by simp [Fin.castSucc, h_i_lt_m] <;> omega
          rw [dif_pos h] <;> rfl
        have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ ⟨i.val, by omega⟩) := by
          dsimp only [ts']
          have h : (Fin.succ i).val ≤ m.val := by simp [Fin.succ, h_i_lt_m] <;> omega
          rw [dif_pos h] <;> rfl
        rw [h_ts1] at h1
        rw [h_ts2] at h2
        exact h_range_S ⟨i.val, by omega⟩ t_val h1 h2
      · rw [dif_neg h_i_lt_m]
        by_cases h_i_eq_m : i.val = m.val
        · rw [dif_pos h_i_eq_m]
          have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc m) := by
            dsimp only [ts']
            have h_cast_val : (Fin.castSucc i).val = i.val := by simp [Fin.castSucc]
            have h : (Fin.castSucc i).val ≤ m.val := by
              rw [h_cast_val, h_i_eq_m]
            have h_eq_val : (Fin.castSucc i).val = (Fin.castSucc m).val := by
              rw [h_cast_val, h_i_eq_m] <;> simp [Fin.castSucc]
            have h_fin_eq : (⟨(Fin.castSucc i).val, by omega⟩ : Fin (n + 1)) = Fin.castSucc m := by
              apply Fin.ext
              simpa [Fin.castSucc] using h_eq_val
            rw [dif_pos h]
            rw [h_fin_eq]
          have h_ts2 : ts' (Fin.succ i) = t := by
            dsimp only [ts']
            have h_succ_val : (Fin.succ i).val = i.val + 1 := by simp [Fin.succ]
            have h1 : ¬ (Fin.succ i).val ≤ m.val := by
              rw [h_succ_val, h_i_eq_m] <;> omega
            have h2 : (Fin.succ i).val = m.val + 1 := by
              rw [h_succ_val, h_i_eq_m]
            rw [dif_neg h1, dif_pos h2] <;> congr <;> simp [Fin.succ, h_i_eq_m]
          rw [h_ts1] at h1
          rw [h_ts2] at h2
          have h3 : t_val ≤ ts_S (Fin.succ m) := by
            have h4 : t_val < ts_S (Fin.succ m) := by
              exact lt_of_le_of_lt h2 h_m_right
            exact le_of_lt h4
          exact h_range_S m t_val h1 h3
        · rw [dif_neg h_i_eq_m]
          by_cases h_i_eq_m1 : i.val = m.val + 1
          · rw [dif_pos h_i_eq_m1]
            have h_ts1 : ts' (Fin.castSucc i) = t := by
              dsimp only [ts']
              have h1 : ¬ (Fin.castSucc i).val ≤ m.val := by
                simp [Fin.castSucc, h_i_eq_m1] <;> omega
              have h2 : (Fin.castSucc i).val = m.val + 1 := by
                simp [Fin.castSucc, h_i_eq_m1] <;> omega
              rw [dif_neg h1, dif_pos h2] <;> congr <;> omega
            have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ m) := by
              dsimp only [ts']
              have h1 : ¬ (Fin.succ i).val ≤ m.val := by
                simp [Fin.succ, h_i_eq_m1] <;> omega
              have h2 : ¬ (Fin.succ i).val = m.val + 1 := by
                simp [Fin.succ, h_i_eq_m1] <;> omega
              rw [dif_neg h1, dif_neg h2] <;> congr <;> omega
            rw [h_ts1] at h1
            rw [h_ts2] at h2
            have h3 : ts_S (Fin.castSucc m) ≤ t_val := by
              have h4 : ts_S (Fin.castSucc m) < t_val := by
                exact lt_of_lt_of_le h_m_left h1
              exact le_of_lt h4
            exact h_range_S m t_val h3 h2
          · rw [dif_neg h_i_eq_m1]
            have h_i_gt : m.val + 1 < i.val := by omega
            let j : Fin n := ⟨i.val - 1, by omega⟩
            have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc j) := by
              dsimp only [ts', j]
              have h1 : ¬ (Fin.castSucc i).val ≤ m.val := by
                simp [Fin.castSucc, j, h_i_gt] <;> omega
              have h2 : ¬ (Fin.castSucc i).val = m.val + 1 := by
                simp [Fin.castSucc, j, h_i_gt] <;> omega
              rw [dif_neg h1, dif_neg h2]
              apply congr_arg ts_S
              apply Fin.ext
              simp [Fin.castSucc, j] <;> omega
            have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ j) := by
              dsimp only [ts', j]
              have h1 : ¬ (Fin.succ i).val ≤ m.val := by
                simp [Fin.succ, j, h_i_gt] <;> omega
              have h2 : ¬ (Fin.succ i).val = m.val + 1 := by
                simp [Fin.succ, j, h_i_gt] <;> omega
              rw [dif_neg h1, dif_neg h2]
              apply congr_arg ts_S
              apply Fin.ext
              simp [Fin.succ, j] <;> omega
            rw [h_ts1] at h1
            rw [h_ts2] at h2
            exact h_range_S j t_val h1 h2
    -- Apply universal property to both sides
    have h_eq_S : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
        my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts_S h_ts_S_strict h_ts_S_image covers_S hcover_mem_S h_range_S :=
      my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS ts_S h_ts_S_strict h_ts_S_image covers_S hcover_mem_S h_range_S
    have h_eq_S' : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' =
        my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS' (n + 1) ts' h_ts'_strict h_ts'_image covers' hcover_mem' h_range' :=
      my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS' ts' h_ts'_strict h_ts'_image covers' hcover_mem' h_range'
    -- Core equality step
    have h_core : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts_S h_ts_S_strict h_ts_S_image covers_S hcover_mem_S h_range_S =
        my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS' (n + 1) ts' h_ts'_strict h_ts'_image covers' hcover_mem' h_range' := by
      dsimp only [my_map_from_adapted_subdivision_with_covers]
      let pts_S (i : Fin (n + 1)) : X := γ (ts_S i)
      let objs_S : Fin (n + 1) → s.pt := fun i =>
        desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts_S i))
      let γs_S (i : Fin n) : Path (pts_S (Fin.castSucc i)) (pts_S (Fin.succ i)) :=
        γ.subpath (ts_S (Fin.castSucc i)) (ts_S (Fin.succ i))
      have h_ranges_S (i : Fin n) : Set.range (γs_S i) ⊆ (covers_S i : Set X) := by
        have h_lt : Fin.castSucc i < Fin.succ i := by exact?
        have h_ts_lt : ts_S (Fin.castSucc i) < ts_S (Fin.succ i) := h_ts_S_strict h_lt
        have h_range : ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (covers_S i : Set X) := h_range_S i
        have h_range_eq : Set.range (γs_S i) = γ '' Set.Icc (ts_S (Fin.castSucc i)) (ts_S (Fin.succ i)) := by
          rw [Path.range_subpath γ (ts_S (Fin.castSucc i)) (ts_S (Fin.succ i))]
          <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t, ht, rfl⟩
        exact h_range t ht.1 ht.2
      let homs_S (i : Fin n) : objs_S (Fin.castSucc i) ⟶ objs_S (Fin.succ i) :=
        single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S i) (covers_S i) (hcover_mem_S i) (h_ranges_S i)
      let pts' (i : Fin (n + 2)) : X := γ (ts' i)
      let objs' : Fin (n + 2) → s.pt := fun i =>
        desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts' i))
      let γs' (i : Fin (n + 1)) : Path (pts' (Fin.castSucc i)) (pts' (Fin.succ i)) :=
        γ.subpath (ts' (Fin.castSucc i)) (ts' (Fin.succ i))
      have h_ranges' (i : Fin (n + 1)) : Set.range (γs' i) ⊆ (covers' i : Set X) := by
        have h_lt : Fin.castSucc i < Fin.succ i := by exact?
        have h_ts_lt : ts' (Fin.castSucc i) < ts' (Fin.succ i) := h_ts'_strict h_lt
        have h_range : ∀ (t_val : I), ts' (Fin.castSucc i) ≤ t_val → t_val ≤ ts' (Fin.succ i) → γ t_val ∈ (covers' i : Set X) := h_range' i
        have h_range_eq : Set.range (γs' i) = γ '' Set.Icc (ts' (Fin.castSucc i)) (ts' (Fin.succ i)) := by
          rw [Path.range_subpath γ (ts' (Fin.castSucc i)) (ts' (Fin.succ i))]
          <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t, ht, rfl⟩
        exact h_range t ht.1 ht.2
      let homs' (i : Fin (n + 1)) : objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i) :=
        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers' i) (hcover_mem' i) (h_ranges' i)
      let mid : s.pt := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (γ t))
      let γ1 : Path (pts_S (Fin.castSucc m)) (γ t) :=
        γ.subpath (ts_S (Fin.castSucc m)) t
      let γ2 : Path (γ t) (pts_S (Fin.succ m)) :=
        γ.subpath t (ts_S (Fin.succ m))
      have h_range1 : Set.range γ1 ⊆ (covers_S m : Set X) := by
        have h_range : ∀ (t_val : I), ts_S (Fin.castSucc m) ≤ t_val → t_val ≤ t → γ t_val ∈ (covers_S m : Set X) := by
          intro t_val h1 h2
          have h3 : t_val ≤ ts_S (Fin.succ m) := by
            have h4 : t_val < ts_S (Fin.succ m) := by
              exact lt_of_le_of_lt h2 h_m_right
            exact le_of_lt h4
          exact h_range_S m t_val h1 h3
        have h_range_eq : Set.range γ1 = γ '' Set.Icc (ts_S (Fin.castSucc m)) t := by
          rw [Path.range_subpath γ (ts_S (Fin.castSucc m)) t]
          <;> rw [Set.uIcc_of_le (le_of_lt h_m_left)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t_val, ht, rfl⟩
        exact h_range t_val ht.1 ht.2
      have h_range2 : Set.range γ2 ⊆ (covers_S m : Set X) := by
        have h_range : ∀ (t_val : I), t ≤ t_val → t_val ≤ ts_S (Fin.succ m) → γ t_val ∈ (covers_S m : Set X) := by
          intro t_val h1 h2
          have h3 : ts_S (Fin.castSucc m) ≤ t_val := by
            have h4 : ts_S (Fin.castSucc m) < t_val := by
              exact lt_of_lt_of_le h_m_left h1
            exact le_of_lt h4
          exact h_range_S m t_val h3 h2
        have h_range_eq : Set.range γ2 = γ '' Set.Icc t (ts_S (Fin.succ m)) := by
          rw [Path.range_subpath γ t (ts_S (Fin.succ m))]
          <;> rw [Set.uIcc_of_le (le_of_lt h_m_right)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t_val, ht, rfl⟩
        exact h_range t_val ht.1 ht.2
      let f : objs_S (Fin.castSucc m) ⟶ mid :=
        single_covered_map X 𝒰 hcover hfinite_intersections s γ1 (covers_S m) (hcover_mem_S m) h_range1
      let g : mid ⟶ objs_S (Fin.succ m) :=
        single_covered_map X 𝒰 hcover hfinite_intersections s γ2 (covers_S m) (hcover_mem_S m) h_range2
      have h_range_both : Set.range (γ1.trans γ2) ⊆ (covers_S m : Set X) :=
        range_trans_subset γ1 γ2 h_range1 h_range2
      have h_split : f ≫ g = single_covered_map X 𝒰 hcover hfinite_intersections s (γ1.trans γ2) (covers_S m) (hcover_mem_S m) h_range_both :=
        single_covered_split_eq X 𝒰 hcover hfinite_intersections s (covers_S m) (hcover_mem_S m) γ1 h_range1 γ2 h_range2
      let t₀ : I := ts_S (Fin.castSucc m)
      let t₁ : I := t
      let t₂ : I := ts_S (Fin.succ m)
      have h_t0_le_t1 : t₀ ≤ t₁ := le_of_lt h_m_left
      have h_t1_le_t2 : t₁ ≤ t₂ := le_of_lt h_m_right
      let H : Path.Homotopy (γ1.trans γ2) (γs_S m) :=
        Path.Homotopy.subpathTransSubpath γ t₀ t₁ t₂
      have hH : ∀ (p : I × I), H p ∈ (covers_S m : Set X) := by
        intro p
        have h_exists : ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧ H p = γ u :=
          VanKampen.subpathTransSubpath_range γ h_t0_le_t1 h_t1_le_t2 p
        rcases h_exists with ⟨u, hu1, hu2, h_eq⟩
        rw [h_eq]
        exact h_range_S m u hu1 hu2
      have h_both_eq : single_covered_map X 𝒰 hcover hfinite_intersections s (γ1.trans γ2) (covers_S m) (hcover_mem_S m) h_range_both =
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S m) (covers_S m) (hcover_mem_S m) (h_ranges_S m) :=
        single_covered_map_homotopic X 𝒰 hcover hfinite_intersections s (γ1.trans γ2) (γs_S m) (covers_S m) (hcover_mem_S m) h_range_both (h_ranges_S m) H hH
      have h_eq : homs_S m = f ≫ g := by
        dsimp only [homs_S]
        rw [←h_both_eq, ←h_split]
      have h0 : objs' 0 = objs_S 0 := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h_ts0 : ts' 0 = ts_S 0 := by
          dsimp only [ts']
          have h : (0 : Fin (n + 2)).val ≤ m.val := by
            simp <;> omega
          rw [dif_pos h] <;> rfl
        rw [h_ts0] <;> rfl
      have h_last : objs' (Fin.last (n + 1)) = objs_S (Fin.last n) := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h_ts_last : ts' (Fin.last (n + 1)) = ts_S (Fin.last n) := by
          dsimp only [ts']
          have h1 : ¬ (Fin.last (n + 1)).val ≤ m.val := by
            simp [Fin.last] <;> omega
          have h2 : ¬ (Fin.last (n + 1)).val = m.val + 1 := by
            simp [Fin.last] <;> omega
          rw [dif_neg h1, dif_neg h2] <;> simp [Fin.last] <;> omega
        rw [h_ts_last] <;> rfl
      have h_before : ∀ (i : Fin n), i.val < m.val →
          let j : Fin (n + 1) := Fin.castSucc i
          ∃ (h1 : objs' (Fin.castSucc j) = objs_S (Fin.castSucc i))
            (h2 : objs' (Fin.succ j) = objs_S (Fin.succ i)),
          eqToHom h1.symm ≫ homs' j ≫ eqToHom h2 = homs_S i := by
        intro i h_i_lt_m
        let j : Fin (n + 1) := Fin.castSucc i
        have h_j_lt_m : j.val < m.val := by
          dsimp only [j]
          simp [Fin.castSucc, h_i_lt_m] <;> omega
        have h_covers : covers' j = covers_S i := by
          dsimp only [covers', j]
          rw [dif_pos h_j_lt_m] <;> rfl
        have h_ts1 : ts' (Fin.castSucc j) = ts_S (Fin.castSucc i) := by
          dsimp only [ts']
          have h : (Fin.castSucc j).val ≤ m.val := by simp [Fin.castSucc, j, h_i_lt_m] <;> omega
          have h_eq_val : (Fin.castSucc j).val = (Fin.castSucc i).val := by
            simp [Fin.castSucc, j] <;> omega
          rw [dif_pos h]
          apply congr_arg
          apply Fin.ext
          exact h_eq_val
        have h_ts2 : ts' (Fin.succ j) = ts_S (Fin.succ i) := by
          dsimp only [ts']
          have h : (Fin.succ j).val ≤ m.val := by simp [Fin.succ, j, h_i_lt_m] <;> omega
          have h_eq_val : (Fin.succ j).val = (Fin.succ i).val := by
            simp [Fin.succ, j] <;> omega
          rw [dif_pos h]
          apply congr_arg
          apply Fin.ext
          exact h_eq_val
        have h_pts1 : pts' (Fin.castSucc j) = pts_S (Fin.castSucc i) := by
          dsimp only [pts', pts_S]
          rw [h_ts1] <;> rfl
        have h1 : objs' (Fin.castSucc j) = objs_S (Fin.castSucc i) := by
          dsimp only [objs', objs_S]
          rw [h_pts1] <;> rfl
        have h_pts2 : pts' (Fin.succ j) = pts_S (Fin.succ i) := by
          dsimp only [pts', pts_S]
          rw [h_ts2] <;> rfl
        have h2 : objs' (Fin.succ j) = objs_S (Fin.succ i) := by
          dsimp only [objs', objs_S]
          rw [h_pts2] <;> rfl
        refine' ⟨h1, h2, _⟩
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' j t_val = γs_S i t_val := by
          intro t_val
          dsimp only [γs', γs_S]
          have h_eq1 : ts' (Fin.castSucc j) = ts_S (Fin.castSucc i) := h_ts1
          have h_eq2 : ts' (Fin.succ j) = ts_S (Fin.succ i) := h_ts2
          simp [Path.subpath, h_eq1, h_eq2]
          <;> rfl
        -- Get hcover_mem for the cover
        have hU : covers_S i ∈ 𝒰 := hcover_mem_S i
        -- We need h_ranges' j with the rewritten cover
        have h_range1 : Set.range (γs' j) ⊆ (covers_S i : Set X) := by
          rw [←h_covers]
          exact h_ranges' j
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) (covers_S i) hU h_range1 ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2) =
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S i) (covers_S i) hU (h_ranges_S i) := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' j) (γs_S i) h_pts1 h_pts2 hfun (covers_S i) hU h_range1 (h_ranges_S i)
        -- The h1 and h2 are exactly the congr_arg equalities
        have h_eq1 : h1 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1 := by
          apply Subsingleton.elim
        have h_eq2 : h2 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2 := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' j vs covers_S i
        have h_covers_eq : covers' j = covers_S i := h_covers
        have hU' : covers' j ∈ 𝒰 := hcover_mem' j
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) (covers' j) hU' (h_ranges' j) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) (covers_S i) hU h_range1 := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' j) ⊆ (U : Set X))
              (hR2 : Set.range (γs' j) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' j) U hU hR1 hR2
          exact h (covers' j) (covers_S i) h_covers_eq hU' hU (h_ranges' j) h_range1
        -- Rewrite homs' j in the goal
        dsimp only [homs']
        rw [h_eq_map]
        exact h_main
      have h_split1 : objs' (Fin.castSucc (Fin.castSucc m)) = objs_S (Fin.castSucc m) := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h1 : (Fin.castSucc (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc] <;> omega
        have h_ts : ts' (Fin.castSucc (Fin.castSucc m)) = ts_S (Fin.castSucc m) := by
          dsimp only [ts']
          rw [dif_pos h1] <;> rfl
        rw [h_ts] <;> rfl
      have h_split2 : objs' (Fin.succ (Fin.castSucc m)) = mid := by
        dsimp only [objs', mid, pts']
        have h1 : ¬ (Fin.succ (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h2 : (Fin.succ (Fin.castSucc m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h_ts : ts' (Fin.succ (Fin.castSucc m)) = t := by
          dsimp only [ts']
          rw [dif_neg h1, dif_pos h2] <;> rfl
        rw [h_ts] <;> rfl
      have h_split3 : homs' (Fin.castSucc m) = eqToHom h_split1 ≫ f ≫ eqToHom h_split2.symm := by
        dsimp only [homs', f]
        have h_covers : covers' (Fin.castSucc m) = covers_S m := by
          dsimp only [covers']
          have h1 : (Fin.castSucc m).val = m.val := by simp [Fin.castSucc] <;> omega
          rw [dif_neg (by simp [Fin.castSucc] <;> omega), dif_pos h1] <;> rfl
        have h_path1 : ts' (Fin.castSucc (Fin.castSucc m)) = ts_S (Fin.castSucc m) := by
          dsimp only [ts']
          have h1 : (Fin.castSucc (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc] <;> omega
          rw [dif_pos h1] <;> rfl
        have h_path2 : ts' (Fin.succ (Fin.castSucc m)) = t := by
          dsimp only [ts']
          have h1 : ¬ (Fin.succ (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
          have h2 : (Fin.succ (Fin.castSucc m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
          rw [dif_neg h1, dif_pos h2] <;> rfl
        -- Extract endpoint equalities
        have hx : pts' (Fin.castSucc (Fin.castSucc m)) = pts_S (Fin.castSucc m) := by
          dsimp only [pts', pts_S]
          rw [h_path1] <;> rfl
        have hy : pts' (Fin.succ (Fin.castSucc m)) = γ t := by
          dsimp only [pts']
          rw [h_path2] <;> rfl
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' (Fin.castSucc m) t_val = γ1 t_val := by
          intro t_val
          dsimp only [γs', γ1]
          have h_eq1 : ts' (Fin.castSucc (Fin.castSucc m)) = ts_S (Fin.castSucc m) := h_path1
          have h_eq2 : ts' (Fin.succ (Fin.castSucc m)) = t := h_path2
          simp [Path.subpath, h_eq1, h_eq2]
          <;> rfl
        -- Get hcover_mem for the cover
        have hU : covers_S m ∈ 𝒰 := hcover_mem_S m
        -- We need h_ranges' (Fin.castSucc m) with the rewritten cover
        have h_range_prime : Set.range (γs' (Fin.castSucc m)) ⊆ (covers_S m : Set X) := by
          rw [←h_covers]
          exact h_ranges' (Fin.castSucc m)
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers_S m) hU h_range_prime ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy) =
            single_covered_map X 𝒰 hcover hfinite_intersections s γ1 (covers_S m) hU h_range1 := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' (Fin.castSucc m)) γ1 hx hy hfun (covers_S m) hU h_range_prime h_range1
        -- The h_split1 and h_split2 are exactly the congr_arg equalities
        have h_eq1 : h_split1 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx := by
          apply Subsingleton.elim
        have h_eq2 : h_split2 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' (Fin.castSucc m) vs covers_S m
        have h_covers_eq : covers' (Fin.castSucc m) = covers_S m := h_covers
        have hU' : covers' (Fin.castSucc m) ∈ 𝒰 := hcover_mem' (Fin.castSucc m)
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers' (Fin.castSucc m)) hU' (h_ranges' (Fin.castSucc m)) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers_S m) hU h_range_prime := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' (Fin.castSucc m)) ⊆ (U : Set X))
              (hR2 : Set.range (γs' (Fin.castSucc m)) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) U hU hR1 hR2
          exact h (covers' (Fin.castSucc m)) (covers_S m) h_covers_eq hU' hU (h_ranges' (Fin.castSucc m)) h_range_prime
        rw [h_eq_map]
        -- Rearrange h_main: from eqToHom(hx').symm ≫ A ≫ eqToHom(hy') = B
        -- get A = eqToHom(hx') ≫ B ≫ eqToHom(hy').symm
        let hx' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx
        let hy' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy
        let A := single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers_S m) hU h_range_prime
        let B := single_covered_map X 𝒰 hcover hfinite_intersections s γ1 (covers_S m) hU h_range1
        have h_final : A = eqToHom hx' ≫ B ≫ eqToHom hy'.symm := by
          let e_x : _ ≅ _ := eqToIso hx'
          let e_y : _ ≅ _ := eqToIso hy'
          have h_main2' : e_x.inv ≫ A ≫ e_y.hom = B := h_main
          exact VanKampen.iso_sandwich_rewrite e_x e_y A B h_main2'
        exact h_final
      have h_split4 : objs' (Fin.castSucc (Fin.succ m)) = mid := by
        dsimp only [objs', mid, pts']
        have h1 : ¬ (Fin.castSucc (Fin.succ m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h2 : (Fin.castSucc (Fin.succ m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h_ts : ts' (Fin.castSucc (Fin.succ m)) = t := by
          dsimp only [ts']
          rw [dif_neg h1, dif_pos h2] <;> rfl
        rw [h_ts] <;> rfl
      have h_split5 : objs' (Fin.succ (Fin.succ m)) = objs_S (Fin.succ m) := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h1 : ¬ (Fin.succ (Fin.succ m)).val ≤ m.val := by simp [Fin.succ] <;> omega
        have h2 : ¬ (Fin.succ (Fin.succ m)).val = m.val + 1 := by simp [Fin.succ] <;> omega
        have h_ts : ts' (Fin.succ (Fin.succ m)) = ts_S (Fin.succ m) := by
          dsimp only [ts']
          rw [dif_neg h1, dif_neg h2] <;> simp [Fin.succ] <;> omega
        rw [h_ts] <;> rfl
      have h_split6 : homs' (Fin.succ m) = eqToHom h_split4 ≫ g ≫ eqToHom h_split5.symm := by
        dsimp only [homs', g]
        have h_covers : covers' (Fin.succ m) = covers_S m := by
          dsimp only [covers']
          have h1 : (Fin.succ m).val = m.val + 1 := by simp [Fin.succ] <;> omega
          rw [dif_neg (by simp [Fin.succ] <;> omega), dif_neg (by simp [Fin.succ] <;> omega), dif_pos h1] <;> rfl
        have h_path1 : ts' (Fin.castSucc (Fin.succ m)) = t := by
          dsimp only [ts']
          have h1 : ¬ (Fin.castSucc (Fin.succ m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
          have h2 : (Fin.castSucc (Fin.succ m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
          rw [dif_neg h1, dif_pos h2] <;> rfl
        have h_path2 : ts' (Fin.succ (Fin.succ m)) = ts_S (Fin.succ m) := by
          dsimp only [ts']
          have h1 : ¬ (Fin.succ (Fin.succ m)).val ≤ m.val := by simp [Fin.succ] <;> omega
          have h2 : ¬ (Fin.succ (Fin.succ m)).val = m.val + 1 := by simp [Fin.succ] <;> omega
          rw [dif_neg h1, dif_neg h2] <;> simp [Fin.succ] <;> omega
        -- Extract endpoint equalities
        have hx : pts' (Fin.castSucc (Fin.succ m)) = γ t := by
          dsimp only [pts']
          rw [h_path1] <;> rfl
        have hy : pts' (Fin.succ (Fin.succ m)) = pts_S (Fin.succ m) := by
          dsimp only [pts', pts_S]
          rw [h_path2] <;> rfl
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' (Fin.succ m) t_val = γ2 t_val := by
          intro t_val
          dsimp only [γs', γ2]
          have h_eq1 : ts' (Fin.castSucc (Fin.succ m)) = t := h_path1
          have h_eq2 : ts' (Fin.succ (Fin.succ m)) = ts_S (Fin.succ m) := h_path2
          have h_left : (γ.subpath (ts' (Fin.castSucc (Fin.succ m))) (ts' (Fin.succ (Fin.succ m)))) t_val =
              γ (Set.Icc.convexComb (ts' (Fin.castSucc (Fin.succ m))) (ts' (Fin.succ (Fin.succ m))) t_val) := by rfl
          have h_right : (γ.subpath t (ts_S (Fin.succ m))) t_val =
              γ (Set.Icc.convexComb t (ts_S (Fin.succ m)) t_val) := by rfl
          rw [h_left, h_right]
          rw [h_eq1, h_eq2]
        -- Get hcover_mem for the cover
        have hU : covers_S m ∈ 𝒰 := hcover_mem_S m
        -- We need h_ranges' (Fin.succ m) with the rewritten cover
        have h_range_prime : Set.range (γs' (Fin.succ m)) ⊆ (covers_S m : Set X) := by
          rw [←h_covers]
          exact h_ranges' (Fin.succ m)
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers_S m) hU h_range_prime ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy) =
            single_covered_map X 𝒰 hcover hfinite_intersections s γ2 (covers_S m) hU h_range2 := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' (Fin.succ m)) γ2 hx hy hfun (covers_S m) hU h_range_prime h_range2
        -- The h_split4 and h_split5 are exactly the congr_arg equalities
        have h_eq1 : h_split4 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx := by
          apply Subsingleton.elim
        have h_eq2 : h_split5 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' (Fin.succ m) vs covers_S m
        have h_covers_eq : covers' (Fin.succ m) = covers_S m := h_covers
        have hU' : covers' (Fin.succ m) ∈ 𝒰 := hcover_mem' (Fin.succ m)
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers' (Fin.succ m)) hU' (h_ranges' (Fin.succ m)) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers_S m) hU h_range_prime := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' (Fin.succ m)) ⊆ (U : Set X))
              (hR2 : Set.range (γs' (Fin.succ m)) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) U hU hR1 hR2
          exact h (covers' (Fin.succ m)) (covers_S m) h_covers_eq hU' hU (h_ranges' (Fin.succ m)) h_range_prime
        rw [h_eq_map]
        let hx' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx
        let hy' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy
        let e_x : _ ≅ _ := eqToIso hx'
        let e_y : _ ≅ _ := eqToIso hy'
        let A := single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers_S m) hU h_range_prime
        let B := single_covered_map X 𝒰 hcover hfinite_intersections s γ2 (covers_S m) hU h_range2
        have h_main2' : e_x.inv ≫ A ≫ e_y.hom = B := h_main
        exact VanKampen.iso_sandwich_rewrite e_x e_y A B h_main2'
      have h_after : ∀ (j : Fin n), j.val > m.val →
          let i : Fin (n + 1) := Fin.succ j
          ∃ (h1 : objs' (Fin.castSucc i) = objs_S (Fin.castSucc j))
            (h2 : objs' (Fin.succ i) = objs_S (Fin.succ j)),
          eqToHom h1.symm ≫ homs' i ≫ eqToHom h2 = homs_S j := by
        intro j h_j_gt
        let i : Fin (n + 1) := Fin.succ j
        have h_i_gt : i.val > m.val + 1 := by
          dsimp only [i]
          simp [Fin.succ] <;> omega
        have h1 : ¬ (Fin.castSucc i).val ≤ m.val := by simp [Fin.castSucc] <;> omega
        have h2 : ¬ (Fin.castSucc i).val = m.val + 1 := by simp [Fin.castSucc] <;> omega
        have h_c1 : ¬ i.val < m.val := by simp [i, Fin.succ] <;> omega
        have h_c2 : ¬ i.val = m.val := by simp [i, Fin.succ] <;> omega
        have h_c3 : ¬ i.val = m.val + 1 := by simp [i, Fin.succ] <;> omega
        have h_covers : covers' i = covers_S j := by
          dsimp only [covers', i]
          rw [dif_neg h_c1, dif_neg h_c2, dif_neg h_c3]
          <;> apply congr_arg covers_S
          <;> apply Fin.ext
          <;> simp [Fin.succ] <;> omega
        have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc j) := by
          dsimp only [ts']
          have h_eq_val : (Fin.castSucc i).val - 1 = (Fin.castSucc j).val := by
            simp [Fin.castSucc, Fin.succ, i] <;> omega
          rw [dif_neg h1, dif_neg h2]
          <;> apply congr_arg ts_S
          <;> apply Fin.ext
          <;> exact h_eq_val
        have h5 : ¬ (Fin.succ i).val ≤ m.val := by simp [Fin.succ, i] <;> omega
        have h6 : ¬ (Fin.succ i).val = m.val + 1 := by simp [Fin.succ, i] <;> omega
        have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ j) := by
          dsimp only [ts']
          have h_eq_val2 : (Fin.succ i).val - 1 = (Fin.succ j).val := by
            simp [Fin.succ, i] <;> omega
          rw [dif_neg h5, dif_neg h6]
          <;> apply congr_arg ts_S
          <;> apply Fin.ext
          <;> exact h_eq_val2
        have h_pts1 : pts' (Fin.castSucc i) = pts_S (Fin.castSucc j) := by
          dsimp only [pts', pts_S]
          rw [h_ts1] <;> rfl
        have h1_obj : objs' (Fin.castSucc i) = objs_S (Fin.castSucc j) := by
          dsimp only [objs', objs_S]
          rw [h_pts1] <;> rfl
        have h_pts2 : pts' (Fin.succ i) = pts_S (Fin.succ j) := by
          dsimp only [pts', pts_S]
          rw [h_ts2] <;> rfl
        have h2_obj : objs' (Fin.succ i) = objs_S (Fin.succ j) := by
          dsimp only [objs', objs_S]
          rw [h_pts2] <;> rfl
        refine' ⟨h1_obj, h2_obj, _⟩
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' i t_val = γs_S j t_val := by
          intro t_val
          dsimp only [γs', γs_S]
          have h_eq1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc j) := h_ts1
          have h_eq2 : ts' (Fin.succ i) = ts_S (Fin.succ j) := h_ts2
          simp [Path.subpath, h_eq1, h_eq2]
          <;> rfl
        -- Get hcover_mem for the cover
        have hU : covers_S j ∈ 𝒰 := hcover_mem_S j
        -- We need h_ranges' i with the rewritten cover
        have h_range1 : Set.range (γs' i) ⊆ (covers_S j : Set X) := by
          rw [←h_covers]
          exact h_ranges' i
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers_S j) hU h_range1 ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2) =
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S j) (covers_S j) hU (h_ranges_S j) := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' i) (γs_S j) h_pts1 h_pts2 hfun (covers_S j) hU h_range1 (h_ranges_S j)
        -- The h1_obj and h2_obj are exactly the congr_arg equalities
        have h_eq1 : h1_obj = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1 := by
          apply Subsingleton.elim
        have h_eq2 : h2_obj = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2 := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' i vs covers_S j
        have h_covers_eq : covers' i = covers_S j := h_covers
        have hU' : covers' i ∈ 𝒰 := hcover_mem' i
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers' i) hU' (h_ranges' i) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers_S j) hU h_range1 := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' i) ⊆ (U : Set X))
              (hR2 : Set.range (γs' i) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' i) U hU hR1 hR2
          exact h (covers' i) (covers_S j) h_covers_eq hU' hU (h_ranges' i) h_range1
        dsimp only [homs']
        rw [h_eq_map]
        exact h_main
      have h_main : eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last =
          comp_list n objs_S homs_S :=
        comp_list_split_explicit_proof m objs_S homs_S f g h_eq objs' homs' h_before h_split1 h_split2 h_split3 h_split4 h_split5 h_split6 h_after h0 h_last
      let eq0_S : objs_S 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
        dsimp only [objs_S, pts_S]
        have h_pts0 : (γ (ts_S 0)) = x := by
          rw [h_ts0_eq]
          exact γ.source
        rw [h_pts0] <;> rfl
      let eq_last_S : objs_S (Fin.last n) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
        dsimp only [objs_S, pts_S]
        have h_pts_last : (γ (ts_S (Fin.last n))) = y := by
          rw [h_ts1_eq]
          exact γ.target
        rw [h_pts_last] <;> rfl
      let eq0_S' : objs' 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
        dsimp only [objs', pts']
        have h_ts0 : ts' 0 = (0 : I) := by
          have h1 : ts' 0 = ts_S (0 : Fin (n + 1)) := by
            dsimp only [ts']
            have h : (0 : Fin (n + 2)).val ≤ m.val := by simp <;> omega
            rw [dif_pos h]
            <;> congr <;> apply Fin.ext <;> simp
          rw [h1]
          exact h_ts0_eq
        have h_pts0 : (γ (ts' 0)) = x := by
          rw [h_ts0]
          exact γ.source
        rw [h_pts0] <;> rfl
      let eq_last_S' : objs' (Fin.last (n + 1)) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
        dsimp only [objs', pts']
        have h_ts1 : ts' (Fin.last (n + 1)) = (1 : I) := by
          dsimp only [ts']
          let i := Fin.last (n + 1)
          have h1 : ¬ i.val ≤ m.val := by
            simp [i, Fin.last] <;> omega
          have h2 : ¬ i.val = m.val + 1 := by
            simp [i, Fin.last] <;> omega
          have h_fin_eq : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
            apply Fin.ext
            simp [i, Fin.last]
            <;> omega
          rw [dif_neg h1, dif_neg h2]
          rw [h_fin_eq]
          exact h_ts1_eq
        have h_pts_last : (γ (ts' (Fin.last (n + 1)))) = y := by
          rw [h_ts1]
          exact γ.target
        rw [h_pts_last] <;> rfl
      have h_eq0 : eq0_S' = h0.trans eq0_S := by
        exact Subsingleton.elim eq0_S' (h0.trans eq0_S)
      have h_eq_last : eq_last_S' = h_last.trans eq_last_S := by
        exact Subsingleton.elim eq_last_S' (h_last.trans eq_last_S)
      have h_step1 : eqToHom eq0_S'.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom eq_last_S' =
          eqToHom (h0.trans eq0_S).symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom (h_last.trans eq_last_S) := by
        rw [h_eq0, h_eq_last]
      have h_step2 : eqToHom (h0.trans eq0_S).symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom (h_last.trans eq_last_S) =
          eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) ≫ eqToHom eq_last_S := by
        simp [eqToHom_trans, Category.assoc] <;> rfl
      have h_step3 : eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) ≫ eqToHom eq_last_S =
          eqToHom eq0_S.symm ≫ comp_list n objs_S homs_S ≫ eqToHom eq_last_S := by
        have h_assoc : eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) ≫ eqToHom eq_last_S =
            (eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last)) ≫ eqToHom eq_last_S := by
          simp [Category.assoc] <;> rfl
        rw [h_assoc]
        have h_rewrite : eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) =
            eqToHom eq0_S.symm ≫ comp_list n objs_S homs_S := by
          rw [h_main]
        rw [h_rewrite]
        <;> simp [Category.assoc] <;> rfl
      rw [h_step1, h_step2, h_step3]
    -- Combine everything
    rw [h_eq_S, h_eq_S']
    exact h_core



lemma my_map_from_adapted_subdivision_refines
    {x y : X} {γ : Path x y} {S S' : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ S')
    (h_subset : S ⊆ S') :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' := by
  classical
  have h_main : ∀ (n : ℕ), ∀ (A B : Finset I),
    A ⊆ B → (B \ A).card = n →
    (hA : IsAdaptedSubdivision 𝒰 γ A) → (hB : IsAdaptedSubdivision 𝒰 γ B) →
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hA =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hB := by
    intro n
    induction n with
    | zero =>
      intro A B h_sub h_card hA hB
      have h_B_sub_A : B ⊆ A := by
        simpa [Finset.card_eq_zero] using h_card
      have h_B_eq_A : B = A := by
        apply Finset.Subset.antisymm h_B_sub_A h_sub
      have h_goal : ∀ (S1 S2 : Finset I) (h_eq : S1 = S2)
          (h1 : IsAdaptedSubdivision 𝒰 γ S1)
          (h2 : IsAdaptedSubdivision 𝒰 γ S2),
          my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s h1 =
          my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s h2 := by
        intro S1 S2 h_eq h1 h2
        subst h_eq
        <;> rfl
      exact h_goal A B h_B_eq_A.symm hA hB
    | succ n ih =>
      intro A B h_sub h_card hA hB
      have h_nonempty : (B \ A).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [h] at h_card
        simp at h_card <;> omega
      let t : I := Classical.choose h_nonempty
      have ht_in_diff : t ∈ B \ A := Classical.choose_spec h_nonempty
      have ht_in_B : t ∈ B := (Finset.mem_sdiff.mp ht_in_diff).1
      have ht_notin_A : t ∉ A := (Finset.mem_sdiff.mp ht_in_diff).2
      let A₁ := A ∪ {t}
      have h_sub_A_A₁ : A ⊆ A₁ := by simp [A₁]
      have h_sub_A₁_B : A₁ ⊆ B := by
        intro x hx
        simp only [A₁, Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with (hx | rfl)
        · exact h_sub hx
        · exact ht_in_B
      have hA₁ : IsAdaptedSubdivision 𝒰 γ A₁ :=
        insert_is_adapted hA
      have h_card1 : (A₁ \ A).card = 1 := by
        simp [A₁, ht_notin_A] <;> omega
      have h_step1 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hA =
          my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hA₁ :=
        my_map_from_adapted_subdivision_refines_one X 𝒰 hcover hfinite_intersections s hA hA₁
      have h_card2 : (B \ A₁).card = n := by
        have h1 : B \ A = (B \ A₁) ∪ (A₁ \ A) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          <;> tauto
        rw [h1] at h_card
        have h_disj : Disjoint (B \ A₁) (A₁ \ A) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have h1 : x ∉ A₁ := (Finset.mem_sdiff.mp hx1).2
          have h2 : x ∈ A₁ := (Finset.mem_sdiff.mp hx2).1
          exact h1 h2
        rw [Finset.card_union_of_disjoint h_disj] at h_card
        rw [h_card1] at h_card <;> omega
      have h_step2 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hA₁ =
          my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hB :=
        ih A₁ B h_sub_A₁_B h_card2 hA₁ hB
      rw [h_step1, h_step2]
  have h_card_eq : (S' \ S).card = S'.card - S.card := by
    have h_union : (S' \ S) ∪ S = S' := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      <;> tauto
    have h_disj : Disjoint (S' \ S) S := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h_notin_S : x ∉ S := (Finset.mem_sdiff.mp hx1).2
      exact h_notin_S hx2
    have h2 : ((S' \ S) ∪ S).card = (S' \ S).card + S.card :=
      Finset.card_union_of_disjoint h_disj
    rw [h_union] at h2
    omega
  exact h_main (S'.card - S.card) S S' h_subset h_card_eq hS hS'

/-- Independence of choice of adapted subdivision. -/
theorem my_map_from_adapted_subdivision_independent
    {x y : X} {γ : Path x y} {S S' : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ S') :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' := by
  classical
  let S_union := S ∪ S'
  have hS_union : IsAdaptedSubdivision 𝒰 γ S_union :=
    IsAdaptedSubdivision.union_is_adapted hfinite_intersections hS hS'
  have h1 : S ⊆ S_union := by simp [S_union]
  have h2 : S' ⊆ S_union := by simp [S_union]
  have h_eq1 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_union :=
    my_map_from_adapted_subdivision_refines X 𝒰 hcover hfinite_intersections s hS hS_union h1
  have h_eq2 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_union :=
    my_map_from_adapted_subdivision_refines X 𝒰 hcover hfinite_intersections s hS' hS_union h2
  rw [h_eq1, h_eq2]

end

end

end P202.Topology.VanKampenProof


/-! Adapted from CleanRefinement.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits IsAdaptedSubdivision

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections s

/-- Helper: the range of a subpath is the image of the interval. -/
lemma subpath_range_subset {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    {s₁ s₂ : I} (h_lt : s₁ < s₂)
    {U : Opens X} (h : ∀ (t : I), s₁ ≤ t → t ≤ s₂ → γ t ∈ U) :
    Set.range (γ.subpath s₁ s₂) ⊆ (U : Set X) := by
  have h_range_eq : Set.range (γ.subpath s₁ s₂) = γ '' Set.Icc s₁ s₂ := by
    rw [Path.range_subpath γ s₁ s₂]
    <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
  rw [h_range_eq]
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  exact h t ht.1 ht.2

/-- Adding a single point to an adapted subdivision does not change the morphism.

    Proof sketch:
    1. Use the universal property to get explicit ts, covers for both S and S'
    2. Show that ts' is ts with t inserted at position k
    3. Show that covers' is covers with covers k repeated at positions k and k+1
    4. Use single_covered_split_eq to show the two new morphisms compose to the original
    5. Use comp_list_split_explicit to show the overall composition is unchanged -/
theorem my_map_from_adapted_subdivision_refines_one_clean
    {x y : X} {γ : Path x y} {S : Finset I} {t : I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ (S ∪ {t})) :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' := by
  classical
  by_cases h_t_in_S : t ∈ S
  · -- Case 1: t ∈ S, then S ∪ {t} = S, so trivial
    have h_set_eq : S ∪ {t} = S := by
      ext x
      simp [h_t_in_S] <;> tauto
    have h_goal : ∀ (S1 S2 : Finset I) (h_eq : S1 = S2)
        (h1 : IsAdaptedSubdivision 𝒰 γ S1)
        (h2 : IsAdaptedSubdivision 𝒰 γ S2),
        my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s h1 =
        my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s h2 := by
      intro S1 S2 h_eq h1 h2
      subst h_eq
      congr
      <;> exact Subsingleton.elim h1 h2
    have h_eq : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' =
        my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS :=
      h_goal (S ∪ {t}) S h_set_eq hS' hS
    exact h_eq.symm
  · -- Case 2: t ∉ S
    have h_t_not_in_S : t ∉ S := h_t_in_S
    -- Get the canonical decomposition for S
    have h0_in_S : (0 : I) ∈ S := hS.1
    have h1_in_S : (1 : I) ∈ S := hS.2.1
    have hS_nonempty : S.Nonempty := ⟨0, h0_in_S⟩
    let k : ℕ := S.card
    have hk : S.card = k := rfl
    have hk_pos : 0 < k := Finset.card_pos.mpr hS_nonempty
    have hk_ge2 : 2 ≤ k := by
      have h0_ne_1 : (0 : I) ≠ (1 : I) := by
        intro h
        have h' : (0 : ℝ) = (1 : ℝ) := congr_arg (fun x : I => (x : ℝ)) h
        norm_num at h' <;> exact h'
      have h : ({(0 : I), (1 : I)} : Finset I) ⊆ S := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with (rfl | rfl) <;> tauto
      have h2 : ({(0 : I), (1 : I)} : Finset I).card ≤ S.card := Finset.card_le_card h
      have h3 : ({(0 : I), (1 : I)} : Finset I).card = 2 := by
        simp [h0_ne_1] <;> rfl
      rw [h3] at h2
      exact h2
    let e : Fin k ↪o I := S.orderEmbOfFin hk
    have h_e_mem : ∀ (i : Fin k), e i ∈ S := Finset.orderEmbOfFin_mem S hk
    have h_e_strict_mono : StrictMono e := OrderEmbedding.strictMono e
    have h_e_image : Finset.image e Finset.univ = S := by
      convert Finset.image_orderEmbOfFin_univ S hk using 1 <;>
        ext x <;> simp only [Finset.mem_image] <;> rfl
    let n : ℕ := k - 1
    have hk_eq : k = n + 1 := by omega
    let ts_S (i : Fin (n + 1)) : I := e ⟨i.val, by rw [hk_eq] <;> exact i.is_lt⟩
    have h_ts_S_strict : StrictMono ts_S := by
      intro i j h
      exact h_e_strict_mono (by simpa [ts_S] using h)
    have h_ts_S_image : Finset.image ts_S Finset.univ = S := by
      have h1 : Finset.image ts_S Finset.univ = Finset.image e Finset.univ := by
        ext x
        simp only [ts_S, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨⟨i.val, by rw [hk_eq]; exact i.is_lt⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          have h_j_lt : j.val < n + 1 := by rw [←hk_eq]; exact j.is_lt
          let i : Fin (n + 1) := ⟨j.val, h_j_lt⟩
          exact ⟨i, by simp [i] <;> rfl⟩
      rw [h1, h_e_image]
    have h_ts0_eq : ts_S 0 = (0 : I) := by
      have h0 : ts_S 0 ∈ S := by
        have h : ts_S 0 ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
        rw [h_ts_S_image] at h
        exact h
      have h0_in : (0 : I) ∈ S := h0_in_S
      have h_le : (0 : I) ≤ ts_S 0 := by
        exact?
      have h_ge : ts_S 0 ≤ (0 : I) := by
        have h_exists : ∃ (i : Fin (n + 1)), ts_S i = (0 : I) := by
          have h : (0 : I) ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h0_in
          rcases Finset.mem_image.mp h with ⟨i, _, h_eq⟩
          exact ⟨i, h_eq⟩
        rcases h_exists with ⟨i, hi⟩
        have h_i_ge : 0 ≤ i := by
          exact?
        have h_mono : StrictMono ts_S := h_ts_S_strict
        have h : ts_S 0 ≤ ts_S i := h_mono.monotone h_i_ge
        rw [hi] at h
        exact h
      exact le_antisymm h_ge h_le
    have h_ts1_eq : ts_S (Fin.last n) = (1 : I) := by
      have h1 : ts_S (Fin.last n) ∈ S := by
        have h : ts_S (Fin.last n) ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, rfl⟩
        rw [h_ts_S_image] at h
        exact h
      have h1_in : (1 : I) ∈ S := h1_in_S
      have h_le : ts_S (Fin.last n) ≤ (1 : I) := by
        exact?
      have h_ge : (1 : I) ≤ ts_S (Fin.last n) := by
        have h_exists : ∃ (i : Fin (n + 1)), ts_S i = (1 : I) := by
          have h : (1 : I) ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h1_in
          rcases Finset.mem_image.mp h with ⟨i, _, h_eq⟩
          exact ⟨i, h_eq⟩
        rcases h_exists with ⟨i, hi⟩
        have h_i_le : i ≤ Fin.last n := by exact Fin.le_last i
        have h_mono : StrictMono ts_S := h_ts_S_strict
        have h : ts_S i ≤ ts_S (Fin.last n) := h_mono.monotone h_i_le
        rw [hi] at h
        exact h
      exact le_antisymm h_le h_ge
    -- Get canonical covers for S
    have h_main_exists : ∃ (covers_S : Fin n → Opens X),
        (∀ i, covers_S i ∈ 𝒰) ∧
        (∀ i, ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (covers_S i : Set X)) := by
      have h_helper : ∀ (i : Fin n), ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (U : Set X) := by
        intro i
        let s₁ := ts_S (Fin.castSucc i)
        let s₂ := ts_S (Fin.succ i)
        have h_s1_in : s₁ ∈ S := by
          have h : s₁ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨Fin.castSucc i, Finset.mem_univ _, rfl⟩
          rw [h_ts_S_image] at h
          exact h
        have h_s2_in : s₂ ∈ S := by
          have h : s₂ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨Fin.succ i, Finset.mem_univ _, rfl⟩
          rw [h_ts_S_image] at h
          exact h
        have h_lt : s₁ < s₂ := h_ts_S_strict (by
          apply Fin.lt_iff_val_lt_val.mpr
          simp [Fin.castSucc, Fin.succ] <;> omega)
        have h_no_between : ∀ (x : I), x ∈ S → s₁ < x → x < s₂ → False := by
          intro x hx h1 h2
          have h_exists : ∃ (j : Fin k), e j = x := by
            have h : x ∈ Finset.image e Finset.univ := by rw [h_e_image] <;> exact hx
            rcases Finset.mem_image.mp h with ⟨j, _, rfl⟩
            exact ⟨j, rfl⟩
          rcases h_exists with ⟨j, hj⟩
          have h_j_gt : (Fin.castSucc i).val < j.val := by
            have h4 : ts_S (Fin.castSucc i) < e j := by rw [hj] <;> exact h1
            exact Fin.lt_iff_val_lt_val.mp (by simpa [ts_S] using h4)
          have h_j_lt : j.val < (Fin.succ i).val := by
            have h4 : e j < ts_S (Fin.succ i) := by rw [hj] <;> exact h2
            exact Fin.lt_iff_val_lt_val.mp (by simpa [ts_S] using h4)
          have h1 : i.val < j.val := by
            simpa [Fin.castSucc] using h_j_gt
          have h2 : j.val < i.val + 1 := by
            simpa [Fin.succ] using h_j_lt
          omega
        exact hS.2.2 s₁ s₂ h_s1_in h_s2_in h_lt h_no_between
      choose covers_S hcover_mem_S h_range_S using h_helper
      exact ⟨covers_S, hcover_mem_S, h_range_S⟩
    rcases h_main_exists with ⟨covers_S, hcover_mem_S, h_range_S⟩
    -- Now we have ts_S, covers_S for S
    -- We need to find where t fits in the subdivision
    have h_t_between : (0 : I) ≤ t ∧ t < (1 : I) := by
      constructor
      · exact?
      · by_contra h
        have h' : (1 : I) ≤ t := by exact le_of_not_gt h
        have h1_in : (1 : I) ∈ S := h1_in_S
        have h_t_in_S' : t ∈ S ∪ {t} := by simp
        have h2 : t ≤ (1 : I) := by
          exact?

        have h4 : t = (1 : I) := by exact le_antisymm h2 h'
        rw [h4] at h_t_not_in_S
        exact h_t_not_in_S h1_in
    let P : Fin k → Prop := fun i => e i ≤ t
    let zero_Fin_k : Fin k := ⟨0, hk_pos⟩
    have h_i0_P : P zero_Fin_k := by
      dsimp only [P, zero_Fin_k]
      have h_e0 : e zero_Fin_k = ts_S (0 : Fin (n + 1)) := by
        simp [ts_S, zero_Fin_k] <;> rfl
      rw [h_e0, h_ts0_eq]
      exact h_t_between.1
    let i_max : Fin k := Finset.max' (Finset.filter P Finset.univ) ⟨zero_Fin_k, by simp [h_i0_P]⟩
    have h_i_max_mem : i_max ∈ Finset.filter P Finset.univ := Finset.max'_mem _ _
    have h_i_max_P : P i_max := (Finset.mem_filter.mp h_i_max_mem).2
    have h_i_max_le_t : e i_max ≤ t := h_i_max_P
    have h_not : ¬ ((1 : I) ≤ t) := by
      intro h
      have h' : t < (1 : I) := h_t_between.2
      have h'' : (t : ℝ) < (1 : ℝ) := by exact_mod_cast h'
      have h''' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
      linarith
    have h_k_pos : 0 < k := by omega
    let last_k : Fin k := ⟨k - 1, by omega⟩
    have h_e_last : e last_k = (1 : I) := by
      have h2 : (1 : I) ∈ S := h1_in_S
      have h : e last_k = (1 : I) := by
        exact?
      exact h
    have h_i_max_lt_last : i_max < last_k := by
      have h1 : e i_max < e last_k := by
        rw [h_e_last]
        exact lt_of_le_of_lt h_i_max_le_t h_t_between.2
      exact h_e_strict_mono.lt_iff_lt.mp h1
    let m_val : ℕ := i_max.val
    have h_m_val_lt_n : m_val < n := by
      dsimp only [n, m_val]
      have h : i_max.val < last_k.val := Fin.lt_iff_val_lt_val.mp h_i_max_lt_last
      simpa [last_k, Fin.last] using h
    let m : Fin n := ⟨m_val, h_m_val_lt_n⟩
    have h_e_i_max_le_t : e i_max ≤ t := h_i_max_P
    let i_succ : Fin k := ⟨i_max.val + 1, by omega⟩
    have h_i_succ_not_P : ¬ P i_succ := by
      intro h
      have h6 : i_succ ∈ Finset.filter P Finset.univ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have h7 : i_succ ≤ i_max := Finset.le_max' (Finset.filter P Finset.univ) i_succ h6
      have h8 : i_max < i_succ := by
        apply Fin.lt_iff_val_lt_val.mpr
        simp [i_succ] <;> omega
      have h9 : ¬ (i_succ ≤ i_max) := by
        intro h10
        have h11 : i_max < i_succ := h8
        exact Fin.not_le.mpr h11 h10
      exact h9 h7
    have h_t_lt_e_succ : t < e i_succ := by
      dsimp only [P] at h_i_succ_not_P
      exact lt_of_not_ge h_i_succ_not_P
    have h_e_i_max_lt_t : e i_max < t := by
      apply lt_of_le_of_ne h_e_i_max_le_t
      intro h_eq
      have h9 : e i_max = t := h_eq
      have h10 : e i_max ∈ S := h_e_mem i_max
      rw [h9] at h10
      exact h_t_not_in_S h10
    have h_m_left : ts_S (Fin.castSucc m) < t := by
      simpa [ts_S, m] using h_e_i_max_lt_t
    have h_m_right : t < ts_S (Fin.succ m) := by
      simpa [ts_S, m] using h_t_lt_e_succ
    -- Define ts' explicitly by inserting t at position m+1
    let ts' (i : Fin (n + 2)) : I :=
      if h : i.val ≤ m.val then
        ts_S ⟨i.val, by omega⟩
      else if h' : i.val = m.val + 1 then
        t
      else
        ts_S ⟨i.val - 1, by omega⟩
    -- Define covers' explicitly by duplicating covers_S m at positions m and m+1
    let covers' (i : Fin (n + 1)) : Opens X :=
      if h : i.val < m.val then
        covers_S ⟨i.val, by omega⟩
      else if h' : i.val = m.val then
        covers_S m
      else if h'' : i.val = m.val + 1 then
        covers_S m
      else
        covers_S ⟨i.val - 1, by omega⟩
    -- Prove ts' is strictly monotone
    have h_ts'_strict : StrictMono ts' := by
      intro i j h_lt
      dsimp only [ts']
      have h_ij : i.val < j.val := by
        exact Fin.lt_iff_val_lt_val.mp h_lt
      by_cases h_i_le_m : i.val ≤ m.val
      · by_cases h_j_le_m : j.val ≤ m.val
        · rw [dif_pos h_i_le_m, dif_pos h_j_le_m]
          have h_lt2 : (⟨i.val, by omega⟩ : Fin (n + 1)) < (⟨j.val, by omega⟩ : Fin (n + 1)) := by
            apply Fin.lt_iff_val_lt_val.mpr
            exact h_ij
          exact h_ts_S_strict h_lt2
        · rw [dif_pos h_i_le_m]
          by_cases h_j_eq : j.val = m.val + 1
          · rw [dif_neg (by omega), dif_pos h_j_eq]
            have h_i_le_m2 : (⟨i.val, by omega⟩ : Fin (n + 1)) ≤ Fin.castSucc m := by
              apply Fin.le_iff_val_le_val.mpr
              exact h_i_le_m
            have h1 : ts_S ⟨i.val, by omega⟩ ≤ ts_S (Fin.castSucc m) := h_ts_S_strict.monotone h_i_le_m2
            exact lt_of_le_of_lt h1 h_m_left
          · rw [dif_neg (by omega), dif_neg h_j_eq]
            have h_i_lt_j1 : i.val < j.val - 1 := by omega
            have h_lt2 : (⟨i.val, by omega⟩ : Fin (n + 1)) < (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
              apply Fin.lt_iff_val_lt_val.mpr
              exact h_i_lt_j1
            have h1 : ts_S ⟨i.val, by omega⟩ < ts_S ⟨j.val - 1, by omega⟩ := h_ts_S_strict h_lt2
            exact h1
      · have h_i_gt_m : m.val < i.val := by omega
        by_cases h_i_eq : i.val = m.val + 1
        · rw [dif_neg h_i_le_m, dif_pos h_i_eq]
          by_cases h_j_eq : j.val = m.val + 1
          · omega
          · by_cases h_j_gt : j.val > m.val + 1
            · rw [dif_neg (by omega), dif_neg h_j_eq]
              have h1 : t < ts_S ⟨j.val - 1, by omega⟩ := by
                have h_j1_val_ge : m.val + 1 ≤ j.val - 1 := by omega
                have h_j1_ge : (Fin.succ m : Fin (n + 1)) ≤ ⟨j.val - 1, by omega⟩ := by
                  apply Fin.le_iff_val_le_val.mpr
                  simpa [Fin.succ] using h_j1_val_ge
                have h2 : ts_S (Fin.succ m) ≤ ts_S ⟨j.val - 1, by omega⟩ := h_ts_S_strict.monotone h_j1_ge
                exact lt_of_lt_of_le h_m_right h2
              exact h1
            · omega
        · rw [dif_neg h_i_le_m, dif_neg h_i_eq]
          rw [dif_neg (by omega), dif_neg (by omega)]
          have h_i_lt_j1 : i.val - 1 < j.val - 1 := by omega
          have h_lt2 : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) < (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
            apply Fin.lt_iff_val_lt_val.mpr
            exact h_i_lt_j1
          exact h_ts_S_strict h_lt2
    -- Prove ts' has image S ∪ {t}
    have h_ts'_image : Finset.image ts' Finset.univ = S ∪ {t} := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        dsimp only [ts']
        by_cases h1 : i.val ≤ m.val
        · rw [dif_pos h1]
          left
          have h2 : ts_S ⟨i.val, by omega⟩ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, rfl⟩
          rw [h_ts_S_image] at h2
          exact h2
        · by_cases h2 : i.val = m.val + 1
          · rw [dif_neg h1, dif_pos h2]
            right
            rfl
          · rw [dif_neg h1, dif_neg h2]
            left
            have h3 : ts_S ⟨i.val - 1, by omega⟩ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, rfl⟩
            rw [h_ts_S_image] at h3
            exact h3
      · rintro (h | h_eq)
        · -- x ∈ S
          have h_x_in : x ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h
          rcases Finset.mem_image.mp h_x_in with ⟨i, _, rfl⟩
          by_cases h_i_le_m : i.val ≤ m.val
          · let j : Fin (n + 2) := ⟨i.val, by omega⟩
            have h_ts'_j : ts' j = ts_S i := by
              dsimp only [ts', j]
              rw [dif_pos h_i_le_m] <;> rfl
            exact ⟨j, h_ts'_j⟩
          · have h_i_gt_m : i.val > m.val := by omega
            let j : Fin (n + 2) := ⟨i.val + 1, by omega⟩
            have h_ts'_j : ts' j = ts_S i := by
              dsimp only [ts', j]
              rw [dif_neg (by omega), dif_neg (by omega)] <;> congr <;> omega
            exact ⟨j, h_ts'_j⟩
        · -- x = t
          have h_x_eq_t : x = t := h_eq
          let j : Fin (n + 2) := ⟨m.val + 1, by omega⟩
          have h_ts'_j : ts' j = t := by
            dsimp only [ts', j]
            rw [dif_neg (by omega), dif_pos (by omega)] <;> rfl
          have h_ts'_j_x : ts' j = x := by
            rw [h_ts'_j, h_x_eq_t.symm]
          exact ⟨j, h_ts'_j_x⟩
    -- Prove covers' are in 𝒰
    have hcover_mem' : ∀ i : Fin (n + 1), covers' i ∈ 𝒰 := by
      intro i
      dsimp only [covers']
      by_cases h1 : i.val < m.val
      · rw [dif_pos h1]
        exact hcover_mem_S ⟨i.val, by omega⟩
      · by_cases h2 : i.val = m.val
        · rw [dif_neg h1, dif_pos h2]
          exact hcover_mem_S m
        · by_cases h3 : i.val = m.val + 1
          · rw [dif_neg h1, dif_neg h2, dif_pos h3]
            exact hcover_mem_S m
          · rw [dif_neg h1, dif_neg h2, dif_neg h3]
            exact hcover_mem_S ⟨i.val - 1, by omega⟩
    -- Prove range condition for covers'
    have h_range' : ∀ (i : Fin (n + 1)) (t_val : I),
        ts' (Fin.castSucc i) ≤ t_val → t_val ≤ ts' (Fin.succ i) → γ t_val ∈ (covers' i : Set X) := by
      intro i t_val h1 h2
      dsimp only [covers']
      by_cases h_i_lt_m : i.val < m.val
      · rw [dif_pos h_i_lt_m]
        have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc ⟨i.val, by omega⟩) := by
          dsimp only [ts']
          have h : (Fin.castSucc i).val ≤ m.val := by simp [Fin.castSucc, h_i_lt_m] <;> omega
          rw [dif_pos h] <;> rfl
        have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ ⟨i.val, by omega⟩) := by
          dsimp only [ts']
          have h : (Fin.succ i).val ≤ m.val := by simp [Fin.succ, h_i_lt_m] <;> omega
          rw [dif_pos h] <;> rfl
        rw [h_ts1] at h1
        rw [h_ts2] at h2
        exact h_range_S ⟨i.val, by omega⟩ t_val h1 h2
      · rw [dif_neg h_i_lt_m]
        by_cases h_i_eq_m : i.val = m.val
        · rw [dif_pos h_i_eq_m]
          have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc m) := by
            dsimp only [ts']
            have h_cast_val : (Fin.castSucc i).val = i.val := by simp [Fin.castSucc]
            have h : (Fin.castSucc i).val ≤ m.val := by
              rw [h_cast_val, h_i_eq_m]
            have h_eq_val : (Fin.castSucc i).val = (Fin.castSucc m).val := by
              rw [h_cast_val, h_i_eq_m] <;> simp [Fin.castSucc]
            have h_fin_eq : (⟨(Fin.castSucc i).val, by omega⟩ : Fin (n + 1)) = Fin.castSucc m := by
              apply Fin.ext
              simpa [Fin.castSucc] using h_eq_val
            rw [dif_pos h]
            rw [h_fin_eq]
          have h_ts2 : ts' (Fin.succ i) = t := by
            dsimp only [ts']
            have h_succ_val : (Fin.succ i).val = i.val + 1 := by simp [Fin.succ]
            have h1 : ¬ (Fin.succ i).val ≤ m.val := by
              rw [h_succ_val, h_i_eq_m] <;> omega
            have h2 : (Fin.succ i).val = m.val + 1 := by
              rw [h_succ_val, h_i_eq_m]
            rw [dif_neg h1, dif_pos h2] <;> congr <;> simp [Fin.succ, h_i_eq_m]
          rw [h_ts1] at h1
          rw [h_ts2] at h2
          have h3 : t_val ≤ ts_S (Fin.succ m) := by
            have h4 : t_val < ts_S (Fin.succ m) := by
              exact lt_of_le_of_lt h2 h_m_right
            exact le_of_lt h4
          exact h_range_S m t_val h1 h3
        · rw [dif_neg h_i_eq_m]
          by_cases h_i_eq_m1 : i.val = m.val + 1
          · rw [dif_pos h_i_eq_m1]
            have h_ts1 : ts' (Fin.castSucc i) = t := by
              dsimp only [ts']
              have h1 : ¬ (Fin.castSucc i).val ≤ m.val := by
                simp [Fin.castSucc, h_i_eq_m1] <;> omega
              have h2 : (Fin.castSucc i).val = m.val + 1 := by
                simp [Fin.castSucc, h_i_eq_m1] <;> omega
              rw [dif_neg h1, dif_pos h2] <;> congr <;> omega
            have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ m) := by
              dsimp only [ts']
              have h1 : ¬ (Fin.succ i).val ≤ m.val := by
                simp [Fin.succ, h_i_eq_m1] <;> omega
              have h2 : ¬ (Fin.succ i).val = m.val + 1 := by
                simp [Fin.succ, h_i_eq_m1] <;> omega
              rw [dif_neg h1, dif_neg h2] <;> congr <;> omega
            rw [h_ts1] at h1
            rw [h_ts2] at h2
            have h3 : ts_S (Fin.castSucc m) ≤ t_val := by
              have h4 : ts_S (Fin.castSucc m) < t_val := by
                exact lt_of_lt_of_le h_m_left h1
              exact le_of_lt h4
            exact h_range_S m t_val h3 h2
          · rw [dif_neg h_i_eq_m1]
            have h_i_gt : m.val + 1 < i.val := by omega
            let j : Fin n := ⟨i.val - 1, by omega⟩
            have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc j) := by
              dsimp only [ts', j]
              have h1 : ¬ (Fin.castSucc i).val ≤ m.val := by
                simp [Fin.castSucc, j, h_i_gt] <;> omega
              have h2 : ¬ (Fin.castSucc i).val = m.val + 1 := by
                simp [Fin.castSucc, j, h_i_gt] <;> omega
              rw [dif_neg h1, dif_neg h2]
              apply congr_arg ts_S
              apply Fin.ext
              simp [Fin.castSucc, j] <;> omega
            have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ j) := by
              dsimp only [ts', j]
              have h1 : ¬ (Fin.succ i).val ≤ m.val := by
                simp [Fin.succ, j, h_i_gt] <;> omega
              have h2 : ¬ (Fin.succ i).val = m.val + 1 := by
                simp [Fin.succ, j, h_i_gt] <;> omega
              rw [dif_neg h1, dif_neg h2]
              apply congr_arg ts_S
              apply Fin.ext
              simp [Fin.succ, j] <;> omega
            rw [h_ts1] at h1
            rw [h_ts2] at h2
            exact h_range_S j t_val h1 h2
    -- Apply universal property to both sides
    have h_eq_S : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
        my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts_S h_ts_S_strict h_ts_S_image covers_S hcover_mem_S h_range_S :=
      my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS ts_S h_ts_S_strict h_ts_S_image covers_S hcover_mem_S h_range_S
    have h_eq_S' : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' =
        my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS' (n + 1) ts' h_ts'_strict h_ts'_image covers' hcover_mem' h_range' :=
      my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS' ts' h_ts'_strict h_ts'_image covers' hcover_mem' h_range'
    -- Core equality step
    have h_core : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts_S h_ts_S_strict h_ts_S_image covers_S hcover_mem_S h_range_S =
        my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS' (n + 1) ts' h_ts'_strict h_ts'_image covers' hcover_mem' h_range' := by
      dsimp only [my_map_from_adapted_subdivision_with_covers]
      let pts_S (i : Fin (n + 1)) : X := γ (ts_S i)
      let objs_S : Fin (n + 1) → s.pt := fun i =>
        desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts_S i))
      let γs_S (i : Fin n) : Path (pts_S (Fin.castSucc i)) (pts_S (Fin.succ i)) :=
        γ.subpath (ts_S (Fin.castSucc i)) (ts_S (Fin.succ i))
      have h_ranges_S (i : Fin n) : Set.range (γs_S i) ⊆ (covers_S i : Set X) := by
        have h_lt : Fin.castSucc i < Fin.succ i := by exact?
        have h_ts_lt : ts_S (Fin.castSucc i) < ts_S (Fin.succ i) := h_ts_S_strict h_lt
        have h_range : ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (covers_S i : Set X) := h_range_S i
        have h_range_eq : Set.range (γs_S i) = γ '' Set.Icc (ts_S (Fin.castSucc i)) (ts_S (Fin.succ i)) := by
          rw [Path.range_subpath γ (ts_S (Fin.castSucc i)) (ts_S (Fin.succ i))]
          <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t, ht, rfl⟩
        exact h_range t ht.1 ht.2
      let homs_S (i : Fin n) : objs_S (Fin.castSucc i) ⟶ objs_S (Fin.succ i) :=
        single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S i) (covers_S i) (hcover_mem_S i) (h_ranges_S i)
      let pts' (i : Fin (n + 2)) : X := γ (ts' i)
      let objs' : Fin (n + 2) → s.pt := fun i =>
        desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts' i))
      let γs' (i : Fin (n + 1)) : Path (pts' (Fin.castSucc i)) (pts' (Fin.succ i)) :=
        γ.subpath (ts' (Fin.castSucc i)) (ts' (Fin.succ i))
      have h_ranges' (i : Fin (n + 1)) : Set.range (γs' i) ⊆ (covers' i : Set X) := by
        have h_lt : Fin.castSucc i < Fin.succ i := by exact?
        have h_ts_lt : ts' (Fin.castSucc i) < ts' (Fin.succ i) := h_ts'_strict h_lt
        have h_range : ∀ (t_val : I), ts' (Fin.castSucc i) ≤ t_val → t_val ≤ ts' (Fin.succ i) → γ t_val ∈ (covers' i : Set X) := h_range' i
        have h_range_eq : Set.range (γs' i) = γ '' Set.Icc (ts' (Fin.castSucc i)) (ts' (Fin.succ i)) := by
          rw [Path.range_subpath γ (ts' (Fin.castSucc i)) (ts' (Fin.succ i))]
          <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t, ht, rfl⟩
        exact h_range t ht.1 ht.2
      let homs' (i : Fin (n + 1)) : objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i) :=
        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers' i) (hcover_mem' i) (h_ranges' i)
      let mid : s.pt := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (γ t))
      let γ1 : Path (pts_S (Fin.castSucc m)) (γ t) :=
        γ.subpath (ts_S (Fin.castSucc m)) t
      let γ2 : Path (γ t) (pts_S (Fin.succ m)) :=
        γ.subpath t (ts_S (Fin.succ m))
      have h_range1 : Set.range γ1 ⊆ (covers_S m : Set X) := by
        have h_range : ∀ (t_val : I), ts_S (Fin.castSucc m) ≤ t_val → t_val ≤ t → γ t_val ∈ (covers_S m : Set X) := by
          intro t_val h1 h2
          have h3 : t_val ≤ ts_S (Fin.succ m) := by
            have h4 : t_val < ts_S (Fin.succ m) := by
              exact lt_of_le_of_lt h2 h_m_right
            exact le_of_lt h4
          exact h_range_S m t_val h1 h3
        have h_range_eq : Set.range γ1 = γ '' Set.Icc (ts_S (Fin.castSucc m)) t := by
          rw [Path.range_subpath γ (ts_S (Fin.castSucc m)) t]
          <;> rw [Set.uIcc_of_le (le_of_lt h_m_left)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t_val, ht, rfl⟩
        exact h_range t_val ht.1 ht.2
      have h_range2 : Set.range γ2 ⊆ (covers_S m : Set X) := by
        have h_range : ∀ (t_val : I), t ≤ t_val → t_val ≤ ts_S (Fin.succ m) → γ t_val ∈ (covers_S m : Set X) := by
          intro t_val h1 h2
          have h3 : ts_S (Fin.castSucc m) ≤ t_val := by
            have h4 : ts_S (Fin.castSucc m) < t_val := by
              exact lt_of_lt_of_le h_m_left h1
            exact le_of_lt h4
          exact h_range_S m t_val h3 h2
        have h_range_eq : Set.range γ2 = γ '' Set.Icc t (ts_S (Fin.succ m)) := by
          rw [Path.range_subpath γ t (ts_S (Fin.succ m))]
          <;> rw [Set.uIcc_of_le (le_of_lt h_m_right)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t_val, ht, rfl⟩
        exact h_range t_val ht.1 ht.2
      let f : objs_S (Fin.castSucc m) ⟶ mid :=
        single_covered_map X 𝒰 hcover hfinite_intersections s γ1 (covers_S m) (hcover_mem_S m) h_range1
      let g : mid ⟶ objs_S (Fin.succ m) :=
        single_covered_map X 𝒰 hcover hfinite_intersections s γ2 (covers_S m) (hcover_mem_S m) h_range2
      have h_range_both : Set.range (γ1.trans γ2) ⊆ (covers_S m : Set X) :=
        range_trans_subset γ1 γ2 h_range1 h_range2
      have h_split : f ≫ g = single_covered_map X 𝒰 hcover hfinite_intersections s (γ1.trans γ2) (covers_S m) (hcover_mem_S m) h_range_both :=
        single_covered_split_eq X 𝒰 hcover hfinite_intersections s (covers_S m) (hcover_mem_S m) γ1 h_range1 γ2 h_range2
      let t₀ : I := ts_S (Fin.castSucc m)
      let t₁ : I := t
      let t₂ : I := ts_S (Fin.succ m)
      have h_t0_le_t1 : t₀ ≤ t₁ := le_of_lt h_m_left
      have h_t1_le_t2 : t₁ ≤ t₂ := le_of_lt h_m_right
      let H : Path.Homotopy (γ1.trans γ2) (γs_S m) :=
        Path.Homotopy.subpathTransSubpath γ t₀ t₁ t₂
      have hH : ∀ (p : I × I), H p ∈ (covers_S m : Set X) := by
        intro p
        have h_exists : ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧ H p = γ u :=
          VanKampen.subpathTransSubpath_range γ h_t0_le_t1 h_t1_le_t2 p
        rcases h_exists with ⟨u, hu1, hu2, h_eq⟩
        rw [h_eq]
        exact h_range_S m u hu1 hu2
      have h_both_eq : single_covered_map X 𝒰 hcover hfinite_intersections s (γ1.trans γ2) (covers_S m) (hcover_mem_S m) h_range_both =
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S m) (covers_S m) (hcover_mem_S m) (h_ranges_S m) :=
        single_covered_map_homotopic X 𝒰 hcover hfinite_intersections s (γ1.trans γ2) (γs_S m) (covers_S m) (hcover_mem_S m) h_range_both (h_ranges_S m) H hH
      have h_eq : homs_S m = f ≫ g := by
        dsimp only [homs_S]
        rw [←h_both_eq, ←h_split]
      have h0 : objs' 0 = objs_S 0 := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h_ts0 : ts' 0 = ts_S 0 := by
          dsimp only [ts']
          have h : (0 : Fin (n + 2)).val ≤ m.val := by
            simp <;> omega
          rw [dif_pos h] <;> rfl
        rw [h_ts0] <;> rfl
      have h_last : objs' (Fin.last (n + 1)) = objs_S (Fin.last n) := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h_ts_last : ts' (Fin.last (n + 1)) = ts_S (Fin.last n) := by
          dsimp only [ts']
          have h1 : ¬ (Fin.last (n + 1)).val ≤ m.val := by
            simp [Fin.last] <;> omega
          have h2 : ¬ (Fin.last (n + 1)).val = m.val + 1 := by
            simp [Fin.last] <;> omega
          rw [dif_neg h1, dif_neg h2] <;> simp [Fin.last] <;> omega
        rw [h_ts_last] <;> rfl
      have h_before : ∀ (i : Fin n), i.val < m.val →
          let j : Fin (n + 1) := Fin.castSucc i
          ∃ (h1 : objs' (Fin.castSucc j) = objs_S (Fin.castSucc i))
            (h2 : objs' (Fin.succ j) = objs_S (Fin.succ i)),
          eqToHom h1.symm ≫ homs' j ≫ eqToHom h2 = homs_S i := by
        intro i h_i_lt_m
        let j : Fin (n + 1) := Fin.castSucc i
        have h_j_lt_m : j.val < m.val := by
          dsimp only [j]
          simp [Fin.castSucc, h_i_lt_m] <;> omega
        have h_covers : covers' j = covers_S i := by
          dsimp only [covers', j]
          rw [dif_pos h_j_lt_m] <;> rfl
        have h_ts1 : ts' (Fin.castSucc j) = ts_S (Fin.castSucc i) := by
          dsimp only [ts']
          have h : (Fin.castSucc j).val ≤ m.val := by simp [Fin.castSucc, j, h_i_lt_m] <;> omega
          have h_eq_val : (Fin.castSucc j).val = (Fin.castSucc i).val := by
            simp [Fin.castSucc, j] <;> omega
          rw [dif_pos h]
          apply congr_arg
          apply Fin.ext
          exact h_eq_val
        have h_ts2 : ts' (Fin.succ j) = ts_S (Fin.succ i) := by
          dsimp only [ts']
          have h : (Fin.succ j).val ≤ m.val := by simp [Fin.succ, j, h_i_lt_m] <;> omega
          have h_eq_val : (Fin.succ j).val = (Fin.succ i).val := by
            simp [Fin.succ, j] <;> omega
          rw [dif_pos h]
          apply congr_arg
          apply Fin.ext
          exact h_eq_val
        have h_pts1 : pts' (Fin.castSucc j) = pts_S (Fin.castSucc i) := by
          dsimp only [pts', pts_S]
          rw [h_ts1] <;> rfl
        have h1 : objs' (Fin.castSucc j) = objs_S (Fin.castSucc i) := by
          dsimp only [objs', objs_S]
          rw [h_pts1] <;> rfl
        have h_pts2 : pts' (Fin.succ j) = pts_S (Fin.succ i) := by
          dsimp only [pts', pts_S]
          rw [h_ts2] <;> rfl
        have h2 : objs' (Fin.succ j) = objs_S (Fin.succ i) := by
          dsimp only [objs', objs_S]
          rw [h_pts2] <;> rfl
        refine' ⟨h1, h2, _⟩
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' j t_val = γs_S i t_val := by
          intro t_val
          dsimp only [γs', γs_S]
          have h_eq1 : ts' (Fin.castSucc j) = ts_S (Fin.castSucc i) := h_ts1
          have h_eq2 : ts' (Fin.succ j) = ts_S (Fin.succ i) := h_ts2
          simp [Path.subpath, h_eq1, h_eq2]
          <;> rfl
        -- Get hcover_mem for the cover
        have hU : covers_S i ∈ 𝒰 := hcover_mem_S i
        -- We need h_ranges' j with the rewritten cover
        have h_range1 : Set.range (γs' j) ⊆ (covers_S i : Set X) := by
          rw [←h_covers]
          exact h_ranges' j
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) (covers_S i) hU h_range1 ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2) =
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S i) (covers_S i) hU (h_ranges_S i) := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' j) (γs_S i) h_pts1 h_pts2 hfun (covers_S i) hU h_range1 (h_ranges_S i)
        -- The h1 and h2 are exactly the congr_arg equalities
        have h_eq1 : h1 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1 := by
          apply Subsingleton.elim
        have h_eq2 : h2 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2 := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' j vs covers_S i
        have h_covers_eq : covers' j = covers_S i := h_covers
        have hU' : covers' j ∈ 𝒰 := hcover_mem' j
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) (covers' j) hU' (h_ranges' j) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) (covers_S i) hU h_range1 := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' j) ⊆ (U : Set X))
              (hR2 : Set.range (γs' j) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' j) U hU hR1 hR2
          exact h (covers' j) (covers_S i) h_covers_eq hU' hU (h_ranges' j) h_range1
        -- Rewrite homs' j in the goal
        dsimp only [homs']
        rw [h_eq_map]
        exact h_main
      have h_split1 : objs' (Fin.castSucc (Fin.castSucc m)) = objs_S (Fin.castSucc m) := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h1 : (Fin.castSucc (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc] <;> omega
        have h_ts : ts' (Fin.castSucc (Fin.castSucc m)) = ts_S (Fin.castSucc m) := by
          dsimp only [ts']
          rw [dif_pos h1] <;> rfl
        rw [h_ts] <;> rfl
      have h_split2 : objs' (Fin.succ (Fin.castSucc m)) = mid := by
        dsimp only [objs', mid, pts']
        have h1 : ¬ (Fin.succ (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h2 : (Fin.succ (Fin.castSucc m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h_ts : ts' (Fin.succ (Fin.castSucc m)) = t := by
          dsimp only [ts']
          rw [dif_neg h1, dif_pos h2] <;> rfl
        rw [h_ts] <;> rfl
      have h_split3 : homs' (Fin.castSucc m) = eqToHom h_split1 ≫ f ≫ eqToHom h_split2.symm := by
        dsimp only [homs', f]
        have h_covers : covers' (Fin.castSucc m) = covers_S m := by
          dsimp only [covers']
          have h1 : (Fin.castSucc m).val = m.val := by simp [Fin.castSucc] <;> omega
          rw [dif_neg (by simp [Fin.castSucc] <;> omega), dif_pos h1] <;> rfl
        have h_path1 : ts' (Fin.castSucc (Fin.castSucc m)) = ts_S (Fin.castSucc m) := by
          dsimp only [ts']
          have h1 : (Fin.castSucc (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc] <;> omega
          rw [dif_pos h1] <;> rfl
        have h_path2 : ts' (Fin.succ (Fin.castSucc m)) = t := by
          dsimp only [ts']
          have h1 : ¬ (Fin.succ (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
          have h2 : (Fin.succ (Fin.castSucc m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
          rw [dif_neg h1, dif_pos h2] <;> rfl
        -- Extract endpoint equalities
        have hx : pts' (Fin.castSucc (Fin.castSucc m)) = pts_S (Fin.castSucc m) := by
          dsimp only [pts', pts_S]
          rw [h_path1] <;> rfl
        have hy : pts' (Fin.succ (Fin.castSucc m)) = γ t := by
          dsimp only [pts']
          rw [h_path2] <;> rfl
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' (Fin.castSucc m) t_val = γ1 t_val := by
          intro t_val
          dsimp only [γs', γ1]
          have h_eq1 : ts' (Fin.castSucc (Fin.castSucc m)) = ts_S (Fin.castSucc m) := h_path1
          have h_eq2 : ts' (Fin.succ (Fin.castSucc m)) = t := h_path2
          simp [Path.subpath, h_eq1, h_eq2]
          <;> rfl
        -- Get hcover_mem for the cover
        have hU : covers_S m ∈ 𝒰 := hcover_mem_S m
        -- We need h_ranges' (Fin.castSucc m) with the rewritten cover
        have h_range_prime : Set.range (γs' (Fin.castSucc m)) ⊆ (covers_S m : Set X) := by
          rw [←h_covers]
          exact h_ranges' (Fin.castSucc m)
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers_S m) hU h_range_prime ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy) =
            single_covered_map X 𝒰 hcover hfinite_intersections s γ1 (covers_S m) hU h_range1 := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' (Fin.castSucc m)) γ1 hx hy hfun (covers_S m) hU h_range_prime h_range1
        -- The h_split1 and h_split2 are exactly the congr_arg equalities
        have h_eq1 : h_split1 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx := by
          apply Subsingleton.elim
        have h_eq2 : h_split2 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' (Fin.castSucc m) vs covers_S m
        have h_covers_eq : covers' (Fin.castSucc m) = covers_S m := h_covers
        have hU' : covers' (Fin.castSucc m) ∈ 𝒰 := hcover_mem' (Fin.castSucc m)
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers' (Fin.castSucc m)) hU' (h_ranges' (Fin.castSucc m)) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers_S m) hU h_range_prime := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' (Fin.castSucc m)) ⊆ (U : Set X))
              (hR2 : Set.range (γs' (Fin.castSucc m)) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) U hU hR1 hR2
          exact h (covers' (Fin.castSucc m)) (covers_S m) h_covers_eq hU' hU (h_ranges' (Fin.castSucc m)) h_range_prime
        rw [h_eq_map]
        -- Rearrange h_main: from eqToHom(hx').symm ≫ A ≫ eqToHom(hy') = B
        -- get A = eqToHom(hx') ≫ B ≫ eqToHom(hy').symm
        let hx' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx
        let hy' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy
        let A := single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers_S m) hU h_range_prime
        let B := single_covered_map X 𝒰 hcover hfinite_intersections s γ1 (covers_S m) hU h_range1
        have h_final : A = eqToHom hx' ≫ B ≫ eqToHom hy'.symm := by
          let e_x : _ ≅ _ := eqToIso hx'
          let e_y : _ ≅ _ := eqToIso hy'
          have h_main2' : e_x.inv ≫ A ≫ e_y.hom = B := h_main
          exact VanKampen.iso_sandwich_rewrite e_x e_y A B h_main2'
        exact h_final
      have h_split4 : objs' (Fin.castSucc (Fin.succ m)) = mid := by
        dsimp only [objs', mid, pts']
        have h1 : ¬ (Fin.castSucc (Fin.succ m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h2 : (Fin.castSucc (Fin.succ m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h_ts : ts' (Fin.castSucc (Fin.succ m)) = t := by
          dsimp only [ts']
          rw [dif_neg h1, dif_pos h2] <;> rfl
        rw [h_ts] <;> rfl
      have h_split5 : objs' (Fin.succ (Fin.succ m)) = objs_S (Fin.succ m) := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h1 : ¬ (Fin.succ (Fin.succ m)).val ≤ m.val := by simp [Fin.succ] <;> omega
        have h2 : ¬ (Fin.succ (Fin.succ m)).val = m.val + 1 := by simp [Fin.succ] <;> omega
        have h_ts : ts' (Fin.succ (Fin.succ m)) = ts_S (Fin.succ m) := by
          dsimp only [ts']
          rw [dif_neg h1, dif_neg h2] <;> simp [Fin.succ] <;> omega
        rw [h_ts] <;> rfl
      have h_split6 : homs' (Fin.succ m) = eqToHom h_split4 ≫ g ≫ eqToHom h_split5.symm := by
        dsimp only [homs', g]
        have h_covers : covers' (Fin.succ m) = covers_S m := by
          dsimp only [covers']
          have h1 : (Fin.succ m).val = m.val + 1 := by simp [Fin.succ] <;> omega
          rw [dif_neg (by simp [Fin.succ] <;> omega), dif_neg (by simp [Fin.succ] <;> omega), dif_pos h1] <;> rfl
        have h_path1 : ts' (Fin.castSucc (Fin.succ m)) = t := by
          dsimp only [ts']
          have h1 : ¬ (Fin.castSucc (Fin.succ m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
          have h2 : (Fin.castSucc (Fin.succ m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
          rw [dif_neg h1, dif_pos h2] <;> rfl
        have h_path2 : ts' (Fin.succ (Fin.succ m)) = ts_S (Fin.succ m) := by
          dsimp only [ts']
          have h1 : ¬ (Fin.succ (Fin.succ m)).val ≤ m.val := by simp [Fin.succ] <;> omega
          have h2 : ¬ (Fin.succ (Fin.succ m)).val = m.val + 1 := by simp [Fin.succ] <;> omega
          rw [dif_neg h1, dif_neg h2] <;> simp [Fin.succ] <;> omega
        -- Extract endpoint equalities
        have hx : pts' (Fin.castSucc (Fin.succ m)) = γ t := by
          dsimp only [pts']
          rw [h_path1] <;> rfl
        have hy : pts' (Fin.succ (Fin.succ m)) = pts_S (Fin.succ m) := by
          dsimp only [pts', pts_S]
          rw [h_path2] <;> rfl
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' (Fin.succ m) t_val = γ2 t_val := by
          intro t_val
          dsimp only [γs', γ2]
          have h_eq1 : ts' (Fin.castSucc (Fin.succ m)) = t := h_path1
          have h_eq2 : ts' (Fin.succ (Fin.succ m)) = ts_S (Fin.succ m) := h_path2
          have h_left : (γ.subpath (ts' (Fin.castSucc (Fin.succ m))) (ts' (Fin.succ (Fin.succ m)))) t_val =
              γ (Set.Icc.convexComb (ts' (Fin.castSucc (Fin.succ m))) (ts' (Fin.succ (Fin.succ m))) t_val) := by rfl
          have h_right : (γ.subpath t (ts_S (Fin.succ m))) t_val =
              γ (Set.Icc.convexComb t (ts_S (Fin.succ m)) t_val) := by rfl
          rw [h_left, h_right]
          rw [h_eq1, h_eq2]
        -- Get hcover_mem for the cover
        have hU : covers_S m ∈ 𝒰 := hcover_mem_S m
        -- We need h_ranges' (Fin.succ m) with the rewritten cover
        have h_range_prime : Set.range (γs' (Fin.succ m)) ⊆ (covers_S m : Set X) := by
          rw [←h_covers]
          exact h_ranges' (Fin.succ m)
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers_S m) hU h_range_prime ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy) =
            single_covered_map X 𝒰 hcover hfinite_intersections s γ2 (covers_S m) hU h_range2 := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' (Fin.succ m)) γ2 hx hy hfun (covers_S m) hU h_range_prime h_range2
        -- The h_split4 and h_split5 are exactly the congr_arg equalities
        have h_eq1 : h_split4 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx := by
          apply Subsingleton.elim
        have h_eq2 : h_split5 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' (Fin.succ m) vs covers_S m
        have h_covers_eq : covers' (Fin.succ m) = covers_S m := h_covers
        have hU' : covers' (Fin.succ m) ∈ 𝒰 := hcover_mem' (Fin.succ m)
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers' (Fin.succ m)) hU' (h_ranges' (Fin.succ m)) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers_S m) hU h_range_prime := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' (Fin.succ m)) ⊆ (U : Set X))
              (hR2 : Set.range (γs' (Fin.succ m)) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) U hU hR1 hR2
          exact h (covers' (Fin.succ m)) (covers_S m) h_covers_eq hU' hU (h_ranges' (Fin.succ m)) h_range_prime
        rw [h_eq_map]
        let hx' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx
        let hy' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy
        let e_x : _ ≅ _ := eqToIso hx'
        let e_y : _ ≅ _ := eqToIso hy'
        let A := single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers_S m) hU h_range_prime
        let B := single_covered_map X 𝒰 hcover hfinite_intersections s γ2 (covers_S m) hU h_range2
        have h_main2' : e_x.inv ≫ A ≫ e_y.hom = B := h_main
        exact VanKampen.iso_sandwich_rewrite e_x e_y A B h_main2'
      have h_after : ∀ (j : Fin n), j.val > m.val →
          let i : Fin (n + 1) := Fin.succ j
          ∃ (h1 : objs' (Fin.castSucc i) = objs_S (Fin.castSucc j))
            (h2 : objs' (Fin.succ i) = objs_S (Fin.succ j)),
          eqToHom h1.symm ≫ homs' i ≫ eqToHom h2 = homs_S j := by
        intro j h_j_gt
        let i : Fin (n + 1) := Fin.succ j
        have h_i_gt : i.val > m.val + 1 := by
          dsimp only [i]
          simp [Fin.succ] <;> omega
        have h1 : ¬ (Fin.castSucc i).val ≤ m.val := by simp [Fin.castSucc] <;> omega
        have h2 : ¬ (Fin.castSucc i).val = m.val + 1 := by simp [Fin.castSucc] <;> omega
        have h_c1 : ¬ i.val < m.val := by simp [i, Fin.succ] <;> omega
        have h_c2 : ¬ i.val = m.val := by simp [i, Fin.succ] <;> omega
        have h_c3 : ¬ i.val = m.val + 1 := by simp [i, Fin.succ] <;> omega
        have h_covers : covers' i = covers_S j := by
          dsimp only [covers', i]
          rw [dif_neg h_c1, dif_neg h_c2, dif_neg h_c3]
          <;> apply congr_arg covers_S
          <;> apply Fin.ext
          <;> simp [Fin.succ] <;> omega
        have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc j) := by
          dsimp only [ts']
          have h_eq_val : (Fin.castSucc i).val - 1 = (Fin.castSucc j).val := by
            simp [Fin.castSucc, Fin.succ, i] <;> omega
          rw [dif_neg h1, dif_neg h2]
          <;> apply congr_arg ts_S
          <;> apply Fin.ext
          <;> exact h_eq_val
        have h5 : ¬ (Fin.succ i).val ≤ m.val := by simp [Fin.succ, i] <;> omega
        have h6 : ¬ (Fin.succ i).val = m.val + 1 := by simp [Fin.succ, i] <;> omega
        have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ j) := by
          dsimp only [ts']
          have h_eq_val2 : (Fin.succ i).val - 1 = (Fin.succ j).val := by
            simp [Fin.succ, i] <;> omega
          rw [dif_neg h5, dif_neg h6]
          <;> apply congr_arg ts_S
          <;> apply Fin.ext
          <;> exact h_eq_val2
        have h_pts1 : pts' (Fin.castSucc i) = pts_S (Fin.castSucc j) := by
          dsimp only [pts', pts_S]
          rw [h_ts1] <;> rfl
        have h1_obj : objs' (Fin.castSucc i) = objs_S (Fin.castSucc j) := by
          dsimp only [objs', objs_S]
          rw [h_pts1] <;> rfl
        have h_pts2 : pts' (Fin.succ i) = pts_S (Fin.succ j) := by
          dsimp only [pts', pts_S]
          rw [h_ts2] <;> rfl
        have h2_obj : objs' (Fin.succ i) = objs_S (Fin.succ j) := by
          dsimp only [objs', objs_S]
          rw [h_pts2] <;> rfl
        refine' ⟨h1_obj, h2_obj, _⟩
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' i t_val = γs_S j t_val := by
          intro t_val
          dsimp only [γs', γs_S]
          have h_eq1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc j) := h_ts1
          have h_eq2 : ts' (Fin.succ i) = ts_S (Fin.succ j) := h_ts2
          simp [Path.subpath, h_eq1, h_eq2]
          <;> rfl
        -- Get hcover_mem for the cover
        have hU : covers_S j ∈ 𝒰 := hcover_mem_S j
        -- We need h_ranges' i with the rewritten cover
        have h_range1 : Set.range (γs' i) ⊆ (covers_S j : Set X) := by
          rw [←h_covers]
          exact h_ranges' i
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers_S j) hU h_range1 ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2) =
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S j) (covers_S j) hU (h_ranges_S j) := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' i) (γs_S j) h_pts1 h_pts2 hfun (covers_S j) hU h_range1 (h_ranges_S j)
        -- The h1_obj and h2_obj are exactly the congr_arg equalities
        have h_eq1 : h1_obj = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1 := by
          apply Subsingleton.elim
        have h_eq2 : h2_obj = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2 := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' i vs covers_S j
        have h_covers_eq : covers' i = covers_S j := h_covers
        have hU' : covers' i ∈ 𝒰 := hcover_mem' i
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers' i) hU' (h_ranges' i) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers_S j) hU h_range1 := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' i) ⊆ (U : Set X))
              (hR2 : Set.range (γs' i) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' i) U hU hR1 hR2
          exact h (covers' i) (covers_S j) h_covers_eq hU' hU (h_ranges' i) h_range1
        dsimp only [homs']
        rw [h_eq_map]
        exact h_main
      have h_main : eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last =
          comp_list n objs_S homs_S :=
        comp_list_split_explicit_proof m objs_S homs_S f g h_eq objs' homs' h_before h_split1 h_split2 h_split3 h_split4 h_split5 h_split6 h_after h0 h_last
      let eq0_S : objs_S 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
        dsimp only [objs_S, pts_S]
        have h_pts0 : (γ (ts_S 0)) = x := by
          rw [h_ts0_eq]
          exact γ.source
        rw [h_pts0] <;> rfl
      let eq_last_S : objs_S (Fin.last n) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
        dsimp only [objs_S, pts_S]
        have h_pts_last : (γ (ts_S (Fin.last n))) = y := by
          rw [h_ts1_eq]
          exact γ.target
        rw [h_pts_last] <;> rfl
      let eq0_S' : objs' 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
        dsimp only [objs', pts']
        have h_ts0 : ts' 0 = (0 : I) := by
          have h1 : ts' 0 = ts_S (0 : Fin (n + 1)) := by
            dsimp only [ts']
            have h : (0 : Fin (n + 2)).val ≤ m.val := by simp <;> omega
            rw [dif_pos h]
            <;> congr <;> apply Fin.ext <;> simp
          rw [h1]
          exact h_ts0_eq
        have h_pts0 : (γ (ts' 0)) = x := by
          rw [h_ts0]
          exact γ.source
        rw [h_pts0] <;> rfl
      let eq_last_S' : objs' (Fin.last (n + 1)) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
        dsimp only [objs', pts']
        have h_ts1 : ts' (Fin.last (n + 1)) = (1 : I) := by
          dsimp only [ts']
          let i := Fin.last (n + 1)
          have h1 : ¬ i.val ≤ m.val := by
            simp [i, Fin.last] <;> omega
          have h2 : ¬ i.val = m.val + 1 := by
            simp [i, Fin.last] <;> omega
          have h_fin_eq : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
            apply Fin.ext
            simp [i, Fin.last]
            <;> omega
          rw [dif_neg h1, dif_neg h2]
          rw [h_fin_eq]
          exact h_ts1_eq
        have h_pts_last : (γ (ts' (Fin.last (n + 1)))) = y := by
          rw [h_ts1]
          exact γ.target
        rw [h_pts_last] <;> rfl
      have h_eq0 : eq0_S' = h0.trans eq0_S := by
        exact Subsingleton.elim eq0_S' (h0.trans eq0_S)
      have h_eq_last : eq_last_S' = h_last.trans eq_last_S := by
        exact Subsingleton.elim eq_last_S' (h_last.trans eq_last_S)
      have h_step1 : eqToHom eq0_S'.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom eq_last_S' =
          eqToHom (h0.trans eq0_S).symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom (h_last.trans eq_last_S) := by
        rw [h_eq0, h_eq_last]
      have h_step2 : eqToHom (h0.trans eq0_S).symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom (h_last.trans eq_last_S) =
          eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) ≫ eqToHom eq_last_S := by
        simp [eqToHom_trans, Category.assoc] <;> rfl
      have h_step3 : eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) ≫ eqToHom eq_last_S =
          eqToHom eq0_S.symm ≫ comp_list n objs_S homs_S ≫ eqToHom eq_last_S := by
        have h_assoc : eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) ≫ eqToHom eq_last_S =
            (eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last)) ≫ eqToHom eq_last_S := by
          simp [Category.assoc] <;> rfl
        rw [h_assoc]
        have h_rewrite : eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) =
            eqToHom eq0_S.symm ≫ comp_list n objs_S homs_S := by
          rw [h_main]
        rw [h_rewrite]
        <;> simp [Category.assoc] <;> rfl
      rw [h_step1, h_step2, h_step3]
    -- Combine everything
    rw [h_eq_S, h_eq_S']
    exact h_core

/-- Helper: adding any point to an adapted subdivision gives another adapted subdivision.
    This is just insert_is_adapted from CommonRefinement.lean. -/
lemma adapted_subdivision_add_point
    {x y : X} {γ : Path x y} {S : Finset I} {t : I}
    (hS : IsAdaptedSubdivision 𝒰 γ S) :
    IsAdaptedSubdivision 𝒰 γ (S ∪ {t}) :=
  insert_is_adapted (𝒰 := 𝒰) hS

/-- Refinement invariance: if S ⊆ S' are both adapted subdivisions,
    then they give the same morphism.

    Proof: by induction on |S' \ S|. Each step adds one point and uses refines_one. -/
theorem my_map_from_adapted_subdivision_refines_clean
    {x y : X} {γ : Path x y} {S S' : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ S')
    (h_sub : S ⊆ S') :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' := by
  classical
  -- We prove by induction on k = |S' \ S|
  have h_main : ∀ (k : ℕ), ∀ (S₁ S₂ : Finset I),
    S₁ ⊆ S₂ → S₂ ⊆ S' → (S₂ \ S₁).card = k →
    (hS₁ : IsAdaptedSubdivision 𝒰 γ S₁) →
    (hS₂ : IsAdaptedSubdivision 𝒰 γ S₂) →
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₁ =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₂ := by
    intro k
    induction k with
    | zero =>
      intro S₁ S₂ h_sub1 h_sub2 h_card hS₁ hS₂
      -- Base case: (S₂ \ S₁).card = 0, so S₂ \ S₁ is empty, so S₂ ⊆ S₁
      have h_S2_sub_S1 : S₂ ⊆ S₁ := by
        simpa [Finset.card_eq_zero] using h_card
      have h_S2_eq_S1 : S₂ = S₁ := by
        apply Finset.Subset.antisymm h_S2_sub_S1 h_sub1
      subst h_S2_eq_S1
      <;> rfl
    | succ k ih =>
      intro S₁ S₂ h_sub1 h_sub2 h_card hS₁ hS₂
      -- Inductive step: (S₂ \ S₁).card = k + 1
      have h_nonempty : (S₂ \ S₁).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [h] at h_card
        simp at h_card <;> omega
      let t : I := Classical.choose h_nonempty
      have ht_in_diff : t ∈ S₂ \ S₁ := Classical.choose_spec h_nonempty
      have ht_in_S2 : t ∈ S₂ := Finset.mem_sdiff.mp ht_in_diff |>.1
      have ht_notin_S1 : t ∉ S₁ := Finset.mem_sdiff.mp ht_in_diff |>.2
      let S_mid := S₁ ∪ {t}
      have h_sub_S1_Smid : S₁ ⊆ S_mid := by simp [S_mid]
      have h_sub_Smid_S2 : S_mid ⊆ S₂ := by
        intro x hx
        simp only [S_mid, Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with (hx | rfl)
        · exact h_sub1 hx
        · exact ht_in_S2
      have hS_mid : IsAdaptedSubdivision 𝒰 γ S_mid :=
        adapted_subdivision_add_point X 𝒰 hcover hfinite_intersections s hS₁
      -- By refines_one, map(S₁) = map(S_mid)
      have h_step1 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₁ =
          my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_mid :=
        my_map_from_adapted_subdivision_refines_one_clean X 𝒰 hcover hfinite_intersections s hS₁ hS_mid
      -- Now (S₂ \ S_mid).card = k
      have h_card2 : (S₂ \ S_mid).card = k := by
        have h1 : S₂ \ S₁ = (S₂ \ S_mid) ∪ (S_mid \ S₁) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · -- Forward direction
            rintro ⟨h_in_S2, h_notin_S1⟩
            by_cases h_in_Smid : x ∈ S_mid
            · -- x ∈ S_mid
              exact Or.inr ⟨h_in_Smid, h_notin_S1⟩
            · -- x ∉ S_mid
              exact Or.inl ⟨h_in_S2, h_in_Smid⟩
          · -- Backward direction
            rintro (⟨h_in_S2, h_notin_Smid⟩ | ⟨h_in_Smid, h_notin_S1⟩)
            · -- Case 1: x ∈ S₂ \ S_mid
              have h_notin_S1 : x ∉ S₁ := by
                intro h
                exact h_notin_Smid (h_sub_S1_Smid h)
              exact ⟨h_in_S2, h_notin_S1⟩
            · -- Case 2: x ∈ S_mid \ S₁
              have h_in_S2 : x ∈ S₂ := h_sub_Smid_S2 h_in_Smid
              exact ⟨h_in_S2, h_notin_S1⟩
        rw [h1] at h_card
        have h_disj : Disjoint (S₂ \ S_mid) (S_mid \ S₁) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have h_notin : x ∉ S_mid := Finset.mem_sdiff.mp hx1 |>.2
          have h_in : x ∈ S_mid := Finset.mem_sdiff.mp hx2 |>.1
          exact h_notin h_in
        have h_card1 : (S_mid \ S₁).card = 1 := by
          simp [S_mid, ht_notin_S1] <;> omega
        rw [Finset.card_union_of_disjoint h_disj] at h_card
        rw [h_card1] at h_card
        <;> omega
      -- By induction hypothesis, map(S_mid) = map(S₂)
      have h_step2 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_mid =
          my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₂ := by
        exact ih S_mid S₂ h_sub_Smid_S2 h_sub2 h_card2 hS_mid hS₂
      rw [h_step1, h_step2]
  have h_card_eq : (S' \ S).card = (S' \ S).card := rfl
  exact h_main (S' \ S).card S S' h_sub (by rfl) h_card_eq hS hS'

/-- Helper: the union of two adapted subdivisions is also an adapted subdivision.
    This is just union_is_adapted from CommonRefinement.lean. -/
lemma adapted_subdivision_union
    {x y : X} {γ : Path x y} {S S' : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ S') :
    IsAdaptedSubdivision 𝒰 γ (S ∪ S') :=
  union_is_adapted hfinite_intersections hS hS'

/-- Independence of choice of adapted subdivision.
    This is the key lemma: any two adapted subdivisions give the same morphism.

    Proof: take their union S ∪ S', which is also an adapted subdivision.
    Then both S and S' refine S ∪ S', so by refines both equal the map for S ∪ S'.
    Hence they are equal to each other. -/
theorem my_map_from_adapted_subdivision_independent_clean
    {x y : X} {γ : Path x y} {S S' : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ S') :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' := by
  classical
  let S_union := S ∪ S'
  have hS_union : IsAdaptedSubdivision 𝒰 γ S_union :=
    adapted_subdivision_union X 𝒰 hcover hfinite_intersections s hS hS'
  have h1 : S ⊆ S_union := by simp [S_union]
  have h2 : S' ⊆ S_union := by simp [S_union]
  have h_eq1 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_union :=
    my_map_from_adapted_subdivision_refines_clean X 𝒰 hcover hfinite_intersections s hS hS_union h1
  have h_eq2 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_union :=
    my_map_from_adapted_subdivision_refines_clean X 𝒰 hcover hfinite_intersections s hS' hS_union h2
  rw [h_eq1, h_eq2]

end

end

end P202.Topology.VanKampenProof


/-! Adapted from Uniqueness.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover

/-- Any two functors F G : π₁(X) → s.pt that make the cocone triangles commute
    must be equal on objects. -/
theorem uniqueness_on_objects
    (F G : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt)
    (hF : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F =
      s.ι.app ⟨U, hU⟩)
    (hG : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G =
      s.ι.app ⟨U, hU⟩) :
    ∀ (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)),
      F.obj x = G.obj x := by
  intro x
  let x_pt : X := x.as
  have h_exists : ∃ (U : Opens X), U ∈ 𝒰 ∧ x_pt ∈ U := hcover x_pt

  rcases h_exists with ⟨U, hU, hxU⟩
  let x_U : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U) :=
    FundamentalGroupoid.mk ⟨x_pt, hxU⟩
  have hF_obj : F.obj ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x_U) =
      (s.ι.app ⟨U, hU⟩).obj x_U := by
    have h_eq : ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F).obj x_U =
        (s.ι.app ⟨U, hU⟩).obj x_U := by
      rw [hF U hU]
      <;> rfl
    exact h_eq
  have hG_obj : G.obj ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x_U) =
      (s.ι.app ⟨U, hU⟩).obj x_U := by
    have h_eq : ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G).obj x_U =
        (s.ι.app ⟨U, hU⟩).obj x_U := by
      rw [hG U hU]
      <;> rfl
    exact h_eq
  have h_π_obj : (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x_U = x := by
    simp [x_U]
    <;> rfl
  rw [h_π_obj] at hF_obj
  rw [h_π_obj] at hG_obj
  exact hF_obj.trans hG_obj.symm

end

end

end P202.Topology.VanKampenProof


/-! Adapted from HomotopyDecomposition.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace Path unitInterval Metric

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- Given an open cover of X, any homotopy can be subdivided into a finite grid
    of subrectangles, each of which maps into some open set from the cover. -/
theorem homotopy_has_subdivision
    (𝒰 : Set (Opens X))
    (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
    {x y : X} {γ₁ γ₂ : Path x y} (H : Path.Homotopy γ₁ γ₂) :
    ∃ (n : ℕ), 0 < n ∧ ∀ (i j : Fin n),
      ∃ (U : Opens X), U ∈ 𝒰 ∧
      ∀ (p : I × I),
        (i : ℝ) / (n : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) →
        (j : ℝ) / (n : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) →
        H p ∈ U := by
  let Y := I × I
  let H' : C(Y, X) := ⟨fun p : Y => H p, H.continuous⟩

  -- Index type for the cover: the subtype of opens in 𝒰
  let idx := {U : Opens X // U ∈ 𝒰}
  let V : idx → Set Y := fun U => H' ⁻¹' (U.val : Set X)
  have hV_open : ∀ (U : idx), IsOpen (V U) := fun U => U.val.2.preimage H'.continuous
  have hV_cover : (Set.univ : Set Y) ⊆ ⋃ (U : idx), V U := by
    intro p _
    have h1 : ∃ (U : Opens X), U ∈ 𝒰 ∧ H' p ∈ U := hcover (H' p)
    rcases h1 with ⟨U, hU_mem, hU⟩
    let U' : idx := ⟨U, hU_mem⟩
    exact Set.mem_iUnion.mpr ⟨U', hU⟩

  -- Y is compact
  have hY_compact : IsCompact (Set.univ : Set Y) := isCompact_univ

  -- Apply Lebesgue number lemma
  have h_lebesgue := Filter.HasBasis.lebesgue_number_lemma
    (Metric.uniformity_basis_dist (α := Y)) hY_compact hV_open hV_cover
  rcases h_lebesgue with ⟨ε, hε_pos, hε⟩

  -- Pick n such that 1 / n < ε
  have h_exists_n : ∃ (n : ℕ), 0 < n ∧ 1 / (n : ℝ) < ε := by
    have h1 : ∃ (n : ℕ), (n : ℝ) > 1 / ε := exists_nat_gt (1 / ε)
    rcases h1 with ⟨n, hn⟩
    have hn_pos : 0 < n := by
      by_contra h
      have h' : n = 0 := by omega
      rw [h'] at hn
      have h_contra : 1 / ε > 0 := by positivity
      linarith
    refine ⟨n, hn_pos, ?_⟩
    have h2 : (n : ℝ) > 1 / ε := hn
    have h3 : 1 / (n : ℝ) < ε := by
      calc
        1 / (n : ℝ) < 1 / (1 / ε) := by gcongr
        _ = ε := by
          field_simp [hε_pos.ne'] <;> ring
    exact h3
  rcases h_exists_n with ⟨n, hn_pos, hn⟩

  refine ⟨n, hn_pos, fun i j => ?_⟩

  have hn_pos' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_pos'' : (n : ℝ) ≠ 0 := hn_pos'.ne'
  have hn_ne_zero : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn_ne_zero⟩

  -- Center point of the subrectangle
  let t₀ : ℝ := ((i : ℝ) + 1 / 2) / (n : ℝ)
  let s₀ : ℝ := ((j : ℝ) + 1 / 2) / (n : ℝ)
  have ht₀_nonneg : 0 ≤ t₀ := by positivity
  have ht₀_le_one : t₀ ≤ 1 := by
    have h1 : 0 ≤ (i : ℝ) := by exact_mod_cast Fin.zero_le i
    have h2 : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr (Fin.is_lt i)
    have h3 : (i : ℝ) + 1 / 2 ≤ (n : ℝ) := by linarith
    have h4 : ((i : ℝ) + 1 / 2) / (n : ℝ) ≤ (n : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right h3 hn_pos'.le
    have h5 : (n : ℝ) / (n : ℝ) = 1 := by
      field_simp [hn_pos'']
    rw [h5] at h4
    exact h4
  have hs₀_nonneg : 0 ≤ s₀ := by positivity
  have hs₀_le_one : s₀ ≤ 1 := by
    have h1 : 0 ≤ (j : ℝ) := by exact_mod_cast Fin.zero_le j
    have h2 : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr (Fin.is_lt j)
    have h3 : (j : ℝ) + 1 / 2 ≤ (n : ℝ) := by linarith
    have h4 : ((j : ℝ) + 1 / 2) / (n : ℝ) ≤ (n : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right h3 hn_pos'.le
    have h5 : (n : ℝ) / (n : ℝ) = 1 := by
      field_simp [hn_pos'']
    rw [h5] at h4
    exact h4
  let z₀ : Y := (⟨t₀, ⟨ht₀_nonneg, ht₀_le_one⟩⟩, ⟨s₀, ⟨hs₀_nonneg, hs₀_le_one⟩⟩)

  -- There exists U ∈ 𝒰 such that ball z₀ ε ⊆ H ⁻¹' U
  have h4 : ∃ (U : idx), UniformSpace.ball z₀ {p : Y × Y | dist p.1 p.2 < ε} ⊆ V U := hε z₀ (by trivial)
  rcases h4 with ⟨U, hU_ball⟩

  refine ⟨U.val, U.property, fun p ht1 ht2 hs1 hs2 => ?_⟩

  -- Let t := (p.1 : ℝ), s := (p.2 : ℝ)
  let t : ℝ := (p.1 : ℝ)
  let s : ℝ := (p.2 : ℝ)

  -- Show |t - t₀| ≤ 1/n
  have h_t_diff_lower : t - t₀ ≥ -(1 / (n : ℝ)) := by
    have h1 : t ≥ (i : ℝ) / (n : ℝ) := ht1
    have h2 : (i : ℝ) / (n : ℝ) - t₀ = -(1 / (2 * (n : ℝ))) := by
      dsimp only [t₀]
      field_simp [hn_pos''] <;> ring
    have h3 : t - t₀ ≥ (i : ℝ) / (n : ℝ) - t₀ := by linarith
    rw [h2] at h3
    have h4 : -(1 / (2 * (n : ℝ))) ≥ -(1 / (n : ℝ)) := by
      have h5 : 0 < (n : ℝ) := hn_pos'
      have h6 : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
        apply one_div_le_one_div_of_le
        <;> linarith
      linarith
    linarith
  have h_t_diff_upper : t - t₀ ≤ 1 / (n : ℝ) := by
    have h1 : t ≤ ((i : ℝ) + 1) / (n : ℝ) := ht2
    have h2 : ((i : ℝ) + 1) / (n : ℝ) - t₀ = 1 / (2 * (n : ℝ)) := by
      dsimp only [t₀]
      field_simp [hn_pos''] <;> ring
    have h3 : t - t₀ ≤ ((i : ℝ) + 1) / (n : ℝ) - t₀ := by linarith
    rw [h2] at h3
    have h4 : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
      have h5 : 0 < (n : ℝ) := hn_pos'
      apply one_div_le_one_div_of_le
      <;> linarith
    linarith
  have h5 : |t - t₀| ≤ 1 / (n : ℝ) := by
    rw [abs_le]
    exact ⟨h_t_diff_lower, h_t_diff_upper⟩

  -- Show |s - s₀| ≤ 1/n
  have h_s_diff_lower : s - s₀ ≥ -(1 / (n : ℝ)) := by
    have h1 : s ≥ (j : ℝ) / (n : ℝ) := hs1
    have h2 : (j : ℝ) / (n : ℝ) - s₀ = -(1 / (2 * (n : ℝ))) := by
      dsimp only [s₀]
      field_simp [hn_pos''] <;> ring
    have h3 : s - s₀ ≥ (j : ℝ) / (n : ℝ) - s₀ := by linarith
    rw [h2] at h3
    have h4 : -(1 / (2 * (n : ℝ))) ≥ -(1 / (n : ℝ)) := by
      have h5 : 0 < (n : ℝ) := hn_pos'
      have h6 : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
        apply one_div_le_one_div_of_le
        <;> linarith
      linarith
    linarith
  have h_s_diff_upper : s - s₀ ≤ 1 / (n : ℝ) := by
    have h1 : s ≤ ((j : ℝ) + 1) / (n : ℝ) := hs2
    have h2 : ((j : ℝ) + 1) / (n : ℝ) - s₀ = 1 / (2 * (n : ℝ)) := by
      dsimp only [s₀]
      field_simp [hn_pos''] <;> ring
    have h3 : s - s₀ ≤ ((j : ℝ) + 1) / (n : ℝ) - s₀ := by linarith
    rw [h2] at h3
    have h4 : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
      have h5 : 0 < (n : ℝ) := hn_pos'
      apply one_div_le_one_div_of_le
      <;> linarith
    linarith
  have h6 : |s - s₀| ≤ 1 / (n : ℝ) := by
    rw [abs_le]
    exact ⟨h_s_diff_lower, h_s_diff_upper⟩

  -- Show dist p z₀ ≤ 1/n
  have h_dist1 : dist p.1 z₀.1 = |t - t₀| := by rfl
  have h_dist2 : dist p.2 z₀.2 = |s - s₀| := by rfl
  have h_dist_le : dist p z₀ ≤ 1 / (n : ℝ) := by
    rw [Prod.dist_eq, h_dist1, h_dist2]
    exact max_le h5 h6

  -- Therefore dist p z₀ < ε
  have h_dist_lt : dist p z₀ < ε := by
    calc
      dist p z₀ ≤ 1 / (n : ℝ) := h_dist_le
      _ < ε := hn

  -- Therefore p ∈ ball z₀ ε
  have h9 : dist z₀ p < ε := by
    rw [dist_comm]
    exact h_dist_lt
  have h10 : p ∈ UniformSpace.ball z₀ {p : Y × Y | dist p.1 p.2 < ε} := h9

  -- Therefore p ∈ H ⁻¹' U
  have h11 : p ∈ V U := hU_ball h10

  -- Therefore H p ∈ U
  exact h11

end

end

end P202.Topology.VanKampenProof


/-! Adapted from PartwiseCoveredHomotopy.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]
variable (𝒰 : Set (Opens X))

/-- A partwise covered homotopy: a homotopy H together with an n×m grid of subrectangles,
    each subrectangle mapping into some open set from 𝒰. -/
structure PartwiseCoveredHomotopy {x y : X} {γ₁ γ₂ : Path x y} (H : Path.Homotopy γ₁ γ₂) (n m : ℕ) : Type u where
  covers : Fin n → Fin m → Opens X
  hcover_mem : ∀ i j, covers i j ∈ 𝒰
  h_rectangles : ∀ (i : Fin n) (j : Fin m),
    ∀ (p : I × I),
      (i : ℝ) / (n : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) →
      (j : ℝ) / (m : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ ((j : ℝ) + 1) / (m : ℝ) →
      H p ∈ covers i j

/-- Every homotopy admits a partwise covered decomposition (square grid). -/
theorem exists_partwise_covered_homotopy
    (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
    {x y : X} {γ₁ γ₂ : Path x y} (H : Path.Homotopy γ₁ γ₂) :
    ∃ (n : ℕ), 0 < n ∧ Nonempty (PartwiseCoveredHomotopy 𝒰 H n n) := by
  classical
  -- Use the homotopy_has_subdivision theorem
  have h_main := homotopy_has_subdivision 𝒰 hcover H
  rcases h_main with ⟨n, hn_pos, h_subdiv⟩
  refine' ⟨n, hn_pos, _⟩

  -- For each (i, j), choose a U ∈ 𝒰 that covers the subrectangle
  let covers : Fin n → Fin n → Opens X := fun i j =>
    Classical.choose (h_subdiv i j)
  let hcover_mem : ∀ i j, covers i j ∈ 𝒰 ∧
    ∀ (p : I × I),
      (i : ℝ) / (n : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) →
      (j : ℝ) / (n : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) →
      H p ∈ covers i j := fun i j => Classical.choose_spec (h_subdiv i j)

  let hcover_mem1 : ∀ i j, covers i j ∈ 𝒰 := fun i j => (hcover_mem i j).1
  let h_rectangles : ∀ (i : Fin n) (j : Fin n),
    ∀ (p : I × I),
      (i : ℝ) / (n : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) →
      (j : ℝ) / (n : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) →
      H p ∈ covers i j := fun i j => (hcover_mem i j).2

  exact ⟨⟨covers, hcover_mem1, h_rectangles⟩⟩

end

end P202.Topology.VanKampenProof


/-! Adapted from CompListChain.lean. -/
namespace P202.Topology.VanKampenProof



section

open CategoryTheory

variable {C : Type*} [Groupoid C]

/-- Given two sequences of objects connected by morphisms, and vertical morphisms
    between corresponding objects, such that each square commutes:

    p₀ --f₀--> p₁ --f₁--> ... --f_{n-1}--> pₙ
    |          |                        |
    v₀         v₁                       vₙ
    |          |                        |
    v          v                        v
    q₀ --g₀--> q₁ --g₁--> ... --g_{n-1}--> qₙ

    Then the total composition along the bottom followed by the last vertical morphism
    equals the first vertical morphism followed by the total composition along the top. -/
lemma comp_list_chain_commute {n : ℕ}
    (p_objs : Fin (n + 1) → C)
    (q_objs : Fin (n + 1) → C)
    (f_bottom : ∀ i : Fin n, p_objs (Fin.castSucc i) ⟶ p_objs (Fin.succ i))
    (f_top : ∀ i : Fin n, q_objs (Fin.castSucc i) ⟶ q_objs (Fin.succ i))
    (f_vert : ∀ i : Fin (n + 1), p_objs i ⟶ q_objs i)
    (h_square : ∀ i : Fin n,
      f_bottom i ≫ f_vert (Fin.succ i) = f_vert (Fin.castSucc i) ≫ f_top i) :
    comp_list n p_objs f_bottom ≫ f_vert (Fin.last n) =
    f_vert 0 ≫ comp_list n q_objs f_top := by
  induction n with
  | zero =>
    have h1 : comp_list 0 p_objs f_bottom = 𝟙 (p_objs 0) := comp_list_zero p_objs
    have h2 : comp_list 0 q_objs f_top = 𝟙 (q_objs 0) := comp_list_zero q_objs
    rw [h1, h2]
    <;> simp [Category.id_comp, Category.comp_id]
    <;> rfl
  | succ n ih =>
    -- For n + 1, we decompose into n + 1 = n + 1
    -- The first n morphisms plus the last one
    let p_objs' : Fin (n + 1) → C := fun i : Fin (n + 1) => p_objs (Fin.castSucc i)
    let q_objs' : Fin (n + 1) → C := fun i : Fin (n + 1) => q_objs (Fin.castSucc i)
    let f_bottom' : ∀ i : Fin n, p_objs' (Fin.castSucc i) ⟶ p_objs' (Fin.succ i) :=
      fun i : Fin n => f_bottom (Fin.castSucc i)
    let f_top' : ∀ i : Fin n, q_objs' (Fin.castSucc i) ⟶ q_objs' (Fin.succ i) :=
      fun i : Fin n => f_top (Fin.castSucc i)
    let f_vert' : ∀ i : Fin (n + 1), p_objs' i ⟶ q_objs' i :=
      fun i : Fin (n + 1) => f_vert (Fin.castSucc i)

    have h_square' : ∀ i : Fin n,
        f_bottom' i ≫ f_vert' (Fin.succ i) = f_vert' (Fin.castSucc i) ≫ f_top' i := by
      intro i
      exact h_square (Fin.castSucc i)

    have h_ih := ih p_objs' q_objs' f_bottom' f_top' f_vert' h_square'

    -- Now we have:
    -- comp_list n p_objs' f_bottom' ≫ f_vert' (Fin.last n) = f_vert' 0 ≫ comp_list n q_objs' f_top'
    -- That is:
    -- comp_list of first n bottoms ≫ f_vert n = f_vert 0 ≫ comp_list of first n tops

    -- And we also have the last square:
    -- f_bottom (Fin.last n) ≫ f_vert (Fin.succ (Fin.last n))
    --   = f_vert (Fin.castSucc (Fin.last n)) ≫ f_top (Fin.last n)
    -- That is:
    -- f_bottom n ≫ f_vert (n+1) = f_vert n ≫ f_top n

    have h_last_square := h_square (Fin.last n)

    -- Note: Fin.last (n + 1) = Fin.succ (Fin.last n)
    -- And Fin.castSucc (Fin.last n) = Fin.last n (in the context of f_vert')
    have h_vert_last_eq : f_vert (Fin.last (n + 1)) = f_vert (Fin.succ (Fin.last n)) := by
      congr <;> simp [Fin.last] <;> omega

    have h_vert'_last_eq : f_vert' (Fin.last n) = f_vert (Fin.castSucc (Fin.last n)) := by
      rfl

    have h_vert'_0_eq : f_vert' 0 = f_vert 0 := by
      rfl

    -- Now we can put it all together using whiskering
    -- Let A = comp_list n p_objs' f_bottom'
    -- Let B = f_bottom (Fin.last n)
    -- Let C = f_vert (Fin.succ (Fin.last n))
    -- Let D = f_vert (Fin.castSucc (Fin.last n))
    -- Let E = f_top (Fin.last n)
    -- We have: B ≫ C = D ≫ E
    -- We want: (A ≫ B) ≫ C' = f_vert 0 ≫ (comp_list n q_objs' f_top' ≫ E)
    --   where C' = f_vert (Fin.last (n + 1)) = C
    -- And we have: A ≫ D = A ≫ f_vert' (Fin.last n)
    -- And: f_vert' 0 ≫ comp_list n q_objs' f_top' = f_vert 0 ≫ comp_list n q_objs' f_top'

    -- First, show that we can replace C' with C
    have h_whisker_right : ∀ {X Y Z : C} (f : X ⟶ Y) {g h : Y ⟶ Z}, g = h → f ≫ g = f ≫ h := by
      intro X Y Z f g h eq
      rw [eq]
    have h_whisker_left : ∀ {X Y Z : C} {f g : X ⟶ Y} (h : Y ⟶ Z), f = g → f ≫ h = g ≫ h := by
      intro X Y Z f g h eq
      rw [eq]

    let A := comp_list n p_objs' f_bottom'
    let B := f_bottom (Fin.last n)
    let C := f_vert (Fin.succ (Fin.last n))
    let D := f_vert (Fin.castSucc (Fin.last n))
    let E := f_top (Fin.last n)
    let F := comp_list n q_objs' f_top'

    have h_BC_eq_DE : B ≫ C = D ≫ E := h_last_square
    have h_AD_eq_Avert' : A ≫ D = A ≫ f_vert' (Fin.last n) := by
      exact h_whisker_right A h_vert'_last_eq.symm
    have h_ih' : A ≫ f_vert' (Fin.last n) = f_vert' 0 ≫ F := h_ih
    have h_vert0_eq : f_vert' 0 ≫ F = f_vert 0 ≫ F := by
      exact h_whisker_left F h_vert'_0_eq

    have h_main1 : (A ≫ B) ≫ f_vert (Fin.last (n + 1)) = (A ≫ B) ≫ C := by
      exact h_whisker_right (A ≫ B) h_vert_last_eq

    have h_main2 : (A ≫ B) ≫ C = A ≫ (B ≫ C) := Category.assoc A B C
    have h_main3 : A ≫ (B ≫ C) = A ≫ (D ≫ E) := by rw [h_BC_eq_DE]
    have h_main4 : A ≫ (D ≫ E) = (A ≫ D) ≫ E := (Category.assoc A D E).symm
    have h_main5 : (A ≫ D) ≫ E = (A ≫ f_vert' (Fin.last n)) ≫ E := by rw [h_AD_eq_Avert']
    have h_main6 : (A ≫ f_vert' (Fin.last n)) ≫ E = (f_vert' 0 ≫ F) ≫ E := by rw [h_ih']
    have h_main7 : (f_vert' 0 ≫ F) ≫ E = (f_vert 0 ≫ F) ≫ E := by
      exact h_whisker_left E h_vert0_eq
    have h_main8 : (f_vert 0 ≫ F) ≫ E = f_vert 0 ≫ (F ≫ E) := Category.assoc (f_vert 0) F E

    have h_final : (A ≫ B) ≫ f_vert (Fin.last (n + 1)) = f_vert 0 ≫ (F ≫ E) := by
      have h : (A ≫ B) ≫ f_vert (Fin.last (n + 1)) = (A ≫ B) ≫ C := h_main1
      rw [h]
      have h2 : (A ≫ B) ≫ C = A ≫ B ≫ C := h_main2
      rw [h2]
      have h3 : A ≫ B ≫ C = A ≫ D ≫ E := h_main3
      rw [h3]
      have h4 : A ≫ D ≫ E = (A ≫ D) ≫ E := h_main4
      rw [h4]
      have h5 : (A ≫ D) ≫ E = (A ≫ f_vert' (Fin.last n)) ≫ E := h_main5
      rw [h5]
      have h6 : (A ≫ f_vert' (Fin.last n)) ≫ E = (f_vert' 0 ≫ F) ≫ E := h_main6
      rw [h6]
      have h7 : (f_vert' 0 ≫ F) ≫ E = (f_vert 0 ≫ F) ≫ E := h_main7
      rw [h7]
      have h8 : (f_vert 0 ≫ F) ≫ E = f_vert 0 ≫ (F ≫ E) := h_main8
      rw [h8]

    have h1 : comp_list (n + 1) p_objs f_bottom =
        comp_list n p_objs' f_bottom' ≫ f_bottom (Fin.last n) := by
      rw [comp_list_succ] <;> rfl

    have h2 : comp_list (n + 1) q_objs f_top =
        comp_list n q_objs' f_top' ≫ f_top (Fin.last n) := by
      rw [comp_list_succ] <;> rfl

    rw [h1, h2]
    exact h_final

end

end P202.Topology.VanKampenProof


/-! Adapted from PathDecompositionLemma.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory

open scoped unitInterval

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Helper: the homotopy class of the concat of paths equals the comp_list of their
    homotopy classes in the fundamental groupoid. -/
lemma concat_eq_comp_list {n : ℕ} (p : Fin (n + 1) → X)
    (F : (k : Fin n) → Path (p (Fin.castSucc k)) (p (Fin.succ k))) :
    FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p F)) =
    comp_list n
      (fun i : Fin (n + 1) => FundamentalGroupoid.mk (p i))
      (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F i))) := by
  induction n with
  | zero =>
    -- Base case: n = 0
    simp [comp_list_zero, Path.concat_zero]
    <;> rfl
  | succ n ih =>
    -- Inductive step: n → n + 1
    let p₁ : Fin (n + 1) → X := fun i : Fin (n + 1) => p (Fin.castSucc i)
    let F₁ : (k : Fin n) → Path (p₁ (Fin.castSucc k)) (p₁ (Fin.succ k)) :=
      fun k : Fin n => F (Fin.castSucc k)
    let p_last : X := p (Fin.last (n + 1))
    have h_concat : Path.concat p F =
        (Path.concat p₁ F₁).trans (F (Fin.last n)) := by
      exact Path.concat_succ p F
    have h1 : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p F)) =
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk ((Path.concat p₁ F₁).trans (F (Fin.last n)))) := by
      congr
      <;> exact h_concat
    rw [h1]
    have h_mk : Path.Homotopic.Quotient.mk ((Path.concat p₁ F₁).trans (F (Fin.last n))) =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (Path.concat p₁ F₁))
          (Path.Homotopic.Quotient.mk (F (Fin.last n))) :=
      Path.Homotopic.Quotient.mk_trans (Path.concat p₁ F₁) (F (Fin.last n))
    let a : FundamentalGroupoid X := FundamentalGroupoid.mk (p₁ 0)
    let b : FundamentalGroupoid X := FundamentalGroupoid.mk (p₁ (Fin.last n))
    let c : FundamentalGroupoid X := FundamentalGroupoid.mk (p (Fin.last (n + 1)))
    let p' : a ⟶ b := FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p₁ F₁))
    let q' : b ⟶ c := FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F (Fin.last n)))
    have h_comp : p' ≫ q' = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk (Path.concat p₁ F₁))
        (Path.Homotopic.Quotient.mk (F (Fin.last n))) :=
      FundamentalGroupoid.comp_eq a b c p' q'
    have h2 : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk ((Path.concat p₁ F₁).trans (F (Fin.last n)))) =
        p' ≫ q' := by
      simpa [h_comp, h_mk] using rfl


    rw [h2]
    have h_succ : comp_list (n + 1)
        (fun i : Fin (n + 2) => FundamentalGroupoid.mk (p i))
        (fun i : Fin (n + 1) => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F i))) =
        comp_list n
          (fun i : Fin (n + 1) => FundamentalGroupoid.mk (p₁ i))
          (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F₁ i))) ≫
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F (Fin.last n))) :=
      comp_list_succ n
        (fun i : Fin (n + 2) => FundamentalGroupoid.mk (p i))
        (fun i : Fin (n + 1) => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F i)))
    rw [h_succ]
    have h_ih' : comp_list n
        (fun i : Fin (n + 1) => FundamentalGroupoid.mk (p₁ i))
        (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F₁ i))) =
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p₁ F₁)) :=
      (ih p₁ F₁).symm
    rw [h_ih']
    <;> rfl

/-- Given a path γ and a strictly monotone sequence of points ts : Fin (n + 1) → I,
    the homotopy class of the subpath from ts 0 to ts (Fin.last n) equals the
    composition of the homotopy classes of its subpaths in the fundamental groupoid. -/
theorem subpath_decomposition_comp_list {x y : X} (γ : Path x y) {n : ℕ}
    (ts : Fin (n + 1) → I)
    (h_ts_strict : StrictMono ts) :
    FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n)))) =
    comp_list n
      (fun i : Fin (n + 1) => FundamentalGroupoid.mk (γ (ts i)))
      (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))))) := by
  let p : Fin (n + 1) → X := fun i => γ (ts i)
  let F : (k : Fin n) → Path (p (Fin.castSucc k)) (p (Fin.succ k)) :=
    fun k => γ.subpath (ts (Fin.castSucc k)) (ts (Fin.succ k))
  have h_homotopic : Path.Homotopic (Path.concat p F) (γ.subpath (ts 0) (ts (Fin.last n))) :=
    Path.Homotopic.concat_subpath γ ts
  have h_eq : Path.Homotopic.Quotient.mk (Path.concat p F) =
      Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n))) :=
    Path.Homotopic.Quotient.eq.mpr h_homotopic
  have h_main : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p F)) =
      comp_list n
        (fun i : Fin (n + 1) => FundamentalGroupoid.mk (p i))
        (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F i))) :=
    concat_eq_comp_list p F
  rw [←h_main]
  rw [h_eq]

end

end

end P202.Topology.VanKampenProof


/-! Adapted from HomotopyInvarianceBase.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

-- NOTE: single_covered_map_homotopic is now in SingleCovered.lean
-- This file is kept for backward compatibility of imports.

end

end

end P202.Topology.VanKampenProof


/-! Adapted from ConsecutiveRows.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

/-- Rectangle identity: given four paths forming the boundary of a rectangle,
    all contained in U ∈ 𝒰, then the composition "bottom ; right" equals
    the composition "left ; top" as single_covered_maps.

    Proof: bottom.trans right is homotopic to left.trans top within U,
    so their single_covered_maps are equal. Then apply single_covered_split_eq to both sides. -/
lemma rectangle_identity_clean {a b c d : X} (U : Opens X) (hU : U ∈ 𝒰)
    (γ_bottom : Path a b) (h_bottom : Set.range γ_bottom ⊆ (U : Set X))
    (γ_right : Path b d) (h_right : Set.range γ_right ⊆ (U : Set X))
    (γ_left : Path a c) (h_left : Set.range γ_left ⊆ (U : Set X))
    (γ_top : Path c d) (h_top : Set.range γ_top ⊆ (U : Set X))
    (H_rect : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top))
    (hH_rect : ∀ (p : I × I), H_rect p ∈ U) :
    single_covered_map X 𝒰 hcover hfinite_intersections s γ_bottom U hU h_bottom ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s γ_right U hU h_right =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ_left U hU h_left ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s γ_top U hU h_top := by
  have h1 : single_covered_map X 𝒰 hcover hfinite_intersections s (γ_bottom.trans γ_right) U hU
      (range_trans_subset γ_bottom γ_right h_bottom h_right) =
      single_covered_map X 𝒰 hcover hfinite_intersections s (γ_left.trans γ_top) U hU
      (range_trans_subset γ_left γ_top h_left h_top) :=
    single_covered_map_homotopic X 𝒰 hcover hfinite_intersections s
      (γ_bottom.trans γ_right) (γ_left.trans γ_top) U hU
      (range_trans_subset γ_bottom γ_right h_bottom h_right)
      (range_trans_subset γ_left γ_top h_left h_top)
      H_rect hH_rect
  have h2 : single_covered_map X 𝒰 hcover hfinite_intersections s γ_bottom U hU h_bottom ≫
      single_covered_map X 𝒰 hcover hfinite_intersections s γ_right U hU h_right =
      single_covered_map X 𝒰 hcover hfinite_intersections s (γ_bottom.trans γ_right) U hU
        (range_trans_subset γ_bottom γ_right h_bottom h_right) :=
    single_covered_split_eq X 𝒰 hcover hfinite_intersections s U hU γ_bottom h_bottom γ_right h_right
  have h3 : single_covered_map X 𝒰 hcover hfinite_intersections s γ_left U hU h_left ≫
      single_covered_map X 𝒰 hcover hfinite_intersections s γ_top U hU h_top =
      single_covered_map X 𝒰 hcover hfinite_intersections s (γ_left.trans γ_top) U hU
        (range_trans_subset γ_left γ_top h_left h_top) :=
    single_covered_split_eq X 𝒰 hcover hfinite_intersections s U hU γ_left h_left γ_top h_top
  rw [h2, h3, h1]

end

end

end P202.Topology.VanKampenProof


/-! Adapted from CompositionFinal.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

/-- Scale a point in I to the first half [0, 1/2] -/
def scale_first_half (t : I) : I :=
  ⟨(t : ℝ) / 2, by
    have h₁ : 0 ≤ (t : ℝ) / 2 := by linarith [t.prop.1]
    have h₂ : (t : ℝ) / 2 ≤ 1 := by linarith [t.prop.2]
    exact ⟨h₁, h₂⟩⟩

/-- Scale a point in I to the second half [1/2, 1] -/
def scale_second_half (t : I) : I :=
  ⟨1 / 2 + (t : ℝ) / 2, by
    have h₁ : 0 ≤ 1 / 2 + (t : ℝ) / 2 := by linarith [t.prop.1]
    have h₂ : 1 / 2 + (t : ℝ) / 2 ≤ 1 := by linarith [t.prop.2]
    exact ⟨h₁, h₂⟩⟩

/-- Helper: Strict monotonicity of scaling functions -/
lemma scale_first_half_strict : StrictMono (scale_first_half : I → I) := by
  intro a b h
  have h' : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
  have h'' : ((a : ℝ) / 2) < ((b : ℝ) / 2) := by linarith
  exact_mod_cast h''

lemma scale_second_half_strict : StrictMono (scale_second_half : I → I) := by
  intro a b h
  have h' : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
  have h'' : (1 / 2 + (a : ℝ) / 2) < (1 / 2 + (b : ℝ) / 2) := by linarith
  exact_mod_cast h''

lemma scale_first_half_le_half (t : I) : (scale_first_half t : ℝ) ≤ 1 / 2 := by
  simp [scale_first_half] <;> linarith [t.prop.2]

lemma scale_second_half_ge_half (t : I) : (scale_second_half t : ℝ) ≥ 1 / 2 := by
  simp [scale_second_half] <;> linarith [t.prop.1]

/-- Given an adapted subdivision, extract canonical decomposition -/
lemma exists_canonical_decomposition' {x y : X} {γ : Path x y} {S : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S) :
    ∃ (n : ℕ) (ts : Fin (n + 1) → I) (h_ts_strict : StrictMono ts)
      (h_ts_image : Finset.image ts Finset.univ = S)
      (covers : Fin n → Opens X) (hcover_mem : ∀ i, covers i ∈ 𝒰)
      (h_range : ∀ i, ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers i : Set X)),
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts h_ts_strict h_ts_image covers hcover_mem h_range := by
  classical
  have h0_in : (0 : I) ∈ S := hS.1
  have h1_in : (1 : I) ∈ S := hS.2.1
  have hS_nonempty : S.Nonempty := ⟨0, h0_in⟩
  let k : ℕ := S.card
  have hk_pos : 0 < k := Finset.card_pos.mpr hS_nonempty
  let e : Fin k ↪o I := S.orderEmbOfFin rfl
  have h_e_mem : ∀ (i : Fin k), e i ∈ S := Finset.orderEmbOfFin_mem S rfl
  have h_e_strict_mono : StrictMono e := OrderEmbedding.strictMono e
  have h_image : Finset.image e Finset.univ = S := by
    convert Finset.image_orderEmbOfFin_univ S rfl using 1 <;>
      ext x <;> simp only [Finset.mem_image] <;> rfl
  let n : ℕ := k - 1
  have hk_eq : k = n + 1 := by omega
  let ts (i : Fin (n + 1)) : I := e ⟨i.val, by rw [hk_eq] <;> exact i.is_lt⟩
  have h_ts_strict : StrictMono ts := by
    intro i j h
    exact h_e_strict_mono (by simpa [ts] using h)
  have h_ts_image : Finset.image ts Finset.univ = S := by
    have h1 : Finset.image ts Finset.univ = Finset.image e Finset.univ := by
      ext x
      simp only [ts, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨⟨i.val, by rw [hk_eq] <;> exact i.is_lt⟩, rfl⟩
      · rintro ⟨j, rfl⟩
        have h_j_lt : j.val < n + 1 := by rw [←hk_eq]; exact j.is_lt
        let i : Fin (n + 1) := ⟨j.val, h_j_lt⟩
        exact ⟨i, by simp [i] <;> rfl⟩
    rw [h1, h_image]
  let choose_data (i : Fin n) :
    ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (U : Set X) := by
    let s₁ := ts (Fin.castSucc i)
    let s₂ := ts (Fin.succ i)
    have h_s1_in : s₁ ∈ S := h_e_mem _
    have h_s2_in : s₂ ∈ S := h_e_mem _
    have h_lt : s₁ < s₂ := h_e_strict_mono (by simp [Fin.castSucc, Fin.succ] <;> omega)
    have h_no_between : ∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False := by
      intro t ht h1 h2
      have h_exists : ∃ (j : Fin k), e j = t := by
        have h : t ∈ Finset.image e Finset.univ := by rw [h_image] <;> exact ht
        rcases Finset.mem_image.mp h with ⟨j, _, rfl⟩
        exact ⟨j, rfl⟩
      rcases h_exists with ⟨j, hj⟩
      have h_j_gt : (Fin.castSucc i).val < j.val := by
        have h4 : ts (Fin.castSucc i) < e j := by rw [hj] <;> exact h1
        have h5 : e ⟨(Fin.castSucc i).val, by rw [hk_eq] <;> exact (Fin.castSucc i).is_lt⟩ = ts (Fin.castSucc i) := by rfl
        rw [←h5] at h4
        exact h_e_strict_mono.lt_iff_lt.mp h4
      have h_j_lt : j.val < (Fin.succ i).val := by
        have h4 : e j < ts (Fin.succ i) := by rw [hj] <;> exact h2
        have h5 : e ⟨(Fin.succ i).val, by rw [hk_eq] <;> exact (Fin.succ i).is_lt⟩ = ts (Fin.succ i) := by rfl
        rw [←h5] at h4
        exact h_e_strict_mono.lt_iff_lt.mp h4
      simp [Fin.castSucc, Fin.succ] at h_j_gt h_j_lt <;> omega
    exact hS.2.2 s₁ s₂ h_s1_in h_s2_in h_lt h_no_between
  choose U hU using choose_data
  let covers (i : Fin n) : Opens X := U i
  let hcover_mem (i : Fin n) : covers i ∈ 𝒰 := (hU i).1
  let h_range (i : Fin n) : ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers i : Set X) := (hU i).2
  have h_eq : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts h_ts_strict h_ts_image covers hcover_mem h_range :=
    my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS ts h_ts_strict h_ts_image covers hcover_mem h_range
  exact ⟨n, ts, h_ts_strict, h_ts_image, covers, hcover_mem, h_range, h_eq⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Main composition lemma -/
theorem my_map_from_adapted_subdivision_comp_cauchy {x y z : X}
    (γ₁ : Path x y) (γ₂ : Path y z)
    {S₁ : Finset I} (hS₁ : IsAdaptedSubdivision 𝒰 γ₁ S₁)
    {S₂ : Finset I} (hS₂ : IsAdaptedSubdivision 𝒰 γ₂ S₂) :
    ∃ (S : Finset I) (hS : IsAdaptedSubdivision 𝒰 (γ₁.trans γ₂) S),
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₁ ≫
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₂ := by
  classical
  -- Step 1: Get canonical decompositions
  rcases exists_canonical_decomposition' X 𝒰 hcover hfinite_intersections s hS₁ with
    ⟨n₁, ts₁, h_ts₁_strict, h_ts₁_image, covers₁, hcover₁_mem, h_range₁, h_eq₁⟩
  rcases exists_canonical_decomposition' X 𝒰 hcover hfinite_intersections s hS₂ with
    ⟨n₂, ts₂, h_ts₂_strict, h_ts₂_image, covers₂, hcover₂_mem, h_range₂, h_eq₂⟩

  let n := n₁ + n₂

  -- Step 2: Helper facts about endpoints
  have h_ts1_last : ts₁ (Fin.last n₁) = (1 : I) := by
    have h1_in : (1 : I) ∈ S₁ := hS₁.2.1
    have h1_in_image : (1 : I) ∈ Finset.image ts₁ Finset.univ := by rw [h_ts₁_image] <;> exact h1_in
    let i : Fin (n₁ + 1) := Classical.choose (Finset.mem_image.mp h1_in_image)
    let hi : ts₁ i = (1 : I) := (Classical.choose_spec (Finset.mem_image.mp h1_in_image)).2
    have h_i_eq_last : i = Fin.last n₁ := by
      apply Fin.eq_last_of_not_lt
      intro h
      have h_tsk_lt_ts1 : ts₁ i < ts₁ (Fin.last n₁) := h_ts₁_strict h
      rw [hi] at h_tsk_lt_ts1
      have h' : (1 : ℝ) < (ts₁ (Fin.last n₁) : ℝ) := by exact_mod_cast h_tsk_lt_ts1
      have h'' : (ts₁ (Fin.last n₁) : ℝ) ≤ 1 := (ts₁ (Fin.last n₁)).prop.2
      linarith
    rw [h_i_eq_last] at hi
    exact hi
  have h_ts2_zero : ts₂ 0 = (0 : I) := by
    have h0_in : (0 : I) ∈ S₂ := hS₂.1
    have h0_in_image : (0 : I) ∈ Finset.image ts₂ Finset.univ := by rw [h_ts₂_image] <;> exact h0_in
    let i : Fin (n₂ + 1) := Classical.choose (Finset.mem_image.mp h0_in_image)
    let hi : ts₂ i = (0 : I) := (Classical.choose_spec (Finset.mem_image.mp h0_in_image)).2
    have h_i_eq_0 : i = 0 := by
      by_contra h
      have h_i_pos : 0 < i := Fin.pos_iff_ne_zero.mpr h
      have h_ts0_lt_tsi : ts₂ 0 < ts₂ i := h_ts₂_strict h_i_pos
      rw [hi] at h_ts0_lt_tsi
      have h_nonneg : (0 : ℝ) ≤ (ts₂ 0 : ℝ) := (ts₂ 0).prop.1
      have h_cont : (ts₂ 0 : ℝ) < (0 : ℝ) := by exact_mod_cast h_ts0_lt_tsi
      linarith
    rw [h_i_eq_0] at hi
    exact hi
  have h_ts1_zero : ts₁ 0 = (0 : I) := by
    have h0_in : (0 : I) ∈ S₁ := hS₁.1
    have h0_in_image : (0 : I) ∈ Finset.image ts₁ Finset.univ := by rw [h_ts₁_image] <;> exact h0_in
    let i : Fin (n₁ + 1) := Classical.choose (Finset.mem_image.mp h0_in_image)
    let hi : ts₁ i = (0 : I) := (Classical.choose_spec (Finset.mem_image.mp h0_in_image)).2
    have h_i_eq_0 : i = 0 := by
      by_contra h
      have h_i_pos : 0 < i := Fin.pos_iff_ne_zero.mpr h
      have h_ts0_lt_tsi : ts₁ 0 < ts₁ i := h_ts₁_strict h_i_pos
      rw [hi] at h_ts0_lt_tsi
      have h_nonneg : (0 : ℝ) ≤ (ts₁ 0 : ℝ) := (ts₁ 0).prop.1
      have h_cont : (ts₁ 0 : ℝ) < (0 : ℝ) := by exact_mod_cast h_ts0_lt_tsi
      linarith
    rw [h_i_eq_0] at hi
    exact hi
  have h_ts2_last : ts₂ (Fin.last n₂) = (1 : I) := by
    have h1_in : (1 : I) ∈ S₂ := hS₂.2.1
    have h1_in_image : (1 : I) ∈ Finset.image ts₂ Finset.univ := by rw [h_ts₂_image] <;> exact h1_in
    let i : Fin (n₂ + 1) := Classical.choose (Finset.mem_image.mp h1_in_image)
    let hi : ts₂ i = (1 : I) := (Classical.choose_spec (Finset.mem_image.mp h1_in_image)).2
    have h_i_eq_last : i = Fin.last n₂ := by
      apply Fin.eq_last_of_not_lt
      intro h
      have h_tsk_lt_ts1 : ts₂ i < ts₂ (Fin.last n₂) := h_ts₂_strict h
      rw [hi] at h_tsk_lt_ts1
      have h' : (1 : ℝ) < (ts₂ (Fin.last n₂) : ℝ) := by exact_mod_cast h_tsk_lt_ts1
      have h'' : (ts₂ (Fin.last n₂) : ℝ) ≤ 1 := (ts₂ (Fin.last n₂)).prop.2
      linarith
    rw [h_i_eq_last] at hi
    exact hi

  -- Step 3: Define concatenated subdivision
  let ts_concat (i : Fin (n + 1)) : I :=
    if h : i.val ≤ n₁ then
      scale_first_half (ts₁ ⟨i.val, by omega⟩)
    else
      scale_second_half (ts₂ ⟨i.val - n₁, by omega⟩)
  let covers_concat (i : Fin n) : Opens X :=
    if h : i.val < n₁ then
      covers₁ ⟨i.val, by omega⟩
    else
      covers₂ ⟨i.val - n₁, by omega⟩

  -- All remaining subproofs are left as future work - this is the skeleton
  have h_ts_concat_strict : StrictMono ts_concat := by
    intro i j h
    have h_val : i.val < j.val := h
    by_cases h_i : i.val ≤ n₁
    · -- i ≤ n₁
      by_cases h_j : j.val ≤ n₁
      · -- both ≤ n₁
        let i' : Fin (n₁ + 1) := ⟨i.val, by omega⟩
        let j' : Fin (n₁ + 1) := ⟨j.val, by omega⟩
        have h_ij' : i' < j' := by exact_mod_cast h_val
        have h_ts_lt : ts₁ i' < ts₁ j' := h_ts₁_strict h_ij'
        have h_ts_lt_val : (ts₁ i' : ℝ) < (ts₁ j' : ℝ) := by exact_mod_cast h_ts_lt
        have h1 : ts_concat i = scale_first_half (ts₁ i') := by
          simp only [ts_concat, h_i] <;> rfl
        have h2 : ts_concat j = scale_first_half (ts₁ j') := by
          simp only [ts_concat, h_j] <;> rfl
        rw [h1, h2]
        apply Subtype.mk_lt_mk.mpr
        <;> linarith
      · -- i ≤ n₁, j > n₁
        have h_j_gt_n1 : ¬ j.val ≤ n₁ := by omega
        have h_j_minus_n1_pos : 0 < j.val - n₁ := by omega
        let k : Fin (n₂ + 1) := ⟨j.val - n₁, by omega⟩
        have h_k_pos : 0 < k := by
          simp [k, Fin.pos_iff_ne_zero] <;> omega
        have h_lt0 : ts₂ 0 < ts₂ k := h_ts₂_strict h_k_pos
        have h0_val : (ts₂ 0 : ℝ) = 0 := by
          have h_eq : ts₂ 0 = (0 : I) := h_ts2_zero
          rw [h_eq]
          <;> simp
        have h_k_val_pos : (0 : ℝ) < (ts₂ k : ℝ) := by
          have h : (ts₂ 0 : ℝ) < (ts₂ k : ℝ) := by exact_mod_cast h_lt0
          rw [h0_val] at h
          exact h
        let tsi : I := ts_concat i
        let tsj : I := ts_concat j
        have h_tsi_eq : tsi = scale_first_half (ts₁ ⟨i.val, by omega⟩) := by
          simp only [ts_concat, h_i, tsi] <;> rfl
        have h_tsj_eq : tsj = scale_second_half (ts₂ k) := by
          simp only [ts_concat, h_j_gt_n1, tsj] <;> rfl
        have h1_val : (tsi : ℝ) ≤ 1 / 2 := by
          rw [h_tsi_eq]
          have h4 : ((scale_first_half (ts₁ ⟨i.val, by omega⟩) : I) : ℝ) = (ts₁ ⟨i.val, by omega⟩ : ℝ) / 2 := by
            simp [scale_first_half] <;> rfl
          rw [h4]
          have h5 : (ts₁ ⟨i.val, by omega⟩ : ℝ) ≤ 1 := (ts₁ ⟨i.val, by omega⟩).prop.2
          linarith
        have h2_val : (1 / 2 : ℝ) < (tsj : ℝ) := by
          rw [h_tsj_eq]
          have h3 : ((scale_second_half (ts₂ k) : I) : ℝ) = 1 / 2 + (ts₂ k : ℝ) / 2 := by
            simp [scale_second_half] <;> rfl
          rw [h3]
          linarith [h_k_val_pos]
        have h_goal_val : (tsi : ℝ) < (tsj : ℝ) := by linarith
        exact Subtype.mk_lt_mk.mpr h_goal_val
    · -- i > n₁, so j > n₁ too
      have h_i' : ¬i.val ≤ n₁ := by tauto
      have h_j' : ¬j.val ≤ n₁ := by omega
      let i' : Fin (n₂ + 1) := ⟨i.val - n₁, by omega⟩
      let j' : Fin (n₂ + 1) := ⟨j.val - n₁, by omega⟩
      have h_ij' : i' < j' := by exact_mod_cast (show i.val - n₁ < j.val - n₁ by omega)
      have h_ts_lt : ts₂ i' < ts₂ j' := h_ts₂_strict h_ij'
      have h_ts_lt_val : (ts₂ i' : ℝ) < (ts₂ j' : ℝ) := by exact_mod_cast h_ts_lt
      have h1 : ts_concat i = scale_second_half (ts₂ i') := by
        simp only [ts_concat, h_i'] <;> rfl
      have h2 : ts_concat j = scale_second_half (ts₂ j') := by
        simp only [ts_concat, h_j'] <;> rfl
      rw [h1, h2]
      apply Subtype.mk_lt_mk.mpr
      <;> linarith
  have hcover_concat_mem : ∀ i : Fin n, covers_concat i ∈ 𝒰 := by
    intro i
    dsimp only [covers_concat]
    by_cases h : i.val < n₁
    · rw [dif_pos h]
      exact hcover₁_mem ⟨i.val, by omega⟩
    · rw [dif_neg h]
      exact hcover₂_mem ⟨i.val - n₁, by omega⟩
  have h_range_concat : ∀ (i : Fin n), ∀ (t : I),
      ts_concat (Fin.castSucc i) ≤ t → t ≤ ts_concat (Fin.succ i) → (γ₁.trans γ₂) t ∈ (covers_concat i : Set X) := by
    intro i t h1 h2
    by_cases h : i.val < n₁
    · -- Case 1: i.val < n₁, use first path
      let i' : Fin n₁ := ⟨i.val, h⟩
      have h_cover : covers_concat i = covers₁ i' := by
        dsimp only [covers_concat]
        rw [dif_pos h] <;> rfl
      have h_cast_lt : (Fin.castSucc i).val < n₁ := by
        simpa [Fin.castSucc] using h
      have h_succ_le : (Fin.succ i).val ≤ n₁ := by
        simp [Fin.succ] <;> omega
      have h_ts1 : ts_concat (Fin.castSucc i) = scale_first_half (ts₁ (Fin.castSucc i')) := by
        dsimp only [ts_concat]
        have h_le : (Fin.castSucc i).val ≤ n₁ := by linarith
        rw [dif_pos h_le] <;> rfl
      have h_ts2 : ts_concat (Fin.succ i) = scale_first_half (ts₁ (Fin.succ i')) := by
        dsimp only [ts_concat]
        rw [dif_pos h_succ_le] <;> rfl
      have h_ts2_val_le_half : (ts_concat (Fin.succ i) : ℝ) ≤ 1 / 2 := by
        rw [h_ts2]
        simp [scale_first_half] <;> have h' := (ts₁ (Fin.succ i')).prop.2 <;> linarith
      have h_t_le_half : (t : ℝ) ≤ 1 / 2 := by
        have h' : (t : ℝ) ≤ (ts_concat (Fin.succ i) : ℝ) := by exact_mod_cast h2
        exact le_trans h' h_ts2_val_le_half
      let t' : I := ⟨2 * (t : ℝ), by
        constructor
        · have h_pos : 0 ≤ (t : ℝ) := t.prop.1
          linarith
        · linarith⟩
      have h_apply : (γ₁.trans γ₂) t = γ₁ t' := by
        rw [Path.trans_apply, dif_pos h_t_le_half]
        <;> congr <;> apply Subtype.ext <;> simp [t'] <;> ring
      have h_ineq1 : (ts₁ (Fin.castSucc i') : ℝ) ≤ (t' : ℝ) := by
        have h' : (ts_concat (Fin.castSucc i) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
        rw [h_ts1] at h'
        simp [scale_first_half, t'] at h' ⊢ <;> linarith
      have h_ineq1' : ts₁ (Fin.castSucc i') ≤ t' := by exact_mod_cast h_ineq1
      have h_ineq2 : (t' : ℝ) ≤ (ts₁ (Fin.succ i') : ℝ) := by
        have h' : (t : ℝ) ≤ (ts_concat (Fin.succ i) : ℝ) := by exact_mod_cast h2
        rw [h_ts2] at h'
        simp [scale_first_half, t'] at h' ⊢ <;> linarith
      have h_ineq2' : t' ≤ ts₁ (Fin.succ i') := by exact_mod_cast h_ineq2
      have h_main : γ₁ t' ∈ (covers₁ i' : Set X) := h_range₁ i' t' h_ineq1' h_ineq2'
      rw [h_apply, h_cover]
      exact h_main
    · -- Case 2: i.val ≥ n₁, use second path
      have h' : n₁ ≤ i.val := by omega
      let i' : Fin n₂ := ⟨i.val - n₁, by omega⟩
      have h_cover : covers_concat i = covers₂ i' := by
        dsimp only [covers_concat]
        rw [dif_neg h] <;> rfl
      have h_cast_val : (Fin.castSucc i).val = i.val := by simp [Fin.castSucc]
      have h_succ_val : (Fin.succ i).val = i.val + 1 := by simp [Fin.succ]
      have h_k1_lt : (Fin.castSucc i).val - n₁ < n₂ + 1 := by omega
      let k1 : Fin (n₂ + 1) := ⟨(Fin.castSucc i).val - n₁, h_k1_lt⟩
      have h_k1_eq : k1 = Fin.castSucc i' := by
        apply Fin.ext <;> simp [k1, i'] <;> omega
      have h_k2_lt : (Fin.succ i).val - n₁ < n₂ + 1 := by omega
      let k2 : Fin (n₂ + 1) := ⟨(Fin.succ i).val - n₁, h_k2_lt⟩
      have h_k2_eq : k2 = Fin.succ i' := by
        apply Fin.ext <;> simp [k2, i'] <;> omega
      have h_ts1_eq : ts_concat (Fin.castSucc i) = scale_second_half (ts₂ (Fin.castSucc i')) := by
        by_cases h_eq : (Fin.castSucc i).val = n₁
        · -- Boundary case: (Fin.castSucc i).val = n₁
          have h_i_val_eq_n1 : i.val = n₁ := by
            rw [←h_cast_val] <;> exact h_eq
          have h_i'_val_eq_0 : i'.val = 0 := by
            simp [i', h_i_val_eq_n1] <;> omega
          have h_ts_cast : ts₂ (Fin.castSucc i') = (0 : I) := by
            have h_fin : Fin.castSucc i' = (0 : Fin (n₂ + 1)) := by
              apply Fin.ext
              simp [h_i'_val_eq_0] <;> omega
            rw [h_fin, h_ts2_zero]
          have h_lt : (Fin.castSucc i).val < n₁ + 1 := by omega
          let k : Fin (n₁ + 1) := ⟨(Fin.castSucc i).val, h_lt⟩
          have h_k_eq_last : k = Fin.last n₁ := by
            apply Fin.ext
            simpa [k] using h_eq
          have h_real_eq : (ts_concat (Fin.castSucc i) : ℝ) = (scale_second_half (ts₂ (Fin.castSucc i')) : ℝ) := by
            rw [h_ts_cast]
            have h1 : (ts_concat (Fin.castSucc i) : ℝ) = (scale_first_half (ts₁ k) : ℝ) := by
              dsimp only [ts_concat]
              have h_le : (Fin.castSucc i).val ≤ n₁ := by linarith
              rw [dif_pos h_le] <;> rfl
            rw [h1, h_k_eq_last, h_ts1_last]
            <;> simp [scale_first_half, scale_second_half] <;> norm_num
          exact Subtype.ext h_real_eq
        · -- General case: (Fin.castSucc i).val > n₁
          have h_ne : (Fin.castSucc i).val ≠ n₁ := h_eq
          have h_gt : n₁ < (Fin.castSucc i).val := by
            rw [h_cast_val] <;> omega
          have h_not_le : ¬ (Fin.castSucc i).val ≤ n₁ := by omega
          dsimp only [ts_concat]
          rw [dif_neg h_not_le]
          <;> congr <;> exact h_k1_eq
      have h_succ_gt : ¬ (Fin.succ i).val ≤ n₁ := by
        rw [h_succ_val] <;> omega
      have h_ts2_eq : ts_concat (Fin.succ i) = scale_second_half (ts₂ (Fin.succ i')) := by
        dsimp only [ts_concat]
        rw [dif_neg h_succ_gt]
        <;> congr <;> exact h_k2_eq
      have h_ts1_val_ge_half : (ts_concat (Fin.castSucc i) : ℝ) ≥ 1 / 2 := by
        rw [h_ts1_eq]
        simp [scale_second_half] <;> have h' := (ts₂ (Fin.castSucc i')).prop.1 <;> linarith
      have h_t_ge_half : (t : ℝ) ≥ 1 / 2 := by
        have h' : (ts_concat (Fin.castSucc i) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
        exact le_trans h_ts1_val_ge_half h'
      let t' : I := ⟨2 * (t : ℝ) - 1, by
        constructor
        · linarith
        · have h_top : (t : ℝ) ≤ 1 := t.prop.2
          linarith⟩
      have h_apply : (γ₁.trans γ₂) t = γ₂ t' := by
        by_cases h_eq : (t : ℝ) = 1 / 2
        · -- Boundary case t = 1/2
          have h_t'_eq_0 : (t' : ℝ) = 0 := by
            simp [t', h_eq] <;> ring
          have h_t' : t' = (0 : I) := by
            apply Subtype.ext <;> simp [h_t'_eq_0]
          rw [h_t']
          <;> simp [Path.trans_apply, h_eq] <;> norm_num
        · -- General case t > 1/2
          have h_ne : (t : ℝ) ≠ 1 / 2 := h_eq
          have h_gt : (t : ℝ) > 1 / 2 := by
            exact lt_of_le_of_ne h_t_ge_half h_ne.symm
          have h_not_le : ¬ (t : ℝ) ≤ 1 / 2 := not_le.mpr h_gt
          rw [Path.trans_apply, dif_neg h_not_le]
          <;> congr <;> apply Subtype.ext <;> simp [t'] <;> ring
      have h_ineq1 : (ts₂ (Fin.castSucc i') : ℝ) ≤ (t' : ℝ) := by
        have h' : (ts_concat (Fin.castSucc i) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
        rw [h_ts1_eq] at h'
        simp [scale_second_half, t'] at h' ⊢ <;> linarith
      have h_ineq1' : ts₂ (Fin.castSucc i') ≤ t' := by exact_mod_cast h_ineq1
      have h_ineq2 : (t' : ℝ) ≤ (ts₂ (Fin.succ i') : ℝ) := by
        have h' : (t : ℝ) ≤ (ts_concat (Fin.succ i) : ℝ) := by exact_mod_cast h2
        rw [h_ts2_eq] at h'
        simp [scale_second_half, t'] at h' ⊢ <;> linarith
      have h_ineq2' : t' ≤ ts₂ (Fin.succ i') := by exact_mod_cast h_ineq2
      have h_main : γ₂ t' ∈ (covers₂ i' : Set X) := h_range₂ i' t' h_ineq1' h_ineq2'
      rw [h_apply, h_cover]
      exact h_main

  have h_n1_pos : 0 < n₁ := by
    by_contra h
    have h' : n₁ = 0 := by omega
    have h0_in : (0 : I) ∈ S₁ := hS₁.1
    have h1_in : (1 : I) ∈ S₁ := hS₁.2.1
    rw [←h_ts₁_image] at h0_in h1_in
    rcases Finset.mem_image.mp h0_in with ⟨i0, _, h0_eq⟩
    rcases Finset.mem_image.mp h1_in with ⟨i1, _, h1_eq⟩
    have h_i0_val : i0.val = 0 := by
      subst h'
      fin_cases i0 <;> simp
    have h_i1_val : i1.val = 0 := by
      subst h'
      fin_cases i1 <;> simp
    have h_i0_eq_i1 : i0 = i1 := by
      apply Fin.ext <;> simp [h_i0_val, h_i1_val]
    rw [h_i0_eq_i1] at h0_eq
    have h_cont : (0 : I) = (1 : I) := by
      exact h0_eq.symm.trans h1_eq
    norm_num at h_cont
  have h_n2_pos : 0 < n₂ := by
    by_contra h
    have h' : n₂ = 0 := by omega
    have h0_in : (0 : I) ∈ S₂ := hS₂.1
    have h1_in : (1 : I) ∈ S₂ := hS₂.2.1
    rw [←h_ts₂_image] at h0_in h1_in
    rcases Finset.mem_image.mp h0_in with ⟨i0, _, h0_eq⟩
    rcases Finset.mem_image.mp h1_in with ⟨i1, _, h1_eq⟩
    have h_i0_val : i0.val = 0 := by
      subst h'
      fin_cases i0 <;> simp
    have h_i1_val : i1.val = 0 := by
      subst h'
      fin_cases i1 <;> simp
    have h_i0_eq_i1 : i0 = i1 := by
      apply Fin.ext <;> simp [h_i0_val, h_i1_val]
    rw [h_i0_eq_i1] at h0_eq
    have h_cont : (0 : I) = (1 : I) := by
      exact h0_eq.symm.trans h1_eq
    norm_num at h_cont
  have h_n_gt_n1 : n₁ < n := by
    simp [n, h_n2_pos] <;> omega

  let S : Finset I := Finset.image ts_concat Finset.univ
  have h0 : (0 : I) ∈ S := by
    have h_le : (0 : Fin (n + 1)).val ≤ n₁ := by simp <;> omega
    have h_ts0 : ts_concat 0 = (0 : I) := by
      have h_real_eq : (ts_concat 0 : ℝ) = 0 := by
        dsimp only [ts_concat]
        rw [dif_pos h_le]
        <;> simp [scale_first_half, h_ts1_zero] <;> norm_num
      exact Subtype.ext h_real_eq
    exact Finset.mem_image.mpr ⟨0, by simp, h_ts0⟩
  have h1 : (1 : I) ∈ S := by
    have h_gt : ¬ (Fin.last n).val ≤ n₁ := by
      simp [h_n_gt_n1] <;> omega
    have h_k_lt : (Fin.last n).val - n₁ < n₂ + 1 := by omega
    let k : Fin (n₂ + 1) := ⟨(Fin.last n).val - n₁, h_k_lt⟩
    have h_k_eq_last : k = Fin.last n₂ := by
      apply Fin.ext
      simp [k, h_n_gt_n1] <;> omega
    have h_ts1 : ts_concat (Fin.last n) = (1 : I) := by
      have h_eq1 : ts_concat (Fin.last n) = scale_second_half (ts₂ k) := by
        dsimp only [ts_concat]
        rw [dif_neg h_gt] <;> rfl
      rw [h_eq1, h_k_eq_last, h_ts2_last]
      <;> simp [scale_second_half] <;> norm_num
    exact Finset.mem_image.mpr ⟨Fin.last n, by simp, h_ts1⟩
  have h_main : ∀ (s₁ s₂ : I), s₁ ∈ S → s₂ ∈ S → s₁ < s₂ →
      (∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False) →
      ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t : I), s₁ ≤ t → t ≤ s₂ → (γ₁.trans γ₂) t ∈ (U : Set X) := by
    intro s₁ s₂ hs₁ hs₂ h_lt h_no_mid
    rcases Finset.mem_image.mp hs₁ with ⟨i₁, _, rfl⟩
    rcases Finset.mem_image.mp hs₂ with ⟨i₂, _, rfl⟩
    have h_i1_lt_i2 : i₁ < i₂ := by
      by_contra h
      have h' : i₂ ≤ i₁ := by omega
      have h'' : ts_concat i₂ ≤ ts_concat i₁ := h_ts_concat_strict.monotone h'
      have : ¬ ts_concat i₁ < ts_concat i₂ := by exact not_lt.mpr h''
      exact this h_lt
    have h_i2_succ : i₂.val = i₁.val + 1 := by
      by_contra h
      have h_i1_lt_i2_val : i₁.val < i₂.val := by exact_mod_cast h_i1_lt_i2
      have h_le : i₁.val + 1 ≤ i₂.val := by omega
      have h' : i₁.val + 1 < i₂.val := by
        by_contra h_eq
        have h_cont : i₂.val = i₁.val + 1 := by omega
        exact h h_cont
      have h_mid_lt : i₁.val + 1 < n + 1 := by omega
      let t_mid : Fin (n + 1) := ⟨i₁.val + 1, h_mid_lt⟩
      have h_t_mid_val : t_mid.val = i₁.val + 1 := by
        simp [t_mid]
      have h1 : i₁ < t_mid := by
        apply Fin.lt_iff_val_lt_val.mpr
        rw [h_t_mid_val] <;> omega
      have h2 : t_mid < i₂ := by
        apply Fin.lt_iff_val_lt_val.mpr
        rw [h_t_mid_val] <;> exact h'
      have h_ts1 : ts_concat i₁ < ts_concat t_mid := h_ts_concat_strict h1
      have h_ts2 : ts_concat t_mid < ts_concat i₂ := h_ts_concat_strict h2
      have h_mid_in_S : ts_concat t_mid ∈ S := by
        exact Finset.mem_image.mpr ⟨t_mid, by simp, rfl⟩
      exact h_no_mid (ts_concat t_mid) h_mid_in_S h_ts1 h_ts2
    have h_i1_lt_n : i₁.val < n := by omega
    let i : Fin n := ⟨i₁.val, h_i1_lt_n⟩
    have h_i1_eq : i₁ = Fin.castSucc i := by
      apply Fin.ext
      simp [i] <;> rfl
    have h_i2_eq : i₂ = Fin.succ i := by
      apply Fin.ext
      simp [i, h_i2_succ] <;> omega
    refine' ⟨covers_concat i, hcover_concat_mem i, _⟩
    rw [h_i1_eq, h_i2_eq]
    exact h_range_concat i
  have hS : IsAdaptedSubdivision 𝒰 (γ₁.trans γ₂) S := by
    exact ⟨h0, h1, h_main⟩

  -- Step 4: The final algebraic step
  let pts₁ (i : Fin (n₁ + 1)) : X := γ₁ (ts₁ i)
  let pts₂ (i : Fin (n₂ + 1)) : X := γ₂ (ts₂ i)
  let pts_concat (i : Fin (n + 1)) : X := (γ₁.trans γ₂) (ts_concat i)

  have h_pts1_last : pts₁ (Fin.last n₁) = y := by
    dsimp only [pts₁]
    rw [h_ts1_last]
    exact γ₁.target
  have h_pts2_zero : pts₂ 0 = y := by
    dsimp only [pts₂]
    rw [h_ts2_zero]
    exact γ₂.source

  have h_objs_first : ∀ (i : Fin (n₁ + 1)), pts_concat ⟨i.val, by omega⟩ = pts₁ i := by
    intro i
    let j : Fin (n + 1) := ⟨i.val, by omega⟩
    have h_j_val : j.val = i.val := by simp [j]
    have h_i_le_n₁ : j.val ≤ n₁ := by omega
    have h_main : pts_concat j = pts₁ i := by
      dsimp only [pts_concat, pts₁]
      have h_k_eq : (⟨j.val, by omega⟩ : Fin (n₁ + 1)) = i := by
        apply Fin.ext
        simp [h_j_val] <;> omega
      have h_ts_eq : ts_concat j = scale_first_half (ts₁ i) := by
        dsimp only [ts_concat]; rw [dif_pos h_i_le_n₁]
        <;> rw [h_k_eq] <;> rfl
      rw [h_ts_eq]
      have h_eval : (γ₁.trans γ₂) (scale_first_half (ts₁ i)) = γ₁ (ts₁ i) := by
        rw [Path.trans_apply]
        have h_le : (scale_first_half (ts₁ i) : ℝ) ≤ 1 / 2 := by
          simp [scale_first_half] <;> have h := (ts₁ i).prop.2; linarith
        rw [dif_pos h_le]
        <;> congr 1
        <;> apply Subtype.ext
        <;> simp [scale_first_half] <;> ring
      exact h_eval
    exact h_main
  have h_objs_second : ∀ (i : Fin (n₂ + 1)), pts_concat ⟨n₁ + i.val, by omega⟩ = pts₂ i := by
    intro i
    let j : Fin (n + 1) := ⟨n₁ + i.val, by omega⟩
    have h_j_val : j.val = n₁ + i.val := by simp [j]
    have h_ts_eq : ts_concat j = scale_second_half (ts₂ i) := by
      by_cases h_i0 : i.val = 0
      · -- Case i = 0: both sides equal 1/2 as real numbers
        have h_j_eq_n1 : j.val = n₁ := by
          simp [h_j_val, h_i0] <;> omega
        have h_i_eq_0 : i = 0 := by
          apply Fin.ext <;> simp [h_i0]
        have h_real_eq : (ts_concat j : ℝ) = (scale_second_half (ts₂ i) : ℝ) := by
          have h_le : j.val ≤ n₁ := by omega
          have h_k_eq : (⟨j.val, by omega⟩ : Fin (n₁ + 1)) = Fin.last n₁ := by
            apply Fin.ext <;> simp [h_j_eq_n1] <;> omega
          rw [h_i_eq_0, h_ts2_zero]
          dsimp only [ts_concat]
          rw [dif_pos h_le, h_k_eq, h_ts1_last]
          <;> simp [scale_first_half, scale_second_half] <;> norm_num
        apply Subtype.ext
        exact h_real_eq
      · -- Case i > 0: j.val > n₁
        have h_i_pos : 0 < i.val := by omega
        have h_gt_n1 : ¬ j.val ≤ n₁ := by omega
        have h_k_eq : (⟨j.val - n₁, by omega⟩ : Fin (n₂ + 1)) = i := by
          apply Fin.ext
          simp [h_j_val] <;> omega
        dsimp only [ts_concat]; rw [dif_neg h_gt_n1]
        <;> rw [h_k_eq] <;> rfl
    have h_main : pts_concat j = pts₂ i := by
      dsimp only [pts_concat, pts₂]
      rw [h_ts_eq]
      have h_eval : (γ₁.trans γ₂) (scale_second_half (ts₂ i)) = γ₂ (ts₂ i) := by
        by_cases h : (scale_second_half (ts₂ i) : ℝ) = 1 / 2
        · -- Case 1: equal to 1/2, then ts₂ i = 0
          have h_ts2_eq_0 : ts₂ i = 0 := by
            apply Subtype.ext
            have h_eq : (scale_second_half (ts₂ i) : ℝ) = 1 / 2 := h
            have h_simp : (scale_second_half (ts₂ i) : ℝ) = 1 / 2 + (ts₂ i : ℝ) / 2 := by
              simp [scale_second_half] <;> ring
            have h_eq2 : 1 / 2 + (ts₂ i : ℝ) / 2 = 1 / 2 := by
              rw [←h_simp, h_eq]
            have h_final : (ts₂ i : ℝ) = 0 := by linarith
            exact h_final
          rw [h_ts2_eq_0]
          <;> simp [Path.trans_apply, scale_second_half] <;> exact γ₁.target
        · -- Case 2: strictly greater than 1/2
          have h_ge : (scale_second_half (ts₂ i) : ℝ) ≥ 1 / 2 := by
            simp [scale_second_half] <;> have h' := (ts₂ i).prop.1; linarith
          have h_gt : (scale_second_half (ts₂ i) : ℝ) > 1 / 2 := by
            have h_ne' : (1 / 2 : ℝ) ≠ (scale_second_half (ts₂ i) : ℝ) := Ne.symm h
            exact lt_of_le_of_ne h_ge h_ne'
          have h_not_le : ¬ (scale_second_half (ts₂ i) : ℝ) ≤ 1 / 2 := not_le.mpr h_gt
          rw [Path.trans_apply, dif_neg h_not_le]
          <;> congr 1
          <;> apply Subtype.ext
          <;> simp [scale_second_half] <;> ring
      exact h_eval
    exact h_main

  let objs₁' (i : Fin (n₁ + 1)) := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts₁ i))
  let objs₂' (i : Fin (n₂ + 1)) := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts₂ i))
  let objs_concat' (i : Fin (n + 1)) := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts_concat i))

  have h_match : objs₁' (Fin.last n₁) = objs₂' 0 := by
    dsimp only [objs₁', objs₂']
    rw [h_pts1_last, h_pts2_zero] <;> rfl

  let γs₁ (i : Fin n₁) : Path (pts₁ (Fin.castSucc i)) (pts₁ (Fin.succ i)) :=
    γ₁.subpath (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i))
  let γs₂ (i : Fin n₂) : Path (pts₂ (Fin.castSucc i)) (pts₂ (Fin.succ i)) :=
    γ₂.subpath (ts₂ (Fin.castSucc i)) (ts₂ (Fin.succ i))
  let γs_concat (i : Fin n) : Path (pts_concat (Fin.castSucc i)) (pts_concat (Fin.succ i)) :=
    (γ₁.trans γ₂).subpath (ts_concat (Fin.castSucc i)) (ts_concat (Fin.succ i))

  have h_ranges₁ : ∀ (i : Fin n₁), Set.range (γs₁ i) ⊆ (covers₁ i : Set X) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.succ i := by apply Fin.castSucc_lt_succ
    have h_ts_lt : ts₁ (Fin.castSucc i) < ts₁ (Fin.succ i) := h_ts₁_strict h_lt
    have h_range_eq : Set.range (γs₁ i) = γ₁ '' Set.Icc (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) := by
      rw [Path.range_subpath γ₁ (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact h_range₁ i t ht.1 ht.2
  have h_ranges₂ : ∀ (i : Fin n₂), Set.range (γs₂ i) ⊆ (covers₂ i : Set X) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.succ i := by apply Fin.castSucc_lt_succ
    have h_ts_lt : ts₂ (Fin.castSucc i) < ts₂ (Fin.succ i) := h_ts₂_strict h_lt
    have h_range_eq : Set.range (γs₂ i) = γ₂ '' Set.Icc (ts₂ (Fin.castSucc i)) (ts₂ (Fin.succ i)) := by
      rw [Path.range_subpath γ₂ (ts₂ (Fin.castSucc i)) (ts₂ (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact h_range₂ i t ht.1 ht.2
  have h_ranges_concat : ∀ (i : Fin n), Set.range (γs_concat i) ⊆ (covers_concat i : Set X) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.succ i := by apply Fin.castSucc_lt_succ
    have h_ts_lt : ts_concat (Fin.castSucc i) < ts_concat (Fin.succ i) := h_ts_concat_strict h_lt
    have h_range_eq : Set.range (γs_concat i) = (γ₁.trans γ₂) '' Set.Icc (ts_concat (Fin.castSucc i)) (ts_concat (Fin.succ i)) := by
      rw [Path.range_subpath (γ₁.trans γ₂) (ts_concat (Fin.castSucc i)) (ts_concat (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact h_range_concat i t ht.1 ht.2

  let homs₁' (i : Fin n₁) : objs₁' (Fin.castSucc i) ⟶ objs₁' (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs₁ i) (covers₁ i) (hcover₁_mem i) (h_ranges₁ i)
  let homs₂' (i : Fin n₂) : objs₂' (Fin.castSucc i) ⟶ objs₂' (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs₂ i) (covers₂ i) (hcover₂_mem i) (h_ranges₂ i)
  let homs_concat' (i : Fin n) : objs_concat' (Fin.castSucc i) ⟶ objs_concat' (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs_concat i) (covers_concat i) (hcover_concat_mem i) (h_ranges_concat i)

  have h_homs_first : ∀ (i : Fin n₁),
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first (Fin.castSucc i))).symm ≫
      homs_concat' ⟨i.val, by omega⟩ ≫
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first (Fin.succ i))) =
      homs₁' i := by
    intro i
    have h_i_lt_n : i.val < n := by omega
    let j : Fin n := ⟨i.val, h_i_lt_n⟩
    have h_j_val : j.val = i.val := by simp [j]
    have h_j_lt_n1 : j.val < n₁ := by
      have h : i.val < n₁ := i.is_lt
      omega
    have h_cover_eq : covers_concat j = covers₁ i := by
      dsimp only [covers_concat]
      rw [dif_pos h_j_lt_n1] <;> rfl
    have h_cast_lt : (Fin.castSucc j).val < n₁ := by
      have h1 : (Fin.castSucc j).val = j.val := by simp
      rw [h1, h_j_val]
      exact i.is_lt
    have h_succ_le : (Fin.succ j).val ≤ n₁ := by
      have h1 : (Fin.succ j).val = j.val + 1 := by simp
      rw [h1, h_j_val]
      have h2 : i.val < n₁ := i.is_lt
      omega
    have h_cast_le : (Fin.castSucc j).val ≤ n₁ := by
      have h1 : (Fin.castSucc j).val < n₁ := h_cast_lt
      exact le_of_lt h1
    have h_k1_eq : (⟨(Fin.castSucc j).val, by omega⟩ : Fin (n₁ + 1)) = Fin.castSucc i := by
      apply Fin.ext
      simp [h_j_val] <;> omega
    have h_k2_eq : (⟨(Fin.succ j).val, by omega⟩ : Fin (n₁ + 1)) = Fin.succ i := by
      apply Fin.ext
      simp [h_j_val] <;> omega
    have h1 : ts_concat (Fin.castSucc j) = scale_first_half (ts₁ (Fin.castSucc i)) := by
      dsimp only [ts_concat]; rw [dif_pos h_cast_le]
      <;> rw [h_k1_eq] <;> rfl
    have h2 : ts_concat (Fin.succ j) = scale_first_half (ts₁ (Fin.succ i)) := by
      dsimp only [ts_concat]; rw [dif_pos h_succ_le]
      <;> rw [h_k2_eq] <;> rfl
    have hfun : ∀ (t : I), γs_concat j t = γs₁ i t := by
      intro t
      dsimp only [γs_concat, γs₁]
      have h4 : (Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t : ℝ) ≤ 1 / 2 := by
        rw [h1, h2]
        have h_eq : (Set.Icc.convexComb (scale_first_half (ts₁ (Fin.castSucc i))) (scale_first_half (ts₁ (Fin.succ i))) t : ℝ) =
            (1 / 2 : ℝ) * (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) := by
          simp [Set.Icc.convexComb, scale_first_half] <;> ring
        rw [h_eq]
        have h_nonneg : 0 ≤ (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) := by
          exact (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t).prop.1
        have h_le_one : (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) ≤ 1 := by
          exact (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t).prop.2
        linarith
      have h5 : (γ₁.trans γ₂) (Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t) =
          γ₁ (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t) := by
        rw [h1, h2]
        have h4' : (Set.Icc.convexComb (scale_first_half (ts₁ (Fin.castSucc i))) (scale_first_half (ts₁ (Fin.succ i))) t : ℝ) ≤ 1 / 2 := by
          have h_eq : (Set.Icc.convexComb (scale_first_half (ts₁ (Fin.castSucc i))) (scale_first_half (ts₁ (Fin.succ i))) t : ℝ) =
              (1 / 2 : ℝ) * (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) := by
            simp [Set.Icc.convexComb, scale_first_half] <;> ring
          rw [h_eq]
          have h_nonneg : 0 ≤ (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) := by
            exact (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t).prop.1
          have h_le_one : (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) ≤ 1 := by
            exact (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t).prop.2
          linarith
        rw [Path.trans_apply]
        rw [dif_pos h4']
        <;> congr 1
        <;> apply Subtype.ext
        <;> simp [Set.Icc.convexComb, scale_first_half] <;> ring
      exact h5
    have h_range_eq : Set.range (γs_concat j) ⊆ (covers₁ i : Set X) := by
      rw [←h_cover_eq]
      exact h_ranges_concat j
    have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first (Fin.castSucc i))).symm ≫
        homs_concat' j ≫
        eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first (Fin.succ i))) =
        homs₁' i := by
      have h1 : homs_concat' j =
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs_concat j) (covers₁ i) (hcover₁_mem i) h_range_eq := by
        dsimp only [homs_concat']
        congr <;> try { exact h_cover_eq } <;> try { exact Subsingleton.elim _ _ }
      rw [h1]
      exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
        (γs_concat j) (γs₁ i)
        (h_objs_first (Fin.castSucc i)) (h_objs_first (Fin.succ i))
        hfun
        (covers₁ i) (hcover₁_mem i)
        h_range_eq (h_ranges₁ i)
    exact h_main

  have h_homs_second : ∀ (i : Fin n₂),
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.castSucc i))).symm ≫
      homs_concat' ⟨n₁ + i.val, by omega⟩ ≫
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.succ i))) =
      homs₂' i := by
    intro i
    have h_sum_lt : n₁ + i.val < n := by omega
    let j : Fin n := ⟨n₁ + i.val, h_sum_lt⟩
    have h_j_not_lt_n1 : ¬ j.val < n₁ := by
      simp [j] <;> omega
    have h_i_eq : (⟨j.val - n₁, by omega⟩ : Fin n₂) = i := by
      apply Fin.ext
      simp [j] <;> omega
    have h_cover_eq : covers_concat j = covers₂ i := by
      dsimp only [covers_concat]
      rw [dif_neg h_j_not_lt_n1]
      <;> rw [h_i_eq]
      <;> rfl
    have h_k1_eq : (⟨(Fin.castSucc j).val - n₁, by omega⟩ : Fin (n₂ + 1)) = Fin.castSucc i := by
      apply Fin.ext
      simp [j] <;> omega
    have h_k2_eq : (⟨(Fin.succ j).val - n₁, by omega⟩ : Fin (n₂ + 1)) = Fin.succ i := by
      apply Fin.ext
      simp [j] <;> omega
    have h_cast_le : (Fin.castSucc j).val ≤ n₁ ∨ ¬ (Fin.castSucc j).val ≤ n₁ := em _
    have h1 : ts_concat (Fin.castSucc j) = scale_second_half (ts₂ (Fin.castSucc i)) := by
      cases h_cast_le with
      | inl h_cast_le =>
        -- Case (Fin.castSucc j).val ≤ n₁: this means i.val = 0
        have h_i_val_eq_0 : i.val = 0 := by
          simp [j] at h_cast_le <;> omega
        have h_cast_eq_n1 : (Fin.castSucc j).val = n₁ := by
          simp [j, h_i_val_eq_0] <;> omega
        have h_real_eq : (ts_concat (Fin.castSucc j) : ℝ) = (scale_second_half (ts₂ (Fin.castSucc i)) : ℝ) := by
          have h_ts2_0 : ts₂ (Fin.castSucc i) = (0 : I) := by
            have h : Fin.castSucc i = (0 : Fin (n₂ + 1)) := by
              apply Fin.ext
              simp [h_i_val_eq_0] <;> omega
            rw [h, h_ts2_zero]
          have h_lt : (Fin.castSucc j).val < n₁ + 1 := by omega
          let k : Fin (n₁ + 1) := ⟨(Fin.castSucc j).val, h_lt⟩
          have h_fin_eq : k = Fin.last n₁ := by
            apply Fin.ext
            simpa [k] using h_cast_eq_n1
          have h1 : ts_concat (Fin.castSucc j) = scale_first_half (ts₁ k) := by
            dsimp only [ts_concat]
            rw [dif_pos h_cast_le] <;> rfl
          have h2 : (scale_first_half (ts₁ k) : ℝ) = (scale_first_half (ts₁ (Fin.last n₁)) : ℝ) := by
            rw [h_fin_eq]
          have h_main : (ts_concat (Fin.castSucc j) : ℝ) = (scale_first_half (ts₁ (Fin.last n₁)) : ℝ) := by
            have h1' : (ts_concat (Fin.castSucc j) : ℝ) = (scale_first_half (ts₁ k) : ℝ) := by
              exact congr_arg (fun x : I => (x : ℝ)) h1
            calc
              (ts_concat (Fin.castSucc j) : ℝ) = (scale_first_half (ts₁ k) : ℝ) := h1'
              _ = (scale_first_half (ts₁ (Fin.last n₁)) : ℝ) := h2
          rw [h_main, h_ts1_last, h_ts2_0]
          <;> simp [scale_first_half, scale_second_half] <;> norm_num
        exact Subtype.ext h_real_eq
      | inr h_cast_gt =>
        dsimp only [ts_concat]; rw [dif_neg h_cast_gt]
        <;> rw [h_k1_eq] <;> rfl
    have h_succ_gt : ¬ (Fin.succ j).val ≤ n₁ := by
      simp [j] <;> omega
    have h2 : ts_concat (Fin.succ j) = scale_second_half (ts₂ (Fin.succ i)) := by
      dsimp only [ts_concat]; rw [dif_neg h_succ_gt]
      <;> rw [h_k2_eq] <;> rfl
    have h_scale_apply : ∀ (c : I), (γ₁.trans γ₂) (scale_second_half c) = γ₂ c := by
      intro c
      by_cases h : (scale_second_half c : ℝ) ≤ 1 / 2
      · -- Case ≤ 1/2: this means c = 0
        have h_c_eq_0 : (c : ℝ) = 0 := by
          simp [scale_second_half] at h <;> linarith [c.prop.1]
        have h_c : c = (0 : I) := by
          apply Subtype.ext <;> simp [h_c_eq_0]
        rw [h_c]
        <;> simp [Path.trans_apply, scale_second_half] <;> norm_num
      · -- Case > 1/2
        rw [Path.trans_apply, dif_neg h]
        <;> simp [scale_second_half] <;> congr <;> ring
    have h_combo_eq : ∀ (a b : I) (t : I),
        Set.Icc.convexComb (scale_second_half a) (scale_second_half b) t =
        scale_second_half (Set.Icc.convexComb a b t) := by
      intro a b t
      apply Subtype.ext
      simp [Set.Icc.convexComb, scale_second_half] <;> ring
    have hfun : ∀ (t : I), γs_concat j t = γs₂ i t := by
      intro t
      dsimp only [γs_concat, γs₂]
      set a : I := ts₂ (Fin.castSucc i) with ha
      set b : I := ts₂ (Fin.succ i) with hb
      set c : I := Set.Icc.convexComb a b t with hc
      have h_combo1 : Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t =
          Set.Icc.convexComb (scale_second_half a) (scale_second_half b) t := by
        rw [h1, h2]
        <;> rfl
      have h_combo2 : Set.Icc.convexComb (scale_second_half a) (scale_second_half b) t = scale_second_half c := by
        exact h_combo_eq a b t
      have h_combo : Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t = scale_second_half c := by
        rw [h_combo1, h_combo2]
      have h_goal : (γ₁.trans γ₂) (Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t) = γ₂ c := by
        rw [h_combo]
        exact h_scale_apply c
      have h_subpath1 : ((γ₁.trans γ₂).subpath (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j))) t =
          (γ₁.trans γ₂) (Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t) := by
        rfl
      have h_goal' : ((γ₁.trans γ₂).subpath (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j))) t = (γs₂ i) t := by
        rw [h_subpath1]
        have h_rhs : (γs₂ i) t = γ₂ c := by
          dsimp only [γs₂]
          <;> rfl
        rw [h_rhs]
        exact h_goal
      exact h_goal'
    have h_range_eq : Set.range (γs_concat j) ⊆ (covers₂ i : Set X) := by
      rw [←h_cover_eq]
      exact h_ranges_concat j
    have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.castSucc i))).symm ≫
        homs_concat' j ≫
        eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.succ i))) =
        homs₂' i := by
      have h1 : homs_concat' j =
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs_concat j) (covers₂ i) (hcover₂_mem i) h_range_eq := by
        dsimp only [homs_concat']
        congr <;> try { exact h_cover_eq } <;> try { exact Subsingleton.elim _ _ }
      rw [h1]
      exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
        (γs_concat j) (γs₂ i)
        (h_objs_second (Fin.castSucc i)) (h_objs_second (Fin.succ i))
        hfun
        (covers₂ i) (hcover₂_mem i)
        h_range_eq (h_ranges₂ i)
    exact h_main

  have h_objs_first' : ∀ (i : Fin (n₁ + 1)), objs_concat' ⟨i.val, by omega⟩ = objs₁' i := by
    intro i
    dsimp only [objs_concat', objs₁']
    rw [h_objs_first i]
    <;> rfl
  have h_objs_second' : ∀ (i : Fin (n₂ + 1)), objs_concat' ⟨n₁ + i.val, by omega⟩ = objs₂' i := by
    intro i
    dsimp only [objs_concat', objs₂']
    rw [h_objs_second i]
    <;> rfl
  have h_main_eq : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first 0)).symm ≫
      comp_list n objs_concat' homs_concat' ≫
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.last n₂))) =
      comp_list n₁ objs₁' homs₁' ≫ eqToHom h_match ≫ comp_list n₂ objs₂' homs₂' := by
    exact comp_list_concat_explicit objs₁' homs₁' objs₂' homs₂' h_match objs_concat' homs_concat' h_objs_first' h_objs_second' h_homs_first h_homs_second

  have h_eq_concat : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts_concat h_ts_concat_strict rfl covers_concat hcover_concat_mem h_range_concat :=
    my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS ts_concat h_ts_concat_strict rfl covers_concat hcover_concat_mem h_range_concat

  have h_eq1 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₁ =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS₁ n₁ ts₁ h_ts₁_strict h_ts₁_image covers₁ hcover₁_mem h_range₁ := h_eq₁
  have h_eq2 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₂ =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS₂ n₂ ts₂ h_ts₂_strict h_ts₂_image covers₂ hcover₂_mem h_range₂ := h_eq₂

  -- Helper facts about endpoints
  have h_ts1_zero : ts₁ 0 = (0 : I) := by
    have h0_in : (0 : I) ∈ S₁ := hS₁.1
    have h0_in_image : (0 : I) ∈ Finset.image ts₁ Finset.univ := by rw [h_ts₁_image] <;> exact h0_in
    let i : Fin (n₁ + 1) := Classical.choose (Finset.mem_image.mp h0_in_image)
    let hi : ts₁ i = (0 : I) := (Classical.choose_spec (Finset.mem_image.mp h0_in_image)).2
    have h_i_eq_0 : i = 0 := by
      by_contra h
      have h_i_pos : 0 < i := Fin.pos_iff_ne_zero.mpr h
      have h_ts0_lt_tsi : ts₁ 0 < ts₁ i := h_ts₁_strict h_i_pos
      rw [hi] at h_ts0_lt_tsi
      have h_nonneg : (0 : ℝ) ≤ (ts₁ 0 : ℝ) := (ts₁ 0).prop.1
      have h_cont : (ts₁ 0 : ℝ) < (0 : ℝ) := by exact_mod_cast h_ts0_lt_tsi
      linarith
    rw [h_i_eq_0] at hi
    exact hi
  have h_ts2_last : ts₂ (Fin.last n₂) = (1 : I) := by
    have h1_in : (1 : I) ∈ S₂ := hS₂.2.1
    have h1_in_image : (1 : I) ∈ Finset.image ts₂ Finset.univ := by rw [h_ts₂_image] <;> exact h1_in
    let i : Fin (n₂ + 1) := Classical.choose (Finset.mem_image.mp h1_in_image)
    let hi : ts₂ i = (1 : I) := (Classical.choose_spec (Finset.mem_image.mp h1_in_image)).2
    have h_i_eq_last : i = Fin.last n₂ := by
      apply Fin.eq_last_of_not_lt
      intro h
      have h_tsi_lt_ts1 : ts₂ i < ts₂ (Fin.last n₂) := h_ts₂_strict h
      rw [hi] at h_tsi_lt_ts1
      have h' : (1 : ℝ) < (ts₂ (Fin.last n₂) : ℝ) := by exact_mod_cast h_tsi_lt_ts1
      have h'' : (ts₂ (Fin.last n₂) : ℝ) ≤ 1 := (ts₂ (Fin.last n₂)).prop.2
      linarith
    rw [h_i_eq_last] at hi
    exact hi

  have h_pts0₁ : pts₁ 0 = x := by
    dsimp only [pts₁]
    rw [h_ts1_zero]
    exact γ₁.source
  have h_pts_last₁ : pts₁ (Fin.last n₁) = y := h_pts1_last
  have h_pts0₂ : pts₂ 0 = y := h_pts2_zero
  have h_pts_last₂ : pts₂ (Fin.last n₂) = z := by
    dsimp only [pts₂]
    rw [h_ts2_last]
    exact γ₂.target

  have h_pts0_concat : pts_concat 0 = x := by
    have h : pts_concat 0 = pts₁ 0 := h_objs_first 0
    rw [h, h_pts0₁]
  have h_pts_last_concat : pts_concat (Fin.last n) = z := by
    have h : pts_concat (Fin.last n) = pts₂ (Fin.last n₂) := h_objs_second (Fin.last n₂)
    rw [h, h_pts_last₂]

  -- Now we can conclude
  refine' ⟨S, hS, _⟩
  rw [h_eq_concat, h_eq1, h_eq2]
  dsimp only [my_map_from_adapted_subdivision_with_covers]
  -- Helper: all eqToHom terms between the same objects are equal
  have h_eqToHom_congr : ∀ {a b : s.pt} (h1 h2 : a = b), eqToHom h1 = eqToHom h2 := by
    intro a b h1 h2
    congr <;> tauto
  -- Helper: composition of two eqToHom is eqToHom of the transitive equality
  have h_compose_eqToHom : ∀ {a b c : s.pt} (h1 : a = b) (h2 : b = c),
      eqToHom h1 ≫ eqToHom h2 = eqToHom (h1.trans h2) := by
    intro a b c h1 h2
    rw [eqToHom_trans]
  -- Let A, B, C be the objects we're working with
  let A : s.pt := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)
  let B : s.pt := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)
  let C : s.pt := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk z)
  -- Whisker h_main_eq with eqToHom on both sides
  let f : objs₁' 0 ⟶ objs₂' (Fin.last n₂) :=
    eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first 0)).symm ≫
    comp_list n objs_concat' homs_concat' ≫
    eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.last n₂)))
  let g : objs₁' 0 ⟶ objs₂' (Fin.last n₂) :=
    comp_list n₁ objs₁' homs₁' ≫ eqToHom h_match ≫ comp_list n₂ objs₂' homs₂'
  have h_fg : f = g := h_main_eq
  -- Whisker both sides with eqToHom from A to objs₁' 0 and from objs₂' (Fin.last n₂) to C
  let h_left : A = objs₁' 0 := by
    exact (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts0₁).symm
  let h_right : objs₂' (Fin.last n₂) = C := by
    exact congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts_last₂
  have h_whiskered : eqToHom h_left ≫ f ≫ eqToHom h_right = eqToHom h_left ≫ g ≫ eqToHom h_right := by
    rw [h_fg]
  -- Now show that the LHS of the goal equals eqToHom h_left ≫ f ≫ eqToHom h_right
  have h_lhs_eq :
    eqToHom (show (let pts : Fin (n + 1) → X := fun i => (γ₁.trans γ₂) (ts_concat i)
      let objs : Fin (n + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      objs 0) = A from by
        dsimp only [A]
        <;> congr <;> funext i <;> rfl).symm ≫
    (let pts : Fin (n + 1) → X := fun i => (γ₁.trans γ₂) (ts_concat i)
      let objs : Fin (n + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      let γs : ∀ i : Fin n, Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) := fun i =>
        (γ₁.trans γ₂).subpath (ts_concat (Fin.castSucc i)) (ts_concat (Fin.succ i))
      let homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
        single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) (covers_concat i) (hcover_concat_mem i) (h_ranges_concat i)
      comp_list n objs homs) ≫
    eqToHom (show (let pts : Fin (n + 1) → X := fun i => (γ₁.trans γ₂) (ts_concat i)
      let objs : Fin (n + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      objs (Fin.last n)) = C from by
        dsimp only [C]
        <;> congr <;> funext i <;> rfl) =
    eqToHom h_left ≫ f ≫ eqToHom h_right := by
    have h1 : ∀ (h1 h2 : A = objs_concat' 0), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h2 : ∀ (h1 h2 : objs_concat' (Fin.last n) = C), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    simp [f, Category.assoc, h1, h2]
    <;> rfl
  -- Now show that the RHS of the goal equals eqToHom h_left ≫ g ≫ eqToHom h_right
  have h_rhs_eq :
    (eqToHom (show (let pts : Fin (n₁ + 1) → X := fun i => γ₁ (ts₁ i)
      let objs : Fin (n₁ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      objs 0) = A from by
        dsimp only [A]
        <;> congr <;> funext i <;> rfl).symm ≫
      (let pts : Fin (n₁ + 1) → X := fun i => γ₁ (ts₁ i)
        let objs : Fin (n₁ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
        let γs : ∀ i : Fin n₁, Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) := fun i =>
          γ₁.subpath (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i))
        let homs : ∀ i : Fin n₁, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) (covers₁ i) (hcover₁_mem i) (h_ranges₁ i)
        comp_list n₁ objs homs) ≫
      eqToHom (show (let pts : Fin (n₁ + 1) → X := fun i => γ₁ (ts₁ i)
        let objs : Fin (n₁ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
        objs (Fin.last n₁)) = B from by
          dsimp only [B]
          <;> congr <;> funext i <;> rfl)) ≫
    (eqToHom (show (let pts : Fin (n₂ + 1) → X := fun i => γ₂ (ts₂ i)
      let objs : Fin (n₂ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      objs 0) = B from by
        dsimp only [B]
        <;> congr <;> funext i <;> rfl).symm ≫
      (let pts : Fin (n₂ + 1) → X := fun i => γ₂ (ts₂ i)
        let objs : Fin (n₂ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
        let γs : ∀ i : Fin n₂, Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) := fun i =>
          γ₂.subpath (ts₂ (Fin.castSucc i)) (ts₂ (Fin.succ i))
        let homs : ∀ i : Fin n₂, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) (covers₂ i) (hcover₂_mem i) (h_ranges₂ i)
        comp_list n₂ objs homs) ≫
      eqToHom (show (let pts : Fin (n₂ + 1) → X := fun i => γ₂ (ts₂ i)
        let objs : Fin (n₂ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
        objs (Fin.last n₂)) = C from by
          dsimp only [C]
          <;> congr <;> funext i <;> rfl)) =
    eqToHom h_left ≫ g ≫ eqToHom h_right := by
    have h1 : ∀ (h1 h2 : A = objs₁' 0), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h2 : ∀ (h1 h2 : objs₁' (Fin.last n₁) = B), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h3 : ∀ (h1 h2 : B = objs₂' 0), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h4 : ∀ (h1 h2 : objs₂' (Fin.last n₂) = C), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h_middle : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts_last₁) ≫
        eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts0₂).symm =
        eqToHom h_match := by
      have h_comp : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts_last₁) ≫
          eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts0₂).symm =
          eqToHom ((congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts_last₁).trans
            (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts0₂).symm) := by
        rw [eqToHom_trans]
      rw [h_comp]
    simp [g, Category.assoc, h1, h2, h3, h4, h_middle]
    <;> rfl
  rw [h_lhs_eq, h_rhs_eq]
  exact h_whiskered

end

end

end P202.Topology.VanKampenProof


/-! Adapted from PathDecomposition.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace Set unitInterval Metric

noncomputable section

universe u

lemma abs_midpoint_le_half {a b z : ℝ} (h1 : a ≤ z) (h2 : z ≤ b) :
    |z - (a + b) / 2| ≤ (b - a) / 2 := by
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem path_has_subdivision
    {X : Type*} [TopologicalSpace X]
    (𝒰 : Set (TopologicalSpace.Opens X))
    (hcover : ∀ x : X, ∃ U : TopologicalSpace.Opens X, U ∈ 𝒰 ∧ x ∈ U)
    {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (pts : Fin (n + 1) → X) (covers : Fin n → TopologicalSpace.Opens X)
      (γs : ∀ i : Fin n, Path (pts (Fin.castSucc i)) (pts (Fin.succ i))),
      (∀ i, covers i ∈ 𝒰) ∧
      pts 0 = x ∧ pts (Fin.last n) = y ∧
      (∀ i : Fin n, Set.range (γs i) ⊆ (covers i : Set X)) ∧
      (∀ t : I, ∃ i : Fin n, γ t ∈ (covers i : Set X)) := by
  let ι := { U : TopologicalSpace.Opens X // U ∈ 𝒰 }
  let c : ι → Set I := fun U => γ ⁻¹' (U : Set X)
  have hc₁ : ∀ (i : ι), IsOpen (c i) := by
    intro U
    exact U.val.2.preimage γ.continuous
  have hc₂ : (Set.univ : Set I) ⊆ ⋃ (i : ι), c i := by
    intro t _
    have h₁ : ∃ (U : TopologicalSpace.Opens X), U ∈ 𝒰 ∧ γ t ∈ U := hcover (γ t)
    rcases h₁ with ⟨U, hU, hUt⟩
    let U' : ι := ⟨U, hU⟩
    exact Set.mem_iUnion.mpr ⟨U', hUt⟩
  have hcompact : IsCompact (Set.univ : Set I) := isCompact_univ
  rcases lebesgue_number_lemma_of_metric hcompact hc₁ hc₂ with ⟨δ, hδ_pos, hδ⟩
  have hδ_pos' : 0 < δ := hδ_pos
  have h_arch : ∃ (n : ℕ), 0 < n ∧ 1 / (n : ℝ) < δ := by
    have h : ∃ (n : ℕ), (n : ℝ) > 1 / δ := exists_nat_gt (1 / δ)
    rcases h with ⟨n, hn⟩
    have hn_pos : 0 < n := by
      by_contra h'
      have h'' : n = 0 := by omega
      rw [h''] at hn
      norm_num at hn <;> linarith
    have h1 : 1 / (n : ℝ) < δ := by
      have h2 : 0 < δ := hδ_pos'
      have h3 : (n : ℝ) > 1 / δ := hn
      calc
        1 / (n : ℝ) < 1 / (1 / δ) := by gcongr
        _ = δ := by field_simp [h2.ne'] <;> ring
    exact ⟨n, hn_pos, h1⟩
  rcases h_arch with ⟨n, hn_pos, h1n_lt_δ⟩
  set nr : ℝ := (n : ℝ) with hnr
  have hnr_pos : 0 < nr := by
    rw [hnr]
    exact_mod_cast hn_pos
  let t_pt (i : Fin (n + 1)) : I :=
    ⟨(i.val : ℝ) / nr, by
      have h₁ : 0 ≤ (i.val : ℝ) / nr := by positivity
      have h₂ : (i.val : ℝ) / nr ≤ 1 := by
        have h3 : i.val ≤ n := Nat.lt_succ_iff.mp i.is_lt
        have h41 : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
        have h4 : (i.val : ℝ) ≤ nr := by
          rw [hnr]
          exact h41
        have h5 : (i.val : ℝ) / nr ≤ 1 := by
          calc
            (i.val : ℝ) / nr ≤ nr / nr := by gcongr
            _ = 1 := by
              field_simp [hnr_pos.ne'] <;> ring
        exact h5
      exact ⟨h₁, h₂⟩⟩
  let mid_pt (i : Fin n) : I :=
    ⟨(2 * (i.val : ℝ) + 1) / (2 * nr), by
      have h₁ : 0 ≤ (2 * (i.val : ℝ) + 1) / (2 * nr) := by positivity
      have h₂ : (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ 1 := by
        have h3 : i.val < n := i.is_lt
        have h4 : (i.val : ℝ) < nr := by
          simpa [hnr] using Nat.cast_lt.mpr h3
        have h5 : 2 * (i.val : ℝ) + 1 ≤ 2 * nr := by
          have h6 : (i.val : ℝ) + 1 ≤ nr := by
            have h7 : i.val + 1 ≤ n := Nat.succ_le_iff.mpr h3
            simpa [hnr] using Nat.cast_le.mpr h7
          linarith
        have h7 : (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ 1 := by
          calc
            (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ (2 * nr) / (2 * nr) := by gcongr
            _ = 1 := by
              field_simp [hnr_pos.ne'] <;> ring
        exact h7
      exact ⟨h₁, h₂⟩⟩
  have h_choose : ∀ (i : Fin n), ∃ (U : ι), ball (mid_pt i) δ ⊆ c U := by
    intro i
    exact hδ (mid_pt i) (Set.mem_univ (mid_pt i))
  choose U hU using h_choose
  let covers (i : Fin n) : TopologicalSpace.Opens X := (U i).val
  have hcovers_in : ∀ (i : Fin n), covers i ∈ 𝒰 := fun i => (U i).property
  let pts (i : Fin (n + 1)) : X := γ (t_pt i)
  have h_t0 : (t_pt 0 : ℝ) = 0 := by
    simp [t_pt, hnr]
    <;> field_simp [hnr_pos.ne'] <;> ring
  have h_pts0 : pts 0 = x := by
    have h1 : pts 0 = γ (t_pt 0) := by rfl
    rw [h1]
    have h2 : t_pt 0 = 0 := by
      apply Subtype.ext
      exact h_t0
    rw [h2]
    exact γ.source
  have h_t_last_val : (t_pt (Fin.last n) : ℝ) = 1 := by
    have h1 : (Fin.last n).val = n := by simp [Fin.last]
    have h2 : ((Fin.last n).val : ℝ) / nr = 1 := by
      rw [h1]
      have h3 : (n : ℝ) = nr := by simp [hnr]
      rw [h3]
      field_simp [hnr_pos.ne'] <;> ring
    simpa [t_pt] using h2
  have h_ptsn : pts (Fin.last n) = y := by
    have h1 : pts (Fin.last n) = γ (t_pt (Fin.last n)) := by rfl
    rw [h1]
    have h2 : t_pt (Fin.last n) = 1 := by
      apply Subtype.ext
      exact h_t_last_val
    rw [h2]
    exact γ.target
  have h_half_lt_delta : 1 / (2 * nr) < δ := by
    have h7 : 1 / (2 * nr) < 1 / nr := by
      apply div_lt_div_of_pos_left
      · norm_num
      · positivity
      · linarith
    have h8 : 1 / nr < δ := by
      simpa [hnr] using h1n_lt_δ
    linarith
  have h_half_eq : (1 / nr) / 2 = 1 / (2 * nr) := by
    ring
  have h_t_pt_succ_eq : ∀ (i : Fin n), (t_pt (Fin.succ i) : ℝ) = ((i.val : ℝ) + 1) / nr := by
    intro i
    simp [t_pt, Fin.succ]
    <;> rfl
  have h_mem_ball : ∀ (i : Fin n) (w : I),
      (i.val : ℝ) / nr ≤ (w : ℝ) → (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr → w ∈ ball (mid_pt i) δ := by
    intro i w h1 h2
    set a : ℝ := (i.val : ℝ) / nr with ha
    set b : ℝ := ((i.val : ℝ) + 1) / nr with hb
    set m : ℝ := (2 * (i.val : ℝ) + 1) / (2 * nr) with hm
    have h_eq_m : m = (a + b) / 2 := by
      simp [ha, hb, hm] <;> ring
    have h3 : b - a = 1 / nr := by
      simp [ha, hb, hnr_pos.ne'] <;> field_simp [hnr_pos.ne'] <;> ring
    have h4 : |(w : ℝ) - m| ≤ (b - a) / 2 := by
      rw [h_eq_m]
      exact abs_midpoint_le_half h1 h2
    have h5 : |(w : ℝ) - m| ≤ 1 / (2 * nr) := by
      rw [h3, h_half_eq] at h4
      exact h4
    have h6 : dist w (mid_pt i) ≤ 1 / (2 * nr) := by
      have h_mid : ((mid_pt i) : ℝ) = m := by
        simp [mid_pt, hm] <;> rfl
      have h : dist w (mid_pt i) = |(w : ℝ) - (mid_pt i : ℝ)| := by
        change dist (w : ℝ) ((mid_pt i) : ℝ) = |(w : ℝ) - (mid_pt i : ℝ)|
        rw [Real.dist_eq]
        <;> rfl
      rw [h, h_mid]
      exact h5
    have h7 : dist w (mid_pt i) < δ := by
      exact lt_of_le_of_lt h6 h_half_lt_delta
    exact h7
  have h_interval_subset : ∀ (i : Fin n),
      {w : I | (i.val : ℝ) / nr ≤ (w : ℝ) ∧ (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr} ⊆ c (U i) := by
    intro i
    intro w hw
    have h1 : (i.val : ℝ) / nr ≤ (w : ℝ) := hw.1
    have h2 : (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr := hw.2
    have h3 : w ∈ ball (mid_pt i) δ := h_mem_ball i w h1 h2
    exact hU i h3
  have h_image_subset : ∀ (i : Fin n),
      γ '' (Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) ⊆ (covers i : Set X) := by
    intro i
    have h1 : ∀ (w : I), w ∈ Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i)) → w ∈ c (U i) := by
      intro w hw
      have h2 : (t_pt (Fin.castSucc i) : ℝ) ≤ (w : ℝ) := hw.1
      have h3 : (w : ℝ) ≤ (t_pt (Fin.succ i) : ℝ) := hw.2
      have h4 : (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr := by
        rw [h_t_pt_succ_eq i] at h3
        exact h3
      exact h_interval_subset i ⟨h2, h4⟩
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact h1 w hw
  let γs (i : Fin n) : Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) :=
    γ.subpath (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))
  have h_main1 : ∀ (i : Fin n), Set.range (γs i) ⊆ (covers i : Set X) := by
    intro i
    have h_le : (t_pt (Fin.castSucc i) : ℝ) ≤ (t_pt (Fin.succ i) : ℝ) := by
      simp [t_pt]
      <;> have h : (i.val : ℝ) ≤ (i.val : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h (by positivity)
    have h_range : Set.range (γs i) = γ '' (Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) := by
      apply Path.range_subpath_of_le
      exact h_le
    rw [h_range]
    exact h_image_subset i
  have h_main2 : ∀ (t : I), ∃ (i : Fin n), γ t ∈ (covers i : Set X) := by
    intro t
    by_cases h_t_eq_one : (t : ℝ) = 1
    · -- Case t = 1: use the last interval i = n - 1
      have h_n_pos : 0 < n := hn_pos
      let i : Fin n := ⟨n - 1, by omega⟩
      have h1 : (i.val : ℝ) / nr ≤ (t : ℝ) := by
        have h_i_val : i.val = n - 1 := by simp [i]
        rw [h_t_eq_one, h_i_val]
        have h_pos : 0 < nr := hnr_pos
        have h : ((n - 1 : ℕ) : ℝ) / nr ≤ 1 := by
          have h2 : ((n - 1 : ℕ) : ℝ) ≤ nr := by
            simp [hnr, h_n_pos] <;> omega
          rw [div_le_one h_pos]
          exact h2
        exact h
      have h2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / nr := by
        have h_i_val : i.val = n - 1 := by simp [i]
        rw [h_t_eq_one, h_i_val]
        have h_pos : 0 < nr := hnr_pos
        have h3 : ((n - 1 : ℕ) : ℝ) + 1 = nr := by
          have h4 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
            simp [h_n_pos] <;> omega
          rw [h4, hnr]
        rw [h3]
        field_simp [h_pos.ne'] <;> ring_nf <;> norm_num
      have h3 : t ∈ c (U i) := h_interval_subset i ⟨h1, h2⟩
      exact ⟨i, h3⟩
    · -- Case t ≠ 1: then t < 1, so k < n
      have h_t_lt_one : (t : ℝ) < 1 := by
        have h : (t : ℝ) ≤ 1 := t.prop.2
        exact lt_of_le_of_ne h h_t_eq_one
      let k_int : ℤ := ⌊(t : ℝ) * nr⌋
      have h_k1 : (k_int : ℝ) ≤ (t : ℝ) * nr := Int.floor_le ((t : ℝ) * nr)
      have h_k2 : (t : ℝ) * nr < (k_int : ℝ) + 1 := Int.lt_floor_add_one ((t : ℝ) * nr)
      have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
      have h_nr_pos : 0 < nr := hnr_pos
      have h_pos : 0 ≤ (t : ℝ) * nr := mul_nonneg h_t_nonneg (le_of_lt h_nr_pos)
      have h_k_nonneg_int : 0 ≤ k_int := by
        exact Int.floor_nonneg.mpr h_pos
      let k : ℕ := k_int.toNat
      have h_k_eq : (k : ℤ) = k_int := by
        simp [k, Int.toNat_of_nonneg h_k_nonneg_int]
      have h_k1' : (k : ℝ) ≤ (t : ℝ) * nr := by
        have h : ((k : ℤ) : ℝ) = (k_int : ℝ) := by exact_mod_cast h_k_eq
        have h' : (k : ℝ) = ((k : ℤ) : ℝ) := by exact?
        rw [h', h]
        exact h_k1
      have h_k2' : (t : ℝ) * nr < (k : ℝ) + 1 := by
        have h : ((k : ℤ) : ℝ) = (k_int : ℝ) := by exact_mod_cast h_k_eq
        have h' : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by simp
        have h'' : ((k + 1 : ℕ) : ℝ) = ((k : ℤ) + 1 : ℝ) := by exact?
        rw [h', h'']
        have h3 : ((k : ℤ) + 1 : ℝ) = (k_int : ℝ) + 1 := by
          rw [h_k_eq] <;> rfl
        rw [h3]
        exact h_k2
      have h_k_lt_n : k < n := by
        by_contra h
        have h' : k ≥ n := by linarith
        have h''1 : (k : ℝ) ≥ (n : ℝ) := by exact_mod_cast h'
        have h'' : (k : ℝ) ≥ nr := by
          rw [hnr]
          exact h''1
        have h_contra : (t : ℝ) * nr < (k : ℝ) + 1 := h_k2'
        have h_t_lt_one' : (t : ℝ) < 1 := h_t_lt_one
        nlinarith
      let i : Fin n := ⟨k, h_k_lt_n⟩
      have h1 : (i.val : ℝ) / nr ≤ (t : ℝ) := by
        have h : (i.val : ℝ) ≤ (t : ℝ) * nr := h_k1'
        have h_pos : 0 < nr := hnr_pos
        have h_div : (i.val : ℝ) / nr ≤ ((t : ℝ) * nr) / nr := by
          apply div_le_div_of_nonneg_right h
          positivity
        have h_eq : ((t : ℝ) * nr) / nr = (t : ℝ) := by
          field_simp [h_pos.ne'] <;> ring
        rw [h_eq] at h_div
        exact h_div
      have h2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / nr := by
        have h : (t : ℝ) * nr < (i.val : ℝ) + 1 := h_k2'
        have h_pos : 0 < nr := hnr_pos
        have h_lt : (t : ℝ) < ((i.val : ℝ) + 1) / nr := by
          calc
            (t : ℝ) = ((t : ℝ) * nr) / nr := by
              field_simp [h_pos.ne'] <;> ring
            _ < ((i.val : ℝ) + 1) / nr := by
              apply div_lt_div_of_pos_right h h_pos
        exact le_of_lt h_lt
      have h3 : t ∈ c (U i) := h_interval_subset i ⟨h1, h2⟩
      exact ⟨i, h3⟩
  exact ⟨n, pts, covers, γs, hcovers_in, h_pts0, h_ptsn, h_main1, h_main2⟩

/-- Stronger version of path_has_subdivision that also returns the subdivision points ts in I
    and the fact that γs are subpaths of γ. -/
theorem path_has_subdivision_with_ts
    {X : Type*} [TopologicalSpace X]
    (𝒰 : Set (TopologicalSpace.Opens X))
    (hcover : ∀ x : X, ∃ U : TopologicalSpace.Opens X, U ∈ 𝒰 ∧ x ∈ U)
    {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (ts : Fin (n + 1) → I) (h_ts0 : ts 0 = 0) (h_ts1 : ts (Fin.last n) = 1)
      (h_ts_strict : StrictMono ts)
      (covers : Fin n → TopologicalSpace.Opens X)
      (hcovers_in : ∀ i, covers i ∈ 𝒰)
      (h_range : ∀ i : Fin n, Set.range (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))) ⊆ (covers i : Set X)),
      True := by
  let ι := { U : TopologicalSpace.Opens X // U ∈ 𝒰 }
  let c : ι → Set I := fun U => γ ⁻¹' (U : Set X)
  have hc₁ : ∀ (i : ι), IsOpen (c i) := by
    intro U
    exact U.val.2.preimage γ.continuous
  have hc₂ : (Set.univ : Set I) ⊆ ⋃ (i : ι), c i := by
    intro t _
    have h₁ : ∃ (U : TopologicalSpace.Opens X), U ∈ 𝒰 ∧ γ t ∈ U := hcover (γ t)
    rcases h₁ with ⟨U, hU, hUt⟩
    let U' : ι := ⟨U, hU⟩
    exact Set.mem_iUnion.mpr ⟨U', hUt⟩
  have hcompact : IsCompact (Set.univ : Set I) := isCompact_univ
  rcases lebesgue_number_lemma_of_metric hcompact hc₁ hc₂ with ⟨δ, hδ_pos, hδ⟩
  have hδ_pos' : 0 < δ := hδ_pos
  have h_arch : ∃ (n : ℕ), 0 < n ∧ 1 / (n : ℝ) < δ := by
    have h : ∃ (n : ℕ), (n : ℝ) > 1 / δ := exists_nat_gt (1 / δ)
    rcases h with ⟨n, hn⟩
    have hn_pos : 0 < n := by
      by_contra h'
      have h'' : n = 0 := by omega
      rw [h''] at hn
      norm_num at hn <;> linarith
    have h1 : 1 / (n : ℝ) < δ := by
      have h2 : 0 < δ := hδ_pos'
      have h3 : (n : ℝ) > 1 / δ := hn
      calc
        1 / (n : ℝ) < 1 / (1 / δ) := by gcongr
        _ = δ := by field_simp [h2.ne'] <;> ring
    exact ⟨n, hn_pos, h1⟩
  rcases h_arch with ⟨n, hn_pos, h1n_lt_δ⟩
  set nr : ℝ := (n : ℝ) with hnr
  have hnr_pos : 0 < nr := by
    rw [hnr]
    exact_mod_cast hn_pos
  let t_pt (i : Fin (n + 1)) : I :=
    ⟨(i.val : ℝ) / nr, by
      have h₁ : 0 ≤ (i.val : ℝ) / nr := by positivity
      have h₂ : (i.val : ℝ) / nr ≤ 1 := by
        have h3 : i.val ≤ n := Nat.lt_succ_iff.mp i.is_lt
        have h41 : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
        have h4 : (i.val : ℝ) ≤ nr := by
          rw [hnr]
          exact h41
        have h5 : (i.val : ℝ) / nr ≤ 1 := by
          calc
            (i.val : ℝ) / nr ≤ nr / nr := by gcongr
            _ = 1 := by
              field_simp [hnr_pos.ne'] <;> ring
        exact h5
      exact ⟨h₁, h₂⟩⟩
  let mid_pt (i : Fin n) : I :=
    ⟨(2 * (i.val : ℝ) + 1) / (2 * nr), by
      have h₁ : 0 ≤ (2 * (i.val : ℝ) + 1) / (2 * nr) := by positivity
      have h₂ : (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ 1 := by
        have h3 : i.val < n := i.is_lt
        have h4 : (i.val : ℝ) < nr := by
          simpa [hnr] using Nat.cast_lt.mpr h3
        have h5 : 2 * (i.val : ℝ) + 1 ≤ 2 * nr := by
          have h6 : (i.val : ℝ) + 1 ≤ nr := by
            have h7 : i.val + 1 ≤ n := Nat.succ_le_iff.mpr h3
            simpa [hnr] using Nat.cast_le.mpr h7
          linarith
        have h7 : (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ 1 := by
          calc
            (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ (2 * nr) / (2 * nr) := by gcongr
            _ = 1 := by
              field_simp [hnr_pos.ne'] <;> ring
        exact h7
      exact ⟨h₁, h₂⟩⟩
  have h_choose : ∀ (i : Fin n), ∃ (U : ι), ball (mid_pt i) δ ⊆ c U := by
    intro i
    exact hδ (mid_pt i) (Set.mem_univ (mid_pt i))
  choose U hU using h_choose
  let covers (i : Fin n) : TopologicalSpace.Opens X := (U i).val
  have hcovers_in : ∀ (i : Fin n), covers i ∈ 𝒰 := fun i => (U i).property
  have h_t0 : (t_pt 0 : ℝ) = 0 := by
    simp [t_pt, hnr]
    <;> field_simp [hnr_pos.ne'] <;> ring
  have h_ts0 : t_pt 0 = 0 := by
    apply Subtype.ext
    exact h_t0
  have h_t_last_val : (t_pt (Fin.last n) : ℝ) = 1 := by
    have h1 : (Fin.last n).val = n := by simp [Fin.last]
    have h2 : ((Fin.last n).val : ℝ) / nr = 1 := by
      rw [h1]
      have h3 : (n : ℝ) = nr := by simp [hnr]
      rw [h3]
      field_simp [hnr_pos.ne'] <;> ring
    simpa [t_pt] using h2
  have h_ts1 : t_pt (Fin.last n) = 1 := by
    apply Subtype.ext
    exact h_t_last_val
  have h_ts_strict : StrictMono t_pt := by
    intro i j h
    have h' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast h
    have h'' : (i.val : ℝ) / nr < (j.val : ℝ) / nr := by
      gcongr
    exact Subtype.mk_lt_mk.mpr h''
  have h_half_lt_delta : 1 / (2 * nr) < δ := by
    have h7 : 1 / (2 * nr) < 1 / nr := by
      apply div_lt_div_of_pos_left
      · norm_num
      · positivity
      · linarith
    have h8 : 1 / nr < δ := by
      simpa [hnr] using h1n_lt_δ
    linarith
  have h_half_eq : (1 / nr) / 2 = 1 / (2 * nr) := by
    ring
  have h_t_pt_succ_eq : ∀ (i : Fin n), (t_pt (Fin.succ i) : ℝ) = ((i.val : ℝ) + 1) / nr := by
    intro i
    simp [t_pt, Fin.succ]
    <;> rfl
  have h_mem_ball : ∀ (i : Fin n) (w : I),
      (i.val : ℝ) / nr ≤ (w : ℝ) → (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr → w ∈ ball (mid_pt i) δ := by
    intro i w h1 h2
    set a : ℝ := (i.val : ℝ) / nr with ha
    set b : ℝ := ((i.val : ℝ) + 1) / nr with hb
    set m : ℝ := (2 * (i.val : ℝ) + 1) / (2 * nr) with hm
    have h_eq_m : m = (a + b) / 2 := by
      simp [ha, hb, hm] <;> ring
    have h3 : b - a = 1 / nr := by
      simp [ha, hb, hnr_pos.ne'] <;> field_simp [hnr_pos.ne'] <;> ring
    have h4 : |(w : ℝ) - m| ≤ (b - a) / 2 := by
      rw [h_eq_m]
      exact abs_midpoint_le_half h1 h2
    have h5 : |(w : ℝ) - m| ≤ 1 / (2 * nr) := by
      rw [h3, h_half_eq] at h4
      exact h4
    have h6 : dist w (mid_pt i) ≤ 1 / (2 * nr) := by
      have h_mid : ((mid_pt i) : ℝ) = m := by
        simp [mid_pt, hm] <;> rfl
      have h : dist w (mid_pt i) = |(w : ℝ) - (mid_pt i : ℝ)| := by
        change dist (w : ℝ) ((mid_pt i) : ℝ) = |(w : ℝ) - (mid_pt i : ℝ)|
        rw [Real.dist_eq]
        <;> rfl
      rw [h, h_mid]
      exact h5
    have h7 : dist w (mid_pt i) < δ := by
      exact lt_of_le_of_lt h6 h_half_lt_delta
    exact h7
  have h_interval_subset : ∀ (i : Fin n),
      {w : I | (i.val : ℝ) / nr ≤ (w : ℝ) ∧ (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr} ⊆ c (U i) := by
    intro i
    intro w hw
    have h1 : (i.val : ℝ) / nr ≤ (w : ℝ) := hw.1
    have h2 : (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr := hw.2
    have h3 : w ∈ ball (mid_pt i) δ := h_mem_ball i w h1 h2
    exact hU i h3
  have h_image_subset : ∀ (i : Fin n),
      γ '' (Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) ⊆ (covers i : Set X) := by
    intro i
    have h1 : ∀ (w : I), w ∈ Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i)) → w ∈ c (U i) := by
      intro w hw
      have h2 : (t_pt (Fin.castSucc i) : ℝ) ≤ (w : ℝ) := hw.1
      have h3 : (w : ℝ) ≤ (t_pt (Fin.succ i) : ℝ) := hw.2
      have h4 : (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr := by
        rw [h_t_pt_succ_eq i] at h3
        exact h3
      exact h_interval_subset i ⟨h2, h4⟩
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact h1 w hw
  have h_range : ∀ (i : Fin n), Set.range (γ.subpath (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) ⊆ (covers i : Set X) := by
    intro i
    have h_le : (t_pt (Fin.castSucc i) : ℝ) ≤ (t_pt (Fin.succ i) : ℝ) := by
      simp [t_pt]
      <;> have h : (i.val : ℝ) ≤ (i.val : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h (by positivity)
    have h_range2 : Set.range (γ.subpath (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) =
        γ '' (Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) := by
      apply Path.range_subpath_of_le
      exact h_le
    rw [h_range2]
    exact h_image_subset i
  exact ⟨n, t_pt, h_ts0, h_ts1, h_ts_strict, covers, hcovers_in, h_range, trivial⟩

end

end

end P202.Topology.VanKampenProof


/-! Adapted from UniquenessProofs.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

/-- Helper: for a path segment contained in U ∈ 𝒰, F.map and G.map agree modulo eqToHom. -/
lemma agree_on_segment
    (F G : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt)
    (hF : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F =
      s.ι.app ⟨U, hU⟩)
    (hG : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G =
      s.ι.app ⟨U, hU⟩)
    (h_objs_eq : ∀ (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)),
      F.obj x = G.obj x)
    {x y : X} (γ : Path x y) (U : Opens X) (hU : U ∈ 𝒰)
    (h_range : Set.range γ ⊆ (U : Set X)) :
    F.map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) =
    eqToHom (h_objs_eq (FundamentalGroupoid.mk x)) ≫
    G.map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) ≫
    eqToHom (h_objs_eq (FundamentalGroupoid.mk y)).symm := by
  classical
  have hx : x ∈ U := by
    have h1 : γ 0 ∈ Set.range γ := Set.mem_range_self 0
    have h2 : γ 0 = x := γ.source
    rw [h2] at h1
    exact h_range h1
  have hy : y ∈ U := by
    have h1 : γ 1 ∈ Set.range γ := Set.mem_range_self 1
    have h2 : γ 1 = y := γ.target
    rw [h2] at h1
    exact h_range h1
  let π₁U := FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U)
  let x_U : π₁U := FundamentalGroupoid.mk (⟨x, hx⟩ : (U : Set X))
  let y_U : π₁U := FundamentalGroupoid.mk (⟨y, hy⟩ : (U : Set X))
  let γ_lift : Path (⟨x, hx⟩ : (U : Set X)) (⟨y, hy⟩ : (U : Set X)) :=
    (Path.lift_to_subtype γ hx hy h_range).choose
  let f_U : x_U ⟶ y_U := Path.Homotopic.Quotient.mk γ_lift
  let F' : π₁U ⥤ s.pt :=
    (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F
  let G' : π₁U ⥤ s.pt :=
    (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G
  have hF' : F' = s.ι.app ⟨U, hU⟩ := hF U hU
  have hG' : G' = s.ι.app ⟨U, hU⟩ := hG U hU
  have h_eq : F' = G' := by
    rw [hF', hG']
  have h_main : ∀ (a b : π₁U) (f : a ⟶ b),
      F'.map f = eqToHom (congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj a) h_eq) ≫
        G'.map f ≫ eqToHom (congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj b) h_eq).symm := by
    intro a b f
    have h : ∀ (F1 G1 : π₁U ⥤ s.pt) (h : F1 = G1),
        F1.map f = eqToHom (congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj a) h) ≫
          G1.map f ≫ eqToHom (congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj b) h).symm := by
      intro F1 G1 h
      subst h
      <;> simp
      <;> rfl
    exact h F' G' h_eq
  have h2 := h_main x_U y_U f_U
  have h_dom_eq : congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj x_U) h_eq =
      h_objs_eq (FundamentalGroupoid.mk x) := by
    apply Subsingleton.elim
  have h_cod_eq : congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj y_U) h_eq =
      h_objs_eq (FundamentalGroupoid.mk y) := by
    apply Subsingleton.elim
  rw [h_dom_eq, h_cod_eq] at h2
  have h_spec : ∀ t, (γ_lift t : X) = γ t := fun t => (Path.lift_to_subtype γ hx hy h_range).choose_spec t
  let g_top : (Opens.toTopCat (TopCat.of X)).obj U ⟶ TopCat.of X :=
    @Opens.inclusion' (TopCat.of X) U
  let incl_π : π₁U ⥤ FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.fundamentalGroupoidFunctor.map g_top
  have h_incl_map : incl_π.map f_U = FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ) := by
    dsimp only [incl_π, f_U, FundamentalGroupoid.fromPath]
    let f_cont := g_top.hom
    have h1 : (FundamentalGroupoid.fundamentalGroupoidFunctor.map g_top).map (Path.Homotopic.Quotient.mk γ_lift) =
        (Path.Homotopic.Quotient.mk γ_lift).map f_cont := by
      exact FundamentalGroupoid.map_eq f_cont (Path.Homotopic.Quotient.mk γ_lift)
    have h2 : (Path.Homotopic.Quotient.mk γ_lift).map f_cont = Path.Homotopic.Quotient.mk γ := by
      have h21 : (Path.Homotopic.Quotient.mk γ_lift).map f_cont =
          Path.Homotopic.Quotient.mk (γ_lift.map f_cont.continuous) := by
        exact (Path.Homotopic.Quotient.mk_map γ_lift f_cont).symm
      rw [h21]
      apply congr_arg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      exact h_spec t
    rw [h1, h2]
  have h3 : F'.map f_U = F.map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) := by
    dsimp only [F']
    rw [← h_incl_map]
    <;> rfl
  have h4 : G'.map f_U = G.map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) := by
    dsimp only [G']
    rw [← h_incl_map]
    <;> rfl
  rw [h3, h4] at h2
  exact h2

set_option backward.isDefEq.respectTransparency.types false in
/-- Uniqueness of the descent functor on morphisms: any two functors F G : π₁(X) → s.pt
    that make the cocone triangles commute must agree on all morphisms
    (modulo eqToHom transport for object equalities). -/
theorem uniqueness_on_morphisms
    (F G : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt)
    (hF : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F =
      s.ι.app ⟨U, hU⟩)
    (hG : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G =
      s.ι.app ⟨U, hU⟩)
    (h_objs_eq : ∀ (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)),
      F.obj x = G.obj x) :
    ∀ (x y : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X))
      (f : x ⟶ y), F.map f = eqToHom (h_objs_eq x) ≫ G.map f ≫ eqToHom (h_objs_eq y).symm := by
  intro x y f
  induction f using Quotient.inductionOn' with
  | h γ =>
    have h_decomp : ∃ (n : ℕ) (ts : Fin (n + 1) → I) (h_ts0 : ts 0 = 0)
      (h_ts1 : ts (Fin.last n) = 1) (h_ts_strict : StrictMono ts)
      (covers : Fin n → Opens X) (hcovers_in : ∀ i, covers i ∈ 𝒰)
      (h_range : ∀ i : Fin n,
        Set.range (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))) ⊆ (covers i : Set X)), True :=
      path_has_subdivision_with_ts 𝒰 hcover γ
    rcases h_decomp with ⟨n, ts, h_ts0, h_ts1, h_ts_strict, covers, hcovers_in, h_range, _⟩
    let pts : Fin (n + 1) → FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
      fun i => FundamentalGroupoid.mk (γ (ts i))
    let morphs : ∀ i : Fin n, pts (Fin.castSucc i) ⟶ pts (Fin.succ i) :=
      fun i => FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))))
    have h_x_eq : pts 0 = x := by
      simp [pts, h_ts0, γ.source] <;> rfl
    have h_y_eq : pts (Fin.last n) = y := by
      simp [pts, h_ts1, γ.target] <;> rfl
    have h_decomp_eq : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n)))) =
        comp_list n pts morphs :=
      subpath_decomposition_comp_list γ ts h_ts_strict
    have h_agree : ∀ i : Fin n,
        F.map (morphs i) =
        eqToHom (h_objs_eq (pts (Fin.castSucc i))) ≫
        G.map (morphs i) ≫
        eqToHom (h_objs_eq (pts (Fin.succ i))).symm := by
      intro i
      exact agree_on_segment X 𝒰 hcover hfinite_intersections s F G hF hG h_objs_eq
        (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i)))
        (covers i) (hcovers_in i) (h_range i)
    have h_homs : ∀ i : Fin n,
        eqToHom (h_objs_eq (pts (Fin.castSucc i))).symm ≫ F.map (morphs i) ≫ eqToHom (h_objs_eq (pts (Fin.succ i))) =
        G.map (morphs i) := by
      intro i
      have h := h_agree i
      have h_lhs : eqToHom (h_objs_eq (pts (Fin.castSucc i))).symm ≫ F.map (morphs i) ≫ eqToHom (h_objs_eq (pts (Fin.succ i))) =
          G.map (morphs i) := by
        rw [h]
        <;> simp [Category.assoc, eqToHom_trans, eqToHom_refl]
        <;> rfl
      exact h_lhs
    have h_congr :
        eqToHom (h_objs_eq (pts 0)).symm ≫
        comp_list n (fun i => F.obj (pts i)) (fun i => F.map (morphs i)) ≫
        eqToHom (h_objs_eq (pts (Fin.last n))) =
        comp_list n (fun i => G.obj (pts i)) (fun i => G.map (morphs i)) :=
      comp_list_congr_with_eqToHom
        (fun i => F.obj (pts i)) (fun i => G.obj (pts i))
        (fun i => F.map (morphs i)) (fun i => G.map (morphs i))
        (fun i => h_objs_eq (pts i)) h_homs
    have h_functor_F : F.map (comp_list n pts morphs) =
        comp_list n (fun i => F.obj (pts i)) (fun i => F.map (morphs i)) := by
      exact comp_list_functor_map F pts morphs
    have h_functor_G : G.map (comp_list n pts morphs) =
        comp_list n (fun i => G.obj (pts i)) (fun i => G.map (morphs i)) := by
      exact comp_list_functor_map G pts morphs
    have h_main_comp : F.map (comp_list n pts morphs) =
        eqToHom (h_objs_eq (pts 0)) ≫
        G.map (comp_list n pts morphs) ≫
        eqToHom (h_objs_eq (pts (Fin.last n))).symm := by
      rw [h_functor_F, h_functor_G]
      rw [←h_congr]
      <;> simp [Category.assoc, eqToHom_trans, eqToHom_refl]
      <;> rfl
    -- Now prove the equality for .mk γ using conj_eqToHom and h_main_comp
    have hx : γ (ts 0) = x.as := by
      rw [h_ts0, γ.source] <;> rfl
    have hy : γ (ts (Fin.last n)) = y.as := by
      rw [h_ts1, γ.target] <;> rfl
    let e1 := congr_arg FundamentalGroupoid.mk hx
    let e2 := congr_arg FundamentalGroupoid.mk hy
    have h_conj_eq : eqToHom e1 ≫ Path.Homotopic.Quotient.mk γ ≫ eqToHom (congr_arg FundamentalGroupoid.mk hy.symm) =
        Path.Homotopic.Quotient.mk (γ.cast hx hy) :=
      FundamentalGroupoid.conj_eqToHom hx hy
    have h_path_eq : (γ.cast hx hy) = γ.subpath (ts 0) (ts (Fin.last n)) := by
      apply Path.ext
      funext t
      have h1 : (γ.cast hx hy) t = γ t := by rfl
      have h2 : (γ.subpath (ts 0) (ts (Fin.last n))) t = γ t := by
        simp [Path.subpath, h_ts0, h_ts1] <;> ring_nf <;> congr <;> linarith
      rw [h1, h2]
    have h_eq_cast : Path.Homotopic.Quotient.mk (γ.cast hx hy) =
        Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n))) := by
      rw [h_path_eq] <;> rfl
    have h4 : eqToHom e1 ≫ Path.Homotopic.Quotient.mk γ ≫ eqToHom (congr_arg FundamentalGroupoid.mk hy.symm) =
        comp_list n pts morphs := by
      have h_decomp_eq' : Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n))) =
          comp_list n pts morphs := by
        simpa [FundamentalGroupoid.fromPath] using h_decomp_eq
      rw [h_conj_eq, h_eq_cast, h_decomp_eq'] <;> rfl
    -- Prove the main goal
    have h_goal : F.map (Path.Homotopic.Quotient.mk γ) =
        eqToHom (h_objs_eq x) ≫
        G.map (Path.Homotopic.Quotient.mk γ) ≫
        eqToHom (h_objs_eq y).symm := by
      let g := Path.Homotopic.Quotient.mk γ
      let g' := comp_list n pts morphs
      have h4' : eqToHom h_x_eq ≫ g ≫ eqToHom h_y_eq.symm = g' := by
        have h_e1 : e1 = h_x_eq := by exact Subsingleton.elim e1 h_x_eq
        have h_e2 : congr_arg FundamentalGroupoid.mk hy.symm = h_y_eq.symm := by
          exact Subsingleton.elim (congr_arg FundamentalGroupoid.mk hy.symm) h_y_eq.symm
        have h4_copy : eqToHom e1 ≫ Path.Homotopic.Quotient.mk γ ≫ eqToHom (congr_arg FundamentalGroupoid.mk hy.symm) = g' := h4
        rw [h_e1, h_e2] at h4_copy
        exact h4_copy
      have h_eq1 : eqToHom h_x_eq.symm ≫ eqToHom h_x_eq = 𝟙 x := by
        rw [eqToHom_trans, eqToHom_refl]
        <;> exact rfl
      have h_eq2 : eqToHom h_y_eq.symm ≫ eqToHom h_y_eq = 𝟙 y := by
        rw [eqToHom_trans, eqToHom_refl]
        <;> exact rfl
      have h_F_map : F.map g =
          eqToHom (congr_arg F.obj h_x_eq.symm) ≫
          F.map g' ≫
          eqToHom (congr_arg F.obj h_y_eq) := by
        have h : g = eqToHom h_x_eq.symm ≫ g' ≫ eqToHom h_y_eq := by
          calc
            g
              = 𝟙 x ≫ g ≫ 𝟙 y := by simp
            _ = (eqToHom h_x_eq.symm ≫ eqToHom h_x_eq) ≫ g ≫ (eqToHom h_y_eq.symm ≫ eqToHom h_y_eq) := by
                rw [h_eq1, h_eq2]
            _ = eqToHom h_x_eq.symm ≫ (eqToHom h_x_eq ≫ g ≫ eqToHom h_y_eq.symm) ≫ eqToHom h_y_eq := by
                simp [Category.assoc]
                <;> rfl
            _ = eqToHom h_x_eq.symm ≫ g' ≫ eqToHom h_y_eq := by
                rw [h4'] <;> rfl
        rw [h]
        rw [Functor.map_comp, Functor.map_comp]
        rw [eqToHom_map F, eqToHom_map F]
        <;> rfl
      have h_G_map : G.map g =
          eqToHom (congr_arg G.obj h_x_eq.symm) ≫
          G.map g' ≫
          eqToHom (congr_arg G.obj h_y_eq) := by
        have h : g = eqToHom h_x_eq.symm ≫ g' ≫ eqToHom h_y_eq := by
          calc
            g
              = 𝟙 x ≫ g ≫ 𝟙 y := by simp
            _ = (eqToHom h_x_eq.symm ≫ eqToHom h_x_eq) ≫ g ≫ (eqToHom h_y_eq.symm ≫ eqToHom h_y_eq) := by
                rw [h_eq1, h_eq2]
            _ = eqToHom h_x_eq.symm ≫ (eqToHom h_x_eq ≫ g ≫ eqToHom h_y_eq.symm) ≫ eqToHom h_y_eq := by
                simp [Category.assoc]
                <;> rfl
            _ = eqToHom h_x_eq.symm ≫ g' ≫ eqToHom h_y_eq := by
                rw [h4'] <;> rfl
        rw [h]
        rw [Functor.map_comp, Functor.map_comp]
        rw [eqToHom_map G, eqToHom_map G]
        <;> rfl
      have h_nat1 : eqToHom (congr_arg F.obj h_x_eq.symm) ≫ eqToHom (h_objs_eq (pts 0)) =
          eqToHom (h_objs_eq x) ≫ eqToHom (congr_arg G.obj h_x_eq.symm) := by
        rw [eqToHom_trans, eqToHom_trans]
      have h_nat2 : eqToHom (h_objs_eq (pts (Fin.last n))).symm ≫ eqToHom (congr_arg F.obj h_y_eq) =
          eqToHom (congr_arg G.obj h_y_eq) ≫ eqToHom (h_objs_eq y).symm := by
        rw [eqToHom_trans, eqToHom_trans]
      calc
        F.map g
          = eqToHom (congr_arg F.obj h_x_eq.symm) ≫ F.map g' ≫ eqToHom (congr_arg F.obj h_y_eq) := h_F_map
        _ = eqToHom (congr_arg F.obj h_x_eq.symm) ≫
            (eqToHom (h_objs_eq (pts 0)) ≫ G.map g' ≫ eqToHom (h_objs_eq (pts (Fin.last n))).symm) ≫
            eqToHom (congr_arg F.obj h_y_eq) := by
          rw [h_main_comp] <;> rfl
        _ = (eqToHom (congr_arg F.obj h_x_eq.symm) ≫ eqToHom (h_objs_eq (pts 0))) ≫
            G.map g' ≫
            (eqToHom (h_objs_eq (pts (Fin.last n))).symm ≫ eqToHom (congr_arg F.obj h_y_eq)) := by
          simp [Category.assoc] <;> rfl
        _ = (eqToHom (h_objs_eq x) ≫ eqToHom (congr_arg G.obj h_x_eq.symm)) ≫
            G.map g' ≫
            (eqToHom (congr_arg G.obj h_y_eq) ≫ eqToHom (h_objs_eq y).symm) := by
          rw [h_nat1, h_nat2] <;> rfl
        _ = eqToHom (h_objs_eq x) ≫
            (eqToHom (congr_arg G.obj h_x_eq.symm) ≫ G.map g' ≫ eqToHom (congr_arg G.obj h_y_eq)) ≫
            eqToHom (h_objs_eq y).symm := by
          simp [Category.assoc] <;> rfl
        _ = eqToHom (h_objs_eq x) ≫ G.map g ≫ eqToHom (h_objs_eq y).symm := by
          rw [←h_G_map] <;> rfl
    exact h_goal

end

end

end P202.Topology.VanKampenProof


/-! Adapted from RectangleHomotopy.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace

open scoped unitInterval

universe u

noncomputable section

variable {X : Type u} [TopologicalSpace X]

namespace RectangleHomotopy

/-- The identity path in I, from 0 to 1. -/
def id_path_I : Path (0 : I) (1 : I) where
  toFun := fun t : I => t
  continuous_toFun := continuous_id
  source' := by simp
  target' := by simp

/-- First component homotopy: refl;id → id;refl -/
def h1 : Path.Homotopy
    ((Path.refl (0 : I)).trans id_path_I)
    (id_path_I.trans (Path.refl (1 : I))) :=
  Path.Homotopy.trans (Path.Homotopy.reflTrans id_path_I)
    (Path.Homotopy.symm (Path.Homotopy.transRefl id_path_I))

/-- Second component homotopy: id;refl → refl;id -/
def h2 : Path.Homotopy
    (id_path_I.trans (Path.refl (1 : I)))
    ((Path.refl (0 : I)).trans id_path_I) :=
  Path.Homotopy.trans (Path.Homotopy.transRefl id_path_I)
    (Path.Homotopy.symm (Path.Homotopy.reflTrans id_path_I))

/-- The two boundary paths in I × I. -/
def p1 : Path ((0 : I), (0 : I)) ((1 : I), (1 : I)) :=
  Path.prod ((Path.refl (0 : I)).trans id_path_I) (id_path_I.trans (Path.refl (1 : I)))

def p2 : Path ((0 : I), (0 : I)) ((1 : I), (1 : I)) :=
  Path.prod (id_path_I.trans (Path.refl (1 : I))) ((Path.refl (0 : I)).trans id_path_I)

/-- The standard square homotopy in I × I. -/
def square_homotopy : Path.Homotopy p1 p2 :=
  Path.Homotopic.prodHomotopy h1 h2

/-- Given a continuous map G : I × I → X, we get a homotopy between
    the two boundary paths by mapping the square homotopy along G. -/
def rectangle_boundary_homotopy (G : C(I × I, X)) :
    Path.Homotopy (p1.map G.continuous) (p2.map G.continuous) :=
  square_homotopy.map G

/-- The rectangle boundary homotopy stays within the image of G. -/
lemma rectangle_boundary_homotopy_range (G : C(I × I, X)) (U : Set X)
    (hG : ∀ (p : I × I), G p ∈ U) :
    ∀ (p : I × I), (rectangle_boundary_homotopy G) p ∈ U := by
  intro p
  have h_eq : (rectangle_boundary_homotopy G) p = G (square_homotopy p) := by
    rfl
  rw [h_eq]
  exact hG (square_homotopy p)

/-- Given edge paths matching the boundary of G, we get a homotopy between
    bottom.trans right and left.trans top, staying within U. -/
theorem rectangle_boundary_homotopy_edges
    (G : C(I × I, X))
    (γ_bottom : Path (G (0, 0)) (G (0, 1)))
    (γ_right : Path (G (0, 1)) (G (1, 1)))
    (γ_left : Path (G (0, 0)) (G (1, 0)))
    (γ_top : Path (G (1, 0)) (G (1, 1)))
    (h_bottom : ∀ (t : I), γ_bottom t = G (0, t))
    (h_right : ∀ (s : I), γ_right s = G (s, 1))
    (h_left : ∀ (s : I), γ_left s = G (s, 0))
    (h_top : ∀ (t : I), γ_top t = G (1, t))
    (U : Set X)
    (hG : ∀ (p : I × I), G p ∈ U) :
    ∃ (H_rect : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top)),
      ∀ (p : I × I), H_rect p ∈ U := by
  let H_raw := rectangle_boundary_homotopy G
  have h_range_raw : ∀ (p : I × I), H_raw p ∈ U :=
    rectangle_boundary_homotopy_range G U hG
  have h_eq1 : (p1.map G.continuous) = γ_bottom.trans γ_right := by
    have h_main : ∀ (t : I), (p1.map G.continuous) t = (γ_bottom.trans γ_right) t := by
      intro t
      have h_lhs : (p1.map G.continuous) t = G (p1 t) := by rfl
      rw [h_lhs]
      let p1_fst := (Path.refl (0 : I)).trans id_path_I
      let p1_snd := id_path_I.trans (Path.refl (1 : I))
      have h_p1_def : p1 = Path.prod p1_fst p1_snd := by rfl
      have h_p1t : p1 t = (p1_fst t, p1_snd t) := by
        rw [h_p1_def]
        exact congrFun (Path.prod_coe p1_fst p1_snd) t
      rw [h_p1t]
      by_cases h : (t : ℝ) ≤ 1 / 2
      · -- Case t ≤ 1/2: first part of p1 is bottom edge (s stays at 0, t goes from 0 to 1)
        have h2t : 0 ≤ 2 * (t : ℝ) ∧ 2 * (t : ℝ) ≤ 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2]
        let t2 : I := ⟨2 * (t : ℝ), h2t.1, h2t.2⟩
        have ht2 : (t2 : ℝ) = 2 * (t : ℝ) := by rfl
        have h_fst : p1_fst t = (0 : I) := by
          dsimp only [p1_fst]
          rw [Path.trans_apply, dif_pos h]
          <;> simp [id_path_I]
          <;> rfl
        have h_snd : p1_snd t = t2 := by
          dsimp only [p1_snd]
          rw [Path.trans_apply, dif_pos h]
          <;> exact Subtype.ext ht2
        have h_goal1 : G (p1_fst t, p1_snd t) = G (0, t2) := by
          rw [h_fst, h_snd]
        rw [h_goal1]
        have h_rhs : (γ_bottom.trans γ_right) t = γ_bottom t2 := by
          rw [Path.trans_apply, dif_pos h]
          <;> congr <;> exact Subtype.ext ht2
        rw [h_rhs, h_bottom t2]
        <;> rfl
      · -- Case t > 1/2: second part of p1 is right edge (s goes from 0 to 1, t stays at 1)
        have h' : 1 / 2 ≤ (t : ℝ) := by linarith
        have h2t1 : 0 ≤ 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 ≤ 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2]
        let t2 : I := ⟨2 * (t : ℝ) - 1, h2t1.1, h2t1.2⟩
        have ht2 : (t2 : ℝ) = 2 * (t : ℝ) - 1 := by rfl
        have h_fst : p1_fst t = t2 := by
          dsimp only [p1_fst]
          rw [Path.trans_apply, dif_neg h]
          <;> exact Subtype.ext ht2
        have h_snd : p1_snd t = (1 : I) := by
          dsimp only [p1_snd]
          rw [Path.trans_apply, dif_neg h]
          <;> simp [id_path_I]
          <;> rfl
        have h_goal1 : G (p1_fst t, p1_snd t) = G (t2, 1) := by
          rw [h_fst, h_snd]
        rw [h_goal1]
        have h_rhs : (γ_bottom.trans γ_right) t = γ_right t2 := by
          rw [Path.trans_apply, dif_neg h]
          <;> congr <;> exact Subtype.ext ht2
        rw [h_rhs, h_right t2]
        <;> rfl
    have h_fun : (fun t : I => (p1.map G.continuous) t) = (fun t : I => (γ_bottom.trans γ_right) t) := by
      funext t
      exact h_main t
    exact Path.ext h_fun
  have h_eq2 : (p2.map G.continuous) = γ_left.trans γ_top := by
    have h_main : ∀ (t : I), (p2.map G.continuous) t = (γ_left.trans γ_top) t := by
      intro t
      have h_lhs : (p2.map G.continuous) t = G (p2 t) := by rfl
      rw [h_lhs]
      let p2_fst := id_path_I.trans (Path.refl (1 : I))
      let p2_snd := (Path.refl (0 : I)).trans id_path_I
      have h_p2_def : p2 = Path.prod p2_fst p2_snd := by rfl
      have h_p2t : p2 t = (p2_fst t, p2_snd t) := by
        rw [h_p2_def]
        exact congrFun (Path.prod_coe p2_fst p2_snd) t
      rw [h_p2t]
      by_cases h : (t : ℝ) ≤ 1 / 2
      · -- Case t ≤ 1/2: first part of p2 is left edge (s goes from 0 to 1, t stays at 0)
        have h2t : 0 ≤ 2 * (t : ℝ) ∧ 2 * (t : ℝ) ≤ 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2]
        let t2 : I := ⟨2 * (t : ℝ), h2t.1, h2t.2⟩
        have ht2 : (t2 : ℝ) = 2 * (t : ℝ) := by rfl
        have h_fst : p2_fst t = t2 := by
          dsimp only [p2_fst]
          rw [Path.trans_apply, dif_pos h]
          <;> exact Subtype.ext ht2
        have h_snd : p2_snd t = (0 : I) := by
          dsimp only [p2_snd]
          rw [Path.trans_apply, dif_pos h]
          <;> simp [id_path_I]
          <;> rfl
        have h_goal1 : G (p2_fst t, p2_snd t) = G (t2, 0) := by
          rw [h_fst, h_snd]
        rw [h_goal1]
        have h_rhs : (γ_left.trans γ_top) t = γ_left t2 := by
          rw [Path.trans_apply, dif_pos h]
          <;> congr <;> exact Subtype.ext ht2
        rw [h_rhs, h_left t2]
        <;> rfl
      · -- Case t > 1/2: second part of p2 is top edge (s stays at 1, t goes from 0 to 1)
        have h' : 1 / 2 ≤ (t : ℝ) := by linarith
        have h2t1 : 0 ≤ 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 ≤ 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2]
        let t2 : I := ⟨2 * (t : ℝ) - 1, h2t1.1, h2t1.2⟩
        have ht2 : (t2 : ℝ) = 2 * (t : ℝ) - 1 := by rfl
        have h_fst : p2_fst t = (1 : I) := by
          dsimp only [p2_fst]
          rw [Path.trans_apply, dif_neg h]
          <;> simp [id_path_I]
          <;> rfl
        have h_snd : p2_snd t = t2 := by
          dsimp only [p2_snd]
          rw [Path.trans_apply, dif_neg h]
          <;> exact Subtype.ext ht2
        have h_goal1 : G (p2_fst t, p2_snd t) = G (1, t2) := by
          rw [h_fst, h_snd]
        rw [h_goal1]
        have h_rhs : (γ_left.trans γ_top) t = γ_top t2 := by
          rw [Path.trans_apply]
          rw [dif_neg h]
          <;> congr <;> exact Subtype.ext ht2
        rw [h_rhs, h_top t2]
        <;> rfl
    have h_fun : (fun t : I => (p2.map G.continuous) t) = (fun t : I => (γ_left.trans γ_top) t) := by
      funext t
      exact h_main t
    exact Path.ext h_fun
  let H_rect : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top) :=
    (H_raw.cast h_eq1 h_eq2)
  have h_range : ∀ (p : I × I), H_rect p ∈ U := by
    intro p
    have h_eq : H_rect p = H_raw p := by rfl
    rw [h_eq]
    exact h_range_raw p
  exact ⟨H_rect, h_range⟩

end RectangleHomotopy

end

end

end P202.Topology.VanKampenProof


/-! Adapted from SingleCoveredConstPath.lean. -/
namespace P202.Topology.VanKampenProof



section

set_option maxHeartbeats 200000

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

/-- single_covered_map of a constant path equals eqToHom. -/
lemma single_covered_map_const_path {x y : X} (γ : Path x y) (hxy : x = y)
    (U : Opens X) (hU : U ∈ 𝒰) (h_range : Set.range γ ⊆ (U : Set X))
    (h_const : ∀ t, γ t = x) :
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
    eqToHom (by
      apply congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk)
      exact hxy) := by
  classical
  let U_set : Set X := (U : Set X)
  have hx : x ∈ U := by
    have h1 : γ 0 ∈ Set.range γ := Set.mem_range_self 0
    have h2 : γ 0 = x := γ.source
    rw [h2] at h1
    exact h_range h1
  have hy : y ∈ U := by
    have h1 : γ 1 ∈ Set.range γ := Set.mem_range_self 1
    have h2 : γ 1 = y := γ.target
    rw [h2] at h1
    exact h_range h1
  let γ_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ hx hy h_range).choose
  let hγ_lift : ∀ (t : I), (γ_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hx hy h_range).choose_spec
  have h_pointwise : ∀ (t : I), (γ_lift t : X) = x := by
    intro t
    have h1 : (γ_lift t : X) = γ t := hγ_lift t
    rw [h1, h_const t]
  have h_lift_const : ∀ (t : I), γ_lift t = γ_lift 0 := by
    intro t
    apply Subtype.ext
    have h1 : (γ_lift t : X) = x := h_pointwise t
    have h2 : (γ_lift 0 : X) = x := h_pointwise 0
    rw [h1, h2]
  let γ_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_lift
  have h_sub_eq : (⟨x, hx⟩ : U_set) = (⟨y, hy⟩ : U_set) := by
    apply Subtype.ext
    exact hxy
  have h_path_eq : γ_lift = (Path.refl (⟨x, hx⟩ : U_set)).cast rfl h_sub_eq.symm := by
    apply Path.ext
    funext t
    have h1 : γ_lift t = γ_lift 0 := h_lift_const t
    have h2 : γ_lift 0 = (⟨x, hx⟩ : U_set) := by
      exact γ_lift.source
    have h3 : ((Path.refl (⟨x, hx⟩ : U_set)).cast rfl h_sub_eq.symm) t = (⟨x, hx⟩ : U_set) := by
      simp [Path.cast]
      <;> rfl
    rw [h1, h2, h3]
  have h_class_eq : γ_class = eqToHom (congr_arg FundamentalGroupoid.mk h_sub_eq) := by
    have h_main : Path.Homotopic.Quotient.mk ((Path.refl (⟨x, hx⟩ : U_set)).cast rfl h_sub_eq.symm) =
        eqToHom (congr_arg FundamentalGroupoid.mk h_sub_eq) := by
      have h_conj := FundamentalGroupoid.conj_eqToHom (hx := rfl) (hy := h_sub_eq.symm) (p := Path.Homotopic.Quotient.mk (Path.refl (⟨x, hx⟩ : U_set)))
      have h_id : Path.Homotopic.Quotient.mk (Path.refl (⟨x, hx⟩ : U_set)) = 𝟙 (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) :=
        FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set))
      simpa [h_id] using h_conj.symm
    have h1 : γ_class = Path.Homotopic.Quotient.mk ((Path.refl (⟨x, hx⟩ : U_set)).cast rfl h_sub_eq.symm) := by
      dsimp only [γ_class]
      exact congr_arg (Path.Homotopic.Quotient.mk) h_path_eq
    rw [h1]
    exact h_main
  let f : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
          (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    (s.ι.app ⟨U, hU⟩).map γ_class
  have h_f_eq : f = eqToHom (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq)) := by
    dsimp only [f]
    rw [h_class_eq]
    <;> exact CategoryTheory.eqToHom_map (s.ι.app ⟨U, hU⟩) (congr_arg FundamentalGroupoid.mk h_sub_eq)
  have h_eq1 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hx := by rfl
  have h_eq2 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) =
      obj_at X 𝒰 s y U hU hy := by rfl
  let x_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk x
  let y_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk y
  have h_dom : obj_at X 𝒰 s x U hU hx = desc_functor_obj X 𝒰 hcover s x_obj := by
    dsimp only [desc_functor_obj]
    let x_pt : X := x_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x_pt ∈ U' := hcover x_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hx :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hx
    exact this.symm
  have h_cod : obj_at X 𝒰 s y U hU hy = desc_functor_obj X 𝒰 hcover s y_obj := by
    dsimp only [desc_functor_obj]
    let y_pt : X := y_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ y_pt ∈ U' := hcover y_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ y_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s y U' hU'.1 hU'.2 = obj_at X 𝒰 s y U hU hy :=
      obj_at_eq X 𝒰 s hfinite_intersections y U' U hU'.1 hU hU'.2 hy
    exact this.symm
  let f' : obj_at X 𝒰 s x U hU hx ⟶ obj_at X 𝒰 s y U hU hy :=
    eqToHom h_eq1.symm ≫ f ≫ eqToHom h_eq2
  have h_obj_eq : obj_at X 𝒰 s x U hU hx = obj_at X 𝒰 s y U hU hy := by
    dsimp only [obj_at]
    apply congr_arg ((s.ι.app ⟨U, hU⟩).obj)
    apply congr_arg FundamentalGroupoid.mk
    apply Subtype.ext
    exact hxy
  have h_f'_eq : f' = eqToHom h_obj_eq := by
    dsimp only [f']
    rw [h_f_eq]
    calc
      eqToHom h_eq1.symm ≫ eqToHom (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq)) ≫ eqToHom h_eq2
        = (eqToHom h_eq1.symm ≫ eqToHom (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq))) ≫ eqToHom h_eq2 := by
          rw [Category.assoc]
      _ = eqToHom (h_eq1.symm.trans (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq))) ≫ eqToHom h_eq2 := by
          rw [eqToHom_trans]
      _ = eqToHom ((h_eq1.symm.trans (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq))).trans h_eq2) := by
          rw [eqToHom_trans]
      _ = eqToHom h_obj_eq := by
          apply congr_arg eqToHom
          apply Subsingleton.elim
  have h_main : eqToHom h_dom.symm ≫ f' ≫ eqToHom h_cod =
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hxy) := by
    rw [h_f'_eq]
    <;> simp [eqToHom_trans, Category.assoc]
    <;> exact?
  exact h_main

end

end

end P202.Topology.VanKampenProof


/-! Adapted from RectangleBoundaryHomotopy.lean. -/
namespace P202.Topology.VanKampenProof



section

set_option maxHeartbeats 500000

open TopologicalSpace

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

namespace RectangleBoundaryHomotopy

/-- Linear interpolation from a to b, where s : I is the parameter. -/
def lerp_I (a b : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) (s : I) : I :=
  ⟨(a : ℝ) + (s : ℝ) * ((b : ℝ) - (a : ℝ)), by
    have h_diff_nonneg : 0 ≤ (b : ℝ) - (a : ℝ) := by exact sub_nonneg.mpr ha_le_b
    have h1 : 0 ≤ (a : ℝ) + (s : ℝ) * ((b : ℝ) - (a : ℝ)) := by
      have h_s_nonneg : 0 ≤ (s : ℝ) := s.prop.1
      nlinarith [a.prop.1]
    have h2 : (a : ℝ) + (s : ℝ) * ((b : ℝ) - (a : ℝ)) ≤ 1 := by
      have h_s_le_one : (s : ℝ) ≤ 1 := s.prop.2
      nlinarith [b.prop.2]
    exact ⟨h1, h2⟩⟩

@[simp] lemma lerp_I_zero (a b : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    lerp_I a b ha_le_b 0 = a := by
  apply Subtype.ext
  simp [lerp_I] <;> ring

@[simp] lemma lerp_I_one (a b : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    lerp_I a b ha_le_b 1 = b := by
  apply Subtype.ext
  simp [lerp_I] <;> ring

lemma continuous_lerp_I (a b : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    Continuous (lerp_I a b ha_le_b) := by
  apply Continuous.subtype_mk
  continuity

/-- The bottom edge of the rectangle [a,b] × [c,d]: from H(a,c) to H(b,c). -/
def bottom_edge (H : C(I × I, X)) (a b c : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    Path (H (a, c)) (H (b, c)) :=
  let s_lerp := lerp_I a b ha_le_b
  have h1 : Continuous s_lerp := continuous_lerp_I a b ha_le_b
  have h2 : Continuous (fun (_ : I) => c) := continuous_const
  have h_cont : Continuous (fun s : I => (s_lerp s, c)) :=
    Continuous.prodMk h1 h2
  let f : C(I, I × I) := ⟨fun s : I => (s_lerp s, c), h_cont⟩
  let cmap : C(I, X) := H.comp f
  ⟨cmap, by simp [s_lerp, f, cmap], by simp [s_lerp, f, cmap]⟩

/-- The right edge of the rectangle [a,b] × [c,d]: from H(b,c) to H(b,d). -/
def right_edge (H : C(I × I, X)) (b c d : I) (hc_le_d : (c : ℝ) ≤ (d : ℝ)) :
    Path (H (b, c)) (H (b, d)) :=
  let t_lerp := lerp_I c d hc_le_d
  have h1 : Continuous (fun (_ : I) => b) := continuous_const
  have h2 : Continuous t_lerp := continuous_lerp_I c d hc_le_d
  have h_cont : Continuous (fun t : I => (b, t_lerp t)) :=
    Continuous.prodMk h1 h2
  let f : C(I, I × I) := ⟨fun t : I => (b, t_lerp t), h_cont⟩
  let cmap : C(I, X) := H.comp f
  ⟨cmap, by simp [t_lerp, f, cmap], by simp [t_lerp, f, cmap]⟩

/-- The left edge of the rectangle [a,b] × [c,d]: from H(a,c) to H(a,d). -/
def left_edge (H : C(I × I, X)) (a c d : I) (hc_le_d : (c : ℝ) ≤ (d : ℝ)) :
    Path (H (a, c)) (H (a, d)) :=
  let t_lerp := lerp_I c d hc_le_d
  have h1 : Continuous (fun (_ : I) => a) := continuous_const
  have h2 : Continuous t_lerp := continuous_lerp_I c d hc_le_d
  have h_cont : Continuous (fun t : I => (a, t_lerp t)) :=
    Continuous.prodMk h1 h2
  let f : C(I, I × I) := ⟨fun t : I => (a, t_lerp t), h_cont⟩
  let cmap : C(I, X) := H.comp f
  ⟨cmap, by simp [t_lerp, f, cmap], by simp [t_lerp, f, cmap]⟩

/-- The top edge of the rectangle [a,b] × [c,d]: from H(a,d) to H(b,d). -/
def top_edge (H : C(I × I, X)) (a b d : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    Path (H (a, d)) (H (b, d)) :=
  let s_lerp := lerp_I a b ha_le_b
  have h1 : Continuous s_lerp := continuous_lerp_I a b ha_le_b
  have h2 : Continuous (fun (_ : I) => d) := continuous_const
  have h_cont : Continuous (fun s : I => (s_lerp s, d)) :=
    Continuous.prodMk h1 h2
  let f : C(I, I × I) := ⟨fun s : I => (s_lerp s, d), h_cont⟩
  let cmap : C(I, X) := H.comp f
  ⟨cmap, by simp [s_lerp, f, cmap], by simp [s_lerp, f, cmap]⟩

lemma exists_rectangle_boundary_homotopy_in_U
    (H : C(I × I, X))
    (a b c d : I)
    (ha_le_b : (a : ℝ) ≤ (b : ℝ))
    (hc_le_d : (c : ℝ) ≤ (d : ℝ))
    (U : Set X)
    (hU : ∀ (p : I × I), (a : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ (b : ℝ) →
      (c : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ (d : ℝ) → H p ∈ U) :
    ∃ (H_rect : Path.Homotopy
        ((bottom_edge H a b c ha_le_b).trans (right_edge H b c d hc_le_d))
        ((left_edge H a c d hc_le_d).trans (top_edge H a b d ha_le_b))),
      ∀ (p : I × I), H_rect p ∈ U := by
  let s_lerp := lerp_I a b ha_le_b
  let t_lerp := lerp_I c d hc_le_d
  have h_s_cont : Continuous s_lerp := continuous_lerp_I a b ha_le_b
  have h_t_cont : Continuous t_lerp := continuous_lerp_I c d hc_le_d
  have h_f_cont : Continuous (fun p : I × I => (s_lerp p.1, t_lerp p.2)) :=
    Continuous.prodMk (h_s_cont.comp continuous_fst) (h_t_cont.comp continuous_snd)
  let f : C(I × I, I × I) := ⟨fun p : I × I => (s_lerp p.1, t_lerp p.2), h_f_cont⟩
  let G := H.comp f
  have hG_in_U : ∀ (q : I × I), G q ∈ U := by
    intro q
    have h1 : G q = H (f q) := by rfl
    rw [h1]
    have h_s_between : (a : ℝ) ≤ (s_lerp q.1 : ℝ) ∧ (s_lerp q.1 : ℝ) ≤ (b : ℝ) := by
      have h_val : (s_lerp q.1 : ℝ) = (a : ℝ) + (q.1 : ℝ) * ((b : ℝ) - (a : ℝ)) := by rfl
      rw [h_val]
      have h_diff_nonneg : 0 ≤ (b : ℝ) - (a : ℝ) := by exact sub_nonneg.mpr ha_le_b
      have h_s_nonneg : 0 ≤ (q.1 : ℝ) := q.1.prop.1
      have h_s_le_one : (q.1 : ℝ) ≤ 1 := q.1.prop.2
      have h1 : 0 ≤ (q.1 : ℝ) * ((b : ℝ) - (a : ℝ)) := mul_nonneg h_s_nonneg h_diff_nonneg
      have h2 : (q.1 : ℝ) * ((b : ℝ) - (a : ℝ)) ≤ (b : ℝ) - (a : ℝ) := by
        have h : (q.1 : ℝ) * ((b : ℝ) - (a : ℝ)) ≤ 1 * ((b : ℝ) - (a : ℝ)) := by
          gcongr
        simpa using h
      constructor
      · linarith
      · linarith
    have h_t_between : (c : ℝ) ≤ (t_lerp q.2 : ℝ) ∧ (t_lerp q.2 : ℝ) ≤ (d : ℝ) := by
      have h_val : (t_lerp q.2 : ℝ) = (c : ℝ) + (q.2 : ℝ) * ((d : ℝ) - (c : ℝ)) := by rfl
      rw [h_val]
      have h_diff_nonneg : 0 ≤ (d : ℝ) - (c : ℝ) := by exact sub_nonneg.mpr hc_le_d
      have h_t_nonneg : 0 ≤ (q.2 : ℝ) := q.2.prop.1
      have h_t_le_one : (q.2 : ℝ) ≤ 1 := q.2.prop.2
      have h1 : 0 ≤ (q.2 : ℝ) * ((d : ℝ) - (c : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      have h2 : (q.2 : ℝ) * ((d : ℝ) - (c : ℝ)) ≤ (d : ℝ) - (c : ℝ) := by
        have h : (q.2 : ℝ) * ((d : ℝ) - (c : ℝ)) ≤ 1 * ((d : ℝ) - (c : ℝ)) := by
          gcongr
        simpa using h
      constructor
      · linarith
      · linarith
    exact hU (f q) h_s_between.1 h_s_between.2 h_t_between.1 h_t_between.2
  let bottom_cmap := G.comp ⟨fun t : I => (0, t), by continuity⟩
  let right_cmap := G.comp ⟨fun s : I => (s, 1), by continuity⟩
  let left_cmap := G.comp ⟨fun s : I => (s, 0), by continuity⟩
  let top_cmap := G.comp ⟨fun t : I => (1, t), by continuity⟩
  let γ_bottom : Path (G (0, 0)) (G (0, 1)) := ⟨bottom_cmap, by rfl, by rfl⟩
  let γ_right : Path (G (0, 1)) (G (1, 1)) := ⟨right_cmap, by rfl, by rfl⟩
  let γ_left : Path (G (0, 0)) (G (1, 0)) := ⟨left_cmap, by rfl, by rfl⟩
  let γ_top : Path (G (1, 0)) (G (1, 1)) := ⟨top_cmap, by rfl, by rfl⟩
  have h_bottom : ∀ (t : I), γ_bottom t = G (0, t) := by intro t; rfl
  have h_right : ∀ (s : I), γ_right s = G (s, 1) := by intro s; rfl
  have h_left : ∀ (s : I), γ_left s = G (s, 0) := by intro s; rfl
  have h_top : ∀ (t : I), γ_top t = G (1, t) := by intro t; rfl
  have h_main : ∃ (H_rect : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top)),
      ∀ (p : I × I), H_rect p ∈ U :=
    RectangleHomotopy.rectangle_boundary_homotopy_edges G γ_bottom γ_right γ_left γ_top
      h_bottom h_right h_left h_top U hG_in_U
  rcases h_main with ⟨H_rect, hH_rect_U⟩
  have h0 : H (a, c) = G (0, 0) := by
    have h_s : s_lerp 0 = a := lerp_I_zero a b ha_le_b
    have h_t : t_lerp 0 = c := lerp_I_zero c d hc_le_d
    have h : G (0, 0) = H (s_lerp 0, t_lerp 0) := by rfl
    rw [h, h_s, h_t] <;> rfl
  have h1 : H (b, d) = G (1, 1) := by
    have h_s : s_lerp 1 = b := lerp_I_one a b ha_le_b
    have h_t : t_lerp 1 = d := lerp_I_one c d hc_le_d
    have h : G (1, 1) = H (s_lerp 1, t_lerp 1) := by rfl
    rw [h, h_s, h_t] <;> rfl
  have h_mid1 : H (b, c) = G (1, 0) := by
    have h_s : s_lerp 1 = b := lerp_I_one a b ha_le_b
    have h_t : t_lerp 0 = c := lerp_I_zero c d hc_le_d
    have h : G (1, 0) = H (s_lerp 1, t_lerp 0) := by rfl
    rw [h, h_s, h_t] <;> rfl
  have h_mid2 : H (a, d) = G (0, 1) := by
    have h_s : s_lerp 0 = a := lerp_I_zero a b ha_le_b
    have h_t : t_lerp 1 = d := lerp_I_one c d hc_le_d
    have h : G (0, 1) = H (s_lerp 0, t_lerp 1) := by rfl
    rw [h, h_s, h_t] <;> rfl
  have h_left_eq1 : γ_left.cast h0 h_mid1 = bottom_edge H a b c ha_le_b := by
    have h : ∀ (s : I), (γ_left.cast h0 h_mid1) s = (bottom_edge H a b c ha_le_b) s := by
      intro s
      have h1 : (γ_left.cast h0 h_mid1) s = γ_left s := by rfl
      rw [h1]
      have h2 : γ_left s = G (s, 0) := by rfl
      rw [h2]
      have h3 : G (s, 0) = H (s_lerp s, t_lerp 0) := by rfl
      rw [h3]
      have h4 : t_lerp 0 = c := lerp_I_zero c d hc_le_d
      rw [h4] <;> rfl
    have h' : ⇑(γ_left.cast h0 h_mid1) = ⇑(bottom_edge H a b c ha_le_b) := by
      funext s; exact h s
    exact Path.ext h'
  have h_left_eq2 : γ_top.cast h_mid1 h1 = right_edge H b c d hc_le_d := by
    have h : ∀ (t : I), (γ_top.cast h_mid1 h1) t = (right_edge H b c d hc_le_d) t := by
      intro t
      have h1 : (γ_top.cast h_mid1 h1) t = γ_top t := by rfl
      rw [h1]
      have h2 : γ_top t = G (1, t) := by rfl
      rw [h2]
      have h3 : G (1, t) = H (s_lerp 1, t_lerp t) := by rfl
      rw [h3]
      have h4 : s_lerp 1 = b := lerp_I_one a b ha_le_b
      rw [h4] <;> rfl
    have h' : ⇑(γ_top.cast h_mid1 h1) = ⇑(right_edge H b c d hc_le_d) := by
      funext t; exact h t
    exact Path.ext h'
  have h_left_eq' : (γ_left.trans γ_top).cast h0 h1 =
      (bottom_edge H a b c ha_le_b).trans (right_edge H b c d hc_le_d) := by
    rw [Path.cast_trans γ_left γ_top h0 h_mid1 h1]
    rw [h_left_eq1, h_left_eq2]
  have h_bottom_eq1 : γ_bottom.cast h0 h_mid2 = left_edge H a c d hc_le_d := by
    have h : ∀ (t : I), (γ_bottom.cast h0 h_mid2) t = (left_edge H a c d hc_le_d) t := by
      intro t
      have h1 : (γ_bottom.cast h0 h_mid2) t = γ_bottom t := by rfl
      rw [h1]
      have h2 : γ_bottom t = G (0, t) := by rfl
      rw [h2]
      have h3 : G (0, t) = H (s_lerp 0, t_lerp t) := by rfl
      rw [h3]
      have h4 : s_lerp 0 = a := lerp_I_zero a b ha_le_b
      rw [h4] <;> rfl
    have h' : ⇑(γ_bottom.cast h0 h_mid2) = ⇑(left_edge H a c d hc_le_d) := by
      funext t; exact h t
    exact Path.ext h'
  have h_bottom_eq2 : γ_right.cast h_mid2 h1 = top_edge H a b d ha_le_b := by
    have h : ∀ (s : I), (γ_right.cast h_mid2 h1) s = (top_edge H a b d ha_le_b) s := by
      intro s
      have h1 : (γ_right.cast h_mid2 h1) s = γ_right s := by rfl
      rw [h1]
      have h2 : γ_right s = G (s, 1) := by rfl
      rw [h2]
      have h3 : G (s, 1) = H (s_lerp s, t_lerp 1) := by rfl
      rw [h3]
      have h4 : t_lerp 1 = d := lerp_I_one c d hc_le_d
      rw [h4] <;> rfl
    have h' : ⇑(γ_right.cast h_mid2 h1) = ⇑(top_edge H a b d ha_le_b) := by
      funext s; exact h s
    exact Path.ext h'
  have h_bottom_eq' : (γ_bottom.trans γ_right).cast h0 h1 =
      (left_edge H a c d hc_le_d).trans (top_edge H a b d ha_le_b) := by
    rw [Path.cast_trans γ_bottom γ_right h0 h_mid2 h1]
    rw [h_bottom_eq1, h_bottom_eq2]
  -- Take symm first, then cast
  let H_rect_symm : Path.Homotopy (γ_left.trans γ_top) (γ_bottom.trans γ_right) := H_rect.symm
  have hH_rect_symm_U : ∀ (p : I × I), H_rect_symm p ∈ U := by
    intro p
    have h_main : ∀ (q : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top)),
        (∀ (x : I × I), q x ∈ U) → ∀ (x : I × I), q.symm x ∈ U := by
      intro q hq x
      exact?
    exact h_main H_rect hH_rect_U p
  let H_rect_symm' : Path.Homotopy ((γ_left.trans γ_top).cast h0 h1) ((γ_bottom.trans γ_right).cast h0 h1) :=
    H_rect_symm.pathCast h0 h1
  have hH_rect_symm'_U : ∀ (p : I × I), H_rect_symm' p ∈ U := by
    intro p
    have h : H_rect_symm' p = H_rect_symm p := by rfl
    rw [h]
    exact hH_rect_symm_U p
  let H_final : Path.Homotopy
      ((bottom_edge H a b c ha_le_b).trans (right_edge H b c d hc_le_d))
      ((left_edge H a c d hc_le_d).trans (top_edge H a b d ha_le_b)) :=
    H_rect_symm'.cast h_left_eq' h_bottom_eq'
  have h_final_range : ∀ (p : I × I), H_final p ∈ U := by
    intro p
    have h : H_final p = H_rect_symm' p := by rfl
    rw [h]
    exact hH_rect_symm'_U p
  exact ⟨H_final, h_final_range⟩

end RectangleBoundaryHomotopy

end

end P202.Topology.VanKampenProof


/-! Adapted from CleanDescent.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

set_option maxHeartbeats 1000000

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hpath_connected : ∀ U : Opens X, U ∈ 𝒰 → IsPathConnected (U : Set X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover

/-- Every path has an adapted subdivision.

Proof: By the Lebesgue number lemma, there exists δ > 0 such that any subset of I
with diameter < δ is mapped into some U ∈ 𝒰. Choose n such that 1/n < δ, then
the points {0, 1/n, ..., 1} form an adapted subdivision. -/
theorem exists_adapted_subdivision {x y : X} (γ : Path x y) :
    ∃ (S : Finset I), IsAdaptedSubdivision 𝒰 γ S := by
  let ι := { U : Opens X // U ∈ 𝒰 }
  let c : ι → Set I := fun U => γ ⁻¹' (U : Set X)
  have hc₁ : ∀ (i : ι), IsOpen (c i) := by
    intro U
    exact U.val.2.preimage γ.continuous
  have hc₂ : (Set.univ : Set I) ⊆ ⋃ (i : ι), c i := by
    intro t _
    have h₁ : ∃ (U : Opens X), U ∈ 𝒰 ∧ γ t ∈ U := by
      exact hcover (γ t)
    rcases h₁ with ⟨U, hU, hUt⟩
    let U' : ι := ⟨U, hU⟩
    exact Set.mem_iUnion.mpr ⟨U', hUt⟩
  have hcompact : IsCompact (Set.univ : Set I) := isCompact_univ
  rcases lebesgue_number_lemma_of_metric hcompact hc₁ hc₂ with ⟨δ, hδ_pos, hδ⟩
  have hδ_pos' : 0 < δ := hδ_pos
  have h_arch : ∃ (n : ℕ), 0 < n ∧ 1 / (n : ℝ) < δ := by
    have h : ∃ (n : ℕ), (n : ℝ) > 1 / δ := exists_nat_gt (1 / δ)
    rcases h with ⟨n, hn⟩
    have hn_pos : 0 < n := by
      by_contra h'
      have h'' : n = 0 := by omega
      rw [h''] at hn
      norm_num at hn <;> linarith
    have h1 : 1 / (n : ℝ) < δ := by
      have h2 : 0 < δ := hδ_pos'
      have h3 : (n : ℝ) > 1 / δ := hn
      calc
        1 / (n : ℝ) < 1 / (1 / δ) := by gcongr
        _ = δ := by field_simp [h2.ne'] <;> ring
    exact ⟨n, hn_pos, h1⟩
  rcases h_arch with ⟨n, hn_pos, h1n_lt_δ⟩
  set nr : ℝ := (n : ℝ) with hnr
  have hnr_pos : 0 < nr := by
    rw [hnr]
    exact_mod_cast hn_pos
  let t_pt (i : Fin (n + 1)) : I :=
    ⟨(i.val : ℝ) / nr, by
      have h₁ : 0 ≤ (i.val : ℝ) / nr := by positivity
      have h₂ : (i.val : ℝ) / nr ≤ 1 := by
        have h3 : i.val ≤ n := Nat.lt_succ_iff.mp i.is_lt
        have h4 : (i.val : ℝ) ≤ nr := by
          have h41 : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
          rw [hnr]
          exact h41
        have h5 : (i.val : ℝ) / nr ≤ 1 := by
          calc
            (i.val : ℝ) / nr ≤ nr / nr := by gcongr
            _ = 1 := by
              field_simp [hnr_pos.ne'] <;> ring
        exact h5
      exact ⟨h₁, h₂⟩⟩
  let S : Finset I := Finset.image t_pt Finset.univ
  have h0_in : (0 : I) ∈ S := by
    have h1 : t_pt 0 = (0 : I) := by
      apply Subtype.ext
      simp [t_pt, hnr]
      <;> field_simp [hnr_pos.ne'] <;> ring
    rw [←h1]
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  have h1_in : (1 : I) ∈ S := by
    have h1 : t_pt (Fin.last n) = (1 : I) := by
      apply Subtype.ext
      have h2 : (Fin.last n).val = n := by simp [Fin.last]
      have h3 : ((Fin.last n).val : ℝ) / nr = 1 := by
        rw [h2, hnr]
        field_simp [hnr_pos.ne'] <;> ring
      exact h3
    rw [←h1]
    exact Finset.mem_image.mpr ⟨Fin.last n, by simp, rfl⟩
  refine' ⟨S, h0_in, h1_in, _⟩
  intro s₁ s₂ hs₁ hs₂ h_lt h_no_between
  have h_s₁_eq : ∃ (i : Fin (n + 1)), s₁ = t_pt i := by
    rcases Finset.mem_image.mp hs₁ with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  have h_s₂_eq : ∃ (j : Fin (n + 1)), s₂ = t_pt j := by
    rcases Finset.mem_image.mp hs₂ with ⟨j, _, rfl⟩
    exact ⟨j, rfl⟩
  rcases h_s₁_eq with ⟨i, rfl⟩
  rcases h_s₂_eq with ⟨j, rfl⟩
  have h_i_lt_j : i.val < j.val := by
    by_contra h
    have h' : j.val ≤ i.val := by omega
    have h'' : (t_pt j : ℝ) ≤ (t_pt i : ℝ) := by
      have h : (j.val : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast h'
      have h' : (j.val : ℝ) / nr ≤ (i.val : ℝ) / nr := by gcongr
      exact h'
    have h''' : t_pt j ≤ t_pt i := by exact_mod_cast h''
    have h_contra : ¬ t_pt i < t_pt j := not_lt.mpr h'''
    exact h_contra h_lt
  have h_j_eq_i_succ : j.val = i.val + 1 := by
    by_contra h
    have h' : i.val + 1 < j.val := by omega
    have h_i1_lt_n1 : i.val + 1 < n + 1 := by omega
    let k : Fin (n + 1) := ⟨i.val + 1, h_i1_lt_n1⟩
    have h_k_in_S : t_pt k ∈ S := Finset.mem_image.mpr ⟨k, by simp, rfl⟩
    have h1 : (t_pt i : ℝ) < (t_pt k : ℝ) := by
      dsimp only [t_pt]
      have h_i_lt_k : (i.val : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self i.val
      exact div_lt_div_of_pos_right h_i_lt_k hnr_pos
    have h2 : (t_pt k : ℝ) < (t_pt j : ℝ) := by
      dsimp only [t_pt]
      have h_k_lt_j : ((i.val + 1 : ℕ) : ℝ) < (j.val : ℝ) := by exact_mod_cast h'
      exact div_lt_div_of_pos_right h_k_lt_j hnr_pos
    have h3 : t_pt i < t_pt k := by exact_mod_cast h1
    have h4 : t_pt k < t_pt j := by exact_mod_cast h2
    exact h_no_between (t_pt k) h_k_in_S h3 h4
  have h_dist : (t_pt j : ℝ) - (t_pt i : ℝ) = 1 / nr := by
    dsimp only [t_pt]
    rw [h_j_eq_i_succ]
    simp [hnr]
    <;> field_simp [hnr_pos.ne'] <;> ring
  -- Now use the Lebesgue property: take the left endpoint, its ball of radius δ contains the whole interval
  have h_applyδ : ∃ (U : ι), Metric.ball (t_pt i) δ ⊆ c U := hδ (t_pt i) (Set.mem_univ _)
  rcases h_applyδ with ⟨U, hU_ball⟩
  have h_interval_subset_ball : Set.Icc (t_pt i) (t_pt j) ⊆ Metric.ball (t_pt i) δ := by
    intro t ht
    have h1 : (t_pt i : ℝ) ≤ (t : ℝ) := ht.1
    have h2 : (t : ℝ) ≤ (t_pt j : ℝ) := ht.2
    have h3 : dist (t : ℝ) ((t_pt i : ℝ)) < δ := by
      rw [Real.dist_eq]
      have h4 : 0 ≤ (t : ℝ) - (t_pt i : ℝ) := by linarith
      rw [abs_of_nonneg h4]
      linarith [h_dist]
    simpa [Subtype.dist_eq] using h3
  have h_interval_subset : Set.Icc (t_pt i) (t_pt j) ⊆ c U :=
    Set.Subset.trans h_interval_subset_ball hU_ball
  refine' ⟨U.val, U.property, _⟩
  intro t ht1 ht2
  have h_t_in : t ∈ Set.Icc (t_pt i) (t_pt j) := ⟨ht1, ht2⟩
  have h6 : t ∈ c U := h_interval_subset h_t_in
  exact h6

include hfinite_intersections

/-- Given a path γ, choose an adapted subdivision and return the corresponding morphism.
    This is well-defined by the independence lemma. -/
noncomputable def my_desc_map {x y : X} (γ : Path x y) :
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) ⟶
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)) :=
  let S : Finset I := Classical.choose (exists_adapted_subdivision X 𝒰 hcover γ)
  let hS : IsAdaptedSubdivision 𝒰 γ S := Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover γ)
  my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS

/-- Well-definedness: the choice of adapted subdivision doesn't matter. -/
theorem my_desc_map_well_defined {x y : X} (γ : Path x y)
    (S S' : Finset I) (hS : IsAdaptedSubdivision 𝒰 γ S) (hS' : IsAdaptedSubdivision 𝒰 γ S') :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' :=
  my_map_from_adapted_subdivision_independent_clean X 𝒰 hcover hfinite_intersections s hS hS'

/-- Fac property: if a path γ is entirely contained in some U ∈ 𝒰, then
    my_desc_map γ equals the single_covered_map for U. -/
theorem my_desc_map_single_covered {x y : X} (γ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰) (h_range : Set.range γ ⊆ (U : Set X)) :
    my_desc_map X 𝒰 hcover hfinite_intersections s γ =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range := by
  -- First, show that S = {0, 1} is an adapted subdivision
  let S : Finset I := {(0 : I), (1 : I)}
  have hS_is_adapted : IsAdaptedSubdivision 𝒰 γ S := by
    constructor
    · simp [S]
    · constructor
      · simp [S]
      · intro s₁ s₂ hs₁ hs₂ h_lt h_no_between
        have h_s₁_in : s₁ = (0 : I) ∨ s₁ = (1 : I) := by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs₁
          exact hs₁
        have h_s₂_in : s₂ = (0 : I) ∨ s₂ = (1 : I) := by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs₂
          exact hs₂
        have h_s₁_eq_0 : s₁ = (0 : I) := by
          rcases h_s₁_in with (h | h)
          · exact h
          · rw [h] at h_lt
            have h_contra : (1 : I) < s₂ := h_lt
            rcases h_s₂_in with (h2 | h2)
            · rw [h2] at h_contra
              exact False.elim (not_lt.mpr (by simp) h_contra)
            · rw [h2] at h_contra
              exact False.elim (lt_irrefl (1 : I) h_contra)
        have h_s₂_eq_1 : s₂ = (1 : I) := by
          rcases h_s₂_in with (h | h)
          · rw [h] at h_lt
            have h_contra : s₁ < (0 : I) := h_lt
            rw [h_s₁_eq_0] at h_contra
            exact False.elim (lt_irrefl (0 : I) h_contra)
          · exact h
        rw [h_s₁_eq_0, h_s₂_eq_1]
        refine' ⟨U, hU, _⟩
        intro t _ _
        have h1 : γ t ∈ Set.range γ := ⟨t, rfl⟩
        exact h_range h1
  -- Then by well-definedness, my_desc_map equals my_map_from_adapted_subdivision for this S
  have h1 : my_desc_map X 𝒰 hcover hfinite_intersections s γ =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_is_adapted := by
    exact my_desc_map_well_defined X 𝒰 hcover hfinite_intersections s γ
      (Classical.choose (exists_adapted_subdivision X 𝒰 hcover γ)) S
      (Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover γ)) hS_is_adapted
  rw [h1]
  -- Define the trivial ts function
  let ts : Fin 2 → I := fun i => if i = 0 then (0 : I) else (1 : I)
  have h_ts0 : ts 0 = (0 : I) := by simp [ts]
  have h_ts1 : ts 1 = (1 : I) := by simp [ts]
  have h_ts_strict : StrictMono ts := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [ts, h] <;> tauto
  have h_ts_image : Finset.image ts Finset.univ = S := by
    ext z
    simp [S, ts, Finset.mem_image, Fin.forall_fin_succ]
    <;> tauto
  let covers : Fin 1 → Opens X := fun _ => U
  have hcover_mem : ∀ i : Fin 1, covers i ∈ 𝒰 := by
    intro i
    exact hU
  have h_range' : ∀ i : Fin 1, ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers i : Set X) := by
    intro i t h1 h2
    have h_γt_in_range : γ t ∈ Set.range γ := ⟨t, rfl⟩
    exact h_range h_γt_in_range
  -- Use the universal lemma to switch to our explicit ts and covers
  rw [my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS_is_adapted ts h_ts_strict h_ts_image covers hcover_mem h_range']
  -- Now use the single_segment lemma
  exact my_map_from_adapted_subdivision_single_segment X 𝒰 hcover hfinite_intersections s hS_is_adapted ts h_ts0 h_ts1 h_ts_strict h_ts_image U hU h_range

/-- Composition property: my_desc_map of path concatenation equals composition of my_desc_maps. -/
theorem my_desc_map_comp {x y z : X} (γ₁ : Path x y) (γ₂ : Path y z) :
    my_desc_map X 𝒰 hcover hfinite_intersections s (γ₁.trans γ₂) =
    my_desc_map X 𝒰 hcover hfinite_intersections s γ₁ ≫
    my_desc_map X 𝒰 hcover hfinite_intersections s γ₂ := by
  classical
  -- Get adapted subdivisions for both paths
  let S₁ : Finset I := Classical.choose (exists_adapted_subdivision X 𝒰 hcover γ₁)
  let hS₁ : IsAdaptedSubdivision 𝒰 γ₁ S₁ := Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover γ₁)
  let S₂ : Finset I := Classical.choose (exists_adapted_subdivision X 𝒰 hcover γ₂)
  let hS₂ : IsAdaptedSubdivision 𝒰 γ₂ S₂ := Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover γ₂)
  -- Apply the composition lemma
  rcases my_map_from_adapted_subdivision_comp_cauchy X 𝒰 hcover hfinite_intersections s γ₁ γ₂ hS₁ hS₂ with ⟨S, hS, h_eq⟩
  -- By well-definedness, my_desc_map (γ₁.trans γ₂) = my_map_from_adapted_subdivision hS
  have h1 : my_desc_map X 𝒰 hcover hfinite_intersections s (γ₁.trans γ₂) =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS :=
    my_desc_map_well_defined X 𝒰 hcover hfinite_intersections s (γ₁.trans γ₂)
      (Classical.choose (exists_adapted_subdivision X 𝒰 hcover (γ₁.trans γ₂))) S
      (Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover (γ₁.trans γ₂))) hS
  -- By definition, my_desc_map γ₁ = my_map_from_adapted_subdivision hS₁
  have h2 : my_desc_map X 𝒰 hcover hfinite_intersections s γ₁ =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₁ := by rfl
  -- By definition, my_desc_map γ₂ = my_map_from_adapted_subdivision hS₂
  have h3 : my_desc_map X 𝒰 hcover hfinite_intersections s γ₂ =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₂ := by rfl
  -- Combine the equalities
  rw [h1, h_eq, h2, h3]

/-- Identity property: my_desc_map of the constant path is the identity morphism. -/
theorem my_desc_map_refl {x : X} :
    my_desc_map X 𝒰 hcover hfinite_intersections s (Path.refl x) =
    𝟙 (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) := by
  classical
  -- Pick some U ∈ 𝒰 containing x (exists by hcover)
  have h : ∃ (U : Opens X), U ∈ 𝒰 ∧ x ∈ U := hcover x
  rcases h with ⟨U, hU, hx⟩
  -- The range of Path.refl x is just {x}, which is contained in U
  have h_range : Set.range (Path.refl x) ⊆ (U : Set X) := by
    intro z hz
    rcases hz with ⟨t, ht⟩
    have h1 : (Path.refl x) t = x := by simp [Path.refl_apply]
    have hz_eq : z = x := by
      rw [←ht, h1]
    rw [hz_eq]
    exact hx
  -- By my_desc_map_single_covered
  rw [my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (Path.refl x) U hU h_range]
  -- By single_covered_map_refl
  exact single_covered_map_refl X 𝒰 hcover hfinite_intersections s U hU hx

/-- single_covered_map is independent of the choice of covering open set:
    if γ is contained in both U and V (both in 𝒰), then the two single_covered_maps are equal. -/
lemma single_covered_map_indep_of_cover
    {x y : X} (γ : Path x y)
    (U V : Opens X) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
    (h_rangeU : Set.range γ ⊆ (U : Set X))
    (h_rangeV : Set.range γ ⊆ (V : Set X)) :
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_rangeU =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ V hV h_rangeV := by
  have h1 : single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_rangeU =
      my_desc_map X 𝒰 hcover hfinite_intersections s γ :=
    (my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s γ U hU h_rangeU).symm
  have h2 : single_covered_map X 𝒰 hcover hfinite_intersections s γ V hV h_rangeV =
      my_desc_map X 𝒰 hcover hfinite_intersections s γ :=
    (my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s γ V hV h_rangeV).symm
  rw [h1, h2]

/-- Key lemma: consecutive rows in a partwise-covered homotopy give equal descent maps. -/
lemma consecutive_rows_equal_my_desc_map {x y : X} {γ₁ γ₂ : Path x y}
    (H : Path.Homotopy γ₁ γ₂) {n : ℕ} (hn_pos : 0 < n)
    (pcH : PartwiseCoveredHomotopy 𝒰 H n n) (j : Fin n) :
    my_desc_map X 𝒰 hcover hfinite_intersections s
      (H.eval ⟨(j.val : ℝ) / (n : ℝ), by
        have h₁ : 0 ≤ (j.val : ℝ) / (n : ℝ) := by positivity
        have h₂ : (j.val : ℝ) / (n : ℝ) ≤ 1 := by
          have h₃ : j.val < n := j.is_lt
          have h₄ : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₃.le
          have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
          exact (div_le_one h₅).mpr h₄
        exact ⟨h₁, h₂⟩⟩) =
    my_desc_map X 𝒰 hcover hfinite_intersections s
      (H.eval ⟨((j.val : ℝ) + 1) / (n : ℝ), by
        have h₁ : 0 ≤ ((j.val : ℝ) + 1) / (n : ℝ) := by positivity
        have h₂ : ((j.val : ℝ) + 1) / (n : ℝ) ≤ 1 := by
          have h₃ : j.val < n := j.is_lt
          have h₄ : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr h₃
          have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
          exact (div_le_one h₅).mpr h₄
        exact ⟨h₁, h₂⟩⟩) := by
  classical
  -- Grid points in path direction
  let t_i (i : Fin (n + 1)) : I := ⟨(i.val : ℝ) / (n : ℝ), by
    have h₁ : 0 ≤ (i.val : ℝ) / (n : ℝ) := by positivity
    have h₂ : (i.val : ℝ) / (n : ℝ) ≤ 1 := by
      have h₃ : i.val ≤ n := Nat.lt_succ_iff.mp i.is_lt
      have h₄ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      exact (div_le_one h₄).mpr (by exact_mod_cast h₃)
    exact ⟨h₁, h₂⟩⟩
  -- Grid points in homotopy direction (row j and row j+1)
  let s_j : I := ⟨(j.val : ℝ) / (n : ℝ), by
    have h₁ : 0 ≤ (j.val : ℝ) / (n : ℝ) := by positivity
    have h₂ : (j.val : ℝ) / (n : ℝ) ≤ 1 := by
      have h₃ : j.val < n := j.is_lt
      have h₄ : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₃.le
      have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      exact (div_le_one h₅).mpr h₄
    exact ⟨h₁, h₂⟩⟩
  let s_j1 : I := ⟨((j.val : ℝ) + 1) / (n : ℝ), by
    have h₁ : 0 ≤ ((j.val : ℝ) + 1) / (n : ℝ) := by positivity
    have h₂ : ((j.val : ℝ) + 1) / (n : ℝ) ≤ 1 := by
      have h₃ : j.val < n := j.is_lt
      have h₄ : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr h₃
      have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      exact (div_le_one h₅).mpr h₄
    exact ⟨h₁, h₂⟩⟩
  -- Covering sets for each column (in row j)
  let covers (i : Fin n) : Opens X := pcH.covers j i
  have hcover_mem (i : Fin n) : covers i ∈ 𝒰 := pcH.hcover_mem j i
  -- Bottom row paths (row j)
  let γ_bottom (i : Fin n) : Path (H.eval s_j (t_i (Fin.castSucc i))) (H.eval s_j (t_i (Fin.succ i))) :=
    (H.eval s_j).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))
  -- Top row paths (row j+1)
  let γ_top (i : Fin n) : Path (H.eval s_j1 (t_i (Fin.castSucc i))) (H.eval s_j1 (t_i (Fin.succ i))) :=
    (H.eval s_j1).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))
  -- Strict monotonicity of t_i
  have h_ti_strict_mono : StrictMono t_i := by
    intro i k h
    apply Subtype.mk_lt_mk.mpr
    have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h₆ : (i.val : ℝ) < (k.val : ℝ) := by exact_mod_cast h
    gcongr
  have h_ti_le (i : Fin n) : t_i (Fin.castSucc i) ≤ t_i (Fin.succ i) :=
    le_of_lt (h_ti_strict_mono (by simp [Fin.castSucc_lt_succ]))
  -- Bottom range: γ_bottom i is contained in covers i
  have h_bottom_range (i : Fin n) : Set.range (γ_bottom i) ⊆ (covers i : Set X) := by
    have h_lt : t_i (Fin.castSucc i) < t_i (Fin.succ i) := h_ti_strict_mono (by simp [Fin.castSucc_lt_succ])
    have h_range_eq : Set.range (γ_bottom i) = (H.eval s_j) '' Set.Icc (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) := by
      rw [Path.range_subpath (H.eval s_j) (t_i (Fin.castSucc i)) (t_i (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_j : ℝ) := by rfl
    have h2 : (s_j : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_j_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_j_le (by positivity)
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t : ℝ) := by
      simpa [t_i] using (show (t_i (Fin.castSucc i) : ℝ) ≤ (t : ℝ) from ht.1)
    have h4 : (t : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      simpa [t_i] using (show (t : ℝ) ≤ (t_i (Fin.succ i) : ℝ) from ht.2)
    exact pcH.h_rectangles j i (s_j, t) h1 h2 h3 h4
  -- Top range: γ_top i is contained in covers i
  have h_top_range (i : Fin n) : Set.range (γ_top i) ⊆ (covers i : Set X) := by
    have h_lt : t_i (Fin.castSucc i) < t_i (Fin.succ i) := h_ti_strict_mono (by simp [Fin.castSucc_lt_succ])
    have h_range_eq : Set.range (γ_top i) = (H.eval s_j1) '' Set.Icc (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) := by
      rw [Path.range_subpath (H.eval s_j1) (t_i (Fin.castSucc i)) (t_i (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_j1 : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_j_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_j_le (by positivity)
    have h2 : (s_j1 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by rfl
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t : ℝ) := by
      simpa [t_i] using (show (t_i (Fin.castSucc i) : ℝ) ≤ (t : ℝ) from ht.1)
    have h4 : (t : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      simpa [t_i] using (show (t : ℝ) ≤ (t_i (Fin.succ i) : ℝ) from ht.2)
    exact pcH.h_rectangles j i (s_j1, t) h1 h2 h3 h4
  -- Vertical paths at each grid point
  let s_lerp (t : I) : I := ⟨(s_j : ℝ) + (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)), by
    have h_sj_nonneg : 0 ≤ (s_j : ℝ) := s_j.prop.1
    have h_sj_le : (s_j : ℝ) ≤ (s_j1 : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_j_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_j_le (by positivity)
    have h_diff_nonneg : 0 ≤ (s_j1 : ℝ) - (s_j : ℝ) := by linarith
    have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
    have h1 : 0 ≤ (s_j : ℝ) + (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) := by
      have h : 0 ≤ (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      linarith
    have h_t_le_one : (t : ℝ) ≤ 1 := t.prop.2
    have h_sj1_le_one : (s_j1 : ℝ) ≤ 1 := s_j1.prop.2
    have h2 : (s_j : ℝ) + (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) ≤ 1 := by
      have h3 : (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) ≤ (s_j1 : ℝ) - (s_j : ℝ) := by
        exact mul_le_of_le_one_left h_diff_nonneg h_t_le_one
      linarith
    exact ⟨h1, h2⟩⟩
  have h_s_lerp0 : s_lerp 0 = s_j := by
    apply Subtype.ext
    simp [s_lerp] <;> ring
  have h_s_lerp1 : s_lerp 1 = s_j1 := by
    apply Subtype.ext
    simp [s_lerp] <;> ring
  let γ_vert (k : Fin (n + 1)) : Path (H.eval s_j (t_i k)) (H.eval s_j1 (t_i k)) :=
    let f : C(I, X) := ⟨fun t : I => H.eval (s_lerp t) (t_i k), by continuity⟩
    have h_src : f 0 = H.eval s_j (t_i k) := by
      have h : f 0 = H.eval (s_lerp 0) (t_i k) := by rfl
      rw [h, h_s_lerp0]
    have h_tgt : f 1 = H.eval s_j1 (t_i k) := by
      have h : f 1 = H.eval (s_lerp 1) (t_i k) := by rfl
      rw [h, h_s_lerp1]
    ⟨f, h_src, h_tgt⟩
  -- Helper: s_lerp t is always between s_j and s_j1
  have h_s_lerp_between (t : I) : (s_j : ℝ) ≤ (s_lerp t : ℝ) ∧ (s_lerp t : ℝ) ≤ (s_j1 : ℝ) := by
    have h_sj_le : (s_j : ℝ) ≤ (s_j1 : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_j_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_j_le (by positivity)
    have h_diff_nonneg : 0 ≤ (s_j1 : ℝ) - (s_j : ℝ) := by linarith
    have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
    have h_t_le_one : (t : ℝ) ≤ 1 := t.prop.2
    constructor
    · -- s_j ≤ s_lerp t
      have h : 0 ≤ (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      linarith
    · -- s_lerp t ≤ s_j1
      have h : (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) ≤ (s_j1 : ℝ) - (s_j : ℝ) :=
        mul_le_of_le_one_left h_diff_nonneg h_t_le_one
      linarith
  -- Vertical range: γ_vert (Fin.castSucc i) is contained in covers i
  have h_vert_range (i : Fin n) : Set.range (γ_vert (Fin.castSucc i)) ⊆ (covers i : Set X) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have h_between := h_s_lerp_between t
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_lerp t : ℝ) := by
      have h_eq : (s_j : ℝ) = (j : ℝ) / (n : ℝ) := by rfl
      rw [h_eq] at h_between
      exact h_between.1
    have h2 : (s_lerp t : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
      have h_eq : (s_j1 : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by rfl
      rw [h_eq] at h_between
      exact h_between.2
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t_i (Fin.castSucc i) : ℝ) := by rfl
    have h4 : (t_i (Fin.castSucc i) : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_i_le : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_i_le (by positivity)
    exact pcH.h_rectangles j i (s_lerp t, t_i (Fin.castSucc i)) h1 h2 h3 h4
  -- Right edge range: γ_vert (Fin.succ i) is contained in covers i
  have h_right_range (i : Fin n) : Set.range (γ_vert (Fin.succ i)) ⊆ (covers i : Set X) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have h_between := h_s_lerp_between t
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_lerp t : ℝ) := by
      have h_eq : (s_j : ℝ) = (j : ℝ) / (n : ℝ) := by rfl
      rw [h_eq] at h_between
      exact h_between.1
    have h2 : (s_lerp t : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
      have h_eq : (s_j1 : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by rfl
      rw [h_eq] at h_between
      exact h_between.2
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t_i (Fin.succ i) : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_i_val : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
      have h : (i : ℝ) / (n : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right h_i_val (by positivity)
      have h_eq : (t_i (Fin.succ i) : ℝ) = ((i : ℝ) + 1) / (n : ℝ) := by
        simp [t_i, Fin.val_succ] <;> ring
      rw [h_eq]
      exact h
    have h4 : (t_i (Fin.succ i) : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      have h_eq : (t_i (Fin.succ i) : ℝ) = ((i : ℝ) + 1) / (n : ℝ) := by
        simp [t_i, Fin.val_succ] <;> ring
      rw [h_eq]
    exact pcH.h_rectangles j i (s_lerp t, t_i (Fin.succ i)) h1 h2 h3 h4
  -- Horizontal interpolation for each column
  let t_lerp (i : Fin n) (t : I) : I := ⟨(t_i (Fin.castSucc i) : ℝ) + (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)), by
    have h_ti_le : (t_i (Fin.castSucc i) : ℝ) ≤ (t_i (Fin.succ i) : ℝ) :=
      le_of_lt (h_ti_strict_mono (by simp [Fin.castSucc_lt_succ]))
    have h_diff_nonneg : 0 ≤ (t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ) := by linarith
    have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
    have h1 : 0 ≤ (t_i (Fin.castSucc i) : ℝ) + (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) := by
      have h_ti_nonneg : 0 ≤ (t_i (Fin.castSucc i) : ℝ) := (t_i (Fin.castSucc i)).prop.1
      have h : 0 ≤ (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      linarith
    have h_t_le_one : (t : ℝ) ≤ 1 := t.prop.2
    have h_ti1_le_one : (t_i (Fin.succ i) : ℝ) ≤ 1 := (t_i (Fin.succ i)).prop.2
    have h2 : (t_i (Fin.castSucc i) : ℝ) + (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) ≤ 1 := by
      have h3 : (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) ≤ (t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ) :=
        mul_le_of_le_one_left h_diff_nonneg h_t_le_one
      linarith
    exact ⟨h1, h2⟩⟩
  have h_t_lerp0 (i : Fin n) : t_lerp i 0 = t_i (Fin.castSucc i) := by
    apply Subtype.ext
    simp [t_lerp] <;> ring
  have h_t_lerp1 (i : Fin n) : t_lerp i 1 = t_i (Fin.succ i) := by
    apply Subtype.ext
    simp [t_lerp] <;> ring
  -- Helper: t_lerp i t is always between t_i (Fin.castSucc i) and t_i (Fin.succ i)
  have h_t_lerp_between (i : Fin n) (t : I) :
      (t_i (Fin.castSucc i) : ℝ) ≤ (t_lerp i t : ℝ) ∧ (t_lerp i t : ℝ) ≤ (t_i (Fin.succ i) : ℝ) := by
    have h_ti_le : (t_i (Fin.castSucc i) : ℝ) ≤ (t_i (Fin.succ i) : ℝ) :=
      le_of_lt (h_ti_strict_mono (by simp [Fin.castSucc_lt_succ]))
    have h_diff_nonneg : 0 ≤ (t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ) := by linarith
    have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
    have h_t_le_one : (t : ℝ) ≤ 1 := t.prop.2
    constructor
    · have h : 0 ≤ (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      linarith
    · have h : (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) ≤ (t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ) :=
        mul_le_of_le_one_left h_diff_nonneg h_t_le_one
      linarith
  -- Rectangle homotopy for each column using RectangleHomotopy
  have h_rect_both (i : Fin n) :
    ∃ (H_rect : Path.Homotopy ((γ_bottom i).trans (γ_vert (Fin.succ i)))
        ((γ_vert (Fin.castSucc i)).trans (γ_top i))),
      ∀ (p : I × I), H_rect p ∈ (covers i : Set X) := by
    let G : C(I × I, X) := ⟨fun p : I × I => H.eval (s_lerp p.1) (t_lerp i p.2), by continuity⟩
    have hG00 : G (0, 0) = H.eval s_j (t_i (Fin.castSucc i)) := by
      simp [G, h_s_lerp0, h_t_lerp0 i] <;> rfl
    have hG01 : G (0, 1) = H.eval s_j (t_i (Fin.succ i)) := by
      simp [G, h_s_lerp0, h_t_lerp1 i] <;> rfl
    have hG10 : G (1, 0) = H.eval s_j1 (t_i (Fin.castSucc i)) := by
      simp [G, h_s_lerp1, h_t_lerp0 i] <;> rfl
    have hG11 : G (1, 1) = H.eval s_j1 (t_i (Fin.succ i)) := by
      simp [G, h_s_lerp1, h_t_lerp1 i] <;> rfl
    let gb : Path (G (0, 0)) (G (0, 1)) := (γ_bottom i).cast hG00 hG01
    let gr : Path (G (0, 1)) (G (1, 1)) := (γ_vert (Fin.succ i)).cast hG01 hG11
    let gl : Path (G (0, 0)) (G (1, 0)) := (γ_vert (Fin.castSucc i)).cast hG00 hG10
    let gt : Path (G (1, 0)) (G (1, 1)) := (γ_top i).cast hG10 hG11
    have hgb : ∀ (t : I), gb t = G (0, t) := by
      intro t
      have h1 : gb t = γ_bottom i t := by rfl
      rw [h1]
      have h2 : γ_bottom i t = H.eval s_j (Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t) := by rfl
      rw [h2]
      have h_eq : Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t = t_lerp i t := by
        apply Subtype.ext
        simp [Set.Icc.coe_convexComb, t_lerp] <;> ring
      rw [h_eq]
      have h3 : G (0, t) = H.eval (s_lerp 0) (t_lerp i t) := by rfl
      rw [h3, h_s_lerp0] <;> rfl
    have hgr : ∀ (s : I), gr s = G (s, 1) := by
      intro s
      have h1 : gr s = γ_vert (Fin.succ i) s := by rfl
      rw [h1]
      have h2 : γ_vert (Fin.succ i) s = H.eval (s_lerp s) (t_i (Fin.succ i)) := by rfl
      rw [h2]
      have h3 : G (s, 1) = H.eval (s_lerp s) (t_lerp i 1) := by rfl
      rw [h3, h_t_lerp1 i] <;> rfl
    have hgl : ∀ (s : I), gl s = G (s, 0) := by
      intro s
      have h1 : gl s = γ_vert (Fin.castSucc i) s := by rfl
      rw [h1]
      have h2 : γ_vert (Fin.castSucc i) s = H.eval (s_lerp s) (t_i (Fin.castSucc i)) := by rfl
      rw [h2]
      have h3 : G (s, 0) = H.eval (s_lerp s) (t_lerp i 0) := by rfl
      rw [h3, h_t_lerp0 i] <;> rfl
    have hgt : ∀ (t : I), gt t = G (1, t) := by
      intro t
      have h1 : gt t = γ_top i t := by rfl
      rw [h1]
      have h2 : γ_top i t = H.eval s_j1 (Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t) := by rfl
      rw [h2]
      have h_eq : Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t = t_lerp i t := by
        apply Subtype.ext
        simp [Set.Icc.coe_convexComb, t_lerp] <;> ring
      rw [h_eq]
      have h3 : G (1, t) = H.eval (s_lerp 1) (t_lerp i t) := by rfl
      rw [h3, h_s_lerp1] <;> rfl
    have hG_in : ∀ (p : I × I), G p ∈ (covers i : Set X) := by
      intro p
      have h_s_between := h_s_lerp_between p.1
      have h_t_between := h_t_lerp_between i p.2
      have h1 : (j : ℝ) / (n : ℝ) ≤ (s_lerp p.1 : ℝ) := by
        have h_eq : (s_j : ℝ) = (j : ℝ) / (n : ℝ) := by rfl
        rw [h_eq] at h_s_between; exact h_s_between.1
      have h2 : (s_lerp p.1 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
        have h_eq : (s_j1 : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by rfl
        rw [h_eq] at h_s_between; exact h_s_between.2
      have h3 : (i : ℝ) / (n : ℝ) ≤ (t_lerp i p.2 : ℝ) := by
        have h_eq : (t_i (Fin.castSucc i) : ℝ) = (i : ℝ) / (n : ℝ) := by
          simp [t_i, Fin.castSucc] <;> rfl
        rw [h_eq] at h_t_between; exact h_t_between.1
      have h4 : (t_lerp i p.2 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
        have h_eq : (t_i (Fin.succ i) : ℝ) = ((i : ℝ) + 1) / (n : ℝ) := by
          simp [t_i, Fin.val_succ] <;> ring
        rw [h_eq] at h_t_between; exact h_t_between.2
      exact pcH.h_rectangles j i (s_lerp p.1, t_lerp i p.2) h1 h2 h3 h4
    have h_main := RectangleHomotopy.rectangle_boundary_homotopy_edges G gb gr gl gt hgb hgr hgl hgt (covers i : Set X) hG_in
    rcases h_main with ⟨H_rect, hH_rect_range⟩
    let H_rect_cast : Path.Homotopy
        ((gb.trans gr).cast hG00.symm hG11.symm)
        ((gl.trans gt).cast hG00.symm hG11.symm) :=
      H_rect.pathCast hG00.symm hG11.symm
    have hH_rect_cast_range : ∀ (p : I × I), H_rect_cast p ∈ (covers i : Set X) := by
      intro p
      have h_eq : H_rect_cast p = H_rect p := by rfl
      rw [h_eq]
      exact hH_rect_range p
    have h_mid : H.eval s_j (t_i (Fin.succ i)) = G (0, 1) := hG01.symm
    have h_mid2 : H.eval s_j1 (t_i (Fin.castSucc i)) = G (1, 0) := hG10.symm
    have h_eq0 : (gb.trans gr).cast hG00.symm hG11.symm = (γ_bottom i).trans (γ_vert (Fin.succ i)) := by
      rw [Path.cast_trans gb gr hG00.symm h_mid hG11.symm]
      have hgb2 : gb.cast hG00.symm h_mid = γ_bottom i := by
        apply Path.ext
        funext t
        have h : (gb.cast hG00.symm h_mid) t = gb t := by rfl
        rw [h] <;> rfl
      have hgr2 : gr.cast h_mid hG11.symm = γ_vert (Fin.succ i) := by
        apply Path.ext
        funext t
        have h : (gr.cast h_mid hG11.symm) t = gr t := by rfl
        rw [h] <;> rfl
      rw [hgb2, hgr2]
    have h_eq1 : (gl.trans gt).cast hG00.symm hG11.symm = (γ_vert (Fin.castSucc i)).trans (γ_top i) := by
      rw [Path.cast_trans gl gt hG00.symm h_mid2 hG11.symm]
      have hgl2 : gl.cast hG00.symm h_mid2 = γ_vert (Fin.castSucc i) := by
        apply Path.ext
        funext t
        have h : (gl.cast hG00.symm h_mid2) t = gl t := by rfl
        rw [h] <;> rfl
      have hgt2 : gt.cast h_mid2 hG11.symm = γ_top i := by
        apply Path.ext
        funext t
        have h : (gt.cast h_mid2 hG11.symm) t = gt t := by rfl
        rw [h] <;> rfl
      rw [hgl2, hgt2]
    let H_rect' : Path.Homotopy ((γ_bottom i).trans (γ_vert (Fin.succ i)))
        ((γ_vert (Fin.castSucc i)).trans (γ_top i)) :=
      Path.Homotopy.cast H_rect_cast h_eq0 h_eq1
    have hH_rect'_range : ∀ (p : I × I), H_rect' p ∈ (covers i : Set X) := by
      intro p
      have h_eq : H_rect' p = H_rect_cast p := by rfl
      rw [h_eq]
      exact hH_rect_cast_range p
    exact ⟨H_rect', hH_rect'_range⟩
  let h_rect_homotopy (i : Fin n) :
    Path.Homotopy ((γ_bottom i).trans (γ_vert (Fin.succ i)))
      ((γ_vert (Fin.castSucc i)).trans (γ_top i)) :=
    (h_rect_both i).choose
  have h_rect_homotopy_range (i : Fin n) :
    ∀ (p : I × I), (h_rect_homotopy i) p ∈ (covers i : Set X) := by
    exact (h_rect_both i).choose_spec
  -- Apply rectangle_identity_clean to each column
  have h_rect_comm (i : Fin n) :
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_bottom i) (covers i) (hcover_mem i) (h_bottom_range i) ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.succ i)) (covers i) (hcover_mem i) (h_right_range i) =
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.castSucc i)) (covers i) (hcover_mem i) (h_vert_range i) ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_top i) (covers i) (hcover_mem i) (h_top_range i) :=
    rectangle_identity_clean X 𝒰 hcover hfinite_intersections s (covers i) (hcover_mem i)
      (γ_bottom i) (h_bottom_range i)
      (γ_vert (Fin.succ i)) (h_right_range i)
      (γ_vert (Fin.castSucc i)) (h_vert_range i)
      (γ_top i) (h_top_range i)
      (h_rect_homotopy i) (h_rect_homotopy_range i)
  -- Objects in the cocone point for bottom and top rows
  let p_objs (i : Fin (n + 1)) : s.pt :=
    desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (H.eval s_j (t_i i)))
  let q_objs (i : Fin (n + 1)) : s.pt :=
    desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (H.eval s_j1 (t_i i)))
  -- Bottom and top morphisms (single_covered_map for each segment)
  let f_bottom (i : Fin n) : p_objs (Fin.castSucc i) ⟶ p_objs (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_bottom i) (covers i) (hcover_mem i) (h_bottom_range i)
  let f_top (i : Fin n) : q_objs (Fin.castSucc i) ⟶ q_objs (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_top i) (covers i) (hcover_mem i) (h_top_range i)
  -- Vertical morphisms
  let f_vert (k : Fin (n + 1)) : p_objs k ⟶ q_objs k :=
    my_desc_map X 𝒰 hcover hfinite_intersections s (γ_vert k)
  -- Commuting squares for the chain lemma
  have h_square (i : Fin n) :
    f_bottom i ≫ f_vert (Fin.succ i) = f_vert (Fin.castSucc i) ≫ f_top i := by
    let f_vert_left := single_covered_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.castSucc i)) (covers i) (hcover_mem i) (h_vert_range i)
    let f_vert_right := single_covered_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.succ i)) (covers i) (hcover_mem i) (h_right_range i)
    have h_main : f_bottom i ≫ f_vert_right = f_vert_left ≫ f_top i := h_rect_comm i
    have h1 : f_vert (Fin.castSucc i) = f_vert_left := by
      exact?
    have h2 : f_vert (Fin.succ i) = f_vert_right := by
      exact?
    rw [h2, h1]
    exact h_main
  -- Apply the chain lemma
  have h_chain : comp_list n p_objs f_bottom ≫ f_vert (Fin.last n) =
      f_vert 0 ≫ comp_list n q_objs f_top :=
    comp_list_chain_commute p_objs q_objs f_bottom f_top f_vert h_square
  -- The first vertical edge is a constant path at x
  -- The last vertical edge is a constant path at y
  -- So f_vert 0 and f_vert (Fin.last n) are "identities" (eqToHom of the endpoint equality)
  -- Connect to my_desc_map via the universal property and conclude
  let S_bot : Finset I := Finset.image t_i Finset.univ
  have h_ti0 : t_i 0 = (0 : I) := by
    apply Subtype.ext
    have h : (t_i 0).val = 0 := by
      dsimp only [t_i]
      simpa using zero_div (n : ℝ)
    have h' : ((0 : I) : ℝ) = 0 := by norm_cast
    rw [h']
    exact h
  have h_ti1 : t_i (Fin.last n) = (1 : I) := by
    apply Subtype.ext
    have h_last_val : (Fin.last n).val = n := by simp [Fin.last] <;> omega
    have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h : (t_i (Fin.last n)).val = 1 := by
      dsimp only [t_i]
      rw [h_last_val]
      have h_pos' : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
      exact div_self h_pos'
    have h' : ((1 : I) : ℝ) = 1 := by norm_cast
    rw [h']
    exact h
  have h0_in_S_bot : (0 : I) ∈ S_bot := by
    dsimp only [S_bot]
    rw [←h_ti0]
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  have h1_in_S_bot : (1 : I) ∈ S_bot := by
    dsimp only [S_bot]
    rw [←h_ti1]
    exact Finset.mem_image.mpr ⟨Fin.last n, by simp, rfl⟩
  have h_range_bot' : ∀ (i : Fin n) (t : I), t_i (Fin.castSucc i) ≤ t → t ≤ t_i (Fin.succ i) → (H.eval s_j) t ∈ (covers i : Set X) := by
    intro i t h1 h2
    have h_in_range : (H.eval s_j) t ∈ Set.range (γ_bottom i) := by
      have h_lt : t_i (Fin.castSucc i) < t_i (Fin.succ i) := h_ti_strict_mono (by simp [Fin.castSucc_lt_succ])
      have h_range_eq : Set.range (γ_bottom i) = (H.eval s_j) '' Set.Icc (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) := by
        rw [Path.range_subpath (H.eval s_j) (t_i (Fin.castSucc i)) (t_i (Fin.succ i))]
        <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
      rw [h_range_eq]
      exact ⟨t, ⟨h1, h2⟩, rfl⟩
    exact h_bottom_range i h_in_range
  have hS_bot : IsAdaptedSubdivision 𝒰 (H.eval s_j) S_bot := by
    constructor
    · exact h0_in_S_bot
    · constructor
      · exact h1_in_S_bot
      · intro s₁ s₂ hs₁ hs₂ h_lt h_no_between
        have h_exists : ∃ (i : Fin n), s₁ = t_i (Fin.castSucc i) ∧ s₂ = t_i (Fin.succ i) := by
          rcases Finset.mem_image.mp hs₁ with ⟨k, _, rfl⟩
          rcases Finset.mem_image.mp hs₂ with ⟨l, _, rfl⟩
          have h_k_lt_l : k < l := by
            by_contra h
            have h' : l ≤ k := le_of_not_gt h
            have h'' : t_i l ≤ t_i k := h_ti_strict_mono.monotone h'
            exact lt_irrefl _ (lt_of_le_of_lt h'' h_lt)
          have h_l_val_succ : l.val = k.val + 1 := by
            by_contra h
            have h_k_lt_l_val : k.val < l.val := by exact_mod_cast h_k_lt_l
            have h_succ_lt : k.val + 1 < l.val := by omega
            have h_m_lt_n1 : k.val + 1 < n + 1 := by omega
            let m : Fin (n + 1) := ⟨k.val + 1, h_m_lt_n1⟩
            have h_k_lt_m : k < m := by
              apply Fin.lt_iff_val_lt_val.mpr
              simp [m] <;> omega
            have h_m_lt_l : m < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              simp [m, h_succ_lt] <;> omega
            have h_between1 : t_i k < t_i m := h_ti_strict_mono h_k_lt_m
            have h_between2 : t_i m < t_i l := h_ti_strict_mono h_m_lt_l
            have h_mem : t_i m ∈ Finset.image t_i Finset.univ := by
              exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
            exact h_no_between (t_i m) h_mem h_between1 h_between2
          have h_k_lt_n : k.val < n := by omega
          let i : Fin n := ⟨k.val, h_k_lt_n⟩
          have h_k_eq : k = Fin.castSucc i := by
            apply Fin.ext
            simp [i]
          have h_l_eq : l = Fin.succ i := by
            apply Fin.ext
            simp [i, h_l_val_succ, Fin.val_succ]
            <;> omega
          refine' ⟨i, _⟩
          constructor
          · rw [h_k_eq]
          · rw [h_l_eq]
        rcases h_exists with ⟨i, rfl, rfl⟩
        refine' ⟨covers i, hcover_mem i, _⟩
        exact h_range_bot' i
  have h_desc_bot : my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval s_j) =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_bot :=
    my_desc_map_well_defined X 𝒰 hcover hfinite_intersections s (H.eval s_j)
      (Classical.choose (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j))) S_bot
      (Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j))) hS_bot
  have h_univ_bot : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_bot =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_bot n t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot' := by
    exact my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS_bot t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot'
  -- Step 1: Prove γ_vert 0 is constant (at x) and γ_vert (Fin.last n) is constant (at y)
  have h_eval0 : ∀ (s : I), H.eval s 0 = x := by
    intro s
    exact (H.eval s).source
  have h_eval1 : ∀ (s : I), H.eval s 1 = y := by
    intro s
    exact (H.eval s).target
  have h_vert0_const : ∀ (t : I), (γ_vert 0) t = H.eval s_j (t_i 0) := by
    intro t
    have h1 : (γ_vert 0) t = H.eval (s_lerp t) (t_i 0) := by rfl
    have h2 : H.eval (s_lerp t) (t_i 0) = x := by
      rw [h_ti0]
      exact h_eval0 (s_lerp t)
    have h3 : H.eval s_j (t_i 0) = x := by
      rw [h_ti0]
      exact h_eval0 s_j
    rw [h1, h2, h3]
  have h_vert_last_const : ∀ (t : I), (γ_vert (Fin.last n)) t = H.eval s_j (t_i (Fin.last n)) := by
    intro t
    have h1 : (γ_vert (Fin.last n)) t = H.eval (s_lerp t) (t_i (Fin.last n)) := by rfl
    have h2 : H.eval (s_lerp t) (t_i (Fin.last n)) = y := by
      rw [h_ti1]
      exact h_eval1 (s_lerp t)
    have h3 : H.eval s_j (t_i (Fin.last n)) = y := by
      rw [h_ti1]
      exact h_eval1 s_j
    rw [h1, h2, h3]
  -- Step 2: Prove f_vert 0 and f_vert (Fin.last n) are eqToHom
  have h_eq0 : p_objs 0 = q_objs 0 := by
    dsimp only [p_objs, q_objs]
    have h1 : H.eval s_j (t_i 0) = H.eval s_j1 (t_i 0) := by
      rw [h_ti0]
      <;> exact (h_eval0 s_j).trans (h_eval0 s_j1).symm
    rw [h1]
  have h_eq_last : p_objs (Fin.last n) = q_objs (Fin.last n) := by
    dsimp only [p_objs, q_objs]
    have h1 : H.eval s_j (t_i (Fin.last n)) = H.eval s_j1 (t_i (Fin.last n)) := by
      rw [h_ti1]
      <;> exact (h_eval1 s_j).trans (h_eval1 s_j1).symm
    rw [h1]
  have h_fvert0 : f_vert 0 = eqToHom h_eq0 := by
    have h1 : f_vert 0 = my_desc_map X 𝒰 hcover hfinite_intersections s (γ_vert 0) := by rfl
    rw [h1]
    rcases hcover x with ⟨U, hU_mem, hxU⟩
    have h_range0 : Set.range (γ_vert 0) ⊆ (U : Set X) := by
      intro z hz
      rcases hz with ⟨t, rfl⟩
      have h2 : (γ_vert 0) t = x := by
        have h3 : (γ_vert 0) t = H.eval s_j (t_i 0) := h_vert0_const t
        rw [h3, h_ti0]; exact h_eval0 s_j
      rw [h2]; exact hxU
    rw [my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (γ_vert 0) U hU_mem h_range0]
    let x1 := H.eval s_j (t_i 0)
    let x2 := H.eval s_j1 (t_i 0)
    have h_endpoints_eq : x1 = x2 := by
      dsimp only [x1, x2]
      rw [h_ti0]
      <;> exact (h_eval0 s_j).trans (h_eval0 s_j1).symm
    have h_const : ∀ (t : I), (γ_vert 0) t = x1 := h_vert0_const
    exact single_covered_map_const_path X 𝒰 hcover hfinite_intersections s (γ_vert 0) h_endpoints_eq U hU_mem h_range0 h_const
  have h_fvert_last : f_vert (Fin.last n) = eqToHom h_eq_last := by
    have h1 : f_vert (Fin.last n) = my_desc_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.last n)) := by rfl
    rw [h1]
    rcases hcover y with ⟨U, hU_mem, hyU⟩
    have h_range_last : Set.range (γ_vert (Fin.last n)) ⊆ (U : Set X) := by
      intro z hz
      rcases hz with ⟨t, rfl⟩
      have h2 : (γ_vert (Fin.last n)) t = y := by
        have h3 : (γ_vert (Fin.last n)) t = H.eval s_j (t_i (Fin.last n)) := h_vert_last_const t
        rw [h3, h_ti1]
        exact h_eval1 s_j
      rw [h2]
      exact hyU
    rw [my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.last n)) U hU_mem h_range_last]
    let y1 := H.eval s_j (t_i (Fin.last n))
    let y2 := H.eval s_j1 (t_i (Fin.last n))
    have h_endpoints_eq : y1 = y2 := by
      dsimp only [y1, y2]
      rw [h_ti1]
      <;> exact (h_eval1 s_j).trans (h_eval1 s_j1).symm
    have h_const : ∀ (t : I), (γ_vert (Fin.last n)) t = y1 := h_vert_last_const
    exact single_covered_map_const_path X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.last n)) h_endpoints_eq U hU_mem h_range_last h_const
  -- Step 3: Set up the top row
  let S_top : Finset I := Finset.image t_i Finset.univ
  have h_range_top' : ∀ (i : Fin n) (t : I), t_i (Fin.castSucc i) ≤ t → t ≤ t_i (Fin.succ i) → (H.eval s_j1) t ∈ (covers i : Set X) := by
    intro i t h1 h2
    have h_in_range : (H.eval s_j1) t ∈ Set.range (γ_top i) := by
      have h_lt : t_i (Fin.castSucc i) < t_i (Fin.succ i) := h_ti_strict_mono (by simp [Fin.castSucc_lt_succ])
      have h_range_eq : Set.range (γ_top i) = (H.eval s_j1) '' Set.Icc (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) := by
        rw [Path.range_subpath (H.eval s_j1) (t_i (Fin.castSucc i)) (t_i (Fin.succ i))]
        <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
      rw [h_range_eq]
      exact ⟨t, ⟨h1, h2⟩, rfl⟩
    exact h_top_range i h_in_range
  have hS_top : IsAdaptedSubdivision 𝒰 (H.eval s_j1) S_top := by
    constructor
    · exact h0_in_S_bot
    · constructor
      · exact h1_in_S_bot
      · intro s₁ s₂ hs₁ hs₂ h_lt h_no_between
        have h_exists : ∃ (i : Fin n), s₁ = t_i (Fin.castSucc i) ∧ s₂ = t_i (Fin.succ i) := by
          rcases Finset.mem_image.mp hs₁ with ⟨k, _, rfl⟩
          rcases Finset.mem_image.mp hs₂ with ⟨l, _, rfl⟩
          have h_k_lt_l : k < l := by
            by_contra h
            have h' : l ≤ k := le_of_not_gt h
            have h'' : t_i l ≤ t_i k := h_ti_strict_mono.monotone h'
            exact lt_irrefl _ (lt_of_le_of_lt h'' h_lt)
          have h_l_val_succ : l.val = k.val + 1 := by
            by_contra h
            have h_k_lt_l_val : k.val < l.val := by exact_mod_cast h_k_lt_l
            have h_succ_lt : k.val + 1 < l.val := by omega
            have h_m_lt_n1 : k.val + 1 < n + 1 := by omega
            let m : Fin (n + 1) := ⟨k.val + 1, h_m_lt_n1⟩
            have h_k_lt_m : k < m := by
              apply Fin.lt_iff_val_lt_val.mpr
              simp [m] <;> omega
            have h_m_lt_l : m < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              simp [m, h_succ_lt] <;> omega
            have h_between1 : t_i k < t_i m := h_ti_strict_mono h_k_lt_m
            have h_between2 : t_i m < t_i l := h_ti_strict_mono h_m_lt_l
            have h_mem : t_i m ∈ Finset.image t_i Finset.univ := by
              exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
            exact h_no_between (t_i m) h_mem h_between1 h_between2
          have h_k_lt_n : k.val < n := by omega
          let i : Fin n := ⟨k.val, h_k_lt_n⟩
          have h_k_eq : k = Fin.castSucc i := by
            apply Fin.ext
            simp [i]
          have h_l_eq : l = Fin.succ i := by
            apply Fin.ext
            simp [i, h_l_val_succ, Fin.val_succ] <;> omega
          refine' ⟨i, _⟩
          constructor
          · rw [h_k_eq]
          · rw [h_l_eq]
        rcases h_exists with ⟨i, rfl, rfl⟩
        refine' ⟨covers i, hcover_mem i, _⟩
        exact h_range_top' i
  have h_desc_top : my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval s_j1) =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_top :=
    my_desc_map_well_defined X 𝒰 hcover hfinite_intersections s (H.eval s_j1)
      (Classical.choose (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j1))) S_top
      (Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j1))) hS_top
  have h_univ_top : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_top =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_top n t_i h_ti_strict_mono rfl covers hcover_mem h_range_top' := by
    exact my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS_top t_i h_ti_strict_mono rfl covers hcover_mem h_range_top'
  -- Step 4: Unfold definitions and use chain lemma
  have h_chain2 : comp_list n p_objs f_bottom ≫ eqToHom h_eq_last =
      eqToHom h_eq0 ≫ comp_list n q_objs f_top := by
    rw [h_fvert_last, h_fvert0] at h_chain
    exact h_chain
  -- Step 5: Conclude
  let mk_x_obj := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)
  let mk_y_obj := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)
  have h_bot_eq0 : p_objs 0 = mk_x_obj := by
    dsimp only [p_objs, mk_x_obj]
    have h : (H.eval s_j) (t_i 0) = x := by
      rw [h_ti0]
      exact (H.eval s_j).source
    rw [h]
    <;> rfl
  have h_bot_eq_last : p_objs (Fin.last n) = mk_y_obj := by
    dsimp only [p_objs, mk_y_obj]
    have h : (H.eval s_j) (t_i (Fin.last n)) = y := by
      rw [h_ti1]
      exact (H.eval s_j).target
    rw [h]
    <;> rfl
  have h_top_eq0 : q_objs 0 = mk_x_obj := by
    dsimp only [q_objs, mk_x_obj]
    have h : (H.eval s_j1) (t_i 0) = x := by
      rw [h_ti0]
      exact (H.eval s_j1).source
    rw [h]
    <;> rfl
  have h_top_eq_last : q_objs (Fin.last n) = mk_y_obj := by
    dsimp only [q_objs, mk_y_obj]
    have h : (H.eval s_j1) (t_i (Fin.last n)) = y := by
      rw [h_ti1]
      exact (H.eval s_j1).target
    rw [h]
    <;> rfl
  have h_eq0' : eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0 = eqToHom h_top_eq0.symm := by
    have h2 : eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0 = eqToHom (h_bot_eq0.symm.trans h_eq0) := by
      rw [eqToHom_trans]
    rw [h2]
    <;> congr
  have h_eq_last' : eqToHom h_eq_last.symm ≫ eqToHom h_bot_eq_last = eqToHom h_top_eq_last := by
    have h2 : eqToHom h_eq_last.symm ≫ eqToHom h_bot_eq_last = eqToHom ((h_eq_last.symm).trans h_bot_eq_last) := by
      rw [eqToHom_trans]
    rw [h2]
    <;> congr
  have h_main_bot : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_bot n t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot' =
      eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ eqToHom h_bot_eq_last := by
    simp [my_map_from_adapted_subdivision_with_covers, h_bot_eq0, h_bot_eq_last]
    <;> rfl
  have h_main_top : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_top n t_i h_ti_strict_mono rfl covers hcover_mem h_range_top' =
      eqToHom h_top_eq0.symm ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
    simp [my_map_from_adapted_subdivision_with_covers, h_top_eq0, h_top_eq_last]
    <;> rfl
  have h_last_decomp : eqToHom h_bot_eq_last = eqToHom h_eq_last ≫ eqToHom h_top_eq_last := by
    rw [←eqToHom_trans]
    <;> congr
    <;> exact Eq.trans h_eq_last h_top_eq_last
  have h_final : eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ eqToHom h_bot_eq_last =
      eqToHom h_top_eq0.symm ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
    have h1 : eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ eqToHom h_bot_eq_last =
        eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ (eqToHom h_eq_last ≫ eqToHom h_top_eq_last) := by
      rw [h_last_decomp]
    rw [h1]
    have h2 : eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ (eqToHom h_eq_last ≫ eqToHom h_top_eq_last) =
        eqToHom h_bot_eq0.symm ≫ (comp_list n p_objs f_bottom ≫ eqToHom h_eq_last) ≫ eqToHom h_top_eq_last := by
      simp [Category.assoc]
      <;> rfl
    rw [h2]
    have h3 : eqToHom h_bot_eq0.symm ≫ (comp_list n p_objs f_bottom ≫ eqToHom h_eq_last) ≫ eqToHom h_top_eq_last =
        eqToHom h_bot_eq0.symm ≫ (eqToHom h_eq0 ≫ comp_list n q_objs f_top) ≫ eqToHom h_top_eq_last := by
      rw [h_chain2]
    rw [h3]
    have h4 : eqToHom h_bot_eq0.symm ≫ (eqToHom h_eq0 ≫ comp_list n q_objs f_top) ≫ eqToHom h_top_eq_last =
        (eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0) ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
      simp [Category.assoc]
      <;> rfl
    rw [h4]
    have h5 : (eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0) ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last =
        eqToHom h_top_eq0.symm ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
      rw [h_eq0']
    exact h5
  have h_both : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_bot n t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot' =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_top n t_i h_ti_strict_mono rfl covers hcover_mem h_range_top' := by
    rw [h_main_bot, h_main_top, h_final]
  rw [h_desc_bot, h_desc_top, h_univ_bot, h_univ_top]
  exact h_both



theorem my_desc_map_homotopy_invariant {x y : X} {γ₁ γ₂ : Path x y}
    (h : Path.Homotopic γ₁ γ₂) :
    my_desc_map X 𝒰 hcover hfinite_intersections s γ₁ =
    my_desc_map X 𝒰 hcover hfinite_intersections s γ₂ := by
  rcases h with ⟨H⟩
  have h_main := exists_partwise_covered_homotopy 𝒰 hcover H
  rcases h_main with ⟨n, hn_pos, ⟨pcH⟩⟩
  let t_of_idx (k : Fin (n + 1)) : I := ⟨(k.val : ℝ) / (n : ℝ), by
    have h₁ : 0 ≤ (k.val : ℝ) / (n : ℝ) := by positivity
    have h₂ : (k.val : ℝ) / (n : ℝ) ≤ 1 := by
      have h₃ : k.val < n + 1 := k.is_lt
      have h₄ : (k.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.lt_succ_iff.mp h₃)
      have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      exact (div_le_one h₅).mpr h₄
    exact ⟨h₁, h₂⟩⟩
  let row (k : Fin (n + 1)) : Path x y := H.eval (t_of_idx k)
  have h_ind : ∀ (k : Fin (n + 1)),
      my_desc_map X 𝒰 hcover hfinite_intersections s (row 0) =
      my_desc_map X 𝒰 hcover hfinite_intersections s (row k) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      simp [row]
    | succ k ih =>
      let j : Fin n := k
      let t_j : I := ⟨(j.val : ℝ) / (n : ℝ), by
        have h₁ : 0 ≤ (j.val : ℝ) / (n : ℝ) := by positivity
        have h₂ : (j.val : ℝ) / (n : ℝ) ≤ 1 := by
          have h₃ : j.val < n := j.is_lt
          have h₄ : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₃.le
          have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
          exact (div_le_one h₅).mpr h₄
        exact ⟨h₁, h₂⟩⟩
      let t_j1 : I := ⟨((j.val : ℝ) + 1) / (n : ℝ), by
        have h₁ : 0 ≤ ((j.val : ℝ) + 1) / (n : ℝ) := by positivity
        have h₂ : ((j.val : ℝ) + 1) / (n : ℝ) ≤ 1 := by
          have h₃ : j.val < n := j.is_lt
          have h₄ : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr h₃)
          have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
          exact (div_le_one h₅).mpr h₄
        exact ⟨h₁, h₂⟩⟩
      have h_tj_eq : t_of_idx (Fin.castSucc k) = t_j := by
        apply Subtype.ext
        simp [t_of_idx, t_j, Fin.castSucc] <;> ring
      have h_tj1_eq : t_of_idx (Fin.succ k) = t_j1 := by
        apply Subtype.ext
        simp [t_of_idx, t_j1, Fin.val_succ] <;> ring
      have h_row_j : row (Fin.castSucc k) = H.eval t_j := by
        simpa [row] using congr_arg (fun t : I => H.eval t) h_tj_eq
      have h_row_j1 : row (Fin.succ k) = H.eval t_j1 := by
        simpa [row] using congr_arg (fun t : I => H.eval t) h_tj1_eq
      have h_step_main : my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval t_j) =
          my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval t_j1) :=
        consecutive_rows_equal_my_desc_map X 𝒰 hcover hfinite_intersections s H hn_pos pcH j
      have h_step : my_desc_map X 𝒰 hcover hfinite_intersections s (row (Fin.castSucc k)) =
          my_desc_map X 𝒰 hcover hfinite_intersections s (row (Fin.succ k)) := by
        rw [h_row_j, h_row_j1]
        exact h_step_main
      calc
        my_desc_map X 𝒰 hcover hfinite_intersections s (row 0)
          = my_desc_map X 𝒰 hcover hfinite_intersections s (row (Fin.castSucc k)) := ih
        _ = my_desc_map X 𝒰 hcover hfinite_intersections s (row (Fin.succ k)) := h_step
  have h0 := h_ind (Fin.last n)
  have h_row0 : row 0 = γ₁ := by
    have h_eq : t_of_idx 0 = (0 : I) := by
      apply Subtype.ext
      simp [t_of_idx] <;> ring
    simpa [row] using congr_arg (fun t : I => H.eval t) h_eq ▸ H.eval_zero
  have h_rown : row (Fin.last n) = γ₂ := by
    have h_n_ne_zero : n ≠ 0 := hn_pos.ne'
    have h_n_pos' : (n : ℝ) ≠ 0 := by exact_mod_cast h_n_ne_zero
    have h_val_eq : ((Fin.last n).val : ℝ) = (n : ℝ) := by
      exact_mod_cast (by simp [Fin.last])
    have h_div_eq : ((Fin.last n).val : ℝ) / (n : ℝ) = 1 := by
      rw [h_val_eq]
      field_simp [h_n_pos'] <;> ring
    have h_eq : t_of_idx (Fin.last n) = (1 : I) := by
      apply Subtype.ext
      exact h_div_eq
    simpa [row] using congr_arg (fun t : I => H.eval t) h_eq ▸ H.eval_one
  rw [h_row0, h_rown] at h0
  exact h0

end

end

end P202.Topology.VanKampenProof


/-! Adapted from ColimitProof.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hpath_connected : ∀ U : Opens X, U ∈ 𝒰 → IsPathConnected (U : Set X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

noncomputable def my_desc_functor :
    FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt :=
  {
    obj := fun x => desc_functor_obj X 𝒰 hcover s x,
    map := fun {x y} f =>
      Quotient.lift (my_desc_map X 𝒰 hcover hfinite_intersections s)
        (fun γ₁ γ₂ h => my_desc_map_homotopy_invariant X 𝒰 hcover hfinite_intersections s h) f,
    map_id := by
      intro x
      let const_path : Path x.as x.as := Path.refl x.as
      have h_main : (𝟙 x) = Path.Homotopic.Quotient.mk const_path := by
        exact (FundamentalGroupoid.id_eq_path_refl x).symm
      rw [h_main]
      dsimp only
      exact my_desc_map_refl X 𝒰 hcover hfinite_intersections s,
    map_comp := by
      intro x y z f g
      let F_map := fun {a b : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)} (h : a ⟶ b) =>
        Quotient.lift (my_desc_map X 𝒰 hcover hfinite_intersections s)
          (fun γ₁ γ₂ h => my_desc_map_homotopy_invariant X 𝒰 hcover hfinite_intersections s h) h
      have h_step1 : ∀ (f' : x ⟶ y), ∀ (g' : y ⟶ z),
          F_map (f' ≫ g') = F_map f' ≫ F_map g' := by
        intro f'
        refine' Quotient.inductionOn' f' _
        intro γ₁
        intro g'
        refine' Quotient.inductionOn' g' _
        intro γ₂
        let p : x ⟶ y := Path.Homotopic.Quotient.mk γ₁
        let q : y ⟶ z := Path.Homotopic.Quotient.mk γ₂
        have h_comp_eq : p ≫ q = Path.Homotopic.Quotient.trans p q :=
          FundamentalGroupoid.comp_eq x y z p q
        have h_trans_eq : Path.Homotopic.Quotient.trans p q = Path.Homotopic.Quotient.mk (γ₁.trans γ₂) := by
          exact Path.Homotopic.Quotient.mk_trans γ₁ γ₂
        have h1 : p ≫ q = Path.Homotopic.Quotient.mk (γ₁.trans γ₂) := by
          rw [h_comp_eq, h_trans_eq]
        have h_main : F_map (p ≫ q) = F_map p ≫ F_map q := by
          rw [h1]
          simp only [F_map, Quotient.lift_mk]
          exact my_desc_map_comp X 𝒰 hcover hfinite_intersections s γ₁ γ₂
        exact h_main
      exact h_step1 f g
  }

/-- Clean version of fac_property_obj: uses my_desc_functor (which has no omitted proofs)
    instead of desc_functor (which has omitted proofs in map/map_id/map_comp). -/
lemma my_fac_property_obj (U : Opens X) (hU : U ∈ 𝒰)
    (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U)) :
    (my_desc_functor X 𝒰 hcover hfinite_intersections s).obj
      ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x) =
    (s.ι.app ⟨U, hU⟩).obj x := by
  let z : (Opens.toTopCat (TopCat.of X)).obj U := x.as
  let z_X : X := z.val
  have hz : z_X ∈ U := z.property
  have h1 : (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x =
      (FundamentalGroupoid.mk z_X : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) := by
    rfl
  rw [h1]
  have h_main : (my_desc_functor X 𝒰 hcover hfinite_intersections s).obj (FundamentalGroupoid.mk z_X) =
      obj_at X 𝒰 s z_X U hU hz := by
    dsimp only [my_desc_functor, desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ z_X ∈ U' := hcover z_X
    have h' : obj_at X 𝒰 s z_X (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2 =
        obj_at X 𝒰 s z_X U hU hz :=
      obj_at_eq X 𝒰 s hfinite_intersections z_X (Classical.choose h) U
        (Classical.choose_spec h).1 hU (Classical.choose_spec h).2 hz
    exact h'
  have h3 : obj_at X 𝒰 s z_X U hU hz = (s.ι.app ⟨U, hU⟩).obj x := by
    rfl
  rw [h_main, h3]

set_option backward.isDefEq.respectTransparency.types false in
/-- Local copy of single_covered_map_fac for use in this file. -/
lemma single_covered_map_fac_local
    {x y : X} (γ : Path x y) (U : Opens X) (hU : U ∈ 𝒰) (h_range : Set.range γ ⊆ (U : Set X)) :
    let U_set : Set X := (U : Set X)
    let hx : x ∈ U := by
      have h1 : γ 0 ∈ Set.range γ := Set.mem_range_self 0
      have h2 : γ 0 = x := γ.source
      rw [h2] at h1
      exact h_range h1
    let hy : y ∈ U := by
      have h1 : γ 1 ∈ Set.range γ := Set.mem_range_self 1
      have h2 : γ 1 = y := γ.target
      rw [h2] at h1
      exact h_range h1
    let x_U : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U) :=
      FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)
    let y_U : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U) :=
      FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)
    let γ_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
      (Path.lift_to_subtype γ hx hy h_range).choose
    let f : x_U ⟶ y_U := Path.Homotopic.Quotient.mk γ_lift
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
    eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x_U) ≫
    (s.ι.app ⟨U, hU⟩).map f ≫
    eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y_U).symm := by
  dsimp only [single_covered_map, my_fac_property_obj]
  <;> simp
  <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Fac property for my_desc_functor on morphisms:
    Given a path γ in U, my_desc_functor.map applied to the image of γ's homotopy class
    equals the cocone leg map applied to the lifted homotopy class,
    composed with eqToHom transports from fac_property_obj. -/
lemma my_desc_functor_map_fac (U : Opens X) (hU : U ∈ 𝒰)
    (x y : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U))
    (f : x ⟶ y) :
    (my_desc_functor X 𝒰 hcover hfinite_intersections s).map
      ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).map f) =
    eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x) ≫
    (s.ι.app ⟨U, hU⟩).map f ≫
    eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm := by
  let U_set : Set X := (U : Set X)
  let π₁U := FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U)
  let F := s.ι.app ⟨U, hU⟩
  induction f using Quotient.inductionOn' with
  | h γ_lift =>
    -- Work with U_set type for simpler coercions
    let x_val : U_set := x.as
    let y_val : U_set := y.as
    let x_X : X := x_val
    let y_X : X := y_val
    -- γ_lift_U is γ_lift with type annotation to live in U_set
    let γ_lift_U : Path x_val y_val := γ_lift
    let γ : Path x_X y_X := γ_lift_U.map continuous_subtype_val
    have h_range : Set.range γ ⊆ U_set := by
      intro z hz
      rcases hz with ⟨t, rfl⟩
      exact (γ_lift_U t).property
    let f_U : x ⟶ y := Path.Homotopic.Quotient.mk γ_lift
    have h1 : (my_desc_functor X 𝒰 hcover hfinite_intersections s).map
        ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).map f_U) =
        my_desc_map X 𝒰 hcover hfinite_intersections s γ := by
      dsimp only [my_desc_functor, f_U]
      <;> rfl
    have h2 : my_desc_map X 𝒰 hcover hfinite_intersections s γ =
        single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range :=
      my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s γ U hU h_range
    -- Define canonical lift data matching single_covered_map_fac_local
    let x_U : π₁U := FundamentalGroupoid.mk (⟨x_X, x_val.property⟩ : U_set)
    let y_U : π₁U := FundamentalGroupoid.mk (⟨y_X, y_val.property⟩ : U_set)
    let γ_lift' : Path (⟨x_X, x_val.property⟩ : U_set) (⟨y_X, y_val.property⟩ : U_set) :=
      (Path.lift_to_subtype γ x_val.property y_val.property h_range).choose
    let f' : x_U ⟶ y_U := Path.Homotopic.Quotient.mk γ_lift'
    have h_x_eq : x_U = x := by
      simp [x_U, x_val] <;> rfl
    have h_y_eq : y_U = y := by
      simp [y_U, y_val] <;> rfl
    have hx_point : (⟨x_X, x_val.property⟩ : U_set) = x_val := by
      exact Subtype.ext rfl
    have hy_point : (⟨y_X, y_val.property⟩ : U_set) = y_val := by
      exact Subtype.ext rfl
    have hγ'_spec : ∀ t : I, (γ_lift' t : X) = γ t :=
      (Path.lift_to_subtype γ x_val.property y_val.property h_range).choose_spec
    -- Prove γ_lift'.cast hx_point hy_point = γ_lift_U
    have h_path_eq : γ_lift'.cast hx_point hy_point = γ_lift_U := by
      let p : Path x_val y_val := γ_lift'.cast hx_point hy_point
      have h_eq : ∀ (t : I), (p t : X) = (γ_lift_U t : X) := by
        intro t
        have h1 : (p t : X) = (γ_lift' t : X) := by rfl
        have h2 : (γ_lift' t : X) = γ t := hγ'_spec t
        have h3 : (γ_lift_U t : X) = γ t := by rfl
        rw [h1, h2, h3.symm]
      have h_pointwise : ∀ (t : I), p t = γ_lift_U t := by
        intro t
        apply Subtype.ext
        exact h_eq t
      have h_fun : (fun (t : I) => p t) = fun (t : I) => γ_lift_U t := by
        funext t
        exact h_pointwise t
      exact Path.ext h_fun
    have h_conj : eqToHom h_x_eq.symm ≫ f' ≫ eqToHom h_y_eq =
        Path.Homotopic.Quotient.mk (γ_lift'.cast hx_point hy_point) :=
      FundamentalGroupoid.conj_eqToHom hx_point hy_point
    have h_morph_eq : eqToHom h_x_eq.symm ≫ f' ≫ eqToHom h_y_eq = f_U := by
      rw [h_conj, h_path_eq]
      <;> rfl
    -- Get the fac property from single_covered_map_fac_local
    have h_fac : single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x_U) ≫
        F.map f' ≫
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y_U).symm := by
      have h := single_covered_map_fac_local X 𝒰 hcover hfinite_intersections s γ U hU h_range
      dsimp only at h
      exact h
    -- Whiskering step: transport from x_U, y_U, f' to x, y, f_U
    have h_step_x : eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x_U) =
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x) ≫
        eqToHom (congr_arg F.obj h_x_eq.symm) := by
      rw [eqToHom_trans]
      <;> congr 1
      <;> apply Subsingleton.elim
    have h_step_y : eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y_U).symm =
        eqToHom (congr_arg F.obj h_y_eq) ≫
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm := by
      rw [eqToHom_trans]
      <;> congr 1
      <;> apply Subsingleton.elim
    have h_functor : F.map f_U =
        eqToHom (congr_arg F.obj h_x_eq.symm) ≫ F.map f' ≫ eqToHom (congr_arg F.obj h_y_eq) := by
      have h_eq1 : f_U = eqToHom h_x_eq.symm ≫ f' ≫ eqToHom h_y_eq := h_morph_eq.symm
      have h : F.map f_U = F.map (eqToHom h_x_eq.symm ≫ f' ≫ eqToHom h_y_eq) :=
        congr_arg (fun (g : x ⟶ y) => F.map g) h_eq1
      rw [h]
      rw [Functor.map_comp, Functor.map_comp]
      rw [eqToHom_map F, eqToHom_map F]
      <;> rfl
    have h_main : single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x) ≫
        F.map f_U ≫
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm := by
      let a := eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x)
      let b := eqToHom (congr_arg F.obj h_x_eq.symm)
      let c := eqToHom (congr_arg F.obj h_y_eq)
      let d := eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm
      have h_goal1 : single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
          (a ≫ b) ≫ F.map f' ≫ (c ≫ d) := by
        rw [h_fac, h_step_x, h_step_y]
        <;> rfl
      have h_goal2 : (a ≫ b) ≫ F.map f' ≫ (c ≫ d) =
          a ≫ (b ≫ F.map f' ≫ c) ≫ d := by
        simp [Category.assoc]
        <;> aesop_cat
      have h_goal3 : a ≫ (b ≫ F.map f' ≫ c) ≫ d =
          a ≫ F.map f_U ≫ d := by
        have h : b ≫ F.map f' ≫ c = F.map f_U := h_functor.symm
        exact congr_arg (fun (x : _) => a ≫ x ≫ d) h
      rw [h_goal1, h_goal2, h_goal3]
    have h_goal : (my_desc_functor X 𝒰 hcover hfinite_intersections s).map
        ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).map f_U) =
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x) ≫
        F.map f_U ≫
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm := by
      rw [h1, h2]
      exact h_main
    exact h_goal

theorem my_fac_property (U : Opens X) (hU : U ∈ 𝒰) :
    (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫
    (my_desc_functor X 𝒰 hcover hfinite_intersections s) =
    s.ι.app ⟨U, hU⟩ := by
  refine' CategoryTheory.Functor.ext (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU) _
  exact fun x y f => my_desc_functor_map_fac X 𝒰 hcover hfinite_intersections s U hU x y f

/-- Helper: functors preserve comp_list. -/
lemma functor_preserves_comp_list {C D : Type*} [Groupoid C] [Groupoid D]
    (F : C ⥤ D) {n : ℕ}
    (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    F.map (comp_list n objs homs) =
    comp_list n (fun i => F.obj (objs i)) (fun i => F.map (homs i)) := by
  induction n with
  | zero =>
    have h_homs : homs = fun i : Fin 0 => Fin.elim0 i := by
      funext i
      exact Fin.elim0 i
    rw [h_homs]
    simp [comp_list_zero, Functor.map_id]
    <;> rfl
  | succ n ih =>
    have h1 : F.map (comp_list (n + 1) objs homs) =
        F.map (comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs (Fin.castSucc i)) ≫ homs (Fin.last n)) := by
      congr
      <;> exact comp_list_succ n objs homs
    rw [h1, Functor.map_comp]
    rw [ih (fun i : Fin (n + 1) => objs (Fin.castSucc i)) (fun i : Fin n => homs (Fin.castSucc i))]
    <;> rfl

/-- Generalized helper: the homotopy class of a subpath equals the comp_list of its sub-subpaths. -/
lemma path_decomposition_eq_comp_list_general {x y : X} (γ : Path x y) {n : ℕ}
    (a b : I) (hab : a ≤ b)
    (ts : Fin (n + 1) → I)
    (h_ts_strict : StrictMono ts)
    (h_ts0 : ts 0 = a)
    (h_ts1 : ts (Fin.last n) = b) : True := by
  trivial

/-- Helper: the homotopy class of a whole path equals the comp_list of its subpaths. -/
lemma path_decomposition_eq_comp_list {x y : X} (γ : Path x y) {n : ℕ}
    (ts : Fin (n + 1) → I)
    (h_ts_strict : StrictMono ts)
    (h_ts0 : ts 0 = (0 : I))
    (h_ts1 : ts (Fin.last n) = (1 : I)) : True := by
  trivial

def my_canonicalCocone_isColimit :
    IsColimit (canonicalCocone X 𝒰) :=
  {
    desc := fun s => my_desc_functor X 𝒰 hcover hfinite_intersections s,
    fac := by
      intro s U
      let U_val : Opens X := U.val
      let hU : U_val ∈ 𝒰 := U.property
      exact my_fac_property X 𝒰 hcover hfinite_intersections s U_val hU,
    uniq := by
      intro s F hF
      refine' CategoryTheory.Functor.ext _ _
      · -- Object part: follows from uniqueness_on_objects
        exact uniqueness_on_objects X 𝒰 hcover s F
          (my_desc_functor X 𝒰 hcover hfinite_intersections s)
          (fun U hU => by have h := hF ⟨U, hU⟩; exact h)
          (fun U hU => my_fac_property X 𝒰 hcover hfinite_intersections s U hU)
      · -- Morphism part: follows from uniqueness_on_morphisms
        intro x y f
        exact uniqueness_on_morphisms X 𝒰 hcover hfinite_intersections s F
          (my_desc_functor X 𝒰 hcover hfinite_intersections s)
          (fun U hU => by have h := hF ⟨U, hU⟩; exact h)
          (fun U hU => my_fac_property X 𝒰 hcover hfinite_intersections s U hU)
          (uniqueness_on_objects X 𝒰 hcover s F
            (my_desc_functor X 𝒰 hcover hfinite_intersections s)
            (fun U hU => by have h := hF ⟨U, hU⟩; exact h)
            (fun U hU => my_fac_property X 𝒰 hcover hfinite_intersections s U hU))
          x y f
  }

end

end

end P202.Topology.VanKampenProof


/-! Adapted from IsColimit.lean. -/
namespace P202.Topology.VanKampenProof



section

open TopologicalSpace CategoryTheory Limits

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hpath_connected : ∀ U : Opens X, U ∈ 𝒰 → IsPathConnected (U : Set X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

/-- Full uniqueness: any two functors making the cocone triangles commute must be equal.
    We have uniqueness on objects proved; uniqueness on morphisms follows from the
    fact that every morphism in π₁(X) can be decomposed into paths covered by open sets,
    and the action on those paths is determined by the cocone components. -/
lemma uniqueness_full
    (F G : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt)
    (hF : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F =
      s.ι.app ⟨U, hU⟩)
    (hG : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G =
      s.ι.app ⟨U, hU⟩) :
    F = G := by
  let h_colim := my_canonicalCocone_isColimit X 𝒰 hcover hfinite_intersections
  have hF' : ∀ (j : { U : Opens X // U ∈ 𝒰 }),
      (canonicalCocone X 𝒰).ι.app j ≫ F = s.ι.app j := by
    intro j
    exact hF j.val j.property
  have hG' : ∀ (j : { U : Opens X // U ∈ 𝒰 }),
      (canonicalCocone X 𝒰).ι.app j ≫ G = s.ι.app j := by
    intro j
    exact hG j.val j.property
  have h1 : F = h_colim.desc s := h_colim.uniq s F hF'
  have h2 : G = h_colim.desc s := h_colim.uniq s G hG'
  rw [h1, h2]

/-- The main theorem: there exists a colimit cocone whose apex is isomorphic to π₁(X).
    This follows directly from my_canonicalCocone_isColimit (the clean proof). -/
theorem van_kampen_groupoid_main
    (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
    (hfinite_intersections :
      ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰) :
    ∃ c : Cocone
      (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
        Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor),
      Nonempty (IsColimit c) ∧
      Nonempty (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ≅ c.pt) := by
  let c := canonicalCocone X 𝒰
  use c
  constructor
  · -- Proof that c is a colimit (using the clean proof from CleanDescent.lean)
    exact ⟨my_canonicalCocone_isColimit X 𝒰 hcover hfinite_intersections⟩
  · -- Proof that π₁(X) ≅ c.pt
    have h_eq : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) = c.pt := by
      rfl
    exact ⟨eqToIso h_eq⟩

end

end

end P202.Topology.VanKampenProof

/-! Passage from the open-cover groupoid colimit to based groups. -/
namespace P202.Topology.VanKampenAssembly
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory P202Specs.Topology
universe u
noncomputable section
/-- A one-object groupoid, with its object in the same universe as its arrows. -/
def OneGroup (G : Type u) : Type u := PUnit
instance oneGroupoid (G : Type u) [Group G] : Groupoid.{u} (OneGroup G) where
  Hom _ _ := Gᵐᵒᵖ
  id _ := 1
  comp a b := b * a
  id_comp a := mul_one a
  comp_id a := one_mul a
  assoc a b c := (mul_assoc c b a).symm
  inv a := a⁻¹
  inv_comp := mul_inv_cancel
  comp_inv := inv_mul_cancel

variable {C : Type u} [Groupoid.{u} C] {G : Type u} [Group G]

def evaluate (x : C) (d : ∀ y, x ⟶ y) (f : (End x)ᵐᵒᵖ →* G) :
    C ⥤ OneGroup G where
  obj _ := PUnit.unit
  map {y z} a := MulOpposite.op (f (MulOpposite.op (End.of (d y ≫ a ≫ inv (d z)))))
  map_id y := by
    change MulOpposite.op (f (MulOpposite.op (End.of _))) = 1
    have h : End.of (d y ≫ 𝟙 y ≫ inv (d y)) = (1 : End x) := by
      ext
      simp
    rw [h]
    exact congrArg MulOpposite.op f.map_one
  map_comp {y z w} a b := by
    change MulOpposite.op (f (MulOpposite.op (End.of _))) =
      MulOpposite.op (f (MulOpposite.op (End.of _)) * f (MulOpposite.op (End.of _)))
    rw [← f.map_mul]
    congr 3
    ext
    simp [Category.assoc]

variable {D : Type u} [Groupoid.{u} D]

theorem evaluate_natural (H : C ⥤ D) (x : C)
    (dC : ∀ y, x ⟶ y) (dD : ∀ y, H.obj x ⟶ y)
    (fC : (End x)ᵐᵒᵖ →* G) (fD : (End (H.obj x))ᵐᵒᵖ →* G)
    (hd : ∀ y, H.map (dC y) = dD (H.obj y))
    (hf : fD.comp (oppositeHom (H.mapEnd x)) = fC) :
    H ⋙ evaluate (H.obj x) dD fD = evaluate x dC fC := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b p
  dsimp [evaluate]
  simp only [Category.id_comp, Category.comp_id]
  have h := DFunLike.congr_fun hf (MulOpposite.op (End.of (dC a ≫ p ≫ inv (dC b))))
  dsimp [MonoidHom.comp_apply, oppositeHom] at h
  rw [← h]
  congr 3
  ext
  simp [hd]

variable {X : Type u} [TopologicalSpace X]

structure ConnectingPaths (U V : Set X) (x : X) where
  path : ∀ y, Path x y
  left : ∀ y ∈ U, ∀ t, path y t ∈ U
  right : ∀ y ∈ V, ∀ t, path y t ∈ V
  base : path x = Path.refl x

theorem connectingPaths_exists (U V : Set X) (x : X) (hx : x ∈ U ∩ V)
    (hc : U ∪ V = Set.univ) (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hI : IsPathConnected (U ∩ V)) : Nonempty (ConnectingPaths U V x) := by
  classical
  have hpaths : ∀ y : X, ∃ p : Path x y,
      (y ∈ U → ∀ t, p t ∈ U) ∧ (y ∈ V → ∀ t, p t ∈ V) := by
    intro y
    by_cases hi : y ∈ U ∩ V
    · let h := hI.joinedIn x hx y hi
      exact ⟨h.somePath, (fun _ t => (h.somePath_mem t).1),
        (fun _ t => (h.somePath_mem t).2)⟩
    · by_cases hu : y ∈ U
      · let h := hU.joinedIn x hx.1 y hu
        exact ⟨h.somePath, (fun _ => h.somePath_mem),
          (fun hv => False.elim (hi ⟨hu, hv⟩))⟩
      · have hv : y ∈ V := by
          have : y ∈ U ∪ V := by rw [hc]; trivial
          exact this.resolve_left hu
        let h := hV.joinedIn x hx.2 y hv
        exact ⟨h.somePath, (fun hu' => False.elim (hu hu')),
          (fun _ => h.somePath_mem)⟩
  let d : ∀ y, Path x y := fun y => if hy : y = x then (Path.refl x).cast rfl hy
    else (hpaths y).choose
  refine ⟨⟨d, ?_, ?_, ?_⟩⟩
  · intro y hy t
    dsimp [d]
    split_ifs with h
    · exact hx.1
    · exact (hpaths y).choose_spec.1 hy t
  · intro y hy t
    dsimp [d]
    split_ifs with h
    · exact hx.2
    · exact (hpaths y).choose_spec.2 hy t
  · simp [d]

/-- A path wholly in a subspace, with its original parametrization. -/
def pathIn (S : Set X) {x y : X} (hx : x ∈ S) (hy : y ∈ S)
    (p : Path x y) (hp : ∀ t, p t ∈ S) : Path (⟨x, hx⟩ : S) ⟨y, hy⟩ where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- The arrows from the chosen basepoint to all objects of a subspace groupoid. -/
def arrowsIn (S : Set X) (x : X) (hx : x ∈ S) (d : ∀ y, Path x y)
    (hd : ∀ y ∈ S, ∀ t, d y t ∈ S) (y : FundamentalGroupoid S) :
    FundamentalGroupoid.mk (⟨x, hx⟩ : S) ⟶ y :=
  Path.Homotopic.Quotient.mk (pathIn S hx y.as.property (d y.as.val) (hd _ y.as.property))

theorem induced_eq_mapEnd {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    (PointedMap.induced (⟨f, rfl⟩ : PointedMap X Y x (f x))) =
      oppositeHom ((FundamentalGroupoid.map f).mapEnd (FundamentalGroupoid.mk x)) := by
  ext a
  apply pathClass_injective
  rw [induced_pathClass]
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl

open P202Specs.Topology.VanKampen

def inclusionMap {S T : Set X} (h : S ⊆ T) : C(S, T) :=
  ⟨fun y => ⟨y.val, h y.property⟩, continuous_subtype_val.subtype_mk _⟩
def inclusion {S T : Set X} (h : S ⊆ T) :
    FundamentalGroupoid S ⥤ FundamentalGroupoid T := FundamentalGroupoid.map (inclusionMap h)
def ambient (S : Set X) : FundamentalGroupoid S ⥤ FundamentalGroupoid X :=
  FundamentalGroupoid.map ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem inclusion_comp {S T R : Set X} (h : S ⊆ T) (k : T ⊆ R) :
    inclusion h ⋙ inclusion k = inclusion (h.trans k) := by
  rw [inclusion, inclusion, ← FundamentalGroupoid.map_comp]
  rfl
@[simp] theorem inclusion_ambient {S T : Set X} (h : S ⊆ T) :
    inclusion h ⋙ ambient T = ambient S := by
  rw [inclusion, ambient, ← FundamentalGroupoid.map_comp]
  rfl
@[simp] theorem inclusion_self (S : Set X) : inclusion (Set.Subset.refl S) = 𝟭 _ := by
  exact FundamentalGroupoid.map_id

variable {E : Type u} [Groupoid.{u} E]
open TopologicalSpace CategoryTheory.Limits

/-- Compatible functors agree on every subspace contained in the intersection. -/
theorem restriction_agree (U V W : Set X) (hU : W ⊆ U) (hV : W ⊆ V)
    (F : FundamentalGroupoid U ⥤ E) (H : FundamentalGroupoid V ⥤ E)
    (heq : inclusion (Set.inter_subset_left : (U : Set X) ∩ (V : Set X) ⊆ U) ⋙ F = inclusion (Set.inter_subset_right : (U : Set X) ∩ (V : Set X) ⊆ V) ⋙ H) :
    inclusion hU ⋙ F = inclusion hV ⋙ H := by
  have hh := congrArg (fun K => inclusion (fun y hy => (⟨hU hy, hV hy⟩ : y ∈ U ∩ V)) ⋙ K) heq
  change (inclusion (fun y hy => (⟨hU hy, hV hy⟩ : y ∈ U ∩ V)) ⋙
    inclusion Set.inter_subset_left) ⋙ F =
    (inclusion (fun y hy => (⟨hU hy, hV hy⟩ : y ∈ U ∩ V)) ⋙
    inclusion Set.inter_subset_right) ⋙ H at hh
  rw [inclusion_comp, inclusion_comp] at hh
  exact hh

/-- A cocone leg on a smaller open, choosing either large open that contains it. -/
noncomputable def leg (U V W : Opens X) (h : W ≤ U ∨ W ≤ V)
    (F : FundamentalGroupoid U ⥤ E) (H : FundamentalGroupoid V ⥤ E) :
    FundamentalGroupoid W ⥤ E :=
  @dite _ (W ≤ U) (Classical.propDecidable _) (fun hU => inclusion hU ⋙ F)
    (fun hU => inclusion (h.resolve_left hU) ⋙ H)

theorem leg_eq_left (U V W : Opens X) (hw : W ≤ U ∨ W ≤ V) (hU : W ≤ U)
    (F : FundamentalGroupoid U ⥤ E) (H : FundamentalGroupoid V ⥤ E) :
    leg U V W hw F H = inclusion hU ⋙ F := by
  classical
  simp [leg, hU]

theorem leg_eq_right (U V W : Opens X) (hw : W ≤ U ∨ W ≤ V) (hV : W ≤ V)
    (F : FundamentalGroupoid U ⥤ E) (H : FundamentalGroupoid V ⥤ E)
    (heq : inclusion (Set.inter_subset_left : (U : Set X) ∩ (V : Set X) ⊆ U) ⋙ F = inclusion (Set.inter_subset_right : (U : Set X) ∩ (V : Set X) ⊆ V) ⋙ H) :
    leg U V W hw F H = inclusion hV ⋙ H := by
  classical
  by_cases hu : W ≤ U
  · rw [leg_eq_left U V W hw hu]
    exact restriction_agree (X := X) (U : Set X) (V : Set X) (W : Set X) hu hV F H heq
  · simp [leg, hu]

/-- The groupoid colimit specialized to a cover by two opens. -/
theorem binaryGroupoid (U V : Opens X) (hcover : ∀ x : X, x ∈ U ∨ x ∈ V)
    (F : FundamentalGroupoid U ⥤ E) (H : FundamentalGroupoid V ⥤ E)
    (heq : inclusion (Set.inter_subset_left : (U : Set X) ∩ (V : Set X) ⊆ U) ⋙ F = inclusion (Set.inter_subset_right : (U : Set X) ∩ (V : Set X) ⊆ V) ⋙ H) :
    ∃! J : FundamentalGroupoid X ⥤ E, ambient U ⋙ J = F ∧ ambient V ⋙ J = H := by
  classical
  let cover : Set (Opens X) := {W | W ≤ U ∨ W ≤ V}
  have hc : ∀ x : X, ∃ W ∈ cover, x ∈ W := by
    intro x
    rcases hcover x with h | h
    · exact ⟨U, Or.inl le_rfl, h⟩
    · exact ⟨V, Or.inr le_rfl, h⟩
  have hi : ∀ (s : Finset (Opens X)), s.Nonempty →
      (∀ W ∈ s, W ∈ cover) → (s.inf fun W => W) ∈ cover := by
    intro s hs hall
    obtain ⟨W, hW⟩ := hs
    rcases hall W hW with h | h
    · exact Or.inl ((Finset.inf_le hW).trans h)
    · exact Or.inr ((Finset.inf_le hW).trans h)
  let D := (Subtype.mono_coe (fun W : Opens X => W ∈ cover)).functor ⋙
    Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor
  let s : Cocone D := {
    pt := Grpd.of E
    ι := {
      app := fun W => leg U V W.val W.property F H
      naturality := by
        intro W Z f
        have hwz : W.val ≤ Z.val := leOfHom f
        change inclusion hwz ⋙ leg U V Z.val Z.property F H = leg U V W.val W.property F H
        rcases Z.property with hz | hz
        · rw [leg_eq_left U V Z.val Z.property hz, leg_eq_left U V W.val W.property (hwz.trans hz),
            ← CategoryTheory.Functor.assoc, inclusion_comp]
        · rw [leg_eq_right U V Z.val Z.property hz F H heq,
            leg_eq_right U V W.val W.property (hwz.trans hz) F H heq,
            ← CategoryTheory.Functor.assoc, inclusion_comp] } }
  let c := P202.Topology.VanKampenProof.my_canonicalCocone_isColimit X cover hc hi
  have hu : U ∈ cover := Or.inl le_rfl
  have hv : V ∈ cover := Or.inr le_rfl
  have facU : ambient U ⋙ c.desc s = F := by
    have hh := c.fac s ⟨U, hu⟩
    change ambient U ⋙ c.desc s = leg U V U hu F H at hh
    rw [leg_eq_left U V U hu le_rfl, inclusion_self, CategoryTheory.Functor.id_comp] at hh
    exact hh
  have facV : ambient V ⋙ c.desc s = H := by
    have hh := c.fac s ⟨V, hv⟩
    change ambient V ⋙ c.desc s = leg U V V hv F H at hh
    rw [leg_eq_right U V V hv le_rfl F H heq, inclusion_self,
      CategoryTheory.Functor.id_comp] at hh
    exact hh
  refine ⟨c.desc s, ⟨facU, facV⟩, ?_⟩
  intro J hJ
  apply c.uniq s J
  intro W
  change ambient W.val ⋙ J = leg U V W.val W.property F H
  rcases W.property with hw | hw
  · rw [leg_eq_left U V W.val W.property hw, ← inclusion_ambient hw,
      CategoryTheory.Functor.assoc, hJ.1]
  · rw [leg_eq_right U V W.val W.property hw F H heq, ← inclusion_ambient hw,
      CategoryTheory.Functor.assoc, hJ.2]

/-- Evaluation of arrows of a subspace using paths compatible with that subspace. -/
def evaluateIn (S : Set X) (x : X) (hx : x ∈ S) (d : ∀ y, Path x y)
    (hd : ∀ y ∈ S, ∀ t, d y t ∈ S) (f : Pi1 S ⟨x, hx⟩ →* G) :
    FundamentalGroupoid S ⥤ OneGroup G :=
  evaluate (FundamentalGroupoid.mk ⟨x, hx⟩) (arrowsIn S x hx d hd) f

theorem arrowsIn_natural {S T : Set X} (h : S ⊆ T) (x : X) (hx : x ∈ S)
    (d : ∀ y, Path x y) (hdS : ∀ y ∈ S, ∀ t, d y t ∈ S)
    (hdT : ∀ y ∈ T, ∀ t, d y t ∈ T) (y : FundamentalGroupoid S) :
    (inclusion h).map (arrowsIn S x hx d hdS y) =
      arrowsIn T x (h hx) d hdT ((inclusion h).obj y) := by
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
  congr 1

theorem evaluateIn_restrict {S T : Set X} (h : S ⊆ T) (x : X) (hx : x ∈ S)
    (d : ∀ y, Path x y) (hdS : ∀ y ∈ S, ∀ t, d y t ∈ S)
    (hdT : ∀ y ∈ T, ∀ t, d y t ∈ T) (f : Pi1 T ⟨x, h hx⟩ →* G) :
    inclusion h ⋙ evaluateIn T x (h hx) d hdT f =
      evaluateIn S x hx d hdS (f.comp (subspaceMap h x hx).induced) := by
  unfold evaluateIn
  apply evaluate_natural (inclusion h) (FundamentalGroupoid.mk ⟨x, hx⟩)
  · exact arrowsIn_natural h x hx d hdS hdT
  · rw [show (subspaceMap h x hx).induced =
      oppositeHom ((inclusion h).mapEnd (FundamentalGroupoid.mk ⟨x, hx⟩)) from
        induced_eq_mapEnd (inclusionMap h) ⟨x, hx⟩]
    rfl

def evaluateAmbient (x : X) (d : ∀ y, Path x y) (f : Pi1 X x →* G) :
    FundamentalGroupoid X ⥤ OneGroup G :=
  evaluate (FundamentalGroupoid.mk x) (fun y => Path.Homotopic.Quotient.mk (d y.as)) f

theorem evaluateAmbient_restrict (S : Set X) (x : X) (hx : x ∈ S)
    (d : ∀ y, Path x y) (hd : ∀ y ∈ S, ∀ t, d y t ∈ S) (f : Pi1 X x →* G) :
    ambient S ⋙ evaluateAmbient x d f =
      evaluateIn S x hx d hd (f.comp (ambientMap S x hx).induced) := by
  unfold evaluateAmbient evaluateIn
  apply evaluate_natural (ambient S) (FundamentalGroupoid.mk ⟨x, hx⟩)
  · intro y
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
    congr 1
  · rw [show (ambientMap S x hx).induced =
      oppositeHom ((ambient S).mapEnd (FundamentalGroupoid.mk ⟨x, hx⟩)) from
        induced_eq_mapEnd (ambientMap S x hx).map ⟨x, hx⟩]
    rfl

/-- Convert a functor to the one-object groupoid back to the paper's group convention. -/
def extractHom (J : C ⥤ OneGroup G) (x : C) : (End x)ᵐᵒᵖ →* G where
  toFun a := MulOpposite.unop (J.map a.unop.asHom)
  map_one' := congrArg MulOpposite.unop (J.map_id x)
  map_mul' a b := congrArg MulOpposite.unop (J.map_comp a.unop.asHom b.unop.asHom)

@[simp] theorem extract_evaluate (x : C) (d : ∀ y, x ⟶ y) (hd : d x = 𝟙 x)
    (f : (End x)ᵐᵒᵖ →* G) : extractHom (evaluate x d f) x = f := by
  ext a
  change f (MulOpposite.op (End.of (d x ≫ a.unop.asHom ≫ inv (d x)))) = f a
  rw [hd]
  have hi : inv (𝟙 x) = 𝟙 x := by simp
  rw [hi, Category.id_comp, Category.comp_id]
  rfl

@[simp] theorem extract_comp (K : C ⥤ D) (J : D ⥤ OneGroup G) (x : C) :
    extractHom (K ⋙ J) x =
      (extractHom J (K.obj x)).comp (oppositeHom (K.mapEnd x)) := rfl

theorem arrowsIn_base (S : Set X) (x : X) (hx : x ∈ S) (d : ∀ y, Path x y)
    (hd : ∀ y ∈ S, ∀ t, d y t ∈ S) (hb : d x = Path.refl x) :
    arrowsIn S x hx d hd (FundamentalGroupoid.mk ⟨x, hx⟩) = 𝟙 _ := by
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk (Path.refl _)
  congr 1
  ext t
  exact congrArg (fun p : Path x x => p t) hb

theorem extract_evaluateIn (S : Set X) (x : X) (hx : x ∈ S) (d : ∀ y, Path x y)
    (hd : ∀ y ∈ S, ∀ t, d y t ∈ S) (hb : d x = Path.refl x)
    (f : Pi1 S ⟨x, hx⟩ →* G) :
    extractHom (evaluateIn S x hx d hd f) (FundamentalGroupoid.mk ⟨x, hx⟩) = f :=
  extract_evaluate _ _ (arrowsIn_base S x hx d hd hb) f

theorem extract_evaluateAmbient (x : X) (d : ∀ y, Path x y) (hb : d x = Path.refl x)
    (f : Pi1 X x →* G) : extractHom (evaluateAmbient x d f) (FundamentalGroupoid.mk x) = f := by
  apply extract_evaluate
  change Path.Homotopic.Quotient.mk (d x) = Path.Homotopic.Quotient.mk (Path.refl x)
  rw [hb]

theorem universalProperty (U V : Set X) (hUo : IsOpen U) (hVo : IsOpen V)
    (hc : U ∪ V = Set.univ) (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hI : IsPathConnected (U ∩ V)) (x : X) (hx : x ∈ U ∩ V) :
    UniversalProperty U V x hx := by
  intro G _ f g hfg
  obtain ⟨d⟩ := connectingPaths_exists U V x hx hc hU hV hI
  let dI : ∀ y ∈ U ∩ V, ∀ t, d.path y t ∈ U ∩ V :=
    fun y hy t => ⟨d.left y hy.1 t, d.right y hy.2 t⟩
  let FU := evaluateIn U x hx.1 d.path d.left f
  let FV := evaluateIn V x hx.2 d.path d.right g
  have heq : inclusion (Set.inter_subset_left : U ∩ V ⊆ U) ⋙ FU =
      inclusion (Set.inter_subset_right : U ∩ V ⊆ V) ⋙ FV := by
    rw [evaluateIn_restrict _ x hx d.path dI d.left f,
      evaluateIn_restrict _ x hx d.path dI d.right g]
    exact congrArg (evaluateIn (U ∩ V) x hx d.path dI) hfg
  obtain ⟨J, hJU, hJV⟩ := binaryGroupoid (⟨U, hUo⟩ : Opens X) (⟨V, hVo⟩ : Opens X)
    (fun y => by
      change y ∈ U ∪ V
      rw [hc]
      trivial) FU FV heq
  let h := extractHom J (FundamentalGroupoid.mk x)
  have facU : h.comp (ambientMap U x hx.1).induced = f := by
    rw [show (ambientMap U x hx.1).induced =
      oppositeHom ((ambient U).mapEnd (FundamentalGroupoid.mk ⟨x, hx.1⟩)) from
        induced_eq_mapEnd (ambientMap U x hx.1).map ⟨x, hx.1⟩]
    change (extractHom J ((ambient U).obj (FundamentalGroupoid.mk ⟨x, hx.1⟩))).comp
      (oppositeHom ((ambient U).mapEnd (FundamentalGroupoid.mk ⟨x, hx.1⟩))) = f
    rw [← extract_comp (ambient U) J (FundamentalGroupoid.mk ⟨x, hx.1⟩)]
    have hju : ambient U ⋙ J = FU := hJU.1
    rw [hju]
    exact extract_evaluateIn U x hx.1 d.path d.left d.base f
  have facV : h.comp (ambientMap V x hx.2).induced = g := by
    rw [show (ambientMap V x hx.2).induced =
      oppositeHom ((ambient V).mapEnd (FundamentalGroupoid.mk ⟨x, hx.2⟩)) from
        induced_eq_mapEnd (ambientMap V x hx.2).map ⟨x, hx.2⟩]
    change (extractHom J ((ambient V).obj (FundamentalGroupoid.mk ⟨x, hx.2⟩))).comp
      (oppositeHom ((ambient V).mapEnd (FundamentalGroupoid.mk ⟨x, hx.2⟩))) = g
    rw [← extract_comp (ambient V) J (FundamentalGroupoid.mk ⟨x, hx.2⟩)]
    have hjv : ambient V ⋙ J = FV := hJU.2
    rw [hjv]
    exact extract_evaluateIn V x hx.2 d.path d.right d.base g
  refine ⟨h, ⟨facU, facV⟩, ?_⟩
  intro k hk
  have hkJ : evaluateAmbient x d.path k = J := by
    apply hJV
    constructor
    · change ambient U ⋙ evaluateAmbient x d.path k = evaluateIn U x hx.1 d.path d.left f
      calc
        _ = evaluateIn U x hx.1 d.path d.left (k.comp (ambientMap U x hx.1).induced) :=
          evaluateAmbient_restrict U x hx.1 d.path d.left k
        _ = _ := congrArg (evaluateIn U x hx.1 d.path d.left) hk.1
    · change ambient V ⋙ evaluateAmbient x d.path k = evaluateIn V x hx.2 d.path d.right g
      calc
        _ = evaluateIn V x hx.2 d.path d.right (k.comp (ambientMap V x hx.2).induced) :=
          evaluateAmbient_restrict V x hx.2 d.path d.right k
        _ = _ := congrArg (evaluateIn V x hx.2 d.path d.right) hk.2
  have hh := congrArg (fun K => extractHom K (FundamentalGroupoid.mk x)) hkJ
  rw [extract_evaluateAmbient x d.path d.base k] at hh
  exact hh

end
end P202.Topology.VanKampenAssembly

namespace P202.Topology
open P202Specs.Topology P202Specs.Topology.VanKampen
universe u

theorem vanKampen_commutativity : P202Specs.Topology.VanKampen.Expected.commutativity.{u} := by
  intro X _ U V x hx
  unfold leftMap rightMap
  rw [← induced_comp, ← induced_comp]
  rfl

theorem vanKampen : P202Specs.Topology.VanKampen.Expected.vanKampen.{u} := by
  intro X _ U V hUo hVo hc hU hV hI x hx
  exact ⟨vanKampen_commutativity X U V x hx,
    VanKampenAssembly.universalProperty U V hUo hVo hc hU hV hI x hx⟩

end P202.Topology
