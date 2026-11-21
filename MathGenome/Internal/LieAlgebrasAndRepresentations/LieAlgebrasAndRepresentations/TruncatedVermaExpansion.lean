import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.TruncatedVermaExpansion
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightCasimir
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightSubmodules
import Mathlib.Data.Set.Finite.List
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LieAlgebrasAndRepresentations.TruncatedVermaExpansion

open Specs.LieAlgebrasAndRepresentations.TruncatedVermaExpansion
open Specs.LieAlgebrasAndRepresentations.FormalCharacters (cone weightSpaces_independent)
open Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir
open Specs.LieAlgebrasAndRepresentations.HighestWeightData (weightSpace_value)
open Specs.LieAlgebrasAndRepresentations.SerreRelations
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open ModuleCasimir (action)
open scoped Classical

open private highestVector_mem_weight from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal

attribute [local instance 100] LieRing.ofAssociativeRing
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u v w z i
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)
local notation "Q₊" => cone H φ
local notation "mult" => Specs.LieAlgebrasAndRepresentations.FormalCharacters.multiplicity

private abbrev rootSum (l : List (simple H φ)) : Module.Dual ℂ H := (l.map Subtype.val).sum

private theorem mem_cone_iff (β : Module.Dual ℂ H) :
    β ∈ Q₊ ↔ ∃ l : List (simple H φ), rootSum H φ l = β := by
  constructor
  · intro h
    refine Submodule.span_induction (p := fun x _ => ∃ l, rootSum H φ l = x)
      ?_ ?_ ?_ ?_ h
    · rintro _ ⟨j, rfl⟩
      exact ⟨[j], by simp [rootSum]⟩
    · exact ⟨[], rfl⟩
    · rintro x y _ _ ⟨l, rfl⟩ ⟨k, rfl⟩
      exact ⟨l ++ k, by simp [rootSum]⟩
    · rintro n x _ ⟨l, hl⟩
      induction n with
      | zero => exact ⟨[], by simp [rootSum]⟩
      | succ n ih =>
        obtain ⟨k, hk⟩ := ih
        exact ⟨k ++ l, by rw [show rootSum H φ (k ++ l) = rootSum H φ k + rootSum H φ l from by simp [rootSum],
          hk, hl, succ_nsmul]⟩
  · rintro ⟨l, rfl⟩
    induction l with
    | nil => exact Submodule.zero_mem _
    | cons j l ih =>
      exact Submodule.add_mem _ (Submodule.subset_span ⟨j, rfl⟩) ih

private theorem direction_nonneg {β : Module.Dual ℂ H} (hβ : β ∈ Q₊) :
    0 ≤ φ β := by
  obtain ⟨l, rfl⟩ := (mem_cone_iff H φ β).mp hβ
  clear hβ
  induction l with
  | nil => simp [rootSum]
  | cons j l ih =>
    change 0 ≤ φ (j.val + rootSum H φ l)
    rw [map_add]
    exact add_nonneg j.property.1.2.le ih

/-- A finite cutoff for the positive direction, containing all weights through the
requested height. Moving up inside the cone preserves membership. -/
private def window (lam : Module.Dual ℂ H) (r : ℝ) : Set (Module.Dual ℂ H) :=
  {μ | lam - μ ∈ Q₊ ∧ φ lam - r ≤ φ μ}

private theorem window_finite [Fintype (simple H φ)] (lam : Module.Dual ℂ H) (r : ℝ) :
    (window H φ lam r).Finite := by
  obtain ⟨δ, hδ, hlow⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ j : simple H φ, δ ≤ φ j.val := by
    by_cases h : (Finset.univ : Finset (simple H φ)).Nonempty
    · obtain ⟨j, _, hj⟩ := Finset.exists_min_image _ (fun j : simple H φ => φ j.val) h
      exact ⟨φ j.val, j.property.1.2, fun k => hj k (Finset.mem_univ _)⟩
    · exact ⟨1, one_pos, fun j => (h ⟨j, Finset.mem_univ _⟩).elim⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (r / δ)
  apply ((List.finite_length_le (simple H φ) n).image
    (fun l => lam - rootSum H φ l)).subset
  intro μ hμ
  obtain ⟨l, hl⟩ := (mem_cone_iff H φ _).mp hμ.1
  refine ⟨l, ?_, ?_⟩
  swap
  · change lam - rootSum H φ l = μ
    rw [hl, sub_sub_cancel]
  have hlen (k : List (simple H φ)) : (k.length : ℝ) * δ ≤ φ (rootSum H φ k) := by
    induction k with
    | nil => simp [rootSum]
    | cons j k ih =>
      change ((k.length + 1 : ℕ) : ℝ) * δ ≤ φ (j.val + rootSum H φ k)
      rw [map_add, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [add_comm _ δ]
      exact add_le_add (hlow j) ih
  have hupper : φ (rootSum H φ l) ≤ r := by
    rw [hl, map_sub]
    exact sub_le_comm.mp hμ.2
  have hcast : (l.length : ℝ) ≤ n :=
    ((le_div_iff₀ hδ).mpr ((hlen l).trans hupper)).trans hn.le
  exact_mod_cast hcast

private theorem height_mem_window [Fintype (simple H φ)] (lam μ : Module.Dual ℂ H)
    (N : ℕ) (h : HeightAtMost H φ (lam - μ) N) :
    μ ∈ window H φ lam ((N : ℝ) * ∑ j : simple H φ, φ j.val) := by
  obtain ⟨l, hl, hn⟩ := h
  refine ⟨(mem_cone_iff H φ _).mpr ⟨l, hl⟩, ?_⟩
  let R := ∑ j : simple H φ, φ j.val
  have hR : 0 ≤ R := Finset.sum_nonneg fun j _ => j.property.1.2.le
  have hlen (k : List (simple H φ)) : φ (rootSum H φ k) ≤ (k.length : ℝ) * R := by
    induction k with
    | nil => simp [rootSum]
    | cons j k ih =>
      change φ (j.val + rootSum H φ k) ≤ ((k.length + 1 : ℕ) : ℝ) * R
      rw [map_add, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm _ R]
      exact add_le_add (Finset.single_le_sum (fun j _ => j.property.1.2.le) (Finset.mem_univ j)) ih
  have hn' : (l.length : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have hupper := (hlen l).trans (mul_le_mul_of_nonneg_right hn' hR)
  change rootSum H φ l = lam - μ at hl
  rw [hl, map_sub] at hupper
  exact sub_le_comm.mp hupper

section WeightModules

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
variable {T : Type w} [AddCommGroup T] [Module ℂ T] [LieRingModule L T] [LieModule ℂ L T]
variable {X : Type z} [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]

private theorem map_action (f : T →ₗ⁅ℂ,L⁆ V) (a : U L) (m : T) :
    f (action ℂ L T a m) = action ℂ L V a (f m) :=
  (Shared.Lie.morphism_correspondence ℂ L T V (LieModule.toEnd ℂ L T)
    (LieModule.toEnd ℂ L V) f.toLinearMap).mpr (fun x m => f.map_lie x m) a m

private theorem map_mem_weight (f : T →ₗ⁅ℂ,L⁆ V) {μ : Module.Dual ℂ H} {x : T}
    (hx : x ∈ weightSpace_value T H μ) : f x ∈ weightSpace_value V H μ := by
  rw [HighestWeight.mem_weightSpace] at hx ⊢
  intro h
  rw [← f.map_lie, hx h, map_smul]

private theorem mem_weight_of_map (f : T →ₗ⁅ℂ,L⁆ V) (hf : Function.Injective f)
    {μ : Module.Dual ℂ H} {x : T} (hx : f x ∈ weightSpace_value V H μ) :
    x ∈ weightSpace_value T H μ := by
  rw [HighestWeight.mem_weightSpace] at hx ⊢
  intro h
  apply hf
  rw [f.map_lie, map_smul, hx h]

private def weightMap (f : T →ₗ⁅ℂ,L⁆ V) (μ : Module.Dual ℂ H) :
    weightSpace_value T H μ →ₗ[ℂ] weightSpace_value V H μ :=
  (f.toLinearMap.comp (weightSpace_value T H μ).subtype).codRestrict _
    (fun x => map_mem_weight H f x.property)

variable [H.IsCartanSubalgebra]

private theorem weightMap_surjective (f : T →ₗ⁅ℂ,L⁆ V) (hf : Function.Surjective f)
    (hT : DirectSum.IsInternal (weightSpace_value T H)) (μ : Module.Dual ℂ H) :
    Function.Surjective (weightMap H f μ) := by
  let images := fun ν => (weightSpace_value T H ν).map f.toLinearMap
  have hle : images ≤ weightSpace_value V H := by
    rintro ν _ ⟨y, hy, rfl⟩
    exact map_mem_weight H f hy
  have hspan : (⨆ ν, images ν) = ⊤ := by
    change (⨆ ν, (weightSpace_value T H ν).map f.toLinearMap) = ⊤
    rw [← Submodule.map_iSup, hT.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf
  -- The images span the target inside its independent family of weight spaces.
  have himages := ((weightSpaces_independent H V).le_iff_eq_of_iSup_eq_top hspan).mp hle
  intro x
  have hx : (x : V) ∈ images μ := by
    rw [congrFun himages μ]
    exact x.property
  obtain ⟨m, hm, he⟩ := hx
  exact ⟨⟨m, hm⟩, Subtype.ext he⟩

private theorem weightMap_injective (f : T →ₗ⁅ℂ,L⁆ V) (hf : Function.Injective f)
    (μ : Module.Dual ℂ H) : Function.Injective (weightMap H f μ) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

private theorem weightSpace_bot_of_injective (f : T →ₗ⁅ℂ,L⁆ V)
    (hf : Function.Injective (weightMap H f μ)) (hV : weightSpace_value V H μ = ⊥) :
    weightSpace_value T H μ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hz : weightMap H f μ ⟨x, hx⟩ = 0 := Subtype.ext
    ((Submodule.eq_bot_iff _).mp hV _ (weightMap H f μ ⟨x, hx⟩).property)
  have hz' : (⟨x, hx⟩ : weightSpace_value T H μ) = 0 := hf (hz.trans (map_zero _).symm)
  exact congrArg Subtype.val hz'

private theorem weightSpace_bot_of_surjective (f : T →ₗ⁅ℂ,L⁆ V)
    (hf : Function.Surjective (weightMap H f μ)) (hT : weightSpace_value T H μ = ⊥) :
    weightSpace_value V H μ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := hf ⟨x, hx⟩
  have hy0 : y = 0 := Subtype.ext (((Submodule.eq_bot_iff _).mp hT) y y.property)
  simpa [hy0] using (congrArg Subtype.val hy).symm

private theorem multiplicity_exact (f : T →ₗ⁅ℂ,L⁆ V) (g : V →ₗ⁅ℂ,L⁆ X)
    (hf : Function.Injective f) (he : Function.Exact f g) (hg : Function.Surjective g)
    (hV : DirectSum.IsInternal (weightSpace_value V H)) (μ : Module.Dual ℂ H)
    [FiniteDimensional ℂ (weightSpace_value V H μ)] :
    mult H V μ = mult H T μ + mult H X μ := by
  let F := weightMap H f μ
  let G := weightMap H g μ
  have hker : G.ker = F.range := by
    ext x
    change G x = 0 ↔ ∃ y, F y = x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (he x.val).mp (congrArg Subtype.val hx)
      exact ⟨⟨y, mem_weight_of_map H f hf (hy ▸ x.property)⟩, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext (he.apply_apply_eq_zero _)
  have hdim := G.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (weightMap_surjective H g hg hV μ), finrank_top, hker,
    ← (LinearEquiv.ofInjective F (weightMap_injective H f hf μ)).finrank_eq] at hdim
  unfold Specs.LieAlgebrasAndRepresentations.FormalCharacters.multiplicity
  exact_mod_cast ((add_comm _ _).trans hdim).symm

variable (Ω : U L) (c : ℂ) (lam : Module.Dual ℂ H)

private structure Conditions (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V]
    [LieModule ℂ L V] : Prop where
  internal : DirectSum.IsInternal (weightSpace_value V H)
  finite : ∀ μ, FiniteDimensional ℂ (weightSpace_value V H μ)
  support : ∀ μ, weightSpace_value V H μ ≠ ⊥ → lam - μ ∈ Q₊
  scalar : ∀ m : V, action ℂ L V Ω m = c • m

private theorem submodule_conditions [IsLieAbelian H] (hV : Conditions H φ Ω c lam V)
    (P : LieSubmodule ℂ L V) : Conditions H φ Ω c lam P := by
  obtain ⟨hP, _, _⟩ := WeightSubmodules.weight_submodules (P.restr H) hV.internal
  have heq : weightSpace_value P H =
      fun μ => (weightSpace_value V H μ).comap P.toSubmodule.subtype := by
    funext μ
    ext x
    change x ∈ weightSpace_value P H μ ↔ (x : V) ∈ weightSpace_value V H μ
    rw [HighestWeight.mem_weightSpace, HighestWeight.mem_weightSpace]
    exact forall_congr' (fun _ => Subtype.ext_iff)
  refine ⟨?_, fun μ => ?_, fun μ hμ => ?_, fun x => ?_⟩
  · rw [heq]
    exact hP
  · letI := hV.finite μ
    exact FiniteDimensional.of_injective _ (weightMap_injective H P.incl P.injective_incl μ)
  · apply hV.support
    exact fun h => hμ (weightSpace_bot_of_injective H P.incl
      (weightMap_injective H P.incl P.injective_incl μ) h)
  · apply P.injective_incl
    rw [map_action, hV.scalar, map_smul]

private theorem quotient_conditions [IsLieAbelian H] (hV : Conditions H φ Ω c lam V)
    (P : LieSubmodule ℂ L V) : Conditions H φ Ω c lam (V ⧸ P) := by
  let q := LieSubmodule.Quotient.mk' P
  have hq := LieSubmodule.Quotient.surjective_mk' P
  have hs (μ : Module.Dual ℂ H) := weightMap_surjective H q hq hV.internal μ
  have hi := (WeightSubmodules.weight_submodules (P.restr H) hV.internal).2.1
  refine ⟨hi, fun μ => ?_, fun μ hμ => ?_, fun x => ?_⟩
  · letI := hV.finite μ
    exact FiniteDimensional.of_surjective _ (hs μ)
  · exact hV.support μ (fun h => hμ (weightSpace_bot_of_surjective H q (hs μ) h))
  · obtain ⟨m, rfl⟩ := hq x
    rw [← map_action, hV.scalar, map_smul]

private theorem kernel_cokernel_multiplicity
    (f : T →ₗ⁅ℂ,L⁆ V) (hT : Conditions H φ Ω c lam T) (hV : Conditions H φ Ω c lam V)
    (μ : Module.Dual ℂ H) :
    mult H V μ = mult H T μ - mult H f.ker μ +
      mult H (V ⧸ f.range) μ := by
  letI := hT.finite μ
  letI := hV.finite μ
  let p := f.codRestrict f.range fun m => ⟨m, rfl⟩
  have hp : Function.Surjective p := by
    rintro ⟨y, m, rfl⟩
    exact ⟨m, rfl⟩
  have h₁ := multiplicity_exact H f.ker.incl p f.ker.injective_incl
    (by
      intro m
      constructor
      · intro hm
        exact ⟨⟨m, congrArg Subtype.val hm⟩, rfl⟩
      · rintro ⟨⟨m, hm⟩, rfl⟩
        exact Subtype.ext hm) hp hT.internal μ
  have h₂ := multiplicity_exact H f.range.incl (LieSubmodule.Quotient.mk' f.range)
    f.range.injective_incl
    (by
      intro m
      rw [LieSubmodule.Quotient.mk_eq_zero]
      exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.property⟩)
    (LieSubmodule.Quotient.surjective_mk' _) hV.internal μ
  linarith

end WeightModules

section Expansion

open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSpace_value)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
variable (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
variable (B : Form (L := L)) (hB : B.Nondegenerate) (hInv : B.lieInvariant L)
variable {I : Type i} [Fintype I] (b : Module.Basis I ℂ L)
variable (χ : Module.Dual ℂ H → U (borel_value H φ) →ₐ[ℂ] ℂ)
variable (hχ : ∀ μ, IsWeightCharacter H φ μ (χ μ))
variable (e : simple H φ → L) (he : ∀ j, e j ∈ rootSpace_value H j.val ∧ e j ≠ 0)

local notation "Ω" => casimir_value B hB b
local notation "cₘ" => eigenvalue_value H φ B

private theorem direction_pos {β : Module.Dual ℂ H} (hβ : β ∈ Q₊) (hne : β ≠ 0) :
    0 < φ β := by
  obtain ⟨l, rfl⟩ := (mem_cone_iff H φ β).mp hβ
  cases l with
  | nil => exact (hne rfl).elim
  | cons j l =>
    change 0 < φ (j.val + rootSum H φ l)
    rw [map_add]
    exact add_pos_of_pos_of_nonneg j.property.1.2
      (direction_nonneg H φ ((mem_cone_iff H φ _).mpr ⟨l, rfl⟩))

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

private theorem annihilated_by_positive {μ : Module.Dual ℂ H} {w : V}
    (hw : w ∈ weightSpace_value V H μ)
    (habove : ∀ ν, φ μ < φ ν → weightSpace_value V H ν = ⊥) :
    ∀ x ∈ positive_value H φ, ⁅x, w⁆ = 0 := by
  let P : LieSubalgebra ℂ L :=
    { carrier := {x | ⁅x, w⁆ = 0}
      zero_mem' := zero_lie w
      add_mem' := fun hx hy => by
        simp only [Set.mem_ofPred_eq] at *
        rw [add_lie, hx, hy, add_zero]
      smul_mem' := fun r _ hx => by
        simp only [Set.mem_ofPred_eq] at *
        rw [smul_lie, hx, smul_zero]
      lie_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at *
        rw [lie_lie, hx, hy, lie_zero, lie_zero, sub_zero] }
  have hP : positive_value H φ ≤ P := by
    rw [positive_value, rootPart, LieSubalgebra.lieSpan_le]
    rintro x ⟨α, hpos, hx⟩
    have h := HighestWeight.root_action V H α μ x w hx hw
    rw [habove _ (by
      rw [map_add]
      exact lt_add_of_pos_right _ (Set.mem_Ioi.mp hpos))] at h
    exact (Submodule.mem_bot ℂ).mp h
  exact fun x hx => hP hx

include hss hφ hInv hχ e he in
private theorem verma_scalar (μ : Module.Dual ℂ H) :
    letI := inducedLieRingModule H φ (χ μ)
    letI := inducedLieModule H φ (χ μ)
    ∀ m : induced_value H φ (χ μ),
      action ℂ L (induced_value H φ (χ μ)) Ω m = cₘ μ • m := by
  letI := inducedLieRingModule H φ (χ μ)
  letI := inducedLieModule H φ (χ μ)
  let M := induced_value H φ (χ μ)
  let w := highestVector_value H φ (χ μ)
  have hw : w ∈ weightSpace_value M H μ := highestVector_mem_weight H φ (χ μ) μ (hχ μ)
  have hw' := (HighestWeight.mem_weightSpace M H μ w).mp hw
  have hs := (VermaWeightsUniversal.verma_weights hss H φ hφ μ (χ μ) (hχ μ)).2.2.1
  have hpos := annihilated_by_positive H φ hw (fun ν hν => by
    by_contra hn
    have h := direction_nonneg H φ ((hs ν).mp hn)
    rw [map_sub] at h
    exact (not_le_of_gt hν) (sub_nonneg.mp h))
  have hcyc : LieSubmodule.lieSpan ℂ L ({w} : Set M) = ⊤ := by
    let P := LieSubmodule.lieSpan ℂ L ({w} : Set M)
    let q := LieSubmodule.Quotient.mk' P
    have hq : q w = 0 := LieSubmodule.Quotient.mk_eq_zero P |>.mpr
      (LieSubmodule.subset_lieSpan (Set.mem_singleton w))
    obtain ⟨f, _, hunique⟩ :=
      (VermaWeightsUniversal.verma_universal hss H φ hφ μ (χ μ) (hχ μ) e he (M ⧸ P)
        0 (by simp) (by simp)).1
    have hzero : q = 0 := (hunique q hq).trans (hunique 0 (by simp)).symm
    apply top_unique
    intro x _
    apply (LieSubmodule.Quotient.mk_eq_zero P).mp
    simp [← show q = LieSubmodule.Quotient.mk' P from rfl, hzero]
  exact HighestWeightCasimir.eigenvalue_action H hss φ hφ B hB hInv b M μ w hw' hpos hcyc

variable (lam : Module.Dual ℂ H) (c : ℂ)

private def HasExpansion (win : Finset (Module.Dual ℂ H)) (V : Type v)
    [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V] : Prop :=
  ∃ a : Module.Dual ℂ H →₀ ℤ,
    (∀ μ, a μ ≠ 0 → lam - μ ∈ Q₊ ∧ cₘ μ = c) ∧
    ∀ ν ∈ win, mult H V ν =
      (Finsupp.linearCombination ℤ (fun μ => vermaMultiplicity H φ (χ μ)) a) ν

private def Expandable (win S : Finset (Module.Dual ℂ H)) : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V],
    Conditions H φ Ω c lam V →
    (∀ ν ∈ win, ν ∉ S → weightSpace_value V H ν = ⊥) →
    HasExpansion H φ B χ lam c win V

variable {win S : Finset (Module.Dual ℂ H)}

include hss hφ hInv hχ e he in
/-- At a maximal remaining weight, the top line of a single Verma module maps
injectively. The kernel therefore omits that weight, and the cokernel has
strictly smaller multiplicity there. This permits processing the weight one
vector at a time before removing it from the finite set. -/
private theorem expansion_step [IsLieAbelian H]
    (closed_window : ∀ μ ∈ win, ∀ ν, lam - ν ∈ Q₊ → φ μ ≤ φ ν → ν ∈ win)
    (ordered : ∀ μ ∈ S, ∀ ν ∈ win, ν ∉ S → φ μ ≤ φ ν)
    (μ : Module.Dual ℂ H) (hμwin : μ ∈ win)
    (hmax : ∀ ν ∈ S, φ ν ≤ φ μ)
    (ih₁ : Expandable.{u,u,i} H φ B hB b χ lam c win (S.erase μ))
    (ih₂ : Expandable.{u,v,i} H φ B hB b χ lam c win (S.erase μ)) :
    Expandable.{u,v,i} H φ B hB b χ lam c win S := by
  classical
  have run (n : ℕ) : ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V]
      [LieModule ℂ L V], Module.finrank ℂ (weightSpace_value V H μ) = n →
      Conditions H φ Ω c lam V →
      (∀ ν ∈ win, ν ∉ S → weightSpace_value V H ν = ⊥) →
      HasExpansion H φ B χ lam c win V := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ _ _ hn hV hout
      by_cases hzero : weightSpace_value V H μ = ⊥
      · apply ih₂ V hV
        intro ν hν hν'
        by_cases heq : ν = μ
        · simpa [heq] using hzero
        · exact hout ν hν (fun h => hν' (Finset.mem_erase.mpr ⟨heq, h⟩))
      · have hμcone := hV.support μ hzero
        have habove (ν : Module.Dual ℂ H) (hν : φ μ < φ ν) :
            weightSpace_value V H ν = ⊥ := by
          by_contra hne
          exact hne (hout ν (closed_window μ hμwin ν (hV.support ν hne) hν.le)
            (fun h => (not_le_of_gt hν) (hmax ν h)))
        obtain ⟨w, hw, hw₀⟩ := (Submodule.ne_bot_iff _).mp hzero
        have hw' := (HighestWeight.mem_weightSpace V H μ w).mp hw
        have hkill := annihilated_by_positive H φ hw habove
        have hew (j : simple H φ) : ⁅e j, w⁆ = 0 :=
          hkill _ (LieSubalgebra.subset_lieSpan ⟨j.val, j.property.1.2, (he j).1⟩)
        letI := inducedLieRingModule H φ (χ μ)
        letI := inducedLieModule H φ (χ μ)
        let M := induced_value H φ (χ μ)
        let topVector := highestVector_value H φ (χ μ)
        obtain ⟨f, hf, _⟩ :=
          (VermaWeightsUniversal.verma_universal hss H φ hφ μ (χ μ) (hχ μ) e he V w hw' hew).1
        change f topVector = w at hf
        have hScal : ∀ m : M, action ℂ L M Ω m = cₘ μ • m :=
          verma_scalar H φ hss hφ B hB hInv b χ hχ e he μ
        have hcm : cₘ μ = c := by
          apply smul_left_injective ℂ hw₀
          have heq := map_action f Ω topVector
          rw [hScal, map_smul, hf, hV.scalar] at heq
          exact heq
        obtain ⟨hMint, hMfin, hMsupp, hMtop⟩ :=
          VermaWeightsUniversal.verma_weights hss H φ hφ μ (χ μ) (hχ μ)
        have hM : Conditions H φ Ω c lam M := ⟨hMint, hMfin,
          fun ν hν => sub_add_sub_cancel lam μ ν ▸
            Submodule.add_mem _ hμcone ((hMsupp ν).mp hν), by simpa only [hcm] using hScal⟩
        let C := V ⧸ f.range
        let q := LieSubmodule.Quotient.mk' f.range
        have hK := submodule_conditions H φ Ω c lam hM f.ker
        have hC := quotient_conditions H φ Ω c lam hV f.range
        have ktop : weightSpace_value f.ker H μ = ⊥ := by
          apply (Submodule.eq_bot_iff _).mpr
          intro y hy
          have hyM := map_mem_weight H f.ker.incl hy
          change (y : M) ∈ weightSpace_value M H μ at hyM
          rw [hMtop, Submodule.mem_span_singleton] at hyM
          obtain ⟨a, ha⟩ := hyM
          have haz : a • w = 0 := by
            rw [← hf, ← map_smul, ha]
            exact y.property
          have ha₀ := smul_left_injective ℂ hw₀ (haz.trans (zero_smul ℂ w).symm)
          apply Subtype.ext
          change (y : M) = 0
          rw [← ha, ha₀, zero_smul]
        obtain ⟨aK, haK, hKeq⟩ := ih₁ f.ker hK (by
          intro ν hν hν'
          by_cases heq : ν = μ
          · simpa [heq] using ktop
          · have hνS : ν ∉ S := fun hv => hν' (Finset.mem_erase.mpr ⟨heq, hv⟩)
            have hμS : μ ∈ S := by
              by_contra h
              exact hzero (hout μ hμwin h)
            apply weightSpace_bot_of_injective H f.ker.incl
              (weightMap_injective H f.ker.incl f.ker.injective_incl ν)
            by_contra hv
            have hd := direction_pos H φ ((hMsupp ν).mp hv) (sub_ne_zero.mpr (Ne.symm heq))
            rw [map_sub] at hd
            exact (not_lt_of_ge (ordered μ hμS ν hν hνS)) (sub_pos.mp hd))
        have hq (ν : Module.Dual ℂ H) :=
          weightMap_surjective H q (LieSubmodule.Quotient.surjective_mk' _) hV.internal ν
        have hdim : Module.finrank ℂ (weightSpace_value C H μ) < n := by
          let Q := weightMap H q μ
          letI := hV.finite μ
          have hpos : 0 < Module.finrank ℂ Q.ker := by
            apply Module.finrank_pos_iff_exists_ne_zero.mpr
            refine ⟨⟨⟨w, hw⟩, ?_⟩, ?_⟩
            · apply Subtype.ext
              exact (LieSubmodule.Quotient.mk_eq_zero _).mpr ⟨topVector, hf⟩
            · intro h
              exact hw₀ (congrArg (fun x : Q.ker => x.val.val) h)
          have h := Q.finrank_range_add_finrank_ker
          rw [LinearMap.range_eq_top.mpr (hq μ), finrank_top, hn] at h
          change Module.finrank ℂ (weightSpace_value (V ⧸ f.range) H μ) < n
          omega
        obtain ⟨aC, haC, hCeq⟩ := ih _ hdim C rfl hC (fun ν hν hν' =>
          weightSpace_bot_of_surjective H q (hq ν) (hout ν hν hν'))
        refine ⟨Finsupp.single μ 1 - aK + aC, ?_, ?_⟩
        · intro ν hν
          by_cases heq : μ = ν
          · exact heq ▸ ⟨hμcone, hcm⟩
          · by_cases h : aK ν = 0
            · exact haC ν (by simpa [Finsupp.single_eq_of_ne (Ne.symm heq), h] using hν)
            · exact haK ν h
        · intro ν hν
          have h := kernel_cokernel_multiplicity H φ Ω c lam f hM hV ν
          rw [hKeq ν hν, hCeq ν hν] at h
          simpa only [map_add, map_sub, Finsupp.linearCombination_single, one_smul,
            Pi.add_apply, Pi.sub_apply, vermaMultiplicity] using h
  intro V _ _ _ _ hV hout
  exact run _ V rfl hV hout

include hss hφ hInv hχ e he in
private theorem expansion_on_window [IsLieAbelian H]
    (win : Finset (Module.Dual ℂ H))
    (closed_window : ∀ μ ∈ win, ∀ ν, lam - ν ∈ Q₊ → φ μ ≤ φ ν → ν ∈ win) :
    Expandable.{u,v,i} H φ B hB b χ lam c win win := by
  classical
  -- Kernels lie in the universe of the Verma modules. Cokernels lie in the
  -- universe of the module being expanded. Induct for both universes together.
  have both (S : Finset (Module.Dual ℂ H)) :
      S ⊆ win → (∀ μ ∈ S, ∀ ν ∈ win, ν ∉ S → φ μ ≤ φ ν) →
      Expandable.{u,u,i} H φ B hB b χ lam c win S ∧
      Expandable.{u,v,i} H φ B hB b χ lam c win S := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro hsub hord
      by_cases hS : S.Nonempty
      · obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image S φ hS
        have hord' (η : Module.Dual ℂ H) (hη : η ∈ S.erase μ)
            (ν : Module.Dual ℂ H) (hν : ν ∈ win) (hν' : ν ∉ S.erase μ) : φ η ≤ φ ν := by
          have hηS := Finset.mem_of_mem_erase hη
          by_cases h : ν = μ
          · exact h ▸ hmax η hηS
          · exact hord η hηS ν hν (fun hv => hν' (Finset.mem_erase.mpr ⟨h, hv⟩))
        have small := ih (S.erase μ) (Finset.erase_ssubset hμ)
          (fun _ hn => hsub (Finset.mem_of_mem_erase hn)) hord'
        exact ⟨expansion_step H φ hss hφ B hB hInv b χ hχ e he lam c
          closed_window hord μ (hsub hμ) hmax small.1 small.1,
          expansion_step H φ hss hφ B hB hInv b χ hχ e he lam c
          closed_window hord μ (hsub hμ) hmax small.1 small.2⟩
      · have hs : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        subst S
        constructor <;> intro V _ _ _ _ _ h <;>
          refine ⟨0, by simp, fun ν hν => ?_⟩ <;>
          simp only [Specs.LieAlgebrasAndRepresentations.FormalCharacters.multiplicity,
            map_zero, Pi.zero_apply, Nat.cast_eq_zero] <;>
          rw [h ν hν (Finset.notMem_empty ν), finrank_bot]
  exact (both win (fun _ h => h) (fun _ _ ν hν hn => (hn hν).elim)).2

end Expansion

theorem truncated_verma_expansion : truncated_verma_expansion_type.{u,v,i} := by
  classical
  intro L _ _ _ hss H _ φ hφ B hB hInv _hPositive I _ b V _ _ _ _ lam c N hV hfin hsupp hscalar
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  letI : IsLieAbelian H := hH.1.1
  letI : Fintype (simple H φ) :=
    ((rootSet_finite H hH.1).subset (fun _ h => h.1.1)).fintype
  choose χ hχ using fun μ => (VermaModules.character_existsUnique hss H φ hφ μ).exists
  choose e he using fun j : simple H φ => (Submodule.ne_bot_iff _).mp j.property.1.1.2
  let r := (N : ℝ) * ∑ j : simple H φ, φ j.val
  let win := (window_finite H φ lam r).toFinset
  have hwin (μ : Module.Dual ℂ H) : μ ∈ win ↔ μ ∈ window H φ lam r := Set.Finite.mem_toFinset _
  have hclosed (μ : Module.Dual ℂ H) (hμ : μ ∈ win) (ν : Module.Dual ℂ H)
      (hν : lam - ν ∈ cone H φ) (hle : φ μ ≤ φ ν) : ν ∈ win :=
    (hwin ν).mpr ⟨hν, ((hwin μ).mp hμ).2.trans hle⟩
  obtain ⟨a, ha, hcoeff⟩ := expansion_on_window H φ hss hφ B hB hInv b χ hχ e he lam c win
    hclosed V ⟨hV, hfin, hsupp, hscalar⟩ (fun _ h hn => (hn h).elim)
  exact ⟨χ, hχ, a, ha, fun ν hν => hcoeff ν ((hwin ν).mpr (height_mem_window H φ lam ν N hν))⟩

end LieAlgebrasAndRepresentations.TruncatedVermaExpansion
