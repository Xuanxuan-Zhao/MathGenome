import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Set.Finite.List

noncomputable section

namespace LieAlgebrasAndRepresentations.VermaWeightsUniversal

open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.HighestWeightData (positiveRootCone_value weightSpace_value)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open UniversalEnvelopingAlgebra (ι)
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)
variable (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)

local instance : LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ
local instance : LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

private theorem induced_lie (x : L) (m : induced_value H φ χ) :
    ⁅x, m⁆ = ι ℂ x • m := rfl

private theorem tensorClass_eq_smul (a : U L) :
    tensorClass H φ χ a 1 = a • highestVector_value H φ χ := by
  change (balance H φ χ).mkQ (a ⊗ₜ[ℂ] (1 : ℂ)) =
    a • (balance H φ χ).mkQ ((1 : U L) ⊗ₜ[ℂ] (1 : ℂ))
  rw [← map_smul]
  change _ = (balance H φ χ).mkQ ((a * 1) ⊗ₜ[ℂ] (1 : ℂ))
  rw [mul_one]

section Universal

variable (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V]

private theorem lieHom_map_enveloping_smul [Module (U L) V] [IsScalarTower ℂ (U L) V]
    (hι : ∀ (x : L) (w : V), ι ℂ x • w = ⁅x, w⁆)
    (f : induced_value H φ χ →ₗ⁅ℂ,L⁆ V)
    (a : U L) (m : induced_value H φ χ) : f (a • m) = a • f m := by
  induction a using Shared.Lie.enveloping_induction ℂ L generalizing m with
  | scalar r => simp only [algebraMap_smul, map_smul]
  | generator x =>
    rw [Shared.Lie.inclusion, ← induced_lie H φ χ, hι]
    exact f.map_lie x m
  | mul a b ha hb => simp only [mul_smul, ha, hb]
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]

theorem verma_universal : verma_universal_type.{u,v} := by
  intro L _ _ _ hss H _ φ hφ lam χ hχ e he V _ _ _ _ w hw hew
  let A := Shared.Lie.representationEquiv ℂ L V (LieModule.toEnd ℂ L V)
  let _ : Module (U L) V := Shared.Lie.actionModule ℂ L V A
  let _ : IsScalarTower ℂ (U L) V := Shared.Lie.action_tower ℂ L V A
  have hι (x : L) (v : V) : ι ℂ x • v = ⁅x, v⁆ := Shared.Lie.lie_extension ℂ L V x v
  -- Evaluation annihilates the generators of the defining left ideal.
  obtain ⟨E, hE⟩ := VermaModules.induced_presentation hss H φ hφ lam χ hχ e he
  let J := definingIdeal_value H φ lam e
  let ev := LinearMap.toSpanSingleton (U L) V w
  have hk : J ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro _ (⟨h, rfl⟩ | ⟨i, rfl⟩)
    · change ((ι ℂ (h : L) - algebraMap ℂ (U L) (lam h)) • w) = 0
      rw [sub_smul, hι, algebraMap_smul, hw, sub_self]
    · exact (hι (e i) w).trans (hew i)
  let F := (J.liftQ ev hk).comp E.symm.toLinearMap
  let f : induced_value H φ χ →ₗ⁅ℂ,L⁆ V :=
    { F.restrictScalars ℂ with
      map_lie' := fun {x m} => by
        change F ⁅x, m⁆ = ⁅x, F m⁆
        rw [induced_lie H φ χ, F.map_smul, hι] }
  have hf : f (highestVector_value H φ χ) = w := by
    have h1 : E (J.mkQ 1) = highestVector_value H φ χ := hE 1
    change F (highestVector_value H φ χ) = w
    rw [← h1]
    simp [F, ev, J]
  refine ⟨⟨f, hf, ?_⟩, fun _ hcyc => ⟨f, hf, ?_⟩⟩
  · intro g hg
    apply LieModuleHom.ext
    intro m
    obtain ⟨q, rfl⟩ := E.surjective m
    obtain ⟨a, rfl⟩ := J.mkQ_surjective q
    change g (E ((definingIdeal_value H φ lam e).mkQ a)) = _
    rw [hE, tensorClass_eq_smul, lieHom_map_enveloping_smul H φ χ V hι, lieHom_map_enveloping_smul H φ χ V hι, hg, hf]
  · apply (LieModuleHom.range_eq_top f).mp
    apply top_unique
    rw [← hcyc, LieSubmodule.lieSpan_le]
    rintro _ rfl
    exact ⟨_, hf⟩

end Universal

section Weights

open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive)
open Shared.Lie.PBW

open private negative_submodule from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules
open private neg_root_mem from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations

private abbrev PositiveRoot := positive H φ

private abbrev Qplus := positiveRootCone_value (fun i : simple H φ => i.val)

section Negative

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

private theorem positiveRoots_finite (hss : IsSemisimple_value ℂ L) :
    (positive H φ).Finite :=
  (rootSet_finite H (RealRootSpace.cartan_isMaximalToral hss H).1).subset
    (fun _ ha => ha.1)

private theorem positiveRoot_mem_cone (hss : IsSemisimple_value ℂ L) (a : PositiveRoot H φ) :
    a.val ∈ Qplus H φ := by
  by_contra hn
  let missing := {β | β ∈ positive H φ ∧ β ∉ Qplus H φ}
  have hfin : missing.Finite := (positiveRoots_finite H φ hss).subset (fun _ hb => hb.1)
  obtain ⟨β, hβ⟩ := hfin.exists_minimalFor φ missing ⟨a.val, a.property, hn⟩
  have hns : β ∉ simple H φ := fun hs =>
    hβ.prop.2 (Submodule.subset_span ⟨⟨β, hs⟩, rfl⟩)
  have hd : ∃ γ ∈ positive H φ, ∃ δ ∈ positive H φ, β = γ + δ := by
    by_contra hc
    exact hns ⟨hβ.prop.1, by simpa using hc⟩
  obtain ⟨γ, hγ, δ, hδ, hsum⟩ := hd
  have hφsum : φ β = φ γ + φ δ := by rw [hsum, map_add]
  have hsmall (η : Module.Dual ℂ H) (hη : η ∈ positive H φ) (hlt : φ η < φ β) :
      η ∈ Qplus H φ := by
    by_contra hm
    exact (not_le.mpr hlt) (hβ.le_of_le (show η ∈ missing from ⟨hη, hm⟩) hlt.le)
  exact hβ.prop.2 (hsum ▸ (Qplus H φ).add_mem
    (hsmall γ hγ (by linarith [hδ.2])) (hsmall δ hδ (by linarith [hγ.2])))

private theorem exists_negative_basis (hss : IsSemisimple_value ℂ L) :
    ∃ b : Module.Basis (PositiveRoot H φ) ℂ (negative_value H φ),
      ∀ i, (b i : L) ∈ rootSpace H (-i.val) := by
  classical
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  have hroot (i : PositiveRoot H φ) : -i.val ∈ rootSet H :=
    neg_root_mem H hss hH i.property.1
  choose f hf hf0 using fun i : PositiveRoot H φ => (rootSpace H (-i.val)).ne_bot_iff.mp (hroot i).2
  have hmem (i : PositiveRoot H φ) : f i ∈ negative_value H φ :=
    LieSubalgebra.subset_lieSpan ⟨-i.val, by simpa using neg_neg_of_pos i.property.2, hf i⟩
  let b₀ : PositiveRoot H φ → negative_value H φ := fun i => ⟨f i, hmem i⟩
  have heq (i : PositiveRoot H φ) : rootSpace H (-i.val) = ℂ ∙ f i :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (finrank_rootSpace_eq_one hss H hH _ (hroot i)) (hf i) (hf0 i)
  have hind : iSupIndep (fun i : PositiveRoot H φ => rootSpace H (-i.val)) :=
    (rootSpace_independent H hH.1).comp (fun _ _ he => Subtype.ext (neg_injective he))
  have hlin : LinearIndependent ℂ f := hind.linearIndependent _ hf hf0
  have hlin' : LinearIndependent ℂ b₀ := hlin.of_comp (negative_value H φ).incl.toLinearMap
  have hspan : Submodule.span ℂ (Set.range b₀) = ⊤ := by
    let N := (negative_value H φ).toSubmodule
    change Submodule.span ℂ (Set.range b₀) = (⊤ : Submodule ℂ N)
    apply Submodule.map_injective_of_injective N.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    change Submodule.span ℂ (Set.range f) = (negative_value H φ).toSubmodule
    rw [Submodule.span_range_eq_iSup, negative_submodule]
    simp_rw [← heq]
    change (⨆ i : PositiveRoot H φ, rootSpace H (-i.val)) =
      ⨆ i : {α : Module.Dual ℂ H // φ α ∈ Set.Iio 0}, rootSpace H i.val
    apply le_antisymm
    · exact iSup_le fun i => le_iSup_of_le ⟨-i.val, by simpa using neg_neg_of_pos i.property.2⟩ le_rfl
    · refine iSup_le fun i => ?_
      by_cases hi : i.val ∈ rootSet H
      · let a : PositiveRoot H φ := ⟨-i.val, neg_root_mem H hss hH hi,
            by simpa using neg_pos.mpr (show φ i.val < 0 from i.property)⟩
        exact le_iSup_of_le a (by simp [a])
      · have hi₀ : i.val ≠ 0 := by
          intro h
          have hlt : φ i.val < 0 := i.property
          simp [h] at hlt
        rw [rootSpace_eq_bot_of_not_mem H _ hi₀ hi]
        exact bot_le
  exact ⟨Module.Basis.mk hlin' hspan.ge, fun i => by simpa [b₀] using hf i⟩

end Negative

private theorem highestVector_mem_weight (lam : Module.Dual ℂ H)
    (hχ : IsWeightCharacter H φ lam χ) :
    highestVector_value H φ χ ∈ weightSpace_value (induced_value H φ χ) H lam := by
  apply (HighestWeight.mem_weightSpace (induced_value H φ χ) H lam _).mpr
  intro h
  let bh : borel_value H φ := LieSubalgebra.inclusion (show H ≤ borel_value H φ from le_sup_left) h
  let b := ι ℂ bh
  have hb : envelopingMap (borel_value H φ).incl b = ι ℂ (h : L) :=
    UniversalEnvelopingAlgebra.lift_ι_apply _ _ _
  rw [induced_lie H φ χ, ← hb, ← tensorClass_eq_smul]
  have ht := VermaModules.tensor_balanced H φ χ 1 b 1
  rw [one_mul, mul_one, hχ.1 h] at ht
  rw [ht]
  let q := (balance H φ χ).mkQ.restrictScalars ℂ
  change q ((1 : U L) ⊗ₜ[ℂ] lam h) = lam h • q ((1 : U L) ⊗ₜ[ℂ] (1 : ℂ))
  rw [← map_smul]
  exact congrArg q (by simpa using TensorProduct.tmul_smul (R := ℂ) (lam h) (1 : U L) (1 : ℂ))

private def wordRoot (l : List (PositiveRoot H φ)) : Module.Dual ℂ H :=
  (l.map Subtype.val).sum

@[simp] private theorem wordRoot_nil : wordRoot H φ [] = 0 := rfl

@[simp] private theorem wordRoot_cons (i : PositiveRoot H φ) (l : List (PositiveRoot H φ)) :
    wordRoot H φ (i :: l) = i.val + wordRoot H φ l := rfl

private theorem wordRoot_append (l k : List (PositiveRoot H φ)) :
    wordRoot H φ (l ++ k) = wordRoot H φ l + wordRoot H φ k := by
  simp only [wordRoot, List.map_append, List.sum_append]

private theorem monomial_mem_weight (lam : Module.Dual ℂ H)
    (hχ : IsWeightCharacter H φ lam χ)
    (b : Module.Basis (PositiveRoot H φ) ℂ (negative_value H φ))
    (hb : ∀ i, (b i : L) ∈ rootSpace H (-i.val)) (l : List (PositiveRoot H φ)) :
    envelopingMap (negative_value H φ).incl (monomial b l) • highestVector_value H φ χ ∈
      weightSpace_value (induced_value H φ χ) H (lam - wordRoot H φ l) := by
  induction l with
  | nil => simpa [monomial, Shared.Lie.word] using highestVector_mem_weight H φ χ lam hχ
  | cons i l ih =>
    have he : monomial b (i :: l) = ι ℂ (b i) * monomial b l := rfl
    have hi : envelopingMap (negative_value H φ).incl (ι ℂ (b i)) = ι ℂ (b i : L) :=
      UniversalEnvelopingAlgebra.lift_ι_apply _ _ _
    rw [he, map_mul, mul_smul, hi, ← induced_lie H φ χ]
    have hm := HighestWeight.root_action (induced_value H φ χ) H (-i.val)
      (lam - wordRoot H φ l) (b i : L) _ (hb i) ih
    convert hm using 2
    rw [wordRoot_cons]
    abel

private theorem exists_word_of_mem_cone {a : Module.Dual ℂ H} (ha : a ∈ Qplus H φ) :
    ∃ l : List (PositiveRoot H φ), wordRoot H φ l = a := by
  refine Submodule.span_induction (p := fun x _ => ∃ l, wordRoot H φ l = x) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩
    exact ⟨[⟨i.val, i.property.1⟩], by simp⟩
  · exact ⟨[], rfl⟩
  · rintro _ _ _ _ ⟨l, hl⟩ ⟨k, hk⟩
    exact ⟨l ++ k, by simp only [wordRoot_append, hl, hk]⟩
  · rintro n x _ ⟨l, hl⟩
    induction n with
    | zero => exact ⟨[], by simp⟩
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k ++ l, by simp only [wordRoot_append, hk, hl, succ_nsmul]⟩

private theorem wordRoot_mem_cone [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] (hss : IsSemisimple_value ℂ L) (l : List (PositiveRoot H φ)) :
    wordRoot H φ l ∈ Qplus H φ := by
  induction l with
  | nil => exact (Qplus H φ).zero_mem
  | cons a l ih => exact (Qplus H φ).add_mem (positiveRoot_mem_cone H φ hss a) ih

private theorem length_mul_le_wordRoot (δ : ℝ) (hδ : ∀ i : PositiveRoot H φ, δ ≤ φ i.val)
    (l : List (PositiveRoot H φ)) : (l.length : ℝ) * δ ≤ φ (wordRoot H φ l) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, wordRoot_cons, map_add]
    linarith [hδ i]

section FiniteFibre

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

private theorem exists_positive_root_lower_bound (hss : IsSemisimple_value ℂ L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i : PositiveRoot H φ, δ ≤ φ i.val := by
  by_cases hp : (positive H φ).Nonempty
  · obtain ⟨α, hα, hmin⟩ := Set.exists_min_image _ φ (positiveRoots_finite H φ hss) hp
    exact ⟨φ α, hα.2, fun i => hmin i.val i.property⟩
  · exact ⟨1, zero_lt_one, fun i => (hp ⟨i.val, i.property⟩).elim⟩

private theorem finite_wordRoot_fibre (hss : IsSemisimple_value ℂ L) [LinearOrder (PositiveRoot H φ)]
    (a : Module.Dual ℂ H) : {l : OrderedWord (PositiveRoot H φ) | wordRoot H φ l.val = a}.Finite := by
  -- A positive lower bound on root values bounds the length of every word in the fibre.
  let _ : Finite (PositiveRoot H φ) := (positiveRoots_finite H φ hss).to_subtype
  obtain ⟨δ, hδ, hmin⟩ := exists_positive_root_lower_bound H φ hss
  obtain ⟨n, hn⟩ := exists_nat_gt (φ a / δ)
  apply ((List.finite_length_le (PositiveRoot H φ) n).preimage
    (Subtype.val_injective : Function.Injective (Subtype.val : OrderedWord _ → _)).injOn).subset
  intro l hl
  have hle := length_mul_le_wordRoot H φ δ hmin l.val
  change wordRoot H φ l.val = a at hl
  rw [hl] at hle
  have hlt := lt_of_le_of_lt hle ((div_lt_iff₀ hδ).mp hn)
  exact Nat.le_of_lt (by exact_mod_cast (lt_of_mul_lt_mul_right hlt hδ.le))

end FiniteFibre

private theorem weightSpace_independent [H.IsCartanSubalgebra] :
    iSupIndep (weightSpace_value (induced_value H φ χ) H) := by
  have hind := (LieSubmodule.iSupIndep_toSubmodule.mpr
    (LieModule.iSupIndep_genWeightSpace ℂ H (induced_value H φ χ))).comp
      (show Function.Injective (fun a : Module.Dual ℂ H => (a : H → ℂ)) from DFunLike.coe_injective)
  exact hind.mono (fun a => LieModule.weightSpace_le_genWeightSpace (induced_value H φ χ) a)

theorem verma_weights : verma_weights_type.{u} := by
  classical
  intro L _ _ _ hss H _ φ hφ lam χ hχ
  obtain ⟨b, hb⟩ := exists_negative_basis H φ hss
  let _ : LinearOrder (PositiveRoot H φ) := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨E, hE, _⟩ := VermaModules.induced_free hss H φ hφ χ
  let B := (orderedBasis b).map E
  let W := weightSpace_value (induced_value H φ χ) H
  let fibre (μ : Module.Dual ℂ H) : Set (OrderedWord (PositiveRoot H φ)) :=
    {l | wordRoot H φ l.val = lam - μ}
  let S (μ : Module.Dual ℂ H) := Submodule.span ℂ (B '' fibre μ)
  have hB (l : OrderedWord (PositiveRoot H φ)) : B l ∈ W (lam - wordRoot H φ l.val) := by
    simpa only [B, W, Module.Basis.map_apply, orderedBasis_apply, orderedMonomial, hE] using
      monomial_mem_weight H φ χ lam hχ b hb l.val
  have hS : S ≤ W := by
    intro μ
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    change wordRoot H φ l.val = lam - μ at hl
    change B l ∈ W μ
    simpa only [hl, sub_sub_cancel] using hB l
  have htop : iSup S = ⊤ := by
    apply top_unique
    rw [← B.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    apply Submodule.mem_iSup_of_mem (lam - wordRoot H φ l.val)
    exact Submodule.subset_span ⟨l, by simp [fibre], rfl⟩
  have hind := weightSpace_independent H φ χ
  -- The fibre spans exhaust the module inside independent simultaneous eigenspaces.
  have hSW : S = W := (hind.le_iff_eq_of_iSup_eq_top htop).mp hS
  change DirectSum.IsInternal W ∧ (∀ μ, FiniteDimensional ℂ (W μ)) ∧
    (∀ μ, W μ ≠ ⊥ ↔ lam - μ ∈ Qplus H φ) ∧ W lam = ℂ ∙ highestVector_value H φ χ
  refine ⟨(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨hind, hSW ▸ htop⟩, ?_, ?_, ?_⟩
  · intro μ
    rw [← hSW]
    exact FiniteDimensional.span_of_finite ℂ ((finite_wordRoot_fibre H φ hss (lam - μ)).image B)
  · intro μ
    rw [← hSW]
    constructor
    · intro h
      by_contra hn
      apply h
      apply Submodule.span_eq_bot.mpr
      rintro _ ⟨l, hl, rfl⟩
      exact (hn (hl ▸ wordRoot_mem_cone H φ hss l.val)).elim
    · intro h
      obtain ⟨l, hl⟩ := exists_word_of_mem_cone H φ h
      let s : OrderedWord (PositiveRoot H φ) := ⟨l.mergeSort (· ≤ ·), List.pairwise_mergeSort' _ _⟩
      have hs : s ∈ fibre μ := by
        change wordRoot H φ (l.mergeSort (· ≤ ·)) = lam - μ
        exact (((List.mergeSort_perm l (· ≤ ·)).map Subtype.val).sum_eq).trans hl
      exact fun he => B.ne_zero s ((Submodule.span_eq_bot.mp he) _ ⟨s, hs, rfl⟩)
  · rw [← hSW]
    have hf : fibre lam = {emptyWord (PositiveRoot H φ)} := by
      ext l
      constructor
      · intro hl
        change wordRoot H φ l.val = lam - lam at hl
        apply Set.mem_singleton_iff.mpr
        apply Subtype.ext
        cases hlist : l.val with
        | nil => rfl
        | cons i k =>
          obtain ⟨δ, hδ, hmin⟩ := exists_positive_root_lower_bound H φ hss
          have hle := length_mul_le_wordRoot H φ δ hmin l.val
          rw [hl, sub_self, map_zero, hlist] at hle
          have hpos : (0 : ℝ) < ((i :: k).length : ℝ) := by
            exact_mod_cast (show 0 < (i :: k).length by simp)
          exact (not_le.mpr (mul_pos hpos hδ) hle).elim
      · rintro (rfl : l = _)
        simp [fibre, emptyWord]
    change Submodule.span ℂ (B '' fibre lam) = _
    rw [hf, Set.image_singleton]
    have hB₀ : B (emptyWord (PositiveRoot H φ)) = highestVector_value H φ χ := by
      simp [B, hE, orderedMonomial, monomial, Shared.Lie.word, emptyWord]
    rw [hB₀]

end Weights

end LieAlgebrasAndRepresentations.VermaWeightsUniversal
