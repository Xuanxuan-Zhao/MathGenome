import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DualCartanProducts
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.TensorDualHom
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.LongestElementRho
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LieAlgebrasAndRepresentations.DualCartanProducts

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.DualCartanProducts
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.HighestWeightData
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
open Specs.LieAlgebrasAndRepresentations.RealRootSpace (Realization E realRoots rootRestriction)
open Module
open scoped Classical TensorProduct

open private weight_independent from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightSubmodules
open private cartan_lattice_comparison_of_realization from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData
open private cone_height weight_in_verma_cone finite_weight_decomposition
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open private direction_vector simple_equiv vector_regular
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open private exists_normalized raising_of_normalized
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightClassification

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {H : LieSubalgebra ℂ L} {φ : Direction H}

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ
local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

section WeightBasis

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
variable {ι : Type w} (b : Basis ι ℂ V) (wt : ι → Module.Dual ℂ H)
variable (hb : ∀ i, b i ∈ weightSpace_value V H (wt i))

include hb in
private theorem repr_lie (h : H) (x : V) (i : ι) :
    b.repr ⁅(h : L), x⁆ i = wt i h * b.repr x i := by
  let c := b.coord i
  have heq : c.comp (LieModule.toEnd ℂ L V h) = (wt i h) • c := by
    apply b.ext
    intro j
    change c ⁅(h : L), b j⁆ = wt i h • c (b j)
    rw [(HighestWeight.mem_weightSpace V H (wt j) (b j)).mp (hb j) h, map_smul]
    by_cases hij : j = i
    · subst j
      rfl
    · simp only [c, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hij), smul_zero]
  exact LinearMap.congr_fun heq x

include hb in
private theorem weight_eq_span (ν : Module.Dual ℂ H) :
    weightSpace_value V H ν = Submodule.span ℂ (b '' {i | wt i = ν}) := by
  apply le_antisymm
  · intro x hx
    apply (b.mem_span_image).mpr
    intro i hi
    have hne : b.repr x i ≠ 0 := Finsupp.mem_support_iff.mp hi
    change wt i = ν
    ext h
    have he := congrArg (fun x => b.repr x i)
      ((HighestWeight.mem_weightSpace V H ν x).mp hx h)
    rw [repr_lie b wt hb, map_smul, Finsupp.smul_apply, smul_eq_mul] at he
    exact mul_right_cancel₀ hne he
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact (show wt i = ν from hi) ▸ hb i

private theorem exists_weight_basis [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
    [FiniteDimensional ℂ V] (hss : IsSemisimple_value ℂ L) :
    ∃ (ι : Type u) (b : Basis ι ℂ V) (wt : ι → Module.Dual ℂ H),
      ∀ i, b i ∈ weightSpace_value V H (wt i) := by
  let bν := fun ν : Module.Dual ℂ H => Module.finBasis ℂ (weightSpace_value V H ν)
  let h := finite_weight_decomposition H hss V
  exact ⟨_, h.collectedBasis bν, Sigma.fst, h.collectedBasis_mem bν⟩

end WeightBasis

section Tensor

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]

private theorem tmul_weight {ν η : Module.Dual ℂ H} {x : V} {y : W}
    (hx : x ∈ weightSpace_value V H ν) (hy : y ∈ weightSpace_value W H η) :
    x ⊗ₜ[ℂ] y ∈ weightSpace_value (V ⊗[ℂ] W) H (ν + η) := by
  apply (HighestWeight.mem_weightSpace _ _ _ _).mpr
  intro h
  rw [TensorProduct.LieModule.lie_tmul_right, (HighestWeight.mem_weightSpace V H ν x).mp hx h,
    (HighestWeight.mem_weightSpace W H η y).mp hy h,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul]
  rfl

private structure TopWeight (H : LieSubalgebra ℂ L) (φ : Direction H)
    (ν : Module.Dual ℂ H) (x : V) : Prop where
  nonzero : x ≠ 0
  weight : x ∈ weightSpace_value V H ν
  killed : ∀ z : positive_value H φ, ⁅(z : L), x⁆ = 0
  line : weightSpace_value V H ν = ℂ ∙ x
  maximal (η : Module.Dual ℂ H) : weightSpace_value V H η ≠ ⊥ →
    φ η ≤ φ ν ∧ (φ η = φ ν → η = ν)

private theorem tensor_top [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (hss : IsSemisimple_value ℂ L)
    {ν η : Module.Dual ℂ H} {x : V} {y : W}
    (hx : TopWeight H φ ν x) (hy : TopWeight H φ η y) :
    TopWeight H φ (ν + η) (x ⊗ₜ[ℂ] y) := by
  obtain ⟨ι, b, B, hb⟩ := exists_weight_basis (H := H) (V := V) hss
  obtain ⟨κ, c, C, hc⟩ := exists_weight_basis (H := H) (V := W) hss
  let d := b.tensorProduct c
  let D : ι × κ → Module.Dual ℂ H := fun i => B i.1 + C i.2
  have hd (i : ι × κ) : d i ∈ weightSpace_value (V ⊗[ℂ] W) H (D i) := by
    rw [show d i = b i.1 ⊗ₜ[ℂ] c i.2 from Basis.tensorProduct_apply' b c i]
    exact tmul_weight (hb i.1) (hc i.2)
  have hB (i : ι) := hx.maximal (B i)
    (fun h => b.ne_zero i (by simpa [h] using hb i))
  have hC (j : κ) := hy.maximal (C j)
    (fun h => c.ne_zero j (by simpa [h] using hc j))
  have hD (i : ι × κ) : φ (D i) ≤ φ (ν + η) ∧
      (φ (D i) = φ (ν + η) → B i.1 = ν ∧ C i.2 = η) := by
    dsimp [D]
    simp only [map_add]
    refine ⟨add_le_add (hB i.1).1 (hC i.2).1, fun h => ⟨?_, ?_⟩⟩
    · exact (hB i.1).2 (by linarith only [(hC i.2).1, (hB i.1).1, h])
    · exact (hC i.2).2 (by linarith only [(hC i.2).1, (hB i.1).1, h])
  have hxy := tmul_weight hx.weight hy.weight
  refine ⟨?_, hxy, ?_, le_antisymm ?_ (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxy)), ?_⟩
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr (show b.repr x ≠ 0 by simpa using hx.nonzero)
    obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr (show c.repr y ≠ 0 by simpa using hy.nonzero)
    intro hz
    have he := Basis.tensorProduct_repr_tmul_apply b c x y i j
    rw [hz, map_zero, Finsupp.zero_apply] at he
    exact (smul_ne_zero (Finsupp.mem_support_iff.mp hj) (Finsupp.mem_support_iff.mp hi)) he.symm
  · intro z
    rw [TensorProduct.LieModule.lie_tmul_right, hx.killed z, hy.killed z,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  · rw [weight_eq_span d D hd]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨hi₁, hi₂⟩ := (hD i).2 (congrArg φ hi)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hx.line ▸ hi₁ ▸ hb i.1)
    obtain ⟨b', hb'⟩ := Submodule.mem_span_singleton.mp (hy.line ▸ hi₂ ▸ hc i.2)
    rw [show d i = b i.1 ⊗ₜ[ℂ] c i.2 from Basis.tensorProduct_apply' b c i, ← ha, ← hb',
      TensorProduct.smul_tmul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro ζ hζ
    rw [weight_eq_span d D hd] at hζ
    obtain ⟨i, hi⟩ : ∃ i, D i = ζ := by
      by_contra! h
      have he : ({i | D i = ζ} : Set (ι × κ)) = ∅ := Set.eq_empty_iff_forall_notMem.mpr h
      simp [he] at hζ
    refine ⟨hi ▸ (hD i).1, fun h => ?_⟩
    obtain ⟨h₁, h₂⟩ := (hD i).2 (hi.symm ▸ h)
    rw [← hi]
    exact congrArg₂ (· + ·) h₁ h₂

end Tensor

section Simple

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
variable (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
variable {lam : Module.Dual ℂ H} {χ : U (borel_value H φ) →ₐ[ℂ] ℂ}
variable (hχ : IsWeightCharacter H φ lam χ)

include hss hφ hχ in
private theorem quotient_top :
    TopWeight H φ lam (quotientHighestVector H φ χ) := by
  let V := simpleQuotient_value H φ χ
  let M := induced_value H φ χ
  let p := quotientMap H φ χ
  let x := quotientHighestVector H φ χ
  obtain ⟨e, f, hef⟩ := exists_normalized hss H φ
  have he := raising_of_normalized H φ hef
  have hhw := (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e he).2
  have hpos := (SimpleHighestWeightQuotient.highest_weight_iff_positive
    hss H φ e he V lam x).mp hhw
  have hs : Function.Surjective p := LieSubmodule.Quotient.surjective_mk' _
  have hi := (VermaWeightsUniversal.verma_weights hss H φ hφ lam χ hχ).1
  let F : M →ₗ[ℂ] V := p.toLinearMap
  let A := weightSpace_value M H
  let B := weightSpace_value V H
  letI : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  have hind : iSupIndep B := weight_independent
  have hmaps : (fun a => (A a).map F) ≤ B := by
    intro a
    rintro _ ⟨m, hm, rfl⟩
    apply (HighestWeight.mem_weightSpace V H a (p m)).mpr
    intro h
    rw [← p.map_lie, (HighestWeight.mem_weightSpace M H a m).mp hm h, map_smul]
  have hspan : (⨆ a, (A a).map F) = ⊤ := by
    rw [← Submodule.map_iSup, hi.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hs
  have hline : B lam = ℂ ∙ x := by
    rw [← congrFun ((hind.le_iff_eq_of_iSup_eq_top hspan).mp hmaps) lam]
    rw [show A lam = ℂ ∙ highestVector_value H φ χ from
      (VermaWeightsUniversal.verma_weights hss H φ hφ lam χ hχ).2.2.2,
      Submodule.map_span, Set.image_singleton]
    rfl
  refine ⟨hpos.1, (HighestWeight.mem_weightSpace _ _ _ _).mpr hpos.2.1, hpos.2.2.1, hline, ?_⟩
  intro μ hμ
  obtain ⟨v, hv, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  have hd := cone_height H φ (weight_in_verma_cone H φ χ hss hφ lam hχ p hs μ v hv hv₀)
  exact ⟨sub_nonneg.mp (by simpa only [map_sub] using hd.1), fun h =>
    (sub_eq_zero.mp (hd.2 (by simp [map_sub, h]))).symm⟩

private theorem range_eq_lieSpan
    {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
    (p : V →ₗ⁅ℂ,L⁆ W) (x : V) (hx : LieSubmodule.lieSpan ℂ L ({x} : Set V) = ⊤) :
    p.range = LieSubmodule.lieSpan ℂ L ({p x} : Set W) := by
  apply le_antisymm
  · rw [← LieModuleHom.map_top, LieSubmodule.map_le_iff_le_comap, ← hx, LieSubmodule.lieSpan_le]
    exact Set.singleton_subset_iff.mpr (LieSubmodule.subset_lieSpan rfl)
  · exact LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr ⟨x, rfl⟩)

include hss hφ hχ in
private theorem cyclic_equiv
    {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] {x : V} (hx : x ≠ 0) (hw : x ∈ weightSpace_value V H lam)
    (hk : ∀ z : positive_value H φ, ⁅(z : L), x⁆ = 0) :
    let K := LieSubmodule.lieSpan ℂ L ({x} : Set V)
    ∃ i : simpleQuotient_value H φ χ ≃ₗ⁅ℂ,L⁆ K,
      (i (quotientHighestVector H φ χ) : V) = x := by
  let K := LieSubmodule.lieSpan ℂ L ({x} : Set V)
  let y : K := ⟨x, LieSubmodule.subset_lieSpan rfl⟩
  have hy : LieSubmodule.lieSpan ℂ L ({y} : Set K) = ⊤ := by
    let J := LieSubmodule.lieSpan ℂ L ({y} : Set K)
    have he : J.map K.incl = K := by
      apply le_antisymm
      · rintro _ ⟨z, _, rfl⟩
        exact z.property
      · exact LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr
          ⟨y, LieSubmodule.subset_lieSpan rfl, rfl⟩)
    apply LieSubmodule.map_injective_of_injective K.injective_incl
    simpa only [LieSubmodule.map_incl_top] using he
  have hy₀ : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have hwy (h : H) : ⁅(h : L), y⁆ = lam h • y :=
    Subtype.ext ((HighestWeight.mem_weightSpace V H lam x).mp hw h)
  have hky (z : positive_value H φ) : ⁅(z : L), y⁆ = 0 := Subtype.ext (hk z)
  obtain ⟨e, f, hef⟩ := exists_normalized hss H φ
  have he := raising_of_normalized H φ hef
  obtain ⟨hdom, hpows⟩ := DominanceNecessary.highest_weight_dominant hss H φ hφ e f hef K lam y
    ⟨hy₀, hwy, hky, hy⟩
  have hhigh := (SimpleHighestWeightQuotient.highest_weight_iff_positive hss H φ e he K lam y).mpr
    ⟨hy₀, hwy, hky, hy⟩
  have hp (i : simple H φ) :
      (LieModule.toEnd ℂ L K (f i) ^ (simpleCoordinate H φ hdom i + 1)) y = 0 := by
    obtain ⟨n, hn, hp⟩ := hpows i
    have hni : simpleCoordinate H φ hdom i = n := by
      exact_mod_cast (Classical.choose_spec (hdom i)).symm.trans hn
    rwa [hni]
  obtain ⟨p, hpy, _⟩ :=
    (HighestWeightClassification.defining_relations hss H φ hφ lam χ hχ hdom e f hef).2.2
      K y hwy hhigh.2.2.1 hp
  have hr := range_eq_lieSpan p (quotientHighestVector H φ χ)
    (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e he).2.2.2.2
  have hsur : Function.Surjective p := (LieModuleHom.range_eq_top p).mp (by rw [hr, hpy, hy])
  letI := (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e he).1
  have hinj : Function.Injective p := by
    apply (LieModuleHom.ker_eq_bot p).mp
    rcases eq_bot_or_eq_top p.ker with hb | ht
    · exact hb
    · exact (hy₀ (hpy ▸ LieModuleHom.mem_ker.mp (ht ▸ LieSubmodule.mem_top _))).elim
  exact ⟨{ LinearEquiv.ofBijective p.toLinearMap ⟨hinj, hsur⟩ with
    map_lie' := fun {x m} => p.map_lie x m }, congrArg Subtype.val hpy⟩

end Simple

theorem cartan_product : cartan_product_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam mu χ ψ hχ hψ hlam hmu
  letI : FiniteDimensional ℂ (simpleQuotient_value H φ χ) :=
    ((HighestWeightClassification.finite_simple_iff_dominant hss H φ hφ lam χ hχ).mpr hlam).1
  letI : FiniteDimensional ℂ (simpleQuotient_value H φ ψ) :=
    ((HighestWeightClassification.finite_simple_iff_dominant hss H φ hφ mu ψ hψ).mpr hmu).1
  obtain ⟨ξ, hξ, _⟩ := VermaModules.character_existsUnique hss H φ hφ (lam + mu)
  let V := simpleQuotient_value H φ χ ⊗[ℂ] simpleQuotient_value H φ ψ
  let x : V := quotientHighestVector H φ χ ⊗ₜ[ℂ] quotientHighestVector H φ ψ
  let K := LieSubmodule.lieSpan ℂ L ({x} : Set V)
  have ht : TopWeight H φ (lam + mu) x :=
    tensor_top hss (quotient_top hss hφ hχ) (quotient_top hss hφ hψ)
  obtain ⟨i, hi⟩ := cyclic_equiv hss hφ hξ ht.nonzero ht.weight ht.killed
  refine ⟨ξ, hξ, ht.nonzero, ht.line, ⟨i, hi⟩, fun J => ⟨?_, ?_⟩⟩
  · rintro ⟨j⟩
    obtain ⟨e, f, hef⟩ := exists_normalized hss H φ
    have hh := (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ _ ξ hξ e
      (raising_of_normalized H φ hef)).2
    let p := J.incl.comp j.toLieModuleHom
    let y := p (quotientHighestVector H φ ξ)
    have hy : y ≠ 0 := fun h =>
      hh.1 ((J.injective_incl.comp j.injective) (h.trans (map_zero p).symm))
    have hweight : y ∈ weightSpace_value V H (lam + mu) := by
      apply (HighestWeight.mem_weightSpace _ _ _ _).mpr
      intro a
      change ⁅(a : L), p _⁆ = (lam + mu) a • p _
      rw [← p.map_lie, hh.2.1, map_smul]
    have hrange : p.range = J := by
      ext z
      constructor
      · rintro ⟨s, rfl⟩
        exact (j s).property
      · intro hz
        obtain ⟨s, hs⟩ := j.surjective ⟨z, hz⟩
        exact ⟨s, congrArg Subtype.val hs⟩
    rw [ht.line] at hweight
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hweight
    have hc₀ : c ≠ 0 := fun h => hy (by simpa [h] using hc.symm)
    rw [← hrange, range_eq_lieSpan p _ hh.2.2.2]
    change LieSubmodule.lieSpan ℂ L ({y} : Set V) = K
    apply le_antisymm
    · apply LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr _)
      rw [← hc]
      exact K.smul_mem _ (LieSubmodule.subset_lieSpan rfl)
    · apply LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr _)
      have heq : x = c⁻¹ • y := by rw [← hc, smul_smul, inv_mul_cancel₀ hc₀, one_smul]
      rw [heq]
      exact (LieSubmodule.lieSpan ℂ L ({y} : Set V)).smul_mem _ (LieSubmodule.subset_lieSpan rfl)
  · rintro rfl
    exact ⟨i⟩

section Longest

open RealRootSpace

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

private theorem exists_longest (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ) :
    ∃ w : weightWeylGroup H, IsLongest H φ w := by
  let d := RealRootSpace.realization hss H
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  letI : Fact (Realization H) := ⟨d⟩
  obtain ⟨dir, hdir⟩ := direction_vector d φ
  have hreg := vector_regular d φ hdir hφ
  obtain ⟨w, hw, _⟩ := longest_weyl_exists_unique (realRoots H) d.root_system dir hreg
  obtain ⟨_, e, he⟩ := FiniteModuleWeights.weyl_complexification H d
  let P := LieAlgebrasAndRepresentations.positiveRoots (realRoots H) dir
  have hpos : d.j '' P = SerreRelations.positive H φ := by
    ext α
    constructor
    · rintro ⟨_, ⟨⟨β, hβ, rfl⟩, hb⟩, rfl⟩
      exact ⟨by simpa only [d.extension_root β hβ] using hβ, (hdir _).trans_gt hb⟩
    · rintro ⟨hα, ha⟩
      refine ⟨rootRestriction H α, ⟨⟨α, hα, rfl⟩, ?_⟩, d.extension_root α hα⟩
      rw [← hdir, d.extension_root α hα]
      exact ha
  refine ⟨e w, ?_⟩
  change (e w).val '' SerreRelations.positive H φ = Neg.neg '' _
  rw [← hpos]
  calc
    (e w).val '' (d.j '' P) = d.j '' (w.val '' P) := by
      simp only [Set.image_image, he w]
    _ = d.j '' (Neg.neg '' P) := by rw [show w.val '' P = Neg.neg '' P from hw]
    _ = Neg.neg '' (d.j '' P) := by
      simp only [Set.image_image, map_neg]

end Longest

section Dual

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

private theorem dual_action (a : L) (f : Module.Dual ℂ V) (x : V) :
    ⁅a, f⁆ x = -f ⁅a, x⁆ :=
  (TensorDualHom.actions_spec ℂ L V V).2.1 a f x

private theorem dual_simple [FiniteDimensional ℂ V]
    [IsSimpleOrder (LieSubmodule ℂ L V)] :
    IsSimpleOrder (LieSubmodule ℂ L (Module.Dual ℂ V)) := by
  haveI : Nontrivial V := (LieSubmodule.nontrivial_iff ℂ L V).mp inferInstance
  refine ⟨fun J => ?_⟩
  let A : LieSubmodule ℂ L V :=
    { J.toSubmodule.dualCoannihilator with
      lie_mem := by
        intro a v hv
        apply (Submodule.mem_dualCoannihilator _).mpr
        intro f hf
        have he := (Submodule.mem_dualCoannihilator v).mp hv ⁅a, f⁆ (J.lie_mem hf)
        rw [dual_action, neg_eq_zero] at he
        exact he }
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq J.toSubmodule
  change finrank ℂ J + finrank ℂ A = finrank ℂ V at hdim
  rcases eq_bot_or_eq_top A with h | h
  · right
    have hJ : finrank ℂ J.toSubmodule = finrank ℂ (Module.Dual ℂ V) := by
      rw [Subspace.dual_finrank_eq]
      have hzero : finrank ℂ A = 0 := by rw [h]; exact finrank_bot ℂ V
      rwa [hzero, add_zero] at hdim
    exact LieSubmodule.toSubmodule_injective (Submodule.eq_top_of_finrank_eq hJ)
  · left
    have hA : ∀ v : V, v ∈ A := fun v => h ▸ LieSubmodule.mem_top v
    apply (LieSubmodule.eq_bot_iff J).mpr
    intro f hf
    ext v
    exact (Submodule.mem_dualCoannihilator v).mp (hA v) f hf

private theorem dual_weight_iff {ι : Type w} (b : Basis ι ℂ V)
    (wt : ι → Module.Dual ℂ H) (hb : ∀ i, b i ∈ weightSpace_value V H (wt i))
    (ν : Module.Dual ℂ H) :
    weightSpace_value (Module.Dual ℂ V) H (-ν) ≠ ⊥ ↔ weightSpace_value V H ν ≠ ⊥ := by
  constructor
  · intro h
    obtain ⟨f, hf, hf₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨i, hi⟩ : ∃ i, f (b i) ≠ 0 := by
      by_contra! he
      exact hf₀ (b.ext fun i => he i)
    have hν : wt i = ν := by
      ext a
      have he := congrArg (fun g : Module.Dual ℂ V => g (b i))
        ((HighestWeight.mem_weightSpace _ _ _ _).mp hf a)
      change ⁅(a : L), f⁆ (b i) = -ν a * f (b i) at he
      rw [dual_action, (HighestWeight.mem_weightSpace V H (wt i) (b i)).mp (hb i) a,
        map_smul, smul_eq_mul, ← neg_mul] at he
      exact neg_injective (mul_right_cancel₀ hi he)
    intro hz
    exact b.ne_zero i (by simpa [hν, hz] using hb i)
  · intro h
    rw [weight_eq_span b wt hb] at h
    obtain ⟨i, hi⟩ : ∃ i, wt i = ν := by
      by_contra! he
      have hem : ({i | wt i = ν} : Set ι) = ∅ := Set.eq_empty_iff_forall_notMem.mpr he
      simp [hem] at h
    have hw : b.coord i ∈ weightSpace_value (Module.Dual ℂ V) H (-ν) := by
      apply (HighestWeight.mem_weightSpace _ _ _ _).mpr
      intro a
      ext x
      rw [dual_action]
      change -b.repr ⁅(a : L), x⁆ i = -ν a * b.repr x i
      rw [repr_lie b wt hb, hi, neg_mul]
    intro hz
    have he : b.coord i = 0 := by simpa only [hz, Submodule.mem_bot] using hw
    have hh := congrArg (fun f : Module.Dual ℂ V => f (b i)) he
    simpa using hh

end Dual

theorem dual_highest_weight : dual_highest_weight_type.{u} := by
  intro L _ _ _ hss H _ φ hφ
  refine ⟨exists_longest hss hφ, ?_⟩
  intro w hw lam χ hχ hlam
  let V := simpleQuotient_value H φ χ
  obtain ⟨hfin, hsimp⟩ :=
    (HighestWeightClassification.finite_simple_iff_dominant hss H φ hφ lam χ hχ).mpr hlam
  letI : FiniteDimensional ℂ V := hfin
  letI : IsSimpleOrder (LieSubmodule ℂ L V) := hsimp
  letI : IsSimpleOrder (LieSubmodule ℂ L (Module.Dual ℂ V)) := dual_simple
  obtain ⟨ι, b, wt, hb⟩ := exists_weight_basis (H := H) (V := V) hss
  have hD := dual_weight_iff b wt hb
  have hW (g : weightWeylGroup H) (ν : Module.Dual ℂ H) :
      weightSpace_value V H (g.val ν) ≠ ⊥ ↔ weightSpace_value V H ν ≠ ⊥ := by
    have he (μ : Module.Dual ℂ H) : weightSpace_value V H μ =
        RepresentationJordan.weightSpace (LieModule.toEnd ℂ L V) H μ := by
      ext x
      rw [HighestWeight.mem_weightSpace V H μ x, FiniteModuleWeights.mem_weightSpace]
      rfl
    simp only [ne_eq, ← Submodule.finrank_eq_zero, he]
    rw [WeightStringsConvexity.multiplicities hss (LieModule.toEnd ℂ L V) H
      (RealRootSpace.cartan_isMaximalToral hss H) g ν]
  have hrev (x : Module.Dual ℂ H)
      (hx : x ∈ positiveRootCone_value (fun i : simple H φ => i.val)) :
      φ (w.val x) ≤ 0 ∧ (φ (w.val x) = 0 → x = 0) := by
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      obtain ⟨α, hα, he⟩ : w.val i.val ∈ Neg.neg '' SerreRelations.positive H φ :=
        hw ▸ Set.mem_image_of_mem w.val i.property.1
      have hh : φ (w.val i.val) < 0 := by rw [← he, map_neg]; exact neg_neg_of_pos hα.2
      exact ⟨hh.le, fun h => (hh.ne h).elim⟩
    · intro x y _ _ hx hy
      simp only [map_add]
      exact ⟨add_nonpos hx.1 hy.1, fun h => by rw [hx.2 (by linarith [hy.1]),
        hy.2 (by linarith [hx.1]), add_zero]⟩
    · intro n x _ hx
      cases n with
      | zero => simp
      | succ n =>
        rw [map_nsmul, map_nsmul, nsmul_eq_mul]
        refine ⟨mul_nonpos_of_nonneg_of_nonpos (by positivity) hx.1, fun h => ?_⟩
        rw [hx.2 ((mul_eq_zero.mp h).resolve_left (by positivity)), smul_zero]
  have hmin (μ : Module.Dual ℂ H) (hμ : weightSpace_value V H μ ≠ ⊥) :
      φ (w.val lam) ≤ φ μ ∧ (φ (w.val lam) = φ μ → w.val lam = μ) := by
    have h := (hW w⁻¹ μ).mpr hμ
    obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hp := weight_in_verma_cone H φ χ hss hφ lam hχ (quotientMap H φ χ)
      (LieSubmodule.Quotient.surjective_mk' _) _ x hx hx₀
    have he : w.val (lam - (w⁻¹).val μ) = w.val lam - μ := by
      rw [map_sub]
      exact congrArg (w.val lam - ·) (w.val.apply_symm_apply μ)
    obtain ⟨hle, heq⟩ := hrev _ hp
    rw [he, map_sub] at hle heq
    refine ⟨sub_nonpos.mp hle, fun h => sub_eq_zero.mp ?_⟩
    rw [← he, heq (sub_eq_zero.mpr h), map_zero]
  have htop := quotient_top hss hφ hχ
  have hlam_ne : weightSpace_value V H lam ≠ ⊥ :=
    fun h => htop.nonzero ((Submodule.mem_bot ℂ).mp (h ▸ htop.weight))
  have hdual := (hD (w.val lam)).mpr ((hW w lam).mpr hlam_ne)
  obtain ⟨⟨μ, hμ⟩, ⟨ψ, hψ, ⟨j⟩⟩, _⟩ :=
    HighestWeightClassification.finite_simple_classification hss H φ hφ (Module.Dual ℂ V)
  have ht := quotient_top hss hφ (show IsWeightCharacter H φ μ ψ from hψ)
  have hwmap {a : Module.Dual ℂ H}
      (h : weightSpace_value (Module.Dual ℂ V) H a ≠ ⊥) :
      weightSpace_value (simpleQuotient_value H φ ψ) H a ≠ ⊥ := by
    obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hh : j x ∈ weightSpace_value (simpleQuotient_value H φ ψ) H a := by
      apply (HighestWeight.mem_weightSpace _ _ _ _).mpr
      intro h
      change ⁅(h : L), j.toLieModuleHom x⁆ = a h • j.toLieModuleHom x
      rw [← j.toLieModuleHom.map_lie, (HighestWeight.mem_weightSpace _ _ _ _).mp hx h, map_smul]
    intro hz
    exact hx₀ (j.injective (((Submodule.mem_bot ℂ).mp (hz ▸ hh)).trans (map_zero j).symm))
  have hμdual : weightSpace_value (Module.Dual ℂ V) H μ ≠ ⊥ := by
    let x := j.symm (quotientHighestVector H φ ψ)
    have hx : x ∈ weightSpace_value (Module.Dual ℂ V) H μ := by
      apply (HighestWeight.mem_weightSpace _ _ _ _).mpr
      intro a
      change ⁅(a : L), j.symm.toLieModuleHom _⁆ = μ a • j.symm.toLieModuleHom _
      rw [← j.symm.toLieModuleHom.map_lie, (HighestWeight.mem_weightSpace _ _ _ _).mp ht.weight a, map_smul]
    intro hz
    apply ht.nonzero
    apply j.symm.injective
    rw [map_zero]
    exact (Submodule.mem_bot ℂ).mp (hz ▸ hx)
  have hnegμ : weightSpace_value V H (-μ) ≠ ⊥ :=
    (hD (-μ)).mp (by simpa only [neg_neg] using hμdual)
  have h₁ := (ht.maximal (-w.val lam) (hwmap hdual)).1
  have h₂ := (hmin (-μ) hnegμ).1
  rw [map_neg] at h₁ h₂
  have he := (ht.maximal (-w.val lam) (hwmap hdual)).2 (by rw [map_neg]; linarith)
  exact he.symm ▸ ⟨hμ, ψ, hψ, ⟨j⟩⟩

theorem empty_product : empty_product_type.{u,v} := by
  intro L _ _ ι A
  let src := TrivialLieModule.equiv ℂ L (ULift.{u} ℂ)
  let tgt := TrivialLieModule.equiv ℂ L ℂ
  let i := src.trans ((ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℂ] ℂ).trans tgt.symm)
  let e : (ModuleWithVector.tensorList A []).carrier ≃ₗ⁅ℂ,L⁆ TrivialLieModule ℂ L ℂ :=
    { i with
      map_lie' := fun {_ _} => i.map_zero }
  exact ⟨e, rfl⟩

section Fundamental

open RealRootSpace

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

private theorem exists_coroot_basis (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ) :
    ∃ c : Basis (simple H φ) ℂ H, ∀ i, c i = coroots H φ i := by
  let d := RealRootSpace.realization hss H
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  letI : Fact (Realization H) := ⟨d⟩
  obtain ⟨v, hv⟩ := direction_vector d φ
  obtain ⟨s, hs⟩ := simple_equiv d φ hv
  have h := cartan_lattice_comparison_of_realization d v (vector_regular d φ hv hφ) s
  dsimp only at h
  simp only [hs] at h
  obtain ⟨_, c, _, _, hc, _⟩ := h
  exact ⟨c, fun i => (hc i).2.2.1⟩

private theorem exists_list_counts {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ι → ℕ) :
    ∃ l : List ι, ∀ i, l.count i = n i := by
  have h (s : Finset ι) : ∃ l : List ι, ∀ i, l.count i = if i ∈ s then n i else 0 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨[], fun i => by simp⟩
    | @insert a s ha ih =>
      obtain ⟨l, hl⟩ := ih
      refine ⟨List.replicate (n a) a ++ l, fun i => ?_⟩
      by_cases hi : i = a
      · subst i
        simp [hl, ha]
      · simp [hl, List.count_replicate, hi, Ne.symm hi]
  obtain ⟨l, hl⟩ := h Finset.univ
  exact ⟨l, fun i => by simpa using hl i⟩

private theorem sum_coordinates_apply {ι : Type u} [DecidableEq ι] (c : Basis ι ℂ H)
    (l : List ι) (j : ι) : ((l.map c.coord).sum) (c j) = (l.count j : ℂ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases hi : i = j
    · subst i
      simp [ih, add_comm]
    · simp [ih, hi, Ne.symm hi]

private theorem unit_top (H : LieSubalgebra ℂ L) (φ : Direction H) :
    TopWeight H φ 0 (ModuleWithVector.unit L).vector := by
  let T := ModuleWithVector.unit L
  let x := T.vector
  have hx : x ≠ 0 := fun h => one_ne_zero (congrArg ULift.down h)
  have htriv (a : L) (y : T.carrier) : ⁅a, y⁆ = 0 := rfl
  refine ⟨hx, (HighestWeight.mem_weightSpace _ _ _ _).mpr (fun a => by simp [htriv]),
    fun a => htriv a x, ?_, ?_⟩
  · apply le_antisymm
    · intro y _
      exact Submodule.mem_span_singleton.mpr ⟨ULift.down y, ULift.ext (mul_one _)⟩
    · apply Submodule.span_le.mpr
      exact Set.singleton_subset_iff.mpr ((HighestWeight.mem_weightSpace _ _ _ _).mpr
        (fun a => by simp [htriv]))
  · intro ν hν
    obtain ⟨y, hy, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hν
    have he : ν = 0 := by
      ext a
      have h := (HighestWeight.mem_weightSpace _ _ _ _).mp hy a
      rw [htriv] at h
      exact (smul_eq_zero.mp h.symm).resolve_right hy₀
    subst ν
    exact ⟨le_rfl, fun _ => rfl⟩

private theorem tensorList_top {ι : Type u} (A : ι → ModuleWithVector L)
    (wt : ι → Module.Dual ℂ H) (hss : IsSemisimple_value ℂ L)
    (hfin : ∀ i, FiniteDimensional ℂ (A i).carrier)
    (htop : ∀ i, TopWeight H φ (wt i) (A i).vector) (l : List ι) :
    let T := ModuleWithVector.tensorList A l
    FiniteDimensional ℂ T.carrier ∧ TopWeight H φ (l.map wt).sum T.vector := by
  induction l with
  | nil =>
    refine ⟨?_, unit_top H φ⟩
    change FiniteDimensional ℂ (TrivialLieModule ℂ L (ULift.{u} ℂ))
    obtain ⟨e, _⟩ := empty_product A
    exact FiniteDimensional.of_injective
      ((TrivialLieModule.equiv ℂ L ℂ).toLinearMap.comp e.toLinearEquiv.toLinearMap)
      ((TrivialLieModule.equiv ℂ L ℂ).injective.comp e.injective)
  | cons i l ih =>
    let B := ModuleWithVector.tensorList A l
    letI : FiniteDimensional ℂ B.carrier := ih.1
    letI : FiniteDimensional ℂ (A i).carrier := hfin i
    change FiniteDimensional ℂ ((A i).carrier ⊗[ℂ] B.carrier) ∧
      TopWeight H φ (wt i + (l.map wt).sum) ((A i).vector ⊗ₜ[ℂ] B.vector)
    exact ⟨inferInstance, tensor_top hss (htop i) ih.2⟩

end Fundamental

theorem fundamental_products : fundamental_products_type.{u} := by
  classical
  intro L _ _ _ hss H _ φ hφ lam χ hχ hlam
  obtain ⟨c, hc⟩ := exists_coroot_basis hss hφ
  let ω := c.coord
  have hd (i : simple H φ) : IsDominant H φ (ω i) := by
    intro j
    refine ⟨if i = j then 1 else 0, ?_⟩
    rw [← hc j]
    by_cases hij : i = j
    · subst j
      simp [ω]
    · simp [ω, hij]
  have hex (i : simple H φ) :=
    HighestWeightClassification.dominant_has_simple_quotient hss H φ hφ (ω i) (hd i)
  choose ψ hψ hf _ using hex
  letI : Finite (simple H φ) := Module.Finite.finite_basis c
  letI : Fintype (simple H φ) := Fintype.ofFinite (α := simple H φ)
  letI : DecidableEq (simple H φ) := Classical.decEq _
  letI : BEq (simple H φ) := @instBEqOfDecidableEq _ (Classical.decEq _)
  obtain ⟨l, hl⟩ := exists_list_counts (simpleCoordinate H φ hlam)
  have hcount (i : simple H φ) : lam (coroots H φ i) = (l.count i : ℂ) := by
    rw [hl, IntegrableHighestWeightQuotient.simpleCoordinate_eq H φ hlam i]
  have hzero (h : lam = 0) : l = [] := by
    by_contra! hn
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hn
    have hc0' : (l.count i : ℂ) = 0 := by simpa [h] using (hcount i).symm
    have hc0 : l.count i = 0 := by exact_mod_cast hc0'
    exact (List.count_eq_zero.mp hc0) hi
  have hsum : (l.map ω).sum = lam := by
    apply c.ext
    intro j
    exact (sum_coordinates_apply c l j).trans ((hcount j).symm.trans (by rw [hc]))
  let A := fun i => simpleFactor H φ (ψ i)
  let T := ModuleWithVector.tensorList A l
  have htop (i : simple H φ) : TopWeight H φ (ω i) (A i).vector :=
    quotient_top hss hφ (hψ i)
  have hprod := tensorList_top A ω hss hf htop l
  letI : FiniteDimensional ℂ T.carrier := hprod.1
  have htopT : TopWeight H φ lam T.vector := hsum ▸ hprod.2
  obtain ⟨e, he⟩ := cyclic_equiv hss hφ hχ htopT.nonzero htopT.weight htopT.killed
  exact ⟨c, ψ, l, hc, hψ, hcount, hzero, htopT.nonzero, htopT.line, e, he⟩

end LieAlgebrasAndRepresentations.DualCartanProducts
