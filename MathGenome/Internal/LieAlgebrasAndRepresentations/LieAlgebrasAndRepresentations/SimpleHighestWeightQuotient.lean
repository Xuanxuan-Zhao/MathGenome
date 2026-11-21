import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightSubmodules
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RepresentationJordan
import Mathlib.LinearAlgebra.Isomorphisms
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient

open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.HighestWeightData (weightSpace_value positiveRootCone_value)
open VermaWeightsUniversal (verma_universal verma_weights)
open HighestWeight (mem_weightSpace root_action)
open scoped Classical

open private positive_le_of_simple from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules
open private rootSpace_le_of_nonzero from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations
open private weight_independent from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightSubmodules

universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)
  (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)

abbrev maximalSubmodule := @maximalSubmodule_value
abbrev simpleQuotient := @simpleQuotient_value

local instance : LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ
local instance : LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

local notation "M" => induced_value H φ χ
local notation "v₀" => highestVector_value H φ χ
local notation "J" => maximalSubmodule_value H φ χ
local notation "q" => quotientMap H φ χ
local notation "Q" => simpleQuotient_value H φ χ

theorem highest_weight_iff_positive : highest_weight_iff_positive_type.{u,v} := by
  intro L _ _ _ hss H _ φ e he V _ _ _ _ lam x
  constructor
  · rintro ⟨hx, hweight, hkill, hgen⟩
    let S : LieSubalgebra ℂ L :=
      { carrier := {z | ⁅z, x⁆ = 0}
        zero_mem' := zero_lie x
        add_mem' := by
          intro a b ha hb
          change ⁅a, x⁆ = 0 at ha
          change ⁅b, x⁆ = 0 at hb
          change ⁅a + b, x⁆ = 0
          rw [add_lie, ha, hb, add_zero]
        smul_mem' := by
          intro c a ha
          change ⁅a, x⁆ = 0 at ha
          change ⁅c • a, x⁆ = 0
          rw [smul_lie, ha, smul_zero]
        lie_mem' := by
          intro a b ha hb
          change ⁅a, x⁆ = 0 at ha
          change ⁅b, x⁆ = 0 at hb
          change ⁅⁅a, b⁆, x⁆ = 0
          simp [lie_lie, ha, hb] }
    have hH := RealRootSpace.cartan_isMaximalToral hss H
    have hpos : positive_value H φ ≤ S := by
      apply positive_le_of_simple H φ hss hH
      intro i
      exact rootSpace_le_of_nonzero H hss hH i.property.1.1 S
        (he i).1 (he i).2 (hkill i)
    exact ⟨hx, hweight, fun z => hpos z.property, hgen⟩
  · rintro ⟨hx, hweight, hkill, hgen⟩
    refine ⟨hx, hweight, fun i => ?_, hgen⟩
    have hpos : e i ∈ positive_value H φ :=
      LieSubalgebra.subset_lieSpan ⟨i.val, i.property.1.2, (he i).1⟩
    exact hkill ⟨e i, hpos⟩

private theorem exists_raisingVectors :
    ∃ e : simple H φ → L, RaisingVectors H φ e := by
  classical
  have he (i : simple H φ) :
      ∃ x : L, x ∈ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value H i.val
        ∧ x ≠ 0 :=
    (Submodule.ne_bot_iff _).mp i.property.1.1.2
  exact ⟨fun i => (he i).choose, fun i => (he i).choose_spec⟩

private theorem cone_height {a : Module.Dual ℂ H}
    (ha : a ∈ positiveRootCone_value (fun i : simple H φ => i.val)) :
    0 ≤ φ a ∧ (φ a = 0 → a = 0) := by
  apply Submodule.span_induction (p := fun x _ => 0 ≤ φ x ∧ (φ x = 0 → x = 0)) _ _ _ _ ha
  · rintro _ ⟨i, rfl⟩
    exact ⟨i.property.1.2.le, fun h => (i.property.1.2.ne' h).elim⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    refine ⟨add_nonneg hx.1 hy.1, fun h => ?_⟩
    rw [hx.2 (by linarith [hy.1]), hy.2 (by linarith [hx.1]), add_zero]
  · intro n x _ hx
    rw [map_nsmul]
    cases n with
    | zero => simp
    | succ n =>
      rw [nsmul_eq_mul]
      refine ⟨mul_nonneg (by positivity) hx.1, fun h => ?_⟩
      rw [hx.2 ((mul_eq_zero.mp h).resolve_left (by positivity)), smul_zero]

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

private theorem hom_eq_of_highest_eq
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (lam : Module.Dual ℂ H) (hχ : IsWeightCharacter H φ lam χ)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    {f g : M →ₗ⁅ℂ,L⁆ V} (h : f v₀ = g v₀) : f = g := by
  obtain ⟨e, he⟩ := exists_raisingVectors H φ
  have hzero : ∃! k : M →ₗ⁅ℂ,L⁆ V, k v₀ = 0 :=
    (verma_universal hss H φ hφ lam χ hχ e he V 0
      (by simp) (by simp)).1
  have hz : f - g = 0 := hzero.unique (by simp [h]) (by simp)
  exact sub_eq_zero.mp hz

private theorem verma_cyclic
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (lam : Module.Dual ℂ H) (hχ : IsWeightCharacter H φ lam χ) :
    LieSubmodule.lieSpan ℂ L ({v₀} : Set M) = ⊤ := by
  let N := LieSubmodule.lieSpan ℂ L ({v₀} : Set M)
  have hv : v₀ ∈ N := LieSubmodule.subset_lieSpan (Set.mem_singleton v₀)
  have hz : LieSubmodule.Quotient.mk' N = 0 :=
    hom_eq_of_highest_eq H φ χ hss hφ lam hχ
      (by simpa using (LieSubmodule.Quotient.mk_eq_zero (N := N)).mpr hv)
  exact top_unique fun x _ => (LieSubmodule.Quotient.mk_eq_zero (N := N)).mp
    (by rw [hz]; rfl)

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
private theorem highest_image
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
    {e : simple H φ → L} {lam : Module.Dual ℂ H} {x : V}
    (hx : IsHighestWeight e lam x)
    (p : V →ₗ⁅ℂ,L⁆ W) (hp : Function.Surjective p) (hpx : p x ≠ 0) :
    IsHighestWeight e lam (p x) := by
  refine ⟨hpx, fun h => ?_, fun i => ?_, ?_⟩
  · rw [← p.map_lie, hx.2.1 h, map_smul]
  · rw [← p.map_lie, hx.2.2.1 i, map_zero]
  · let N := LieSubmodule.lieSpan ℂ L ({p x} : Set W)
    have hpre : N.comap p = ⊤ := by
      apply top_unique
      rw [← hx.2.2.2, LieSubmodule.lieSpan_le]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact LieSubmodule.subset_lieSpan (Set.mem_singleton (p x))
    apply top_unique
    intro y _
    obtain ⟨z, rfl⟩ := hp y
    exact (LieSubmodule.mem_comap (f := p) (N' := N)).mp
      (hpre ▸ LieSubmodule.mem_top z)

private theorem verma_highest
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (lam : Module.Dual ℂ H) (hχ : IsWeightCharacter H φ lam χ)
    (e : simple H φ → L) (he : RaisingVectors H φ e) :
    IsHighestWeight e lam v₀ := by
  obtain ⟨_, _, hweights, hline⟩ := verma_weights hss H φ hφ lam χ hχ
  have hv : v₀ ∈ weightSpace_value M H lam := by
    rw [hline]
    exact Submodule.mem_span_singleton_self v₀
  refine ⟨(VermaModules.induced_free hss H φ hφ χ).choose_spec.2,
    (mem_weightSpace M H lam v₀).mp hv, fun i => ?_, verma_cyclic H φ χ hss hφ lam hχ⟩
  have hmem := root_action M H i.val lam (e i) v₀ (he i).1 hv
  have hbot : weightSpace_value M H (lam + i.val) = ⊥ := by
    by_contra hb
    have h := (cone_height H φ ((hweights _).mp hb)).1
    rw [map_sub, map_add] at h
    exact (not_le_of_gt i.property.1.2) (by linarith)
  rwa [hbot, Submodule.mem_bot] at hmem

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
theorem maximal_submodule : maximal_submodule_type := by
  classical
  intro L _ _ _ hss H _ φ hφ lam χ hχ
  let verma := induced_value H φ χ
  let topVector := highestVector_value H φ χ
  let maximal := maximalSubmodule_value H φ χ
  obtain ⟨hint, _, _, hline⟩ := verma_weights hss H φ hφ lam χ hχ
  have hcyc := verma_cyclic H φ χ hss hφ lam hχ
  have hv0 := (VermaModules.induced_free hss H φ hφ χ).choose_spec.2
  let A := weightSpace_value verma H
  let B : Submodule ℂ verma := ⨆ μ ∈ {μ | μ ≠ lam}, A μ
  have hdis : Disjoint (A lam) B :=
    hint.submodule_iSupIndep.disjoint_biSup (by simp)
  have hvA : topVector ∈ A lam := by
    change topVector ∈ weightSpace_value verma H lam
    rw [hline]
    exact Submodule.mem_span_singleton_self topVector
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  have hproper (N : LieSubmodule ℂ L verma) (hN : N ≠ ⊤) : N.toSubmodule ≤ B := by
    have hvN : topVector ∉ N := fun hv =>
      hN (top_unique (hcyc ▸ LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv)))
    obtain ⟨hparts, _, _⟩ := WeightSubmodules.weight_submodules (N.restr H) hint
    let C (μ : Module.Dual ℂ H) := (A μ).comap N.toSubmodule.subtype
    have htop : (⨆ μ, C μ) = ⊤ := hparts.submodule_iSup_eq_top
    intro x hx
    let y : N := ⟨x, hx⟩
    have hy : y ∈ ⨆ μ, C μ := by rw [htop]; trivial
    change (y : verma) ∈ B
    refine Submodule.iSup_induction (motive := fun z : N => (z : verma) ∈ B) C hy ?_ ?_ ?_
    · intro μ z hz
      have hza : (z : verma) ∈ A μ := hz
      by_cases hm : μ = lam
      · subst μ
        rw [show A lam = ℂ ∙ topVector from hline, Submodule.mem_span_singleton] at hza
        obtain ⟨c, hc⟩ := hza
        have hc0 : c = 0 := by
          by_contra hcn
          apply hvN
          have hcN := N.smul_mem c⁻¹ z.property
          rwa [← hc, smul_smul, inv_mul_cancel₀ hcn, one_smul] at hcN
        rw [← hc, hc0, zero_smul]
        exact B.zero_mem
      · exact (show A μ ≤ B from le_iSup₂_of_le μ hm le_rfl) hza
    · exact B.zero_mem
    · intro a b ha hb
      exact B.add_mem ha hb
  have hJB : (maximal).toSubmodule ≤ B := by
    change (maximalSubmodule_value H φ χ).toSubmodule ≤ B
    rw [maximalSubmodule_value, LieSubmodule.sSup_toSubmodule_eq_iSup]
    exact iSup₂_le hproper
  refine ⟨fun hj => ?_, fun N hN => le_sSup hN⟩
  have hm : topVector ∈ maximalSubmodule_value H φ χ := by
    rw [hj]
    exact LieSubmodule.mem_top topVector
  have hvB : topVector ∈ B := hJB hm
  exact hv0 (Submodule.disjoint_def.mp hdis topVector hvA hvB)

private theorem quotient_highest_ne_zero
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (lam : Module.Dual ℂ H) (hχ : IsWeightCharacter H φ lam χ) :
    q v₀ ≠ 0 := by
  intro h
  have hv : v₀ ∈ J := (LieSubmodule.Quotient.mk_eq_zero (N := J)).mp h
  have ht : J = ⊤ := top_unique
    (verma_cyclic H φ χ hss hφ lam hχ ▸
      LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv))
  exact (maximal_submodule hss H φ hφ lam χ hχ).1 ht

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
theorem simple_quotient : simple_quotient_type := by
  intro L _ _ _ hss H _ φ hφ lam χ hχ e he
  let maximal := maximalSubmodule_value H φ χ
  let projection := quotientMap H φ χ
  have hq := LieSubmodule.Quotient.surjective_mk' maximal
  have hv := quotient_highest_ne_zero H φ χ hss hφ lam hχ
  refine ⟨?_, highest_image H φ (verma_highest H φ χ hss hφ lam hχ e he) projection hq hv⟩
  let : Nontrivial (simpleQuotient_value H φ χ) := nontrivial_of_ne _ _ hv
  constructor
  intro N
  by_cases ht : N.comap projection = ⊤
  · right
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := hq y
    exact (LieSubmodule.mem_comap (f := projection) (N' := N)).mp
      (ht ▸ LieSubmodule.mem_top x)
  · left
    apply le_bot_iff.mp
    intro y hy
    obtain ⟨x, rfl⟩ := hq y
    have hx : x ∈ maximal := (maximal_submodule hss H φ hφ lam χ hχ).2 ht hy
    exact (LieSubmodule.mem_bot _).mpr ((LieSubmodule.Quotient.mk_eq_zero (N := maximal)).mpr hx)

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
theorem exists_simple_quotient : exists_simple_quotient_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam e he
  obtain ⟨χ, hχ, _⟩ := VermaModules.character_existsUnique hss H φ hφ lam
  exact ⟨χ, hχ, maximal_submodule hss H φ hφ lam χ hχ,
    simple_quotient hss H φ hφ lam χ hχ e he⟩

private theorem factors_to_quotient
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (lam : Module.Dual ℂ H) (hχ : IsWeightCharacter H φ lam χ)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    (p : M →ₗ⁅ℂ,L⁆ V) (hp : Function.Surjective p) (hker : p.ker ≠ ⊤) :
    ∃ f : V →ₗ⁅ℂ,L⁆ Q, (∀ x, f (p x) = q x) ∧ Function.Surjective f := by
  have hle : p.ker ≤ J := (maximal_submodule hss H φ hφ lam χ hχ).2 hker
  have hk : LinearMap.ker (p : M →ₗ[ℂ] V) ≤ LinearMap.ker (q : M →ₗ[ℂ] Q) := by
    rw [← LieModuleHom.ker_toSubmodule, ← LieModuleHom.ker_toSubmodule,
      LieSubmodule.Quotient.mk'_ker]
    exact hle
  let F := LinearMap.liftOfSurjective (f := (p : M →ₗ[ℂ] V)) hp ⟨(q : M →ₗ[ℂ] Q), hk⟩
  have hF (x : M) : F (p x) = q x := LinearMap.equivOfSurjective_apply hp hk
  let f : V →ₗ⁅ℂ,L⁆ Q :=
    { F with
      map_lie' := by
        intro a y
        obtain ⟨x, rfl⟩ := hp y
        change F ⁅a, p x⁆ = ⁅a, F (p x)⁆
        rw [← p.map_lie, hF, hF, (q).map_lie] }
  refine ⟨f, hF, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J y
  exact ⟨p x, hF x⟩

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
theorem highest_weight_surjects : highest_weight_surjects_type.{u,v} := by
  intro L _ _ _ hss H _ φ hφ lam χ hχ e he V _ _ _ _ x hx
  let topVector := highestVector_value H φ χ
  obtain ⟨p, hpx, hp⟩ :=
    (verma_universal hss H φ hφ lam χ hχ e he V x hx.2.1 hx.2.2.1).2 hx.1 hx.2.2.2
  have hker : p.ker ≠ ⊤ := by
    intro h
    exact hx.1 (hpx ▸ LieModuleHom.mem_ker.mp (h ▸ LieSubmodule.mem_top topVector))
  obtain ⟨f, hfp, hf⟩ := factors_to_quotient H φ χ hss hφ lam hχ p hp hker
  refine ⟨f, ⟨hpx ▸ hfp topVector, hf⟩, fun g hg => ?_⟩
  have h : g.comp p = f.comp p := hom_eq_of_highest_eq H φ χ hss hφ lam hχ
    (by change g (p topVector) = f (p topVector); rw [hpx, hg.1, ← hpx, hfp])
  apply LieModuleHom.ext
  intro y
  obtain ⟨m, rfl⟩ := hp y
  exact LieModuleHom.congr_fun h m

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
theorem unique_simple_quotient : unique_simple_quotient_type.{u,v} := by
  intro L _ _ _ hss H _ φ hφ lam χ hχ V _ _ _ _ _ p hp
  let topVector := highestVector_value H φ χ
  let quotientType := simpleQuotient_value H φ χ
  have hker : p.ker ≠ ⊤ := by
    intro h
    have ht : (⊤ : LieSubmodule ℂ L V) ≤ ⊥ := by
      intro y _
      obtain ⟨x, rfl⟩ := hp y
      exact (LieSubmodule.mem_bot _).mpr (LieModuleHom.mem_ker.mp (h ▸ LieSubmodule.mem_top x))
    exact IsSimpleOrder.bot_ne_top (le_antisymm bot_le ht)
  obtain ⟨f, hfp, hf⟩ := factors_to_quotient H φ χ hss hφ lam hχ p hp hker
  have hinj : Function.Injective f := by
    apply (LieModuleHom.ker_eq_bot f).mp
    rcases eq_bot_or_eq_top f.ker with h | h
    · exact h
    · exact (quotient_highest_ne_zero H φ χ hss hφ lam hχ
        ((hfp topVector).symm.trans (LieModuleHom.mem_ker.mp (h ▸ LieSubmodule.mem_top (p topVector))))).elim
  let F := LinearEquiv.ofBijective (f : V →ₗ[ℂ] quotientType) ⟨hinj, hf⟩
  let i : V ≃ₗ⁅ℂ,L⁆ quotientType := ⟨f, F.symm, F.left_inv, F.right_inv⟩
  refine ⟨i, hfp topVector, fun j hj => ?_⟩
  have h : j.toLieModuleHom.comp p = f.comp p :=
    hom_eq_of_highest_eq H φ χ hss hφ lam hχ (hj.trans (hfp topVector).symm)
  apply LieModuleEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := hp y
  exact LieModuleHom.congr_fun h x

private theorem finite_weight_decomposition
    (hss : IsSemisimple_value ℂ L)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] :
    DirectSum.IsInternal (weightSpace_value V H) := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  have hab (a b : H) : ⁅a, b⁆ = 0 := trivial_lie_zero H H a b
  have hsem (a : H) := LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra
    (K := ℂ) (L := L) (H := H) a.property
  exact RepresentationJordan.toral_weight_decomposition ℂ L V hss (LieModule.toEnd ℂ L V) H hab
    (fun a => (absolutely_semisimple_iff _).mpr (hsem a))

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
theorem finite_simple_quotient : finite_simple_quotient_type.{u,v} := by
  classical
  intro L _ _ _ hss H _ φ hφ e he V _ _ _ _ _ _
  let A := weightSpace_value V H
  have hint := finite_weight_decomposition H hss V
  have hfinite : {μ | A μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hint.submodule_iSupIndep
  have hnonempty : {μ | A μ ≠ ⊥}.Nonempty := by
    by_contra hn
    have hbot : ∀ μ, A μ = ⊥ := fun μ => not_not.mp (fun h => hn ⟨μ, h⟩)
    let : Nontrivial V := (LieSubmodule.nontrivial_iff ℂ L V).mp inferInstance
    have ht : (⨆ μ, A μ) = ⊤ := hint.submodule_iSup_eq_top
    rw [show (⨆ μ, A μ) = ⊥ by simp only [hbot, iSup_bot]] at ht
    exact bot_ne_top ht
  obtain ⟨lam, hlam, hmax⟩ := hfinite.toFinset.exists_max_image φ
    (by simpa only [Set.Finite.toFinset_nonempty] using hnonempty)
  have hlam' : A lam ≠ ⊥ := hfinite.mem_toFinset.mp hlam
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hlam'
  have hekill (i : simple H φ) : ⁅e i, x⁆ = 0 := by
    have hh := root_action V H i.val lam (e i) x (he i).1 hx
    have hbot : A (lam + i.val) = ⊥ := by
      by_contra hn
      have h := hmax _ (hfinite.mem_toFinset.mpr hn)
      rw [map_add] at h
      exact (not_le_of_gt i.property.1.2) (by linarith)
    rwa [show weightSpace_value V H (lam + i.val) = ⊥ from hbot, Submodule.mem_bot] at hh
  have hcyc : LieSubmodule.lieSpan ℂ L ({x} : Set V) = ⊤ := by
    rcases eq_bot_or_eq_top (LieSubmodule.lieSpan ℂ L ({x} : Set V)) with hb | ht
    · have hm := LieSubmodule.subset_lieSpan (R := ℂ) (L := L) (Set.mem_singleton x)
      exact (hx0 ((LieSubmodule.mem_bot _).mp (hb ▸ hm))).elim
    · exact ht
  have hw : IsHighestWeight e lam x := ⟨hx0, (mem_weightSpace V H lam x).mp hx, hekill, hcyc⟩
  obtain ⟨c, hc, _⟩ := VermaModules.character_existsUnique hss H φ hφ lam
  obtain ⟨p, hpv, hp⟩ :=
    (verma_universal hss H φ hφ lam c hc e he V x hw.2.1 hekill).2 hx0 hcyc
  obtain ⟨i, hi, _⟩ := unique_simple_quotient hss H φ hφ lam c hc V p hp
  exact ⟨lam, c, x, hc, hw, i, hpv ▸ hi⟩

private theorem weight_in_verma_cone
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (lam : Module.Dual ℂ H) (hχ : IsWeightCharacter H φ lam χ)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    (p : M →ₗ⁅ℂ,L⁆ V) (hp : Function.Surjective p)
    (mu : Module.Dual ℂ H) (x : V) (hx : x ∈ weightSpace_value V H mu) (hx0 : x ≠ 0) :
    lam - mu ∈ positiveRootCone_value (fun i : simple H φ => i.val) := by
  let A := weightSpace_value M H
  let B := weightSpace_value V H
  let F : M →ₗ[ℂ] V := p
  obtain ⟨hint, _, hweights, _⟩ := verma_weights hss H φ hφ lam χ hχ
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  have hind : iSupIndep B := weight_independent
  have hmaps : (fun a => (A a).map F) ≤ B := by
    intro a
    rintro _ ⟨m, hm, rfl⟩
    apply (mem_weightSpace V H a (p m)).mpr
    intro h
    change ⁅(h : L), p m⁆ = a h • p m
    rw [← p.map_lie, (mem_weightSpace M H a m).mp hm h, map_smul]
  have hspan : (⨆ a, (A a).map F) = ⊤ := by
    rw [← Submodule.map_iSup, hint.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hp
  have heq := (hind.le_iff_eq_of_iSup_eq_top hspan).mp hmaps
  apply (hweights mu).mp
  intro hb
  have hmu := congrFun heq mu
  change (weightSpace_value M H mu).map F = B mu at hmu
  rw [hb, Submodule.map_bot] at hmu
  have hxb : x ∈ (⊥ : Submodule ℂ V) := hmu.symm ▸ hx
  exact hx0 (by simpa using hxb)

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
theorem highest_weight_eq_of_equiv : highest_weight_eq_of_equiv_type.{u,v,w} := by
  intro L _ _ _ hss H _ φ hφ e he V W _ _ _ _ _ _ _ _ lam mu x y hx hy i
  obtain ⟨c, hc, _⟩ := VermaModules.character_existsUnique hss H φ hφ lam
  obtain ⟨d, hd, _⟩ := VermaModules.character_existsUnique hss H φ hφ mu
  obtain ⟨p, _, hp⟩ :=
    (verma_universal hss H φ hφ lam c hc e he V x hx.2.1 hx.2.2.1).2 hx.1 hx.2.2.2
  obtain ⟨r, _, hr⟩ :=
    (verma_universal hss H φ hφ mu d hd e he W y hy.2.1 hy.2.2.1).2 hy.1 hy.2.2.2
  have hix : IsHighestWeight e lam (i x) :=
    highest_image H φ hx i.toLieModuleHom i.surjective (fun h => hx.1 (i.injective (by simpa using h)))
  have hab := weight_in_verma_cone H φ c hss hφ lam hc (i.toLieModuleHom.comp p)
    (i.surjective.comp hp) mu y ((mem_weightSpace W H mu y).mpr hy.2.1) hy.1
  have hba := weight_in_verma_cone H φ d hss hφ mu hd r hr lam (i x)
    ((mem_weightSpace W H lam (i x)).mpr hix.2.1) hix.1
  have h1 := cone_height H φ hab
  have h2 := (cone_height H φ hba).1
  have hnonneg := h1.1
  have hzero : φ (lam - mu) = 0 := by
    rw [map_sub] at h2 hnonneg ⊢
    linarith
  exact sub_eq_zero.mp (h1.2 hzero)

end LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
