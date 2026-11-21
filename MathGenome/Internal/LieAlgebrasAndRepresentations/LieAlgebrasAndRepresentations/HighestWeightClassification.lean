import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightClassification
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompleteReducibility
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DominanceNecessary
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LieAlgebrasAndRepresentations.HighestWeightClassification

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.HighestWeightClassification
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.HighestWeightData (weightSpace_value)
open UniversalEnvelopingAlgebra (ι)
open scoped Classical DirectSum

open private verma_highest highest_image factors_to_quotient
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open private power_smul_eq enveloping_mem
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

local instance {H : LieSubalgebra ℂ L} {φ : Direction H}
    {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {H : LieSubalgebra ℂ L} {φ : Direction H}
    {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

private theorem exists_normalized [FiniteDimensional ℂ L] (hss : IsSemisimple_value ℂ L)
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H) :
    ∃ e f : simple H φ → L, Normalized H φ e f := by
  have ht (i : simple H φ) := LieAlgebrasAndRepresentations.exists_root_triple hss H
    (RealRootSpace.cartan_isMaximalToral hss H) i.val i.property.1.1
  choose e f he hf hne hnf hef _ _ using ht
  exact ⟨e, f, fun i => ⟨he i, hf i, hne i, hnf i, hef i⟩⟩

private theorem raising_of_normalized [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (φ : Direction H)
    {e f : simple H φ → L} (hef : Normalized H φ e f) : RaisingVectors H φ e :=
  fun i => ⟨(hef i).1, (hef i).2.2.1⟩

theorem finite_simple_iff_dominant : finite_simple_iff_dominant_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam χ hχ
  constructor
  · intro h
    exact DominanceNecessary.finite_simple_quotient_dominant hss H φ hφ lam χ hχ h.1
  · intro hd
    obtain ⟨e, f, hef⟩ := exists_normalized hss H φ
    exact ⟨(FiniteHighestWeightExistence.finite_highest_weight_existence
        hss H φ hφ lam χ hχ hd e f hef).2.2.2,
      (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ
        e (raising_of_normalized H φ hef)).1⟩

theorem dominant_has_simple_quotient : dominant_has_simple_quotient_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam hd
  obtain ⟨χ, hχ, _⟩ := VermaModules.character_existsUnique hss H φ hφ lam
  exact ⟨χ, hχ, (finite_simple_iff_dominant hss H φ hφ lam χ hχ).mpr hd⟩

theorem simple_quotients_equiv_iff : simple_quotients_equiv_iff_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam mu χ ψ hχ hψ
  constructor
  · rintro ⟨i⟩
    obtain ⟨e, f, hef⟩ := exists_normalized hss H φ
    have he := raising_of_normalized H φ hef
    have h₁ := (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e he).2
    have h₂ := (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ mu ψ hψ e he).2
    exact SimpleHighestWeightQuotient.highest_weight_eq_of_equiv hss H φ hφ e he
      _ _ lam mu _ _ h₁ h₂ i
  · rintro rfl
    obtain ⟨c, hc, hu⟩ := VermaModules.character_existsUnique hss H φ hφ lam
    have h : χ = ψ := (hu χ hχ).trans (hu ψ hψ).symm
    subst ψ
    exact ⟨LieModuleEquiv.refl⟩

theorem finite_simple_classification : finite_simple_classification_type.{u,v} := by
  intro L _ _ _ hss H _ φ hφ V _ _ _ _ _ _
  obtain ⟨e, f, hef⟩ := exists_normalized hss H φ
  obtain ⟨lam, χ, x, hχ, _, i, _⟩ :=
    SimpleHighestWeightQuotient.finite_simple_quotient hss H φ hφ e
      (raising_of_normalized H φ hef) V
  have hfinite : FiniteDimensional ℂ (simpleQuotient_value H φ χ) :=
    FiniteDimensional.of_surjective i.toLinearEquiv.toLinearMap i.surjective
  have hd := DominanceNecessary.finite_simple_quotient_dominant hss H φ hφ lam χ hχ hfinite
  refine ⟨⟨lam, hd⟩, ⟨χ, hχ, ⟨i⟩⟩, ?_⟩
  rintro mu ⟨ψ, hψ, ⟨j⟩⟩
  exact Subtype.ext ((simple_quotients_equiv_iff hss H φ hφ mu.val lam ψ χ hψ hχ).mp
    ⟨j.symm.trans i⟩)

private theorem map_action_power
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
    (p : V →ₗ⁅ℂ,L⁆ W) (a : L) (n : ℕ) (x : V) :
    p ((LieModule.toEnd ℂ L V a ^ n) x) =
      (LieModule.toEnd ℂ L W a ^ n) (p x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    change p ⁅a, (LieModule.toEnd ℂ L V a ^ n) x⁆ =
      ⁅a, (LieModule.toEnd ℂ L W a ^ n) (p x)⁆
    rw [p.map_lie, ih]

private def quotientLift {V : Type v} {W : Type w}
    [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
    (N : LieSubmodule ℂ L V) (p : V →ₗ⁅ℂ,L⁆ W) (h : N ≤ p.ker) :
    V ⧸ N →ₗ⁅ℂ,L⁆ W where
  __ := N.toSubmodule.liftQ p.toLinearMap h
  map_lie' := by
    intro a z
    obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N z
    exact p.map_lie a x

theorem integrable_quotient_equiv : integrable_quotient_equiv_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam χ hχ hd e f hef
  let N := relationSubmodule_value H φ χ hd f
  let Q := quotient_value H φ χ hd f
  let q := LieSubmodule.Quotient.mk' N
  let v := highestClass H φ χ hd f
  have hq := LieSubmodule.Quotient.surjective_mk' N
  have he := raising_of_normalized H φ hef
  obtain ⟨hv, hline, _, _, _⟩ :=
    IntegrableHighestWeightQuotient.quotient_integrable hss H φ hφ lam χ hχ hd e f hef
  let : FiniteDimensional ℂ Q :=
    (FiniteHighestWeightExistence.finite_highest_weight_existence
      hss H φ hφ lam χ hχ hd e f hef).1
  have hN : q.ker ≠ ⊤ := by
    intro h
    exact hv (LieModuleHom.mem_ker.mp (h ▸ LieSubmodule.mem_top (highestVector_value H φ χ)))
  obtain ⟨p, hpq, hp⟩ :=
    factors_to_quotient H φ χ hss hφ lam hχ q hq hN
  have hvHighest : IsHighestWeight e lam v :=
    highest_image H φ (verma_highest H φ χ hss hφ lam hχ e he) q hq hv
  have hpv : p v ≠ 0 := (hpq _).trans_ne
    (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e he).2.1
  -- Complete reducibility provides a Lie module projection with kernel ker p.
  let qK := LieSubmodule.Quotient.mk' p.ker
  obtain ⟨s, hs⟩ := CompleteReducibility.quotient_section ℂ L Q hss p.ker
  let E := s.comp qK
  have hE (z : Q) : qK (E z) = qK z :=
    LieModuleHom.congr_fun hs (qK z)
  have hEv : E v ≠ 0 := by
    intro h
    have hvK : qK v = 0 := by simpa only [h, map_zero] using (hE v).symm
    exact hpv (LieModuleHom.mem_ker.mp ((LieSubmodule.Quotient.mk_eq_zero p.ker).mp hvK))
  have hweight : E v ∈ weightSpace_value Q H lam := by
    apply (HighestWeight.mem_weightSpace Q H lam (E v)).mpr
    intro h
    rw [← E.map_lie, hvHighest.2.1 h, map_smul]
  rw [hline] at hweight
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hweight
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hEv (by simpa using hc.symm)
  have hvRange : v ∈ E.range := by
    rw [← show c⁻¹ • E v = v by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]]
    exact E.range.smul_mem _ ⟨v, rfl⟩
  have hsurj : Function.Surjective E := by
    apply (LieModuleHom.range_eq_top E).mp
    rw [← top_le_iff, ← hvHighest.2.2.2, LieSubmodule.lieSpan_le]
    simpa using hvRange
  have hid (z : Q) : E z = z := by
    obtain ⟨y, rfl⟩ := hsurj z
    change s (qK (E y)) = E y
    rw [hE]
    rfl
  have hinj : Function.Injective p := by
    apply (LieModuleHom.ker_eq_bot p).mp
    apply (LieSubmodule.eq_bot_iff _).mpr
    intro z hz
    have hz' : qK z = 0 := (LieSubmodule.Quotient.mk_eq_zero p.ker).mpr hz
    rw [← hid z]
    change s (qK z) = 0
    rw [hz', map_zero]
  let i := LinearEquiv.ofBijective p.toLinearMap ⟨hinj, hp⟩
  exact ⟨⟨p, i.symm, i.left_inv, i.right_inv⟩, hpq⟩

theorem defining_relations : defining_relations_type.{u,v} := by
  intro L _ _ _ hss H _ φ hφ lam χ hχ hd e f hef
  let m := highestVector_value H φ χ
  let N := relationSubmodule_value H φ χ hd f
  let q := LieSubmodule.Quotient.mk' N
  let x := quotientHighestVector H φ χ
  let rel (j : simple H φ) := (ι ℂ (f j)) ^ (simpleCoordinate H φ hd j + 1) • m
  have hrel (j : simple H φ) : rel j ∈ N :=
    Submodule.subset_span ⟨j, rfl⟩
  have he := raising_of_normalized H φ hef
  obtain ⟨i, hi⟩ := integrable_quotient_equiv hss H φ hφ lam χ hχ hd e f hef
  have hix : i (q m) = x := hi m
  refine ⟨(SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e he).2,
    fun j => ?_, ?_⟩
  · change (LieModule.toEnd ℂ L (simpleQuotient_value H φ χ) (f j) ^
      (simpleCoordinate H φ hd j + 1)) x = 0
    rw [← hix]
    change (LieModule.toEnd ℂ L (simpleQuotient_value H φ χ) (f j) ^
      (simpleCoordinate H φ hd j + 1)) (i.toLieModuleHom (q m)) = 0
    rw [← map_action_power i.toLieModuleHom, ← map_action_power q, ← power_smul_eq H φ χ]
    change i (q (rel j)) = 0
    rw [(LieSubmodule.Quotient.mk_eq_zero N).mpr (hrel j), map_zero]
  · intro V _ _ _ _ y hyH hyE hyF
    obtain ⟨p, hpy, huniq⟩ :=
      (VermaWeightsUniversal.verma_universal hss H φ hφ lam χ hχ e he V y hyH hyE).1
    have hN : N ≤ p.ker := by
      intro z hz
      change z ∈ Submodule.span (U L) (Set.range rel) at hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        apply LieModuleHom.mem_ker.mpr
        change p ((ι ℂ (f j)) ^ (simpleCoordinate H φ hd j + 1) • m) = 0
        rw [power_smul_eq H φ χ, map_action_power, hpy]
        exact hyF j
      | zero => exact p.ker.zero_mem
      | add x y _ _ hx hy => exact p.ker.add_mem hx hy
      | smul a z _ hz => exact enveloping_mem H φ χ p.ker a z hz
    let g := quotientLift N p hN
    let k := g.comp i.symm.toLieModuleHom
    have hky : k x = y := by
      rw [← hix]
      change g (i.symm (i (q m))) = y
      rw [i.symm_apply_apply]
      exact hpy
    refine ⟨k, hky, fun k' hk' => ?_⟩
    let l := i.toLieModuleHom.comp q
    have hl : l m = x := hix
    have hpre : k'.comp l = k.comp l :=
      (huniq _ (by change k' (l m) = y; rw [hl, hk'])).trans
        (huniq _ (by change k (l m) = y; rw [hl, hky])).symm
    ext z
    obtain ⟨a, rfl⟩ := i.surjective.comp (LieSubmodule.Quotient.surjective_mk' N) z
    exact LieModuleHom.congr_fun hpre a

theorem finite_decomposition : finite_decomposition_type.{u,v} := by
  intro L _ _ _ hss H _ φ hφ V _ _ _ _ _
  obtain ⟨S, hS, hirr, _, i, hi⟩ :=
    CompleteReducibility.finite_simple_decomposition_equivariant ℂ L V hss
  refine ⟨S, hS, ?_, ?_⟩
  · refine ⟨i, ?_⟩
    apply DirectSum.linearMap_ext
    intro W
    apply LinearMap.ext
    intro z
    exact (hi W z).trans (DirectSum.coeLinearMap_lof (fun W : S => W.val.toSubmodule) W z).symm
  · intro W hW
    let : IsSimpleOrder (LieSubmodule ℂ L W) := hirr W hW
    obtain ⟨lam, ⟨χ, hχ, hi⟩, _⟩ := finite_simple_classification hss H φ hφ W
    exact ⟨lam.val, χ, lam.property, hχ, hi⟩

end LieAlgebrasAndRepresentations.HighestWeightClassification
