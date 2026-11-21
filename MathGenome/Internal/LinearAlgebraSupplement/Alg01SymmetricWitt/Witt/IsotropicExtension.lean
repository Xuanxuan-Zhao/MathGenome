import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.IsotropicExtension
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.HyperbolicSplitting
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Alg01SymmetricWitt.Witt.IsotropicExtension

open Coordinates (hyperbolicPlane hyperbolicSum firstCoordinates totallyIsotropic
  hyperbolicPlane_apply hyperbolicSum_apply hyperbolicSum_zero mem_firstCoordinates)
open HyperbolicSplitting (hyperbolicSplitting)
open OrthogonalSplitting (orthogonalComplement)

universe u v

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]

/-- Separate the first hyperbolic plane from a nonempty coordinate sum. -/
private def separateFirst (n : ℕ) (q : QuadraticForm k V) :
    ((hyperbolicSum k (n + 1)).prod q).IsometryEquiv
      ((hyperbolicPlane k).prod ((hyperbolicSum k n).prod q)) := by
  let headTail : (Fin (n + 1) → k × k) ≃ₗ[k] (k × k) × (Fin n → k × k) :=
    { (Fin.consEquiv (fun _ : Fin (n + 1) => k × k)).symm with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact
    { (headTail.prodCongr (LinearEquiv.refl k V)).trans
        (LinearEquiv.prodAssoc k (k × k) (Fin n → k × k) V) with
      map_app' := fun z => by
        change hyperbolicPlane k (z.1 0) + (hyperbolicSum k n (Fin.tail z.1) + q z.2) =
          hyperbolicSum k (n + 1) z.1 + q z.2
        simp only [hyperbolicPlane_apply, hyperbolicSum_apply, Fin.tail]
        rw [Fin.sum_univ_succ, add_assoc] }

private theorem firstCoordinates_succ {n : ℕ} (x : Fin (n + 1) → k × k) :
    x ∈ firstCoordinates k (n + 1) ↔ (x 0).2 = 0 ∧ Fin.tail x ∈ firstCoordinates k n := by
  simp only [mem_firstCoordinates, Fin.tail]
  exact ⟨fun h => ⟨h 0, fun i => h i.succ⟩, fun h i => Fin.cases h.1 h.2 i⟩

private theorem mem_firstLine (p : k × k) :
    p ∈ k ∙ (1, 0) ↔ p.2 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro hp
    exact ⟨p.1, Prod.ext (mul_one _) ((mul_zero _).trans hp.symm)⟩

/-- Adapt a hyperbolic splitting to the given totally isotropic subspace. -/
theorem isotropicExtension : Specs.Alg01SymmetricWitt.Witt.IsotropicExtension.isotropicExtension.{u,v} := by
  intro k V _ _ _ _ _ q hq T hT
  dsimp only
  generalize hm : Module.finrank k T = m
  induction m generalizing V with
  | zero =>
    have hbot : T = ⊥ := Submodule.finrank_eq_zero.mp hm
    let : Unique (Fin 0 → k × k) := uniqueOfSubsingleton 0
    let i : ((hyperbolicSum k 0).prod (q.comp (⊤ : Submodule k V).subtype)).IsometryEquiv q :=
      { LinearEquiv.uniqueProd.trans Submodule.topEquiv with
        map_app' := fun z => by
          change q (z.2 : V) = hyperbolicSum k 0 z.1 + q (z.2 : V)
          rw [hyperbolicSum_zero, zero_apply, zero_add] }
    have hn : (q.comp (⊤ : Submodule k V).subtype).Nondegenerate := by
      let e : (q.comp (⊤ : Submodule k V).subtype).IsometryEquiv q :=
        { Submodule.topEquiv with map_app' := fun _ => rfl }
      apply QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr
      rw [← e.symm.map_radical, hq.radical_eq_bot, Submodule.map_bot]
    refine ⟨⊤, i, hn, fun _ => rfl, fun x c => ?_⟩
    change (c : V) ∈ T ↔ x ∈ firstCoordinates k 0 ∧ c = 0
    have hx : x ∈ firstCoordinates k 0 := mem_firstCoordinates.mpr fun i => Fin.elim0 i
    rw [hbot, Submodule.mem_bot, and_iff_right hx]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  | succ n ih =>
    have hne : T ≠ ⊥ := fun h => Nat.succ_ne_zero n (hm.symm.trans
      (Submodule.finrank_eq_zero.mpr h))
    obtain ⟨e, heT, he⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨f, _, _, _, ⟨i, hi⟩, _, ⟨a, ha⟩, hW⟩ :=
      hyperbolicSplitting q hq e he (hT e heT)
    let P := Submodule.span k ({e, f} : Set V)
    let W := orthogonalComplement q P
    let qW := q.comp W.subtype
    let split : ((hyperbolicPlane k).prod qW).IsometryEquiv q :=
      (i.prod (QuadraticMap.IsometryEquiv.refl qW)).trans a
    have hsplit (p : k × k) (w : W) :
        split (p, w) = p.1 • e + p.2 • f + (w : V) := by
      change a (i p, w) = _
      rw [ha, hi]
    let S := T.comap W.subtype
    have hS : totallyIsotropic qW S := fun w hw => hT (w : V) hw
    have hfirst (p : k × k) (hp : p.2 = 0) : split (p, (0 : W)) ∈ T := by
      simpa [hsplit, hp] using T.smul_mem p.1 heT
    have hTsplit (p : k × k) (w : W) :
        split (p, w) ∈ T ↔ p.2 = 0 ∧ w ∈ S := by
      constructor
      · intro h
        -- Adding the first basis vector changes the quadratic value by the second coordinate.
        have he' : split ((1, 0), (0 : W)) ∈ T := hfirst (1, 0) rfl
        have hpadd : p + (1, 0) = (p.1 + 1, p.2) := Prod.ext rfl (add_zero _)
        have hadd : split ((p.1 + 1, p.2), w) ∈ T := by
          simpa [← map_add, hpadd] using T.add_mem h he'
        have hq₁ := split.map_app ((p.1 + 1, p.2), w)
        have hq₂ := split.map_app (p, w)
        rw [hT _ hadd, QuadraticMap.prod_apply, hyperbolicPlane_apply] at hq₁
        rw [hT _ h, QuadraticMap.prod_apply, hyperbolicPlane_apply] at hq₂
        have hp : p.2 = 0 := by
          have hh := add_right_cancel (hq₁.symm.trans hq₂)
          rw [Prod.fst, Prod.snd, add_mul, one_mul] at hh
          exact add_left_cancel (hh.trans (add_zero _).symm)
        refine ⟨hp, ?_⟩
        have hw := T.sub_mem h (hfirst p hp)
        change (w : V) ∈ T
        simpa [hsplit] using hw
      · rintro ⟨hp, hw⟩
        change (w : V) ∈ T at hw
        simpa [hsplit, hp] using T.add_mem (T.smul_mem p.1 heT) hw
    let L : Submodule k (k × k) := k ∙ (1, 0)
    have hpull : T.comap split.toLinearEquiv.toLinearMap = L.prod S := by
      ext z
      exact (hTsplit z.1 z.2).trans (and_congr (mem_firstLine z.1).symm Iff.rfl)
    have hL : Module.finrank k L = 1 :=
      finrank_span_singleton (by simp : ((1, 0) : k × k) ≠ 0)
    have hdim := split.toLinearEquiv.symm.finrank_map_eq T
    rw [← Submodule.comap_equiv_eq_map_symm, hpull, (L.prodEquiv S).finrank_eq,
      Module.finrank_prod, hL, hm] at hdim
    have hn : Module.finrank k S = n :=
      Nat.succ.inj ((Nat.add_comm (Module.finrank k S) 1).trans hdim)
    obtain ⟨D, j, hD, hj, hmem⟩ := ih qW hW S hS hn
    let C := D.map W.subtype
    let b : (qW.comp D.subtype).IsometryEquiv (q.comp C.subtype) :=
      { Submodule.equivMapOfInjective W.subtype W.subtype_injective D with
        map_app' := fun _ => rfl }
    have hb (c : C) : (((b.symm c : D) : W) : V) = (c : V) := by
      exact Submodule.map_equivMapOfInjective_symm_apply W.subtype W.subtype_injective D c
    have hC : (q.comp C.subtype).Nondegenerate := by
      apply QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr
      rw [← b.map_radical, hD.radical_eq_bot, Submodule.map_bot]
    let tailSplit := ((QuadraticMap.IsometryEquiv.refl (hyperbolicSum k n)).prod b.symm).trans j
    let result : ((hyperbolicSum k (n + 1)).prod (q.comp C.subtype)).IsometryEquiv q :=
      ((separateFirst n (q.comp C.subtype)).trans
        ((QuadraticMap.IsometryEquiv.refl (hyperbolicPlane k)).prod tailSplit)).trans split
    refine ⟨C, result, hC, ?_, ?_⟩
    · intro c
      change split ((0, 0), j (0, b.symm c)) = _
      rw [hj, hsplit]
      simpa using hb c
    · intro x c
      change split (x 0, j (Fin.tail x, b.symm c)) ∈ T ↔
        x ∈ firstCoordinates k (n + 1) ∧ c = 0
      rw [hTsplit, hmem, firstCoordinates_succ, and_assoc]
      exact and_congr Iff.rfl
        (and_congr Iff.rfl (map_eq_zero_iff b.symm (EquivLike.injective b.symm)))

end Alg01SymmetricWitt.Witt.IsotropicExtension
