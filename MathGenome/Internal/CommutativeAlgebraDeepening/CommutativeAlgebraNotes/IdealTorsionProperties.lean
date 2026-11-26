import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Noetherian.Defs

/-! Left exactness and radical invariance of ideal torsion. -/

open CategoryTheory CategoryTheory.Limits

namespace CommutativeAlgebraNotes

universe v u

variable {R : Type u} [CommRing R]

/-- A short exact sequence remains exact at its first two terms after applying ideal torsion. -/
theorem idealTorsionFunctor_leftExact [IsNoetherianRing R] (I : Ideal R)
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    (S.map (idealTorsionFunctor I)).Exact ∧ Mono ((idealTorsionFunctor I).map S.f) := by
  have hf := hS.moduleCat_injective_f
  constructor
  · apply (ShortComplex.moduleCat_exact_iff _).2
    intro y hy
    change ↥(idealTorsion I S.X₂) at y
    change Ideal.primaryComponent.map I S.g.hom y = 0 at hy
    have hy' : S.g y.val = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (S.moduleCat_exact_iff.mp hS.exact) y.val hy'
    obtain ⟨n, hn, hann⟩ := (mem_idealTorsion I y.val).1 y.property
    have hxT : x ∈ idealTorsion I S.X₁ := (mem_idealTorsion I x).2
      ⟨n, hn, fun a ha => hf (by
        change S.f.hom (a • x) = S.f.hom 0
        rw [map_smul, map_zero]
        change a • S.f x = 0
        rw [hx]
        exact hann a ha)⟩
    exact ⟨⟨x, hxT⟩, Subtype.ext hx⟩
  · apply ConcreteCategory.mono_of_injective
    intro x x' h
    exact Subtype.ext (hf (congrArg Subtype.val h))

/-- Ideal torsion preserves finite limits. -/
instance idealTorsionFunctor_preservesFiniteLimits [IsNoetherianRing R] (I : Ideal R) :
    PreservesFiniteLimits (idealTorsionFunctor.{v} I) :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2
    (idealTorsionFunctor_leftExact I)

private theorem idealTorsion_le_of_le_radical [IsNoetherianRing R] {I J : Ideal R}
    (h : J ≤ I.radical) (M : Type v) [AddCommGroup M] [Module R M] :
    idealTorsion I M ≤ idealTorsion J M := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h J.fg_of_isNoetherianRing
  have hk' : J ^ (k + 1) ≤ I := (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk
  intro x hx
  obtain ⟨n, hn, hann⟩ := (mem_idealTorsion I x).1 hx
  refine (mem_idealTorsion J x).2 ⟨(k + 1) * n, Nat.mul_pos (Nat.succ_pos k) hn, ?_⟩
  intro a ha
  rw [pow_mul] at ha
  exact hann a (Ideal.pow_right_mono hk' n ha)

/-- Equal radicals give equal submodules of every module. -/
theorem idealTorsion_eq_of_radical_eq [IsNoetherianRing R] {I J : Ideal R}
    (h : I.radical = J.radical) (M : Type v) [AddCommGroup M] [Module R M] :
    idealTorsion I M = idealTorsion J M :=
  le_antisymm
    (idealTorsion_le_of_le_radical (Ideal.le_radical.trans_eq h.symm) M)
    (idealTorsion_le_of_le_radical (Ideal.le_radical.trans_eq h) M)

private def idealTorsionIsoApp [IsNoetherianRing R] {I J : Ideal R}
    (h : I.radical = J.radical) (M : ModuleCat.{v} R) :
    (idealTorsionFunctor I).obj M ≅ (idealTorsionFunctor J).obj M :=
  (LinearEquiv.ofEq _ _ (idealTorsion_eq_of_radical_eq h M)).toModuleIso

private theorem idealTorsionIsoApp_comp_inclusion [IsNoetherianRing R] {I J : Ideal R}
    (h : I.radical = J.radical) (M : ModuleCat.{v} R) :
    (idealTorsionIsoApp h M).hom ≫ (idealTorsionInclusion J).app M =
      (idealTorsionInclusion I).app M := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp]
  change (idealTorsion J M).subtype.comp
    (LinearEquiv.ofEq _ _ (idealTorsion_eq_of_radical_eq h M)).toLinearMap =
      (idealTorsion I M).subtype
  apply LinearMap.ext
  intro x
  exact LinearEquiv.coe_ofEq_apply (idealTorsion_eq_of_radical_eq h M) x

/-- For equal radicals the natural isomorphism identifies both inclusions into the identity. -/
theorem idealTorsionFunctor_inclusion_iso_of_radical_eq [IsNoetherianRing R] {I J : Ideal R}
    (h : I.radical = J.radical) :
    ∃ e : idealTorsionFunctor.{v} I ≅ idealTorsionFunctor.{v} J,
      e.hom ≫ idealTorsionInclusion J = idealTorsionInclusion I := by
  let e : idealTorsionFunctor.{v} I ≅ idealTorsionFunctor.{v} J :=
    NatIso.ofComponents (idealTorsionIsoApp h) (fun {_ N} f => by
      have : Mono ((idealTorsionInclusion J).app N) :=
        ConcreteCategory.mono_of_injective _ Subtype.val_injective
      apply (cancel_mono ((idealTorsionInclusion J).app N)).mp
      rw [Category.assoc, idealTorsionIsoApp_comp_inclusion, Category.assoc,
        (idealTorsionInclusion J).naturality, ← Category.assoc,
        idealTorsionIsoApp_comp_inclusion]
      exact (idealTorsionInclusion I).naturality f)
  refine ⟨e, ?_⟩
  apply NatTrans.ext
  funext M
  rw [NatTrans.comp_app]
  exact idealTorsionIsoApp_comp_inclusion h M

/-- The torsion functor for the zero ideal is the identity via its natural inclusion. -/
theorem idealTorsionInclusion_bot_isIso [IsNoetherianRing R] :
    IsIso (idealTorsionInclusion.{v} (⊥ : Ideal R)) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro M
  apply (ConcreteCategory.isIso_iff_bijective _).2
  refine ⟨Subtype.val_injective, fun x => ?_⟩
  refine ⟨⟨x, (mem_idealTorsion _ x).2 ⟨1, le_rfl, ?_⟩⟩, rfl⟩
  intro a ha
  have ha0 : a = 0 := by simpa only [pow_one, Submodule.mem_bot] using ha
  simp [ha0]

/-- The torsion functor for the unit ideal is a zero functor. -/
theorem idealTorsionFunctor_top_isZero [IsNoetherianRing R] :
    IsZero (idealTorsionFunctor.{v} (⊤ : Ideal R)) := by
  refine (Functor.isZero_iff _).2 fun M => ?_
  change IsZero (ModuleCat.of R (idealTorsion (⊤ : Ideal R) M))
  rw [ModuleCat.isZero_of_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun x => Subtype.ext ?_
  change x.val = (0 : M)
  obtain ⟨n, _, hn⟩ := (mem_idealTorsion (⊤ : Ideal R) (x : M)).1 x.property
  have hone := Ideal.pow_mem_pow (I := (⊤ : Ideal R)) (x := 1) (by simp) n
  simpa only [one_pow, one_smul] using hn (1 ^ n) hone

end CommutativeAlgebraNotes
