import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ArtinianSocleCriterion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.IdealTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualExactDetection
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ResidueHullArtinian
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Nakayama

/-! Artinianness of the residue-field hull and the socle criterion over a Noetherian local ring. -/

namespace CommutativeAlgebraNotes

open IsLocalRing AdvCommAlg.Depth

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The residue-field injective hull is Artinian over the given Noetherian local ring. -/
theorem residueHull_isArtinian [IsNoetherianRing R] (E : ResidueFieldEnvelope R) :
    IsArtinian R E.carrier :=
  residueHull_artinian E

/-- All elements of an Artinian module are killed by powers of the maximal ideal. -/
theorem idealTorsion_eq_top_of_isArtinian [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] [IsArtinian R T] :
    idealTorsion (maximalIdeal R) T = ⊤ := by
  apply top_unique
  intro x _
  let N : Submodule R T := Submodule.span R {x}
  let m := maximalIdeal R
  let chain : ℕ →o (Submodule R T)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual (m ^ n • N),
      fun _ _ h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes chain
  have hstable : m ^ n • N = m • (m ^ n • N) := by
    have h : m ^ n • N = m ^ (n + 1) • N := hn (n + 1) (Nat.le_succ n)
    simpa only [pow_succ', Submodule.mul_smul] using h
  have hfg : (m ^ n • N).FG :=
    Submodule.FG.smul (IsNoetherian.noetherian (m ^ n)) (Submodule.fg_span_singleton x)
  have hz : m ^ n • N = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m _ hfg hstable.le
      (by rw [jacobson_eq_maximalIdeal _ bot_ne_top])
  refine (mem_idealTorsion (maximalIdeal R) x).mpr ⟨n + 1, Nat.succ_pos n, ?_⟩
  intro a ha
  have ha' : a ∈ m ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) ha
  have hax : a • x ∈ m ^ n • N :=
    Submodule.smul_mem_smul ha' (Submodule.mem_span_singleton_self x)
  simpa only [hz, Submodule.mem_bot] using hax

/-- The socle is essential in every maximal-ideal power-torsion module. -/
theorem socle_essential_of_powerTorsion {T : Type u} [AddCommGroup T] [Module R T]
    (hT : idealTorsion (maximalIdeal R) T = ⊤) (N : Submodule R T) (hN : N ≠ ⊥) :
    N ⊓ Socle R T ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  have hxT : x ∈ idealTorsion (maximalIdeal R) T := hT.symm ▸ Submodule.mem_top
  obtain ⟨n, hpos, hn⟩ := (mem_idealTorsion (maximalIdeal R) x).mp hxT
  clear hpos
  induction n with
  | zero =>
    exact False.elim (hx0 (by simpa using hn 1 (by simp)))
  | succ n ih =>
    by_cases h : ∀ a ∈ (maximalIdeal R) ^ n, a • x = 0
    · exact ih h
    · push Not at h
      obtain ⟨a, ha, hax⟩ := h
      apply (N ⊓ Socle R T).ne_bot_iff.mpr
      refine ⟨a • x, ⟨N.smul_mem a hx, (mem_socle_iff _).mpr ?_⟩, hax⟩
      intro r hr
      rw [smul_smul]
      apply hn
      rw [pow_succ']
      exact Ideal.mul_mem_mul hr ha

/-- Finite socle dimension gives an embedding in that many copies of the residue-field hull. -/
theorem exists_residueHullPower_embedding (E : ResidueFieldEnvelope R)
    {T : Type u} [AddCommGroup T] [Module R T]
    (hT : idealTorsion (maximalIdeal R) T = ⊤)
    (hfin : FiniteDimensional (ResidueField R) (Socle R T)) :
    ∃ f : T →ₗ[R] (Fin (Module.finrank (ResidueField R) (Socle R T)) → E.carrier),
      Function.Injective f ∧ (Socle R T).map f = Socle R _ := by
  let k := ResidueField R
  let t := Module.finrank k (Socle R T)
  let e : Socle R T ≃ₗ[R] (Fin t → k) :=
    (Module.finBasis k (Socle R T)).equivFun.restrictScalars R
  let g : Socle R T →ₗ[R] (Fin t → E.carrier) :=
    LinearMap.pi fun i => E.inclusion.comp ((LinearMap.proj i).comp e.toLinearMap)
  let : Module.Injective R E.carrier := E.isEnvelope.injectiveModule
  obtain ⟨f, hf⟩ := Module.Injective.extension_property R (Fin t → E.carrier)
    (Socle R T) T (Socle R T).subtype (Socle R T).subtype_injective g
  have hcoord (x : Socle R T) (i : Fin t) : f x i = E.inclusion (e x i) :=
    congrFun (DFunLike.congr_fun hf x) i
  refine ⟨f, LinearMap.ker_eq_bot.mp ?_, ?_⟩
  · by_contra hker
    obtain ⟨x, ⟨hxKer, hxSocle⟩, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (socle_essential_of_powerTorsion hT f.ker hker)
    have hfx : f x = 0 := LinearMap.mem_ker.mp hxKer
    let z : Socle R T := ⟨x, hxSocle⟩
    have hz : e z = 0 := by
      funext i
      change e z i = 0
      apply E.isEnvelope.injective
      rw [← hcoord, map_zero]
      exact congrFun hfx i
    exact hx (congrArg Subtype.val (e.injective (hz.trans e.map_zero.symm)))
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      apply (mem_socle_iff _).mpr
      intro r hr
      rw [← f.map_smul, (mem_socle_iff _).mp hx r hr, map_zero]
    · intro y hy
      have h (i : Fin t) : ∃ a : k, E.inclusion a = y i := by
        have hi : y i ∈ Socle R E.carrier := (mem_socle_iff _).mpr fun r hr =>
          congrFun ((mem_socle_iff _).mp hy r hr) i
        rwa [residueFieldEnvelope_socle E] at hi
      choose a ha using h
      let z := e.symm a
      refine ⟨z.val, z.property, ?_⟩
      funext i
      rw [hcoord z i, e.apply_symm_apply]
      exact ha i

/-- A maximal-ideal power-torsion module is Artinian exactly when its socle is finite-dimensional. -/
theorem isArtinian_iff_socle_finiteDimensional [IsNoetherianRing R]
    {T : Type u} [AddCommGroup T] [Module R T]
    (hT : idealTorsion (maximalIdeal R) T = ⊤) :
    IsArtinian R T ↔ FiniteDimensional (ResidueField R) (Socle R T) := by
  constructor
  · intro h
    have hSocle : IsArtinian (ResidueField R) (Socle R T) :=
      isArtinian_of_tower R (inferInstance : IsArtinian R (Socle R T))
    exact (IsSemisimpleModule.finite_tfae.out 3 1).mp hSocle
  · intro h
    obtain ⟨E⟩ := residueFieldEnvelope_exists R
    let : IsArtinian R E.carrier := residueHull_isArtinian E
    obtain ⟨f, hf, _⟩ := exists_residueHullPower_embedding E hT h
    exact isArtinian_of_injective f hf

end CommutativeAlgebraNotes
