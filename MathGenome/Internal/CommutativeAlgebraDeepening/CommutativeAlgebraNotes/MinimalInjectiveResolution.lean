import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MinimalInjectiveResolution
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MinimalInjectiveResolutionSocles
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveHullTruncations
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ArtinianSocleCriterion

/-! Minimal injective resolutions and the maximal-ideal torsion of injective modules. -/

noncomputable section

namespace CommutativeAlgebraNotes

open CategoryTheory IsLocalRing AdvCommAlg.Depth
open MinimalInjectiveResolutionSoclesSpecs (residueObject)

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Every module has a minimal injective resolution with zero residue-field Hom differentials. -/
theorem exists_minimalInjectiveResolution_with_zero_residueHom_differential
    (X : ModuleCat.{u} R) :
    ∃ J : MinimalInjectiveResolution X,
      ∀ (i j : ℕ) (f : residueObject R ⟶ J.toInjectiveResolution.cocomplex.X i),
        f ≫ J.toInjectiveResolution.cocomplex.d i j = 0 := by
  obtain ⟨J⟩ := exists_minimalInjectiveResolution X
  exact ⟨J, minimalInjectiveResolution_residueHom_differential_zero J⟩

omit [IsNoetherianRing R] in
private def socleTorsionEquiv (J : Type u) [AddCommGroup J] [Module R J] :
    Socle R (idealTorsion (maximalIdeal R) J) ≃ₗ[ResidueField R] Socle R J := by
  let T := idealTorsion (maximalIdeal R) J
  let f : Socle R T →ₗ[R] Socle R J :=
    (T.subtype.comp (Socle R T).subtype).codRestrict _ fun x =>
      (mem_socle_iff _).mpr fun a ha =>
        congrArg Subtype.val ((mem_socle_iff x.val).mp x.property a ha)
  refine (LinearEquiv.ofBijective f ⟨?_, ?_⟩).extendScalarsOfSurjective
    (residue_surjective (R := R))
  · intro x y h
    have hval : x.val.val = y.val.val := congrArg (fun z : Socle R J => z.val) h
    exact Subtype.ext (Subtype.ext hval)
  · intro y
    have hy : ∀ a ∈ maximalIdeal R, a • y.val = 0 := (mem_socle_iff y.val).mp y.property
    let x : T := ⟨y.val, (mem_idealTorsion (maximalIdeal R) y.val).mpr
      ⟨1, le_rfl, fun a ha => hy a (by simpa only [pow_one] using ha)⟩⟩
    exact ⟨⟨x, (mem_socle_iff x).mpr fun a ha => Subtype.ext (hy a ha)⟩, Subtype.ext rfl⟩

omit [IsNoetherianRing R] in
private theorem torsionModule_is_powerTorsion (J : Type u) [AddCommGroup J] [Module R J] :
    idealTorsion (maximalIdeal R) (idealTorsion (maximalIdeal R) J) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, hn, h⟩ := (mem_idealTorsion (maximalIdeal R) x.val).mp x.property
  exact (mem_idealTorsion (maximalIdeal R) x).mpr
    ⟨n, hn, fun a ha => Subtype.ext (h a ha)⟩

private theorem hullPower_is_powerTorsion (E : ResidueFieldEnvelope R) (t : ℕ) :
    idealTorsion (maximalIdeal R) (Fin t → E.carrier) = ⊤ := by
  classical
  apply top_unique
  intro x _
  choose n _ hx using fun i => exists_mem_hullTruncation E (x i)
  refine (mem_idealTorsion (maximalIdeal R) x).mpr
    ⟨Finset.univ.sup n + 1, Nat.succ_pos _, fun a ha => ?_⟩
  funext i
  have hi : n i ≤ Finset.univ.sup n + 1 :=
    (Finset.le_sup (f := n) (Finset.mem_univ i)).trans (Nat.le_succ _)
  exact (Submodule.mem_torsionBySet_iff _ _).mp (hx i)
    ⟨a, Ideal.pow_le_pow_right hi ha⟩

/-- The maximal-ideal torsion in an injective module is a power of the residue-field
hull when its socle is finite-dimensional. The exponent is the dimension of that socle. -/
theorem injective_torsion_equiv_hullPower (E : ResidueFieldEnvelope R)
    {J : Type u} [AddCommGroup J] [Module R J]
    (hJ : Module.Injective R J) (hfin : FiniteDimensional (ResidueField R) (Socle R J)) :
    Nonempty (idealTorsion (maximalIdeal R) J ≃ₗ[R]
      (Fin (Module.finrank (ResidueField R) (Socle R J)) → E.carrier)) := by
  let T := idealTorsion (maximalIdeal R) J
  let e := socleTorsionEquiv (R := R) J
  let : FiniteDimensional (ResidueField R) (Socle R T) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  obtain ⟨f, hf, hs⟩ := exists_residueHullPower_embedding E (torsionModule_is_powerTorsion J)
    (inferInstance : FiniteDimensional (ResidueField R) (Socle R T))
  have hT : Module.Injective R T := idealTorsion_injective (maximalIdeal R) hJ
  obtain ⟨p, hp⟩ := hT.out f hf (LinearMap.id : T →ₗ[R] T)
  have hker : p.ker = ⊥ := by
    by_contra h
    obtain ⟨x, ⟨hxker, hxsoc⟩, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (socle_essential_of_powerTorsion (hullPower_is_powerTorsion E _) p.ker h)
    rw [← hs] at hxsoc
    obtain ⟨y, _, rfl⟩ := hxsoc
    have hy : y = 0 := (hp y).symm.trans (LinearMap.mem_ker.mp hxker)
    exact hx0 ((congrArg f hy).trans f.map_zero)
  have hp_inj := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective f := fun x => ⟨p x, hp_inj (hp (p x))⟩
  have hdim : Module.finrank (ResidueField R) (Socle R T) =
      Module.finrank (ResidueField R) (Socle R J) := e.finrank_eq
  rw [← hdim]
  exact ⟨LinearEquiv.ofBijective f ⟨hf, hsurj⟩⟩

end CommutativeAlgebraNotes
