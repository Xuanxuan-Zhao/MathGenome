import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.LeftExact

/-! Proposition M01: exactness and detection by the Matlis dual.
The proofs apply to every commutative local ring, including the Noetherian rings of Chapter 3. -/

noncomputable section

open CategoryTheory

namespace CommutativeAlgebraNotes

universe u v w z

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The socle is the image of the given inclusion of the residue field. -/
theorem residueFieldEnvelope_socle (E : ResidueFieldEnvelope R) :
    AdvCommAlg.Depth.Socle R E.carrier = LinearMap.range E.inclusion := by
  apply le_antisymm
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact (LinearMap.range E.inclusion).zero_mem
    let N : Submodule R E.carrier := Submodule.span R {x}
    have hxN : x ∈ N := Submodule.mem_span_singleton_self x
    have hN : N ≠ ⊥ := fun h => hx0 (by simpa [h] using hxN)
    obtain ⟨y, ⟨hyN, hyRange⟩, hy⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (residueFieldEnvelope_essential E N hN)
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hyN
    have hr : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp
      (fun hm => hy ((mem_socle_iff x).mp hx r hm))
    obtain ⟨a, rfl⟩ := hr
    have h := (LinearMap.range E.inclusion).smul_mem (↑a⁻¹ : R) hyRange
    simpa [smul_smul] using h
  · rintro _ ⟨a, rfl⟩
    rw [mem_socle_iff]
    intro r hr
    have hz : r • a = 0 := by
      change IsLocalRing.residue R r * a = 0
      rw [(IsLocalRing.residue_eq_zero_iff r).mpr hr, zero_mul]
    rw [← E.inclusion.map_smul, hz, map_zero]

/-- The displayed residue-field inclusion identifies the residue field with the socle. -/
theorem residueFieldEnvelope_socle_equiv (E : ResidueFieldEnvelope R) :
    ∃ e : IsLocalRing.ResidueField R ≃ₗ[IsLocalRing.ResidueField R]
        AdvCommAlg.Depth.Socle R E.carrier,
      ∀ a, (e a).val = E.inclusion a := by
  let e := (LinearEquiv.ofInjective E.inclusion E.isEnvelope.injective).trans
    (LinearEquiv.ofEq _ _ (residueFieldEnvelope_socle E).symm)
  exact ⟨e.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := R)), fun _ => rfl⟩

theorem exists_residueFieldEnvelope_socle (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ E : ResidueFieldEnvelope R,
      AdvCommAlg.Depth.Socle R E.carrier = LinearMap.range E.inclusion := by
  obtain ⟨E⟩ := residueFieldEnvelope_exists R
  exact ⟨E, residueFieldEnvelope_socle E⟩

variable (E : ResidueFieldEnvelope R)
variable {X : Type v} {Y : Type w} {Z : Type z}
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]

/-- Every functional extends along an injective linear map. -/
theorem matlisDualMap_surjective (f : X →ₗ[R] Y) (hf : Function.Injective f) :
    Function.Surjective (matlisDualMap E f) := by
  let _ : Module.Injective R E.carrier := E.isEnvelope.injectiveModule
  intro g
  exact Module.Injective.extension_property R E.carrier X Y f hf g

theorem matlisDualMap_shortExact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective (matlisDualMap E g) ∧
    Function.Exact (matlisDualMap E g) (matlisDualMap E f) ∧
    Function.Surjective (matlisDualMap E f) :=
  ⟨LinearMap.lcomp_injective_of_surjective g hg,
    LinearMap.exact_lcomp_of_exact_of_surjective E.carrier hex hg,
    matlisDualMap_surjective E f hf⟩

/-- Matlis duality sends each short exact sequence to a reversed short exact sequence. -/
theorem matlisDual_shortExact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.op.map (MatlisDual E)).ShortExact := by
  obtain ⟨hi, he, hs⟩ := matlisDualMap_shortExact E S.f.hom S.g.hom
    hS.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
    hS.moduleCat_surjective_g
  exact ModuleCat.shortComplex_shortExact _ he hi hs

/-- A nonzero vector is detected by a functional into the residue-field hull. -/
theorem matlisDual_separates (x : X) (hx : x ≠ 0) :
    ∃ f : MatlisDualModule E X, f x ≠ 0 := by
  let cyclicMap := (LinearMap.toSpanSingleton R X x).rangeRestrict
  let residue := Algebra.linearMap R (IsLocalRing.ResidueField R)
  have hproper : (LinearMap.ker cyclicMap : Ideal R) ≠ ⊤ := by
    intro h
    have h1 : 1 ∈ LinearMap.ker cyclicMap := h.symm ▸ Submodule.mem_top
    have hs1 := congrArg Subtype.val (LinearMap.mem_ker.mp h1)
    exact hx (by simpa [cyclicMap] using hs1)
  have hker : LinearMap.ker cyclicMap ≤ LinearMap.ker residue := by
    intro r hr
    exact LinearMap.mem_ker.mpr <| (IsLocalRing.residue_eq_zero_iff r).mpr
      (IsLocalRing.le_maximalIdeal hproper hr)
  let quotientMap :=
    cyclicMap.liftOfSurjective (LinearMap.surjective_rangeRestrict _) ⟨residue, hker⟩
  obtain ⟨f, hf⟩ := matlisDualMap_surjective E _ (Submodule.subtype_injective _)
    (E.inclusion.comp quotientMap)
  have hf1 := DFunLike.congr_fun hf (cyclicMap 1)
  change f ((cyclicMap 1).val) = E.inclusion (quotientMap (cyclicMap 1)) at hf1
  have hq1 : quotientMap (cyclicMap 1) = residue 1 :=
    LinearMap.equivOfSurjective_apply (LinearMap.surjective_rangeRestrict _) hker
  have hfx : f x = E.inclusion 1 := by simpa [cyclicMap, residue, hq1] using hf1
  refine ⟨f, ?_⟩
  rw [hfx, ← E.inclusion.map_zero]
  exact fun h => one_ne_zero (E.isEnvelope.injective h)

theorem matlisDual_nontrivial_iff (X : Type v) [AddCommGroup X] [Module R X] :
    Nontrivial (MatlisDualModule E X) ↔ Nontrivial X := by
  constructor
  · intro h
    by_contra! hX
    let _ := hX
    obtain ⟨f, g, hfg⟩ := h
    exact hfg (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  · intro h
    let _ := h
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨f, hf⟩ := matlisDual_separates E x hx
    exact ⟨⟨f, 0, fun h0 => hf (DFunLike.congr_fun h0 x)⟩⟩

theorem matlisEvaluation_injective (X : Type v) [AddCommGroup X] [Module R X] :
    Function.Injective (matlisEvaluation E X) := by
  intro x y h
  by_contra hxy
  obtain ⟨f, hf⟩ := matlisDual_separates E (x - y) (sub_ne_zero.mpr hxy)
  exact hf (by rw [f.map_sub, sub_eq_zero]; exact DFunLike.congr_fun h f)

end CommutativeAlgebraNotes
