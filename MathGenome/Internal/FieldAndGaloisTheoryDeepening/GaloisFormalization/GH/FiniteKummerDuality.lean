import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.FiniteKummerDuality
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KummerRadicals
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-! Finite Kummer correspondence and its evaluation pairing. -/

namespace GaloisFormalization.GH.FiniteKummerDuality

open Specs.GaloisFormalization.GH.KummerCoefficients
open Specs.GaloisFormalization.GH.FiniteKummerDuality
open Specs.GaloisFormalization.GH.KummerRadicals (HasKummerRatios)
open Specs.GaloisFormalization.GH.KrullLayers (restrict)
open KummerRadicals

universe u v

section Characters

variable {G : Type*} {S : Type v} [Monoid G] [Field S] {m : ℕ}

/-- An (m)-torsion source forces all unit-valued characters to land in the roots of unity. -/
private def rootCharactersEquivUnits (hpow : ∀ g : G, g ^ m = 1) :
    (G →* Roots S m) ≃* (G →* Sˣ) where
  toFun χ := (Roots S m).subtype.comp χ
  invFun χ := χ.codRestrict (Roots S m) fun g =>
    (mem_rootsOfUnity m (χ g)).mpr (by rw [← map_pow, hpow, map_one])
  left_inv χ := MonoidHom.ext fun g => Subtype.ext rfl
  right_inv χ := MonoidHom.ext fun _ => rfl
  map_mul' _ _ := MonoidHom.ext fun _ => rfl

end Characters

local instance finiteRootCharacters {G : Type*} {S : Type*} [Monoid G] [Field S] [Finite G]
    {m : ℕ} [NeZero m] : Finite (G →* Roots S m) :=
  Finite.of_injective (fun χ : G →* Roots S m => (χ : G → Roots S m)) DFunLike.coe_injective

section FiniteCharacters

variable {G : Type*} {S : Type v} [CommGroup G] [Finite G] [Field S]
  {m : ℕ} [NeZero m] [HasEnoughRootsOfUnity S m]

private theorem card_rootCharacters (hpow : ∀ g : G, g ^ m = 1) :
    Nat.card (G →* Roots S m) = Nat.card G := by
  let : HasEnoughRootsOfUnity S (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd S (Monoid.exponent_dvd_of_forall_pow_eq_one hpow)
  exact (Nat.card_congr (rootCharactersEquivUnits hpow).toEquiv).trans
    (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G S)

private theorem eq_one_of_rootCharacters (hpow : ∀ g : G, g ^ m = 1) {g : G}
    (h : ∀ χ : G →* Roots S m, χ g = 1) : g = 1 := by
  let : HasEnoughRootsOfUnity S (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd S (Monoid.exponent_dvd_of_forall_pow_eq_one hpow)
  by_contra hg
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G S hg
  obtain ⟨ψ, rfl⟩ := (rootCharactersEquivUnits hpow).surjective χ
  exact hχ (congrArg Subtype.val (h ψ))

end FiniteCharacters

variable {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
  {m : ℕ}

private theorem powerClass_pow_eq_one (d : PowerClasses k m) : d ^ m = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (powerMap k m).range d
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (a ^ m)).mpr ⟨a, rfl⟩

private theorem exists_root_in_radicalLayer (hm : 1 ≤ m) (hu : IsUnit (m : k))
    {D : Subgroup (PowerClasses k m)} {L : FiniteGaloisIntermediateField k S}
    (hL : L.toIntermediateField = radicalField D) {a : kˣ} (ha : powerClass k m a ∈ D) :
    ∃ α : Lˣ, α ^ m = Units.map (algebraMap k L) a := by
  obtain ⟨β, hβ⟩ := KummerCoefficients.powerMap_surjective k S hm hu
    (Units.map (algebraMap k S) a)
  have hmem : (β : S) ∈ L.toIntermediateField := by
    rw [hL]
    exact IntermediateField.subset_adjoin k _ ⟨a, β, ha, hβ, rfl⟩
  let x : L := ⟨β, hmem⟩
  let α : Lˣ := Units.mk0 x (fun hx => β.ne_zero (congrArg Subtype.val hx))
  have hα : Units.map (algebraMap L S).toMonoidHom α = β := Units.ext rfl
  have hscalar : Units.map (algebraMap L S).toMonoidHom
      (Units.map (algebraMap k L).toMonoidHom a) = Units.map (algebraMap k S).toMonoidHom a := by
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply k L S (a : k)).symm
  refine ⟨α, Units.map_injective (f := (algebraMap L S).toMonoidHom)
    (algebraMap L S).injective ?_⟩
  change Units.map (algebraMap L S).toMonoidHom (α ^ m) =
    Units.map (algebraMap L S).toMonoidHom (Units.map (algebraMap k L).toMonoidHom a)
  rw [map_pow, hα, hscalar]
  exact hβ

section FieldCharacters

variable [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] [NeZero m] [HasEnoughRootsOfUnity S m]
  {e : PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m)}

/-- Character separation recovers the layer from the classes that become powers in it. -/
private theorem radicalField_of_classes (hm : 1 ≤ m) (hu : IsUnit (m : k))
    (hμ : rootsInBase k S m) (he : HasKummerRatios e)
    (L : AbelianKummerLayers k S m) :
    Finite (classesOfField m L.val.toIntermediateField) ∧
      radicalField (classesOfField m L.val.toIntermediateField) = L.val.toIntermediateField := by
  let C := classesOfField m L.val.toIntermediateField
  let : CommGroup Gal(L.val/k) := { toGroup := inferInstance, mul_comm := L.property.1 }
  obtain ⟨hC, eL, heL, _⟩ := classesOfFieldCharacters hm hu hμ he L.val
  have hker : (restrict L.val).toMonoidHom.ker = L.val.toIntermediateField.fixingSubgroup :=
    KrullLayers.restrict_ker L.val
  have hfix : characterKernelIntersection C e = L.val.toIntermediateField.fixingSubgroup := by
    ext σ
    change σ ∈ (⨅ d : C, (e d).toMonoidHom.ker) ↔
      σ ∈ L.val.toIntermediateField.fixingSubgroup
    rw [Subgroup.mem_iInf, ← hker, MonoidHom.mem_ker]
    constructor
    · intro h
      apply eq_one_of_rootCharacters (S := S) L.property.2
      intro χ
      obtain ⟨d, rfl⟩ := eL.surjective χ
      exact (heL d σ).trans (h d)
    · intro h d
      exact (hC d).mp d.property (hker ▸ MonoidHom.mem_ker.mpr h)
  refine ⟨Finite.of_injective eL eL.injective, ?_⟩
  calc
    radicalField C = IntermediateField.fixedField (characterKernelIntersection C e) :=
      (radicalFieldFixedField hm hu he C).2
    _ = L.val.toIntermediateField := by rw [hfix, InfiniteGalois.fixedField_fixingSubgroup]

/-- The faithful pairing on a radical layer exhausts the characters in both variables. -/
private theorem duality_of_radicalField (hm : 1 ≤ m) (hu : IsUnit (m : k))
    (hμ : rootsInBase k S m) (he : HasKummerRatios e)
    (D : Subgroup (PowerClasses k m)) [Finite D] (L : FiniteGaloisIntermediateField k S)
    (hL : L.toIntermediateField = radicalField D) :
    D = classesOfField m L.toIntermediateField ∧
      ∃ (eG : Gal(L/k) ≃* (D →* Roots S m)) (eD : D ≃* (Gal(L/k) →* Roots S m)),
        (∀ (g : Gal(L/k)) (d : D), eG g d = eD d g) ∧
        ∀ (d : D) (a : kˣ), powerClass k m a = d.val →
          ∀ (α : Lˣ), α ^ m = Units.map (algebraMap k L) a →
            ∀ g : Gal(L/k), (eG g d : Sˣ) =
              Units.map (algebraMap L S) ((g • α) / α) := by
  let C := classesOfField m L.toIntermediateField
  obtain ⟨hC, eL, heL, hratio⟩ := classesOfFieldCharacters hm hu hμ he L
  obtain ⟨⟨F, hF, hFeval⟩, hcomm, hpow⟩ := radicalGaloisGroup hm hu he D L hL
  let : CommGroup Gal(L/k) := { toGroup := inferInstance, mul_comm := hcomm }
  let : Finite C := Finite.of_injective eL eL.injective
  have hDC : D ≤ C := by
    intro a ha
    apply (hC a).mpr
    intro σ hσ
    rw [hL, (radicalFieldFixedField hm hu he D).1] at hσ
    exact Subgroup.mem_iInf.mp hσ ⟨a, ha⟩
  let χ : D →* (Gal(L/k) →* Roots S m) := eL.toMonoidHom.comp (Subgroup.inclusion hDC)
  let f : Gal(L/k) →* (D →* Roots S m) :=
    { toFun := fun g =>
        { toFun := fun d => χ d g
          map_one' := DFunLike.congr_fun (map_one χ) g
          map_mul' := fun d₁ d₂ => DFunLike.congr_fun (map_mul χ d₁ d₂) g }
      map_one' := MonoidHom.ext fun d => map_one (χ d)
      map_mul' := fun g h => MonoidHom.ext fun d => map_mul (χ d) g h }
  have hf : Function.Injective f := by
    have hagree (g : Gal(L/k)) (d : D) : F g d = f g d := by
      obtain ⟨σ, rfl⟩ := KrullLayers.restrict_surjective L g
      exact (hFeval σ d).trans (heL (Subgroup.inclusion hDC d) σ).symm
    intro g h hgh
    apply hF
    funext d
    rw [hagree g d, hagree h d, hgh]
  have hcardG : Nat.card (Gal(L/k) →* Roots S m) = Nat.card Gal(L/k) :=
    card_rootCharacters hpow
  have hcardD : Nat.card (D →* Roots S m) = Nat.card D := by
    apply card_rootCharacters (G := D) (S := S)
    intro d
    exact Subtype.ext (powerClass_pow_eq_one d.val)
  have hcardC : Nat.card C = Nat.card Gal(L/k) :=
    (Nat.card_congr eL.toEquiv).trans hcardG
  have hEq : D = C := Subgroup.eq_of_le_of_card_ge hDC (calc
    Nat.card C = Nat.card Gal(L/k) := hcardC
    _ ≤ Nat.card (D →* Roots S m) := Nat.card_le_card_of_injective f hf
    _ = Nat.card D := hcardD)
  have hcard : Nat.card D = Nat.card Gal(L/k) := hEq.symm ▸ hcardC
  have hfbij := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, hcard.symm.trans hcardD.symm⟩
  have hχbij := (Nat.bijective_iff_injective_and_card χ).mpr
    ⟨eL.injective.comp (Subgroup.inclusion_injective hDC), hcard.trans hcardG.symm⟩
  refine ⟨hEq, MulEquiv.ofBijective f hfbij, MulEquiv.ofBijective χ hχbij, fun _ _ => rfl, ?_⟩
  intro d a hda α hα g
  have ha : powerClass k m a ∈ C := hda.symm ▸ hDC d.property
  have hd : Subgroup.inclusion hDC d = ⟨powerClass k m a, ha⟩ := Subtype.ext hda.symm
  change (eL (Subgroup.inclusion hDC d) g : Sˣ) = _
  rw [hd]
  exact hratio a α hα ha g

end FieldCharacters

/-- The finite Kummer correspondence on the chosen separable closure. -/
theorem finiteKummerCorrespondence : FiniteKummerCorrespondence.{u,v} := by
  intro k S _ _ _ _ m hm hu hμ
  classical
  let : TopologicalSpace Sˣ := ⊥
  let : DiscreteTopology Sˣ := discreteTopology_bot _
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let : HasEnoughRootsOfUnity S m :=
    HasEnoughRootsOfUnity.of_card_le (KummerCoefficients.roots_card k S hm hu).ge
  obtain ⟨e, he⟩ := existsKummerCharacterEquiv hm hu hμ
  have hexists (D : FinitePowerSubgroups k m) :
      ∃ L : AbelianKummerLayers k S m, L.val.toIntermediateField = radicalField D.val := by
    let : Finite D.val := D.property
    obtain ⟨_, _, L, hL⟩ := radicalFieldFiniteGalois hm hu he D.val
    exact ⟨⟨L, (radicalGaloisGroup hm hu he D.val L hL).2⟩, hL⟩
  let toLayer (D : FinitePowerSubgroups k m) := (hexists D).choose
  let toClasses (L : AbelianKummerLayers k S m) : FinitePowerSubgroups k m :=
    ⟨classesOfField m L.val.toIntermediateField, (radicalField_of_classes hm hu hμ he L).1⟩
  let corr : FinitePowerSubgroups k m ≃ AbelianKummerLayers k S m :=
    { toFun := toLayer
      invFun := toClasses
      left_inv := fun D => by
        let : Finite D.val := D.property
        apply Subtype.ext
        exact (duality_of_radicalField hm hu hμ he D.val (toLayer D).val
          (hexists D).choose_spec).1.symm
      right_inv := fun L => Subtype.ext (FiniteGaloisIntermediateField.val_injective
        ((hexists (toClasses L)).choose_spec.trans (radicalField_of_classes hm hu hμ he L).2)) }
  exact ⟨corr, fun D => (hexists D).choose_spec, fun _ => rfl⟩

/-- The two character equivalences are evaluations of the same root ratio. -/
theorem perfectRadicalPairing : PerfectRadicalPairing.{u,v} := by
  intro k S _ _ _ _ m hm hu hμ D _ L hL
  let : TopologicalSpace Sˣ := ⊥
  let : DiscreteTopology Sˣ := discreteTopology_bot _
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let : HasEnoughRootsOfUnity S m :=
    HasEnoughRootsOfUnity.of_card_le (KummerCoefficients.roots_card k S hm hu).ge
  obtain ⟨e, he⟩ := existsKummerCharacterEquiv hm hu hμ
  obtain ⟨_, eG, eD, heval, hratio⟩ := duality_of_radicalField hm hu hμ he D L hL
  exact ⟨eG, eD, heval, fun d a ha =>
    ⟨exists_root_in_radicalLayer hm hu hL (ha.symm ▸ d.property), hratio d a ha⟩⟩

end GaloisFormalization.GH.FiniteKummerDuality
