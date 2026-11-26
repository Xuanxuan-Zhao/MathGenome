import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalQuotientAdjunction
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualFunctor
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyBaseChange
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.LinearAlgebra.Isomorphisms
import Batteries.Tactic.OpenPrivate

/-! Coinduction along a local quotient and its Čech comparison. -/

noncomputable section

open CategoryTheory
open ModuleCat (restrictScalars coextendScalars)
open IsLocalRing (ResidueField maximalIdeal)

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.LocalQuotientAdjunction

universe u

variable {S R : Type u} [CommRing S] [CommRing R]

/-- Evaluation at one, linear for the action by precomposition on the restricted Hom. -/
abbrev coinductionAdjunction : AdjunctionType.{u} := @adjunction

theorem coinductionAdjunction_formulas : AdjunctionFormulas.{u} := by
  intro S R _ _ f X J
  exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem coinductionAdjunction_natural : AdjunctionNaturality.{u} := by
  intro S R _ _ f X Y J K a b g
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- Restriction preserves monomorphisms, so its right adjoint preserves injectives. -/
theorem coinduction_injective : CoinductionInjective.{u} := by
  intro S R _ _ f J h
  exact (ModuleCat.restrictCoextendScalarsAdj f).map_injective J h

private theorem evaluateOne_eq (f : S →+* R) (J : ModuleCat.{u} S)
    (g : (coextendScalars f).obj J) :
    evaluateOne f J g = g (1 : R) := rfl

private def regularRestriction (f : S →+* R) :
    S →ₗ[S] (restrictScalars f).obj (ModuleCat.of R R) where
  toFun := f
  map_add' := f.map_add
  map_smul' s t := f.map_mul s t

private theorem coinduced_apply_image (f : S →+* R) (J : ModuleCat.{u} S)
    (g : (coextendScalars f).obj J) (s : S) : g (f s) = s • g (1 : R) := by
  let l := ModuleCat.CoextendScalars.equiv f J g
  have h := l.map_smul s (1 : R)
  calc
    g (f s) = g (f s * 1) := congrArg (fun r : R => g r) (mul_one (f s)).symm
    _ = s • g (1 : R) := h

private theorem evaluateOne_injective (f : S →+* R) (hf : Function.Surjective f)
    (J : ModuleCat.{u} S) : Function.Injective (evaluateOne f J) := by
  intro g h he
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro r
  obtain ⟨s, rfl⟩ := hf (show R from r)
  change (show (coextendScalars f).obj J from g) (f s) =
    (show (coextendScalars f).obj J from h) (f s)
  rw [coinduced_apply_image, coinduced_apply_image, ← evaluateOne_eq f J g,
    ← evaluateOne_eq f J h, he]

/-- Evaluation realizes precisely the vectors annihilated by the kernel. -/
theorem coinduction_evaluation_annihilator : EvaluationAnnihilator.{u} := by
  intro S R _ _ f hf J
  have hmem (g : (coextendScalars f).obj J) : evaluateOne f J g ∈ kernelAnnihilator f J := by
    apply (Submodule.mem_torsionBySet_iff _ _).mpr
    rintro ⟨s, hs⟩
    erw [evaluateOne_eq, ← coinduced_apply_image, RingHom.mem_ker.mp hs]
    exact (ModuleCat.CoextendScalars.equiv f J g).map_zero
  let e := (evaluateOne f J).hom.codRestrict _ hmem
  have he : Function.Bijective e := by
    refine ⟨?_, ?_⟩
    · intro g h he
      exact evaluateOne_injective f hf J (congrArg Subtype.val he)
    · intro z
      let l : S →ₗ[S] J := LinearMap.toSpanSingleton S J z.val
      have hl : LinearMap.ker (regularRestriction f) ≤ LinearMap.ker l := by
        intro s hs
        change f s = 0 at hs
        exact (Submodule.mem_torsionBySet_iff _ _).mp z.property ⟨s, RingHom.mem_ker.mpr hs⟩
      have hs : Function.Surjective (regularRestriction f) := hf
      let g := (ModuleCat.CoextendScalars.equiv f J).symm
        ((regularRestriction f).liftOfSurjective hs ⟨l, hl⟩)
      refine ⟨g, Subtype.ext ?_⟩
      change g (1 : R) = z.val
      rw [show (1 : R) = regularRestriction f 1 from (f.map_one).symm]
      exact (LinearMap.equivOfSurjective_apply hs hl (m := 1)).trans (one_smul S z.val)
  let E := LinearEquiv.ofBijective e he
  exact ⟨E, fun _ => rfl, fun s g => E.map_smul s g⟩

section Complexes

open CochainComplex HomComplex

/-- The ordinary signed Hom over the source ring with the target action on its argument. -/
abbrev restrictedLinearHomComplex : RestrictedHomComplexType.{u} := @restrictedHomComplex

/-- The degreewise linear adjunction for arbitrary source and target complexes. -/
def coinductionCochainEquiv (f : S →+* R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (V : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    (linearHomComplex R U (CoinducedComplex f V)).X n ≃ₗ[R]
      (restrictedLinearHomComplex f U V).X n where
  toFun z := Cochain.mk fun p q h => coinductionAdjunction f (U.X p) (V.X q) (z.v p q h)
  invFun z := Cochain.mk fun p q h => (coinductionAdjunction f (U.X p) (V.X q)).symm (z.v p q h)
  left_inv _ := Cochain.ext _ _ fun p q _ => (coinductionAdjunction f (U.X p) (V.X q)).symm_apply_apply _
  right_inv _ := Cochain.ext _ _ fun p q _ => (coinductionAdjunction f (U.X p) (V.X q)).apply_symm_apply _
  map_add' _ _ := Cochain.ext _ _ fun p q _ => (coinductionAdjunction f (U.X p) (V.X q)).map_add _ _
  map_smul' _ _ := Cochain.ext _ _ fun p q _ => (coinductionAdjunction f (U.X p) (V.X q)).map_smul _ _

private theorem coinductionCochainEquiv_δ (f : S →+* R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (V : CochainComplex (ModuleCat.{u} S) ℤ)
    (n m : ℤ) (z : (linearHomComplex R U (CoinducedComplex f V)).X n) :
    coinductionCochainEquiv f U V m ((linearHomComplex R U (CoinducedComplex f V)).d n m z) =
      (restrictedLinearHomComplex f U V).d n m (coinductionCochainEquiv f U V n z) := by
  apply Cochain.ext
  intro p q hpq
  change coinductionAdjunction f (U.X p) (V.X q) ((δ n m z).v p q hpq) =
    (δ n m (coinductionCochainEquiv f U V n z)).v p q hpq
  simp only [δ, Cochain.mk_v, Functor.mapHomologicalComplex_obj_d, map_add, Units.smul_def, map_zsmul]
  rfl

/-- Coinduction adjunction on the signed Hom complexes, for arbitrary cochain complexes. -/
def coinductionHomComplexIso (f : S →+* R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (V : CochainComplex (ModuleCat.{u} S) ℤ) :
    linearHomComplex R U (CoinducedComplex f V) ≅ restrictedLinearHomComplex f U V :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (coinductionCochainEquiv f U V n).toModuleIso)
    (fun n m _ => ModuleCat.hom_ext (LinearMap.ext fun z => (coinductionCochainEquiv_δ f U V n m z).symm))

theorem coinductionCochainAdjunction : CochainAdjunction.{u} := by
  intro S R _ _ f U V
  exact ⟨coinductionHomComplexIso f U V, fun _ _ _ _ _ => rfl⟩

end Complexes

section Cech

open HomologicalComplex MonoidalCategory

open private rowFunctor rowIso from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison

open private restrictCoefficients mapHomology span_map_list from
  MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyBaseChange

/-- The actual augmentations and differentials are compared for the given list. -/
theorem localQuotient_cech_restriction : CechRestriction.{u} := by
  intro S R _ _ f rs
  exact ⟨restrictCoefficients f rs⟩

private theorem cechCohomology_linear (rs : List R) (q : ℤ) :
    (Specs.CommutativeAlgebraNotes.CechGeneratorIndependence.cechCohomology rs q).Linear R := by
  let H := homologyFunctor (ModuleCat.{u} R) (.up ℤ) q
  let Q := shortComplexFunctor (ModuleCat.{u} R) (.up ℤ) q
  let K := CechComplex rs
  let : (rowFunctor K).Linear R := ⟨fun g r => by
    apply HomologicalComplex.hom_ext
    intro i
    exact MonoidalLinear.whiskerLeft_smul (K.X i) r g⟩
  let : Q.Linear R := ⟨fun g r => by ext <;> rfl⟩
  let : H.Linear R := inferInstanceAs (Functor.Linear R (Q ⋙ ShortComplex.homologyFunctor _))
  exact Functor.linear_of_iso R (Functor.isoWhiskerRight (rowIso K) H)

/-- Local cohomology over the quotient is computed by the same augmented Čech complex. -/
theorem localQuotient_cech : LocalQuotientCech.{u} := by
  intro S R _ _ _ _ _ _ f _ hf rs hrs
  have hm : Ideal.span {r | r ∈ rs.map f} = maximalIdeal R := by
    rw [span_map_list, hrs, IsLocalRing.map_maximalIdeal_of_surjective f hf]
  refine ⟨hm, fun q => ?_⟩
  obtain ⟨e⟩ := localCohomologyCechComparison (maximalIdeal R) (rs.map f) hm q
  let Hs := homologyFunctor (ModuleCat.{u} S) (.up ℤ) q
  let Hr := homologyFunctor (ModuleCat.{u} R) (.up ℤ) q
  let F := restrictScalars.{u} f
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Cs := cechWithCoefficients rs
  let Cr := cechWithCoefficients (rs.map f)
  let L := Specs.CommutativeAlgebraNotes.IdealTorsion.localCohomology.{u} (maximalIdeal R) q
  let a : L ⋙ F ≅ F ⋙ Cs ⋙ Hs :=
    calc
      _ ≅ (Cr ⋙ Hr) ⋙ F := Functor.isoWhiskerRight e _
      _ ≅ Cr ⋙ (Hr ⋙ F) := Functor.associator _ _ _
      _ ≅ Cr ⋙ (Fc ⋙ Hs) := Functor.isoWhiskerLeft _ (mapHomology F q).symm
      _ ≅ (Cr ⋙ Fc) ⋙ Hs := (Functor.associator _ _ _).symm
      _ ≅ (F ⋙ Cs) ⋙ Hs := Functor.isoWhiskerRight (restrictCoefficients f rs).symm _
      _ ≅ _ := Functor.associator _ _ _
  let : (Cr ⋙ Hr).Linear R := cechCohomology_linear (rs.map f) q
  let : L.Linear R := Functor.linear_of_iso R e.symm
  refine ⟨a, fun X r => ?_⟩
  have h := a.hom.naturality (r • 𝟙 X)
  change F.map (L.map (r • 𝟙 X)) ≫ a.hom.app X = _ at h
  rw [L.map_smul, L.map_id] at h
  exact h

end Cech

variable [IsLocalRing S] [IsLocalRing R]

theorem localQuotient_residue_bijective : ResidueIdentification.{u} := by
  intro S R _ _ _ _ f _ hf
  refine ⟨(ResidueField.map f).injective, ?_⟩
  intro y
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) y
  obtain ⟨s, rfl⟩ := hf r
  exact ⟨IsLocalRing.residue S s, ResidueField.map_residue f s⟩

private def residueForward (f : S →+* R) [IsLocalHom f] :
    ResidueField S →ₗ[S] (restrictScalars f).obj (ModuleCat.of R (ResidueField R)) where
  toFun := ResidueField.map f
  map_add' := (ResidueField.map f).map_add
  map_smul' s a := by
    change ResidueField.map f (IsLocalRing.residue S s * a) =
      IsLocalRing.residue R (f s) * ResidueField.map f a
    rw [map_mul, ResidueField.map_residue]

private def residueRestriction (f : S →+* R) [IsLocalHom f] (hf : Function.Surjective f) :
    (restrictScalars f).obj (ModuleCat.of R (ResidueField R)) ≃ₗ[S] ResidueField S :=
  (LinearEquiv.ofBijective (residueForward f) (localQuotient_residue_bijective f hf)).symm

private def restrictSubmodule (f : S →+* R) {X : ModuleCat.{u} R} (N : Submodule R X) :
    Submodule S ((restrictScalars f).obj X) where
  carrier := fun x => (show X from x) ∈ N
  zero_mem' := N.zero_mem
  add_mem' := N.add_mem
  smul_mem' s _ hx := N.smul_mem (f s) hx

/-- Coinduction carries a chosen source hull to a hull of the target residue field. -/
theorem coinduction_residue_envelope : CoinducedEnvelope.{u} := by
  intro S R _ _ _ _ _ _ f _ hf E
  let J := ModuleCat.of S E.carrier
  let X := ModuleCat.of R (ResidueField R)
  let h : (restrictScalars f).obj X ⟶ J :=
    ModuleCat.ofHom (X := (restrictScalars f).obj X) (Y := J)
      (E.inclusion.comp (residueRestriction f hf).toLinearMap)
  let i := (coinductionAdjunction f X J).symm h
  have hi (a : ResidueField S) : i (ResidueField.map f a) (1 : R) = E.inclusion a := by
    change h ((1 : R) • ResidueField.map f a) = E.inclusion a
    rw [one_smul]
    exact congrArg E.inclusion ((residueRestriction f hf).apply_symm_apply a)
  have hi' : Function.Injective i := by
    intro x y hxy
    apply (residueRestriction f hf).injective
    apply E.isEnvelope.injective
    have he := congrArg (fun g : (coextendScalars f).obj J => g (1 : R)) hxy
    change h ((1 : R) • x) = h ((1 : R) • y) at he
    simp only [one_smul] at he
    exact he
  refine ⟨i.hom, ⟨hi', ?_, ?_⟩, hi⟩
  · exact (Module.injective_iff_injective_object R _).mpr
      (coinduction_injective f J ((Module.injective_iff_injective_object S _).mp
        E.isEnvelope.injectiveModule))
  · intro N hN
    let ev := (evaluateOne f J).hom
    have hev : Function.Injective ev := evaluateOne_injective f hf J
    let M := (restrictSubmodule f N).map ev
    have hM : M ≠ ⊥ := by
      obtain ⟨x, hx, hx0⟩ := N.ne_bot_iff.mp hN
      exact M.ne_bot_iff.mpr ⟨ev x, ⟨x, hx, rfl⟩, fun h => hx0 (hev (h.trans ev.map_zero.symm))⟩
    obtain ⟨z, hz, hz0⟩ := (M ⊓ LinearMap.range E.inclusion).ne_bot_iff.mp
      (E.isEnvelope.essential M hM)
    obtain ⟨⟨x, hx, rfl⟩, ⟨a, ha⟩⟩ := hz
    have hx' : x = i (ResidueField.map f a) := hev (ha.symm.trans (hi a).symm)
    exact (N ⊓ LinearMap.range i.hom).ne_bot_iff.mpr
      ⟨x, ⟨hx, ⟨ResidueField.map f a, hx'.symm⟩⟩, fun h => hz0 (h ▸ ev.map_zero)⟩

/-- Identification with any chosen target hull, respecting the residue-field inclusion. -/
theorem localQuotient_envelope_equiv : EnvelopeComparison.{u} := by
  intro S R _ _ _ _ _ _ f _ hf E F
  obtain ⟨i, hi, hres⟩ := coinduction_residue_envelope f hf E
  let G : ResidueFieldEnvelope R :=
    ⟨_, i, hi⟩
  obtain ⟨e, he⟩ := residueFieldEnvelope_equiv F G
  refine ⟨e, fun a => ?_⟩
  have hc := LinearMap.congr_fun he (ResidueField.map f a)
  change e (F.inclusion (ResidueField.map f a)) = i (ResidueField.map f a) at hc
  rw [hc, hres]

end CommutativeAlgebraNotes
