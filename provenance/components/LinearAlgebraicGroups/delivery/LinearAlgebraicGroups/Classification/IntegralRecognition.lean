import Specs.LinearAlgebraicGroups.Classification.IntegralRecognition
import LinearAlgebraicGroups.Classification.CharZeroLifting
import LinearAlgebraicGroups.Classification.IntegralRootCoordinates
import LinearAlgebraicGroups.Classification.IntegralRelativeCell
import LinearAlgebraicGroups.Classification.IntegralLinkedRoots
import LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import LinearAlgebraicGroups.Classification.PinnedUniqueness
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Flat.TorsionFree


open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct

set_option linter.style.haveILetI false

universe u

namespace LinearAlgebraicGroups.Classification.IntegralRecognition

open LinearAlgebraicGroups.Specs
open Specs.IntegralRecognition
open Specs.IntegralCentralQuotient (IntegralRing HopfSpectrum spectrumOfHopfHom IsCentral IsRightTorsor)
open Specs.Pinning (BasedRootDatum BasedIso SplitBorelPair AttachedDatum)
open CharacterDescent (Character)

noncomputable section

private theorem mapsSimple_iff {D E : BasedRootDatum.{u}} (e : BasedIso D E) (i : D.I) :
    e.val.indexEquiv i ∈ E.base.support ↔ i ∈ D.base.support := by
  change e.val.indexEquiv i ∈ (E.base.support : Set E.I) ↔ i ∈ (D.base.support : Set D.I)
  have eq := congrArg (fun s : Set E.I => e.val.indexEquiv i ∈ s) e.property
  exact eq.symm.to_iff.trans e.val.indexEquiv.injective.mem_set_image

private def characterEquiv {D E : BasedRootDatum.{u}} (e : BasedIso D E) :
    Multiplicative D.X ≃* Multiplicative E.X :=
  e.val.weightEquiv.toAddEquiv.toMultiplicative

private theorem characterEquiv_root {D E : BasedRootDatum.{u}} (e : BasedIso D E) (i : D.I) :
    characterEquiv e (Multiplicative.ofAdd (D.datum.root i)) =
      Multiplicative.ofAdd (E.datum.root (e.val.indexEquiv i)) := by
  exact RootPairing.Hom.root_weightMap_apply D.datum E.datum i e.val.toHom

private theorem pairing_preserved {D E : BasedRootDatum.{u}} (e : BasedIso D E)
    (i : D.I) (x : D.X) :
    E.datum.toLinearMap (e.val.weightEquiv x) (E.datum.coroot (e.val.indexEquiv i)) =
      D.datum.toLinearMap x (D.datum.coroot i) :=
  e.val.coroot'_weightEquiv i x

private def latticeMapOfIso {D E : BasedRootDatum.{u}} (e : BasedIso D E) :
    LatticeMap D E where
  characters := (characterEquiv e).symm.toMonoidHom
  injective := (characterEquiv e).symm.injective
  finiteIndex := by
    rw [MonoidHom.range_eq_top.mpr (characterEquiv e).symm.surjective]
    infer_instance
  roots := e.val.indexEquiv
  simple_iff := mapsSimple_iff e
  root_eq i := (characterEquiv e).symm_apply_eq.mpr (characterEquiv_root e i).symm
  coroot_eq i x := by
    change D.datum.toLinearMap (e.val.weightEquiv.symm x) (D.datum.coroot i) = _
    have h := pairing_preserved e i (e.val.weightEquiv.symm x)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The isogeny kernel lattice quotient kills each root, independently of the residue
characteristic. -/
private theorem kernelCharacter_root {D E : BasedRootDatum.{u}} (h : LatticeMap D E)
    (i : D.I) :
    QuotientGroup.mk' h.characters.range (Multiplicative.ofAdd (D.datum.root i)) = 1 := by
  rw [← h.root_eq i]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩

/-- The character group of the quotient torus is identified with the target lattice. -/
private def quotientCharacterEquiv {D E : BasedRootDatum.{u}} (h : LatticeMap D E) :
    Multiplicative E.X ≃* (QuotientGroup.mk' h.characters.range).ker :=
  MulEquiv.ofBijective
    (h.characters.codRestrict _ fun χ => by
      exact (QuotientGroup.eq_one_iff _).mpr ⟨χ, rfl⟩)
    ⟨fun _ _ eq => h.injective (congrArg Subtype.val eq), fun ⟨χ, hχ⟩ => by
      have hmem : χ ∈ h.characters.range := (QuotientGroup.eq_one_iff _).mp hχ
      obtain ⟨ψ, hψ⟩ := hmem
      exact ⟨ψ, Subtype.ext hψ⟩⟩

@[simp] private theorem quotientCharacterEquiv_subtype {D E : BasedRootDatum.{u}}
    (h : LatticeMap D E) :
    (QuotientGroup.mk' h.characters.range).ker.subtype.comp (quotientCharacterEquiv h).toMonoidHom =
      h.characters := rfl


private def attachedCharacterEquiv {D : BasedRootDatum.{u}} {k : Type u} [Field k]
    {P : SplitBorelPair k} {A : AttachedDatum P} (d : BasedIso D A.toBased) :
    Multiplicative D.X ≃* Character P.T.group :=
  d.val.weightEquiv.toAddEquiv.toMultiplicative

private def attachedCharacterMap {D E : BasedRootDatum.{u}} {k : Type u} [Field k]
    {P Q : SplitBorelPair k} {A : AttachedDatum P} {B : AttachedDatum Q}
    (d : BasedIso D A.toBased) (e : BasedIso E B.toBased) (h : LatticeMap D E) :
    Character Q.T.group →* Character P.T.group :=
  (attachedCharacterEquiv d).toMonoidHom.comp
    (h.characters.comp (attachedCharacterEquiv e).symm.toMonoidHom)

/-- Compare the actual lattices of the geometric fibres using their given based
identifications with the integral lattices. -/
private def attachedLatticeMap {D E : BasedRootDatum.{u}} {k : Type u} [Field k]
    {P Q : SplitBorelPair k} {A : AttachedDatum P} {B : AttachedDatum Q}
    (d : BasedIso D A.toBased) (e : BasedIso E B.toBased) (h : LatticeMap D E) :
    Specs.CharZeroLifting.LatticeMap A B where
  characters := attachedCharacterMap d e h
  injective := (attachedCharacterEquiv d).injective.comp
    (h.injective.comp (attachedCharacterEquiv e).symm.injective)
  finiteIndex := by
    letI := h.finiteIndex
    let c := attachedCharacterEquiv d
    let f := attachedCharacterMap d e h
    have hle : h.characters.range ≤ f.range.comap c.toMonoidHom := by
      rintro _ ⟨χ, rfl⟩
      exact ⟨attachedCharacterEquiv e χ, by
        change c (h.characters ((attachedCharacterEquiv e).symm
          (attachedCharacterEquiv e χ))) = c (h.characters χ)
        rw [MulEquiv.symm_apply_apply]⟩
    exact Finite.of_surjective _ (QuotientGroup.map_surjective_of_surjective
      h.characters.range f.range c.toMonoidHom
      (QuotientGroup.mk_surjective.comp c.surjective) hle)
  roots := d.val.indexEquiv.symm.trans (h.roots.trans e.val.indexEquiv)
  simple_iff α := by
    change Pinning.IsSimple Q (e.val.indexEquiv (h.roots (d.val.indexEquiv.symm α))) ↔
      Pinning.IsSimple P α
    let i := d.val.indexEquiv.symm α
    have hd : d.val.indexEquiv i = α := d.val.indexEquiv.apply_symm_apply α
    have he : Pinning.IsSimple Q (e.val.indexEquiv (h.roots i)) ↔
        h.roots i ∈ E.base.support :=
      (B.simple_iff _).symm.trans (mapsSimple_iff e _)
    have hf : Pinning.IsSimple P α ↔ i ∈ D.base.support :=
      (A.simple_iff α).symm.trans (hd ▸ mapsSimple_iff d i)
    exact he.trans ((h.simple_iff i).trans hf.symm)
  root_eq α := by
    letI := A.comm
    letI := B.comm
    let i := d.val.indexEquiv.symm α
    have hd : d.val.indexEquiv i = α := d.val.indexEquiv.apply_symm_apply α
    have ha := (characterEquiv_root d i).trans
      (congrArg Multiplicative.ofAdd (A.datum.root_eq (d.val.indexEquiv i)))
    have hb := (characterEquiv_root e (h.roots i)).trans
      (congrArg Multiplicative.ofAdd (B.datum.root_eq (e.val.indexEquiv (h.roots i))))
    change attachedCharacterEquiv d (h.characters ((attachedCharacterEquiv e).symm
      (e.val.indexEquiv (h.roots i)).val)) = α.val
    have hc : (attachedCharacterEquiv e).symm (e.val.indexEquiv (h.roots i)).val =
        Multiplicative.ofAdd (E.datum.root (h.roots i)) :=
      (attachedCharacterEquiv e).symm_apply_eq.mpr hb.symm
    rw [hc, h.root_eq]
    exact ha.trans (congrArg Subtype.val hd)
  coroot_eq α χ := by
    letI := A.comm
    letI := B.comm
    let i := d.val.indexEquiv.symm α
    let ψ := (attachedCharacterEquiv e).symm χ
    have hd : d.val.indexEquiv i = α := d.val.indexEquiv.apply_symm_apply α
    have he : e.val.weightEquiv ψ.toAdd = Additive.ofMul χ :=
      (attachedCharacterEquiv e).apply_symm_apply χ
    have ha := pairing_preserved d i (h.characters ψ).toAdd
    have hb := pairing_preserved e (h.roots i) ψ.toAdd
    change CharacterPairing.pairing P.T.group (attachedCharacterEquiv d (h.characters ψ))
        (Specs.CharZeroLifting.attachedCoroot A α) =
      CharacterPairing.pairing Q.T.group χ
        (Specs.CharZeroLifting.attachedCoroot B (e.val.indexEquiv (h.roots i)))
    rw [← A.datum.pairing_eq, ← B.datum.pairing_eq]
    change A.toBased.datum.toLinearMap (d.val.weightEquiv (h.characters ψ).toAdd)
        (A.toBased.datum.coroot α) =
      B.toBased.datum.toLinearMap (Additive.ofMul χ)
        (B.toBased.datum.coroot (e.val.indexEquiv (h.roots i)))
    rw [← hd, ha]
    exact (h.coroot_eq i ψ.toAdd).trans <| hb.symm.trans <|
      congrArg (fun x : B.toBased.X =>
        B.toBased.datum.toLinearMap x (B.toBased.datum.coroot (e.val.indexEquiv (h.roots i)))) he

/-- Relabeling a quotient by an isomorphic model preserves the entire torsor square. -/
private theorem rightTorsor_comp_equiv {R A B C M : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C] [HopfAlgebra R A] [HopfAlgebra R B] [HopfAlgebra R C]
    [CommGroup M] (j : B →ₐc[R] A) (π : A →ₐc[R] MonoidAlgebra R M)
    (e : C ≃ₐc[R] B) (hj : IsRightTorsor j π) :
    IsRightTorsor (j.comp e.toBialgHom) π := by
  let F := hopfSpec (CommRingCat.of R) ⋙ Grp.forget (Over (Spec (CommRingCat.of R))) ⋙
    Over.forget (Spec (CommRingCat.of R))
  let i : (HopfSpectrum R B).X.left ≅ (HopfSpectrum R C).X.left :=
    F.mapIso (CommHopfAlgCat.isoMk e).op
  let q := (spectrumOfHopfHom j).hom.hom.left
  have hcomp : (spectrumOfHopfHom (j.comp e.toBialgHom)).hom.hom.left = q ≫ i.hom := by
    change F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp]
    rfl
  obtain ⟨hf, hfl, hs, hfp, hp⟩ := hj
  letI : IsFinite q := hf
  letI : Flat q := hfl
  letI : Surjective q := hs
  letI : LocallyOfFinitePresentation q := hfp
  unfold IsRightTorsor
  dsimp only
  rw [hcomp]
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) i ?_ ?_ ?_ ?_ <;>
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  all_goals exact (Category.id_comp (q ≫ i.hom)).symm

section AffineMorphism

variable {R K B C S : Type*} [CommRing R] [CommRing K] [CommRing B] [CommRing C] [CommRing S]
  [Algebra R K] [Algebra R B] [Algebra R C] [Algebra R S]
  [Algebra B S] [IsScalarTower R B S]

/-- Faithfully flat descent to the base of an affine cover. The overlap equality
can be checked after an injective scalar extension when the overlap is flat. -/
private theorem descendAffineMorphism [Module.FaithfullyFlat B S] [Module.Flat R B]
    (hK : Function.Injective (algebraMap R K))
    (generic : K ⊗[R] C →ₐ[K] K ⊗[R] B) (localMap : C →ₐ[R] S)
    (hlocal : ∀ c : C,
      (1 : K) ⊗ₜ[R] localMap c =
        Algebra.TensorProduct.map (AlgHom.id R K) ((Algebra.ofId B S).restrictScalars R)
          (generic (1 ⊗ₜ[R] c))) :
    ∃! f : C →ₐ[R] B, ((Algebra.ofId B S).restrictScalars R).comp f = localMap := by
  let T := S ⊗[B] S
  let l : S →ₐ[R] T := ((Algebra.TensorProduct.includeLeft : S →ₐ[B] T)).restrictScalars R
  let r : S →ₐ[R] T := ((Algebra.TensorProduct.includeRight : S →ₐ[B] T)).restrictScalars R
  let j : B →ₐ[R] S := (Algebra.ofId B S).restrictScalars R
  have hbase : l.comp j = r.comp j := by
    ext b
    exact ((Algebra.TensorProduct.includeLeft : S →ₐ[B] T).commutes b).trans
      ((Algebra.TensorProduct.includeRight : S →ₐ[B] T).commutes b).symm
  have hflat : Module.Flat R T := Module.Flat.trans R B T
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : T →ₐ[R] K ⊗[R] T) :=
    Algebra.TensorProduct.includeRight_injective hK
  have hdesc (c : C) : l (localMap c) = r (localMap c) := by
    apply hinj
    have hl := congrArg (Algebra.TensorProduct.map (AlgHom.id R K) l) (hlocal c)
    have hr := congrArg (Algebra.TensorProduct.map (AlgHom.id R K) r) (hlocal c)
    change (1 : K) ⊗ₜ[R] l (localMap c) = (1 : K) ⊗ₜ[R] r (localMap c)
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← AlgHom.comp_apply,
      ← Algebra.TensorProduct.map_comp] at hl hr
    change _ = Algebra.TensorProduct.map _ (l.comp j) _ at hl
    change _ = Algebra.TensorProduct.map _ (r.comp j) _ at hr
    rw [hbase] at hl
    exact hl.trans hr.symm
  have hmem (c : C) : localMap c ∈ j.range := by
    change localMap c ∈ Set.range (algebraMap B S)
    rw [← Algebra.IsEffective.eqLocus_includeLeft_includeRight (.of_faithfullyFlat B S)]
    exact hdesc c
  have hji : Function.Injective j := FaithfulSMul.algebraMap_injective B S
  let e := AlgEquiv.ofInjective j hji
  let f := e.symm.toAlgHom.comp (localMap.codRestrict j.range hmem)
  refine ⟨f, ?_, fun g hg => ?_⟩
  · ext c
    exact congrArg Subtype.val (e.apply_symm_apply ⟨localMap c, hmem c⟩)
  · exact AlgHom.ext fun c => hji
      ((congrArg (fun a : C →ₐ[R] S => a c) hg).trans
        (congrArg Subtype.val (e.apply_symm_apply ⟨localMap c, hmem c⟩)).symm)

end AffineMorphism

section BialgebraExtension

variable {R K B C : Type*} [CommRing R] [CommRing K] [CommRing B] [CommRing C] [Algebra R K]

/-- Base change on the two factors of the comultiplication is injective for
a flat underlying module and an injective base-ring map. -/
private def extendTensorSquare (R K B : Type*) [CommRing R] [CommRing K] [CommRing B]
    [Algebra R K] [Algebra R B] :
    B ⊗[R] B →ₗ[R] (K ⊗[R] B) ⊗[K] (K ⊗[R] B) :=
  ((TensorProduct.AlgebraTensorModule.distribBaseChange R K B B).restrictScalars R).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeRight : B ⊗[R] B →ₐ[R] K ⊗[R] (B ⊗[R] B)).toLinearMap

@[simp] private theorem extendTensorSquare_tmul [Algebra R B] (b b' : B) :
    extendTensorSquare R K B (b ⊗ₜ[R] b') =
      ((1 : K) ⊗ₜ[R] b) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b') :=
  TensorProduct.AlgebraTensorModule.distribBaseChange_tmul R K b b' 1

private theorem extendTensorSquare_inj [Algebra R B] [Module.Flat R B]
    (hK : Function.Injective (algebraMap R K)) :
    Function.Injective (extendTensorSquare R K B) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange R K B B).injective.comp
    (Algebra.TensorProduct.includeRight_injective hK)

private theorem extendTensorSquare_comul [Bialgebra R B] (b : B) :
    extendTensorSquare R K B (Bialgebra.comulAlgHom R B b) =
      Bialgebra.comulAlgHom K (K ⊗[R] B) ((1 : K) ⊗ₜ[R] b) := by
  let p : B →ₐ[R] (K ⊗[R] B) := Algebra.TensorProduct.includeRight
  let η : R →+* K := algebraMap R K
  have hp : p.toRingHom.comp (algebraMap R B) = (algebraMap K (K ⊗[R] B)).comp η := by
    ext r
    exact (p.commutes r).trans (IsScalarTower.algebraMap_apply R K (K ⊗[R] B) r)
  have hb := DFunLike.congr_fun (Bialgebra.comul_includeRight (R := R) (A := K) (B := B)) b
  change Bialgebra.comulAlgHom K (K ⊗[R] B) ((1 : K) ⊗ₜ[R] b) =
    Algebra.TensorProduct.mapRingHom η p.toRingHom p.toRingHom hp hp
      (Bialgebra.comulAlgHom R B b) at hb
  rw [hb]
  generalize Bialgebra.comulAlgHom R B b = z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro b b'
    rw [extendTensorSquare_tmul, Algebra.TensorProduct.mapRingHom_tmul]
    rfl
  · intro z z' hz hz'
    rw [map_add, map_add, hz, hz']

/-- An algebra homomorphism that agrees with a bialgebra homomorphism
after injective flat base change already preserves the Hopf operations. -/
private theorem isBialgebraMorphism_of_extension [Bialgebra R B] [Bialgebra R C]
    [Module.Flat R B] (hK : Function.Injective (algebraMap R K))
    (f : C →ₐ[R] B) (g : K ⊗[R] C →ₐc[K] K ⊗[R] B)
    (h : ∀ c : C, g (1 ⊗ₜ[R] c) = (1 : K) ⊗ₜ[R] f c) :
    ∃ f' : C →ₐc[R] B, f'.toAlgHom = f := by
  refine ⟨BialgHom.ofAlgHom f ?_ ?_, rfl⟩
  · ext c
    apply hK
    have hc := DFunLike.congr_fun (g.counitAlgHom_comp) ((1 : K) ⊗ₜ[R] c)
    change Bialgebra.counitAlgHom K (K ⊗[R] B) (g ((1 : K) ⊗ₜ[R] c)) =
      Bialgebra.counitAlgHom K (K ⊗[R] C) ((1 : K) ⊗ₜ[R] c) at hc
    rw [h] at hc
    simpa [Bialgebra.TensorProduct.counitAlgHom_def, Algebra.TensorProduct.map_tmul, Algebra.smul_def] using hc
  · ext c
    change (Algebra.TensorProduct.map f f) (Bialgebra.comulAlgHom R C c) =
      Bialgebra.comulAlgHom R B (f c)
    apply extendTensorSquare_inj (K := K) hK
    rw [extendTensorSquare_comul, ← h]
    have hc := DFunLike.congr_fun g.map_comp_comulAlgHom ((1 : K) ⊗ₜ[R] c)
    change Algebra.TensorProduct.map g.toAlgHom g.toAlgHom
      (Bialgebra.comulAlgHom K (K ⊗[R] C) ((1 : K) ⊗ₜ[R] c)) =
      Bialgebra.comulAlgHom K (K ⊗[R] B) (g ((1 : K) ⊗ₜ[R] c)) at hc
    rw [← hc, ← extendTensorSquare_comul]
    generalize Bialgebra.comulAlgHom R C c = z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro a b
      simp only [Algebra.TensorProduct.map_tmul, extendTensorSquare_tmul, BialgHom.coe_toAlgHom, h]
    · intro x y hx hy
      simp only [map_add, hx, hy]

end BialgebraExtension

section AffineIsomorphism

variable {R K B C S T : Type*}
  [CommRing R] [CommRing K] [CommRing B] [CommRing C] [CommRing S] [CommRing T]
  [Algebra R K] [Bialgebra R B] [Bialgebra R C]
  [Algebra R S] [Algebra B S] [IsScalarTower R B S]
  [Algebra R T] [Algebra C T] [IsScalarTower R C T]

/-- Extend a generic bialgebra map by descent from its integral realization on
an affine faithfully flat cover of its domain scheme. -/
private theorem descendAffineBialgebraMap
    [Module.Flat R B] [Module.Flat R K] [Module.FaithfullyFlat B S]
    (hK : Function.Injective (algebraMap R K))
    (g : K ⊗[R] C →ₐc[K] K ⊗[R] B) (f₀ : C →ₐ[R] S)
    (localAgreement : ∀ c : C, (1 : K) ⊗ₜ[R] f₀ c =
      Algebra.TensorProduct.map (AlgHom.id R K) ((Algebra.ofId B S).restrictScalars R)
        (g (1 ⊗ₜ[R] c))) :
    ∃ f : C →ₐc[R] B, ∀ c : C, g (1 ⊗ₜ[R] c) = (1 : K) ⊗ₜ[R] f c := by
  obtain ⟨f, hf, _⟩ := descendAffineMorphism hK g.toAlgHom f₀ localAgreement
  let j : B →ₐ[R] S := (Algebra.ofId B S).restrictScalars R
  have hj : Function.Injective j.toLinearMap := FaithfulSMul.algebraMap_injective B S
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id R K) j) :=
    Module.Flat.lTensor_preserves_injective_linearMap j.toLinearMap hj
  have hagree (c : C) : g (1 ⊗ₜ[R] c) = (1 : K) ⊗ₜ[R] f c := by
    apply hinj
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact (localAgreement c).symm.trans
      (congrArg (fun e : C →ₐ[R] S => (1 : K) ⊗ₜ[R] e c) hf.symm)
  obtain ⟨f', hf'⟩ := isBialgebraMorphism_of_extension hK f g hagree
  refine ⟨f', fun c => ?_⟩
  change g (1 ⊗ₜ[R] c) = (1 : K) ⊗ₜ[R] f'.toAlgHom c
  rw [hf']
  exact hagree c

end AffineIsomorphism


private theorem modelFlat {D : BasedRootDatum.{u}} (P : Model D) :
    @Module.Flat IntegralRing.{u} P.A _ _ (Algebra.toModule) := by
  haveI := P.smooth
  have hf : Flat (HopfSpectrum IntegralRing.{u} P.A).X.hom := inferInstance
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap IntegralRing.{u} P.A))) at hf
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hf)

private theorem integralRing_isDomain : IsDomain IntegralRing.{u} :=
  (ULift.ringEquiv (R := ℤ)).toMulEquiv.isDomain ℤ

private theorem integralRing_isPrincipalIdealRing : IsPrincipalIdealRing IntegralRing.{u} :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ℤ)).symm.toRingHom
    (ULift.ringEquiv (R := ℤ)).symm.surjective

private theorem pin_has_nonzero_coefficient {D : BasedRootDatum.{u}} (P : Model D)
    (i : ↥D.base.support) :
    ∃ a : P.A, ((P.pin i).val a).snd ≠ 0 := by
  by_contra! h
  obtain ⟨c, _, hc⟩ := (P.pin_basis i).2 (P.pin i) (P.pin_basis i).1
  have hconst (b : IntegralRing.{u}) : b = c :=
    hc b (fun a => by rw [h a, mul_zero])
  exact one_ne_zero ((hconst 1).trans (hconst 0).symm)

section Centrality

open WithConv

variable {R A X M : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommGroup X] [CommGroup M]

-- The test algebra is only a commutative algebra. Its points still form a group
-- via the antipode in the source Hopf algebra.
local instance pointConvolutionGroup {S : Type u} [CommRing S] [Algebra R S] :
    Group (WithConv (A →ₐ[R] S)) where
  inv f := toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A))
  inv_mul_cancel f := by
    change toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)) * f = 1
    have h := AlgHom.comp_convMul_distrib f.ofConv
      (toConv (HopfAlgebra.antipodeAlgHom R A)) (toConv (AlgHom.id R A))
    rw [AlgHom.antipode_id_cancel, AlgHom.convOne_def] at h
    apply WithConv.ext
    rw [AlgHom.comp_id] at h
    rw [← h]
    apply AlgHom.ext
    intro a
    exact f.ofConv.commutes _

/-- A point of the diagonalizable kernel commutes with each root coordinate
whose character is killed in the quotient lattice. -/
private theorem rootCommutesWithKernel
    (t : A →ₐc[R] MonoidAlgebra R X) (z : X →* M) (α : X) (hz : z α = 1)
    (x : A →ₐ[R] Polynomial R) (hx : IntegralCentralQuotient.RootScalarAction t x α)
    (S : CommAlgCat.{u} R) (s : MonoidAlgebra R M →ₐ[R] S) (a : S) :
    Commute (toConv ((Polynomial.aeval a).comp x))
      (toConv (s.comp ((MonoidAlgebra.mapDomainBialgHom R z).comp t).toAlgHom)) := by
  let z₀ := (MonoidAlgebra.mapDomainBialgHom R z).toAlgHom
  let g := toConv ((s.comp z₀).comp t.toAlgHom)
  let v := toConv ((Polynomial.aeval a).comp x)
  have h := hx S a (s.comp z₀)
  have hchar : (s.comp z₀) (MonoidAlgebra.of R X α) = 1 := by
    change s (MonoidAlgebra.mapDomainBialgHom R z (MonoidAlgebra.single α 1)) = 1
    rw [MonoidAlgebra.mapDomainBialgHom_single, hz]
    change s 1 = 1
    exact map_one s
  change g * v * g⁻¹ = toConv ((Polynomial.aeval ((s.comp z₀) (MonoidAlgebra.of R X α) * a)).comp x) at h
  rw [hchar, one_mul] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

/-- Testing commutation on all algebras recovers equality of the translation
coactions, using the universal pair of points on the tensor product. -/
private theorem kernelCentral_of_pointwise
    (π : A →ₐc[R] MonoidAlgebra R M)
    (h : ∀ (S : CommAlgCat.{u} R) (g : A →ₐ[R] S) (s : MonoidAlgebra R M →ₐ[R] S),
      Commute (toConv g) (toConv (s.comp π.toAlgHom))) :
    IsCentral π := by
  let S := CommAlgCat.of R (A ⊗[R] MonoidAlgebra R M)
  let l : A →ₐ[R] S := Algebra.TensorProduct.includeLeft
  let r : MonoidAlgebra R M →ₐ[R] S := Algebra.TensorProduct.includeRight
  let q := r.comp π.toAlgHom
  have hright :
      Algebra.TensorProduct.lift l q (fun _ _ => Commute.all _ _) =
        Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom := by
    apply AlgHom.ext
    intro a
    refine TensorProduct.inductionOn a ?_ ?_
    · intro b c
      change _ = Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom (b ⊗ₜ[R] c)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
      change (b ⊗ₜ[R] (1 : MonoidAlgebra R M)) * ((1 : A) ⊗ₜ[R] π c) =
        b ⊗ₜ[R] π c
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · intro a b ha hb
      rw [map_add, map_add, ha, hb]
  have hleft :
      Algebra.TensorProduct.lift q l (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.comm R (MonoidAlgebra R M) A).toAlgHom.comp
          (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R A)) := by
    apply AlgHom.ext
    intro a
    refine TensorProduct.inductionOn a ?_ ?_
    · intro b c
      change _ = Algebra.TensorProduct.comm R (MonoidAlgebra R M) A
        (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R A) (b ⊗ₜ[R] c))
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.lift_tmul]
      change ((1 : A) ⊗ₜ[R] π b) * (c ⊗ₜ[R] (1 : MonoidAlgebra R M)) =
        c ⊗ₜ[R] π b
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    · intro a b ha hb
      rw [map_add, map_add, ha, hb]
  apply AlgHom.ext
  intro a
  have eq := congrArg (fun f : WithConv (A →ₐ[R] S) => f a) (h S l r).eq
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, hright, hleft] at eq
  exact eq

private theorem torusPoints_commute
    (t : A →ₐc[R] MonoidAlgebra R X) (S : CommAlgCat.{u} R)
    (s₁ s₂ : MonoidAlgebra R X →ₐ[R] S) :
    Commute (toConv (s₁.comp t.toAlgHom)) (toConv (s₂.comp t.toAlgHom)) := by
  have h : Commute (toConv s₁) (toConv s₂) := Commute.all _ _
  exact ((AlgHom.convMul_comp_bialgHom_distrib (toConv s₁) (toConv s₂) t).symm.trans
    ((congrArg (fun f : WithConv _ => f.ofConv.comp t.toAlgHom) h.eq).trans
      (AlgHom.convMul_comp_bialgHom_distrib (toConv s₂) (toConv s₁) t))) |> WithConv.ext

end Centrality

section TangentExtension

variable {R K A : Type u} [CommRing R] [CommRing K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A]

/-- Extend an identity tangent vector to the scalar-extended Hopf algebra. -/
private def extendTangent (v : Tangent R A) : Tangent K (K ⊗[R] A) := by
  let p := Algebra.TensorProduct.lift (Algebra.ofId K (DualNumber K))
    ((dualCoefficients K).comp v.val) (fun _ _ => Commute.all _ _)
  refine ⟨p, AlgHom.ext fun a => ?_⟩
  refine TensorProduct.inductionOn a ?_ ?_
  · intro k b
    change (TrivSqZeroExt.fstHom K K K) (p (k ⊗ₜ[R] b)) =
      Bialgebra.counitAlgHom K (K ⊗[R] A) (k ⊗ₜ[R] b)
    have hb : (v.val b).fst = Bialgebra.counitAlgHom R A b :=
      DFunLike.congr_fun v.property b
    rw [Bialgebra.TensorProduct.counitAlgHom_def]
    simp only [p, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, map_mul,
      Algebra.TensorProduct.map_tmul]
    change k * algebraMap R K (v.val b).fst =
      Algebra.TensorProduct.rid R K K
        ((Bialgebra.counitAlgHom K K k) ⊗ₜ[R] (Bialgebra.counitAlgHom R A b))
    rw [Algebra.TensorProduct.rid_tmul, hb, Algebra.smul_def, mul_comm]
    rfl
  · intro a b ha hb
    rw [map_add, map_add, ha, hb]

private theorem extendTangent_one_tmul (v : Tangent R A) (a : A) :
    (extendTangent (K := K) v).val ((1 : K) ⊗ₜ[R] a) = dualCoefficients K (v.val a) := by
  simp only [extendTangent, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply]

private theorem extendTangent_snd (v : Tangent R A) (a : A) :
    ((extendTangent (K := K) v).val ((1 : K) ⊗ₜ[R] a)).snd =
      algebraMap R K (v.val a).snd := by
  unfold extendTangent
  simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply]
  rfl

private theorem extendTangent_has_nonzero_coefficient (v : Tangent R A)
    (h : ∃ a, (v.val a).snd ≠ 0) (hK : Function.Injective (algebraMap R K)) :
    ∃ a : K ⊗[R] A, ((extendTangent (K := K) v).val a).snd ≠ 0 := by
  obtain ⟨a, ha⟩ := h
  refine ⟨1 ⊗ₜ[R] a, ?_⟩
  rw [extendTangent_snd]
  exact fun hz => ha (hK (hz.trans (map_zero _).symm))

private theorem integralRing_algebraMap_injective (k : Type u) [Field k] [CharZero k]
    [Algebra IntegralRing.{u} k] : Function.Injective (algebraMap IntegralRing.{u} k) := by
  have h (x : IntegralRing.{u}) : algebraMap IntegralRing.{u} k x = Int.cast x.down := by
    obtain ⟨n⟩ := x
    exact map_intCast (algebraMap IntegralRing.{u} k) n
  intro x y eq
  apply ULift.ext
  rw [h, h] at eq
  exact Int.cast_injective eq

private theorem extendPin_has_nonzero_coefficient {D : BasedRootDatum.{u}} (P : Model D)
    (i : ↥D.base.support) {k : Type u} [Field k] [CharZero k] [Algebra IntegralRing.{u} k] :
    ∃ a, ((extendTangent (K := k) (P.pin i)).val a).snd ≠ 0 :=
  extendTangent_has_nonzero_coefficient (P.pin i) (pin_has_nonzero_coefficient P i)
    (integralRing_algebraMap_injective k)

end TangentExtension

section AffinePoints

set_option backward.isDefEq.respectTransparency false

open WithConv
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open Specs.IntegralCentralQuotient (spectrumOfAlgHom)
open AdjointRepresentation (GroupPoints)

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]

private theorem spectrumOfAlgHom_comp [Algebra R A] [Algebra R B] [Algebra R C]
    (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
    spectrumOfAlgHom (g.comp f) = spectrumOfAlgHom g ≫ spectrumOfAlgHom f := by
  rw [← Functor.map_comp]
  rfl

private theorem spectrumOfHopfHom_comp [HopfAlgebra R A] [HopfAlgebra R B] [HopfAlgebra R C]
    (g : B →ₐc[R] C) (f : A →ₐc[R] B) :
    spectrumOfHopfHom (g.comp f) = spectrumOfHopfHom g ≫ spectrumOfHopfHom f := by
  rw [← Functor.map_comp]
  rfl

/-- The Laurent generator evaluates under the point corresponding to an algebra map
by applying that map to the character monomial. -/
private theorem characterValue_spectrum {k : Type u} [Field k]
    [HopfAlgebra k A] [Algebra k B] (χ : Character (HopfSpectrum k A))
    (t : A →ₐ[k] B) :
    CharacterPairing.characterValue χ (CommAlgCat.of k B) (spectrumOfAlgHom t) =
      t (characterMonomial χ) := by
  let F := algSpec (CommRingCat.of k)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let L := CommAlgCat.of k (MonoidAlgebra k DiagonalizableGroups.IntegerCharacters)
  let a := CommAlgCat.of k A
  let b := CommAlgCat.of k B
  let q : op a ⟶ op L := ff.preimage χ.hom.hom
  have h : F.map q = χ.hom.hom := ff.map_preimage _
  have heq : ff.preimage (spectrumOfAlgHom t ≫ χ.hom.hom) =
      (CommAlgCat.ofHom t : a ⟶ b).op ≫ q := by
    apply ff.map_injective
    change F.map (ff.preimage (spectrumOfAlgHom t ≫ χ.hom.hom)) =
      F.map ((CommAlgCat.ofHom t : a ⟶ b).op ≫ q)
    rw [ff.map_preimage, F.map_comp, h]
  change ((ff.preimage (spectrumOfAlgHom t ≫ χ.hom.hom)).unop).hom _ = _
  rw [heq]
  rfl

private theorem characterMonomial_comp {k : Type u} [Field k]
    [HopfAlgebra k A] [HopfAlgebra k B]
    (f : B →ₐc[k] A) (χ : Character (HopfSpectrum k B)) :
    characterMonomial (spectrumOfHopfHom f ≫ χ) = f (characterMonomial χ) :=
  characterValue_spectrum χ f.toAlgHom

/-- The Laurent coordinate and its inverse generate the character algebra. -/
private theorem characterMonomial_injective {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A] :
    Function.Injective (characterMonomial (K := k) (C := A)) := by
  intro χ ψ h
  let L := CommAlgCat.of k (MonoidAlgebra k DiagonalizableGroups.IntegerCharacters.{u})
  let C := CommAlgCat.of k A
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f : L ⟶ C := (ff.preimage χ.hom.hom).unop
  let g : L ⟶ C := (ff.preimage ψ.hom.hom).unop
  let m := MonoidAlgebra.of k DiagonalizableGroups.IntegerCharacters.{u}
  let a := (f.hom.toMonoidHom.comp m).toHomUnits
  let b := (g.hom.toMonoidHom.comp m).toHomUnits
  have hgen : a DiagonalizableGroups.integerGenerator = b DiagonalizableGroups.integerGenerator :=
    Units.ext h
  have hfg : f.hom = g.hom := by
    apply MonoidAlgebra.algHom_ext
    · intro z
      have hz : DiagonalizableGroups.integerGenerator ^ z.down.toAdd = z := by
        apply ULift.ext
        change Multiplicative.ofAdd (z.down.toAdd • (1 : ℤ)) = z.down
        simp
      have hh : a z = b z := by rw [← hz, map_zpow, map_zpow, hgen]
      exact congrArg Units.val hh
    · ext
  apply Grp.hom_ext
  have he : f = g := CommAlgCat.hom_ext hfg
  have he' := congrArg (fun m : L ⟶ C => (algSpec (CommRingCat.of k)).map m.op) he
  exact (ff.map_preimage χ.hom.hom).symm.trans (he'.trans (ff.map_preimage ψ.hom.hom))

/-- Vanishing on the identity tangent is detected on its algebra-valued point. -/
private def tangentPoint {k : Type u} [Field k] [HopfAlgebra k A]
    {G : GroupScheme k} (e : HopfSpectrum k A ≅ G) (p : Tangent k A) : Lie k G := by
  refine ⟨spectrumOfAlgHom p.val ≫ e.hom.hom.hom, ?_⟩
  change mapPoints (dualReduction k) (spectrumOfAlgHom p.val ≫ e.hom.hom.hom) = 1
  rw [show mapPoints (dualReduction k) (spectrumOfAlgHom p.val ≫ e.hom.hom.hom) =
    spectrumOfAlgHom ((TrivSqZeroExt.fstHom k k k).comp p.val) ≫ e.hom.hom.hom by
      rw [spectrumOfAlgHom_comp]; rfl]
  rw [p.property]
  change Spec.mapMulEquiv (1 : WithConv (A →ₐ[k] k)) ≫ e.hom.hom.hom = 1
  rw [map_one]
  exact MonObj.one_comp e.hom.hom.hom

private theorem tangentPoint_ne_zero {k : Type u} [Field k] [HopfAlgebra k A]
    {G : GroupScheme k} (e : HopfSpectrum k A ≅ G) (p : Tangent k A)
    (hp : ∃ a : A, (p.val a).snd ≠ 0) : tangentPoint e p ≠ 0 := by
  intro h
  have eq := congrArg (fun v : Lie k G => v.toMul.val) h
  change spectrumOfAlgHom p.val ≫ e.hom.hom.hom = 1 at eq
  have ho : (1 : (testSpec k).obj (op (CommAlgCat.of k (DualNumber k))) ⟶
      (HopfSpectrum k A).X) ≫ e.hom.hom.hom = 1 := MonObj.one_comp e.hom.hom.hom
  have hh := (cancel_mono e.hom.hom.hom).mp (eq.trans ho.symm)
  have hval : toConv p.val = (1 : WithConv (A →ₐ[k] DualNumber k)) := by
    apply Spec.mapMulEquiv.injective
    rw [map_one]
    exact hh
  obtain ⟨a, ha⟩ := hp
  apply ha
  have heq := congrArg (fun f : WithConv (A →ₐ[k] DualNumber k) => (f.ofConv a).snd) hval
  exact heq.trans (map_zero (algebraMap k k))

end AffinePoints

section ExtendPoint

open WithConv

variable {R K A S : Type u} [CommRing R] [CommRing K] [CommRing A] [CommRing S]
  [Algebra R K] [HopfAlgebra R A] [Algebra K S] [Algebra R S] [IsScalarTower R K S]

/-- Restrict a point of a scalar-extended algebra to the original algebra. -/
private abbrev restrictPoint : (K ⊗[R] A →ₐ[K] S) ≃ (A →ₐ[R] S) :=
  (AlgHom.liftEquiv R K A S).symm

private theorem restrictPoint_mul (p q : WithConv (K ⊗[R] A →ₐ[K] S)) :
    toConv (restrictPoint (p * q).ofConv) =
      toConv (restrictPoint p.ofConv) * toConv (restrictPoint q.ofConv) := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  change (p * q).ofConv ((1 : K) ⊗ₜ[R] a) =
    (toConv (restrictPoint p.ofConv) * toConv (restrictPoint q.ofConv)).ofConv a
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  change (Algebra.TensorProduct.lift p.ofConv q.ofConv _) (Bialgebra.comulAlgHom K (K ⊗[R] A)
      ((1 : K) ⊗ₜ[R] a)) =
    (Algebra.TensorProduct.lift (restrictPoint p.ofConv) (restrictPoint q.ofConv) _)
      (Bialgebra.comulAlgHom R A a)
  rw [← extendTensorSquare_comul]
  generalize Bialgebra.comulAlgHom R A a = z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro b c
    rw [extendTensorSquare_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  · intro x y hx hy
    rw [map_add, map_add, map_add, hx, hy]

private theorem restrictPoint_one :
    toConv (restrictPoint (K := K) (1 : WithConv (K ⊗[R] A →ₐ[K] S)).ofConv) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  simp only [AlgHom.convOne_def, AlgHom.comp_apply, AlgHom.liftEquiv_symm_apply]
  have e := DFunLike.congr_fun
    (Bialgebra.counitAlgHom_comp_includeRight (R := R) (A := K) (B := A)) a
  change Bialgebra.counitAlgHom K (K ⊗[R] A) ((1 : K) ⊗ₜ[R] a) =
    algebraMap R K (Bialgebra.counitAlgHom R A a) at e
  exact congrArg (algebraMap K S) e |>.trans (IsScalarTower.algebraMap_apply R K S _).symm

private theorem restrictPoint_extendedTangent (v : Tangent R A) :
    restrictPoint (K := K) (S := DualNumber S)
      ((dualCoefficients S).comp (extendTangent (K := K) v).val) =
        (dualCoefficients S).comp v.val := by
  apply AlgHom.ext
  intro a
  change dualCoefficients S ((extendTangent (K := K) v).val ((1 : K) ⊗ₜ[R] a)) =
    dualCoefficients S (v.val a)
  simp only [extendTangent, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply]
  apply TrivSqZeroExt.ext <;> exact (IsScalarTower.algebraMap_apply R K S _).symm

end ExtendPoint

section ExtendedWeights

open WithConv
open AdjointRepresentation (scale)
attribute [local instance] pointConvolutionGroup

variable {R K A : Type u} [CommRing R] [Field K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A]

private def restrictPointMonoidHom {S : Type u} [CommRing S] [Algebra K S] [Algebra R S]
    [IsScalarTower R K S] :
    WithConv (K ⊗[R] A →ₐ[K] S) →* WithConv (A →ₐ[R] S) where
  toFun p := toConv (restrictPoint p.ofConv)
  map_one' := restrictPoint_one
  map_mul' := restrictPoint_mul

private theorem extendTangent_weight {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (α : X) (v : Tangent R A) (hv : HasWeight t α v)
    (S : CommAlgCat.{u} K) (s : K ⊗[R] MonoidAlgebra R X →ₐ[K] S) :
    let tK := Bialgebra.TensorProduct.map (BialgHom.id K K) t
    let g := toConv ((TrivSqZeroExt.inlAlgHom K S S).comp (s.comp tK.toAlgHom))
    let p := (dualCoefficients S).comp (extendTangent (K := K) v).val
    let c := s ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
    g * toConv p * g⁻¹ = toConv ((scale S c).hom.comp p) := by
  dsimp only
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let s₀ : MonoidAlgebra R X →ₐ[R] S := restrictPoint s
  let j := restrictPointMonoidHom (R := R) (K := K) (A := A) (S := DualNumber S)
  have hj : Function.Injective j := fun p q h =>
    WithConv.ofConv_injective (restrictPoint.injective (congrArg WithConv.ofConv h))
  let tK := Bialgebra.TensorProduct.map (BialgHom.id K K) t
  let g := toConv ((TrivSqZeroExt.inlAlgHom K S S).comp (s.comp tK.toAlgHom))
  let p := (dualCoefficients S).comp (extendTangent (K := K) v).val
  let c := s ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
  change g * toConv p * g⁻¹ = toConv ((scale S c).hom.comp p)
  apply hj
  rw [map_mul, map_mul, map_inv]
  have hg : j g = toConv ((TrivSqZeroExt.inlAlgHom R S S).comp (s₀.comp t.toAlgHom)) := by
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    change (TrivSqZeroExt.inlAlgHom K S S) (s (tK ((1 : K) ⊗ₜ[R] a))) =
      (TrivSqZeroExt.inlAlgHom R S S) (s₀ (t a))
    rw [Bialgebra.TensorProduct.map_tmul]
    rfl
  have hp : j (toConv p) = toConv ((dualCoefficients S).comp v.val) :=
    congrArg toConv (restrictPoint_extendedTangent v)
  have hsc : j (toConv ((scale S c).hom.comp p)) =
      toConv (((TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))).restrictScalars R).comp
        ((dualCoefficients S).comp v.val)) := by
    apply WithConv.ext
    have heq := restrictPoint_extendedTangent (K := K) (S := S) v
    apply AlgHom.ext
    intro a
    have ha := DFunLike.congr_fun heq a
    change (scale S c).hom (p ((1 : K) ⊗ₜ[R] a)) =
      (TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))) (dualCoefficients S (v.val a))
    change p ((1 : K) ⊗ₜ[R] a) = dualCoefficients S (v.val a) at ha
    rw [ha]
    apply TrivSqZeroExt.ext
    · exact (TrivSqZeroExt.fst_map _ _).symm
    · change c * _ = _
      simp only [TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  rw [hg, hp, hsc]
  exact hv (CommAlgCat.of R S) s₀

end ExtendedWeights

section FibrePinning

set_option backward.isDefEq.respectTransparency false

open WithConv
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open Specs.IntegralCentralQuotient (spectrumOfAlgHom)
open AdjointRepresentation (GroupPoints constants dualMap scale)
attribute [local instance] pointConvolutionGroup

variable {R K A : Type u} [CommRing R] [Field K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A]

/-- The weight equality in coordinates is the adjoint weight equality for
the geometric fibre, with the character read on the marked torus. -/
private theorem tangentPoint_weight {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (α : X) (v : Tangent R A) (hv : HasWeight t α v)
    {G : GroupScheme K} (T : ClosedSubgroup G) (χ : Character T.group)
    (e : HopfSpectrum K (K ⊗[R] A) ≅ G)
    (s : HopfSpectrum K (K ⊗[R] MonoidAlgebra R X) ≅ T.group)
    (hT : spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) t) ≫ e.hom =
      s.hom ≫ T.inclusion)
    (hχ : characterMonomial (s.hom ≫ χ) = (1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α) :
    tangentPoint e (extendTangent (K := K) v) ∈ CharacterPairing.adjointWeightVectors T χ := by
  intro S a
  let q : WithConv (K ⊗[R] MonoidAlgebra R X →ₐ[K] S) :=
    Spec.mapMulEquiv.symm (a ≫ s.inv.hom.hom)
  have hq : spectrumOfAlgHom q.ofConv ≫ s.hom.hom.hom = a := by
    change Spec.mapMulEquiv q ≫ s.hom.hom.hom = a
    rw [MulEquiv.apply_symm_apply, Category.assoc]
    have hs := congrArg (fun f : T.group ⟶ T.group => f.hom.hom) s.inv_hom_id
    rw [Grp.comp_hom_hom, Grp.id_hom_hom] at hs
    rw [hs, Category.comp_id]
  let tK := Bialgebra.TensorProduct.map (BialgHom.id K K) t
  let g := toConv ((TrivSqZeroExt.inlAlgHom K S S).comp (q.ofConv.comp tK.toAlgHom))
  let p := (dualCoefficients S).comp (extendTangent (K := K) v).val
  let c := q.ofConv ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
  have hc : CharacterPairing.characterValue χ S a = c := by
    rw [← hq]
    have hh : CharacterPairing.characterValue χ S
        (spectrumOfAlgHom q.ofConv ≫ s.hom.hom.hom) =
      CharacterPairing.characterValue (s.hom ≫ χ) S (spectrumOfAlgHom q.ofConv) := by
      unfold CharacterPairing.characterValue
      rw [Category.assoc]
      rfl
    rw [hh]
    exact (characterValue_spectrum (s.hom ≫ χ) q.ofConv).trans (congrArg q.ofConv hχ)
  let W := CommAlgCat.of K (DualNumber S)
  let m : WithConv (K ⊗[R] A →ₐ[K] W) →* GroupPoints G W :=
    (((groupPointsFunctor K).map e.hom).app W).hom.comp Spec.mapMulEquiv.toMonoidHom
  have hg : m g = mapPoints (constants S) (a ≫ T.inclusion.hom.hom) := by
    change spectrumOfAlgHom ((TrivSqZeroExt.inlAlgHom K S S).comp (q.ofConv.comp tK.toAlgHom)) ≫
      e.hom.hom.hom = spectrumOfAlgHom (TrivSqZeroExt.inlAlgHom K S S) ≫
        (a ≫ T.inclusion.hom.hom)
    rw [spectrumOfAlgHom_comp, spectrumOfAlgHom_comp, Category.assoc, Category.assoc]
    change _ ≫ (_ ≫ (spectrumOfHopfHom tK).hom.hom ≫ e.hom.hom.hom) = _
    rw [← Grp.comp_hom_hom, hT, Grp.comp_hom_hom]
    rw [← Category.assoc (spectrumOfAlgHom q.ofConv), hq]
  have hp : m (toConv p) =
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId K S)))
        (tangentPoint e (extendTangent (K := K) v)).toMul.val := by
    change spectrumOfAlgHom p ≫ e.hom.hom.hom =
      spectrumOfAlgHom (dualCoefficients (R := K) S) ≫
        (spectrumOfAlgHom (extendTangent (K := K) v).val ≫ e.hom.hom.hom)
    rw [← Category.assoc, ← spectrumOfAlgHom_comp]
  have hscale : m (toConv ((scale S c).hom.comp p)) = mapPoints (scale S c) (m (toConv p)) := by
    change spectrumOfAlgHom ((scale S c).hom.comp p) ≫ e.hom.hom.hom =
      spectrumOfAlgHom (scale S c).hom ≫ (spectrumOfAlgHom p ≫ e.hom.hom.hom)
    rw [spectrumOfAlgHom_comp, Category.assoc]
  have he := congrArg m (extendTangent_weight t α v hv S q.ofConv)
  change m (g * toConv p * g⁻¹) = m (toConv ((scale S c).hom.comp p)) at he
  rw [map_mul, map_mul, map_inv, hscale, hg, hp] at he
  dsimp only
  rw [hc]
  exact he

private def simpleIndex {D : BasedRootDatum.{u}} {P : SplitBorelPair K}
    {E : AttachedDatum P} (d : BasedIso D E.toBased) (α : Pinning.SimpleRoot P) :
    ↥D.base.support :=
  ⟨d.val.indexEquiv.symm α.val, (mapsSimple_iff d _).mp <| by
    exact (d.val.indexEquiv.apply_symm_apply (show E.toBased.I from α.val)).symm ▸
      (E.simple_iff α.val).mpr α.property⟩

private def attachedSimpleRoot {D : BasedRootDatum.{u}} {P : SplitBorelPair K}
    {E : AttachedDatum P} (d : BasedIso D E.toBased) (i : ↥D.base.support) :
    Pinning.SimpleRoot P :=
  ⟨d.val.indexEquiv i.val, (E.simple_iff _).mp ((mapsSimple_iff d i.val).mpr i.property)⟩

private theorem simpleIndex_attachedSimpleRoot {D : BasedRootDatum.{u}} {P : SplitBorelPair K}
    {E : AttachedDatum P} (d : BasedIso D E.toBased) (i : ↥D.base.support) :
    simpleIndex d (attachedSimpleRoot d i) = i :=
  Subtype.ext (d.val.indexEquiv.symm_apply_apply i.val)

private theorem simpleIndex_character {D : BasedRootDatum.{u}} {P : SplitBorelPair K}
    {E : AttachedDatum P} (d : BasedIso D E.toBased) (α : Pinning.SimpleRoot P) :
    attachedCharacterEquiv d (Multiplicative.ofAdd (D.datum.root (simpleIndex d α).val)) =
      α.val.val := by
  letI := E.comm
  let i := (simpleIndex d α).val
  exact (characterEquiv_root d i).trans
    ((congrArg Multiplicative.ofAdd (E.datum.root_eq (d.val.indexEquiv i))).trans
      (congrArg Subtype.val (d.val.indexEquiv.apply_symm_apply α.val)))

end FibrePinning

section ModelFibre

open Specs.IntegralCentralQuotient (spectrumOfAlgHom)
set_option maxHeartbeats 400000

-- Use the action associated to the given algebra in each tensor product.
local instance (priority := 2000) integralAlgebraModule {A : Type u} [CommRing A]
    [Algebra IntegralRing.{u} A] : Module IntegralRing.{u} A := Algebra.toModule
set_option backward.isDefEq.respectTransparency false

open WithConv

/-- The marked integral tangent bases determine the pinning on the geometric
generic fibre. -/
private theorem fibrePinningExists
    {K : Type u} [Field K] [CharZero K] [Algebra IntegralRing.{u} K]
    (vectorComparison : Pinning.PinningVectors.{u}) {D : BasedRootDatum.{u}}
    (P : Model D)
    {P' : SplitBorelPair K} {E : AttachedDatum P'} (d : BasedIso D E.toBased)
    (e : HopfSpectrum K (K ⊗[IntegralRing.{u}] P.A) ≅ P'.G.val)
    (s : HopfSpectrum K (K ⊗[IntegralRing.{u}] MonoidAlgebra IntegralRing.{u} (Multiplicative D.X)) ≅
      P'.T.group)
    (hT : spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) P.torus) ≫ e.hom =
      s.hom ≫ P'.T.inclusion)
    (hχ : ∀ x : D.X, characterMonomial (s.hom ≫ attachedCharacterEquiv d (Multiplicative.ofAdd x)) =
      (1 : K) ⊗ₜ[IntegralRing.{u}] MonoidAlgebra.of IntegralRing.{u}
        (Multiplicative D.X) (Multiplicative.ofAdd x))
    (L : RootGroups.AdditiveLine K) (U : OrderedRootProducts.RootSubgroupFamily P'.T) :
    ∃ p : Pinning.Pinning L P' U, ∀ α : Pinning.SimpleRoot P',
      RootGroups.rootPoint ((p α).val.hom ≫ (U α.val).val.inclusion)
        (CommAlgCat.of K (DualNumber K)) DualNumber.eps =
      (tangentPoint e (extendTangent (K := K) (P.pin (simpleIndex d α)))).toMul.val := by
  let v (α : Pinning.SimpleRoot P') : Pinning.RootVector P'.T α.val.val :=
    ⟨tangentPoint e (extendTangent (K := K) (P.pin (simpleIndex d α))), by
      apply tangentPoint_weight P.torus
        (Multiplicative.ofAdd (D.datum.root (simpleIndex d α).val))
        _ (P.pin_basis (simpleIndex d α)).1 P'.T α.val.val e s hT
      rw [← simpleIndex_character d α]
      exact hχ _, tangentPoint_ne_zero e _ (extendPin_has_nonzero_coefficient P _)⟩
  obtain ⟨j, hj, _⟩ := vectorComparison L P' U
  refine ⟨j.symm v, fun α => ?_⟩
  have he := hj (j.symm v) α
  rw [Equiv.apply_symm_apply] at he
  exact he.symm


private abbrev extendBialg {R K A B : Type u} [CommRing R] [CommRing K]
    [CommRing A] [CommRing B] [Algebra R K] [Bialgebra R A] [Bialgebra R B]
    (f : A →ₐc[R] B) : K ⊗[R] A →ₐc[K] K ⊗[R] B :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) f

private def hopfPullback {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] (f : HopfSpectrum k B ⟶ HopfSpectrum k A) :
    A →ₐc[k] B :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage f).unop.hom

private theorem spectrum_hopfPullback {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] (f : HopfSpectrum k B ⟶ HopfSpectrum k A) :
    spectrumOfHopfHom (hopfPullback f) = f :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f

private abbrev genericTorusMap {R K X Y : Type u} [CommRing R] [Field K] [Algebra R K]
    [CommGroup X] [CommGroup Y] (h : Y →* X) :
    HopfSpectrum K (K ⊗[R] MonoidAlgebra R X) ⟶
      HopfSpectrum K (K ⊗[R] MonoidAlgebra R Y) :=
  spectrumOfHopfHom (R := K) (C := K ⊗[R] MonoidAlgebra R Y) (D := K ⊗[R] MonoidAlgebra R X)
    (extendBialg (K := K) (MonoidAlgebra.mapDomainBialgHom R h))

private theorem genericTorusMap_monomial {R K X Y : Type u} [CommRing R] [Field K]
    [Algebra R K] [CommGroup X] [CommGroup Y] (h : Y →* X)
    (χ : Character (HopfSpectrum K (K ⊗[R] MonoidAlgebra R Y))) (y : Y)
    (hy : characterMonomial χ = (1 : K) ⊗ₜ[R] MonoidAlgebra.of R Y y) :
    characterMonomial (genericTorusMap h ≫ χ) =
      (1 : K) ⊗ₜ[R] MonoidAlgebra.of R X (h y) := by
  let f := extendBialg (K := K) (MonoidAlgebra.mapDomainBialgHom R h)
  have hcomp : characterMonomial (genericTorusMap h ≫ χ) = f (characterMonomial χ) :=
    characterMonomial_comp (k := K) (A := K ⊗[R] MonoidAlgebra R X)
      (B := K ⊗[R] MonoidAlgebra R Y) f χ
  rw [hcomp, hy]
  simp only [f, extendBialg, Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply,
    MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainBialgHom_single]

/-- The torus map of the lifted field isogeny pulls back the marked integral
characters by the original lattice homomorphism. -/
private theorem genericTorusComparison {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {D E : BasedRootDatum.{u}} {P Q : SplitBorelPair K}
    {A : AttachedDatum P} {B : AttachedDatum Q}
    (d : BasedIso D A.toBased) (e : BasedIso E B.toBased) (h : LatticeMap D E)
    (s : HopfSpectrum K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X)) ≅
      P.T.group)
    (r : HopfSpectrum K (K ⊗[R] MonoidAlgebra R (Multiplicative E.X)) ≅
      Q.T.group)
    (hs : ∀ x : D.X, characterMonomial (s.hom ≫ attachedCharacterEquiv d (Multiplicative.ofAdd x)) =
      (1 : K) ⊗ₜ[R] MonoidAlgebra.of R
        (Multiplicative D.X) (Multiplicative.ofAdd x))
    (hr : ∀ y : E.X, characterMonomial (r.hom ≫ attachedCharacterEquiv e (Multiplicative.ofAdd y)) =
      (1 : K) ⊗ₜ[R] MonoidAlgebra.of R
        (Multiplicative E.X) (Multiplicative.ofAdd y))
    (t : P.T.group ⟶ Q.T.group)
    (ht : ∀ χ : Character Q.T.group, t ≫ χ = (attachedLatticeMap d e h).characters χ)
    (separates : Specs.PinnedUniqueness.CharactersSeparatePoints.{u}) :
    s.hom ≫ t = genericTorusMap (R := R) (K := K) h.characters ≫ r.hom := by
  let S := CommAlgCat.of K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X))
  let f := genericTorusMap (R := R) (K := K) h.characters
  apply Grp.hom_ext
  change (s.hom ≫ t).hom.hom = (f ≫ r.hom).hom.hom
  apply separates Q.split S
  intro χ
  obtain ⟨y, rfl⟩ := (attachedCharacterEquiv e).surjective χ
  let ψ := attachedCharacterEquiv e y
  have ht' : t ≫ ψ = attachedCharacterEquiv d (h.characters y) := by
    have v := ht ψ
    change t ≫ ψ = attachedCharacterEquiv d (h.characters ((attachedCharacterEquiv e).symm ψ)) at v
    rwa [MulEquiv.symm_apply_apply] at v
  have hc : (s.hom ≫ t) ≫ ψ = (f ≫ r.hom) ≫ ψ := by
    apply characterMonomial_injective
    have hmon : characterMonomial (r.hom ≫ ψ) =
        (1 : K) ⊗ₜ[R] MonoidAlgebra.of R (Multiplicative E.X) y := hr y.toAdd
    have hval : characterMonomial (s.hom ≫ attachedCharacterEquiv d (h.characters y)) =
        (1 : K) ⊗ₜ[R] MonoidAlgebra.of R (Multiplicative D.X) (h.characters y) :=
      hs (h.characters y).toAdd
    rw [Category.assoc, Category.assoc, ht', hval]
    exact (genericTorusMap_monomial (R := R) (K := K) h.characters (r.hom ≫ ψ) y hmon).symm
  exact congrArg (fun c : Character _ => c.hom.hom) hc

/-- Marking compatibility on scalar extension of the two integral Hopf algebras. -/
private def GenericLiftsMarking {K : Type u} [Field K] [Algebra IntegralRing.{u} K]
    {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E) (h : LatticeMap D E)
    (f : K ⊗[IntegralRing.{u}] Q.A →ₐc[K] K ⊗[IntegralRing.{u}] P.A) : Prop :=
  (extendBialg P.torus).comp f =
    (extendBialg (MonoidAlgebra.mapDomainBialgHom IntegralRing.{u} h.characters)).comp
      (extendBialg Q.torus) ∧
  ∀ i : ↥D.base.support, (extendTangent (K := K) (P.pin i)).val.comp f.toAlgHom =
    (extendTangent (K := K) (Q.pin ⟨h.roots i.val, (h.simple_iff i.val).mpr i.property⟩)).val

private abbrev extendTorusInclusion {R K A X : Type u} [CommRing R] [Field K]
    [CommRing A] [Algebra R K] [HopfAlgebra R A] [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) :
    HopfSpectrum K (K ⊗[R] MonoidAlgebra R X) ⟶ HopfSpectrum K (K ⊗[R] A) :=
  spectrumOfHopfHom (R := K) (C := K ⊗[R] A) (D := K ⊗[R] MonoidAlgebra R X) (extendBialg (K := K) t)

/-- Apply the characteristic-zero premise to the marked geometric generic
fibres. The resulting morphism matches the integral torus and tangent pins
after extension of scalars. -/
private theorem genericLift
    (lift : Specs.CharZeroLifting.Statement.{u}) (pinnings : Pinning.PinningsExist.{u})
    (vectorComparison : Pinning.PinningVectors.{u})
    (separates : Specs.PinnedUniqueness.CharactersSeparatePoints.{u}) {K : Type u}
    [Field K] [CharZero K] [IsAlgClosed K] [Algebra IntegralRing.{u} K]
    (L : RootGroups.AdditiveLine K) {D E : BasedRootDatum.{u}}
    (P : Model D) (Q : Model E) (h : LatticeMap D E) :
    ∃ f : HopfSpectrum K (K ⊗[IntegralRing.{u}] P.A) ⟶
        HopfSpectrum K (K ⊗[IntegralRing.{u}] Q.A),
      extendTorusInclusion (K := K) P.torus ≫ f =
        genericTorusMap (R := IntegralRing.{u}) (K := K) h.characters ≫
          extendTorusInclusion (K := K) Q.torus ∧
      (∀ i : ↥D.base.support,
        spectrumOfAlgHom (extendTangent (K := K) (P.pin i)).val ≫ f.hom.hom =
          spectrumOfAlgHom (extendTangent (K := K)
            (Q.pin ⟨h.roots i.val, (h.simple_iff i.val).mpr i.property⟩)).val) ∧
      (Function.Bijective h.characters → IsIso f) := by
  obtain ⟨P', p, s, D', d, hp, hs⟩ := P.fibreDatum K
  obtain ⟨Q', q, r, E', e, hq, hr⟩ := Q.fibreDatum K
  obtain ⟨U, _⟩ := pinnings L P'
  obtain ⟨V, _⟩ := pinnings L Q'
  obtain ⟨pinP, hpinP⟩ := fibrePinningExists vectorComparison P d p s hp hs L U
  obtain ⟨pinQ, hpinQ⟩ := fibrePinningExists vectorComparison Q e q r hq hr L V
  let PP : Pinning.PinnedGroup L := ⟨P', U, pinP⟩
  let QQ : Pinning.PinnedGroup L := ⟨Q', V, pinQ⟩
  let hh := attachedLatticeMap d e h
  obtain ⟨F, t, _, _, _, _, hT, _, hχ, hpin, hiso⟩ := lift PP QQ D' E' hh
  refine ⟨p.hom ≫ F ≫ q.inv, ?_, ?_, ?_⟩
  · have ht := genericTorusComparison (R := IntegralRing.{u}) (K := K) d e h s r hs hr t hχ separates
    have hp' : extendTorusInclusion (K := K) P.torus ≫ p.hom = s.hom ≫ P'.T.inclusion := hp
    have hq' : extendTorusInclusion (K := K) Q.torus ≫ q.hom = r.hom ≫ Q'.T.inclusion := hq
    rw [← Category.assoc, hp']
    calc
      _ = (s.hom ≫ t) ≫ Q'.T.inclusion ≫ q.inv := by
        have hTF : P'.T.inclusion ≫ F = t ≫ Q'.T.inclusion := hT
        simpa only [Category.assoc] using
          congrArg (fun b : P'.T.group ⟶ Q'.G.val => s.hom ≫ b ≫ q.inv) hTF
      _ = _ := by
        apply (cancel_mono q.hom).mp
        rw [ht]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hq']
  · intro i
    let j : ↥E.base.support := ⟨h.roots i.val, (h.simple_iff i.val).mpr i.property⟩
    let α := attachedSimpleRoot d i
    let β := attachedSimpleRoot e j
    have hβ : hh.simpleRoot α = β := by
      apply Subtype.ext
      exact congrArg (fun l => e.val.indexEquiv (h.roots l))
        (d.val.indexEquiv.symm_apply_apply i.val)
    have hpin' : (pinP α).val.hom ≫ (U α.val).val.inclusion ≫ F =
        (pinQ (hh.simpleRoot α)).val.hom ≫ (V (hh.simpleRoot α).val).val.inclusion := hpin α
    rw [hβ] at hpin'
    let b := CommAlgCat.of K (DualNumber K)
    have hd := congrArg (fun x : L.group ⟶ Q'.G.val => RootGroups.rootPoint x b DualNumber.eps) hpin'
    have hd' : RootGroups.rootPoint ((pinP α).val.hom ≫ (U α.val).val.inclusion) b
        DualNumber.eps ≫ F.hom.hom =
      RootGroups.rootPoint ((pinQ β).val.hom ≫ (V β.val).val.inclusion) b DualNumber.eps := by
      simpa only [RootGroups.rootPoint, Grp.comp_hom_hom, Category.assoc] using hd
    rw [hpinP, hpinQ, simpleIndex_attachedSimpleRoot, simpleIndex_attachedSimpleRoot] at hd'
    change spectrumOfAlgHom (extendTangent (K := K) (P.pin i)).val ≫ p.hom.hom.hom ≫ F.hom.hom =
      spectrumOfAlgHom (extendTangent (K := K) (Q.pin j)).val ≫ q.hom.hom.hom at hd'
    have hd'' := congrArg (fun m => m ≫ q.inv.hom.hom) hd'
    have hqi : q.hom.hom.hom ≫ q.inv.hom.hom = 𝟙 _ := by
      simpa only [Grp.comp_hom_hom, Grp.id_hom_hom] using
        congrArg (fun a : HopfSpectrum K (K ⊗[IntegralRing.{u}] Q.A) ⟶
          HopfSpectrum K (K ⊗[IntegralRing.{u}] Q.A) => a.hom.hom) q.hom_inv_id
    let z : (testSpec K).obj (op b) ⟶ (HopfSpectrum K (K ⊗[IntegralRing.{u}] Q.A)).X :=
      spectrumOfAlgHom (extendTangent (K := K) (Q.pin j)).val
    change _ = z
    calc
      _ = z ≫ 𝟙 _ := by
        simpa only [Grp.comp_hom_hom, Category.assoc, hqi] using hd''
      _ = z := Category.comp_id z
  · intro hb
    letI : IsIso F := hiso ⟨hh.injective, (attachedCharacterEquiv d).surjective.comp
      (hb.surjective.comp (attachedCharacterEquiv e).symm.surjective)⟩
    infer_instance

private theorem extendBialg_one_tmul {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B] [Algebra R K]
    [Bialgebra R A] [Bialgebra R B] (f : A →ₐc[R] B) (a : A) :
    extendBialg (K := K) f ((1 : K) ⊗ₜ[R] a) = (1 : K) ⊗ₜ[R] f a := rfl

/-- An integral extension of a generically marked map preserves the entire
marking. This uses injective base change on torus functions and scalars. -/
private theorem marking_of_genericAgreement
    {K : Type u} [Field K] [CharZero K] [Algebra IntegralRing.{u} K]
    {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E) (h : LatticeMap D E)
    (f : Q.A →ₐc[IntegralRing.{u}] P.A)
    (g : K ⊗[IntegralRing.{u}] Q.A →ₐc[K] K ⊗[IntegralRing.{u}] P.A)
    (hg : GenericLiftsMarking P Q h g)
    (he : ∀ a : Q.A, g ((1 : K) ⊗ₜ[IntegralRing.{u}] a) =
      (1 : K) ⊗ₜ[IntegralRing.{u}] f a) :
    LiftsMarking P Q h.characters h.roots (fun i hi => (h.simple_iff i).mpr hi) f := by
  let R := IntegralRing.{u}
  have hR : Function.Injective (algebraMap R K) := integralRing_algebraMap_injective K
  constructor
  · apply BialgHom.ext
    intro a
    have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight :
        MonoidAlgebra R (Multiplicative D.X) →ₐ[R] K ⊗[R] MonoidAlgebra R (Multiplicative D.X)) :=
      Algebra.TensorProduct.includeRight_injective hR
    apply hinj
    have hm := DFunLike.congr_fun hg.1 ((1 : K) ⊗ₜ[R] a)
    change (extendBialg (K := K) P.torus) (g (1 ⊗ₜ[R] a)) =
      (extendBialg (K := K) (MonoidAlgebra.mapDomainBialgHom R h.characters))
      ((extendBialg (K := K) Q.torus) (1 ⊗ₜ[R] a)) at hm
    rw [he, extendBialg_one_tmul, extendBialg_one_tmul, extendBialg_one_tmul] at hm
    exact hm
  · intro i
    apply AlgHom.ext
    intro a
    let j : ↥E.base.support := ⟨h.roots i.val, (h.simple_iff i.val).mpr i.property⟩
    have hp := DFunLike.congr_fun (hg.2 i) ((1 : K) ⊗ₜ[R] a)
    rw [AlgHom.comp_apply] at hp
    change (extendTangent (K := K) (P.pin i)).val (g (1 ⊗ₜ[R] a)) =
      (extendTangent (K := K) (Q.pin j)).val (1 ⊗ₜ[R] a) at hp
    rw [he] at hp
    have hs := congrArg TrivSqZeroExt.snd hp
    rw [extendTangent_snd, extendTangent_snd] at hs
    change (P.pin i).val (f a) = (Q.pin j).val a
    apply TrivSqZeroExt.ext
    · have hl := DFunLike.congr_fun (P.pin i).property (f a)
      have hr := DFunLike.congr_fun (Q.pin j).property a
      have hf := DFunLike.congr_fun f.counitAlgHom_comp a
      exact hl.trans (hf.trans hr.symm)
    · exact hR hs

end ModelFibre

section RootCoordinates

attribute [local instance 10000] Algebra.toModule

open Specs.IntegralCentralQuotient (spectrumOfAlgHom)
open OrderedRootProducts (Enumerates)
open private fibre_rootCoordinate from LinearAlgebraicGroups.Classification.IntegralRootCoordinates
open private subgroupIso_of_same from LinearAlgebraicGroups.RootData.RankOneFlag

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private def linkedLatticeMap {D E : BasedRootDatum.{u}} (h : LatticeMap D E) :
    Specs.IntegralLinkedRoots.LatticeMap D E :=
  ⟨h.characters, h.injective, h.finiteIndex, h.roots, h.simple_iff, h.root_eq, h.coroot_eq⟩

private theorem extendCoordinate_eq {R K A : Type u} [CommRing R] [Field K]
    [CommRing A] [Algebra R K] [HopfAlgebra R A] (x : A →ₐ[R] Polynomial R) :
    Specs.IntegralRelativeCell.extendCoordinate K x = Specs.IntegralLinkedRoots.extendRoot (K := K) x := by
  unfold Specs.IntegralRelativeCell.extendCoordinate Specs.IntegralLinkedRoots.extendRoot
  congr 1

private theorem modelRootCoordinates {D : BasedRootDatum.{u}} (P : Model D) :
    ∃ x : D.I → P.A →ₐ[IntegralRing.{u}] Polynomial IntegralRing.{u},
      Specs.IntegralLinkedRoots.RootCoordinates P.torus P.pin x := by
  obtain ⟨x, hs, hm, h0, hw, hp, hf⟩ :=
    Classification.IntegralRootCoordinates.integralRootCoordinates P.torus P.finitePresentation
      P.smooth P.torus_surjective P.fibreDatum P.pin P.pin_basis
  refine ⟨x, fun i => ⟨hs i, fun S => ⟨h0 i S, hm i S⟩, hw i⟩, hp, ?_⟩
  intro K _ _ _
  obtain ⟨Q, e, s, E, d, ht, hmon⟩ := P.fibreDatum K
  let F : Specs.IntegralLinkedRoots.FibreFrame D P.torus K := ⟨Q, e, s, E, d, ht, hmon⟩
  refine ⟨F, fun i => ?_⟩
  obtain ⟨U, L, j, hU, _, _, hcoord⟩ := hf i K Q e s E d ht hmon
  refine ⟨U, L, j, hU, fun S a => ?_⟩
  change spectrumOfAlgHom ((Polynomial.aeval a : Polynomial K →ₐ[K] S).comp
    (Specs.IntegralRootCoordinates.fibreCoordinate K (x i))) ≫ e.hom.hom.hom = _
  rw [spectrumOfAlgHom_comp, Category.assoc, hcoord]
  rfl

private theorem additiveLine_eq {K : Type u} [Field K] (L M : RootGroups.AdditiveLine K) : L = M := by
  have hd : L.operations.delta = M.operations.delta :=
    Polynomial.algHom_ext (L.comultiplication.trans M.comultiplication.symm)
  have hc : L.operations.epsilon = M.operations.epsilon :=
    Polynomial.algHom_ext (L.counit.trans M.counit.symm)
  have hi : L.operations.inverse = M.operations.inverse :=
    Polynomial.algHom_ext (L.antipode.trans M.antipode.symm)
  rcases L with ⟨⟨_, _, _, _, _, _, _, _⟩, _, _, _⟩
  rcases M with ⟨⟨_, _, _, _, _, _, _, _⟩, _, _, _⟩
  cases hd
  cases hc
  cases hi
  rfl

private theorem modelFibreCoordinates {D : BasedRootDatum.{u}} (P : Model D)
    {x : D.I → P.A →ₐ[IntegralRing.{u}] Polynomial IntegralRing.{u}}
    (hx : Specs.IntegralLinkedRoots.RootCoordinates P.torus P.pin x)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra IntegralRing.{u} K] :
    ∃ F : Specs.IntegralRelativeCell.FibreDatum D P.torus K, Specs.IntegralRelativeCell.FibreCoordinates F x := by
  obtain ⟨Q, e, s, E, d, ht, hmon⟩ := P.fibreDatum K
  let F : Specs.IntegralRelativeCell.FibreDatum D P.torus K := ⟨Q, e, s, E, d, ht, hmon⟩
  let L := Classification.Pinning.standardAdditiveLine K
  obtain ⟨U, _⟩ := Classification.Pinning.pinningsExist L Q
  refine ⟨F, L, U, fun i => ?_⟩
  obtain ⟨V, M, j, _, hu, ha, hj⟩ := fibre_rootCoordinate P.torus i (x i)
    (hx.1 i).1 ⟨fun S => (hx.1 i).2.1 S |>.2, fun S => (hx.1 i).2.1 S |>.1, (hx.1 i).2.2⟩
      K Q e s E d ht hmon
  let α := d.val.indexEquiv i
  obtain ⟨v, hv⟩ := subgroupIso_of_same (hu (U α).val (U α).property)
  have heq : M = L := additiveLine_eq M L
  subst M
  refine ⟨⟨j ≪≫ v, ?_⟩, ?_⟩
  · change RootGroups.HasScalarAction Q.T α.val ((j.hom ≫ v.hom) ≫ (U α).val.inclusion)
    rw [Category.assoc, hv]
    exact ha
  · change spectrumOfAlgHom (Specs.IntegralRelativeCell.extendCoordinate K (x i)) ≫ e.hom.hom.hom =
      (j.hom ≫ v.hom).hom.hom ≫ (U α).val.inclusion.hom.hom
    rw [extendCoordinate_eq]
    change spectrumOfAlgHom (Specs.IntegralRootCoordinates.fibreCoordinate K (x i)) ≫ e.hom.hom.hom = _
    rw [hj]
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      (congrArg (fun f : V.group ⟶ Q.G.val => j.hom.hom.hom ≫ f.hom.hom) hv).symm

private theorem preserves_positive {D E : BasedRootDatum.{u}} (h : LatticeMap D E) (i : D.I) :
    E.base.IsPos (h.roots i) ↔ D.base.IsPos i := by
  letI := D.finiteRoots
  letI := E.finiteRoots
  let p : E.X →+ D.X := h.characters.toAdditive
  have hr (j : D.I) : p (E.datum.root (h.roots j)) = D.datum.root j :=
    congrArg Multiplicative.toAdd (h.root_eq j)
  have hr' (j : E.I) : p (E.datum.root j) = D.datum.root (h.roots.symm j) := by
    rw [← hr (h.roots.symm j), Equiv.apply_symm_apply]
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · have H : ∀ {j}, E.base.IsPos j → D.base.IsPos (h.roots.symm j) := by
      intro j hj
      refine hj.induction_on_add (fun a ha => D.base.isPos_of_mem_support
        ((h.simple_iff (h.roots.symm a)).mp (by simpa using ha))) ?_
      intro a b c hab ha hb
      apply ha.add (D.base.isPos_of_mem_support ((h.simple_iff (h.roots.symm b)).mp (by simpa using hb)))
      rw [← hr' c, ← hr' a, ← hr' b, hab, map_add]
    simpa using H hi
  · refine hi.induction_on_add (fun a ha => E.base.isPos_of_mem_support ((h.simple_iff a).mpr ha)) ?_
    intro a b c hab ha hb
    apply ha.add (E.base.isPos_of_mem_support ((h.simple_iff b).mpr hb))
    apply h.injective
    change Multiplicative.ofAdd (p (E.datum.root (h.roots c))) =
      Multiplicative.ofAdd (p (E.datum.root (h.roots a) + E.datum.root (h.roots b)))
    rw [hr, map_add, hr, hr, hab]

private theorem enumerated_roots {I : Type u} [Finite I] (S : Set I) :
    ∃ l : List I, Enumerates l S := by
  classical
  letI := Fintype.ofFinite I
  let s := Finset.univ.filter (· ∈ S)
  exact ⟨s.toList, Finset.nodup_toList _, fun i => by simp [s]⟩

private theorem enumerates_map {I J : Type u} (e : I ≃ J) {l : List I} {S : Set I} {T : Set J}
    (hl : Enumerates l S) (h : ∀ i, e i ∈ T ↔ i ∈ S) : Enumerates (l.map e) T := by
  refine ⟨hl.1.map e.injective, fun j => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective j
  simpa only [List.mem_map, e.injective.eq_iff, exists_eq_right, h] using hl.2 i

end RootCoordinates

section CellMaps

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj CategoryTheory.Obj
open Specs.IntegralCentralQuotient (OverBase spectrumOfAlgHom cellMap lineProduct rootProduct)
open Specs.IntegralRelativeCell (cellDivision)

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

private def relabelLineProduct {I J : Type u} (e : I → J) :
    (l : List I) → lineProduct R l ≅ lineProduct R (l.map e)
  | [] => Iso.refl _
  | _ :: l => tensorIso (Iso.refl _) (relabelLineProduct e l)

private abbrev Cell {I : Type u} (l m : List I) (T : OverBase R) : OverBase R :=
  lineProduct R l ⊗ (T ⊗ lineProduct R m)

private def cellChange {I J : Type u} {T U : OverBase R} (e : I → J) (d : T ⟶ U)
    (l m : List I) : Cell l m T ⟶ Cell (l.map e) (m.map e) U :=
  (relabelLineProduct e l).hom ⊗ₘ (d ⊗ₘ (relabelLineProduct e m).hom)

private theorem cellChange_isIso {I J : Type u} {T U : OverBase R} (e : I → J) (d : T ⟶ U)
    [IsIso d] (l m : List I) : IsIso (cellChange e d l m) := by
  change IsIso (_ ⊗ₘ (d ⊗ₘ _))
  infer_instance

variable {A B : Type u} [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]

private theorem rootProduct_relabel {I J : Type u} (e : I → J)
    (y : J → A →ₐ[R] Polynomial R) (l : List I) :
    (relabelLineProduct e l).hom ≫ rootProduct y (l.map e) =
      rootProduct (fun i => y (e i)) l := by
  induction l with
  | nil => exact Category.id_comp _
  | cons i l ih =>
    change (relabelLineProduct e (i :: l)).hom ≫ rootProduct y (e i :: l.map e) = _
    simp only [relabelLineProduct, tensorIso_hom, Iso.refl_hom, rootProduct,
      MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp, ih]

private theorem map_rootProduct {K I J : Type u} [CommRing K]
    (F : OverBase R ⥤ OverBase K) [F.Monoidal]
    (g : F.mapGrp.obj (HopfSpectrum R A) ⟶ F.mapGrp.obj (HopfSpectrum R B))
    (e : I → J) (x : I → A →ₐ[R] Polynomial R) (y : J → B →ₐ[R] Polynomial R)
    (hr : ∀ i, F.map (spectrumOfAlgHom (x i)) ≫ g.hom.hom =
      F.map (spectrumOfAlgHom (y (e i)))) (l : List I) :
    F.map (rootProduct x l) ≫ g.hom.hom = F.map (rootProduct (fun i => y (e i)) l) := by
  induction l with
  | nil =>
    simp only [rootProduct, Functor.map_one]
    exact MonObj.one_comp _
  | cons i l ih =>
    simp only [rootProduct, Functor.map_mul, Functor.map_comp, MonObj.mul_comp, Category.assoc, hr, ih]

set_option maxHeartbeats 1200000 in
private theorem map_cell {K I J X Y : Type u} [CommRing K] [CommGroup X] [CommGroup Y]
    (F : OverBase R ⥤ OverBase K) [F.Monoidal]
    (g : F.mapGrp.obj (HopfSpectrum R A) ⟶ F.mapGrp.obj (HopfSpectrum R B))
    (e : I → J) (x : I → A →ₐ[R] Polynomial R) (y : J → B →ₐ[R] Polynomial R)
    (t : A →ₐc[R] MonoidAlgebra R X) (s : B →ₐc[R] MonoidAlgebra R Y)
    (d : (HopfSpectrum R (MonoidAlgebra R X)).X ⟶ (HopfSpectrum R (MonoidAlgebra R Y)).X)
    (hr : ∀ i, F.map (spectrumOfAlgHom (x i)) ≫ g.hom.hom =
      F.map (spectrumOfAlgHom (y (e i))))
    (ht : F.map (spectrumOfHopfHom t).hom.hom ≫ g.hom.hom =
      F.map (d ≫ (spectrumOfHopfHom s).hom.hom))
    (l m : List I) :
    F.map (cellMap t x l m) ≫ g.hom.hom =
      F.map (cellChange e d l m ≫ cellMap s y (l.map e) (m.map e)) := by
  simp only [cellChange, cellMap, MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc,
    Category.assoc, rootProduct_relabel, Functor.map_mul, Functor.map_comp, MonObj.mul_comp,
    map_rootProduct F g e x y hr]
  rw [Functor.map_comp] at ht
  simp only [ht]

private theorem map_cellDivision {K : Type u} [CommRing K]
    (F : OverBase R ⥤ OverBase K) [F.Monoidal]
    {G H : Grp (OverBase R)} (g : F.mapGrp.obj G ⟶ F.mapGrp.obj H)
    {W V : OverBase R} {i : W ⟶ G.X} {j : V ⟶ H.X} (v : W ⟶ V)
    (h : F.map i ≫ g.hom.hom = F.map (v ≫ j)) :
    F.map (cellDivision G i) ≫ g.hom.hom =
      F.map ((v ⊗ₘ v) ≫ cellDivision H j) := by
  simp only [cellDivision, MonObj.comp_mul, GrpObj.comp_inv, tensorHom_fst_assoc,
    tensorHom_snd_assoc, Category.assoc, Functor.map_comp, Functor.map_mul, Functor.map_inv',
    MonObj.mul_comp, GrpObj.inv_comp] at h ⊢
  rw [h]

end CellMaps

section GenericCells

attribute [local instance 10000] Algebra.toModule

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open Specs.IntegralCentralQuotient (OverBase spectrumOfAlgHom cellMap lineProduct fibreGroup)
open Specs.IntegralRelativeCell (cellDivision FaithfullyFlatCellCover)
open private changeOfBase fibreSpecIso fibreGroupIso fibreSpecIso_natural lineFibreIso lineFibreIso_comm
  from LinearAlgebraicGroups.Classification.IntegralRelativeCell

set_option backward.isDefEq.respectTransparency false

private def affinePullback {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (f : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R B)) ⟶
      (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))) : A →ₐ[R] B :=
  ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage f).unop.hom

private theorem spectrum_affinePullback {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (f : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R B)) ⟶
      (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))) :
    spectrumOfAlgHom (affinePullback f) = f :=
  (algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage f

private theorem spectrumOfAlgHom_injective {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    Function.Injective (fun f : A →ₐ[R] B => spectrumOfAlgHom f) := by
  intro f g h
  exact congrArg (fun e => e.unop.hom)
    ((algSpec.fullyFaithful (R := CommRingCat.of R)).map_injective h)

private theorem spectrumOfHopfHom_left_injective {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B] :
    Function.Injective (fun f : A →ₐc[R] B => (spectrumOfHopfHom f).hom.hom) := by
  intro f g h
  exact BialgHom.ext fun a => DFunLike.congr_fun (spectrumOfAlgHom_injective h) a

private theorem hopfSquare_of_spectrum {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [HopfAlgebra R A] [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R D]
    (f : B →ₐc[R] A) (s : A →ₐc[R] C) (t : B →ₐc[R] D) (a : D →ₐc[R] C)
    (h : spectrumOfHopfHom s ≫ spectrumOfHopfHom f =
      spectrumOfHopfHom a ≫ spectrumOfHopfHom t) : s.comp f = a.comp t := by
  apply spectrumOfHopfHom_left_injective
  exact congrArg (fun m : HopfSpectrum R C ⟶ HopfSpectrum R B => m.hom.hom)
    ((spectrumOfHopfHom_comp s f).trans (h.trans (spectrumOfHopfHom_comp a t).symm))

private theorem genericTorus_comm {R K A B X Y : Type u} [CommRing R] [Field K]
    [CommRing A] [CommRing B] [Algebra R K] [HopfAlgebra R A] [HopfAlgebra R B]
    [CommGroup X] [CommGroup Y] (t : A →ₐc[R] MonoidAlgebra R X) (s : B →ₐc[R] MonoidAlgebra R Y)
    (h : Y →* X) (f : HopfSpectrum K (K ⊗[R] A) ⟶ HopfSpectrum K (K ⊗[R] B))
    (hf : extendTorusInclusion (K := K) t ≫ f = genericTorusMap (R := R) (K := K) h ≫
      extendTorusInclusion (K := K) s) :
    (extendBialg (K := K) t).comp (hopfPullback f) =
      (extendBialg (K := K) (MonoidAlgebra.mapDomainBialgHom R h)).comp (extendBialg (K := K) s) := by
  apply hopfSquare_of_spectrum
  rw [spectrum_hopfPullback]
  exact hf

set_option maxHeartbeats 1500000 in
private theorem genericLiftOnAlgebras {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    [Algebra IntegralRing.{u} K] {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E)
    (h : LatticeMap D E) :
    ∃ g : K ⊗[IntegralRing.{u}] Q.A →ₐc[K] K ⊗[IntegralRing.{u}] P.A,
      GenericLiftsMarking P Q h g := by
  obtain ⟨f, ht, hp, _⟩ := genericLift LinearAlgebraicGroups.CharZeroLifting.centralIsogeny
    Classification.Pinning.pinningsExist Classification.Pinning.pinningVectors
    Classification.PinnedUniqueness.charactersSeparatePoints
    (Classification.Pinning.standardAdditiveLine K) P Q h
  refine ⟨hopfPullback f, ?_, fun i => ?_⟩
  · exact genericTorus_comm P.torus Q.torus h.characters f ht
  · apply spectrumOfAlgHom_injective
    dsimp only
    rw [spectrumOfAlgHom_comp]
    change spectrumOfAlgHom (extendTangent (K := K) (P.pin i)).val ≫
      (spectrumOfHopfHom (hopfPullback f)).hom.hom = _
    rw [spectrum_hopfPullback]
    exact hp i

private theorem genericMarking_of_integral {K : Type u} [Field K] [Algebra IntegralRing.{u} K]
    {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E) (h : LatticeMap D E)
    (f : Q.A →ₐc[IntegralRing.{u}] P.A)
    (hf : LiftsMarking P Q h.characters h.roots (fun i hi => (h.simple_iff i).mpr hi) f) :
    GenericLiftsMarking P Q h (extendBialg (K := K) f) := by
  refine ⟨?_, fun i => ?_⟩
  · apply BialgHom.ext
    intro a
    refine TensorProduct.inductionOn a ?_ ?_
    · intro k b
      have e := DFunLike.congr_fun hf.1 b
      change P.torus (f b) = MonoidAlgebra.mapDomainBialgHom IntegralRing.{u} h.characters
        (Q.torus b) at e
      change k ⊗ₜ[IntegralRing.{u}] P.torus (f b) =
        k ⊗ₜ[IntegralRing.{u}] MonoidAlgebra.mapDomainBialgHom IntegralRing.{u} h.characters
          (Q.torus b)
      rw [e]
    · intro a b ha hb
      simp only [map_add, ha, hb]
  · let R := IntegralRing.{u}
    apply (AlgHom.liftEquiv R K Q.A (DualNumber K)).symm.injective
    apply AlgHom.ext
    intro a
    change (extendTangent (K := K) (P.pin i)).val
        ((extendBialg (K := K) f) ((1 : K) ⊗ₜ[R] a)) =
      (extendTangent (K := K) (Q.pin ⟨h.roots i.val, (h.simple_iff i.val).mpr i.property⟩)).val
        ((1 : K) ⊗ₜ[R] a)
    rw [extendBialg_one_tmul, extendTangent_one_tmul, extendTangent_one_tmul]
    exact congrArg (dualCoefficients K) (DFunLike.congr_fun (hf.2 i) a)

private theorem extendLinkedTangent_eq {R K A : Type u} [CommRing R] [Field K] [Algebra R K]
    [CommRing A] [HopfAlgebra R A] (v : Tangent R A) :
    Specs.IntegralLinkedRoots.extendTangent (K := K) v = (extendTangent (K := K) v).val := by
  let e := AlgHom.liftEquiv R K A (DualNumber K)
  apply e.symm.injective
  apply AlgHom.ext
  intro a
  change e.symm (e ((Specs.IntegralLinkedRoots.dualCoefficients K).comp v.val)) a =
    (extendTangent (K := K) v).val ((1 : K) ⊗ₜ[R] a)
  rw [Equiv.symm_apply_apply, extendTangent_one_tmul]
  rfl

private theorem linkedMarking_of_generic {K : Type u} [Field K] [Algebra IntegralRing.{u} K]
    {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E) (h : LatticeMap D E)
    (g : K ⊗[IntegralRing.{u}] Q.A →ₐc[K] K ⊗[IntegralRing.{u}] P.A)
    (hg : GenericLiftsMarking P Q h g) :
    Specs.IntegralLinkedRoots.GenericMarking P.torus Q.torus P.pin Q.pin (linkedLatticeMap h) g := by
  refine ⟨hg.1, fun i b => ?_⟩
  let j : ↥E.base.support := ⟨h.roots i.val, (h.simple_iff i.val).mpr i.property⟩
  rw [extendLinkedTangent_eq]
  change (extendTangent (K := K) (P.pin i)).val (g ((1 : K) ⊗ₜ[IntegralRing.{u}] b)) =
    dualCoefficients K ((Q.pin j).val b)
  exact (DFunLike.congr_fun (hg.2 i) ((1 : K) ⊗ₜ[IntegralRing.{u}] b)).trans
    (extendTangent_one_tmul (Q.pin j) b)

open private polynomial_extend_apply from LinearAlgebraicGroups.Classification.IntegralLinkedRoots

private theorem integralRootMatch {R K A B : Type u} [CommRing R] [Field K] [Algebra R K]
    [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]
    (hK : Function.Injective (algebraMap R K)) (f : B →ₐc[R] A)
    (g : K ⊗[R] B →ₐc[K] K ⊗[R] A)
    (hf : ∀ b : B, g ((1 : K) ⊗ₜ[R] b) = (1 : K) ⊗ₜ[R] f b)
    (x : A →ₐ[R] Polynomial R) (y : B →ₐ[R] Polynomial R)
    (hm : (Specs.IntegralLinkedRoots.extendRoot (K := K) x).comp g.toAlgHom =
      Specs.IntegralLinkedRoots.extendRoot (K := K) y) : x.comp f.toAlgHom = y := by
  apply AlgHom.ext
  intro b
  have he := DFunLike.congr_fun hm ((1 : K) ⊗ₜ[R] b)
  change Specs.IntegralLinkedRoots.extendRoot (K := K) x (g (1 ⊗ₜ[R] b)) =
    Specs.IntegralLinkedRoots.extendRoot (K := K) y (1 ⊗ₜ[R] b) at he
  rw [hf, polynomial_extend_apply, polynomial_extend_apply] at he
  exact Polynomial.map_injective (algebraMap R K) hK he

variable {R K A B : Type u} [CommRing R] [Field K] [Algebra R K]
  [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]

private def fibreMapOfBialg (g : K ⊗[R] B →ₐc[K] K ⊗[R] A) :
    (fibreGroup (R := R) K).obj (HopfSpectrum R A) ⟶
      (fibreGroup (R := R) K).obj (HopfSpectrum R B) :=
  (fibreGroupIso (R := R) K A).hom ≫ spectrumOfHopfHom g ≫ (fibreGroupIso (R := R) K B).inv

private theorem fibreMapOfBialg_comm (g : K ⊗[R] B →ₐc[K] K ⊗[R] A) :
    (fibreMapOfBialg g).hom.hom ≫ (fibreSpecIso (R := R) K B).hom =
      (fibreSpecIso (R := R) K A).hom ≫ spectrumOfAlgHom g.toAlgHom := by
  change (fibreSpecIso K A).hom ≫ (spectrumOfAlgHom g.toAlgHom ≫
    (fibreSpecIso K B).inv) ≫ (fibreSpecIso K B).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem baseChange_compatibility {C : Type u} [CommRing C] [Algebra R C]
    (q : A →ₐ[R] C) (p : B →ₐ[R] C) (g : K ⊗[R] B →ₐc[K] K ⊗[R] A) :
    (changeOfBase K).map (spectrumOfAlgHom q) ≫ (fibreMapOfBialg g).hom.hom =
        (changeOfBase K).map (spectrumOfAlgHom p) ↔
      (Algebra.TensorProduct.map (AlgHom.id K K) q).comp g.toAlgHom =
        Algebra.TensorProduct.map (AlgHom.id K K) p := by
  let F := changeOfBase (R := R) K
  let eC := fibreSpecIso (R := R) K C
  let eB := fibreSpecIso (R := R) K B
  have hq : eC.inv ≫ F.map (spectrumOfAlgHom q) ≫ (fibreMapOfBialg g).hom.hom ≫ eB.hom =
      spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) q) ≫ spectrumOfAlgHom g.toAlgHom := by
    rw [fibreMapOfBialg_comm]
    have e := congrArg (fun v => v ≫ (fibreSpecIso K A).hom ≫ spectrumOfAlgHom g.toAlgHom)
      (fibreSpecIso_natural K q)
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using e
  have hp : eC.inv ≫ F.map (spectrumOfAlgHom p) ≫ eB.hom =
      spectrumOfAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) p) := by
    have e := congrArg (fun v => v ≫ eB.hom) (fibreSpecIso_natural K p)
    simpa only [eB, Category.assoc, Iso.inv_hom_id, Category.comp_id] using e
  change F.map (spectrumOfAlgHom q) ≫ _ = F.map (spectrumOfAlgHom p) ↔ _
  rw [← cancel_epi eC.inv, ← cancel_mono eB.hom]
  simp only [Category.assoc, hq, hp, ← spectrumOfAlgHom_comp]
  exact spectrumOfAlgHom_injective.eq_iff

private theorem genericCellMatch {I J X Y : Type u} [CommGroup X] [CommGroup Y]
    (t : A →ₐc[R] MonoidAlgebra R X) (s : B →ₐc[R] MonoidAlgebra R Y)
    (a : Y →* X) (e : I → J) (x : I → A →ₐ[R] Polynomial R) (y : J → B →ₐ[R] Polynomial R)
    (g : K ⊗[R] B →ₐc[K] K ⊗[R] A)
    (ht : (extendBialg (K := K) t).comp g =
      (extendBialg (K := K) (MonoidAlgebra.mapDomainBialgHom R a)).comp (extendBialg (K := K) s))
    (hr : ∀ i, (Specs.IntegralLinkedRoots.extendRoot (K := K) (x i)).comp g.toAlgHom =
      Specs.IntegralLinkedRoots.extendRoot (K := K) (y (e i))) (l m : List I) :
    (changeOfBase K).map (cellMap t x l m) ≫ (fibreMapOfBialg g).hom.hom =
      (changeOfBase K).map
        (cellChange e (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R a)).hom.hom l m ≫
          cellMap s y (l.map e) (m.map e)) := by
  let F := changeOfBase (R := R) K
  apply map_cell F (fibreMapOfBialg g) e x y t s
  · intro i
    let L := lineFibreIso (R := R) K
    have hline {C : Type u} [CommRing C] [HopfAlgebra R C] (z : C →ₐ[R] Polynomial R) :
        L.hom ≫ F.map (spectrumOfAlgHom z) ≫ (fibreSpecIso K C).hom =
          spectrumOfAlgHom (Specs.IntegralLinkedRoots.extendRoot (K := K) z) := by
      have hz := congrArg (fun w => w ≫ (fibreSpecIso K C).hom) (lineFibreIso_comm K z)
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, extendCoordinate_eq] using hz
    rw [← cancel_epi L.hom, ← cancel_mono (fibreSpecIso (R := R) K B).hom]
    simp only [Category.assoc, fibreMapOfBialg_comm]
    calc
      _ = (L.hom ≫ F.map (spectrumOfAlgHom (x i)) ≫ (fibreSpecIso K A).hom) ≫
          spectrumOfAlgHom g.toAlgHom := by simp only [Category.assoc]
      _ = spectrumOfAlgHom (Specs.IntegralLinkedRoots.extendRoot (K := K) (y (e i))) := by
        rw [hline, ← spectrumOfAlgHom_comp, hr]
      _ = _ := (hline (y (e i))).symm
  · let d := MonoidAlgebra.mapDomainBialgHom R a
    change F.map (spectrumOfAlgHom t.toAlgHom) ≫ (fibreMapOfBialg g).hom.hom =
      F.map (spectrumOfAlgHom d.toAlgHom ≫ spectrumOfAlgHom s.toAlgHom)
    rw [← spectrumOfAlgHom_comp]
    apply (baseChange_compatibility t.toAlgHom (d.toAlgHom.comp s.toAlgHom) g).mpr
    rw [Algebra.TensorProduct.map_id_comp]
    exact congrArg BialgHom.toAlgHom ht

private theorem faithfulFlatCover_descends
    [Module.Flat R A] [Module.Flat R K] (hK : Function.Injective (algebraMap R K))
    {W V : OverBase R} (i : W ⟶ (HopfSpectrum R A).X)
    (j : V ⟶ (HopfSpectrum R B).X) (v : W ⟶ V) (cover : FaithfullyFlatCellCover i)
    (g : K ⊗[R] B →ₐc[K] K ⊗[R] A)
    (h : (changeOfBase K).map i ≫ (fibreMapOfBialg g).hom.hom =
      (changeOfBase K).map (v ≫ j)) :
    ∃ f : B →ₐc[R] A, ∀ b : B, g ((1 : K) ⊗ₜ[R] b) = (1 : K) ⊗ₜ[R] f b := by
  obtain ⟨C, e, q, hq, hff⟩ := cover
  let d := (v ⊗ₘ v) ≫ cellDivision (HopfSpectrum R B) j
  let p := affinePullback (e.hom ≫ d)
  have hloc : (changeOfBase K).map (spectrumOfAlgHom q) ≫ (fibreMapOfBialg g).hom.hom =
      (changeOfBase K).map (spectrumOfAlgHom p) := by
    rw [hq, spectrum_affinePullback, Functor.map_comp, Category.assoc,
      map_cellDivision (changeOfBase K) (fibreMapOfBialg g) v h, ← Functor.map_comp]
  have he := (baseChange_compatibility q p g).mp hloc
  letI : Algebra A C := q.toRingHom.toAlgebra
  letI : IsScalarTower R A C := IsScalarTower.of_algHom q
  letI : Module.FaithfullyFlat A C := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  apply descendAffineBialgebraMap hK g p
  intro b
  exact (DFunLike.congr_fun he ((1 : K) ⊗ₜ[R] b)).symm

end GenericCells

section DifferenceCovers

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open Specs.IntegralRelativeCell (cellDivision)

set_option backward.isDefEq.respectTransparency false

private theorem pullback_of_cover_epi {S : Scheme.{u}} {X Y Z : Over S} (d : X ⟶ Y) (a : Z ⟶ Y)
    [Flat d.left] [Surjective d.left] : Epi (pullback.snd d a) := by
  let F := Over.forget S
  have hp := (IsPullback.of_hasPullback d a).map F
  letI : Flat (pullback.snd d a).left := MorphismProperty.of_isPullback hp ‹Flat d.left›
  letI : Surjective (pullback.snd d a).left := MorphismProperty.of_isPullback hp ‹Surjective d.left›
  letI := Flat.epi_of_flat_of_surjective (pullback.snd d a).left
  exact Over.epi_of_epi_left _

private theorem cellDivision_comm {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)
    {U V : Over S} {i : U ⟶ G.X} {j : V ⟶ H.X} (e : U ⟶ V)
    (h : i ≫ f.hom.hom = e ≫ j) :
    cellDivision G i ≫ f.hom.hom = (e ⊗ₘ e) ≫ cellDivision H j := by
  simp only [cellDivision, MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul, GrpObj.comp_inv,
    tensorHom_fst_assoc, tensorHom_snd_assoc, Category.assoc, h]

private theorem groupMaps_eq_of_cell {S : Scheme.{u}} {G H : Grp (Over S)}
    {f g : G ⟶ H} {U : Over S} (i : U ⟶ G.X)
    [Flat (cellDivision G i).left] [Surjective (cellDivision G i).left]
    (h : i ≫ f.hom.hom = i ≫ g.hom.hom) : f = g := by
  letI := Flat.epi_of_flat_of_surjective (cellDivision G i).left
  letI := Over.epi_of_epi_left (cellDivision G i)
  apply Grp.hom_ext
  apply (cancel_epi (cellDivision G i)).mp
  simp only [cellDivision, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, h]

private theorem groupIso_of_schemeIso {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)
    [IsIso f.hom.hom.left] : IsIso f := by
  letI : IsIso ((Over.forget S).map f.hom.hom) := inferInstanceAs (IsIso f.hom.hom.left)
  letI : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget S)
  let e : G ≅ H := Grp.mkIso (asIso f.hom.hom) (IsMonHom.one_hom (f := f.hom.hom))
    (IsMonHom.mul_hom (f := f.hom.hom))
  have he : e.hom = f := Grp.hom_ext _ _ rfl
  exact he ▸ e.isIso_hom

/-- A difference cover detects the kernel of a homomorphism that identifies the
two cells. The target cell's difference cover then supplies an inverse. -/
private theorem groupIso_of_matching_cells {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) {U V C : Over S} (i : U ⟶ G.X) (j : V ⟶ H.X) [Mono j]
    (e : U ≅ V) (h : i ≫ f.hom.hom = e.hom ≫ j)
    (d : C ⟶ G.X) [Flat d.left] [Surjective d.left] (a : C ⟶ U ⊗ U)
    (hd : d = a ≫ cellDivision G i)
    [Smooth (cellDivision H j).left] [Surjective (cellDivision H j).left] : IsIso f := by
  have hk {Y : Over S} (k : Y ⟶ G.X) (hk : k ≫ f.hom.hom = 1) : k = 1 := by
    let p := pullback.snd d k
    letI : Epi p := pullback_of_cover_epi d k
    apply (cancel_epi p).mp
    let w := pullback.fst d k ≫ a
    let u := w ≫ fst U U
    let v := w ≫ snd U U
    have hfact : p ≫ k = (u ≫ i) * (v ≫ i)⁻¹ := by
      calc
        p ≫ k = pullback.fst d k ≫ d := pullback.condition.symm
        _ = pullback.fst d k ≫ a ≫ cellDivision G i := congrArg (_ ≫ ·) hd
        _ = _ := by simp [w, u, v, cellDivision, MonObj.comp_mul, GrpObj.comp_inv]
    have hf : (u ≫ i) ≫ f.hom.hom = (v ≫ i) ≫ f.hom.hom := by
      apply mul_inv_eq_one.mp
      rw [← GrpObj.inv_comp, ← MonObj.mul_comp, ← hfact, Category.assoc, hk, MonObj.comp_one]
    have he : u = v := (cancel_mono (e.hom ≫ j)).mp (by
      simpa only [Category.assoc, h] using hf)
    rw [hfact, he, mul_inv_cancel, MonObj.comp_one]
  haveI : Mono f.hom.hom := ⟨fun a b hab => by
    apply mul_inv_eq_one.mp
    apply hk
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, mul_inv_cancel]⟩
  let s := (e.inv ⊗ₘ e.inv) ≫ cellDivision G i
  have hs : s ≫ f.hom.hom = cellDivision H j := by
    rw [Category.assoc, cellDivision_comm f e.hom h, ← Category.assoc, tensorHom_comp_tensorHom]
    simp
  haveI : StrongEpi (s.left ≫ f.hom.hom.left) := by
    rw [← Over.comp_left, hs]
    infer_instance
  haveI : StrongEpi f.hom.hom.left := strongEpi_of_strongEpi s.left f.hom.hom.left
  letI : IsIso f.hom.hom.left := isIso_of_mono_of_strongEpi _
  exact groupIso_of_schemeIso f

end DifferenceCovers

section IntegralLift

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open Specs.IntegralCentralQuotient (OverBase spectrumOfAlgHom cellMap)
open Specs.IntegralRelativeCell (cellDivision)
open private matchLinkedFamily from LinearAlgebraicGroups.Classification.IntegralLinkedRoots

set_option backward.isDefEq.respectTransparency false

private abbrev torusMap {R X Y : Type u} [CommRing R] [CommGroup X] [CommGroup Y] (h : Y →* X) :=
  (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R h)).hom.hom

private theorem torusMap_isIso {R X Y : Type u} [CommRing R] [CommGroup X] [CommGroup Y]
    (e : Y ≃* X) : IsIso (torusMap (R := R) e.toMonoidHom) := by
  let f := spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R e.toMonoidHom)
  let g := spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R e.symm.toMonoidHom)
  have h₁ : f ≫ g = 𝟙 _ := by
    rw [← spectrumOfHopfHom_comp, ← MonoidAlgebra.mapDomainBialgHom_comp,
      show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id X from
        MonoidHom.ext e.apply_symm_apply, MonoidAlgebra.mapDomainBialgHom_id]
    exact CategoryTheory.Functor.map_id (hopfSpec (CommRingCat.of R)) _
  have h₂ : g ≫ f = 𝟙 _ := by
    rw [← spectrumOfHopfHom_comp, ← MonoidAlgebra.mapDomainBialgHom_comp,
      show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Y from
        MonoidHom.ext e.symm_apply_apply, MonoidAlgebra.mapDomainBialgHom_id]
    exact CategoryTheory.Functor.map_id (hopfSpec (CommRingCat.of R)) _
  exact ⟨⟨g.hom.hom, congrArg (·.hom.hom) h₁, congrArg (·.hom.hom) h₂⟩⟩

private theorem integralCellMatch {R A B I J X Y : Type u} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B] [CommGroup X] [CommGroup Y]
    (t : A →ₐc[R] MonoidAlgebra R X) (s : B →ₐc[R] MonoidAlgebra R Y)
    (a : Y →* X) (e : I → J) (x : I → A →ₐ[R] Polynomial R) (y : J → B →ₐ[R] Polynomial R)
    (f : B →ₐc[R] A)
    (ht : t.comp f = (MonoidAlgebra.mapDomainBialgHom R a).comp s)
    (hr : ∀ i, (x i).comp f.toAlgHom = y (e i)) (l m : List I) :
    cellMap t x l m ≫ (spectrumOfHopfHom f).hom.hom =
      cellChange e (torusMap (R := R) a) l m ≫ cellMap s y (l.map e) (m.map e) := by
  let F := 𝟭 (OverBase R)
  let f' := spectrumOfHopfHom f
  let E := Functor.mapGrpIdIso (C := OverBase R)
  let g : F.mapGrp.obj (HopfSpectrum R A) ⟶ F.mapGrp.obj (HopfSpectrum R B) :=
    E.hom.app _ ≫ f' ≫ E.inv.app _
  have hg : g.hom.hom = f'.hom.hom := by
    change 𝟙 (HopfSpectrum R A).X ≫ f'.hom.hom ≫ 𝟙 (HopfSpectrum R B).X = _
    simp only [Category.id_comp, Category.comp_id]
  have hr' (i : I) : F.map (spectrumOfAlgHom (x i)) ≫ g.hom.hom =
      F.map (spectrumOfAlgHom (y (e i))) := by
    rw [hg]
    change spectrumOfAlgHom (x i) ≫ spectrumOfAlgHom f.toAlgHom = spectrumOfAlgHom (y (e i))
    rw [← spectrumOfAlgHom_comp, hr]
  have ht' : F.map (spectrumOfHopfHom t).hom.hom ≫ g.hom.hom =
      F.map (torusMap (R := R) a ≫ (spectrumOfHopfHom s).hom.hom) := by
    change (spectrumOfHopfHom t).hom.hom ≫ g.hom.hom = _
    rw [hg]
    exact congrArg (fun v : HopfSpectrum R (MonoidAlgebra R X) ⟶ HopfSpectrum R B => v.hom.hom)
      ((spectrumOfHopfHom_comp t f).symm.trans
        ((congrArg spectrumOfHopfHom ht).trans (spectrumOfHopfHom_comp _ _)))
  have hc := map_cell F g e x y t s (torusMap (R := R) a) hr' ht' l m
  change cellMap t x l m ≫ g.hom.hom = _ at hc
  rw [hg] at hc
  exact hc

private abbrev modelCell {D : BasedRootDatum.{u}} (P : Model D)
    (x : D.I → P.A →ₐ[IntegralRing.{u}] Polynomial IntegralRing.{u}) (l m : List D.I) :=
  cellMap P.torus x l m

private structure MatchedCells {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E)
    (h : LatticeMap D E) (f : Q.A →ₐc[IntegralRing.{u}] P.A) where
  source : D.I → P.A →ₐ[IntegralRing.{u}] Polynomial IntegralRing.{u}
  target : E.I → Q.A →ₐ[IntegralRing.{u}] Polynomial IntegralRing.{u}
  sourceLaws : Specs.IntegralLinkedRoots.RootCoordinates P.torus P.pin source
  negative : List D.I
  positive : List D.I
  sourceOpen : IsOpenImmersion (modelCell P source negative positive).left
  targetOpen : IsOpenImmersion (modelCell Q target (negative.map h.roots) (positive.map h.roots)).left
  sourceSmooth : Smooth
    (cellDivision (HopfSpectrum IntegralRing.{u} P.A) (modelCell P source negative positive)).left
  sourceSurjective : Surjective
    (cellDivision (HopfSpectrum IntegralRing.{u} P.A) (modelCell P source negative positive)).left
  targetSmooth : Smooth (cellDivision (HopfSpectrum IntegralRing.{u} Q.A)
    (modelCell Q target (negative.map h.roots) (positive.map h.roots))).left
  targetSurjective : Surjective (cellDivision (HopfSpectrum IntegralRing.{u} Q.A)
    (modelCell Q target (negative.map h.roots) (positive.map h.roots))).left
  comparison : modelCell P source negative positive ≫ (spectrumOfHopfHom f).hom.hom =
    cellChange h.roots (torusMap (R := IntegralRing.{u}) h.characters) negative positive ≫
      modelCell Q target (negative.map h.roots) (positive.map h.roots)

attribute [local instance 10000] Algebra.toModule

private theorem genericFieldFlat {K : Type u} [Field K] [CharZero K] [Algebra IntegralRing.{u} K] :
    Module.Flat IntegralRing.{u} K := by
  letI := integralRing_isDomain
  letI := integralRing_isPrincipalIdealRing
  letI : Module.IsTorsionFree IntegralRing.{u} K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (integralRing_algebraMap_injective K)
  infer_instance

set_option maxHeartbeats 2000000 in
private theorem liftMarkedMap {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E)
    (h : LatticeMap D E) :
    ∃ f : Q.A →ₐc[IntegralRing.{u}] P.A,
      LiftsMarking P Q h.characters h.roots (fun i hi => (h.simple_iff i).mpr hi) f ∧
      Nonempty (MatchedCells P Q h f) ∧
      ∀ g : Q.A →ₐc[IntegralRing.{u}] P.A,
        LiftsMarking P Q h.characters h.roots (fun i hi => (h.simple_iff i).mpr hi) g → g = f := by
  let R := IntegralRing.{u}
  letI : CharZero (ULift.{u} ℚ) := charZero_of_injective_ringHom
    (f := (ULift.ringEquiv (R := ℚ)).symm.toRingHom) (ULift.ringEquiv (R := ℚ)).symm.injective
  let K := AlgebraicClosure (ULift.{u} ℚ)
  letI : CharZero K := Algebra.charZero_of_charZero (ULift.{u} ℚ) K
  letI : Algebra R K := ((Int.castRingHom K).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  letI : Module.Flat R K := genericFieldFlat
  letI : Module.Flat R P.A := modelFlat P
  letI := D.finiteRoots
  obtain ⟨x, hx⟩ := modelRootCoordinates P
  obtain ⟨y, hy⟩ := modelRootCoordinates Q
  obtain ⟨x', y', w, hx', hy', hxl, hyl, hxu, hyu, _⟩ :=
    Classification.IntegralLinkedRoots.linkedCoordinates P.finitePresentation Q.finitePresentation
      P.smooth Q.smooth P.torus Q.torus P.torus_surjective Q.torus_surjective
      P.pin Q.pin P.pin_basis Q.pin_basis (linkedLatticeMap h) x y hx hy
  obtain ⟨l, hl⟩ := enumerated_roots {i : D.I | ¬ D.base.IsPos i}
  obtain ⟨m, hm⟩ := enumerated_roots {i : D.I | D.base.IsPos i}
  have hl' : Specs.OrderedRootProducts.Enumerates (l.map h.roots) {j : E.I | ¬ E.base.IsPos j} :=
    enumerates_map h.roots hl (fun i => not_congr (preserves_positive h i))
  have hm' : Specs.OrderedRootProducts.Enumerates (m.map h.roots) {j : E.I | E.base.IsPos j} :=
    enumerates_map h.roots hm (preserves_positive h)
  obtain ⟨_, hPo, hPs, hPu, hcover⟩ := Classification.IntegralRelativeCell.integralRelativeCell D P.torus x'
    P.finitePresentation P.smooth P.torus_surjective (fun i => ⟨(hx'.1 i).1, fun S => (hx'.1 i).2.1 S |>.2⟩)
    (modelFibreCoordinates P hx') l m hl hm
  obtain ⟨_, hQo, hQs, hQu, _⟩ := Classification.IntegralRelativeCell.integralRelativeCell E Q.torus y'
    Q.finitePresentation Q.smooth Q.torus_surjective (fun i => ⟨(hy'.1 i).1, fun S => (hy'.1 i).2.1 S |>.2⟩)
    (modelFibreCoordinates Q hy') (l.map h.roots) (m.map h.roots) hl' hm'
  have matchRoots (g : K ⊗[R] Q.A →ₐc[K] K ⊗[R] P.A) (hg : GenericLiftsMarking P Q h g) (i : D.I) :
      (Specs.IntegralLinkedRoots.extendRoot (K := K) (x' i)).comp g.toAlgHom =
        Specs.IntegralLinkedRoots.extendRoot (K := K) (y' (h.roots i)) :=
    matchLinkedFamily (linkedLatticeMap h) hx' hy' (fun j => (hxl j).2) (fun j => (hyl j).2)
      w hxu hyu g (linkedMarking_of_generic P Q h g hg) i
  obtain ⟨g, hg⟩ := genericLiftOnAlgebras (K := K) P Q h
  have hK := integralRing_algebraMap_injective K
  let v := cellChange h.roots (torusMap (R := R) h.characters) l m
  have hgm := genericCellMatch P.torus Q.torus h.characters h.roots x' y' g hg.1 (matchRoots g hg) l m
  obtain ⟨f, hf⟩ := faithfulFlatCover_descends hK (modelCell P x' l m)
    (modelCell Q y' (l.map h.roots) (m.map h.roots)) v hcover g hgm
  have hmark := marking_of_genericAgreement P Q h f g hg hf
  have hcompare (f' : Q.A →ₐc[R] P.A)
      (hf' : LiftsMarking P Q h.characters h.roots (fun i hi => (h.simple_iff i).mpr hi) f') :
      modelCell P x' l m ≫ (spectrumOfHopfHom f').hom.hom =
        v ≫ modelCell Q y' (l.map h.roots) (m.map h.roots) := by
    let g' := extendBialg (K := K) f'
    have h' := genericMarking_of_integral (K := K) P Q h f' hf'
    exact integralCellMatch P.torus Q.torus h.characters h.roots x' y' f' hf'.1
      (fun i => integralRootMatch hK f' g' (extendBialg_one_tmul f') (x' i) (y' (h.roots i))
        (matchRoots g' h' i)) l m
  refine ⟨f, hmark, ⟨⟨x', y', hx', l, m, hPo, hQo, hPs, hPu, hQs, hQu, hcompare f hmark⟩⟩, ?_⟩
  intro f' hf'
  letI := hPs
  letI := hPu
  have eq := groupMaps_eq_of_cell (modelCell P x' l m) ((hcompare f' hf').trans (hcompare f hmark).symm)
  exact spectrumOfHopfHom_left_injective (congrArg (·.hom.hom) eq)

private theorem bialgEquiv_of_isIso {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B] (f : B →ₐc[R] A) [IsIso (spectrumOfHopfHom f)] :
    ∃ e : B ≃ₐc[R] A, e.toBialgHom = f := by
  let i := (hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimageIso (asIso (spectrumOfHopfHom f))
  exact ⟨CommHopfAlgCat.ofIso i.unop, by
    apply spectrumOfHopfHom_left_injective
    exact congrArg (·.hom.hom) ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage _)⟩

/-- A specified isomorphism of based root data lifts uniquely to the integral pinned models. -/
theorem pinnedIsomorphisms : PinnedIsomorphisms.{u} := by
  intro D E P Q e
  let R := IntegralRing.{u}
  let h := latticeMapOfIso e
  obtain ⟨f, hf, ⟨C⟩, hu⟩ := liftMarkedMap P Q h
  let i := modelCell P C.source C.negative C.positive
  let j := modelCell Q C.target (C.negative.map h.roots) (C.positive.map h.roots)
  let v := cellChange h.roots (torusMap (R := R) h.characters) C.negative C.positive
  letI : IsIso (torusMap (R := R) h.characters) := torusMap_isIso (characterEquiv e).symm
  letI : IsIso v := cellChange_isIso _ _ _ _
  letI : IsOpenImmersion j.left := C.targetOpen
  letI : Mono j := Over.mono_of_mono_left _
  letI : Smooth (cellDivision (HopfSpectrum R Q.A) j).left := C.targetSmooth
  letI : Surjective (cellDivision (HopfSpectrum R Q.A) j).left := C.targetSurjective
  letI : Flat (cellDivision (HopfSpectrum R P.A) i).left :=
    @AlgebraicGeometry.instFlatOfSmooth _ _ _ C.sourceSmooth
  letI : Surjective (cellDivision (HopfSpectrum R P.A) i).left := C.sourceSurjective
  letI : IsIso (spectrumOfHopfHom f) := groupIso_of_matching_cells _ i j (asIso v) C.comparison
    (cellDivision (HopfSpectrum R P.A) i) (𝟙 _) (Category.id_comp _).symm
  obtain ⟨b, hb⟩ := bialgEquiv_of_isIso f
  refine ⟨b, ?_, fun c hc => ?_⟩
  · change LiftsMarking P Q h.characters h.roots _ b.toBialgHom
    rw [hb]
    exact hf
  · have hcf := hu c.toBialgHom hc
    exact BialgEquiv.ext fun a => DFunLike.congr_fun (hcf.trans hb.symm) a

end IntegralLift

section KernelCentrality

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open Specs.IntegralCentralQuotient (OverBase spectrumOfAlgHom cellMap rootProduct lineProduct RootScalarAction)
open Specs.IntegralRelativeCell (cellDivision)
open private specProductIso specProductIso_fst specProductIso_snd
  from LinearAlgebraicGroups.Classification.IntegralCentralQuotient

set_option backward.isDefEq.respectTransparency false

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]

private theorem commute_of_universal_points {B C : Type u}
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : A →ₐ[R] C)
    (h : Commute (toConv (Algebra.TensorProduct.includeLeft.comp f))
      (toConv (Algebra.TensorProduct.includeRight.comp g)))
    {Y : OverBase R}
    (a : Y ⟶ (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R B)))
    (b : Y ⟶ (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R C))) :
    Commute (a ≫ spectrumOfAlgHom f : Y ⟶ (HopfSpectrum R A).X) (b ≫ spectrumOfAlgHom g) := by
  let e := specProductIso R B C
  let p := CartesianMonoidalCategory.lift a b ≫ e.hom
  have ha : p ≫ spectrumOfAlgHom (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C) = a := by
    simp only [p, e, Category.assoc, specProductIso_fst, lift_fst]
  have hb : p ≫ spectrumOfAlgHom (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C) = b := by
    simp only [p, e, Category.assoc, specProductIso_snd, lift_snd]
  let W := (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (B ⊗[R] C)))
  let l : B →ₐ[R] B ⊗[R] C := Algebra.TensorProduct.includeLeft
  let r : C →ₐ[R] B ⊗[R] C := Algebra.TensorProduct.includeRight
  let f₁ : W ⟶ (HopfSpectrum R A).X := spectrumOfAlgHom (l.comp f)
  let g₁ : W ⟶ (HopfSpectrum R A).X := spectrumOfAlgHom (r.comp g)
  have hl : p ≫ f₁ = a ≫ spectrumOfAlgHom f := by
    dsimp only [f₁, l]
    rw [spectrumOfAlgHom_comp, ← Category.assoc, ha]
  have hr : p ≫ g₁ = b ≫ spectrumOfAlgHom g := by
    dsimp only [g₁, r]
    rw [spectrumOfAlgHom_comp, ← Category.assoc, hb]
  have hc : Commute f₁ g₁ := h.map (Spec.mapMulEquiv (R := R) (S := A) (T := B ⊗[R] C))
  have he := congrArg (fun w : W ⟶ (HopfSpectrum R A).X => p ≫ w) hc.eq
  let a₁ : Y ⟶ (HopfSpectrum R A).X := a ≫ spectrumOfAlgHom f
  let b₁ : Y ⟶ (HopfSpectrum R A).X := b ≫ spectrumOfAlgHom g
  change a₁ * b₁ = b₁ * a₁
  simpa only [MonObj.comp_mul, show p ≫ f₁ = a₁ from hl, show p ≫ g₁ = b₁ from hr] using he

set_option maxHeartbeats 1000000 in
private theorem centrality_on_cell {X M I : Type u} [CommGroup X] [CommGroup M]
    (t : A →ₐc[R] MonoidAlgebra R X) (z : X →* M)
    (α : I → X) (hz : ∀ i, z (α i) = 1) (x : I → A →ₐ[R] Polynomial R)
    (hx : ∀ i, RootScalarAction t (x i) (α i)) (l m : List I)
    [Smooth (cellDivision (HopfSpectrum R A) (cellMap t x l m)).left]
    [Surjective (cellDivision (HopfSpectrum R A) (cellMap t x l m)).left] :
    IsCentral ((MonoidAlgebra.mapDomainBialgHom R z).comp t) := by
  let Z := MonoidAlgebra R M
  let T := MonoidAlgebra R X
  let π := (MonoidAlgebra.mapDomainBialgHom R z).comp t
  let G := HopfSpectrum R A
  let i := cellMap t x l m
  let d := cellDivision G i
  let k := (spectrumOfHopfHom π).hom.hom
  have hroot {Y : OverBase R} (j : I)
      (a : Y ⟶ (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (Polynomial R))))
      (b : Y ⟶ (HopfSpectrum R Z).X) : Commute (a ≫ spectrumOfAlgHom (x j) : Y ⟶ G.X) (b ≫ k) := by
    apply commute_of_universal_points (x j) π.toAlgHom _ a b
    let S := CommAlgCat.of R (Polynomial R ⊗[R] Z)
    let f : Polynomial R →ₐ[R] S := Algebra.TensorProduct.includeLeft
    let g : Z →ₐ[R] S := Algebra.TensorProduct.includeRight
    have hf : Polynomial.aeval (f Polynomial.X) = f :=
      Polynomial.algHom_ext (Polynomial.aeval_X _)
    simpa only [hf] using rootCommutesWithKernel t z (α j) (hz j) (x j) (hx j) S g (f Polynomial.X)
  have htorus {Y : OverBase R} (a : Y ⟶ (HopfSpectrum R T).X)
      (b : Y ⟶ (HopfSpectrum R Z).X) :
      Commute (a ≫ (spectrumOfHopfHom t).hom.hom) (b ≫ k) := by
    apply commute_of_universal_points t.toAlgHom π.toAlgHom _ a b
    let S := CommAlgCat.of R (T ⊗[R] Z)
    let f : T →ₐ[R] S := Algebra.TensorProduct.includeLeft
    let g : Z →ₐ[R] S := Algebra.TensorProduct.includeRight
    exact torusPoints_commute t S f (g.comp (MonoidAlgebra.mapDomainBialgHom R z).toAlgHom)
  have hprod {Y : OverBase R} (b : Y ⟶ (HopfSpectrum R Z).X)
      (n : List I) (a : Y ⟶ lineProduct R n) : Commute (a ≫ rootProduct x n) (b ≫ k) := by
    induction n with
    | nil => simpa only [rootProduct, MonObj.comp_one] using Commute.one_left (b ≫ k)
    | cons j n ih =>
      simp only [rootProduct, MonObj.comp_mul]
      exact (hroot j (a ≫ fst _ _) b).mul_left (ih (a ≫ snd _ _))
  have hcell {Y : OverBase R} (a : Y ⟶ _) (b : Y ⟶ (HopfSpectrum R Z).X) :
      Commute (a ≫ i) (b ≫ k) := by
    simp only [i, cellMap, MonObj.comp_mul]
    exact (hprod b l (a ≫ fst _ _)).mul_left
      ((htorus (a ≫ snd _ _ ≫ fst _ _) b).mul_left (hprod b m (a ≫ snd _ _ ≫ snd _ _)))
  have hall {Y : OverBase R} (a : Y ⟶ G.X) (b : Y ⟶ (HopfSpectrum R Z).X) : Commute a (b ≫ k) := by
    let p := pullback.snd d a
    let w := pullback.fst d a
    letI : Epi p := pullback_of_cover_epi d a
    change a * (b ≫ k) = (b ≫ k) * a
    apply (cancel_epi p).mp
    have hpa : p ≫ a = (w ≫ fst _ _ ≫ i) * (w ≫ snd _ _ ≫ i)⁻¹ := by
      rw [← pullback.condition]
      simp [d, w, cellDivision, MonObj.comp_mul, GrpObj.comp_inv]
    simp only [MonObj.comp_mul, hpa]
    exact ((hcell (w ≫ fst _ _) (p ≫ b)).mul_left
      (Commute.inv_left_iff.mpr (hcell (w ≫ snd _ _) (p ≫ b)))).eq
  apply kernelCentral_of_pointwise π
  intro S a b
  let e := Spec.mapMulEquiv (R := R) (S := A) (T := S)
  apply e.injective
  simp only [map_mul]
  have hb : e (toConv (b.comp π.toAlgHom)) = spectrumOfAlgHom b ≫ k :=
    spectrumOfAlgHom_comp b π.toAlgHom
  rw [hb]
  exact (hall (spectrumOfAlgHom a) (spectrumOfAlgHom b)).eq

end KernelCentrality

section QuotientLift

attribute [local instance 10000] Algebra.toModule

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open Specs.IntegralCentralQuotient (OverBase spectrumOfAlgHom cellMap cellTorusQuotient
  lineProduct rightCoaction invariants)
open Specs.IntegralRelativeCell (cellDivision)
open private invariantHopfAlgebra quotientInclusion tensorInclusion_injective quotientCell
  torusProjection_torsor middleProjection_isPullback characterRestriction_surjective
  from LinearAlgebraicGroups.Classification.IntegralCentralQuotient

set_option backward.isDefEq.respectTransparency false

private theorem latticeRestriction_kills {D E : BasedRootDatum.{u}} (P : Model D) (Q : Model E)
    (h : LatticeMap D E) (f : Q.A →ₐc[IntegralRing.{u}] P.A)
    (hf : LiftsMarking P Q h.characters h.roots (fun i hi => (h.simple_iff i).mpr hi) f) :
    (kernelRestriction P h).toAlgHom.comp f.toAlgHom =
      (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom IntegralRing.{u} Q.A) := by
  let R := IntegralRing.{u}
  let z := QuotientGroup.mk' h.characters.range
  have ht (χ : Multiplicative E.X) : z (h.characters χ) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨χ, rfl⟩
  have htorus : (MonoidAlgebra.mapDomainBialgHom R (z.comp h.characters)).toAlgHom =
      (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R (MonoidAlgebra R (Multiplicative E.X))) := by
    apply MonoidAlgebra.algHom_ext
    · intro χ
      rw [AlgHom.comp_apply]
      change MonoidAlgebra.mapDomainBialgHom R (z.comp h.characters) (MonoidAlgebra.single χ 1) = _
      simp [MonoidAlgebra.mapDomainBialgHom_single, ht]
    · exact Subsingleton.elim _ _
  change (((MonoidAlgebra.mapDomainBialgHom R z).comp P.torus).comp f).toAlgHom = _
  rw [BialgHom.comp_assoc, hf.1, ← BialgHom.comp_assoc, ← MonoidAlgebra.mapDomainBialgHom_comp,
    BialgHom.comp_toAlgHom, htorus, AlgHom.comp_assoc, Q.torus.counitAlgHom_comp]

variable {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A]
  [HopfAlgebra R B] [CommGroup M] [Fintype M]

private theorem factorsThroughInvariants (π : A →ₐc[R] MonoidAlgebra R M) (hπ : IsCentral π)
    (f : B →ₐc[R] A)
    (hf : π.toAlgHom.comp f.toAlgHom = (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R B)) :
    letI : HopfAlgebra R ↥(invariants π) := invariantHopfAlgebra π hπ
    ∃ f₀ : B →ₐc[R] ↥(invariants π), (quotientInclusion π hπ).comp f₀ = f := by
  let H := MonoidAlgebra R M
  letI : HopfAlgebra R ↥(invariants π) := invariantHopfAlgebra π hπ
  let j := quotientInclusion π hπ
  have hright : (rightCoaction π).comp f.toAlgHom =
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] H).comp f.toAlgHom := by
    have hcomp :
        (Algebra.TensorProduct.map f.toAlgHom (Algebra.ofId R H)).comp
          (Algebra.TensorProduct.rid R R B).symm.toAlgHom =
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] H).comp f.toAlgHom := by
      ext b
      change f b ⊗ₜ[R] (1 : H) = _
      rfl
    unfold rightCoaction
    rw [AlgHom.comp_assoc, ← f.map_comp_comulAlgHom, ← AlgHom.comp_assoc,
      ← Algebra.TensorProduct.map_comp, AlgHom.id_comp, hf,
      ← show f.toAlgHom.comp (AlgHom.id R B) = f.toAlgHom from AlgHom.comp_id _,
      Algebra.TensorProduct.map_comp, AlgHom.comp_assoc]
    have hr :
        (Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.counitAlgHom R B)).comp
          (Bialgebra.comulAlgHom R B) = (Algebra.TensorProduct.rid R R B).symm.toAlgHom :=
      AlgHom.toLinearMap_injective (Coalgebra.lTensor_counit_comp_comul (R := R) (A := B))
    rw [hr, hcomp, AlgHom.comp_id]
  let p : B →ₐ[R] invariants π :=
    f.toAlgHom.codRestrict (invariants π) fun b => DFunLike.congr_fun hright b
  have hj : j.toAlgHom.comp p = f.toAlgHom := rfl
  have he : (Bialgebra.counitAlgHom R ↥(invariants π)).comp p = Bialgebra.counitAlgHom R B := by
    rw [← j.counitAlgHom_comp, AlgHom.comp_assoc, hj, f.counitAlgHom_comp]
  have hd : (Algebra.TensorProduct.map p p).comp (Bialgebra.comulAlgHom R B) =
      (Bialgebra.comulAlgHom R ↥(invariants π)).comp p := by
    suffices (Algebra.TensorProduct.map j.toAlgHom j.toAlgHom).comp
        ((Algebra.TensorProduct.map p p).comp (Bialgebra.comulAlgHom R B)) =
        (Algebra.TensorProduct.map j.toAlgHom j.toAlgHom).comp
          ((Bialgebra.comulAlgHom R ↥(invariants π)).comp p) by
      exact AlgHom.ext fun x => tensorInclusion_injective π (DFunLike.congr_fun this x)
    rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, hj, f.map_comp_comulAlgHom,
      ← AlgHom.comp_assoc, j.map_comp_comulAlgHom, AlgHom.comp_assoc, hj]
  exact ⟨BialgHom.ofAlgHom p he hd, BialgHom.ext fun _ => rfl⟩

private theorem cellTorusQuotient_epi {X I : Type u} [CommGroup X] [Module.Finite ℤ (Additive X)]
    [IsNoetherianRing R] (z : X →* M) (hz : Function.Surjective z) (l m : List I) :
    Epi (cellTorusQuotient (R := R) z l m) := by
  let T := (HopfSpectrum R (MonoidAlgebra R X)).X
  let T₀ := (HopfSpectrum R (MonoidAlgebra R ↥z.ker)).X
  let q : T ⟶ T₀ := torusMap (R := R) z.ker.subtype
  have ht := torusProjection_torsor (R := R) z hz
  have hp := (middleProjection_isPullback (lineProduct R l) (lineProduct R m) q).map (Over.forget _)
  letI : Flat (cellTorusQuotient (R := R) z l m).left := MorphismProperty.of_isPullback hp ht.2.1
  letI : Surjective (cellTorusQuotient (R := R) z l m).left :=
    MorphismProperty.of_isPullback hp ht.2.2.1
  letI := Flat.epi_of_flat_of_surjective (cellTorusQuotient (R := R) z l m).left
  exact Over.epi_of_epi_left _

set_option maxHeartbeats 2400000 in
/-- An ordinary based isogeny lifts to the finite diagonalizable quotient of the source,
with the target identified by the comparison of the two marked cells. -/
theorem centralIsogenies : CentralIsogenies.{u} := by
  intro D E P Q h
  let R := IntegralRing.{u}
  letI : IsNoetherianRing R := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  letI : Module.Finite ℤ (Additive (Multiplicative D.X)) := D.finiteX
  letI : Module.Flat R P.A := modelFlat P
  letI : Algebra.FinitePresentation R P.A := P.finitePresentation
  letI := h.finiteIndex
  letI := Fintype.ofFinite (Multiplicative D.X ⧸ h.characters.range)
  obtain ⟨f, hf, ⟨C⟩, _⟩ := liftMarkedMap P Q h
  let z := QuotientGroup.mk' h.characters.range
  have hz : Function.Surjective z := QuotientGroup.mk_surjective
  let π := kernelRestriction P h
  let i := modelCell P C.source C.negative C.positive
  let j := modelCell Q C.target (C.negative.map h.roots) (C.positive.map h.roots)
  let G := HopfSpectrum R P.A
  let H := HopfSpectrum R Q.A
  letI : Smooth (cellDivision G i).left := C.sourceSmooth
  letI : Surjective (cellDivision G i).left := C.sourceSurjective
  letI : Smooth (cellDivision H j).left := C.targetSmooth
  letI : Surjective (cellDivision H j).left := C.targetSurjective
  letI : IsOpenImmersion j.left := C.targetOpen
  letI : Mono j := Over.mono_of_mono_left _
  have hc : IsCentral π :=
    centrality_on_cell P.torus z (fun r => Multiplicative.ofAdd (D.datum.root r))
      (kernelCharacter_root h) C.source (fun r => (C.sourceLaws.1 r).2.2) C.negative C.positive
  have hπ : Function.Surjective π := (characterRestriction_surjective (R := R) z hz).comp P.torus_surjective
  letI : HopfAlgebra R ↥(invariants π) := invariantHopfAlgebra π hc
  let p : ↥(invariants π) →ₐc[R] P.A := quotientInclusion π hc
  let q := (spectrumOfHopfHom p).hom.hom
  have ht := Classification.IntegralCentralQuotient.spectrumTorsor π hc hπ
  have ht' : IsRightTorsor p π := ht
  letI : Flat q.left := ht'.2.1
  letI : Surjective q.left := ht'.2.2.1
  obtain ⟨t₀, ht₀, _⟩ := Classification.IntegralCentralQuotient.quotientTorus z P.torus P.torus_surjective hc
  let i₀ := cellMap t₀ (fun r => (C.source r).comp p.toAlgHom) C.negative C.positive
  let v₀ := cellTorusQuotient (R := R) z C.negative C.positive
  obtain ⟨_, hpb⟩ := quotientCell z hz P.torus p t₀ ht₀ C.source C.negative C.positive C.sourceOpen hc ht'
  have hcell : i ≫ q = v₀ ≫ i₀ := hpb.w.symm
  letI : Epi v₀ := cellTorusQuotient_epi z hz C.negative C.positive
  obtain ⟨f₀, hf₀⟩ := factorsThroughInvariants π hc f (latticeRestriction_kills P Q h f hf)
  let g := spectrumOfHopfHom f₀
  have hfac : q ≫ g.hom.hom = (spectrumOfHopfHom f).hom.hom := by
    exact congrArg (·.hom.hom) ((spectrumOfHopfHom_comp p f₀).symm.trans (congrArg spectrumOfHopfHom hf₀))
  let e := quotientCharacterEquiv h
  let u := cellChange h.roots (torusMap (R := R) e.toMonoidHom) C.negative C.positive
  letI : IsIso (torusMap (R := R) e.toMonoidHom) := torusMap_isIso e
  letI : IsIso u := cellChange_isIso _ _ _ _
  have htorus : torusMap (R := R) z.ker.subtype ≫ torusMap (R := R) e.toMonoidHom =
      torusMap (R := R) h.characters := by
    exact congrArg (·.hom.hom) ((spectrumOfHopfHom_comp _ _).symm.trans
      (congrArg spectrumOfHopfHom ((MonoidAlgebra.mapDomainBialgHom_comp (R := R) _ _).symm.trans
        (congrArg (MonoidAlgebra.mapDomainBialgHom R) (quotientCharacterEquiv_subtype h)))))
  have hu : v₀ ≫ u = cellChange h.roots (torusMap (R := R) h.characters) C.negative C.positive := by
    simp only [v₀, u, cellTorusQuotient, cellChange, tensorHom_comp_tensorHom, Category.id_comp]
    change _ ⊗ₘ ((torusMap (R := R) z.ker.subtype ≫ torusMap (R := R) e.toMonoidHom) ⊗ₘ _) = _
    rw [htorus]
  have hcompare : i₀ ≫ g.hom.hom = u ≫ j := by
    apply (cancel_epi v₀).mp
    calc
      v₀ ≫ i₀ ≫ g.hom.hom = i ≫ q ≫ g.hom.hom := by rw [← Category.assoc, ← hcell, Category.assoc]
      _ = i ≫ (spectrumOfHopfHom f).hom.hom := by rw [hfac]
      _ = v₀ ≫ u ≫ j := by rw [← Category.assoc, hu]; exact C.comparison
  let d := cellDivision G i ≫ q
  letI : Flat d.left := by change Flat ((cellDivision G i).left ≫ q.left); infer_instance
  letI : Surjective d.left := by change Surjective ((cellDivision G i).left ≫ q.left); infer_instance
  letI : IsIso (spectrumOfHopfHom f₀) :=
    groupIso_of_matching_cells g i₀ j (asIso u) hcompare d (v₀ ⊗ₘ v₀)
      (cellDivision_comm (spectrumOfHopfHom p) v₀ hcell)
  obtain ⟨b, hb⟩ := bialgEquiv_of_isIso f₀
  have hpb' := rightTorsor_comp_equiv p π b ht'
  rw [hb, hf₀] at hpb'
  exact ⟨f, hf, hc, hpb'⟩

end QuotientLift

end

end LinearAlgebraicGroups.Classification.IntegralRecognition
