import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.FiniteWordClosure
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.FiniteWordClosure

noncomputable section

open Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup IsNormalSubgroup subgroupConjugation)
open Specs.FiniteWordClosure (power wordDomain evaluate ConjugationStable)

variable {k : Type u} [Field k]
variable {G : GroupScheme k} {X T S : SchemeOver k} (f : X ⟶ G.X)

private theorem evaluate_precomp (q : S ⟶ T) (n : ℕ) (p : T ⟶ wordDomain X n) :
    evaluate f n (q ≫ p) = q ≫ evaluate f n p := by
  induction n with
  | zero => simp [evaluate, MonObj.comp_one]
  | succ n ih => simp only [evaluate, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, ih]

private def wordMap (n : ℕ) : wordDomain X n ⟶ G.X :=
  evaluate f n (𝟙 _)

private theorem comp_wordMap (n : ℕ) (p : T ⟶ wordDomain X n) :
    p ≫ wordMap f n = evaluate f n p := by
  rw [wordMap, ← evaluate_precomp, Category.comp_id]

private def IsWord (n : ℕ) (z : T ⟶ G.X) : Prop :=
  ∃ p : T ⟶ wordDomain X n, p ≫ wordMap f n = z

private theorem isWord_zero (z : T ⟶ G.X) : IsWord f 0 z ↔ z = 1 := by
  constructor
  · rintro ⟨p, hp⟩
    rw [comp_wordMap, evaluate] at hp
    exact hp.symm
  · rintro rfl
    exact ⟨toUnit T, comp_wordMap f 0 (toUnit T)⟩

private theorem isWord_succ (n : ℕ) (z : T ⟶ G.X) :
    IsWord f (n + 1) z ↔
      ∃ (a b : T ⟶ X) (v : T ⟶ G.X),
        IsWord f n v ∧ (a ≫ f) * (b ≫ f)⁻¹ * v = z := by
  constructor
  · rintro ⟨p, hp⟩
    rw [comp_wordMap] at hp
    let a := p ≫ fst X (X ⊗ wordDomain X n)
    let q := p ≫ snd X (X ⊗ wordDomain X n)
    let b := q ≫ fst X (wordDomain X n)
    let r := q ≫ snd X (wordDomain X n)
    exact ⟨a, b, evaluate f n r, ⟨r, comp_wordMap f n r⟩, hp⟩
  · rintro ⟨a, b, v, ⟨r, hr⟩, rfl⟩
    let p : T ⟶ wordDomain X (n + 1) := lift a (lift b r)
    refine ⟨p, (comp_wordMap f (n + 1) p).trans ?_⟩
    have ha : p ≫ fst X (X ⊗ wordDomain X n) = a := lift_fst a (lift b r)
    have hb : p ≫ snd X (X ⊗ wordDomain X n) = lift b r := lift_snd a (lift b r)
    rw [evaluate, ha, hb, lift_fst, lift_snd, ← comp_wordMap f n r, hr]

private theorem one_isWord : IsWord f 0 (1 : T ⟶ G.X) :=
  (isWord_zero f _).mpr rfl

private theorem pair_isWord (a b : T ⟶ X) : IsWord f 1 ((a ≫ f) * (b ≫ f)⁻¹) :=
  (isWord_succ f 0 _).mpr ⟨a, b, 1, one_isWord f, mul_one _⟩

private theorem isWord_mul {m n : ℕ} {z z' : T ⟶ G.X}
    (hz : IsWord f m z) (hz' : IsWord f n z') : IsWord f (m + n) (z * z') := by
  induction m generalizing z with
  | zero =>
    rw [(isWord_zero f _).mp hz, one_mul, Nat.zero_add]
    exact hz'
  | succ m ih =>
    obtain ⟨a, b, v, hv, rfl⟩ := (isWord_succ f m z).mp hz
    rw [Nat.succ_add, mul_assoc]
    exact (isWord_succ f _ _).mpr ⟨a, b, _, ih hv, rfl⟩

private theorem isWord_inv {n : ℕ} {z : T ⟶ G.X} (hz : IsWord f n z) :
    IsWord f n z⁻¹ := by
  induction n generalizing z with
  | zero => simpa [(isWord_zero f _).mp hz] using (one_isWord f (T := T))
  | succ n ih =>
    obtain ⟨a, b, v, hv, rfl⟩ := (isWord_succ f n z).mp hz
    simpa only [mul_inv_rev, inv_inv] using isWord_mul f (ih hv) (pair_isWord f b a)

private theorem isWord_conj (hf : ConjugationStable f) (g : T ⟶ G.X)
    {n : ℕ} {z : T ⟶ G.X} (hz : IsWord f n z) : IsWord f n (g * z * g⁻¹) := by
  change IsWord f n (MulAut.conj g z)
  induction n generalizing z with
  | zero => simpa [(isWord_zero f _).mp hz] using (one_isWord f (T := T))
  | succ n ih =>
    obtain ⟨a, b, v, hv, rfl⟩ := (isWord_succ f n z).mp hz
    obtain ⟨a', ha⟩ := hf T g a
    obtain ⟨b', hb⟩ := hf T g b
    rw [map_mul, map_mul, map_inv]
    exact (isWord_succ f _ _).mpr ⟨a', b', _, ih hv, by rw [ha, hb]; rfl⟩

private theorem isWord_wordMap (n : ℕ) : IsWord f n (wordMap f n) :=
  ⟨𝟙 _, Category.id_comp _⟩

private theorem isWord_advance (x₀ : 𝟙_ (SchemeOver k) ⟶ X) {n : ℕ} {z : T ⟶ G.X}
    (hz : IsWord f n z) : IsWord f (n + 1) z := by
  let a := toUnit T ≫ x₀
  exact (isWord_succ f _ _).mpr ⟨a, a, z, hz, by simp⟩

private theorem word_kernel_le {n : ℕ} {z : T ⟶ G.X} (hz : IsWord f n z) :
    (wordMap f n).left.ker ≤ z.left.ker := by
  obtain ⟨q, rfl⟩ := hz
  exact q.left.le_ker_comp (wordMap f n).left

private theorem affine_tensor {A B : SchemeOver k} [IsAffine A.left] [IsAffine B.left] :
    IsAffine (A ⊗ B).left := by
  rw [Over.tensorObj_left]
  infer_instance

private theorem affine_power [IsAffine X.left] (m : ℕ) : IsAffine (power X m).left := by
  induction m with
  | zero => change IsAffine (Spec (CommRingCat.of k)); infer_instance
  | succ m ih => exact affine_tensor (A := X) (B := power X m)

-- Padding makes the kernels decrease. The height bound on primes gives a
-- minimal member, which is contained in every kernel of the family.
private theorem kernel_stabilizes [IsAffine X.left] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (x₀ : 𝟙_ (SchemeOver k) ⟶ X)
    (hX : ∀ m, IsIntegral (power X m).left) :
    ∃ n : ℕ, 0 < n ∧ ∀ m, (wordMap f n).left.ker ≤ (wordMap f m).left.ker := by
  classical
  let J (m : ℕ) : Ideal Γ(G.X.left, ⊤) := RingHom.ker (wordMap f m).left.appTop.hom
  let e := Scheme.IdealSheafData.equivOfIsAffine (X := G.X.left)
  have ele {I K : G.X.left.IdealSheafData} : e I ≤ e K ↔ I ≤ K := e.map_le_map_iff'
  have hJ (m : ℕ) : e ((wordMap f m).left.ker) = J m := by
    have : IsAffine (wordDomain X m).left := affine_power (2 * m)
    change ((wordMap f m).left.ker).ideal ⟨⊤, isAffineOpen_top _⟩ = _
    exact (wordMap f m).left.ker_apply _
  have hanti : Antitone J := antitone_nat_of_succ_le fun m ↦ by
    rw [← hJ, ← hJ]
    exact ele.mpr (word_kernel_le f (isWord_advance f x₀ (isWord_wordMap f m)))
  have hprime (m : ℕ) : (J m).IsPrime := by
    have : IsIntegral (wordDomain X m).left := hX (2 * m)
    exact RingHom.ker_isPrime _
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsNoetherianRing Γ(G.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let height (n : ℕ) := (J (n + 1)).height.toNat
  obtain ⟨n, hn⟩ : ∃ n, ∀ m, height n ≤ height m := by
    have hex : ∃ a, ∃ m, height m = a := ⟨_, 0, rfl⟩
    obtain ⟨n, hn⟩ := Nat.find_spec hex
    exact ⟨n, fun m ↦ hn.symm ▸ Nat.find_min' hex ⟨m, rfl⟩⟩
  refine ⟨n + 1, Nat.succ_pos _, fun m ↦ ele.mp ?_⟩
  rw [hJ, hJ]
  by_cases hm : m ≤ n + 1
  · exact hanti hm
  · have hm' : n + 1 ≤ m := by omega
    cases m with
    | zero => omega
    | succ m =>
      have := hprime (m + 1)
      have := hprime (n + 1)
      have h₁ := (J (n + 1)).height_lt_top Ideal.IsPrime.ne_top'
      have h₂ := (J (m + 1)).height_lt_top Ideal.IsPrime.ne_top'
      exact ((J (m + 1)).eq_of_le_of_height_le (hanti hm') (by
        rw [← ENat.natCast_toNat h₁.ne, ← ENat.natCast_toNat h₂.ne]
        exact_mod_cast hn m)).ge


private theorem ker_comp_eq {A B C : SchemeOver k} (p : A ⟶ B) (z : B ⟶ C)
    [IsSchemeTheoreticallyDominant p.left] : (p ≫ z).left.ker = z.left.ker := by
  rw [Over.comp_left, Scheme.Hom.ker_comp, p.left.ker_eq_bot, Scheme.IdealSheafData.map_bot]

private def liftClosed {A B C : SchemeOver k} (i : B ⟶ C) (z : A ⟶ C)
    [IsClosedImmersion i.left] (h : i.left.ker ≤ z.left.ker) : A ⟶ B :=
  Over.homMk (IsClosedImmersion.lift i.left z.left h) <| by
    rw [← i.w, ← Category.assoc, IsClosedImmersion.lift_fac, z.w]

private theorem liftClosed_fac {A B C : SchemeOver k} (i : B ⟶ C) (z : A ⟶ C)
    [IsClosedImmersion i.left] (h : i.left.ker ≤ z.left.ker) : liftClosed i z h ≫ i = z :=
  Over.OverMorphism.ext (IsClosedImmersion.lift_fac i.left z.left h)

private theorem dominant_whiskerLeft {A B : SchemeOver k} (C : SchemeOver k)
    (p : A ⟶ B) [QuasiCompact p.left] [IsSchemeTheoreticallyDominant p.left] :
    IsSchemeTheoreticallyDominant (C ◁ p).left := by
  have hp : IsPullback (C ◁ p).left (snd C A).left (snd C B).left p.left := by
    refine IsPullback.of_right (h₁₂ := (fst C B).left) (h₂₂ := B.hom) (v₁₃ := C.hom) ?_ ?_ ?_
    · rw [← Over.comp_left, whiskerLeft_fst, Over.w]
      exact IsPullback.of_hasPullback _ _
    · rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
    · exact IsPullback.of_hasPullback _ _
  have : Flat (snd C B).left := by change Flat (pullback.snd C.hom B.hom); infer_instance
  exact IsSchemeTheoreticallyDominant.of_isPullback hp.flip

private theorem dominant_whiskerRight {A B : SchemeOver k} (C : SchemeOver k)
    (p : A ⟶ B) [QuasiCompact p.left] [IsSchemeTheoreticallyDominant p.left] :
    IsSchemeTheoreticallyDominant (p ▷ C).left := by
  have hp : IsPullback (p ▷ C).left (fst A C).left (fst B C).left p.left := by
    refine IsPullback.of_right (h₁₂ := (snd B C).left) (h₂₂ := B.hom) (v₁₃ := C.hom) ?_ ?_ ?_
    · rw [← Over.comp_left, whiskerRight_snd, Over.w]
      exact (IsPullback.of_hasPullback A.hom C.hom).flip
    · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    · exact (IsPullback.of_hasPullback B.hom C.hom).flip
  have : Flat (fst B C).left := by change Flat (pullback.fst B.hom C.hom); infer_instance
  exact IsSchemeTheoreticallyDominant.of_isPullback hp.flip

private theorem dominant_tensor {A B : SchemeOver k} (p : A ⟶ B)
    [QuasiCompact p.left] [IsSchemeTheoreticallyDominant p.left] :
    IsSchemeTheoreticallyDominant (p ⊗ₘ p).left := by
  rw [tensorHom_def, Over.comp_left]
  have := dominant_whiskerRight A p
  have := dominant_whiskerLeft B p
  infer_instance

private theorem dominant_toImage {A B : Scheme.{u}} (z : A ⟶ B) [IsAffine B]
    [QuasiCompact z] : IsSchemeTheoreticallyDominant z.toImage := by
  have : IsAffine z.image := isAffine_of_isAffineHom z.imageι
  have hinj : Function.Injective z.toImage.appTop :=
    z.toImage_app_injective ⟨⊤, isAffineOpen_top B⟩
  constructor
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [z.toImage.ker_apply ⟨⊤, isAffineOpen_top _⟩, Scheme.IdealSheafData.ideal_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp hinj

private theorem comp_lifted_mul {Y : SchemeOver k} (i : Y ⟶ G.X) (m : Y ⊗ Y ⟶ Y)
    (hm : m ≫ i = (fst Y Y ≫ i) * (snd Y Y ≫ i))
    (q : T ⟶ Y ⊗ Y) :
    q ≫ m ≫ i = (q ≫ fst Y Y ≫ i) * (q ≫ snd Y Y ≫ i) := by
  rw [hm, MonObj.comp_mul]

/-- A monomorphism carrying unit, multiplication and inversion induces a group structure. -/
@[instance_reducible] private def subgroupStructure {Y : SchemeOver k} (i : Y ⟶ G.X) [Mono i]
    (e : 𝟙_ (SchemeOver k) ⟶ Y) (m : Y ⊗ Y ⟶ Y) (v : Y ⟶ Y)
    (he : e ≫ i = 1) (hm : m ≫ i = (fst Y Y ≫ i) * (snd Y Y ≫ i))
    (hv : v ≫ i = i⁻¹) : GrpObj Y where
  one := e
  mul := m
  inv := v
  one_mul := by
    apply (cancel_mono i).mp
    rw [Category.assoc, comp_lifted_mul i m hm]
    simp [he, MonObj.comp_one, leftUnitor_hom]
  mul_one := by
    apply (cancel_mono i).mp
    rw [Category.assoc, comp_lifted_mul i m hm]
    simp [he, MonObj.comp_one, rightUnitor_hom]
  mul_assoc := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, comp_lifted_mul i m hm, whiskerRight_fst_assoc, whiskerRight_snd_assoc,
      whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, MonObj.comp_mul, associator_hom_fst_assoc,
      associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc, mul_assoc]
  left_inv := by
    apply (cancel_mono i).mp
    rw [Category.assoc, Category.assoc, comp_lifted_mul i m hm]
    simp [hv, he, MonObj.comp_one]
  right_inv := by
    apply (cancel_mono i).mp
    rw [Category.assoc, Category.assoc, comp_lifted_mul i m hm]
    simp [hv, he, MonObj.comp_one]

private theorem isMonHom_of_factor {A B : GroupScheme k} (i : A ⟶ G) (j : B ⟶ G)
    [Mono j.hom.hom] (q : A.X ⟶ B.X) (hq : q ≫ j.hom.hom = i.hom.hom) :
    IsMonHom q := by
  constructor
  · apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, hq, IsMonHom.one_hom, IsMonHom.one_hom]
  · apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, hq, IsMonHom.mul_hom (f := i.hom.hom), Category.assoc,
      IsMonHom.mul_hom (f := j.hom.hom), ← Category.assoc, tensorHom_comp_tensorHom, hq]

private theorem isWord_factors {H : GroupScheme k} (j : H ⟶ G)
    (fH : X ⟶ H.X) (hfH : fH ≫ j.hom.hom = f)
    {n : ℕ} {z : T ⟶ G.X} (hz : IsWord f n z) :
    ∃ zH : T ⟶ H.X, zH ≫ j.hom.hom = z := by
  induction n generalizing z with
  | zero =>
    exact ⟨1, (MonObj.one_comp _).trans ((isWord_zero f z).mp hz).symm⟩
  | succ n ih =>
    obtain ⟨a, b, v, hv, rfl⟩ := (isWord_succ f n z).mp hz
    obtain ⟨vH, hvH⟩ := ih hv
    refine ⟨(a ≫ fH) * (b ≫ fH)⁻¹ * vH, ?_⟩
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hfH, hvH]

theorem existsFiniteWordClosure : Specs.FiniteWordClosure.ExistsFiniteWordClosure.{u} := by
  intro k _ G X f x₀ hX _ _ hx₀ hintegral hconj
  have : IsAffine X.left := hX
  have : IsAffine G.val.X.left := G.property.1
  have : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  obtain ⟨n, hn, hstable⟩ := kernel_stabilizes f x₀ hintegral
  let F := wordMap f n
  have : IsAffine (wordDomain X n).left := affine_power (2 * n)
  let Y : SchemeOver k := Over.mk (F.left.imageι ≫ G.val.X.hom)
  let i : Y ⟶ G.val.X := Over.homMk F.left.imageι rfl
  let w : wordDomain X n ⟶ Y := Over.homMk F.left.toImage <| by
    change F.left.toImage ≫ F.left.imageι ≫ G.val.X.hom = _
    rw [← Category.assoc, F.left.toImage_imageι, F.w]
  have hw : w ≫ i = F := Over.OverMorphism.ext F.left.toImage_imageι
  have hi : i.left.ker = F.left.ker := F.left.ker.ker_subschemeι
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion F.left.imageι)
  have : Mono i := Over.mono_of_mono_left i
  have : QuasiCompact w.left := inferInstanceAs (QuasiCompact F.left.toImage)
  have hdom : IsSchemeTheoreticallyDominant w.left := dominant_toImage F.left
  have wordFactors {U : SchemeOver k} {m : ℕ} {z : U ⟶ G.val.X} (hz : IsWord f m z) :
      i.left.ker ≤ z.left.ker := hi.trans_le ((hstable m).trans (word_kernel_le f hz))
  have hfactors : i.left.ker ≤ f.left.ker := by
    let b := toUnit X ≫ x₀
    have hb : b ≫ f = 1 := by
      simp [b, hx₀, MonObj.comp_one]
    apply wordFactors
    simpa only [hb, inv_one, mul_one, Category.id_comp] using pair_isWord f (𝟙 X) b
  let e := liftClosed i (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) (wordFactors (one_isWord f))
  have he := liftClosed_fac i _ (wordFactors (one_isWord f (T := 𝟙_ (SchemeOver k))))
  -- Pull back multiplication along the dominant product of the word map.
  -- There it is a word of length n + n, so it factors through the stable image.
  let mulG := (fst Y Y ≫ i) * (snd Y Y ≫ i)
  have hmker : i.left.ker ≤ mulG.left.ker := by
    have : IsSchemeTheoreticallyDominant (w ⊗ₘ w).left := dominant_tensor w
    rw [← ker_comp_eq (w ⊗ₘ w) mulG]
    apply wordFactors
    have h₁ : IsWord f n (fst (wordDomain X n) (wordDomain X n) ≫ F) := ⟨_, rfl⟩
    have h₂ : IsWord f n (snd (wordDomain X n) (wordDomain X n) ≫ F) := ⟨_, rfl⟩
    simpa only [mulG, MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc, hw] using
      isWord_mul f h₁ h₂
  let m := liftClosed i mulG hmker
  have hm := liftClosed_fac i mulG hmker
  have hvker : i.left.ker ≤ (i⁻¹).left.ker := by
    rw [← ker_comp_eq w i⁻¹]
    apply wordFactors
    rw [GrpObj.comp_inv, hw]
    exact isWord_inv f (isWord_wordMap f n)
  let v := liftClosed i i⁻¹ hvker
  have hv := liftClosed_fac i i⁻¹ hvker
  let : GrpObj Y := subgroupStructure i e m v he hm hv
  have : IsMonHom i := by
    constructor
    · exact he.trans (MonObj.one_eq_one G.val.X).symm
    · change m ≫ i = (i ⊗ₘ i) ≫ μ[G.val.X]
      rw [hm, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
  let N : ClosedSubgroup G.val := ⟨Grp.mk Y, Grp.ofHom i, ‹IsClosedImmersion i.left›⟩
  refine ⟨N, n, w, hn, ?_, hdom, ⟨liftClosed i f hfactors, liftClosed_fac i f hfactors⟩, ?_, ?_⟩
  · let c := subgroupConjugation N.inclusion
    have hc : i.left.ker ≤ c.left.ker := by
      -- Work on the universal sections of the product with the word domain.
      let p := G.val.X ◁ w
      have : IsSchemeTheoreticallyDominant p.left := dominant_whiskerLeft G.val.X w
      rw [← ker_comp_eq p c]
      apply wordFactors
      change IsWord f _ (p ≫ ((fst G.val.X Y * (snd G.val.X Y ≫ i)) * (fst G.val.X Y)⁻¹))
      simp only [p, MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_fst, whiskerLeft_snd_assoc, hw]
      exact isWord_conj f hconj _ (⟨snd _ _, rfl⟩ : IsWord f n (snd _ _ ≫ F))
    exact ⟨liftClosed i c hc, liftClosed_fac i c hc⟩
  · rintro H ⟨fH, hfH⟩
    let j := H.inclusion.hom.hom
    have : IsClosedImmersion j.left := H.isClosedImmersion
    have : Mono j := Over.mono_of_mono_left j
    obtain ⟨wH, hwH⟩ := isWord_factors f H.inclusion fH hfH (isWord_wordMap f n)
    have hji : j.left.ker ≤ i.left.ker := by
      rw [hi, ← show wH ≫ j = F from hwH]
      exact wH.left.le_ker_comp j.left
    let q := liftClosed j i hji
    have hq := liftClosed_fac j i hji
    have : IsMonHom q := isMonHom_of_factor N.inclusion H.inclusion q hq
    exact ⟨Grp.homMk q, Grp.hom_ext _ _ hq⟩
  · intro T p
    change p ≫ w ≫ i = _
    rw [hw, comp_wordMap]

end

end LinearAlgebraicGroups.FiniteWordClosure
