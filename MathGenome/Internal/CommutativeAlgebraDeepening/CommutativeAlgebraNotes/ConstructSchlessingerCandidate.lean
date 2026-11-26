import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ConstructSchlessingerCandidate
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LargestArtinLiftQuotient
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import Batteries.Tactic.OpenPrivate

universe u w

namespace CommutativeAlgebraNotes.SchlessingerCandidate

open CategoryTheory LocalArtinAlgebra SchlessingerConditionsSpec
  SchlessingerTangentVectorSpaceSpec SchlessingerCandidateSpec IsLocalRing
open scoped TensorProduct

noncomputable section

set_option linter.style.haveILetI false

private theorem map_comp_apply {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k)
    {A B C : LocalArtinAlgebra.{u,u} k} (f : Hom A B) (g : Hom B C)
    (x : F.toFunctor.obj A) :
    F.toFunctor.map (g.comp f) x = F.toFunctor.map g (F.toFunctor.map f x) :=
  ConcreteCategory.congr_hom (F.toFunctor.map_comp f g) x

section Completion

variable {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
local notation "m" => maximalIdeal S

omit [IsLocalRing S] [IsNoetherianRing S] in
private theorem smul_top_eq (I : Ideal S) : (I • (⊤ : Submodule S S)) = I :=
  (Ideal.smul_eq_mul I ⊤).trans (Ideal.mul_top I)

private theorem mem_of_all_quotient_images {J : Ideal S} {x : S}
    (hx : ∀ q : ℕ, Ideal.Quotient.mk (m ^ q) x ∈ J.map (Ideal.Quotient.mk (m ^ q))) :
    x ∈ J := by
  by_cases hJ : J = ⊤
  · simp [hJ]
  have hJm := le_maximalIdeal hJ
  letI := quotientNontrivial J hJm
  letI := quotientLocal J hJm
  let f := Ideal.Quotient.mk J
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsHausdorff.haus' (I := maximalIdeal (S ⧸ J))
  intro n
  rw [SModEq.zero, smul_top_eq, ← map_maximalIdeal_of_surjective f hf, ← Ideal.map_pow]
  obtain ⟨y, hy, hey⟩ := Ideal.mem_image_of_mem_map_of_surjective _
    Ideal.Quotient.mk_surjective (hx n)
  have hxy : x - y ∈ m ^ n := Ideal.Quotient.eq.mp hey.symm
  have he : f (x - y) = f x := by
    rw [map_sub, show f y = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hy, sub_zero]
  rw [← he]
  exact Ideal.mem_map_of_mem f hxy

/-- The image of the intersection is the eventual image at each finite order. -/
theorem stableImages : StableImages.{u} := by
  intro S _ _ _ _ J hJ
  classical
  let nI := maximalIdeal S
  let Q (q : ℕ) := S ⧸ nI ^ q
  let π (q : ℕ) : S →+* Q q := Ideal.Quotient.mk _
  have hπ (q : ℕ) : Function.Surjective (π q) := Ideal.Quotient.mk_surjective
  have hArtin (q : ℕ) : IsArtinianRing (Q q) := by
    cases q with
    | zero =>
      change IsArtinianRing (S ⧸ nI ^ 0)
      rw [pow_zero, Ideal.one_eq_top]
      haveI : Subsingleton (S ⧸ (⊤ : Ideal S)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      exact isArtinian_of_finite
    | succ q =>
      have h : nI ^ (q + 1) ≤ nI := Ideal.pow_le_self (Nat.succ_ne_zero q)
      letI := quotientNontrivial _ h
      letI := quotientLocal _ h
      apply (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr
      refine ⟨q + 1, ?_⟩
      rw [← map_maximalIdeal_of_surjective (π (q + 1)) (hπ _), ← Ideal.map_pow,
        Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker]
      exact Ideal.mk_ker.ge
  have stability (q : ℕ) : ∃ N, ∀ j ≥ N, (J j).map (π q) = (J N).map (π q) := by
    letI := hArtin q
    obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes
      (R := Q q) (M := Q q) ⟨fun i => (J i).map (π q), fun _ _ h => Ideal.map_mono (hJ h)⟩
    exact ⟨N, fun j hj => (hN j hj).symm⟩
  choose N hN using stability
  let D (q : ℕ) : Ideal (Q q) := (J (N q)).map (π q)
  have allStages (q i : ℕ) : D q ≤ (J i).map (π q) := by
    rw [show D q = (J (max (N q) i)).map (π q) from (hN q _ (le_max_left ..)).symm]
    exact Ideal.map_mono (hJ (le_max_right ..))
  have next (q : ℕ) (x : D q) : ∃ y : D (q + 1),
      Ideal.Quotient.factorPow nI (Nat.le_succ q) y.val = x.val := by
    let l := max (N q) (N (q + 1))
    have hx : x.val ∈ (J l).map (π q) := allStages q l x.property
    obtain ⟨s, hs, he⟩ := Ideal.mem_image_of_mem_map_of_surjective _ (hπ q) hx
    refine ⟨⟨π (q + 1) s, ?_⟩, he⟩
    rw [show D (q + 1) = (J l).map (π (q + 1)) from (hN _ _ (le_max_right ..)).symm]
    exact Ideal.mem_map_of_mem _ hs
  intro q
  refine ⟨N q, fun j hj => (hN q j hj).trans ?_⟩
  apply le_antisymm _ (Ideal.map_mono (iInf_le J (N q)))
  intro x hx
  let z : (n : ℕ) → D (q + n) := fun n =>
    Nat.recOn n (show D (q + 0) from ⟨x, hx⟩)
      (fun n a => (next (q + n) a).choose)
  have hz (n : ℕ) : (z n).val = Ideal.Quotient.factorPow nI
      (Nat.le_succ (q + n)) (z (n + 1)).val :=
    ((next (q + n) (z n)).choose_spec).symm
  have hzall {a b : ℕ} (h : a ≤ b) : (z a).val =
      Ideal.Quotient.factorPow nI (Nat.add_le_add_left h q) (z b).val :=
    Ideal.Quotient.eq_factor_of_eq_factor_succ
      (fun _ _ h => Ideal.pow_le_pow_right (Nat.add_le_add_left h q)) (fun n => (z n).val) hz h
  choose s hs using fun n => hπ (q + n) (z n).val
  have agree {a b : ℕ} (h : a ≤ b) : π (q + a) (s a) = π (q + a) (s b) := by
    rw [hs a, hzall h, ← hs b]
    rfl
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := nI) inferInstance (f := s) (by
    intro a b hab
    rw [SModEq.sub_mem, smul_top_eq]
    exact Ideal.pow_le_pow_right (Nat.le_add_left a q)
      (Ideal.Quotient.eq.mp (agree hab)))
  have hL' (a : ℕ) : π (q + a) L = (z a).val := by
    have hlarge : a ≤ q + a := Nat.le_add_left a q
    have h := hL (q + a)
    rw [SModEq.sub_mem, smul_top_eq] at h
    exact (Ideal.Quotient.eq.mpr h).symm.trans ((agree hlarge).symm.trans (hs a))
  have hmem : L ∈ ⨅ i, J i := by
    apply Ideal.mem_iInf.mpr
    intro i
    apply mem_of_all_quotient_images
    intro n
    have h := allStages (q + n) i (hL' n ▸ (z n).property)
    obtain ⟨a, ha, hea⟩ := Ideal.mem_image_of_mem_map_of_surjective _ (hπ _) h
    have he : π n a = π n L :=
      congrArg (Ideal.Quotient.factorPow nI (Nat.le_add_left n q)) hea
    exact he ▸ Ideal.mem_map_of_mem _ ha
  have he : π q L = x := hL' 0
  rw [← he]
  exact Ideal.mem_map_of_mem (π q) hmem

private theorem quotient_complete [IsAdicComplete m S]
    (J : Ideal S) (hJ : J ≤ m) :
    letI := quotientLocal J hJ
    IsAdicComplete (maximalIdeal (S ⧸ J)) (S ⧸ J) := by
  classical
  letI := quotientNontrivial J hJ
  letI := quotientLocal J hJ
  let f := Ideal.Quotient.mk J
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hm (n : ℕ) : (m ^ n).map f = maximalIdeal (S ⧸ J) ^ n := by
    rw [Ideal.map_pow, map_maximalIdeal_of_surjective f hf]
  refine { toIsHausdorff := inferInstance, prec' := ?_ }
  intro x hx
  have step (n : ℕ) (a : {s : S // f s = x n}) :
      ∃ b : {s : S // f s = x (n + 1)}, a.val - b.val ∈ m ^ n := by
    have h := hx (Nat.le_succ n)
    rw [SModEq.sub_mem, smul_top_eq, ← hm] at h
    obtain ⟨d, hd, he⟩ := Ideal.mem_image_of_mem_map_of_surjective f hf h
    refine ⟨⟨a.val - d, ?_⟩, ?_⟩
    · rw [map_sub, a.property, he, sub_sub_cancel]
    · change a.val - (a.val - d) ∈ m ^ n
      rw [sub_sub_cancel]
      exact hd
  let a : (n : ℕ) → {s : S // f s = x n} := fun n =>
    Nat.recOn n ⟨(hf (x 0)).choose, (hf (x 0)).choose_spec⟩ (fun n s => (step n s).choose)
  have hstep (n : ℕ) : (a n).val - (a (n + 1)).val ∈ m ^ n := (step n (a n)).choose_spec
  have hseq {i j : ℕ} (hij : i ≤ j) : (a i).val - (a j).val ∈ m ^ i := by
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      have hh := (m ^ i).add_mem ih (Ideal.pow_le_pow_right hij (hstep j))
      rwa [sub_add_sub_cancel] at hh
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := m) inferInstance
    (f := fun n => (a n).val) (by
      intro i j hij
      rw [SModEq.sub_mem, smul_top_eq]
      exact hseq hij)
  refine ⟨f L, fun n => ?_⟩
  rw [SModEq.sub_mem, smul_top_eq, ← hm, ← (a n).property, ← map_sub]
  apply Ideal.mem_map_of_mem
  simpa only [SModEq.sub_mem, smul_top_eq] using hL n

end Completion

section Stages

open LargestArtinLiftQuotientSpec
open private lift_of_presentation from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LargestArtinLiftQuotient

variable {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k) (r : ℕ)

local notation "S" => Series k r
local notation "nI" => maximalIdeal S
local notation "res" => seriesResidue k r

private structure Stage (i : ℕ) where
  ideal : Ideal S
  below : ideal ≤ nI
  power : nI ^ (i + 2) ≤ ideal
  element : F.toFunctor.obj (artinQuotient res ideal below ⟨_, power⟩)

variable {F r}

private abbrev Stage.obj {i : ℕ} (s : Stage F r i) : LocalArtinAlgebra.{u,u} k :=
  artinQuotient res s.ideal s.below ⟨_, s.power⟩

private abbrev Stage.transition {i j : ℕ} {s : Stage F r i} {t : Stage F r j}
    (h : s.ideal ≤ t.ideal) : Hom s.obj t.obj :=
  artinTransition res h

private theorem artinTransition_comp {I K L : Ideal S}
    {hI : I ≤ nI} {hK : K ≤ nI} {hL : L ≤ nI}
    {pI : ∃ q : ℕ, nI ^ q ≤ I} {pK : ∃ q : ℕ, nI ^ q ≤ K} {pL : ∃ q : ℕ, nI ^ q ≤ L}
    (h : I ≤ K) (g : K ≤ L) :
    (artinTransition res (hI := hK) (hK := hL) (pI := pK) (pK := pL) g).comp
      (artinTransition res (hI := hI) (pI := pI) h) = artinTransition res (h.trans g) := by
  apply Hom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) x
  rfl

private theorem Stage.transition_id {i : ℕ} (s : Stage F r i) :
    s.transition (t := s) le_rfl = Hom.id s.obj := by
  apply Hom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := s.ideal) x
  rfl

private structure Next {i : ℕ} (s : Stage F r i) (t : Stage F r (i + 1)) : Prop where
  le : t.ideal ≤ s.ideal
  mul_le : nI * s.ideal ≤ t.ideal
  compatible : F.toFunctor.map (Stage.transition (s := t) (t := s) le) t.element = s.element
  least : ∀ (K : Ideal S) (hK : K ≤ s.ideal) (pK : ∃ q : ℕ, nI ^ q ≤ K),
    nI * s.ideal ≤ K →
    (∃ y : F.toFunctor.obj (artinQuotient res K (hK.trans s.below) pK),
      F.toFunctor.map (artinTransition res hK) y = s.element) → t.ideal ≤ K

private theorem advance (h₁ : H1Model F) {i : ℕ} (s : Stage F r i) :
    ∃ t : Stage F r (i + 1), Next s t := by
  let P := nI * s.ideal
  have hPI : P ≤ s.ideal := Ideal.mul_le_right
  have hPmax := hPI.trans s.below
  have hPpow : nI ^ (i + 1 + 2) ≤ P := by
    rw [show i + 1 + 2 = 1 + (i + 2) by omega, pow_add, pow_one]
    exact Ideal.mul_mono le_rfl s.power
  let B := artinQuotient res P hPmax ⟨_, hPpow⟩
  let π : S →+* B := Ideal.Quotient.mk P
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  let f : Hom B s.obj := artinTransition res hPI
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hPI
  have hker : RingHom.ker f.val.toRingHom = s.ideal.map π :=
    Ideal.Quotient.factor_ker hPI
  have hm : maximalIdeal B = (nI).map π := (map_maximalIdeal_of_surjective π hπ).symm
  have hkill : ∀ a ∈ maximalIdeal B, ∀ b ∈ RingHom.ker f.val.toRingHom, a * b = 0 := by
    intro a ha b hb
    rw [hm] at ha
    rw [hker] at hb
    obtain ⟨a', ha', rfl⟩ := Ideal.mem_image_of_mem_map_of_surjective π hπ ha
    obtain ⟨b', hb', rfl⟩ := Ideal.mem_image_of_mem_map_of_surjective π hπ hb
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_mul ha' hb')
  obtain ⟨U, hU⟩ := ArtinFunctor.exists_least_lift_subspace F h₁ f hf hkill s.element
  let L := idealOfSocleSubmodule f hkill U hU.1.1
  let J := L.comap π
  have hPJ : P ≤ J := by
    intro a ha
    change π a ∈ L
    rw [show π a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact L.zero_mem
  have hJI : J ≤ s.ideal := by
    intro a ha
    have h : π a ∈ RingHom.ker f.val.toRingHom := hU.1.1 ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp h)
  have hJm := hJI.trans s.below
  have hJpow := hPpow.trans hPJ
  let C := artinQuotient res J hJm ⟨_, hJpow⟩
  let p : Hom B C := artinTransition res hPJ
  let g : Hom C s.obj := artinTransition res hJI
  have hpker : RingHom.ker p.val.toRingHom = L :=
    (Ideal.Quotient.factor_ker hPJ).trans (Ideal.map_comap_of_surjective π hπ L)
  have hcomp : g.comp p = f := artinTransition_comp hPJ hJI
  have hUker : U ≤ kernelSubspace p := by
    change L.restrictScalars k ≤ _
    change _ ≤ (RingHom.ker p.val.toRingHom).restrictScalars k
    rw [hpker]
  obtain ⟨y, hy⟩ := lift_of_presentation F hU.1.2 p g hUker hcomp
  let t : Stage F r (i + 1) := ⟨J, hJm, hJpow, y⟩
  refine ⟨t, hJI, hPJ, hy, ?_⟩
  intro K hKI pK hPK hLift
  let C' := artinQuotient res K (hKI.trans s.below) pK
  let p' : Hom B C' := artinTransition res hPK
  let g' : Hom C' s.obj := artinTransition res hKI
  have hp'ker : RingHom.ker p'.val.toRingHom = K.map π := Ideal.Quotient.factor_ker hPK
  have hw : kernelSubspace p' ≤ kernelSubspace f := by
    change RingHom.ker p'.val.toRingHom ≤ RingHom.ker f.val.toRingHom
    rw [hp'ker, hker]
    exact Ideal.map_mono hKI
  have hp' : Function.Surjective p' := Ideal.Quotient.factor_surjective hPK
  have hcomp' : g'.comp p' = f := artinTransition_comp hPK hKI
  have hUL : U ≤ kernelSubspace p' := hU.2 ⟨hw, C', p', g', hp', rfl, hcomp', hLift⟩
  have hLK : L ≤ K.map π := by
    change U ≤ (K.map π).restrictScalars k
    exact (congrArg (fun I : Ideal B => I.restrictScalars k) hp'ker) ▸ hUL
  change L.comap π ≤ K
  have h := Ideal.comap_mono (f := π) hLK
  have hπker : RingHom.ker π = P := Ideal.mk_ker
  rw [Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hπker,
    sup_of_le_left hPK] at h
  exact h

private theorem square_below : nI ^ 2 ≤ nI := Ideal.pow_le_self (by decide)

private abbrev firstStage (r : ℕ) (k : Type u) [Field k] : LocalArtinAlgebra.{u,u} k :=
  artinQuotient (seriesResidue k r) ((maximalIdeal (Series k r)) ^ 2) square_below ⟨2, le_rfl⟩

private def stageSequence (h₁ : H1Model F) (x : F.toFunctor.obj (firstStage r k)) :
    (i : ℕ) → Stage F r i
  | 0 => ⟨nI ^ 2, square_below, le_rfl, x⟩
  | i + 1 => (advance h₁ (stageSequence h₁ x i)).choose

private theorem stageSequence_next (h₁ : H1Model F) (x : F.toFunctor.obj (firstStage r k))
    (i : ℕ) : Next (stageSequence h₁ x i) (stageSequence h₁ x (i + 1)) :=
  (advance h₁ (stageSequence h₁ x i)).choose_spec

private def towerFromFirst (h₁ : H1Model F) (x : F.toFunctor.obj (firstStage r k)) : Tower F r := by
  let s := stageSequence h₁ x
  have hn (i : ℕ) : Next (s i) (s (i + 1)) := stageSequence_next h₁ x i
  have ha : Antitone (fun i => (s i).ideal) := antitone_nat_of_succ_le (fun i => (hn i).le)
  refine
    { ideal := fun i => (s i).ideal
      below := fun i => (s i).below
      power := fun i => (s i).power
      first := rfl
      decreasing := ha
      element := fun i => (s i).element
      compatible := ?_
      mul_le := fun i => (hn i).mul_le
      least := fun i => (hn i).least }
  intro i j hij
  change F.toFunctor.map (Stage.transition (s := s j) (t := s i) (ha hij)) (s j).element =
    (s i).element
  induction j, hij using Nat.le_induction with
  | base =>
    rw [Stage.transition_id]
    exact ConcreteCategory.congr_hom (F.toFunctor.map_id _) _
  | succ j hij ih =>
    have h : (Stage.transition (s := s j) (t := s i) (ha hij)).comp
        (Stage.transition (s := s (j + 1)) (t := s j) (hn j).le) =
        Stage.transition (s := s (j + 1)) (t := s i) (ha (hij.trans (Nat.le_succ j))) :=
      artinTransition_comp _ _
    rw [← h, map_comp_apply, (hn j).compatible, ih]

end Stages

section FirstOrder

variable {k : Type u} [Field k] {r : ℕ}
local notation "S" => Series k r
local notation "nI" => maximalIdeal S
local notation "V" => (Fin r → k)

open MvPowerSeries

private theorem coeff_linear_mul (a b : S) (i : Fin r) :
    coeff (Finsupp.single i 1) (a * b) =
      constantCoeff a * coeff (Finsupp.single i 1) b +
        coeff (Finsupp.single i 1) a * constantCoeff b := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map,
    show (1 : ℕ) = 0 + 1 by rfl, Finset.Nat.sum_antidiagonal_succ]
  simp [coeff_zero_eq_constantCoeff_apply]

private def firstJet : S →ₐ[k] splitModel k V where
  toFun f := ⟨constantCoeff f, fun i => coeff (Finsupp.single i 1) f⟩
  map_zero' := TrivSqZeroExt.ext (map_zero _) (funext fun _ => map_zero _)
  map_one' := by
    apply TrivSqZeroExt.ext (map_one _)
    funext i
    change coeff (Finsupp.single i 1) (1 : S) = 0
    classical simp [coeff_one]
  map_add' a b := TrivSqZeroExt.ext (map_add _ _ _) (funext fun _ => map_add _ _ _)
  map_mul' a b := by
    apply TrivSqZeroExt.ext (map_mul _ _ _)
    funext i
    change coeff (Finsupp.single i 1) (a * b) = constantCoeff a * coeff (Finsupp.single i 1) b +
      constantCoeff b * coeff (Finsupp.single i 1) a
    rw [coeff_linear_mul, mul_comm (constantCoeff b)]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact constantCoeff_C c
    · funext i
      change coeff (Finsupp.single i 1) (C c) = 0
      classical simp [coeff_C]

private theorem firstJet_ker : RingHom.ker (firstJet (k := k) (r := r)).toRingHom = nI ^ 2 := by
  ext f
  rw [RingHom.mem_ker, CompleteRegularPowerSeries.maximalIdealPower k r 2 f]
  constructor
  · intro h a
    by_cases hd : 2 ≤ a.degree
    · simp [Nat.sub_eq_zero_of_le hd]
    have hsmall : a.degree = 0 ∨ a.degree = 1 := by omega
    suffices coeff a f = 0 by rw [this]; exact Ideal.zero_mem _
    rcases hsmall with h₀ | h₁
    · have hzero := (Finsupp.degree_eq_zero_iff a).mp h₀
      subst a
      exact congrArg (TrivSqZeroExt.fst : TrivSqZeroExt k V → k) h
    · have hm : a ∈ {d : Fin r →₀ ℕ | d.degree = 1} := h₁
      rw [← Finsupp.range_single_one] at hm
      obtain ⟨i, rfl⟩ := hm
      exact congrFun (congrArg (TrivSqZeroExt.snd : TrivSqZeroExt k V → V) h) i
  · intro h
    apply TrivSqZeroExt.ext
    · have h₀ := h 0
      change constantCoeff f = 0
      simpa [maximalIdeal_eq_bot, coeff_zero_eq_constantCoeff_apply] using h₀
    · funext i
      have hi := h (Finsupp.single i 1)
      change coeff (Finsupp.single i 1) f = 0
      simpa [Finsupp.degree_single, maximalIdeal_eq_bot] using hi

private theorem firstJet_surjective : Function.Surjective (firstJet (k := k) (r := r)) := by
  classical
  intro z
  refine ⟨C z.fst + ∑ i : Fin r, monomial (Finsupp.single i 1) (z.snd i), ?_⟩
  apply TrivSqZeroExt.ext
  · change constantCoeff _ = _
    rw [map_add, constantCoeff_C, map_sum, Finset.sum_eq_zero]
    · simp
    · intro i _
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial]
      have h : Finsupp.single i (1 : ℕ) ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
      simp [h.symm]
  · funext i
    change coeff (Finsupp.single i 1) _ = _
    simp [map_sum, coeff_C, coeff_monomial, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

private def firstJetQuot : Hom (firstStage r k) (splitModel k V) :=
  letI := quotientLocal (nI ^ 2) square_below
  let f := Ideal.Quotient.liftₐ (nI ^ 2) (firstJet (k := k) (r := r)) (fun _ hx =>
    RingHom.mem_ker.mp ((firstJet_ker (k := k) (r := r)).symm ▸ hx))
  ⟨f, ⟨(IsLocalHom.of_surjective f.toRingHom (fun z => by
    obtain ⟨s, hs⟩ := firstJet_surjective z
    exact ⟨Ideal.Quotient.mk _ s, hs⟩)).map_nonunit⟩⟩

private theorem firstJetQuot_bijective : Function.Bijective (firstJetQuot (k := k) (r := r)) := by
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot firstJetQuot.val.toRingHom).mpr
    ext a
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective (I := nI ^ 2) a
    change firstJet f = 0 ↔ Ideal.Quotient.mk (nI ^ 2) f ∈ (⊥ : Ideal (S ⧸ nI ^ 2))
    rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, ← firstJet_ker]
    rfl
  · intro z
    obtain ⟨s, hs⟩ := firstJet_surjective z
    exact ⟨Ideal.Quotient.mk _ s, hs⟩

private theorem firstJetQuot_X (i : Fin r) :
    firstJetQuot (k := k) (Ideal.Quotient.mk (nI ^ 2) (X i)) =
      TrivSqZeroExt.inr (Pi.basisFun k (Fin r) i) := by
  classical
  apply TrivSqZeroExt.ext
  · exact constantCoeff_X i
  · funext j
    change coeff (Finsupp.single j 1) (X i : S) = (Pi.basisFun k (Fin r) i) j
    rw [coeff_index_single_X, Pi.basisFun_apply, Pi.single_apply]

end FirstOrder

section FormalObject

variable {k : Type u} [Field k] {F : ArtinFunctorModel.{u,w} k} {r : ℕ}
variable (T : Tower F r)
local notation "S" => Series k r
local notation "nI" => maximalIdeal S
local notation "J" => T.limitIdeal

private theorem series_complete : IsAdicComplete nI S :=
  (CompleteRegularPowerSeries.overField k r).2.2.1

private theorem tower_complete :
    letI := quotientLocal J ((T.limit_le 0).trans (T.below 0))
    IsAdicComplete (maximalIdeal (S ⧸ J)) (S ⧸ J) := by
  letI := series_complete (k := k) (r := r)
  exact quotient_complete J ((T.limit_le 0).trans (T.below 0))

local notation "R" => T.ring (tower_complete T)
local notation "π" => Ideal.Quotient.mk J
local notation "p" => T.projection (hc := tower_complete T)

private theorem projection_surj (i : ℕ) : Function.Surjective (p i) :=
  Ideal.Quotient.factor_surjective (T.limit_le i)

private theorem ker_projection (i : ℕ) : RingHom.ker (p i).val = (T.ideal i).map π :=
  Ideal.Quotient.factor_ker (T.limit_le i)

private theorem map_power (q : ℕ) : (nI ^ q).map π = maximalIdeal R ^ q := by
  letI := quotientLocal J ((T.limit_le 0).trans (T.below 0))
  letI := quotientNontrivial J ((T.limit_le 0).trans (T.below 0))
  change (nI ^ q).map π = maximalIdeal (S ⧸ J) ^ q
  rw [Ideal.map_pow, map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective]

private theorem cofinal (q : ℕ) : ∃ i : ℕ, (T.ideal i).map π ≤ maximalIdeal R ^ q := by
  letI := series_complete (k := k) (r := r)
  obtain ⟨i, hi⟩ := stableImages S T.ideal T.decreasing q
  refine ⟨i, ?_⟩
  rw [← map_power T]
  intro a ha
  obtain ⟨s, hs, rfl⟩ := Ideal.mem_image_of_mem_map_of_surjective π
    Ideal.Quotient.mk_surjective ha
  let e := Ideal.Quotient.mk (nI ^ q)
  have hse : e s ∈ (T.ideal i).map e := Ideal.mem_map_of_mem e hs
  rw [hi _ le_rfl] at hse
  obtain ⟨t, ht, hts⟩ := Ideal.mem_image_of_mem_map_of_surjective e
    Ideal.Quotient.mk_surjective hse
  have hst : s - t ∈ nI ^ q := Ideal.Quotient.eq.mp hts.symm
  have he : π (s - t) = π s := by
    rw [map_sub, show π t = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ht, sub_zero]
  rw [← he]
  exact Ideal.mem_map_of_mem π hst

private theorem power_le_image (i : ℕ) :
    maximalIdeal R ^ (i + 2) ≤ (T.ideal i).map π := by
  rw [← map_power T]
  exact Ideal.map_mono (T.power i)

private theorem projection_comp {i j : ℕ} (h : i ≤ j) :
    (p j).postcomp (artinTransition (seriesResidue k r) (T.decreasing h)) = p i := by
  apply CompleteLocalAlgebra.Hom.ext
  intro x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) x
  rfl

private theorem maximalPower_le_ker {A : LocalArtinAlgebra.{u,u} k}
    (f : CompleteLocalAlgebra.Hom R A) {q : ℕ} (hq : maximalIdeal A ^ q = ⊥) :
    maximalIdeal R ^ q ≤ RingHom.ker f.val := by
  letI : IsLocalHom f.val.toRingHom := ⟨f.property.map_nonunit⟩
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
  exact (le_bot_iff.mp ((Ideal.pow_right_mono (map_maximalIdeal_le f.val.toRingHom) q).trans hq.le))

private theorem factor_at {A : LocalArtinAlgebra.{u,u} k} (f : CompleteLocalAlgebra.Hom R A)
    (i : ℕ) (hker : RingHom.ker (p i).val ≤ RingHom.ker f.val) :
    ∃ g : Hom (T.stage i) A, (p i).postcomp g = f := by
  let g := (p i).val.liftOfSurjective (projection_surj T i) f.val hker
  have hg (x : R) : g ((p i) x) = f x :=
    AlgHom.liftOfSurjective_apply _ (projection_surj T i) _ _ x
  let g' : Hom (T.stage i) A := ⟨g, ⟨fun a ha => by
    obtain ⟨x, rfl⟩ := projection_surj T i a
    exact (IsUnit.of_map f.val x (hg x ▸ ha)).map (p i).val⟩⟩
  exact ⟨g', CompleteLocalAlgebra.Hom.ext hg⟩

private theorem factor_at_unique {A : LocalArtinAlgebra.{u,u} k} (i : ℕ)
    {a b : Hom (T.stage i) A} (h : (p i).postcomp a = (p i).postcomp b) : a = b := by
  apply Hom.ext
  intro x
  obtain ⟨s, rfl⟩ := projection_surj T i x
  exact congrArg (fun f : CompleteLocalAlgebra.Hom R A => f s) h

private theorem factor_exists {A : LocalArtinAlgebra.{u,u} k} (f : CompleteLocalAlgebra.Hom R A) :
    ∃ (i : ℕ) (g : Hom (T.stage i) A), (p i).postcomp g = f := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  obtain ⟨i, hi⟩ := cofinal T n
  have hn' : maximalIdeal A ^ n = ⊥ := by simpa only [Ideal.zero_eq_bot] using hn
  have hker := maximalPower_le_ker T f hn'
  rw [← ker_projection] at hi
  obtain ⟨g, hg⟩ := factor_at T f i (hi.trans hker)
  exact ⟨i, g, hg⟩

private theorem same_evaluation {A : LocalArtinAlgebra.{u,u} k} {i j : ℕ}
    (a : Hom (T.stage i) A) (b : Hom (T.stage j) A)
    (h : (p i).postcomp a = (p j).postcomp b) :
    F.toFunctor.map a (T.element i) = F.toFunctor.map b (T.element j) := by
  let l := max i j
  have hi : i ≤ l := le_max_left _ _
  have hj : j ≤ l := le_max_right _ _
  let u : Hom (T.stage l) (T.stage i) := artinTransition (seriesResidue k r) (T.decreasing hi)
  let v : Hom (T.stage l) (T.stage j) := artinTransition (seriesResidue k r) (T.decreasing hj)
  have hu : (p l).postcomp (a.comp u) = (p i).postcomp a := by
    change ((p l).postcomp u).postcomp a = _
    rw [projection_comp T hi]
  have hv : (p l).postcomp (b.comp v) = (p j).postcomp b := by
    change ((p l).postcomp v).postcomp b = _
    rw [projection_comp T hj]
  have hab : a.comp u = b.comp v := factor_at_unique T l (hu.trans (h.trans hv.symm))
  simpa only [map_comp_apply, show F.toFunctor.map u (T.element l) = T.element i from T.compatible hi,
    show F.toFunctor.map v (T.element l) = T.element j from T.compatible hj] using
    congrArg (fun g : Hom (T.stage l) A => F.toFunctor.map g (T.element l)) hab

private def evaluate {A : LocalArtinAlgebra.{u,u} k} (f : CompleteLocalAlgebra.Hom R A) :
    F.toFunctor.obj A :=
  let h := factor_exists T f
  F.toFunctor.map h.choose_spec.choose (T.element h.choose)

private theorem evaluate_at {A : LocalArtinAlgebra.{u,u} k} (i : ℕ) (g : Hom (T.stage i) A) :
    evaluate T ((p i).postcomp g) = F.toFunctor.map g (T.element i) := by
  let h := factor_exists T ((p i).postcomp g)
  exact same_evaluation T h.choose_spec.choose g h.choose_spec.choose_spec

private def transformation : (representableModel.{u,w} R).toFunctor ⟶ F.toFunctor where
  app _ := TypeCat.ofHom fun f => evaluate T f.down
  naturality := by
    intro A B g
    apply ConcreteCategory.hom_ext
    intro a
    change evaluate T (a.down.postcomp g) = F.toFunctor.map g (evaluate T a.down)
    obtain ⟨i, f, hf⟩ := factor_exists T a.down
    rw [← hf, evaluate_at]
    change evaluate T ((p i).postcomp (g.comp f)) = _
    rw [evaluate_at, map_comp_apply]

end FormalObject

section Tangent

variable {k : Type u} [Field k] {F : ArtinFunctorModel.{u,w} k} {r : ℕ}
local notation "V" => (Fin r → k)
local notation "D" => dualModel k

private def inverseHom {A B : LocalArtinAlgebra.{u,u} k} (f : Hom A B)
    (hf : Function.Bijective f) : Hom B A := by
  let e : A ≃ₐ[k] B := AlgEquiv.ofBijective f.val hf
  exact ⟨e.symm.toAlgHom, ⟨(IsLocalHom.of_surjective (e.symm : B →+* A) e.symm.surjective).map_nonunit⟩⟩

private theorem inverseHom_right {A B : LocalArtinAlgebra.{u,u} k} (f : Hom A B)
    (hf : Function.Bijective f) : f.comp (inverseHom f hf) = Hom.id B :=
  Hom.ext (fun x => (AlgEquiv.ofBijective f.val hf).apply_symm_apply x)

private theorem inverseHom_left {A B : LocalArtinAlgebra.{u,u} k} (f : Hom A B)
    (hf : Function.Bijective f) : (inverseHom f hf).comp f = Hom.id A :=
  Hom.ext (fun x => (AlgEquiv.ofBijective f.val hf).symm_apply_apply x)

private theorem precomp_bijective {A B C : LocalArtinAlgebra.{u,u} k} (f : Hom A B)
    (hf : Function.Bijective f) : Function.Bijective (fun g : Hom B C => g.comp f) := by
  constructor
  · intro a b h
    apply Hom.ext
    intro x
    obtain ⟨y, rfl⟩ := hf.surjective x
    exact congrArg (fun g : Hom A C => g y) h
  · intro a
    refine ⟨a.comp (inverseHom f hf), ?_⟩
    apply Hom.ext
    intro x
    exact congrArg (fun g : Hom A A => a (g x)) (inverseHom_left f hf)

private def covectorToDual (l : Module.Dual k V) : Hom (splitModel k V) D :=
  (show Hom (splitModel k k) D from eqToHom (split_eq_dual k)).comp (splitMapModel l)

private theorem covectorToDual_apply (l : Module.Dual k V) (x : splitModel k V) :
    covectorToDual l x = (⟨x.fst, l x.snd⟩ : TrivSqZeroExt k k) := by
  change (show Hom (splitModel k k) D from eqToHom (split_eq_dual k)).val
    ((splitMapModel l).val x) = _
  rw [split_eq_dual_apply]
  letI : Module kᵐᵒᵖ V := splitOppositeModule k V
  letI : Module kᵐᵒᵖ k := splitOppositeModule k k
  letI : IsCentralScalar k V := ⟨fun _ _ => rfl⟩
  letI : IsCentralScalar k k := ⟨fun _ _ => rfl⟩
  change TrivSqZeroExt.map l x = _
  exact TrivSqZeroExt.ext (TrivSqZeroExt.fst_map l x) (TrivSqZeroExt.snd_map l x)

private theorem covectorToDual_bijective :
    Function.Bijective (covectorToDual (k := k) (r := r)) := by
  constructor
  · intro l h he
    apply LinearMap.ext
    intro v
    let x : splitModel k V := TrivSqZeroExt.inr v
    have hv : covectorToDual l x = covectorToDual h x :=
      congrArg (fun a : Hom (splitModel k V) D => a x) he
    exact congrArg (TrivSqZeroExt.snd : TrivSqZeroExt k k → k)
      ((covectorToDual_apply l x).symm.trans (hv.trans (covectorToDual_apply h x)))
  · intro f
    let l : Module.Dual k V := (TrivSqZeroExt.sndHom k k).comp
      (f.val.toLinearMap.comp (TrivSqZeroExt.inrHom k V))
    refine ⟨l, Subtype.ext ?_⟩
    apply AlgHom.ext
    intro z
    let x : splitModel k V := TrivSqZeroExt.inr z.snd
    have hx : (covectorToDual l).val x = f.val x := by
      refine (covectorToDual_apply l x).trans (TrivSqZeroExt.ext ?_ ?_)
      · exact (f.residue_apply x).symm
      · rfl
    have hz : algebraMap k (splitModel k V) z.fst + x = z :=
      TrivSqZeroExt.inl_fst_add_inr_snd_eq z
    rw [← hz, map_add, map_add, AlgHom.commutes, AlgHom.commutes, hx]

private theorem dual_maximal_sq : (maximalIdeal D) ^ 2 = ⊥ := by
  rw [pow_two]
  refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
  intro x hx y hy
  rw [← LocalArtinAlgebra.ker_residue] at hx hy
  have hx' : x.fst = 0 := RingHom.mem_ker.mp hx
  have hy' : y.fst = 0 := RingHom.mem_ker.mp hy
  apply (Submodule.mem_bot (R := D) (M := D)).mpr
  have hx'' : x = (TrivSqZeroExt.inr x.snd : TrivSqZeroExt k k) := TrivSqZeroExt.ext hx' rfl
  have hy'' : y = (TrivSqZeroExt.inr y.snd : TrivSqZeroExt k k) := TrivSqZeroExt.ext hy' rfl
  letI : Module kᵐᵒᵖ k := Semiring.toOppositeModule
  change (x : TrivSqZeroExt k k) * y = 0
  rw [hx'', hy'']
  exact TrivSqZeroExt.inr_mul_inr k _ _

private theorem dual_factor_bijective (T : Tower F r) :
    Function.Bijective (fun a : Hom (T.stage 0) D =>
      ((T.projection (hc := tower_complete T) 0).postcomp a :
        CompleteLocalAlgebra.Hom (T.ring (tower_complete T)) D)) := by
  constructor
  · intro a b h
    exact factor_at_unique T 0 h
  · intro f
    have hker := maximalPower_le_ker T f (dual_maximal_sq (k := k))
    refine factor_at T f 0 ?_
    rw [ker_projection, T.first, map_power]
    exact hker

private theorem tangent_bijective (laws : VectorLaws F)
    (T : Tower F r) (jet : Hom (T.stage 0) (splitModel k V)) (hj : Function.Bijective jet)
    (e : SplitTensorComparison F laws V) :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    ∀ (b : Module.Basis (Fin r) k (TangentModel F)),
    e.equiv (F.toFunctor.map jet (T.element 0)) = ∑ i, b i ⊗ₜ[k] (Pi.basisFun k (Fin r) i) →
    Function.Bijective ((transformation T).app D :
      TangentModel (representableModel.{u,w} (T.ring (tower_complete T))) → TangentModel F) := by
  letI := tangentAddCommGroupModel F laws
  letI := tangentModuleModel F laws
  intro b hb
  let h : Module.Dual k V → TangentModel (representableModel.{u,w} (T.ring (tower_complete T))) :=
    fun l => ULift.up ((T.projection (hc := tower_complete T) 0).postcomp ((covectorToDual l).comp jet))
  have hh : Function.Bijective h :=
    Equiv.ulift.symm.bijective.comp ((dual_factor_bijective T).comp
      ((precomp_bijective (C := D) jet hj).comp covectorToDual_bijective))
  have heval (l : Module.Dual k V) :
      (transformation T).app D (h l) = ∑ i, l (Pi.basisFun k (Fin r) i) • b i := by
    change evaluate T ((T.projection (hc := tower_complete T) 0).postcomp
      ((covectorToDual l).comp jet)) = _
    rw [evaluate_at, map_comp_apply]
    change F.toFunctor.map ((show Hom (splitModel k k) D from eqToHom (split_eq_dual k)).comp
      (splitMapModel l)) (F.toFunctor.map jet (T.element 0)) = _
    rw [map_comp_apply]
    change tangentIdentification F
      (onLinear F l (F.toFunctor.map jet (T.element 0))) = _
    rw [← e.contract, hb, map_sum, LinearMap.sum_apply]
    simp only [tensorContraction_tmul]
  have hcoords : Function.Bijective (fun l : Module.Dual k V =>
      ∑ i, l (Pi.basisFun k (Fin r) i) • b i) := by
    let v := Pi.basisFun k (Fin r)
    have h₁ : Function.Bijective (fun l : Module.Dual k V => fun i => l (v i)) := by
      constructor
      · intro l l' h
        exact v.ext (fun i => congrFun h i)
      · intro a
        refine ⟨v.constr k a, ?_⟩
        funext i
        exact v.constr_basis k a i
    have h₂ := b.equivFun.symm.bijective.comp h₁
    simpa only [Function.comp_def, Module.Basis.equivFun_symm_apply] using h₂
  have hcomp : Function.Bijective (((transformation T).app D :
      TangentModel (representableModel.{u,w} (T.ring (tower_complete T))) → TangentModel F) ∘ h) := by
    change Function.Bijective (fun l => (transformation T).app D (h l))
    rw [funext heval]
    exact hcoords
  exact ⟨fun a b hab => by
    obtain ⟨a', rfl⟩ := hh.surjective a
    obtain ⟨b', rfl⟩ := hh.surjective b
    exact congrArg h (hcomp.injective hab), hcomp.surjective.of_comp⟩

end Tangent

/-- Construction of the source's quotient tower and its tangent-isomorphic natural map. -/
theorem construct : Construction.{u,w} := by
  intro k _ F h₁ h₂ h₃
  let laws := ArtinFunctor.tangentVectorLaws F h₂
  refine ⟨laws, ?_⟩
  letI := tangentAddCommGroupModel F laws
  letI := tangentModuleModel F laws
  letI : Module.Finite k (TangentModel F) := (ArtinFunctor.h3_iff_finite F laws).mp h₃
  let r := Module.finrank k (TangentModel F)
  let V := Fin r → k
  let b := Module.finBasis k (TangentModel F)
  let e := ArtinFunctor.splitTensorComparison F h₂ V
  let t : TangentModel F ⊗[k] V := ∑ i, b i ⊗ₜ[k] (Pi.basisFun k (Fin r) i)
  let jet := firstJetQuot (k := k) (r := r)
  have hj : Function.Bijective jet := firstJetQuot_bijective
  let x := F.toFunctor.map (inverseHom jet hj) (e.equiv.symm t)
  let T := towerFromFirst h₁ x
  have hx : e.equiv (F.toFunctor.map jet (T.element 0)) = t := by
    change e.equiv (F.toFunctor.map jet (F.toFunctor.map (inverseHom jet hj) (e.equiv.symm t))) = t
    rw [← map_comp_apply, inverseHom_right]
    have h := ConcreteCategory.congr_hom (F.toFunctor.map_id (splitModel k V)) (e.equiv.symm t)
    change F.toFunctor.map (Hom.id (splitModel k V)) (e.equiv.symm t) = e.equiv.symm t at h
    rw [h, Equiv.apply_symm_apply]
  refine ⟨b, T, jet, e, hj, firstJetQuot_X, hx, tower_complete T, transformation T,
    cofinal T, power_le_image T, fun _ => factor_exists T, fun _ i g => evaluate_at T i g,
    tangent_bijective laws T jet hj e b hx⟩

end
end CommutativeAlgebraNotes.SchlessingerCandidate
