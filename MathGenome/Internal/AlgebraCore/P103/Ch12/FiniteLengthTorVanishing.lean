import MathGenome.Internal.AlgebraCore.Specs.P103.Ch12.FiniteLengthTorVanishing
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorExactSequences
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.Quotient

namespace P103.Ch12.FiniteLengthTorVanishing
open CategoryTheory P103.BalancedTensor
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Specs.Ch12.FiniteLengthTorVanishing
noncomputable section
universe u v w

theorem simple_equiv_residue : simple_equiv_residueType.{u,v} := by
  intro R _ _ F _ _ _
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule R F)
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  exact ⟨e⟩

/-- A linear equivalence also respects the canonical right actions. -/
def commRightEquiv {R : Type u} [CommRing R]
    {A : Type v} {B : Type w} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) :
    letI := commRightModule R A
    letI := commRightModule R B
    A ≃ₗ[Rᵐᵒᵖ] B := by
  letI := commRightModule R A
  letI := commRightModule R B
  exact { e.toAddEquiv with map_smul' := fun r x => e.map_smul r.unop x }

/-- Isomorphism invariance, including change of projective resolution. -/
theorem tor_subsingleton_of_equiv {R : Type u} [Ring R]
    {A B : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ B) (M : ModuleCat.{w} R)
    (e : A ≃ₗ[Rᵐᵒᵖ] B) (h : Subsingleton (TorWith P.val M 1)) :
    Subsingleton (TorWith Q.val M 1) := by
  let T := P103.Ch11.ExtTorDefinitions.torMaps.{u,v,w} (R := R) 1
  let f : A ⟶ B := ModuleCat.ofHom e.toLinearMap
  let g : B ⟶ A := ModuleCat.ofHom e.symm.toLinearMap
  have hgf : g ≫ f = 𝟙 B := by ext x; exact e.apply_symm_apply x
  have hleft : (T.map P Q f (𝟙 M)).comp (T.map Q P g (𝟙 M)) = LinearMap.id := by
    rw [← T.comp, hgf, Category.id_comp, T.id]
  have hinj : Function.Injective (T.map Q P g (𝟙 M)) := by
    apply Function.LeftInverse.injective (f := T.map Q P g (𝟙 M))
    intro x
    exact LinearMap.congr_fun hleft x
  letI := h
  exact hinj.subsingleton

/-- Tor of a zero module is zero, from additivity and the identity law. -/
theorem tor_subsingleton_zero {R : Type u} [Ring R]
    (A : ModuleCat.{v} Rᵐᵒᵖ) [Subsingleton A]
    (P : ProjectiveChoice Rᵐᵒᵖ A) (M : ModuleCat.{w} R) :
    Subsingleton (TorWith P.val M 1) := by
  let T := P103.Ch11.ExtTorDefinitions.torMaps.{u,v,w} (R := R) 1
  have hzero : T.map P P (0 : A ⟶ A) (𝟙 M) = 0 := by
    have hh := T.add_first P P (0 : A ⟶ A) 0 (𝟙 M)
    exact add_left_cancel (a := T.map P P 0 (𝟙 M))
      (by simpa only [add_zero] using hh.symm)
  have hid : (𝟙 A : A ⟶ A) = 0 := by ext x; exact Subsingleton.elim _ _
  have hz : (LinearMap.id : TorWith P.val M 1 →ₗ[ℤ] TorWith P.val M 1) = 0 := by
    rw [← T.id P M, hid, hzero]
  exact ⟨fun x y => by
    have hx : x = 0 := LinearMap.congr_fun hz x
    have hy : y = 0 := LinearMap.congr_fun hz y
    exact hx.trans hy.symm⟩

/-- Vanishing is stable under extensions, by the first-variable Tor sequence. -/
theorem tor_vanishing_extension {R : Type u} [Ring R]
    {A B C : ModuleCat.{v} Rᵐᵒᵖ} (M : ModuleCat.{w} R)
    (i : A →ₗ[Rᵐᵒᵖ] B) (p : B →ₗ[Rᵐᵒᵖ] C)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p)
    (L : ProjectiveChoice Rᵐᵒᵖ A) (N : ProjectiveChoice Rᵐᵒᵖ C)
    (hL : Subsingleton (TorWith L.val M 1))
    (hN : Subsingleton (TorWith N.val M 1))
    (P : ProjectiveChoice Rᵐᵒᵖ B) : Subsingleton (TorWith P.val M 1) := by
  obtain ⟨⟨H⟩, hH⟩ := P103.Ch11.TorExactSequences.first_sequence R A B C
    i p hi he hp L.val N.val L.property N.property M
  obtain ⟨δ, hδ⟩ := (hH H).1
  have hex := (hδ 0).2.1
  letI := hL
  letI := hN
  have hz (x : TorWith H.middle M 1) : x = 0 := by
    obtain ⟨a, ha⟩ := (hex x).mp (Subsingleton.elim _ _)
    rw [← ha, Subsingleton.elim a 0, map_zero]
  have hmid : Subsingleton (TorWith H.middle M 1) :=
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact tor_subsingleton_of_equiv ⟨H.middle, H.projective⟩ P M
    (LinearEquiv.refl Rᵐᵒᵖ B) hmid

set_option maxHeartbeats 800000 in
/-- Induction on the iterated simple extensions defining finite length. -/
theorem finite_length_vanishing : finite_length_vanishingType.{u,v,w} := by
  intro R _ _ _ k F _ _ _ _ M _ _ ek
  letI := commRightModule R k
  intro Pk hPk hk hF
  induction hF with
  | @of_subsingleton F _ _ _ =>
    letI := commRightModule R F
    intro P hP
    exact tor_subsingleton_zero (ModuleCat.of Rᵐᵒᵖ F) ⟨P, hP⟩ (ModuleCat.of R M)
  | @of_simple_quotient F _ _ N hsimple hN ih =>
    letI := commRightModule R F
    letI := commRightModule R N
    letI := commRightModule R (F ⧸ N)
    let L := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ N)
    let Q := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
      (ModuleCat.of Rᵐᵒᵖ (F ⧸ N))
    obtain ⟨e⟩ := simple_equiv_residue R (F ⧸ N)
    have hQ : Subsingleton (TorWith Q.val M 1) :=
      tor_subsingleton_of_equiv (A := ModuleCat.of Rᵐᵒᵖ k)
        (B := ModuleCat.of Rᵐᵒᵖ (F ⧸ N)) ⟨Pk, hPk⟩ Q (ModuleCat.of R M)
        (commRightEquiv (R := R) (ek.trans e.symm)) hk
    intro P hP
    exact tor_vanishing_extension (A := ModuleCat.of Rᵐᵒᵖ N)
      (B := ModuleCat.of Rᵐᵒᵖ F) (C := ModuleCat.of Rᵐᵒᵖ (F ⧸ N)) (ModuleCat.of R M)
      (commRightLinear (K := R) N.subtype) (commRightLinear (K := R) N.mkQ)
      (Submodule.injective_subtype N) (LinearMap.exact_subtype_mkQ N)
      N.mkQ_surjective L Q (ih L.val L.property) hQ ⟨P, hP⟩

/-- The same conclusion with the actual residue field in the hypothesis. -/
theorem residue_finite_length_vanishing : residue_finite_length_vanishingType.{u,w} := by
  intro R _ _ _ F _ _ M _ _
  letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
  intro Pk hPk hk hF
  exact finite_length_vanishing R (R ⧸ IsLocalRing.maximalIdeal R) F M
    (LinearEquiv.refl R _) Pk hPk hk hF

/-- The quotient is Noetherian and has nilpotent maximal ideal, hence is
Artinian. This is an equivalent proof of the finite m-power filtration. -/
theorem power_quotient_finite_length (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (j : ℕ) (hj : 1 ≤ j) :
    IsFiniteLength R (R ⧸ IsLocalRing.maximalIdeal R ^ j) := by
  let J := IsLocalRing.maximalIdeal R ^ j
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (Ideal.pow_le_self (by omega))
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  letI : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : IsNoetherianRing (R ⧸ J) := isNoetherianRing_of_surjective R (R ⧸ J)
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal (R ⧸ J)) := by
    refine ⟨j, ?_⟩
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
    exact Ideal.map_quotient_self J
  letI : IsArtinianRing (R ⧸ J) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal (R ⧸ J)).mpr hnil
  have : IsArtinian R (R ⧸ J) := isArtinian_of_surjective_algebraMap
    (Ideal.Quotient.mk_surjective (I := J))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, this⟩

theorem quotient_finite_length : quotient_finite_lengthType.{u} := by
  intro R _ _ _ I j hj
  let J := IsLocalRing.maximalIdeal R ^ j
  let K := I ⊔ J
  let f : (R ⧸ J) →ₗ[R] R ⧸ K :=
    (Ideal.Quotient.factorₐ R (show J ≤ K from le_sup_right)).toLinearMap
  exact (power_quotient_finite_length R j hj).of_surjective
    (f := f) (Ideal.Quotient.factor_surjective (show J ≤ K from le_sup_right))

theorem quotient_vanishing : quotient_vanishingType.{u,w} := by
  intro R _ _ _ M _ _
  letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
  intro Pk hPk hk I j hj
  exact finite_length_vanishing R (R ⧸ IsLocalRing.maximalIdeal R)
    (R ⧸ (I ⊔ IsLocalRing.maximalIdeal R ^ j)) M (LinearEquiv.refl R _) Pk hPk hk
    (quotient_finite_length R I j hj)

end
end P103.Ch12.FiniteLengthTorVanishing
