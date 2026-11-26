import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! The formal base and compatible objects in the forward direction of Theorem 6.9. -/

universe u w

namespace CommutativeAlgebraNotes.SchlessingerCandidateSpec

open CategoryTheory LocalArtinAlgebra SchlessingerConditionsSpec
  SchlessingerTangentVectorSpaceSpec IsLocalRing
open scoped TensorProduct

noncomputable section

abbrev Series (k : Type u) [Field k] (r : ℕ) := MvPowerSeries (Fin r) k

def seriesResidue (k : Type u) [Field k] (r : ℕ) : Series k r →ₐ[k] k where
  __ := MvPowerSeries.constantCoeff
  commutes' c := MvPowerSeries.constantCoeff_C c

instance (k : Type u) [Field k] (r : ℕ) : IsLocalHom (seriesResidue k r) :=
  ⟨fun _ h => MvPowerSeries.isUnit_iff_constantCoeff.mpr h⟩

section Quotients

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]
  [IsLocalRing S] [IsNoetherianRing S]

abbrev quotientNontrivial (I : Ideal S) (hI : I ≤ maximalIdeal S) : Nontrivial (S ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hI)

abbrev quotientLocal (I : Ideal S) (hI : I ≤ maximalIdeal S) : IsLocalRing (S ⧸ I) :=
  letI := quotientNontrivial I hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

omit [IsNoetherianRing S] in
theorem ker_eq_maximal (ρ : S →ₐ[k] k) [IsLocalHom ρ] :
    RingHom.ker ρ = maximalIdeal S := by
  ext a
  rw [RingHom.mem_ker, mem_maximalIdeal, mem_nonunits_iff,
    ← isUnit_map_iff ρ a, isUnit_iff_ne_zero, not_not]

def quotientResidue (ρ : S →ₐ[k] k) [IsLocalHom ρ] (I : Ideal S) (hI : I ≤ maximalIdeal S) :
    (S ⧸ I) →ₐ[k] k :=
  Ideal.Quotient.liftₐ I ρ (fun _ ha => RingHom.mem_ker.mp ((ker_eq_maximal ρ).symm ▸ hI ha))

instance (ρ : S →ₐ[k] k) [IsLocalHom ρ] (I : Ideal S) (hI : I ≤ maximalIdeal S) :
    IsLocalHom (quotientResidue ρ I hI) := by
  constructor
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (IsUnit.of_map ρ a hx).map (Ideal.Quotient.mk I)

def artinQuotient (ρ : S →ₐ[k] k) [IsLocalHom ρ] (I : Ideal S) (hI : I ≤ maximalIdeal S)
    (hp : ∃ q : ℕ, maximalIdeal S ^ q ≤ I) : LocalArtinAlgebra.{u,u} k :=
  letI := quotientNontrivial I hI
  letI := quotientLocal I hI
  letI : IsArtinianRing (S ⧸ I) := (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr (by
    obtain ⟨q, hq⟩ := hp
    refine ⟨q, ?_⟩
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hq)
  { carrier := S ⧸ I, residue := quotientResidue ρ I hI }

abbrev artinTransition (ρ : S →ₐ[k] k) [IsLocalHom ρ] {I K : Ideal S}
    {hI : I ≤ maximalIdeal S} {hK : K ≤ maximalIdeal S}
    {pI : ∃ q : ℕ, maximalIdeal S ^ q ≤ I} {pK : ∃ q : ℕ, maximalIdeal S ^ q ≤ K}
    (h : I ≤ K) : Hom (artinQuotient ρ I hI pI) (artinQuotient ρ K hK pK) :=
  letI := quotientNontrivial K hK
  letI := quotientLocal I hI
  ⟨Ideal.Quotient.factorₐ k h,
    ⟨(IsLocalHom.of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)).map_nonunit⟩⟩

def completeQuotient (ρ : S →ₐ[k] k) [IsLocalHom ρ] (I : Ideal S) (hI : I ≤ maximalIdeal S)
    (hc : letI := quotientLocal I hI; IsAdicComplete (maximalIdeal (S ⧸ I)) (S ⧸ I)) :
    CompleteLocalAlgebraModel k :=
  letI := quotientLocal I hI
  { carrier := S ⧸ I, residue := quotientResidue ρ I hI, complete := hc }

abbrev toArtinQuotient (ρ : S →ₐ[k] k) [IsLocalHom ρ] {I K : Ideal S}
    {hI : I ≤ maximalIdeal S} {hK : K ≤ maximalIdeal S}
    {hc : letI := quotientLocal I hI; IsAdicComplete (maximalIdeal (S ⧸ I)) (S ⧸ I)}
    {pK : ∃ q : ℕ, maximalIdeal S ^ q ≤ K} (h : I ≤ K) :
    CompleteLocalAlgebra.Hom (completeQuotient ρ I hI hc) (artinQuotient ρ K hK pK) :=
  letI := quotientNontrivial K hK
  letI := quotientLocal I hI
  ⟨Ideal.Quotient.factorₐ k h,
    ⟨(IsLocalHom.of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)).map_nonunit⟩⟩

end Quotients

/-- The stage indexed by i corresponds to the source's i + 2. -/
structure Tower {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k) (r : ℕ) where
  ideal : ℕ → Ideal (Series k r)
  below : ∀ i, ideal i ≤ maximalIdeal (Series k r)
  power : ∀ i, maximalIdeal (Series k r) ^ (i + 2) ≤ ideal i
  decreasing : Antitone ideal
  first : ideal 0 = maximalIdeal (Series k r) ^ 2
  element : ∀ i, F.toFunctor.obj (artinQuotient (seriesResidue k r) (ideal i) (below i)
    ⟨i + 2, power i⟩)
  compatible : ∀ {i j} (h : i ≤ j),
    F.toFunctor.map (artinTransition (seriesResidue k r) (decreasing h)) (element j) = element i
  mul_le : ∀ i, maximalIdeal (Series k r) * ideal i ≤ ideal (i + 1)
  least : ∀ i (K : Ideal (Series k r)) (hK : K ≤ ideal i)
    (pK : ∃ q : ℕ, maximalIdeal (Series k r) ^ q ≤ K),
    maximalIdeal (Series k r) * ideal i ≤ K →
    (∃ y : F.toFunctor.obj (artinQuotient (seriesResidue k r) K (hK.trans (below i)) pK),
      F.toFunctor.map (artinTransition (seriesResidue k r) hK) y = element i) →
    ideal (i + 1) ≤ K

namespace Tower

variable {k : Type u} [Field k] {F : ArtinFunctorModel.{u,w} k} {r : ℕ} (T : Tower F r)

abbrev stage (i : ℕ) : LocalArtinAlgebra.{u,u} k :=
  artinQuotient (seriesResidue k r) (T.ideal i) (T.below i) ⟨i + 2, T.power i⟩

abbrev limitIdeal : Ideal (Series k r) := ⨅ i, T.ideal i

theorem limit_le (i : ℕ) : T.limitIdeal ≤ T.ideal i := iInf_le _ i

abbrev ring (hc : letI := quotientLocal T.limitIdeal ((T.limit_le 0).trans (T.below 0))
    IsAdicComplete (maximalIdeal (Series k r ⧸ T.limitIdeal)) (Series k r ⧸ T.limitIdeal)) :
    CompleteLocalAlgebraModel k :=
  completeQuotient (seriesResidue k r) T.limitIdeal ((T.limit_le 0).trans (T.below 0)) hc

abbrev projection {hc : letI := quotientLocal T.limitIdeal ((T.limit_le 0).trans (T.below 0))
    IsAdicComplete (maximalIdeal (Series k r ⧸ T.limitIdeal)) (Series k r ⧸ T.limitIdeal)}
    (i : ℕ) : CompleteLocalAlgebra.Hom (T.ring hc) (T.stage i) :=
  toArtinQuotient (seriesResidue k r) (T.limit_le i)

end Tower

/-- In a complete Noetherian local ring the images of descending ideals in an
Artin truncation eventually coincide with the image of their intersection. -/
def StableImages : Prop :=
  ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (maximalIdeal S) S] (J : ℕ → Ideal S), Antitone J →
    ∀ q : ℕ, ∃ N : ℕ, ∀ j ≥ N,
      (J j).map (Ideal.Quotient.mk (maximalIdeal S ^ q)) =
        (⨅ i, J i).map (Ideal.Quotient.mk (maximalIdeal S ^ q))

/-- The tower, its first-order class, and its induced map out of the actual quotient
by the intersection. The evaluation formula applies through every stage through
which a local map factors. -/
def Construction : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k),
    H1Model F → H2Model F → H3Model F →
    ∃ laws : VectorLaws F,
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    let r := Module.finrank k (TangentModel F)
    let V := Fin r → k
    ∃ (b : Module.Basis (Fin r) k (TangentModel F)) (T : Tower F r)
      (jet : Hom (T.stage 0) (splitModel k V)) (e : SplitTensorComparison F laws V),
      Function.Bijective jet ∧
      (∀ i : Fin r, jet (Ideal.Quotient.mk (T.ideal 0) (MvPowerSeries.X i)) =
        TrivSqZeroExt.inr (Pi.basisFun k (Fin r) i)) ∧
      e.equiv (F.toFunctor.map jet (T.element 0)) =
        ∑ i : Fin r, b i ⊗ₜ[k] (Pi.basisFun k (Fin r) i) ∧
      ∃ (hc : letI := quotientLocal T.limitIdeal ((T.limit_le 0).trans (T.below 0))
              IsAdicComplete (maximalIdeal (Series k r ⧸ T.limitIdeal)) (Series k r ⧸ T.limitIdeal))
        (τ : (representableModel.{u,w} (T.ring hc)).toFunctor ⟶ F.toFunctor),
        (∀ q : ℕ, ∃ i : ℕ, (T.ideal i).map (Ideal.Quotient.mk T.limitIdeal) ≤
          maximalIdeal (T.ring hc) ^ q) ∧
        (∀ i : ℕ, maximalIdeal (T.ring hc) ^ (i + 2) ≤
          (T.ideal i).map (Ideal.Quotient.mk T.limitIdeal)) ∧
        (∀ (A : LocalArtinAlgebra.{u,u} k) (f : CompleteLocalAlgebra.Hom (T.ring hc) A),
          ∃ (i : ℕ) (g : Hom (T.stage i) A), (T.projection i).postcomp g = f) ∧
        (∀ (A : LocalArtinAlgebra.{u,u} k) (i : ℕ) (g : Hom (T.stage i) A),
          τ.app A (ULift.up ((T.projection i).postcomp g)) =
            F.toFunctor.map g (T.element i)) ∧
        Function.Bijective ((τ.app (dualModel k)) :
          TangentModel (representableModel.{u,w} (T.ring hc)) → TangentModel F)

end

end CommutativeAlgebraNotes.SchlessingerCandidateSpec
