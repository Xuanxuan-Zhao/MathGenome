import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.AugmentedCechComplex
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

open CategoryTheory

namespace Specs.CommutativeAlgebraNotes.PowerSeriesLocalCohomology

universe u

abbrev Series (k : Type u) [Field k] (d : ℕ) := MvPowerSeries (Fin d) k

variable (k : Type u) [Field k] (d : ℕ)

/-- The denominator of the top term of the Čech complex. -/
noncomputable abbrev fullProduct : Series k d := ∏ i : Fin d, MvPowerSeries.X i

/-- The denominator in the summand indexed by the face missing variable `j`. -/
noncomputable abbrev faceProduct (j : Fin d) : Series k d :=
  ∏ i ∈ Finset.univ.erase j, MvPowerSeries.X i

theorem variable_mul_faceProduct (j : Fin d) :
    MvPowerSeries.X j * faceProduct k d j = fullProduct k d :=
  Finset.mul_prod_erase _ _ (Finset.mem_univ j)

noncomputable abbrev faceMap (j : Fin d) :
    Localization.Away (faceProduct k d j) →ₐ[Series k d] Localization.Away (fullProduct k d) :=
  AugmentedCechComplex.localizationMap _ _ _
    ⟨MvPowerSeries.X j, by rw [mul_comm, variable_mul_faceProduct]⟩

/-- The sum of the images of the Čech face localizations. -/
noncomputable abbrev faceImages : Submodule (Series k d) (Localization.Away (fullProduct k d)) :=
  ⨆ j : Fin d, LinearMap.range (faceMap k d j).toLinearMap

/-- A principal-localization fraction with denominator `p^N`. -/
def fraction {S : Type u} [CommRing S] (p : S) (N : ℕ) (f : S) : Localization.Away p :=
  Localization.mk f ⟨p ^ N, ⟨N, rfl⟩⟩

/-- Indices store the positive inverse exponents minus one. -/
abbrev Index (d : ℕ) := Fin d → ℕ

/-- The element with monomial expression `∏ i, X i ^ (-(a i + 1))`. -/
noncomputable abbrev inverseMonomial (a : Index d) : Localization.Away (fullProduct k d) :=
  let N := Finset.univ.sup a + 1
  fraction (fullProduct k d) N
    (MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm (fun i => N - (a i + 1))) 1)

/-- The top local cohomology of the power series ring with its own coefficients. -/
noncomputable abbrev top : ModuleCat.{u} (Series k d) :=
  (IdealTorsion.localCohomology.{u} (IsLocalRing.maximalIdeal (Series k d)) (d : ℤ)).obj
    (ModuleCat.of (Series k d) (Series k d))

/-- The field action is restriction along the inclusion of constant series. -/
noncomputable abbrev topOverField : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (algebraMap k (Series k d))).obj (top k d)

/-- The top local cohomology is the Čech quotient, and the specified inverse
monomials give a basis under this quotient comparison. -/
def InverseMonomialBasis : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ),
    ∃ π : ModuleCat.of (Series k d) (Localization.Away (fullProduct k d)) ⟶ top k d,
      Function.Surjective π ∧ π.hom.ker = faceImages k d ∧
        ∃ b : Module.Basis (Index d) k (topOverField k d),
          ∀ a, b a = π (inverseMonomial k d a)

/-- The top cohomology is isomorphic over the power series ring to the
injective envelope of its residue field. -/
def TopIsInjectiveEnvelope : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ)
    (E : _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs.residueFieldEnvelopeValue (Series k d)),
    Nonempty (top k d ≅ ModuleCat.of (Series k d) E.carrier)

end Specs.CommutativeAlgebraNotes.PowerSeriesLocalCohomology
