import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.KummerObstructions

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.TorusFibreKummerRealization

open CentralCover CentralCoverSpreading IntegralCentralQuotient
open LinearAlgebraicGroups.Arithmetic.Kummer

noncomputable section

/-- Reduction of the marked torus lattice modulo the power exponents. -/
def reduceCharacters {I : Type} (n : I → ℕ) :
    ULift.{u} (Multiplicative (I → ℤ)) →* ULift.{u} (∀ i, Characters (n i)) where
  toFun x := ⟨fun i => Multiplicative.ofAdd (x.down.toAdd i : ZMod (n i))⟩
  map_one' := by
    apply ULift.ext
    funext i
    change Multiplicative.ofAdd ((0 : ℤ) : ZMod (n i)) = 1
    rw [Int.cast_zero, ofAdd_zero]
  map_mul' x y := by
    apply ULift.ext
    funext i
    change Multiplicative.ofAdd ((x.down.toAdd i + y.down.toAdd i : ℤ) : ZMod (n i)) =
      Multiplicative.ofAdd (x.down.toAdd i : ZMod (n i)) *
        Multiplicative.ofAdd (y.down.toAdd i : ZMod (n i))
    rw [Int.cast_add, ofAdd_add]

/-- The standard kernel inclusion into the source torus. -/
abbrev kernelIntoTorus (R : Type u) [CommRing R] {I : Type} (n : I → ℕ) :
    integralRootsOfUnityProduct R n ⟶ integralSplitTorus R I :=
  spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R (reduceCharacters n))

/-- The character of the indicated Smith coordinate on either marked torus. -/
def torusCharacter {I : Type} (i : I) : ULift.{u} (Multiplicative (I → ℤ)) := by
  classical
  exact ⟨Multiplicative.ofAdd (Pi.single i 1)⟩

/-- The integral kernel can be identified by the marked source torus.
For every presentation of the resulting cover, a target torus point
with the prescribed unit coordinates realizes their classes simultaneously. -/
def Statement : Prop :=
  ∀ {R E : Type u} [CommRing R] [IsDomain R] [Field E] [Algebra R E] [IsFractionRing R E]
    {G H : AffineAlgebraicGroup E} {q : H.val ⟶ G.val} {N : ClosedSubgroup H.val}
    {T : SplitCoverData G H q N} {m : ℕ} {j : MatrixEmbedding G m}
    (M : IntegralModel (R := R) T j),
    ∃ eZ : M.kernel.val ≅ integralRootsOfUnityProduct R T.exponents,
      eZ.inv ≫ M.kernelInclusion =
        kernelIntoTorus R T.exponents ≫ M.splitSourceTorus.inv ≫ M.sourceTorusInclusion ∧
      ∀ {B A : Type u} [CommRing B] [CommRing A] [HopfAlgebra R B] [HopfAlgebra R A]
        (eG : HopfSpectrum R B ≅ M.target.val) (eH : HopfSpectrum R A ≅ M.source.val)
        (q₀ : B →ₐc[R] A) (π : A →ₐc[R] KernelCoordinates R T.exponents),
        spectrumOfHopfHom q₀ ≫ eG.hom = eH.hom ≫ M.map →
        spectrumOfHopfHom π ≫ eH.hom = eZ.inv ≫ M.kernelInclusion →
        IsRightTorsor q₀ π →
        ∃ s : B →ₐc[R] TorusCoordinates R T.indices,
          spectrumOfHopfHom s ≫ eG.hom = M.splitTargetTorus.inv ≫ M.targetTorusInclusion ∧
          ∀ {V : Type u} [CommRing V] [Algebra R V] [IsLocalRing V] (a : T.indices → Vˣ),
            ∃ (t : TorusCoordinates R T.indices →ₐ[R] V) (p : B →ₐ[R] V),
              (∀ i, t (MonoidAlgebra.of R _ (torusCharacter i)) = (a i : V)) ∧
              p = t.comp s.toAlgHom ∧
              letI : Algebra B A := q₀.toAlgHom.toAlgebra
              ∀ i, PullbackHasClass T.exponents π p i (classOf (T.exponents i) (a i))

end

end LinearAlgebraicGroups.Specs.TorusFibreKummerRealization
