import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsHomology
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsCohomology
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ArbitraryRankPIDSubmodules

/-! Splittings in paper.tex 2947–2952 and 3010–3032. The degree-zero
statements encode H₋₁ = 0 separately. No naturality in the complex, or
canonical choice of boundary sections, is asserted. -/
namespace P103.Specs.Ch11.UniversalCoefficientsSplitting
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
namespace H
export P103.Specs.Ch11.UniversalCoefficientsHomology
  (Complex FlatTermsAndBoundaries PositiveSequence ZeroSequence UniversalCoefficients
   jTensor shiftedBoundaryTerms)
end H
namespace Q
export P103.Specs.Ch11.UniversalCoefficientsCohomology
  (Ordinary previousBoundary boundaryProjection ProjectiveTermsAndBoundaries
   IsRestriction IsExtCoker CokerSequence BoundaryCoker j)
end Q
noncomputable section
universe u v w

/-- Chosen linear sections of all boundary projections, including B₋₁ = 0. -/
structure BoundarySections {R : Type u} [Ring R] (C : Q.Ordinary.{u,v} R) where
  s : ∀ n, Q.previousBoundary C n →ₗ[R] C.X n
  right_inv : ∀ n, (Q.boundaryProjection C n).comp (s n) = LinearMap.id

def boundary_sectionsType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Q.Ordinary.{u,v} R),
    (∀ n, Module.Projective R (boundaries C n)) → Nonempty (BoundarySections C)

/-- The differential in the coordinates determined by the chosen sections. -/
def coordinatesType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Q.Ordinary.{u,v} R) (S : BoundarySections C),
    ∃ e : ∀ n, (cycles C n × Q.previousBoundary C n) ≃ₗ[R] C.X n,
      (∀ n z b, e n (z,b) = z.val + S.s n b) ∧
      ∀ n z b, (e n).symm ((C.d (n+1) n).hom (e (n+1) (z,b))) =
        (Q.j C n b, 0)

/-- The section lifts the actual Tor/kernel representative by the given s.
It is a section of the prescribed UCT β, for every permitted UCT sequence. -/
def homology_splittingType : Prop :=
  ∀ {R : Type u} [Ring R] (C : H.Complex.{u,v} R),
    H.FlatTermsAndBoundaries.{u,v,w} C → ∀ (S : BoundarySections C)
    (M : ModuleCat.{w} R) (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n)))
    (U : H.PositiveSequence C M n P),
    ∃ σ : TorWith P.val M 1 →ₗ[ℤ] Homology (tensorComplex C M) (n+1),
      U.β.comp σ = LinearMap.id ∧
      ∀ x, ∃ z : cycles (tensorComplex C M) (n+1),
        z.val = tensorMap (S.s (n+1)) (LinearMap.id : M →ₗ[R] M)
          (U.kernelIso x).val ∧ σ x = homologyClass _ (n+1) z

def homology_zero_splittingType : Prop :=
  ∀ {R : Type u} [Ring R] (C : H.Complex.{u,v} R) (M : ModuleCat.{w} R)
    (U : H.ZeroSequence C M) (P : ProjectiveChoice Rᵐᵒᵖ (H.shiftedBoundaryTerms C 0)),
    (∃ r : Homology (tensorComplex C M) 0 →ₗ[ℤ] Tensor R (Homology C 0) M,
      r.comp U.α = LinearMap.id) ∧
    ∃ σ : TorWith P.val M 1 →ₗ[ℤ] Homology (tensorComplex C M) 0,
      (U.β P).comp σ = LinearMap.id

/-- Projective boundaries suffice for the additional homological splitting
hypothesis; existence of the genuine UCT sequences is included. -/
def homology_projectiveType : Prop :=
  ∀ {R : Type u} [Ring R] (C : H.Complex.{u,v} R),
    H.FlatTermsAndBoundaries.{u,v,w} C →
    (∀ n, Module.Projective Rᵐᵒᵖ (boundaries C n)) →
    ∃ S : BoundarySections C, ∀ (M : ModuleCat.{w} R) (n : ℕ)
      (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n))),
      ∃ (U : H.PositiveSequence C M n P)
        (σ : TorWith P.val M 1 →ₗ[ℤ] Homology (tensorComplex C M) (n+1)),
        U.β.comp σ = LinearMap.id

/-- In coordinates, extend a functional on Hₙ by zero on Bₙ₋₁.
This fixes a genuine section of every map with the UCT restriction formula,
including degree zero. -/
def cohomology_splittingType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Q.Ordinary.{u,v} R) (S : BoundarySections C)
    (M : ModuleCat.{w} R) (n : ℕ)
    (β : Homology (homComplex C M) n →ₗ[ℤ] (Homology C n →ₗ[R] M)),
    Q.IsRestriction C M n β →
    ∃ σ : (Homology C n →ₗ[R] M) →ₗ[ℤ] Homology (homComplex C M) n,
      β.comp σ = LinearMap.id ∧
      ∀ h, ∃ z : cycles (homComplex C M) n,
        σ h = homologyClass _ n z ∧
        ∀ (a : cycles C n) (b : Q.previousBoundary C n),
          P103.Specs.Ch11.UniversalCoefficientsCohomology.homTerm C M n z.val
            (a.val + S.s n b) = h (homologyClass C n a)

/-- The actual Ext/Hom short exact sequence together with a right section. -/
def cohomology_projectiveType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Q.Ordinary.{u,v} R),
    Q.ProjectiveTermsAndBoundaries C → ∀ (S : BoundarySections C)
    (M : ModuleCat.{w} R) (n : ℕ) (N : LeftResolution R (Homology C n)),
    N.IsProjective →
    ∃ (e : ExtWith N M 1 ≃ₗ[ℤ] Q.BoundaryCoker C M n)
      (α : Q.BoundaryCoker C M n →ₗ[ℤ] Homology (homComplex C M) (n+1))
      (β : Homology (homComplex C M) (n+1) →ₗ[ℤ] (Homology C (n+1) →ₗ[R] M))
      (σ : (Homology C (n+1) →ₗ[R] M) →ₗ[ℤ] Homology (homComplex C M) (n+1)),
      Q.IsExtCoker C M n N e ∧ Q.CokerSequence C M n α β ∧
      Function.Injective (α.comp e.toLinearMap) ∧
      Function.Exact (α.comp e.toLinearMap) β ∧ Function.Surjective β ∧
      β.comp σ = LinearMap.id

/-- No finite generation or finite rank assumption. -/
def pid_freeType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : Q.Ordinary.{u,v} R), (∀ n, Module.Free R (C.X n)) →
    ∀ n, Module.Free R (cycles C n) ∧ Module.Free R (boundaries C n)

def pid_homologyType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : H.Complex.{u,v} R), (∀ n, Module.Free Rᵐᵒᵖ (C.X n)) →
    H.FlatTermsAndBoundaries.{u,v,w} C ∧
    ∃ S : BoundarySections C, ∀ M : ModuleCat.{w} R,
      Nonempty (H.ZeroSequence C M) ∧ ∀ (n : ℕ)
      (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n))),
      ∃ (U : H.PositiveSequence C M n P)
        (σ : TorWith P.val M 1 →ₗ[ℤ] Homology (tensorComplex C M) (n+1)),
        U.β.comp σ = LinearMap.id

def pid_cohomologyType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : Q.Ordinary.{u,v} R), (∀ n, Module.Free R (C.X n)) →
    Q.ProjectiveTermsAndBoundaries C ∧ Nonempty (BoundarySections C)

/-- These equations are linearity for the usual coefficient-induced scalar
 actions, with the established Tor module action. Degree zero is explicit. -/
def homology_scalar_splittingType : Prop :=
  ∀ {K : Type u} [CommRing K] (U : H.UniversalCoefficients.{u,v,w} K)
    (C : H.Complex.{u,v} K) (hC : H.FlatTermsAndBoundaries.{u,v,w} C)
    (S : BoundarySections C) (M : ModuleCat.{w} K),
    (∃ ρ : Homology (tensorComplex C M) 0 →ₗ[ℤ] Tensor K (Homology C 0) M,
      ρ.comp (U.zero C hC M).α = LinearMap.id ∧
      ∀ r x, ρ (homologyMap (tensorSecondMap C (scalarMap M r).hom) 0 x) =
        tensorMap LinearMap.id (scalarMap M r).hom (ρ x)) ∧
    ∀ (n : ℕ) (P : ProjectiveChoice Kᵐᵒᵖ (ModuleCat.of Kᵐᵒᵖ (Homology C n)))
      (T : TorMaps.{u,v,w} K 1),
      letI := torModule T P M
      ∃ σ : TorWith P.val M 1 →ₗ[ℤ] Homology (tensorComplex C M) (n+1),
        (U.positive C hC M n P).β.comp σ = LinearMap.id ∧
        ∀ r x, σ (r • x) =
          homologyMap (tensorSecondMap C (scalarMap M r).hom) (n+1) (σ x)

/-- Linearity of the chosen cohomological section, including degree zero,
for the upstream canonical coefficient module structure. -/
def cohomology_scalar_splittingType : Prop :=
  ∀ {K : Type u} [CommRing K] (C : Q.Ordinary.{u,v} K) (S : BoundarySections C)
    (M : ModuleCat.{w} K) (n : ℕ)
    (β : Homology (homComplex C M) n →ₗ[ℤ] (Homology C n →ₗ[K] M)),
    Q.IsRestriction C M n β →
    letI := P103.Specs.Ch11.UniversalCoefficientsCohomology.cohomologyModule C M n
    ∃ σ : (Homology C n →ₗ[K] M) →ₗ[K] Homology (homComplex C M) n,
      β.comp (σ.restrictScalars ℤ) = LinearMap.id

/-- The complete positive-degree Ext/Hom UCT sequence with a right section. -/
def SplitExtSequence {R : Type u} [Ring R] (C : Q.Ordinary.{u,v} R)
    (M : ModuleCat.{w} R) (n : ℕ) (N : LeftResolution R (Homology C n)) : Prop :=
  ∃ (e : ExtWith N M 1 ≃ₗ[ℤ] Q.BoundaryCoker C M n)
    (α : Q.BoundaryCoker C M n →ₗ[ℤ] Homology (homComplex C M) (n+1))
    (β : Homology (homComplex C M) (n+1) →ₗ[ℤ] (Homology C (n+1) →ₗ[R] M))
    (σ : (Homology C (n+1) →ₗ[R] M) →ₗ[ℤ] Homology (homComplex C M) (n+1)),
    Q.IsExtCoker C M n N e ∧ Q.CokerSequence C M n α β ∧
    Function.Injective (α.comp e.toLinearMap) ∧
    Function.Exact (α.comp e.toLinearMap) β ∧ Function.Surjective β ∧
    β.comp σ = LinearMap.id

/-- Both endpoints and every positive degree, specialized to arbitrary-rank
free complexes over a PID. Scalar linearity follows from the scalar splitting
theorems above for the same sections. -/
def pid_cohomology_sequencesType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : Q.Ordinary.{u,v} R), (∀ n, Module.Free R (C.X n)) →
    ∃ S : BoundarySections C,
      (∀ M : ModuleCat.{w} R,
        ∃ e : Homology (homComplex C M) 0 ≃ₗ[ℤ] (Homology C 0 →ₗ[R] M),
          Q.IsRestriction C M 0 e.toLinearMap ∧
          ∃ σ : (Homology C 0 →ₗ[R] M) →ₗ[ℤ] Homology (homComplex C M) 0,
            e.toLinearMap.comp σ = LinearMap.id) ∧
      ∀ (M : ModuleCat.{w} R) (n : ℕ) (N : LeftResolution R (Homology C n)),
        N.IsProjective → SplitExtSequence C M n N

end
end P103.Specs.Ch11.UniversalCoefficientsSplitting
