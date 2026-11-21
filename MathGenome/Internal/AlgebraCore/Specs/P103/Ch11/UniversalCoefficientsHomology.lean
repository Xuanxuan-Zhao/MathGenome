import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.DimensionShifting

/-!
Homology universal coefficients, paper.tex 2926–2938 and 2954–2987.
The ring is arbitrary, associative and unital, and the complex is ordinary
nonnegative. Homology and tensor products are the upstream explicit quotients.
Both terms and boundaries are flat. No boundary projection is assumed split.
The zero-degree isomorphism and the positive-degree sequences together cover
all n ≥ 0, with H₋₁ = B₋₁ = 0. Naturality is simultaneous in both variables
and in the choice of projective model for the Tor term.
-/
namespace P103.Specs.Ch11.UniversalCoefficientsHomology
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence P103.Specs.Ch10.Horseshoe
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch02.FlatnessTests
noncomputable section
universe u v w
variable {R : Type u} [Ring R]

abbrev Complex (R : Type u) [Ring R] := ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ

/-- Exactly the two flatness assumptions of the source. -/
def FlatTermsAndBoundaries (C : Complex.{u,v} R) : Prop :=
  (∀ n, RightFlat.{u,v,w} R (C.X n)) ∧
  (∀ n, RightFlat.{u,v,w} R (boundaries C n))

/-- A graded module with all differentials zero. -/
abbrev zeroDifferentialComplex (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ) : Complex R where
  X := X
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

abbrev cycleTerms (C : Complex.{u,v} R) (n : ℕ) : ModuleCat.{v} Rᵐᵒᵖ :=
  ModuleCat.of Rᵐᵒᵖ (cycles C n)

/-- L₀ = B₋₁ = 0, and Lₙ₊₁ = Bₙ. The bottom submodule is an actual
zero module in the same universe, including when the ring is zero. -/
abbrev shiftedBoundaryTerms (C : Complex.{u,v} R) : ℕ → ModuleCat.{v} Rᵐᵒᵖ
  | 0 => ModuleCat.of Rᵐᵒᵖ (↥(⊥ : Submodule Rᵐᵒᵖ (C.X 0)))
  | n+1 => ModuleCat.of Rᵐᵒᵖ (boundaries C n)

abbrev cycleComplex (C : Complex.{u,v} R) := zeroDifferentialComplex (cycleTerms C)
abbrev shiftedBoundaryComplex (C : Complex.{u,v} R) :=
  zeroDifferentialComplex (shiftedBoundaryTerms C)

/-- The actual inclusion jₙ : Bₙ → Zₙ. -/
def boundaryToCycles (C : Complex.{u,v} R) (n : ℕ) :
    boundaries C n →ₗ[Rᵐᵒᵖ] cycles C n :=
  Submodule.inclusion (boundaryInclusion C n)

/-- Differential with codomain restricted to its image, also at degree zero. -/
def boundaryProjectionTerm (C : Complex.{u,v} R) :
    ∀ n, C.X n →ₗ[Rᵐᵒᵖ] shiftedBoundaryTerms C n
  | 0 => 0
  | n+1 => (C.d (n+1) n).hom.codRestrict (boundaries C n) (by
      intro x
      change ∃ y, (C.d ((ComplexShape.down ℕ).prev n) n).hom y = _
      rw [ChainComplex.prev]
      exact ⟨x, rfl⟩)

def cycleInclusion (C : Complex.{u,v} R) : cycleComplex C ⟶ C where
  f n := ModuleCat.ofHom (cycles C n).subtype
  comm' n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (C.d n m).hom x.val = 0
    have hx := x.property
    change (C.d n ((ComplexShape.down ℕ).next n)).hom x.val = 0 at hx
    rwa [(ComplexShape.down ℕ).next_eq' h] at hx

def boundaryProjection (C : Complex.{u,v} R) : C ⟶ shiftedBoundaryComplex C where
  f n := ModuleCat.ofHom (boundaryProjectionTerm C n)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases m with
    | zero => rfl
    | succ m =>
      apply Subtype.ext
      change 0 = (C.d (m+1) m).hom ((C.d n (m+1)).hom x)
      have hh := congrArg ModuleCat.Hom.hom (C.d_comp_d n (m+1) m)
      exact (DFunLike.congr_fun hh x).symm

/-- The tensor of a zero-differential complex again has zero differential. -/
theorem tensorZero_d (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (M : ModuleCat.{w} R) (n m : ℕ) :
    (tensorComplex (zeroDifferentialComplex X) M).d n m = 0 := by
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  change tmul R 0 b = 0
  simp [tmul]

/-- Every tensor is a cycle in a tensored zero-differential complex. -/
def tensorZeroCycle (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (M : ModuleCat.{w} R) (n : ℕ) :
    Tensor R (X n) M →ₗ[ℤ] cycles (tensorComplex (zeroDifferentialComplex X) M) n :=
  LinearMap.id.codRestrict (cycles _ n) (by
    intro x
    change (tensorComplex (zeroDifferentialComplex X) M).d n
      ((ComplexShape.down ℕ).next n) x = 0
    rw [tensorZero_d]
    rfl)

/-- Canonical class map for a tensored zero-differential complex. -/
def tensorZeroClass (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (M : ModuleCat.{w} R) (n : ℕ) :
    Tensor R (X n) M →ₗ[ℤ] Homology (tensorComplex (zeroDifferentialComplex X) M) n :=
  (homologyClass _ n).comp (tensorZeroCycle X M n)

/-- The tensor of a cycle is a cycle, with no exactness assumption. -/
def tensorCycle (C : Complex.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ)
    (z : cycles C n) (m : M) : cycles (tensorComplex C M) n :=
  ⟨tmul R z.val m, by
    change tmul R ((C.d n ((ComplexShape.down ℕ).next n)).hom z.val) m = 0
    rw [show (C.d n ((ComplexShape.down ℕ).next n)).hom z.val = 0 from z.property]
    simp [tmul]⟩

abbrev jTensor (C : Complex.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ) :=
  tensorMap (boundaryToCycles C n) (LinearMap.id : M →ₗ[R] M)

/-- Normalization of the Tor₁/kernel isomorphism by the positive Tor
connecting map for 0 → Bₙ → Zₙ → Hₙ → 0. No arbitrary automorphism of Tor
is permitted. All projective models are allowed. -/
def TorKernelIdentification (C : Complex.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n)))
    (e : TorWith P.val M 1 ≃ₗ[ℤ] LinearMap.ker (jTensor C M n)) : Prop :=
  ∃ (L : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (boundaries C n)))
    (H : ProjectiveData (boundaryToCycles C n) (homologyClass C n) L.val P.val)
    (δ : TorWith P.val M 1 →ₗ[ℤ] TorWith L.val M 0)
    (z : TorWith L.val M 0 ≃+ Tensor R (boundaries C n) M),
    Connecting (tensorFirstMap H.inclusion M) (tensorFirstMap H.projection M) 1 0 δ ∧
    (∀ a, z (homologyClass _ 0 a) = tensorMap L.val.ε LinearMap.id a.val) ∧
    ∀ x, (e x).val = z (δ x)

/-- A complete sequence in degree n+1, including the two prescribed maps. -/
structure PositiveSequence (C : Complex.{u,v} R) (M : ModuleCat.{w} R) (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n))) where
  α : Tensor R (Homology C (n+1)) M →ₗ[ℤ] Homology (tensorComplex C M) (n+1)
  β : Homology (tensorComplex C M) (n+1) →ₗ[ℤ] TorWith P.val M 1
  injective_α : Function.Injective α
  exact : Function.Exact α β
  surjective_β : Function.Surjective β
  α_formula : ∀ (z : cycles C (n+1)) (m : M),
    α (tmul R (homologyClass C (n+1) z) m) =
      homologyClass (tensorComplex C M) (n+1) (tensorCycle C M (n+1) z m)
  kernelIso : TorWith P.val M 1 ≃ₗ[ℤ] LinearMap.ker (jTensor C M n)
  kernelIso_canonical : TorKernelIdentification C M n P kernelIso
  β_formula : ∀ x,
    tensorZeroClass (shiftedBoundaryTerms C) M (n+1) (kernelIso (β x)).val =
      homologyMap (tensorFirstMap (boundaryProjection C) M) (n+1) x

/-- Degree zero: the Tor₁(H₋₁,M) endpoint is zero. -/
structure ZeroSequence (C : Complex.{u,v} R) (M : ModuleCat.{w} R) where
  α : Tensor R (Homology C 0) M →ₗ[ℤ] Homology (tensorComplex C M) 0
  bijective_α : Function.Bijective α
  α_formula : ∀ (z : cycles C 0) (m : M),
    α (tmul R (homologyClass C 0 z) m) =
      homologyClass (tensorComplex C M) 0 (tensorCycle C M 0 z m)
  zero_tor : ∀ P : ProjectiveChoice Rᵐᵒᵖ (shiftedBoundaryTerms C 0),
    Subsingleton (TorWith P.val M 1)

/-- The degree-zero right arrow is the unique map into Tor₁(0,M). -/
def ZeroSequence.β {C : Complex.{u,v} R} {M : ModuleCat.{w} R}
    (_S : ZeroSequence C M) (P : ProjectiveChoice Rᵐᵒᵖ (shiftedBoundaryTerms C 0)) :
    Homology (tensorComplex C M) 0 →ₗ[ℤ] TorWith P.val M 1 := 0

/-- The whole natural family. Simultaneous maps include naturality in each
variable separately and compatibility with every projective choice for Tor.
Over a commutative ring, coefficient scalar endomorphisms give the usual
scalar linearity of both arrows. -/
structure UniversalCoefficients (R : Type u) [Ring R] where
  zero : ∀ (C : Complex.{u,v} R), FlatTermsAndBoundaries.{u,v,w} C →
    ∀ M : ModuleCat.{w} R, ZeroSequence C M
  positive : ∀ (C : Complex.{u,v} R), FlatTermsAndBoundaries.{u,v,w} C →
    ∀ (M : ModuleCat.{w} R) (n : ℕ) (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n))),
      PositiveSequence C M n P
  natural_zero : ∀ (C D : Complex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (hD : FlatTermsAndBoundaries.{u,v,w} D)
    (f : C ⟶ D) (M M' : ModuleCat.{w} R) (g : M ⟶ M'),
    (homologyMap (tensorFirstMap f M ≫ tensorSecondMap D g.hom) 0).comp (zero C hC M).α =
      (zero D hD M').α.comp (tensorMap (homologyMap f 0) g.hom)
  natural_positive : ∀ (C D : Complex.{u,v} R)
    (hC : FlatTermsAndBoundaries.{u,v,w} C) (hD : FlatTermsAndBoundaries.{u,v,w} D)
    (f : C ⟶ D) (M M' : ModuleCat.{w} R) (g : M ⟶ M') (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology C n)))
    (P' : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Homology D n))) (T : TorMaps.{u,v,w} R 1),
    (homologyMap (tensorFirstMap f M ≫ tensorSecondMap D g.hom) (n+1)).comp
        (positive C hC M n P).α =
      (positive D hD M' n P').α.comp (tensorMap (homologyMap f (n+1)) g.hom) ∧
    (T.map P P' (ModuleCat.ofHom (homologyMap f n)) g).comp (positive C hC M n P).β =
      (positive D hD M' n P').β.comp
        (homologyMap (tensorFirstMap f M ≫ tensorSecondMap D g.hom) (n+1))

def cycles_flatType : Prop :=
  ∀ (R : Type u) [Ring R] (C : Complex.{u,v} R),
    FlatTermsAndBoundaries.{u,v,w} C → ∀ n, RightFlat.{u,v,w} R (cycles C n)

def tensor_degreewise_exactType : Prop :=
  ∀ (R : Type u) [Ring R] (C : Complex.{u,v} R),
    FlatTermsAndBoundaries.{u,v,w} C → ∀ M : ModuleCat.{w} R,
      DegreewiseExact (tensorFirstMap (cycleInclusion C) M)
        (tensorFirstMap (boundaryProjection C) M)

/-- The homology sequence connector is exactly jₙ ⊗ 1, with positive sign,
under the canonical homology identifications of the zero complexes. -/
def tensor_connectorType : Prop :=
  ∀ (R : Type u) [Ring R] (C : Complex.{u,v} R),
    FlatTermsAndBoundaries.{u,v,w} C → ∀ (M : ModuleCat.{w} R) (n : ℕ),
    ∃ δ : Homology (tensorComplex (shiftedBoundaryComplex C) M) (n+1) →ₗ[ℤ]
        Homology (tensorComplex (cycleComplex C) M) n,
      Connecting (tensorFirstMap (cycleInclusion C) M)
        (tensorFirstMap (boundaryProjection C) M) (n+1) n δ ∧
      SequenceExact (tensorFirstMap (cycleInclusion C) M)
        (tensorFirstMap (boundaryProjection C) M) (n+1) n δ ∧
      ∀ t, δ (tensorZeroClass (shiftedBoundaryTerms C) M (n+1) t) =
        tensorZeroClass (cycleTerms C) M n (jTensor C M n t)

def universal_coefficientsType : Prop :=
  ∀ (R : Type u) [Ring R], Nonempty (UniversalCoefficients.{u,v,w} R)

/-- Explicit short exactness at the H₋₁ = 0 endpoint. -/
def zero_sequence_exactType : Prop :=
  ∀ (R : Type u) [Ring R] (C : Complex.{u,v} R) (M : ModuleCat.{w} R)
    (S : ZeroSequence C M) (P : ProjectiveChoice Rᵐᵒᵖ (shiftedBoundaryTerms C 0)),
    Function.Injective S.α ∧ Function.Exact S.α (S.β P) ∧ Function.Surjective (S.β P)

/-- The zero-degree right arrow is natural as well. The map between the
H₋₁ terms is the unique map of zero modules. -/
def zero_tail_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (C D : Complex.{u,v} R) (f : C ⟶ D)
    (M M' : ModuleCat.{w} R) (g : M ⟶ M') (S : ZeroSequence C M) (S' : ZeroSequence D M')
    (P : ProjectiveChoice Rᵐᵒᵖ (shiftedBoundaryTerms C 0))
    (P' : ProjectiveChoice Rᵐᵒᵖ (shiftedBoundaryTerms D 0)) (T : TorMaps.{u,v,w} R 1),
    (T.map P P' 0 g).comp (S.β P) =
      (S'.β P').comp (homologyMap (tensorFirstMap f M ≫ tensorSecondMap D g.hom) 0)

/-- The chapter's commutative scalar convention. The displayed tensor and
homology endomorphisms ARE the coefficient-induced scalar actions. For the
Tor term we use the established `torModule` action explicitly. -/
def scalar_compatibilityType : Prop :=
  ∀ (K : Type u) [CommRing K] (U : UniversalCoefficients.{u,v,w} K)
    (C : Complex.{u,v} K) (hC : FlatTermsAndBoundaries.{u,v,w} C) (M : ModuleCat.{w} K),
    (∀ r, (homologyMap (tensorSecondMap C (scalarMap M r).hom) 0).comp (U.zero C hC M).α =
      (U.zero C hC M).α.comp (tensorMap LinearMap.id (scalarMap M r).hom)) ∧
    ∀ (n : ℕ) (P : ProjectiveChoice Kᵐᵒᵖ (ModuleCat.of Kᵐᵒᵖ (Homology C n)))
      (T : TorMaps.{u,v,w} K 1),
      (∀ r, (homologyMap (tensorSecondMap C (scalarMap M r).hom) (n+1)).comp
          (U.positive C hC M n P).α =
        (U.positive C hC M n P).α.comp (tensorMap LinearMap.id (scalarMap M r).hom)) ∧
      (letI := torModule T P M
       ∀ r x, (U.positive C hC M n P).β
          (homologyMap (tensorSecondMap C (scalarMap M r).hom) (n+1) x) =
        r • (U.positive C hC M n P).β x)

end
end P103.Specs.Ch11.UniversalCoefficientsHomology
