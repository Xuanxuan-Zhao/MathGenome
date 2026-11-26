import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding

namespace LinearAlgebraicGroups.Specs.ExceptionalStableAlcoveRepresentatives

open CategoryTheory
open ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open ExceptionalAffineBruhat
open ExceptionalAffineBuilding
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model integerAlgebra)
attribute [local instance] integerAlgebra
open scoped TensorProduct CategoryTheory.MonObj

universe u

noncomputable section

/-- The order of the actual marked adjoint alcove quotient in the split exceptional cases. -/
def ExceptionalAlcoveQuotientOrder : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : ExceptionalIwahoriImageComparison.MarkedCentralCover M M'}
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (_ : SplitLevel K c p p' e) (n : ℕ) (b : Fin n ≃ E.base.support),
    (n = 6 ∨ n = 7 ∨ n = 8) →
    ExceptionalNumbering E n b → E.datum.rootSpan ℤ = ⊤ →
    Nat.card (alcoveStabilizer (ApartmentRoots.split E.datum ℚ)
      ((ApartmentRoots.split E.datum ℚ).alcove p')) = (if n = 6 then 3 else if n = 7 then 2 else 1)

/-- A chosen stable alcove gives a cocycle in the marked standard alcove stabilizer
after transport by its chamber representative. Trivial type class is exactly
Iwahori membership there. -/
def StableAlcoveStabilizer : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : ExceptionalIwahoriImageComparison.MarkedCentralCover M M'}
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e} (B : SplitBuildingLevel Y)
    {Γ : Type u} [Group Γ] {ρ : Γ →* MulAut (FieldPoints M' K)}
    {f : Γ → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)},
    (∀ σ, AutomorphismComparison Y.ad (ρ σ) (f σ)) →
    ∀ (coef : CoefficientAction B.ad ρ f) (a : Γ → FieldPoints M' K)
      (g : Y.ad.G₀) (_ : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)),
      (∀ σ, B.adjoint.action (a σ) '' (coef.action σ '' B.ad.realization.closedFace g ∅) =
        B.ad.realization.closedFace g ∅) →
      let a₀ σ := (g : FieldPoints M' K)⁻¹ * a σ * ρ σ g
      (∀ σ τ, a₀ (σ * τ) = a₀ σ * ρ σ (a₀ τ)) ∧
      ∀ σ, B.adjoint.action (a₀ σ) '' (coef.action σ '' B.ad.realization.closedFace 1 ∅) =
          B.ad.realization.closedFace 1 ∅ ∧
        a₀ σ ∈ Y.ad.I ⊔ lengthZeroNormalizer Y.ad ∧
        (typeChange Y.typeQuotient (a₀ σ) = 1 ↔ a₀ σ ∈ Y.ad.I)

/-- The outer type correction lifts back to the same marked adjoint alcove stabilizer.
The coefficient action and its transport are those of the pinned comparison. -/
def OuterAlcoveTypeCorrection : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : ExceptionalIwahoriImageComparison.MarkedCentralCover M M'}
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e} (_ : SplitBuildingLevel Y)
    (b : Fin 6 ≃ E.base.support),
    ExceptionalNumbering E 6 b → E.datum.rootSpan ℤ = ⊤ →
    ∀ {Γ : Type u} [Group Γ] (φ : Γ) (_ : Subgroup.zpowers φ = ⊤)
      (ρ : Γ →* MulAut (FieldPoints M' K))
      (f : Γ → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y))
      (β : Γ →* MulAut (alcoveStabilizer (ApartmentRoots.split E.datum ℚ)
        ((ApartmentRoots.split E.datum ℚ).alcove p'))),
      (∀ σ, AutomorphismComparison Y.ad (ρ σ) (f σ) ∧
        TypeQuotientTransport Y.typeQuotient Y.typeQuotient (ρ σ).toMonoidHom (β σ).toMonoidHom) →
      (∀ z, β φ z = z⁻¹) →
      ∀ (a : Γ → FieldPoints M' K),
      (∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) →
      (∀ σ, a σ ∈ Y.ad.I ⊔ lengthZeroNormalizer Y.ad) →
      ∃ k : lengthZeroNormalizer Y.ad,
        typeChange Y.typeQuotient k = (typeChange Y.typeQuotient (a φ))⁻¹ ∧
        let a₀ σ := (k : FieldPoints M' K)⁻¹ * a σ * ρ σ k
        (∀ σ τ, a₀ (σ * τ) = a₀ σ * ρ σ (a₀ τ)) ∧
        ∀ σ, a₀ σ ∈ Y.ad.I

section Coefficients

open ExceptionalMarkedRootDescent (MarkedFibre markedWeylWord)
open AutomorphismSequence (AdjointQuotient)
open ExceptionalIwahoriCongruence (integralRing)
open IntegralSemisimpleModel (cocharacter torusPoint)
open ExceptionalLocalRootCoordinates (normalizedValuation)

/-- Over each unramified level, the scalar and pinned actions transport the type
quotient attached to the same marked split apartment. -/
def MarkedAlcoveCoefficientComparison : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : ExceptionalIwahoriImageComparison.MarkedCentralCover M M') (n : ℕ)
    (b : Fin n ≃ D.base.support) (b' : Fin n ≃ E.base.support),
    (n = 6 ∨ n = 7 ∨ n = 8) →
    ExceptionalNumbering D n b → ExceptionalNumbering E n b' →
    D.datum.corootSpan ℤ = ⊤ → E.datum.rootSpan ℤ = ⊤ →
    ∃ (p : ℚ ⊗[ℤ] D.Y) (p' : ℚ ⊗[ℤ] E.Y)
      (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)) (X : SplitLevel F c p p' e)
      (_ : SplitBuildingLevel X),
      e.toLinearMap = c.pushCocharacter.baseChange ℚ ∧ p' = e p ∧
      ∀ (K : Type u) [Field K] [Algebra F K] [FiniteDimensional F K]
        [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
        IsUnramifiedLocalExtension F K →
        ∃ (Y : SplitLevel K c p p' e) (_ : SplitBuildingLevel Y),
          let s := scalarPoints M' (algebraMap F K)
          ScalarComparison (algebraMap F K) s X.ad Y.ad ∧
          TypeQuotientTransport X.typeQuotient Y.typeQuotient s (MonoidHom.id _) ∧
          Nat.card (alcoveStabilizer (ApartmentRoots.split E.datum ℚ)
            ((ApartmentRoots.split E.datum ℚ).alcove p')) = (if n = 6 then 3 else if n = 7 then 2 else 1) ∧
          Y.Coefficients (F := F) ∧
          ∀ (h : n = 6)
            (C : MarkedFibre M F) (C' : MarkedFibre M' F)
            (l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned)
            (l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned)
            (Q : AdjointQuotient C.realization.pinned.pair.G)
            (Q' : AdjointQuotient C'.realization.pinned.pair.G),
            Y.OuterE6Coefficients (h ▸ b) (h ▸ b') C C' (l := l) (l' := l') (Q := Q) (Q' := Q')

/-- The inner representative is a translation cocharacter evaluated at the
base uniformizer followed by a word of pinned simple lifts over that field. -/
def InnerLengthZeroRepresentatives : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : ExceptionalIwahoriImageComparison.MarkedCentralCover M M'}
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (X : SplitLevel F c p p' e) (_ : SplitBuildingLevel X)
    (n : ℕ) (b : Fin n ≃ E.base.support) (_ : n = 6 ∨ n = 7 ∨ n = 8)
    (_ : ExceptionalNumbering E n b) (_ : E.datum.rootSpan ℤ = ⊤)
    (π : Fˣ) (_ : normalizedValuation F (π : F) = WithZero.exp (-1 : ℤ)),
    let A := ApartmentRoots.split E.datum ℚ
    ∀ z : alcoveStabilizer A (A.alcove p'),
      ∃ (y : E.Y) (word : List E.I) (t : X.ad.N),
        (∀ i ∈ word, i ∈ E.base.support) ∧
        (t : FieldPoints M' F) =
          (torusPoint E (integralRing F) (cocharacter E y (integralRing F) π) ≫ M'.torus.hom.hom) *
            markedWeylWord M'.toIntegralMarking (integralRing F) word ∧
        X.ad.affine t = z.val.val ∧
        typeChange X.typeQuotient t = z ∧
        (t : FieldPoints M' F) ∈ lengthZeroNormalizer X.ad ∧
        IsOfFinOrder (t : FieldPoints M' F) ∧
        (t : FieldPoints M' F) ^ (Nat.card (alcoveStabilizer A (A.alcove p')) * 2) = 1 ∧
        (z = 1 → (t : FieldPoints M' F) = 1)

/-- The arithmetic Frobenius of the chosen unramified enlargement,
with the generator and its action on the actual residue field. -/
def IsArithmeticFrobenius {F L : Type u} [Field F] [Field L] [Algebra F L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    (φ : Gal(L/F)) : Prop :=
  Subgroup.zpowers φ = ⊤ ∧
  ∀ z z' : (ValuativeRel.valuation L).valuationSubring, (z' : L) = φ (z : L) →
    IsLocalRing.residue _ z' = IsLocalRing.residue _ z ^ Nat.card (residue F)

/-- Scalar inflation uses the actual restriction of coefficient automorphisms
and preserves the marked stabilizer and its type class. -/
def ScalarAlcoveCocycleInflation : Prop :=
  ∀ {F K L : Type u} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L]
    [IsScalarTower F K L] [FiniteDimensional F K] [FiniteDimensional F L] [IsGalois F K] [IsGalois F L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F L] [ValuativeExtension K L],
    IsUnramifiedLocalExtension F K → IsUnramifiedLocalExtension F L →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
      {c : ExceptionalIwahoriImageComparison.MarkedCentralCover M M'}
      {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
      {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
      (Y : SplitLevel K c p p' e) (Z : SplitLevel L c p p' e)
      (res : Gal(L/F) →* Gal(K/F)),
      (∀ σ x, algebraMap K L (res σ x) = σ (algebraMap K L x)) →
      let s := scalarPoints M' (algebraMap K L)
      ScalarComparison (algebraMap K L) s Y.ad Z.ad →
      TypeQuotientTransport Y.typeQuotient Z.typeQuotient s (MonoidHom.id _) →
      ∀ (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
        (ρ' : Gal(L/F) →* MulAut (FieldPoints M' L)),
        (∀ σ g, ρ σ g = scalarPoints M' σ.toRingHom g) →
        (∀ σ g, ρ' σ g = scalarPoints M' σ.toRingHom g) →
        ∀ (a : Gal(K/F) → FieldPoints M' K),
          (∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) →
          (∀ σ, a σ ∈ Y.ad.I ⊔ lengthZeroNormalizer Y.ad) →
          let a' σ := s (a (res σ))
          (∀ σ τ, a' (σ * τ) = a' σ * ρ' σ (a' τ)) ∧
          (∀ σ, a' σ ∈ Z.ad.I ⊔ lengthZeroNormalizer Z.ad) ∧
          ∀ σ, typeChange Z.typeQuotient (a' σ) = typeChange Y.typeQuotient (a (res σ))

/-- At the chosen divisible unramified level the base representative defines
a coefficient cocycle. Its difference from the given stabilizer cocycle lies
in the Iwahori and is a cocycle for the representative-twisted action. -/
def InnerAlcoveRepresentativeCocycle : Prop :=
  ∀ {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    (_ : IsUnramifiedLocalExtension F L)
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : ExceptionalIwahoriImageComparison.MarkedCentralCover M M'}
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (X : SplitLevel F c p p' e) (Z : SplitLevel L c p p' e) (_ : SplitBuildingLevel Z),
    let s := scalarPoints M' (algebraMap F L)
    ScalarComparison (algebraMap F L) s X.ad Z.ad →
    TypeQuotientTransport X.typeQuotient Z.typeQuotient s (MonoidHom.id _) →
    ∀ (φ : Gal(L/F)), IsArithmeticFrobenius φ →
    ∀ (ρ : Gal(L/F) →* MulAut (FieldPoints M' L)),
      (∀ σ g, ρ σ g = scalarPoints M' σ.toRingHom g) →
      (∀ σ, TypeQuotientTransport Z.typeQuotient Z.typeQuotient (ρ σ).toMonoidHom (MonoidHom.id _)) →
    ∀ (a : Gal(L/F) → FieldPoints M' L),
      (∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) →
      (∀ σ, a σ ∈ Z.ad.I ⊔ lengthZeroNormalizer Z.ad) →
    ∀ (t : lengthZeroNormalizer X.ad),
      typeChange X.typeQuotient t = typeChange Z.typeQuotient (a φ) →
      orderOf (t : FieldPoints M' F) ∣ Nat.card Gal(L/F) →
      ∃ r : Gal(L/F) →* FieldPoints M' L,
        r φ = s t ∧ (∀ σ, r σ ∈ lengthZeroNormalizer Z.ad) ∧
        (∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ)) ∧
        (∀ σ, typeChange Z.typeQuotient (r σ) = typeChange Z.typeQuotient (a σ)) ∧
        (∀ σ, a σ * (r σ)⁻¹ ∈ Z.ad.I) ∧
        (∀ σ, Z.ad.I.map ((MulAut.conj (r σ) * ρ σ).toMonoidHom) = Z.ad.I) ∧
        ∀ σ τ, a (σ * τ) * (r (σ * τ))⁻¹ =
          (a σ * (r σ)⁻¹) * MulAut.conj (r σ) (ρ σ (a τ * (r τ)⁻¹))

end Coefficients


end

end LinearAlgebraicGroups.Specs.ExceptionalStableAlcoveRepresentatives
