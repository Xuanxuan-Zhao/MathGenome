import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleModule.Basic

/-! Independent specification and shared data for Definition MR01. -/

namespace RepTheorySurvey.Modular.MR01Spec

universe uG uO uK uF uA uI uV

-- The expected type declarations intentionally combine independent parameter universes.
set_option linter.checkUnivs false

def primeToPartType := Type uG → ℕ → ℕ

noncomputable def primeToPartValue : primeToPartType.{uG} :=
  fun G p => ordCompl[p] (Nat.card G)

def isPRegularType := {G : Type uG} → [Group G] → ℕ → G → Prop

def isPRegularValue : isPRegularType.{uG} :=
  @fun _ _ p g => (orderOf g).Coprime p

def pRegularType := (G : Type uG) → [Group G] → ℕ → Type uG

def pRegularValue : pRegularType.{uG} :=
  fun G _ p => {g : G // (orderOf g).Coprime p}

def splitMatrixAlgebraType :=
  (F : Type uF) → [Field F] → (A : Type uA) → [Ring A] → [Algebra F A] → Prop

/-- A finite product of square matrix algebras of positive sizes over the given field. -/
def splitMatrixAlgebraValue : splitMatrixAlgebraType.{uF, uA} :=
  fun F _ A _ _ =>
    ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, 0 < d i) ∧
      Nonempty (A ≃ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F))

def radicalQuotientType := (F : Type uF) → [Field F] → (G : Type uG) → [Group G] →
  Type (max uF uG)

abbrev radicalQuotientValue : radicalQuotientType.{uF, uG} :=
  fun F _ G _ => MonoidAlgebra F G ⧸ Ring.jacobson (MonoidAlgebra F G)

def radicalQuotientMapType :=
  (F : Type uF) → [Field F] → (G : Type uG) → [Group G] →
    MonoidAlgebra F G →ₐ[F] (MonoidAlgebra F G ⧸ Ring.jacobson (MonoidAlgebra F G))

noncomputable def radicalQuotientMapValue : radicalQuotientMapType.{uF, uG} :=
  fun F _ G _ => Ideal.Quotient.mkₐ F (Ring.jacobson (MonoidAlgebra F G))

def reductionType :=
  (O : Type uO) → [CommRing O] → [IsLocalRing O] → (G : Type uG) → [Group G] →
    MonoidAlgebra O G →+* MonoidAlgebra (IsLocalRing.ResidueField O) G

noncomputable def reductionValue : reductionType.{uO, uG} :=
  fun O _ _ G _ => MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)

def fractionMapType :=
  (O : Type uO) → [CommRing O] → (K : Type uK) → [Field K] → [Algebra O K] →
    (G : Type uG) → [Group G] → MonoidAlgebra O G →+* MonoidAlgebra K G

noncomputable def fractionMapValue : fractionMapType.{uO, uK, uG} :=
  fun O _ K _ _ G _ => MonoidAlgebra.mapRingHom G (algebraMap O K)

/-- The fields of a splitting system for a specified finite group, prime and coefficient rings. -/
structure SplittingSystemData (G : Type uG) [Group G] [Finite G] (p : ℕ)
    (O : Type uO) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type uK) [Field K] [Algebra O K] : Type uO where
  prime : p.Prime
  uniformizer : O
  maximalIdeal_eq_span : IsLocalRing.maximalIdeal O = Ideal.span {uniformizer}
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  fractionRing : IsFractionRing O K
  charZero : CharZero K
  residueChar : CharP (IsLocalRing.ResidueField O) p
  primitiveRoot : ∃ ζ : K, IsPrimitiveRoot ζ (primeToPartValue G p)
  ordinarySplit : splitMatrixAlgebraValue K (MonoidAlgebra K G)
  modularSplit : splitMatrixAlgebraValue (IsLocalRing.ResidueField O)
    (radicalQuotientValue (IsLocalRing.ResidueField O) G)

def splittingSystemType :=
  (G : Type uG) → [Group G] → [Finite G] → ℕ →
    (O : Type uO) → [CommRing O] → [IsDomain O] → [IsDiscreteValuationRing O] →
    (K : Type uK) → [Field K] → [Algebra O K] → Type uO

def splittingSystemValue : splittingSystemType.{uG, uO, uK} :=
  fun G _ _ p O _ _ _ K _ _ => SplittingSystemData G p O K

/-- A complete, irredundant family of simple left modules. -/
structure SimpleRepresentativeFamily {A : Type uA} [Ring A] {ι : Type uI}
    (S : ι → ModuleCat.{uV} A) : Prop where
  simple : ∀ i, IsSimpleModule A (S i)
  eq_of_iso : ∀ {i j}, Nonempty (S i ≃ₗ[A] S j) → i = j
  exhaustive : ∀ M : ModuleCat.{uV} A, IsSimpleModule A M →
    ∃ i, Nonempty (M ≃ₗ[A] S i)

def simpleFamilyType :=
  {A : Type uA} → [Ring A] → {ι : Type uI} → (ι → ModuleCat.{uV} A) → Prop

def simpleFamilyValue : simpleFamilyType.{uA, uI, uV} :=
  fun S => SimpleRepresentativeFamily S

def moduleRepresentationType :=
  (F : Type uF) → [Field F] → (G : Type uG) → [Group G] →
    (M : Type uV) → [AddCommGroup M] → [Module (MonoidAlgebra F G) M] →
      Representation F G (RestrictScalars F (MonoidAlgebra F G) M)

noncomputable def moduleRepresentationValue : moduleRepresentationType.{uF, uG, uV} :=
  fun F _ G _ M _ _ => Representation.ofModule (k := F) (G := G) M

def representationModuleType :=
  {F : Type uF} → [Field F] → {G : Type uG} → [Group G] →
    {V : Type uV} → [AddCommGroup V] → [Module F V] →
      Representation F G V → ModuleCat.{uV} (MonoidAlgebra F G)

noncomputable def representationModuleValue : representationModuleType.{uF, uG, uV} :=
  @fun F _ G _ _ _ _ ρ => ModuleCat.of (MonoidAlgebra F G) ρ.asModule

def primeToPartPos :=
  ∀ (G : Type uG) [Group G] [Finite G] (p : ℕ), 0 < ordCompl[p] (Nat.card G)

def primeToPartGreatest :=
  ∀ (G : Type uG) [Group G] [Finite G] {p : ℕ}, p.Prime →
    let m := ordCompl[p] (Nat.card G)
    m ∣ Nat.card G ∧ m.Coprime p ∧
      ∀ d : ℕ, d ∣ Nat.card G → d.Coprime p → d ∣ m

def orderOfDvdPrimeToPart :=
  ∀ {G : Type uG} [Group G] {p : ℕ}, p.Prime →
    ∀ g : {g : G // (orderOf g).Coprime p}, orderOf g.val ∣ ordCompl[p] (Nat.card G)

def residueKernel :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : SplittingSystemData G p O K),
    RingHom.ker (IsLocalRing.residue O) = Ideal.span {S.uniformizer}

end RepTheorySurvey.Modular.MR01Spec
