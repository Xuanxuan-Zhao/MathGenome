import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Abelian.Injective.Ext

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AdvCommAlg.Gorenstein AdvCommAlg.Depth

namespace CommutativeAlgebraNotes.MinimalInjectiveResolutionSoclesSpecs

universe u

variable {R : Type u} [CommRing R]

/-- The input to the recursion is an injective envelope for each module,
including its actual essential inclusion. -/
abbrev EnvelopeChoice := (Y : ModuleCat.{u} R) → InjectiveEnvelope R Y

/-- The next cosyzygy is the quotient by the image of the chosen inclusion. -/
def cosyzygy (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) :
    ℕ → ModuleCat.{u} R
  | 0 => X
  | n + 1 => ModuleCat.of R ((H (cosyzygy H X n)).carrier ⧸
      LinearMap.range (H (cosyzygy H X n)).inclusion)

abbrev term (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) (n : ℕ) :
    ModuleCat.{u} R := ModuleCat.of R (H (cosyzygy H X n)).carrier

def inclusion (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) (n : ℕ) :
    cosyzygy H X n ⟶ term H X n :=
  ModuleCat.ofHom (H (cosyzygy H X n)).inclusion

def quotient (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) (n : ℕ) :
    term H X n ⟶ cosyzygy H X (n + 1) :=
  ModuleCat.ofHom (LinearMap.range (H (cosyzygy H X n)).inclusion).mkQ

@[reassoc (attr := simp)]
theorem inclusion_quotient (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) (n : ℕ) :
    inclusion H X n ≫ quotient H X n = 0 := by
  apply ModuleCat.hom_ext
  ext x
  exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ x)

/-- The outgoing differential is the quotient followed by the next hull inclusion. -/
def differential (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) (n : ℕ) :
    term H X n ⟶ term H X (n + 1) :=
  quotient H X n ≫ inclusion H X (n + 1)

abbrev cocomplex (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (term H X) (differential H X) (fun n => by simp [differential])

@[simp]
theorem cocomplex_d (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) (n : ℕ) :
    (cocomplex H X).d n (n + 1) = differential H X n :=
  CochainComplex.of_d _ _ n

def augmentation (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) :
    (CochainComplex.single₀ (ModuleCat.{u} R)).obj X ⟶ cocomplex H X :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨inclusion H X 0, by
    change inclusion H X 0 ≫ (cocomplex H X).d 0 (0 + 1) = 0
    rw [cocomplex_d, differential, inclusion_quotient_assoc, zero_comp]⟩

@[simp]
theorem augmentation_f_zero (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) :
    (augmentation H X).f 0 = inclusion H X 0 :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- A choice of the specified hull tower together with its resolution property. -/
structure Resolution (X : ModuleCat.{u} R) where
  envelopes : EnvelopeChoice (R := R)
  quasiIso : QuasiIso (augmentation envelopes X)

def Resolution.toInjectiveResolution {X : ModuleCat.{u} R} (J : Resolution X) :
    InjectiveResolution X where
  cocomplex := cocomplex J.envelopes X
  injective n := by
    let E := J.envelopes (cosyzygy J.envelopes X n)
    let : Module.Injective R E.carrier := E.isEnvelope.injectiveModule
    exact Module.injective_object_of_injective_module R E.carrier
  ι := augmentation J.envelopes X
  quasiIso := J.quasiIso

def resolutionType :=
  ∀ {R : Type u} [CommRing R], ModuleCat.{u} R → Type (u + 1)

abbrev resolutionValue {R : Type u} [CommRing R] (X : ModuleCat.{u} R) := Resolution X

def resolutionExists : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X : ModuleCat.{u} R), Nonempty (Resolution X)

abbrev residueObject (R : Type u) [CommRing R] [IsLocalRing R] : ModuleCat.{u} R :=
  ModuleCat.of R (IsLocalRing.ResidueField R)

def residueHomDifferentialZero : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X : ModuleCat.{u} R} (J : Resolution X) (i j : ℕ)
    (f : residueObject R ⟶ J.toInjectiveResolution.cocomplex.X i),
    f ≫ J.toInjectiveResolution.cocomplex.d i j = 0

/-- The Ext comparison sends the class of a cocycle to evaluation at the residue class of 1.
Both sides carry their usual descended residue-field actions. -/
def residueExtSocleComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X : ModuleCat.{u} R} (J : Resolution X) (n : ℕ),
    ∃ e : ResidueExt X n ≃ₗ[IsLocalRing.ResidueField R]
        Socle R (J.toInjectiveResolution.cocomplex.X n),
      ∀ (f : residueObject R ⟶ J.toInjectiveResolution.cocomplex.X n)
        (hf : f ≫ J.toInjectiveResolution.cocomplex.d n (n + 1) = 0),
        (e (J.toInjectiveResolution.extMk f (n + 1) rfl hf)).val = f.hom 1

end CommutativeAlgebraNotes.MinimalInjectiveResolutionSoclesSpecs
