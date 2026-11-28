import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SplittingSystem
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Trace

/-! Independent specifications for the simple columns of split matrix factors. -/

namespace RepTheorySurvey.Modular.SplitMatrixColumnsSpec

open scoped Matrix Matrix.Module

universe uF uA uG uV

-- The declaration types quantify over independent universes.
set_option linter.checkUnivs false

section
variable {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
  {r : ℕ} {d : Fin r → ℕ}

/-- The native left module on a column, pulled back along evaluation of the chosen factor. -/
noncomputable def columnModule
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) :
    ModuleCat.{uF} A :=
  letI := Module.compHom (Fin (d i) → F)
    ((Pi.evalRingHom (fun j : Fin r => Matrix (Fin (d j)) (Fin (d j)) F) i).comp q.toRingHom)
  ModuleCat.of A (Fin (d i) → F)

instance columnFieldModule
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) :
    Module F (columnModule q i) :=
  inferInstanceAs (Module F (Fin (d i) → F))

instance columnFieldFinite
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) :
    Module.Finite F (columnModule q i) :=
  inferInstanceAs (Module.Finite F (Fin (d i) → F))

instance columnScalarTower
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) :
    IsScalarTower F A (columnModule q i) :=
  IsScalarTower.of_algebraMap_smul (A := A) fun c v => by
    change ((q (algebraMap F A c)) i) *ᵥ (v : Fin (d i) → F) = c • (v : Fin (d i) → F)
    rw [q.commutes]
    exact Matrix.Module.scalar_smul c (v : Fin (d i) → F)

instance columnSMulCommClass
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) :
    SMulCommClass A F (columnModule q i) where
  smul_comm a c v := by
    change (q a i) *ᵥ (c • v) = c • ((q a i) *ᵥ v)
    exact (q a i).mulVecLin.map_smul c v

/-- The action of the chosen factor, viewed as a field-linear endomorphism. -/
noncomputable abbrev columnAction
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) :
    A →ₐ[F] Module.End F (Fin (d i) → F) :=
  Matrix.toLinAlgEquiv'.toAlgHom.comp
    ((Pi.evalAlgHom F (fun j : Fin r => Matrix (Fin (d j)) (Fin (d j)) F) i).comp q)

end

def columnModuleType :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ},
    (A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) → Fin r → ModuleCat.{uF} A

noncomputable def columnModuleValue : columnModuleType.{uF, uA} := @columnModule

def columnActionType :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ},
    (A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) →
    (i : Fin r) → A →ₐ[F] Module.End F (Fin (d i) → F)

noncomputable def columnActionValue : columnActionType.{uF, uA} := @columnAction

def columnActionApply :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F))
    (i : Fin r) (a : A) (v : columnModule q i),
    columnAction q i a v = a • v

def columnLsmul :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) (a : A),
    (columnAction q i a : Module.End F (columnModule q i)) =
    Algebra.lsmul F F (columnModule q i) a

def columnFinrank :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) i,
    Module.finrank F (columnModule q i) = d i

def columnActionSurjective :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)),
    Function.Surjective q → ∀ i : Fin r, Function.Surjective (columnAction q i)

def columnFamily :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)),
    (∀ i, 0 < d i) → Function.Surjective q → RingHom.ker q.toRingHom ≤ Ring.jacobson A →
    MR01Spec.SimpleRepresentativeFamily (columnModule q)

def columnExhaustive :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)),
    (∀ i, 0 < d i) → Function.Surjective q → RingHom.ker q.toRingHom ≤ Ring.jacobson A →
    ∀ M : ModuleCat.{uV} A, IsSimpleModule A M → ∃ i, Nonempty (M ≃ₗ[A] columnModule q i)

def columnScalarBijective :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)),
    (∀ i, 0 < d i) → Function.Surjective q →
    ∀ i, Function.Bijective (algebraMap F (Module.End A (columnModule q i)))

def columnRank :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (a : A) (i : Fin r),
    Module.finrank F (LinearMap.range (columnAction q i a)) = (q a i).rank

def columnRankOne :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (a : A) (i : Fin r),
    (q a i).rank = 1 → (∀ j, j ≠ i → q a j = 0) →
    ∀ j : Fin r, Module.finrank F (LinearMap.range (columnAction q j a)) =
      if j = i then 1 else 0

def columnTrace :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (a : A) (i : Fin r),
    LinearMap.trace F (Fin (d i) → F) (columnAction q i a) = Matrix.trace (q a i)

open Classical in
def columnTraceTest :=
  ∀ {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)),
    Function.Surjective q → ∀ (i : Fin r) (s : Fin (d i)), ∃ a : A,
    q a = Pi.single i (Matrix.single s s 1) ∧
    ∀ j : Fin r, LinearMap.trace F (Fin (d j) → F) (columnAction q j a) =
      if j = i then 1 else 0

section
variable {F : Type uF} [Field F] {G : Type uG} [Group G]
  {r : ℕ} {d : Fin r → ℕ}

noncomputable abbrev modularColumnMap
    (e : MR01Spec.radicalQuotientValue F G ≃ₐ[F]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) :=
  e.toAlgHom.comp (MR01Spec.radicalQuotientMapValue F G)

end

def modularColumnMapType :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G] {r : ℕ} {d : Fin r → ℕ},
    (MR01Spec.radicalQuotientValue F G ≃ₐ[F]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) →
    MonoidAlgebra F G →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)

noncomputable def modularColumnMapValue : modularColumnMapType.{uF, uG} := @modularColumnMap

def modularColumnMapSurjective :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G] {r : ℕ} {d : Fin r → ℕ}
    (e : MR01Spec.radicalQuotientValue F G ≃ₐ[F]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)),
    Function.Surjective (modularColumnMap e)

def modularColumnMapKer :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G] {r : ℕ} {d : Fin r → ℕ}
    (e : MR01Spec.radicalQuotientValue F G ≃ₐ[F]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)),
    RingHom.ker (modularColumnMap e).toRingHom = Ring.jacobson (MonoidAlgebra F G)

def ordinaryColumnFamily :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G] {r : ℕ} {d : Fin r → ℕ},
    (∀ i, 0 < d i) →
    ∀ e : MonoidAlgebra F G ≃ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F),
      MR01Spec.SimpleRepresentativeFamily (columnModule e.toAlgHom)

def modularColumnFamily :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G] {r : ℕ} {d : Fin r → ℕ},
    (∀ i, 0 < d i) →
    ∀ e : MR01Spec.radicalQuotientValue F G ≃ₐ[F]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F),
      MR01Spec.SimpleRepresentativeFamily (columnModule (modularColumnMap e))

def ordinaryColumnsExist :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G],
    MR01Spec.splitMatrixAlgebraValue F (MonoidAlgebra F G) →
    ∃ (n : ℕ) (m : Fin n → ℕ), (∀ i, 0 < m i) ∧
      ∃ e : MonoidAlgebra F G ≃ₐ[F] ((i : Fin n) → Matrix (Fin (m i)) (Fin (m i)) F),
        MR01Spec.SimpleRepresentativeFamily (columnModule e.toAlgHom)

def modularColumnsExist :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G],
    MR01Spec.splitMatrixAlgebraValue F (MR01Spec.radicalQuotientValue F G) →
    ∃ (n : ℕ) (m : Fin n → ℕ), (∀ i, 0 < m i) ∧
      ∃ e : MR01Spec.radicalQuotientValue F G ≃ₐ[F]
        ((i : Fin n) → Matrix (Fin (m i)) (Fin (m i)) F),
        MR01Spec.SimpleRepresentativeFamily (columnModule (modularColumnMap e))

end RepTheorySurvey.Modular.SplitMatrixColumnsSpec
