import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Exact.Basic

/-!
Local detection in Theorem 4.2 (paper.tex 848–849, 864–866).
All modules are arbitrary unital modules over a commutative ring, including
zero rings. `Subsingleton M` expresses that the module is zero. Localization
and its induced maps are the same fraction objects as in ModuleLocalization.
-/
namespace P103.Ch04.LocalDetectionSpecs

universe u v w x

/-- The annihilator of an element is the annihilator of its cyclic submodule. -/
def NonzeroWitness : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (m : M), m ≠ 0 →
    ∃ (P : Ideal R) (hP : P.IsMaximal), letI := hP
      (Submodule.span R ({m} : Set M)).annihilator ≤ P ∧
        LocalizedModule.mk (S := P.primeCompl) m 1 ≠ 0

def ZeroDetection : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    Subsingleton M ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Subsingleton (LocalizedModule P.primeCompl M)

def InjectivityDetection : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N),
    Function.Injective f ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Function.Injective (LocalizedModule.map P.primeCompl f)

def SurjectivityDetection : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N),
    Function.Surjective f ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Function.Surjective (LocalizedModule.map P.primeCompl f)

def BijectivityDetection : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N),
    Function.Bijective f ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (LocalizedModule.map P.primeCompl f)

/-- No assumption on the composite is made in either direction. -/
def ExactnessDetection : Prop :=
  ∀ (R : Type u) [CommRing R] (L : Type v) (M : Type w) (N : Type x)
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (f : L →ₗ[R] M) (g : M →ₗ[R] N),
    Function.Exact f g ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Function.Exact (LocalizedModule.map P.primeCompl f)
        (LocalizedModule.map P.primeCompl g)

/-- Arbitrary indexed sequences with a successor function; exactness is at
all consecutive pairs. Integer indexed chains and cochains are obtained by
choosing predecessor or successor on the integers. -/
def SequenceExactnessDetection : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) (next : ι → ι)
    (M : ι → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (d : ∀ i, M i →ₗ[R] M (next i)),
    (∀ i, Function.Exact (d i) (d (next i))) ↔
      ∀ (P : Ideal R) [P.IsMaximal], ∀ i,
        Function.Exact (LocalizedModule.map P.primeCompl (d i))
          (LocalizedModule.map P.primeCompl (d (next i)))

/-- The empty family of maximal ideals in the zero ring causes no exception. -/
def ZeroRingCase : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R]
    (M : Type v) [AddCommGroup M] [Module R M],
    Subsingleton M ∧ ¬ ∃ P : Ideal R, P.IsMaximal

end P103.Ch04.LocalDetectionSpecs
