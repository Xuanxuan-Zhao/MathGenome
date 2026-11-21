import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! The completion is the inverse limit of the quotients by `I^n M`.
The additional zeroth coordinate in Mathlib is the zero module; the
`positive_residues` statement explicitly identifies the positive-index limit.
There are no Noetherian, finite generation, or separatedness hypotheses. -/
universe u v w z

namespace P103.Adic

abbrev Power {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) : Submodule R M :=
  I ^ n • ⊤

abbrev Residue {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) := M ⧸ Power I M n

abbrev Completion {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] := AdicCompletion I M

end P103.Adic

namespace P103.Specs.Ch07.CompletionInterface
open P103.Adic

def canonicalType := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M], M →ₗ[R] Completion I M

noncomputable def canonicalValue (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : M →ₗ[R] Completion I M :=
  AdicCompletion.of I M

def projectionType := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ), Completion I M →ₗ[R] Residue I M n

noncomputable def projectionValue (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) : Completion I M →ₗ[R] Residue I M n :=
  AdicCompletion.eval I M n

def transitionType := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n), Residue I M n →ₗ[R] Residue I M m

noncomputable def transitionValue (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n) : Residue I M n →ₗ[R] Residue I M m :=
  AdicCompletion.transitionMap I M h

def completedMapType := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N), Completion I M →ₗ[Completion I R] Completion I N

noncomputable def completedMapValue (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : Completion I M →ₗ[Completion I R] Completion I N :=
  AdicCompletion.map I f

def canonicalRingType := ∀ (R : Type u) [CommRing R] (I : Ideal R), R →+* Completion I R

noncomputable def canonicalRingValue (R : Type u) [CommRing R] (I : Ideal R) : R →+* Completion I R :=
  algebraMap R (Completion I R)

def completedRingType := ∀ (R : Type u) [CommRing R] (I : Ideal R), CommRing (Completion I R)

noncomputable def completedRingValue (R : Type u) [CommRing R] (I : Ideal R) : CommRing (Completion I R) :=
  inferInstance

def completedModuleType := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M], Module (Completion I R) (Completion I M)

noncomputable def completedModuleValue (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Module (Completion I R) (Completion I M) :=
  inferInstance

def zeroIdealEquivType := ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], M ≃ₗ[R] Completion (⊥ : Ideal R) M

noncomputable def zeroIdealEquivValue (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] : M ≃ₗ[R] Completion (⊥ : Ideal R) M :=
  AdicCompletion.ofLinearEquiv ⊥ M

def canonical_coordinateType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (x : M) (n : ℕ), AdicCompletion.eval I M n (AdicCompletion.of I M x) = (Power I M n).mkQ x

def transition_representativeType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n) (x : M), AdicCompletion.transitionMap I M h ((Power I M n).mkQ x) = (Power I M m).mkQ x

def compatibleType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n) (x : Completion I M), AdicCompletion.transitionMap I M h (AdicCompletion.eval I M n x) = AdicCompletion.eval I M m x

def ext_positiveType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (x y : Completion I M) (h : ∀ n : ℕ, AdicCompletion.eval I M (n+1) x = AdicCompletion.eval I M (n+1) y), x = y

def positive_residuesType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (f : ∀ n : ℕ, Residue I M (n+1))
    (hf : ∀ {m n : ℕ} (h : m ≤ n),
      AdicCompletion.transitionMap I M (Nat.add_le_add_right h 1) (f n) = f m), (∃! x : Completion I M, ∀ n : ℕ, AdicCompletion.eval I M (n+1) x = f n)

def canonical_kernelType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M], LinearMap.ker (AdicCompletion.of I M) = ⨅ n : ℕ, Power I M n

def map_coordinateType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (x : Completion I M) (n : ℕ), AdicCompletion.eval I N n (AdicCompletion.map I f x) = f.reduceModIdeal (I ^ n) (AdicCompletion.eval I M n x)

def map_canonicalType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (x : M), AdicCompletion.map I f (AdicCompletion.of I M x) = AdicCompletion.of I N (f x)

def map_identityType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M], AdicCompletion.map I (LinearMap.id (R := R) (M := M)) = LinearMap.id

def map_compositionType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (P : Type z) [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P), (AdicCompletion.map I g).comp (AdicCompletion.map I f) = AdicCompletion.map I (g.comp f)

def ring_canonical_coordinateType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (r : R) (n : ℕ), AdicCompletion.evalₐ I n (algebraMap R (Completion I R) r) = Ideal.Quotient.mk (I ^ n) r

def ring_mul_coordinateType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (r s : Completion I R) (n : ℕ), (r * s).val n = r.val n * s.val n

def ring_one_coordinateType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ), (1 : Completion I R).val n = 1

def scalar_coordinateType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (r : Completion I R) (x : Completion I M) (n : ℕ), (r • x).val n = r.val n • x.val n

def scalar_canonicalType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (r : R) (x : M), (algebraMap R (Completion I R) r) • AdicCompletion.of I M x = AdicCompletion.of I M (r • x)

def zeroIdealEquiv_canonicalType : Prop := ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : M), AdicCompletion.ofLinearEquiv (⊥ : Ideal R) M x = AdicCompletion.of ⊥ M x

def topIdeal_subsingletonType : Prop := ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], Subsingleton (Completion (⊤ : Ideal R) M)

def zeroModule_subsingletonType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M], Subsingleton (Completion I M)

def zeroRing_subsingletonType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton R], Subsingleton (Completion I M)

def mapType := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N), Completion I M →ₗ[R] Completion I N

noncomputable def mapValue (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : Completion I M →ₗ[R] Completion I N :=
  (AdicCompletion.map I f).restrictScalars R

def map_naturalType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N), ((AdicCompletion.map I f).restrictScalars R).comp (AdicCompletion.of I M) = (AdicCompletion.of I N).comp f

def zeroIdealEquiv_naturalType : Prop := ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (x : M), AdicCompletion.map (⊥ : Ideal R) f (AdicCompletion.ofLinearEquiv ⊥ M x) = AdicCompletion.ofLinearEquiv ⊥ N (f x)

def canonical_injective_iffType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M], Function.Injective (AdicCompletion.of I M) ↔ (⨅ n : ℕ, Power I M n) = ⊥

def inverseLimit_universalType : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : ∀ n : ℕ, N →ₗ[R] Residue I M n)
    (hf : ∀ {m n : ℕ} (h : m ≤ n), (AdicCompletion.transitionMap I M h).comp (f n) = f m), (∃! F : N →ₗ[R] Completion I M, ∀ n : ℕ, (AdicCompletion.eval I M n).comp F = f n)

end P103.Specs.Ch07.CompletionInterface
