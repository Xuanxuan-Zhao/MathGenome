import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletionInterface

/-! Canonical adic completion interface, paper.tex, section Adic completion.
All constructions apply to arbitrary commutative rings, ideals and modules,
including the zero ring and zero modules. -/
universe u v w z
namespace P103.Ch07.CompletionInterface
open P103.Adic

noncomputable def canonical (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : M →ₗ[R] Completion I M :=
  AdicCompletion.of I M

noncomputable def projection (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) : Completion I M →ₗ[R] Residue I M n :=
  AdicCompletion.eval I M n

noncomputable def transition (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n) : Residue I M n →ₗ[R] Residue I M m :=
  AdicCompletion.transitionMap I M h

noncomputable def completedMap (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : Completion I M →ₗ[Completion I R] Completion I N :=
  AdicCompletion.map I f

noncomputable def canonicalRing (R : Type u) [CommRing R] (I : Ideal R) : R →+* Completion I R :=
  algebraMap R (Completion I R)

noncomputable def completedRing (R : Type u) [CommRing R] (I : Ideal R) : CommRing (Completion I R) :=
  inferInstance

noncomputable def completedModule (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Module (Completion I R) (Completion I M) :=
  inferInstance

noncomputable def zeroIdealEquiv (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] : M ≃ₗ[R] Completion (⊥ : Ideal R) M :=
  AdicCompletion.ofLinearEquiv ⊥ M

theorem canonical_coordinate (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (x : M) (n : ℕ) : AdicCompletion.eval I M n (AdicCompletion.of I M x) = (Power I M n).mkQ x := by
  rfl

theorem transition_representative (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n) (x : M) : AdicCompletion.transitionMap I M h ((Power I M n).mkQ x) = (Power I M m).mkQ x := by
  rfl

theorem compatible (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n) (x : Completion I M) : AdicCompletion.transitionMap I M h (AdicCompletion.eval I M n x) = AdicCompletion.eval I M m x := by
  exact x.property h

theorem ext_positive (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (x y : Completion I M) (h : ∀ n : ℕ, AdicCompletion.eval I M (n+1) x = AdicCompletion.eval I M (n+1) y) : x = y := by
  apply AdicCompletion.ext
  intro n
  cases n with
  | zero =>
    have hx := x.property (Nat.zero_le 1)
    have hy := y.property (Nat.zero_le 1)
    exact hx.symm.trans ((congrArg (AdicCompletion.transitionMap I M (Nat.zero_le 1)) (h 0)).trans hy)
  | succ n => exact h n

theorem positive_residues (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (f : ∀ n : ℕ, Residue I M (n+1))
    (hf : ∀ {m n : ℕ} (h : m ≤ n),
      AdicCompletion.transitionMap I M (Nat.add_le_add_right h 1) (f n) = f m) : (∃! x : Completion I M, ∀ n : ℕ, AdicCompletion.eval I M (n+1) x = f n) := by
  let g : ∀ n : ℕ, Residue I M n := fun n => match n with
    | 0 => 0
    | k+1 => f k
  have hg : ∀ {m n : ℕ} (h : m ≤ n), AdicCompletion.transitionMap I M h (g n) = g m := by
    intro m n h
    cases m with
    | zero =>
      have hz : Power I M 0 = ⊤ := by simp [Power]
      have : Subsingleton (Residue I M 0) := by
        change Subsingleton (M ⧸ Power I M 0)
        rw [hz]
        infer_instance
      exact Subsingleton.elim _ _
    | succ m =>
      cases n with
      | zero => omega
      | succ n => exact hf (Nat.le_of_succ_le_succ h)
  refine ⟨⟨g, hg⟩, fun n => rfl, ?_⟩
  intro y hy
  exact ext_positive R I M y ⟨g, hg⟩ hy

theorem canonical_kernel (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : LinearMap.ker (AdicCompletion.of I M) = ⨅ n : ℕ, Power I M n := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_iInf]
  constructor
  · intro h n
    have hn := congrArg (fun y : Completion I M => y.val n) h
    exact (Submodule.Quotient.mk_eq_zero _).mp hn
  · intro h
    apply AdicCompletion.ext
    intro n
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h n)

theorem map_coordinate (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (x : Completion I M) (n : ℕ) : AdicCompletion.eval I N n (AdicCompletion.map I f x) = f.reduceModIdeal (I ^ n) (AdicCompletion.eval I M n x) := by
  rfl

theorem map_canonical (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (x : M) : AdicCompletion.map I f (AdicCompletion.of I M x) = AdicCompletion.of I N (f x) := by
  exact AdicCompletion.map_of I f x

theorem map_identity (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : AdicCompletion.map I (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  exact AdicCompletion.map_id I M

theorem map_composition (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (P : Type z) [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) : (AdicCompletion.map I g).comp (AdicCompletion.map I f) = AdicCompletion.map I (g.comp f) := by
  exact AdicCompletion.map_comp I f g

theorem ring_canonical_coordinate (R : Type u) [CommRing R] (I : Ideal R) (r : R) (n : ℕ) : AdicCompletion.evalₐ I n (algebraMap R (Completion I R) r) = Ideal.Quotient.mk (I ^ n) r := by
  exact AdicCompletion.evalₐ_of I n r

theorem ring_mul_coordinate (R : Type u) [CommRing R] (I : Ideal R) (r s : Completion I R) (n : ℕ) : (r * s).val n = r.val n * s.val n := by
  rfl

theorem ring_one_coordinate (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ) : (1 : Completion I R).val n = 1 := by
  rfl

theorem scalar_coordinate (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (r : Completion I R) (x : Completion I M) (n : ℕ) : (r • x).val n = r.val n • x.val n := by
  rfl

theorem scalar_canonical (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (r : R) (x : M) : (algebraMap R (Completion I R) r) • AdicCompletion.of I M x = AdicCompletion.of I M (r • x) := by
  rw [IsScalarTower.algebraMap_smul (Completion I R) r (AdicCompletion.of I M x)]
  exact (AdicCompletion.of I M).map_smul r x |>.symm

theorem zeroIdealEquiv_canonical (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : M) : AdicCompletion.ofLinearEquiv (⊥ : Ideal R) M x = AdicCompletion.of ⊥ M x := by
  rfl

theorem topIdeal_subsingleton (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] : Subsingleton (Completion (⊤ : Ideal R) M) := by
  exact IsHausdorff.subsingleton (inferInstance : IsHausdorff (⊤ : Ideal R) (Completion ⊤ M))

theorem zeroModule_subsingleton (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M] : Subsingleton (Completion I M) := by
  constructor
  intro x y
  apply AdicCompletion.ext
  intro n
  exact Subsingleton.elim _ _

theorem zeroRing_subsingleton (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton R] : Subsingleton (Completion I M) := by
  have : Subsingleton M := Module.subsingleton R M
  exact zeroModule_subsingleton R I M

noncomputable def map (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : Completion I M →ₗ[R] Completion I N :=
  (AdicCompletion.map I f).restrictScalars R

theorem map_natural (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : ((AdicCompletion.map I f).restrictScalars R).comp (AdicCompletion.of I M) = (AdicCompletion.of I N).comp f := by
  rfl

theorem zeroIdealEquiv_natural (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (x : M) : AdicCompletion.map (⊥ : Ideal R) f (AdicCompletion.ofLinearEquiv ⊥ M x) = AdicCompletion.ofLinearEquiv ⊥ N (f x) := by
  rfl

theorem canonical_injective_iff (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Function.Injective (AdicCompletion.of I M) ↔ (⨅ n : ℕ, Power I M n) = ⊥ := by
  rw [← LinearMap.ker_eq_bot, canonical_kernel R I M]

theorem inverseLimit_universal (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (N : Type w) [AddCommGroup N] [Module R N] (f : ∀ n : ℕ, N →ₗ[R] Residue I M n)
    (hf : ∀ {m n : ℕ} (h : m ≤ n), (AdicCompletion.transitionMap I M h).comp (f n) = f m) : (∃! F : N →ₗ[R] Completion I M, ∀ n : ℕ, (AdicCompletion.eval I M n).comp F = f n) := by
  refine ⟨AdicCompletion.lift I f hf, fun n => rfl, ?_⟩
  intro F hF
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  exact DFunLike.congr_fun (hF n) x

end P103.Ch07.CompletionInterface
