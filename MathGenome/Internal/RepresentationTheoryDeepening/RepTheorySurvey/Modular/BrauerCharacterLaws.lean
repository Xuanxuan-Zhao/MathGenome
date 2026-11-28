import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.Characters
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.RegularOperators
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.Roots

/-! Additivity and residue-field reduction of Brauer characters. -/

namespace RepTheorySurvey.Modular

open LinearMap Polynomial
open IsLocalRing (ResidueField)

universe uG uO uK uU uM uN

private theorem charpoly_mul_of_exact {F U M N : Type*} [Field F]
    [AddCommGroup U] [Module F U] [Module.Finite F U]
    [AddCommGroup M] [Module F M] [Module.Finite F M]
    [AddCommGroup N] [Module F N] [Module.Finite F N]
    {i : U →ₗ[F] M} {q : M →ₗ[F] N}
    (hi : Function.Injective i) (hq : Function.Surjective q) (hex : Function.Exact i q)
    (A : Module.End F U) (B : Module.End F M) (C : Module.End F N)
    (hiB : ∀ u, i (A u) = B (i u)) (hqB : ∀ x, q (B x) = C (q x)) :
    B.charpoly = A.charpoly * C.charpoly := by
  classical
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  obtain ⟨e, he₁, he₂⟩ := hex.splitSurjectiveEquiv hi ⟨s, hs⟩
  have he₁' (u : U) : e (i u) = (u, 0) := by rw [he₁]; simp
  have he₂' (x : M) : (e x).2 = q x := by rw [he₂]; rfl
  let T := e.conj B
  have hinl (u : U) : T (u, 0) = (A u, 0) := by
    change e (B (e.symm (u, 0))) = _
    rw [← he₁' u, e.symm_apply_apply, ← hiB, he₁']
  have hsnd (x : U × N) : (T x).2 = C x.2 := by
    change (e (B (e.symm x))).2 = _
    rw [he₂', hqB, ← he₂', e.apply_symm_apply]
  let bU := Module.finBasis F U
  let bN := Module.finBasis F N
  let b := bU.prod bN
  let upperRight := Matrix.of fun j l => bU.repr (T (0, bN l)).1 j
  have hm : toMatrix b b T =
      Matrix.fromBlocks (toMatrix bU bU A) upperRight 0 (toMatrix bN bN C) := by
    ext j l
    cases j <;> cases l <;> simp [b, toMatrix_apply, hinl, hsnd, upperRight]
  rw [← e.charpoly_conj B, ← charpoly_toMatrix T b, hm, Matrix.charpoly_fromBlocks_zero₂₁,
    charpoly_toMatrix, charpoly_toMatrix]

variable {G : Type uG} [Group G]

set_option backward.isDefEq.respectTransparency false

/-- Ordinary characters have equal values on conjugate elements. -/
theorem ordinaryCharacter_eq_of_isConj {K : Type uK} [Field K]
    (V : Type uM) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)] {g h : G}
    (hgh : IsConj g h) : ordinaryCharacter (K := K) V g = ordinaryCharacter (K := K) V h := by
  obtain ⟨a, rfl⟩ := isConj_iff.mp hgh
  exact ((moduleRepresentation K G V).char_conj g a).symm

section Brauer

variable [Finite G] {p : ℕ}
  {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K]

local notation "k" => ResidueField O
local notation "kG" => MonoidAlgebra k G
local notation "m" => primeToPart G p
local notation "Vₖ" => RestrictScalars k kG

variable (S : SplittingSystem G p O K)

/-- The Brauer character is constant on each p-regular conjugacy class. -/
theorem brauerCharacter_eq_of_same_class
    (M : Type uM) [AddCommGroup M] [Module kG M] [Module.Finite k (Vₖ M)]
    {g h : PRegular G p} (hgh : pRegularConjClass g = pRegularConjClass h) :
    brauerCharacter S M g = brauerCharacter S M h :=
  brauerCharacter_eq_of_isConj S M
    (ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val hgh))

attribute [local instance] RestrictScalars.moduleOrig

omit [Finite G] in
private theorem intertwines_moduleRepresentation
    {F : Type*} [Field F] {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (MonoidAlgebra F G) V] [Module (MonoidAlgebra F G) W]
    (f : V →ₗ[MonoidAlgebra F G] W) (g : G)
    (v : RestrictScalars F (MonoidAlgebra F G) V) :
    f (moduleRepresentation F G V g v) =
      moduleRepresentation F G W g (f v) := by
  simp only [← Representation.asAlgebraHom_of, Representation.ofModule_asAlgebraHom_apply_apply]
  exact f.map_smul (MonoidAlgebra.of F G g) v

/-- A short exact sequence of residue-field representations gives a sum of Brauer characters. -/
theorem brauerCharacter_add_of_exact
    (U : Type uU) [AddCommGroup U] [Module kG U] [Module.Finite k (Vₖ U)]
    (M : Type uM) [AddCommGroup M] [Module kG M] [Module.Finite k (Vₖ M)]
    (N : Type uN) [AddCommGroup N] [Module kG N] [Module.Finite k (Vₖ N)]
    (i : U →ₗ[kG] M) (q : M →ₗ[kG] N)
    (hi : Function.Injective i) (hq : Function.Surjective q) (hex : Function.Exact i q)
    (g : PRegular G p) :
    brauerCharacter S M g = brauerCharacter S U g + brauerCharacter S N g := by
  let i' : Vₖ U →ₗ[k] Vₖ M := (show Vₖ U →ₗ[kG] Vₖ M from i).restrictScalars k
  let q' : Vₖ M →ₗ[k] Vₖ N := (show Vₖ M →ₗ[kG] Vₖ N from q).restrictScalars k
  let A := moduleRepresentation k G U g.val
  let B := moduleRepresentation k G M g.val
  let C := moduleRepresentation k G N g.val
  have hp : B.charpoly = A.charpoly * C.charpoly :=
    charpoly_mul_of_exact (i := i') (q := q') hi hq hex A B C
      (intertwines_moduleRepresentation i g.val) (intertwines_moduleRepresentation q g.val)
  have hne : A.charpoly * C.charpoly ≠ 0 :=
    mul_ne_zero A.charpoly_monic.ne_zero C.charpoly_monic.ne_zero
  simp only [brauerCharacter, ← show B = moduleRepresentation k G M g.val from rfl,
    ← show A = moduleRepresentation k G U g.val from rfl,
    ← show C = moduleRepresentation k G N g.val from rfl,
    hp, rootMultiplicity_mul hne, add_nsmul, Finset.sum_add_distrib]

/-- Additivity of Brauer characters as functions on the regular conjugacy classes. -/
theorem brauerClassCharacter_add_of_exact
    (U : Type uU) [AddCommGroup U] [Module kG U] [Module.Finite k (Vₖ U)]
    (M : Type uM) [AddCommGroup M] [Module kG M] [Module.Finite k (Vₖ M)]
    (N : Type uN) [AddCommGroup N] [Module kG N] [Module.Finite k (Vₖ N)]
    (i : U →ₗ[kG] M) (q : M →ₗ[kG] N)
    (hi : Function.Injective i) (hq : Function.Surjective q) (hex : Function.Exact i q) :
    brauerClassCharacter S M = brauerClassCharacter S U + brauerClassCharacter S N := by
  funext c
  obtain ⟨g, rfl⟩ := pRegularConjClass_surjective c
  simpa only [Pi.add_apply, brauerClassCharacter_apply] using
    brauerCharacter_add_of_exact S U M N i q hi hq hex g

/-- Reducing the Brauer character gives the residue-field trace of the action. -/
theorem residue_brauerCharacter
    (M : Type uM) [AddCommGroup M] [Module kG M] [Module.Finite k (Vₖ M)]
    (g : PRegular G p) :
    IsLocalRing.residue O (brauerCharacter S M g) =
      LinearMap.trace k (Vₖ M) (moduleRepresentation k G M g.val) := by
  classical
  let : NeZero m := ⟨(primeToPart_pos G p).ne'⟩
  let := Fintype.ofFinite (rootsOfUnity m k)
  let T := moduleRepresentation k G M g.val
  obtain ⟨_, b, eigenvalue, hb⟩ := residueRegularEigenbasis S g M
  let d j := (eigenvalue j).val.val
  have hMatrix : toMatrix b b T = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, map_smul]
    by_cases h : i = j
    · subst i
      simp [d]
    · simp [Module.Basis.repr_self, d, h]
  have hp : T.charpoly = ∏ j, (X - C (d j)) := by
    rw [← charpoly_toMatrix T b, hMatrix, Matrix.charpoly_diagonal]
  have hne : (∏ j, (X - C (d j))) ≠ 0 := hp ▸ T.charpoly_monic.ne_zero
  have hmult (ζ : rootsOfUnity m k) :
      T.charpoly.rootMultiplicity ζ.val.val = ∑ j, if ζ = eigenvalue j then 1 else 0 := by
    rw [← count_roots, hp, roots_prod _ _ hne, Multiset.count_bind]
    change (∑ j, Multiset.count ζ.val.val (roots (X - C (d j)))) = _
    simp only [roots_X_sub_C, Multiset.count_singleton, d, rootsOfUnity.coe_injective.eq_iff]
  have hlift (ζ : rootsOfUnity m k) :
      IsLocalRing.residue O (residualRootLift S ζ).val.val = ζ.val.val :=
    congrArg (fun v : rootsOfUnity m k => v.val.val) (reduce_residualRootLift S ζ)
  change IsLocalRing.residue O (brauerCharacter S M g) = LinearMap.trace k (Vₖ M) T
  rw [LinearMap.trace_eq_matrix_trace k b, hMatrix, Matrix.trace_diagonal]
  simp only [brauerCharacter, map_sum, map_nsmul, hlift,
    ← show T = moduleRepresentation k G M g.val from rfl, hmult, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single (eigenvalue j)]
  · simp [d]
  · intro ζ _ hζ
    simp [hζ]
  · simp

/-- Reduction of the Brauer character on conjugacy classes recovers the modular trace there. -/
theorem residue_brauerClassCharacter
    (M : Type uM) [AddCommGroup M] [Module kG M] [Module.Finite k (Vₖ M)]
    (c : PRegularConjClasses G p) :
    IsLocalRing.residue O (brauerClassCharacter S M c) =
      ordinaryClassCharacter (K := k) M c.val := by
  obtain ⟨g, rfl⟩ := pRegularConjClass_surjective c
  rw [brauerClassCharacter_apply, residue_brauerCharacter S M]
  rfl

end Brauer

end RepTheorySurvey.Modular
