import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.BrauerCharacterLaws
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.StableLattices
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.CharacterReduction

/-! Comparison of ordinary and Brauer characters via a stable integral lattice. -/

namespace RepTheorySurvey.Modular

open IsLocalRing (ResidueField)
open LinearMap Polynomial

private theorem charpoly_map_of_baseChange {R A M W : Type*}
    [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]
    [Module.Free A W] [Module.Finite A W]
    {f : M →ₗ[R] W} (h : IsBaseChange A f)
    (T : Module.End R M) (U : Module.End A W)
    (comm : ∀ x, U (f x) = f (T x)) :
    U.charpoly = T.charpoly.map (algebraMap R A) := by
  classical
  let b := Module.finBasis R M
  let c := h.basis b
  have matrix_eq : toMatrix c c U = (toMatrix b b T).map (algebraMap R A) := by
    ext i j
    rw [toMatrix_apply, Matrix.map_apply, toMatrix_apply, h.basis_apply b j, comm,
      h.basis_repr_comp_apply]
  rw [← charpoly_toMatrix U c, matrix_eq, Matrix.charpoly_map, charpoly_toMatrix]

set_option backward.isDefEq.respectTransparency false

private theorem charpoly_ofModule_asModule {F G W : Type*} [Field F] [Group G]
    [AddCommGroup W] [Module F W] [Module.Finite F W] (ρ : Representation F G W)
    [Module.Finite F (RestrictScalars F (MonoidAlgebra F G) ρ.asModule)] (g : G) :
    (Representation.ofModule (k := F) ρ.asModule g).charpoly = (ρ g).charpoly := by
  let e := MR04Spec.asModuleScalarEquiv ρ
  let T := Representation.ofModule (k := F) ρ.asModule g
  have h (x) : T x = e.symm (ρ g (e x)) := by
    exact Representation.ofModule_asModule_act ρ g x
  have he : e.conj T = ρ g := by
    ext x
    change e (T (e.symm x)) = _
    rw [h, e.apply_symm_apply, e.apply_symm_apply]
  rw [← he, LinearEquiv.charpoly_conj]

universe uG uO uK uV uU uN

section Reduction

variable {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K]
    (S : SplittingSystem G p O K)
    (V : Type uV) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)]

local notation "κ" => ResidueField O
local notation "kG" => MonoidAlgebra κ G
local notation "m" => primeToPart G p

omit [Finite G] [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)] in
/-- The reduction of a stable lattice is finite dimensional over the residue field. -/
theorem NativeStableLattice.finite_reduction (L : NativeStableLattice O K G V) :
    Module.Finite κ (RestrictScalars κ kG (NativeStableLattice.reduction L)) :=
  MR04Spec.nativeReductionFinite V L

/-- On regular elements, the Brauer character of any stable lattice reduction
equals the restriction of the ordinary character after embedding its values in the fraction field. -/
theorem brauerCharacter_reduction (L : NativeStableLattice O K G V) :
    letI := NativeStableLattice.finite_reduction V L
    ∀ g : PRegular G p,
      algebraMap O K (brauerCharacter S (NativeStableLattice.reduction L) g) = ordinaryCharacter (K := K) V g.val := by
  intro g
  classical
  let : IsFractionRing O K := S.fractionRing
  let W := RestrictScalars K (MonoidAlgebra K G) V
  let : Module O W := Module.restrictScalars O K W
  let := IsScalarTower.restrictScalars O K W
  let := L.finite
  let := L.free
  let : NeZero m := ⟨(primeToPart_pos G p).ne'⟩
  let := Fintype.ofFinite (rootsOfUnity m κ)
  let ρ := moduleRepresentation K G V
  let σ := integralLatticeAction O L
  let T := ρ g.val
  let A := σ g.val
  let M := NativeStableLattice.reduction L
  let : Module.Finite κ (RestrictScalars κ kG M) := NativeStableLattice.finite_reduction V L
  let U := moduleRepresentation κ G M g.val
  have hK : T.charpoly = A.charpoly.map (algebraMap O K) :=
    charpoly_map_of_baseChange (StableLattice.baseChange L) A T (fun _ => rfl)
  have hk : U.charpoly = A.charpoly.map (IsLocalRing.residue O) := by
    have he : U.charpoly = (residueRepresentation σ g.val).charpoly := by
      let : Module.Finite κ (RestrictScalars κ kG (residueRepresentation σ).asModule) :=
        Module.Finite.equiv (MR04Spec.asModuleScalarEquiv (residueRepresentation σ)).symm
      change (Representation.ofModule (k := κ) (residueRepresentation σ).asModule g.val).charpoly = _
      exact charpoly_ofModule_asModule (residueRepresentation σ) g.val
    rw [he]
    exact charpoly_map_of_baseChange (residue_baseChange L.carrier) A
      (residueRepresentation σ g.val) (residueRepresentation_reduce σ g.val)
  obtain ⟨_, b, eigenvalue, hb⟩ := fractionRegularEigenbasis S g V
  let d j := (eigenvalue j).val.val
  have hMatrix : toMatrix b b T = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, map_smul]
    by_cases h : i = j
    · subst i
      simp [d]
    · simp [Module.Basis.repr_self, d, h]
  have hsplit : T.charpoly = ∏ j, (X - C (d j)) := by
    rw [← charpoly_toMatrix T b, hMatrix, Matrix.charpoly_diagonal]
  let lift j := Classical.choose (fractionRoots_surjective S (eigenvalue j))
  have lift_map (j) : algebraMap O K (lift j).val.val = d j :=
    congrArg (fun v : rootsOfUnity m K => v.val.val)
      (Classical.choose_spec (fractionRoots_surjective S (eigenvalue j)))
  have hIntegral : A.charpoly = ∏ j, (X - C (lift j).val.val) := by
    apply Polynomial.map_injective (algebraMap O K) (IsFractionRing.injective O K)
    rw [← hK, hsplit]
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      lift_map]
  let ζ j := restrictRootsOfUnity (IsLocalRing.residue O) m (lift j)
  have hResidue : U.charpoly = ∏ j, (X - C (ζ j).val.val) := by
    rw [hk, hIntegral]
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hne : (∏ j, (X - C (ζ j).val.val)) ≠ 0 :=
    hResidue ▸ U.charpoly_monic.ne_zero
  have hmult (v : rootsOfUnity m κ) :
      U.charpoly.rootMultiplicity v.val.val = ∑ j, if v = ζ j then 1 else 0 := by
    rw [← count_roots, hResidue, roots_prod _ _ hne, Multiset.count_bind]
    change (∑ j, Multiset.count v.val.val (roots (X - C (ζ j).val.val))) = _
    simp only [roots_X_sub_C, Multiset.count_singleton, rootsOfUnity.coe_injective.eq_iff]
  have hlift (j) : residualRootLift S (ζ j) = lift j :=
    (residualRootsEquiv S).symm_apply_apply (lift j)
  change algebraMap O K (brauerCharacter S M g) = LinearMap.trace K W T
  rw [LinearMap.trace_eq_matrix_trace K b, hMatrix, Matrix.trace_diagonal]
  simp only [brauerCharacter, map_sum, map_nsmul,
    ← show U = moduleRepresentation κ G M g.val from rfl, hmult, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single (ζ j)]
  · simp [hlift, lift_map]
  · intro v _ hv
    simp [hv]
  · simp

/-- The lattice character comparison descends to regular conjugacy classes. -/
theorem brauerClassCharacter_reduction (L : NativeStableLattice O K G V) :
    letI := NativeStableLattice.finite_reduction V L
    ∀ c : PRegularConjClasses G p,
      algebraMap O K (brauerClassCharacter S (NativeStableLattice.reduction L) c) =
        ordinaryClassCharacter (K := K) V c.val := by
  intro c
  let := NativeStableLattice.finite_reduction V L
  obtain ⟨g, rfl⟩ := pRegularConjClass_surjective c
  rw [brauerClassCharacter_apply S (NativeStableLattice.reduction L) g]
  exact brauerCharacter_reduction S V L g

end Reduction

/-- Brauer characters satisfy the character laws of MR04, and every ordinary module
has a stable lattice whose character comparison holds for every choice of lattice. -/
theorem brauerCharacters_and_stableLattices :
    MR04Spec.brauerCharactersAndStableLattices.{uG, uO, uK, uV, uU, uN} := by
  refine ⟨?_, ?_, ?_⟩
  · intro G _ _ p O _ _ _ K _ _ S M _ _ _ g h hgh
    exact brauerCharacter_eq_of_isConj S M hgh
  · intro G _ _ p O _ _ _ K _ _ S U _ _ _ M _ _ _ N _ _ _ i q hi hq hex g
    exact brauerCharacter_add_of_exact S U M N i q hi hq hex g
  · intro G _ _ p O _ _ _ K _ _ S V _ _ _
    exact ⟨exists_nativeStableLattice S V, brauerCharacter_reduction S V⟩

end RepTheorySurvey.Modular
