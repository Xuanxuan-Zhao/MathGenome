import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.StandardIndependence
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.Straightening
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardBasisRationalModel
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
open scoped BigOperators TensorProduct
namespace AdvancedFiniteGroupRepresentations

abbrev RationalPermutationModule := @Specs.AdvancedFiniteGroupRepresentations.RationalPermutationModule
abbrev rationalPermutationRepresentation := @Specs.AdvancedFiniteGroupRepresentations.rationalPermutationRepresentation
abbrev rationalPolytabloid := @Specs.AdvancedFiniteGroupRepresentations.rationalPolytabloid
abbrev rationalSpechtSpan := @Specs.AdvancedFiniteGroupRepresentations.rationalSpechtSpan
abbrev RationalSpechtModule := @Specs.AdvancedFiniteGroupRepresentations.RationalSpechtModule
abbrev rationalEmbedding := @Specs.AdvancedFiniteGroupRepresentations.rationalEmbedding

variable {n : ℕ} {p : Partition n}

/-- The complex basis is the independent standard family, transported along
its already proved equality of spans with the original Specht submodule. -/
def standardBasis (p : Partition n) : Module.Basis (StandardTableau p) ℂ (SpechtModule p) :=
  (Module.Basis.span (standard_polytabloids_linearIndependent p)).map
    (LinearEquiv.ofEq _ _ (standardPolytabloids_span p))

@[simp] theorem standardBasis_val (p : Partition n) (t : StandardTableau p) :
    (standardBasis p t).val = polytabloid t.val := by
  simp only [standardBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

theorem standard_basis (p : Partition n) :
    ∃ b : Module.Basis (StandardTableau p) ℂ (SpechtModule p),
      ∀ t, (b t).val = polytabloid t.val :=
  ⟨standardBasis p, standardBasis_val p⟩

theorem specht_finrank (p : Partition n) :
    Module.finrank ℂ (SpechtModule p) = standardTableauCount p :=
  Module.finrank_eq_nat_card_basis (standardBasis p)

@[simp] theorem rationalEmbedding_apply (v : RationalPermutationModule p) (q : Tabloid p) :
    (rationalEmbedding p v).coeff q = (v.coeff q : ℂ) := rfl

theorem rationalEmbedding_injective (p : Partition n) :
    Function.Injective (rationalEmbedding p) := by
  intro v w h
  ext q
  exact Rat.cast_injective (congrArg (fun x : PermutationModule p => x.coeff q) h)

@[simp] theorem rationalEmbedding_polytabloid (t : Tableau p) :
    rationalEmbedding p (rationalPolytabloid t) = polytabloid t := by
  classical
  rw [polytabloid_sum]
  simp only [rationalPolytabloid, Specs.AdvancedFiniteGroupRepresentations.rationalPolytabloid,
    map_sum]
  apply Finset.sum_congr rfl
  intro c _
  ext q
  simp [rationalEmbedding_apply, Finsupp.single_apply, permutationSign, tabloid,
    Specs.AdvancedFiniteGroupRepresentations.permutationSign, apply_ite, Rat.cast_intCast, Rat.cast_zero]
  intro h hn
  exact (hn h).elim

/-- A rational-linear retraction of the scalar embedding fixes all rational
coordinates. It need not preserve complex multiplication. -/
private def scalarRetraction : ℂ →ₗ[ℚ] ℚ := (Algebra.linearMap ℚ ℂ).leftInverse

private theorem scalarRetraction_cast (a : ℚ) : scalarRetraction (a : ℂ) = a := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective ℚ ℂ)) a

private def coefficientRetraction (p : Partition n) :
    PermutationModule p →ₗ[ℚ] RationalPermutationModule p :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap scalarRetraction).comp
      ((MonoidAlgebra.coeffLinearEquiv ℂ).restrictScalars ℚ).toLinearMap)

private theorem coefficientRetraction_smul (z : ℂ) (v : RationalPermutationModule p) :
    coefficientRetraction p (z • rationalEmbedding p v) = scalarRetraction z • v := by
  ext q
  change scalarRetraction (z * (v.coeff q : ℂ)) = scalarRetraction z * v.coeff q
  calc
    _ = scalarRetraction (v.coeff q • z) := by rw [Algebra.smul_def]; congr 1; exact mul_comm _ _
    _ = v.coeff q • scalarRetraction z := map_smul _ _ _
    _ = _ := by simp [smul_eq_mul, mul_comm]

private theorem coefficientRetraction_embedding (v : RationalPermutationModule p) :
    coefficientRetraction p (rationalEmbedding p v) = v := by
  ext q
  exact scalarRetraction_cast (v.coeff q)

theorem rational_polytabloid_straightening (t : Tableau p) :
    rationalPolytabloid t ∈ Submodule.span ℚ
      (Set.range (fun u : StandardTableau p => rationalPolytabloid u.val)) := by
  obtain ⟨s,a,ha⟩ := polytabloid_linearCombination t
  have hh := congrArg (coefficientRetraction p) ha
  simp only [← rationalEmbedding_polytabloid, map_sum,
    coefficientRetraction_smul, coefficientRetraction_embedding] at hh
  rw [hh]
  apply Submodule.sum_mem
  intro u hu
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u,rfl⟩)

theorem rational_standard_independent (p : Partition n) :
    LinearIndependent ℚ (fun t : StandardTableau p => rationalPolytabloid t.val) := by
  apply LinearIndependent.of_comp (rationalEmbedding p)
  simpa only [Function.comp_def, rationalEmbedding_polytabloid] using
    (standard_polytabloids_linearIndependent p).restrict_scalars' ℚ

theorem rational_standard_span (p : Partition n) :
    Submodule.span ℚ (Set.range (fun t : StandardTableau p => rationalPolytabloid t.val)) =
      rationalSpechtSpan p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact Submodule.subset_span ⟨t.val,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact rational_polytabloid_straightening t

def rationalStandardBasis (p : Partition n) :
    Module.Basis (StandardTableau p) ℚ (RationalSpechtModule p) :=
  (Module.Basis.span (rational_standard_independent p)).map
    (LinearEquiv.ofEq _ _ (rational_standard_span p))

@[simp] theorem rationalStandardBasis_val (p : Partition n) (t : StandardTableau p) :
    (rationalStandardBasis p t).val = rationalPolytabloid t.val := by
  simp only [rationalStandardBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

theorem rational_standard_basis (p : Partition n) :
    ∃ b : Module.Basis (StandardTableau p) ℚ (RationalSpechtModule p),
      ∀ t, (b t).val = rationalPolytabloid t.val :=
  ⟨rationalStandardBasis p, rationalStandardBasis_val p⟩

theorem rational_specht_finrank (p : Partition n) :
    Module.finrank ℚ (RationalSpechtModule p) = standardTableauCount p :=
  Module.finrank_eq_nat_card_basis (rationalStandardBasis p)


/-- Coefficient extension commutes with the permutation action on tabloids. -/
theorem rationalEmbedding_equivariant (g : SymmetricGroup n) (v : RationalPermutationModule p) :
    rationalEmbedding p (rationalPermutationRepresentation p g v) =
      permutationRepresentation p g (rationalEmbedding p v) := by
  ext q
  simp [rationalPermutationRepresentation,
    Specs.AdvancedFiniteGroupRepresentations.rationalPermutationRepresentation,
    permutationRepresentation, Specs.AdvancedFiniteGroupRepresentations.permutationRepresentation,
    Representation.coeff_ofMulAction, rationalEmbedding_apply]

theorem rationalPolytabloid_equivariant (g : SymmetricGroup n) (t : Tableau p) :
    rationalPermutationRepresentation p g (rationalPolytabloid t) = rationalPolytabloid (g • t) := by
  apply rationalEmbedding_injective p
  rw [rationalEmbedding_equivariant, rationalEmbedding_polytabloid,
    polytabloid_equivariant, rationalEmbedding_polytabloid]

theorem rational_specht_stable (g : SymmetricGroup n) (v : RationalPermutationModule p)
    (hv : v ∈ rationalSpechtSpan p) :
    rationalPermutationRepresentation p g v ∈ rationalSpechtSpan p := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t,rfl⟩ := hv
    rw [rationalPolytabloid_equivariant]
    exact Submodule.subset_span ⟨g • t,rfl⟩
  | zero => simp
  | add v w hv hw ihv ihw => simpa using (rationalSpechtSpan p).add_mem ihv ihw
  | smul z v hv ih => simpa using (rationalSpechtSpan p).smul_mem z ih

def rationalSpechtSubrepresentation (p : Partition n) :
    Subrepresentation (rationalPermutationRepresentation p) where
  toSubmodule := rationalSpechtSpan p
  apply_mem_toSubmodule g v hv := rational_specht_stable g v hv

def rationalSpechtRepresentation (p : Partition n) :
    Representation ℚ (SymmetricGroup n) (RationalSpechtModule p) :=
  (rationalSpechtSubrepresentation p).toRepresentation

def complexSpechtRepresentation (p : Partition n) :
    Representation ℂ (SymmetricGroup n) (SpechtModule p) :=
  (spechtSubrepresentation p).toRepresentation

theorem rationalEmbedding_mem (v : RationalPermutationModule p) (hv : v ∈ rationalSpechtSpan p) :
    rationalEmbedding p v ∈ spechtSpan p := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t,rfl⟩ := hv
    rw [rationalEmbedding_polytabloid]
    exact polytabloid_mem_specht t
  | zero => simp
  | add v w hv hw ihv ihw => simpa using (spechtSpan p).add_mem ihv ihw
  | smul z v hv ih =>
    rw [map_smul]
    exact (spechtSpan p).smul_mem z ih

/-- The rational model sits in the original complex Specht module by extending
its tabloid coefficients. -/
def rationalSpechtEmbedding (p : Partition n) :
    RationalSpechtModule p →ₗ[ℚ] SpechtModule p :=
  ((rationalEmbedding p).comp (rationalSpechtSpan p).subtype).codRestrict
    ((spechtSpan p).restrictScalars ℚ) (fun v => rationalEmbedding_mem v.val v.property)

@[simp] theorem rationalSpechtEmbedding_val (v : RationalSpechtModule p) :
    (rationalSpechtEmbedding p v).val = rationalEmbedding p v.val := rfl

@[simp] theorem rationalSpechtEmbedding_basis (t : StandardTableau p) :
    rationalSpechtEmbedding p (rationalStandardBasis p t) = standardBasis p t := by
  apply Subtype.ext
  simp

/-- Matching standard bases yields an isomorphism after extension of scalars. -/
def complexificationEquiv (p : Partition n) :
    (ℂ ⊗[ℚ] RationalSpechtModule p) ≃ₗ[ℂ] SpechtModule p :=
  ((rationalStandardBasis p).baseChange ℂ).equiv (standardBasis p) (Equiv.refl _)

/-- It agrees with the canonical extension of the coefficient embedding. -/
theorem complexificationEquiv_eq_lift (p : Partition n) :
    (complexificationEquiv p).toLinearMap = (rationalSpechtEmbedding p).liftBaseChange ℂ := by
  apply ((rationalStandardBasis p).baseChange ℂ).ext
  intro t
  change (((rationalStandardBasis p).baseChange ℂ).equiv (standardBasis p) (Equiv.refl _))
    (((rationalStandardBasis p).baseChange ℂ) t) = _
  rw [Module.Basis.equiv_apply]
  simp

@[simp] theorem complexificationEquiv_tmul (z : ℂ) (v : RationalSpechtModule p) :
    (complexificationEquiv p (z ⊗ₜ[ℚ] v)).val = z • rationalEmbedding p v.val := by
  change ((complexificationEquiv p).toLinearMap (z ⊗ₜ[ℚ] v)).val = _
  rw [complexificationEquiv_eq_lift, LinearMap.liftBaseChange_tmul]
  rfl

theorem complexificationEquiv_equivariant (g : SymmetricGroup n)
    (x : ℂ ⊗[ℚ] RationalSpechtModule p) :
    complexificationEquiv p
      ((rationalSpechtRepresentation p g).baseChange ℂ x) =
    complexSpechtRepresentation p g (complexificationEquiv p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    apply Subtype.ext
    change (complexificationEquiv p
      ((rationalSpechtRepresentation p g).baseChange ℂ (z ⊗ₜ[ℚ] v))).val =
      permutationRepresentation p g (complexificationEquiv p (z ⊗ₜ[ℚ] v)).val
    rw [LinearMap.baseChange_tmul, complexificationEquiv_tmul,
      complexificationEquiv_tmul, map_smul]
    exact congrArg (z • ·) (rationalEmbedding_equivariant g v.val)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- FR-B03: the actual rational tabloid span, with its inherited action,
complexifies equivariantly to the original complex Specht module. -/
theorem rational_model (p : Partition n) :
    ∃ (ρQ : Representation ℚ (SymmetricGroup n) (RationalSpechtModule p))
      (ρC : Representation ℂ (SymmetricGroup n) (SpechtModule p))
      (e : (ℂ ⊗[ℚ] RationalSpechtModule p) ≃ₗ[ℂ] SpechtModule p),
      (∀ g v, (ρQ g v).val = rationalPermutationRepresentation p g v.val) ∧
      (∀ g v, (ρC g v).val = permutationRepresentation p g v.val) ∧
      (∀ z v, (e (z ⊗ₜ[ℚ] v)).val = z • rationalEmbedding p v.val) ∧
      (∀ g x, e ((ρQ g).baseChange ℂ x) = ρC g (e x)) := by
  exact ⟨rationalSpechtRepresentation p,
    complexSpechtRepresentation p, complexificationEquiv p,
    (fun _ _ => rfl), (fun _ _ => rfl), complexificationEquiv_tmul,
    complexificationEquiv_equivariant⟩

end AdvancedFiniteGroupRepresentations
