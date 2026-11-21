import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.PolynomialHomogeneousDecomposition
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SchurWeylDuality
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.LengthBound
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.PolynomialClassification

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct
open Module
universe u v
namespace AdvancedFiniteGroupRepresentations

abbrev tensorImageElement := @Specs.AdvancedFiniteGroupRepresentations.tensorImageElement

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Coordinates of the actual diagonal tensor action, including n = 0. -/
theorem diagonal_tensor_matrix {d : ℕ} (b : Basis (Fin d) ℂ V)
    (n : ℕ) (g : LinearGroup V) (a z : Fin n → Fin d) :
    LinearMap.toMatrix (Basis.piTensorProduct (fun _ : Fin n => b))
      (Basis.piTensorProduct (fun _ : Fin n => b)) (diagonalOperator V n g) a z =
      ∏ j, matrixCoordinates b g (a j, z j) := by
  classical
  rw [LinearMap.toMatrix_apply, Basis.piTensorProduct_apply]
  change (Basis.piTensorProduct (fun _ : Fin n => b)).repr
    (diagonalOperator V n g (pureTensor V n (fun j => b (z j)))) a = _
  rw [diagonal_pureTensor]
  change (Basis.piTensorProduct (fun _ : Fin n => b)).repr
    (PiTensorProduct.tprod ℂ (fun j => g (b (z j)))) a = _
  rw [Basis.piTensorProduct_repr_tprod_apply]
  simp only [matrixCoordinates, Specs.AdvancedFiniteGroupRepresentations.matrixCoordinates,
    LinearMap.toMatrix_apply, LinearEquiv.coe_coe]

/-- Fixed inclusions and retractions preserve homogeneous matrix entries.
The ambient basis may have any finite index type. -/
theorem homogeneous_entries_sandwich {X : Type*} {W : Type v}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup W] [Module ℂ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d m : ℕ}
    (b : Basis (Fin d) ℂ V) (a : Basis ι ℂ X) (c : Basis (Fin m) ℂ W)
    (R : LinearGroup V → Module.End ℂ X) (n : ℕ)
    (h : ∀ i j, ∃ p : MvPolynomial (Fin d × Fin d) ℂ,
      p.IsHomogeneous n ∧ ∀ g, MvPolynomial.eval (matrixCoordinates b g) p =
        LinearMap.toMatrix a a (R g) i j)
    (ιW : W →ₗ[ℂ] X) (π : X →ₗ[ℂ] W) :
    ∀ i j, ∃ p : MvPolynomial (Fin d × Fin d) ℂ,
      p.IsHomogeneous n ∧ ∀ g, MvPolynomial.eval (matrixCoordinates b g) p =
        LinearMap.toMatrix c c (π.comp ((R g).comp ιW)) i j := by
  classical
  choose p hp heval using h
  intro i j
  refine ⟨∑ k : ι, ∑ l : ι,
    MvPolynomial.C (LinearMap.toMatrix a c π i k) *
      (p k l * MvPolynomial.C (LinearMap.toMatrix c a ιW l j)), ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro k _
    apply MvPolynomial.IsHomogeneous.sum
    intro l _
    apply MvPolynomial.IsHomogeneous.C_mul
    simpa only [add_zero] using (hp k l).mul (MvPolynomial.isHomogeneous_C _ _)
  · intro g
    simp only [map_sum, map_mul, MvPolynomial.eval_C, heval,
      LinearMap.toMatrix_comp c a c, LinearMap.toMatrix_comp c a a,
      Matrix.mul_apply, Finset.mul_sum]

/-- Any equivariant subspace embedded in the tensor power inherits degree-n
polynomial entries. No irreducibility is needed for this argument. -/
theorem tensor_subspace_homogeneous {W : Type v} [AddCommGroup W] [Module ℂ W]
    {d m : ℕ} (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (n : ℕ) (ρ : Representation ℂ (LinearGroup V) W)
    (ιW : W →ₗ[ℂ] TensorPower V n) (hinj : Function.Injective ιW)
    (hequiv : ∀ g w, ιW (ρ g w) = diagonalOperator V n g (ιW w)) :
    IsHomogeneousRepresentation b c ρ n := by
  classical
  let a := Basis.piTensorProduct (fun _ : Fin n => b)
  have hentries : ∀ i j, ∃ p : MvPolynomial (Fin d × Fin d) ℂ,
      p.IsHomogeneous n ∧ ∀ g, MvPolynomial.eval (matrixCoordinates b g) p =
        LinearMap.toMatrix a a (diagonalOperator V n g) i j := by
    intro i j
    refine ⟨∏ k : Fin n, MvPolynomial.X (i k, j k), ?_, ?_⟩
    · simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
        (fun k : Fin n => (MvPolynomial.X (i k, j k) : MvPolynomial (Fin d × Fin d) ℂ))
        (fun _ => 1) (fun _ _ => MvPolynomial.isHomogeneous_X _ _)
    · intro g
      rw [diagonal_tensor_matrix b]
      simp
  let π := ιW.leftInverse
  have hπ : ∀ w, π (ιW w) = w :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hinj)
  have heq : ∀ g, π.comp ((diagonalOperator V n g).comp ιW) = ρ g := by
    intro g
    ext w
    simpa only [LinearMap.comp_apply, ← hequiv] using hπ (ρ g w)
  intro i j
  obtain ⟨p, hp, he⟩ := homogeneous_entries_sandwich b a c
    (diagonalOperator V n) n hentries ιW π i j
  exact ⟨p, hp, fun g => by rw [he g, heq]⟩

/-- Evaluation at a fixed nonzero Specht vector embeds the multiplicity space
into the tensor power, as follows from the canonical evaluation isomorphism. -/
theorem multiplicity_evaluation_injective [FiniteDimensional ℂ V]
    {n : ℕ} (p : Partition n) (s : SpechtModule p) (hs : s ≠ 0) :
    Function.Injective (fun f : TensorMultiplicity V p => f.val s) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hs
  intro f h he
  have ht : s ⊗ₜ[ℂ] f = s ⊗ₜ[ℂ] h := by
    apply evaluationInclusion_injective V p
    simpa using he
  have := congrArg (tensorContractLeft φ) ht
  simpa [hφ] using this

/-- Every canonical multiplicity representation has homogeneous polynomial
matrix entries in every basis. -/
theorem tensorMultiplicity_homogeneous :
    Specs.AdvancedFiniteGroupRepresentations.tensorMultiplicity_homogeneousType.{u} := by
  intro V _ _ _ d b n p m c
  let s : SpechtModule p := ⟨polytabloid (canonicalTableau p), polytabloid_mem_specht _⟩
  have hs : s ≠ 0 := by
    intro hz
    exact polytabloid_ne_zero _ (congrArg Subtype.val hz)
  let ιW : TensorMultiplicity V p →ₗ[ℂ] TensorPower V n :=
    { toFun := fun f => f.val s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply tensor_subspace_homogeneous b c n (tensorMultiplicityRepresentation V p) ιW
    (multiplicity_evaluation_injective p s hs)
  intro g f
  rfl

/-- The nonzero canonical polynomial simple objects satisfy precisely the
length cutoff from Schur–Weyl duality. -/
theorem canonical_polynomial_simple :
    Specs.AdvancedFiniteGroupRepresentations.canonical_polynomial_simpleType.{u} := by
  intro V _ _ _ d b n p hp
  have hd : Module.finrank ℂ V = d := by simpa using Module.finrank_eq_card_basis b
  have hn : Nontrivial (TensorMultiplicity V p) :=
    (tensorMultiplicity_nonzero_iff V p).mpr (hd ▸ hp)
  letI := hn
  exact ⟨hn, tensorMultiplicity_irreducible V p,
    fun m c => tensorMultiplicity_homogeneous V d b p m c⟩

/-- Distinct shapes below the length cutoff give nonisomorphic polynomial
simple objects. -/
theorem canonical_polynomial_nonisomorphic :
    Specs.AdvancedFiniteGroupRepresentations.canonical_polynomial_nonisomorphicType.{u} := by
  intro V _ _ _ d b n p q hp hq hpq
  letI := (canonical_polynomial_simple V d b p hp).1
  letI := (canonical_polynomial_simple V d b q hq).1
  exact tensorMultiplicity_nonisomorphic V p q hpq

/-- Arbitrary matrix-entry polynomial representations split into homogeneous
degrees, with the full invariant-subspace and zero-dimensional conclusions. -/
theorem polynomial_homogeneous_splitting :
    Specs.AdvancedFiniteGroupRepresentations.polynomial_homogeneous_splittingType.{u,v} := by
  intro V W _ _ _ _ _ d m b c ρ h
  exact homogeneous_decomposition b c ρ h

/-- The empty multiplicity is the trivial line; in dimension zero every
positive-degree homogeneous representation has zero underlying space. -/
theorem zero_dimension_polynomial_boundary :
    Specs.AdvancedFiniteGroupRepresentations.zero_dimension_polynomial_boundaryType.{u,v} := by
  intro V _ _
  refine ⟨tensorMultiplicity_empty_line V, ?_⟩
  intro W _ _ m b c ρ
  exact ⟨zero_dimension_degree_zero b c ρ,
    fun n hn h => zero_dimension_no_positive_degree b c ρ n hn h⟩

/-- A degree-n monomial is a product indexed by a word of length n.
This includes the empty word and does not require any variables to exist. -/
theorem monomial_word {σ : Type*} (s : σ →₀ ℕ) (n : ℕ)
    (h : s.sum (fun _ k => k) = n) :
    ∃ w : Fin n → σ, ∀ x : σ → ℂ,
      s.prod (fun a k => x a ^ k) = ∏ j, x (w j) := by
  classical
  let l := s.toMultiset.toList
  have hl : l.length = n := by
    simp [l, Finsupp.card_toMultiset, Function.id_def, h]
  rw [← hl]
  refine ⟨l.get, ?_⟩
  intro x
  calc
    s.prod (fun a k => x a ^ k) = (s.toMultiset.map x).prod := by
      rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset]
      rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add ..)]
    _ = (l.map x).prod := (Multiset.prod_map_toList _ _).symm
    _ = ∏ j, x (l.get j) := by
      simpa only [List.map_ofFn, Fin.prod_ofFn, Function.comp_def] using
        congrArg (fun t : List σ => (t.map x).prod) (List.ofFn_get l).symm

/-- Homogeneous polynomials on group matrices are linear functionals of the
actual tensor operator, rather than of a freely presented algebra. -/
theorem homogeneous_tensor_functional {d n : ℕ} (b : Basis (Fin d) ℂ V)
    (p : MvPolynomial (Fin d × Fin d) ℂ) (hp : p.IsHomogeneous n) :
    ∃ L : Module.End ℂ (TensorPower V n) →ₗ[ℂ] ℂ,
      ∀ g, L (diagonalOperator V n g) = MvPolynomial.eval (matrixCoordinates b g) p := by
  classical
  have hex (s : {s // s ∈ p.support}) : ∃ w : Fin n → Fin d × Fin d,
      ∀ x : (Fin d × Fin d) → ℂ, s.val.prod (fun a k => x a ^ k) = ∏ j, x (w j) :=
    monomial_word s.val n (by
      simpa only [Finsupp.sum] using (hp.degree_eq_sum_deg_support s.property).symm)
  choose w hw using hex
  let a := Basis.piTensorProduct (fun _ : Fin n => b)
  let E (s : {s // s ∈ p.support}) : Module.End ℂ (TensorPower V n) →ₗ[ℂ] ℂ :=
    { toFun := fun T => LinearMap.toMatrix a a T (fun j => (w s j).1) (fun j => (w s j).2)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  refine ⟨∑ s : {s // s ∈ p.support}, p.coeff s.val • E s, ?_⟩
  intro g
  have heval : MvPolynomial.eval (matrixCoordinates b g) p =
      ∑ s : {s // s ∈ p.support}, p.coeff s.val *
        s.val.prod (fun a k => matrixCoordinates b g a ^ k) := by
    calc
      _ = MvPolynomial.eval (matrixCoordinates b g)
          (∑ s ∈ p.support, MvPolynomial.monomial s (p.coeff s)) :=
        congrArg _ p.as_sum
      _ = _ := by
        simp only [map_sum, MvPolynomial.eval_monomial]
        exact (Finset.sum_coe_sort p.support _).symm
  rw [heval]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  dsimp [E]
  rw [diagonal_tensor_matrix b, hw s]

/-- The polynomial entries assemble to a linear map on tensor operators. -/
theorem homogeneous_tensor_linear_map {W : Type v} [AddCommGroup W] [Module ℂ W]
    {d m n : ℕ} (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : Representation ℂ (LinearGroup V) W) (hρ : IsHomogeneousRepresentation b c ρ n) :
    ∃ L : Module.End ℂ (TensorPower V n) →ₗ[ℂ] Module.End ℂ W,
      ∀ g, L (diagonalOperator V n g) = ρ g := by
  classical
  have hex i j : ∃ L : Module.End ℂ (TensorPower V n) →ₗ[ℂ] ℂ,
      ∀ g, L (diagonalOperator V n g) = LinearMap.toMatrix c c (ρ g) i j := by
    obtain ⟨p, hp, he⟩ := hρ i j
    obtain ⟨L, hL⟩ := homogeneous_tensor_functional b p hp
    exact ⟨L, fun g => (hL g).trans (he g)⟩
  choose L hL using hex
  refine ⟨(LinearMap.toMatrix c c).symm.toLinearMap.comp
    (LinearMap.pi fun i => LinearMap.pi fun j => L i j), ?_⟩
  intro g
  apply (LinearMap.toMatrix c c).injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  ext i j
  exact hL i j g

/-- A linear map specified on a spanning group action respects products on
its span as soon as the prescribed images form a group action. -/
theorem linear_map_mul_on_group_span {G A C : Type*} [Group G]
    [Ring A] [Algebra ℂ A] [Ring C] [Algebra ℂ C]
    (r : G →* A) (s : G →* C) (L : A →ₗ[ℂ] C) (hL : ∀ g, L (r g) = s g)
    (x y : A) (hx : x ∈ Submodule.span ℂ (Set.range r))
    (hy : y ∈ Submodule.span ℂ (Set.range r)) : L (x * y) = L x * L y := by
  have hg (g : G) : L (r g * y) = L (r g) * L y := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨h, rfl⟩ := hz
      rw [← map_mul, hL, hL, hL, map_mul]
    | zero => simp
    | add z t hz ht ihz iht => simp [mul_add, ihz, iht, map_add]
    | smul a z hz ih => simp [mul_smul_comm, ih]
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨g, rfl⟩ := hz; exact hg g
  | zero => simp
  | add z t hz ht ihz iht => simp [add_mul, ihz, iht, map_add]
  | smul a z hz ih => simp [smul_mul_assoc, ih]

/-- Every homogeneous polynomial representation factors through the actual
unital tensor-image algebra, including the zero-algebra boundary. -/
theorem homogeneous_factorization :
    Specs.AdvancedFiniteGroupRepresentations.homogeneous_factorizationType.{u,v} := by
  intro V W _ _ _ _ d m n b c ρ hρ
  obtain ⟨L, hL⟩ := homogeneous_tensor_linear_map b c ρ hρ
  let f : tensorB V n →ₗ[ℂ] Module.End ℂ W := L.comp (tensorB V n).val.toLinearMap
  have hf1 : f 1 = 1 := by
    change L 1 = 1
    have h : L (diagonalRepresentation V n 1) = ρ 1 := hL 1
    simpa only [map_one] using h
  have hfmul (x y : tensorB V n) : f (x * y) = f x * f y := by
    apply linear_map_mul_on_group_span (diagonalRepresentation V n) ρ L (hL) x.val y.val
    · change x.val ∈ Submodule.span ℂ (Set.range (diagonalOperator V n))
      rw [← tensorB_span V n]; exact x.property
    · change y.val ∈ Submodule.span ℂ (Set.range (diagonalOperator V n))
      rw [← tensorB_span V n]; exact y.property
  refine ⟨AlgHom.ofLinearMap f hf1 hfmul, ?_⟩
  exact hL

/-- The tensor-image algebra is the product of the endomorphism algebras of
all canonical multiplicities. Zero multiplicities give zero-algebra factors. -/
def tensorBlockEquiv [FiniteDimensional ℂ V] (n : ℕ) :
    (∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p)) ≃ₐ[ℂ] tensorB V n := by
  classical
  let ψ : (∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p)) →ₐ[ℂ]
      Module.End ℂ (TensorPower V n) :=
    { toFun := secondFactorTransport V
      map_one' := by
        apply tensorEvaluation_end_ext V
        intro p v f
        simp
      map_mul' := by
        intro F H
        apply tensorEvaluation_end_ext V
        intro p v f
        simp [Module.End.mul_apply]
      map_zero' := by
        apply tensorEvaluation_end_ext V
        intro p v f
        simp
      map_add' := by
        intro F H
        apply tensorEvaluation_end_ext V
        intro p v f
        simp
      commutes' := by
        intro a
        apply tensorEvaluation_end_ext V
        intro p v f
        rw [secondFactorTransport_evaluation]
        rfl }
  have hinj : Function.Injective ψ := by
    intro F H he
    funext p
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have := congrArg (fun T : Module.End ℂ (TensorPower V n) => T (f.val v)) he
    exact (secondFactorTransport_evaluation V F p v f).symm.trans
      (this.trans (secondFactorTransport_evaluation V H p v f))
  have hr : ψ.range = tensorB V n := by
    apply le_antisymm
    · rintro _ ⟨F, rfl⟩
      have hB : tensorB V n = secondFactorBlocks V n := by
        rw [← firstCentralizer V n, tensorA_eq_firstFactorBlocks V n,
          firstFactorBlocks_centralizer V n]
      rw [hB]
      exact secondFactorTransport_mem V F
    · apply Algebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      refine ⟨fun p => tensorMultiplicityOperator V p g, ?_⟩
      apply tensorEvaluation_end_ext V
      intro p v f
      change secondFactorTransport V _ (f.val v) = _
      rw [secondFactorTransport_evaluation]
      rfl
  let φ := ψ.codRestrict (tensorB V n) (fun F => by rw [← hr]; exact ⟨F, rfl⟩)
  refine AlgEquiv.ofBijective φ ⟨?_, ?_⟩
  · intro F H he
    exact hinj (congrArg Subtype.val he)
  · intro T
    have hT : T.val ∈ ψ.range := by rw [hr]; exact T.property
    obtain ⟨F, hF⟩ := hT
    exact ⟨F, Subtype.ext hF⟩

@[simp] theorem tensorBlockEquiv_evaluation [FiniteDimensional ℂ V] (n : ℕ)
    (F : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p))
    (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p) :
    (tensorBlockEquiv (V := V) n F).val (f.val v) = (F p f).val v :=
  secondFactorTransport_evaluation V F p v f

/-- Finite products of full matrix blocks are semisimple, including the empty
and zero-algebra cases. -/
theorem tensorB_semisimple [FiniteDimensional ℂ V] (n : ℕ) :
    IsSemisimpleRing (tensorB V n) := by
  have (p : Partition n) : IsSemisimpleRing (Module.End ℂ (TensorMultiplicity V p)) :=
    IsSemisimpleRing.moduleEnd ℂ (TensorMultiplicity V p)
  exact (tensorBlockEquiv (V := V) n).toRingEquiv.isSemisimpleRing

/-- The original group generators span the tensor-image algebra internally. -/
theorem tensorImageElement_span (n : ℕ) :
    Submodule.span ℂ (Set.range (tensorImageElement V n)) = ⊤ := by
  apply Submodule.map_injective_of_injective (tensorB V n).toSubmodule.injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top]
  have hi : (tensorB V n).toSubmodule.subtype '' Set.range (tensorImageElement V n) =
      Set.range (diagonalOperator V n) := by
    ext T
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨tensorImageElement V n g, ⟨g, rfl⟩, rfl⟩
  rw [hi, tensorB_span]

/-- Invariant subspaces and tensor-image submodules are exactly the same
lattice when the group action is obtained from a tensor-image module. -/
def tensorSubmoduleOrderIso {W : Type v} [AddCommGroup W] [Module ℂ W] (n : ℕ)
    [Module (tensorB V n) W] [IsScalarTower ℂ (tensorB V n) W]
    (ρ : Representation ℂ (LinearGroup V) W)
    (hρ : ∀ g w, tensorImageElement V n g • w = ρ g w) :
    Subrepresentation ρ ≃o Submodule (tensorB V n) W where
  toFun S :=
    { carrier := S
      zero_mem' := S.toSubmodule.zero_mem
      add_mem' := S.toSubmodule.add_mem
      smul_mem' := by
        intro T w hw
        have hT : T ∈ Submodule.span ℂ (Set.range (tensorImageElement V n)) := by
          rw [tensorImageElement_span]; trivial
        induction hT using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨g, rfl⟩ := hz
          rw [hρ]
          exact S.apply_mem_toSubmodule g hw
        | zero =>
          change (0 : tensorB V n) • w ∈ S.toSubmodule
          simpa only [zero_smul] using S.toSubmodule.zero_mem
        | add x y hx hy ihx ihy =>
          change (x + y) • w ∈ S.toSubmodule
          rw [add_smul]
          exact S.toSubmodule.add_mem ihx ihy
        | smul a x hx ih =>
          change (a • x) • w ∈ S.toSubmodule
          rw [smul_assoc]
          exact S.toSubmodule.smul_mem a ih }
  invFun N :=
    { toSubmodule := N.restrictScalars ℂ
      apply_mem_toSubmodule := by
        intro g w hw
        rw [← hρ]
        exact N.smul_mem _ hw }
  left_inv S := by ext w; rfl
  right_inv N := by ext w; rfl
  map_rel_iff' := Iff.rfl

/-- Descent and the full block algebra imply complete reducibility. -/
theorem homogeneous_complete_reducibility :
    Specs.AdvancedFiniteGroupRepresentations.homogeneous_complete_reducibilityType.{u,v} := by
  intro V W _ _ _ _ d m n b c ρ hρ
  letI : FiniteDimensional ℂ V := Module.Finite.of_basis b
  obtain ⟨Φ, hΦ⟩ := homogeneous_factorization V W d m n b c ρ hρ
  letI : Module (tensorB V n) W := Module.compHom W Φ.toRingHom
  letI : IsScalarTower ℂ (tensorB V n) W :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      change Φ (algebraMap ℂ (tensorB V n) a) w = a • w
      rw [Φ.commutes]
      rfl)
  have hgen (g : LinearGroup V) (w : W) : tensorImageElement V n g • w = ρ g w := by
    change Φ (tensorImageElement V n g) w = ρ g w
    rw [hΦ]
  haveI := tensorB_semisimple (V := V) n
  letI : ComplementedLattice (Submodule (tensorB V n) W) :=
    (isSemisimpleModule_iff (tensorB V n) W).mp inferInstance
  exact (tensorSubmoduleOrderIso (V := V) n ρ hgen).symm.complementedLattice

@[simp] theorem tensorBlockEquiv_generator [FiniteDimensional ℂ V] (n : ℕ)
    (g : LinearGroup V) :
    tensorBlockEquiv (V := V) n (fun p => tensorMultiplicityOperator V p g) =
      tensorImageElement V n g := by
  apply Subtype.ext
  apply tensorEvaluation_end_ext V
  intro p v f
  rw [tensorBlockEquiv_evaluation]
  rfl

@[simp] theorem tensorBlockEquiv_symm_generator [FiniteDimensional ℂ V] (n : ℕ)
    (g : LinearGroup V) :
    (tensorBlockEquiv (V := V) n).symm (tensorImageElement V n g) =
      fun p => tensorMultiplicityOperator V p g := by
  rw [← tensorBlockEquiv_generator]
  exact (tensorBlockEquiv (V := V) n).symm_apply_apply _

/-- Simplicity transfers along a genuine equivariant linear equivalence. -/
theorem irreducible_of_representation_equiv {G X Y : Type*} [Monoid G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (e : Representation.Equiv ρ σ) [σ.IsIrreducible] : ρ.IsIrreducible := by
  apply (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr
  let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  have hf : Function.Bijective f := e.toLinearEquiv.bijective
  exact IsSimpleModule.congr (LinearEquiv.ofBijective f hf)

/-- Every simple module acted on by the tensor-image algebra is one of its
canonical nonzero multiplicity modules. -/
theorem tensorModule_simple_exists [FiniteDimensional ℂ V]
    {W : Type v} [AddCommGroup W] [Module ℂ W] (n : ℕ)
    [Module (tensorB V n) W] [IsScalarTower ℂ (tensorB V n) W]
    (ρ : Representation ℂ (LinearGroup V) W)
    (hρ : ∀ g w, tensorImageElement V n g • w = ρ g w)
    [ρ.IsIrreducible] :
    ∃ p : Partition n, Nontrivial (TensorMultiplicity V p) ∧
      Nonempty (Representation.Equiv ρ (tensorMultiplicityRepresentation V p)) := by
  classical
  haveI := tensorB_semisimple (V := V) n
  letI : IsSimpleModule (tensorB V n) W :=
    (isSimpleModule_iff (tensorB V n) W).mpr
      ((OrderIso.isSimpleOrder_iff (tensorSubmoduleOrderIso (V := V) n ρ hρ)).mp inferInstance)
  letI := IsSimpleModule.nontrivial (tensorB V n) W
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule (tensorB V n) W
  let E : W →ₗ[ℂ] tensorB V n := (I.subtype.comp e.toLinearMap).restrictScalars ℂ
  have hEinj : Function.Injective E := I.injective_subtype.comp e.injective
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hEw : E w ≠ 0 := fun h => hw (hEinj (h.trans (map_zero E).symm))
  let β := tensorBlockEquiv (V := V) n
  have hex : ∃ (p : Partition n) (f : TensorMultiplicity V p), (β.symm (E w) p) f ≠ 0 := by
    by_contra! hz
    apply hEw
    apply β.symm.injective
    rw [map_zero]
    funext p
    apply LinearMap.ext
    intro f
    exact hz p f
  obtain ⟨p, f, hf⟩ := hex
  let K : W →ₗ[ℂ] TensorMultiplicity V p :=
    { toFun := fun w => β.symm (E w) p f
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have hK (g : LinearGroup V) (w : W) :
      K (ρ g w) = tensorMultiplicityOperator V p g (K w) := by
    have hE : E (ρ g w) = tensorImageElement V n g * E w := by
      rw [← hρ]
      exact congrArg Subtype.val (e.map_smul (tensorImageElement V n g) w)
    change β.symm (E (ρ g w)) p f = _
    rw [hE, map_mul]
    change (β.symm (tensorImageElement V n g) p) (β.symm (E w) p f) = _
    rw [tensorBlockEquiv_symm_generator]
    rfl
  let k : Representation.IntertwiningMap ρ (tensorMultiplicityRepresentation V p) :=
    K.intertwiningMap_of_isIntertwiningMap _ _ hK
  have hk : k ≠ 0 := by
    intro hk
    exact hf (DFunLike.congr_fun hk w)
  have hnonzero : Nontrivial (TensorMultiplicity V p) := by
    have h : K w ≠ 0 := hf
    exact ⟨⟨K w, 0, h⟩⟩
  letI := hnonzero
  haveI := tensorMultiplicity_irreducible V p
  refine ⟨p, hnonzero, ⟨k.ofBijective ?_⟩⟩
  exact (Representation.IsIrreducible.bijective_or_eq_zero k).resolve_right hk

/-- The nonzero simple objects at degree n are exactly the canonical
multiplicities indexed by partitions of n with length at most dim V. -/
theorem homogeneous_simple_classification :
    Specs.AdvancedFiniteGroupRepresentations.homogeneous_simple_classificationType.{u,v} := by
  intro V W _ _ _ _ d m n b c ρ hρ
  letI : FiniteDimensional ℂ V := Module.Finite.of_basis b
  constructor
  · intro hs
    letI := hs
    obtain ⟨Φ, hΦ⟩ := homogeneous_factorization V W d m n b c ρ hρ
    letI : Module (tensorB V n) W := Module.compHom W Φ.toRingHom
    letI : IsScalarTower ℂ (tensorB V n) W :=
      IsScalarTower.of_algebraMap_smul (fun a w => by
        change Φ (algebraMap ℂ (tensorB V n) a) w = a • w
        rw [Φ.commutes]
        rfl)
    have hgen (g : LinearGroup V) (w : W) : tensorImageElement V n g • w = ρ g w := by
      change Φ (tensorImageElement V n g) w = ρ g w
      rw [hΦ]
    obtain ⟨p, hp, he⟩ := tensorModule_simple_exists (V := V) n ρ hgen
    have hd : Module.finrank ℂ V = d := by simpa using Module.finrank_eq_card_basis b
    exact ⟨p, hd ▸ (tensorMultiplicity_nonzero_iff V p).mp hp, he⟩
  · rintro ⟨p, hp, ⟨e⟩⟩
    haveI := (canonical_polynomial_simple V d b p hp).2.1
    exact irreducible_of_representation_equiv e

end AdvancedFiniteGroupRepresentations
