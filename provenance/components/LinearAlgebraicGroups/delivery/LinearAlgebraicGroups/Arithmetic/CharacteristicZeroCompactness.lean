import Specs.LinearAlgebraicGroups.Arithmetic.CharacteristicZeroCompactness
import LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms
import LinearAlgebraicGroups.Arithmetic.AnisotropicAdNilpotents
import LinearAlgebraicGroups.Arithmetic.BracketLatticeCompactness
import LinearAlgebraicGroups.Arithmetic.CentralIsogenyRationalCosets
import LinearAlgebraicGroups.Arithmetic.FiniteAdelicMorphism
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Group.Quotient

open scoped BigOperators RestrictedProduct
open CategoryTheory

set_option backward.isDefEq.respectTransparency false

namespace LinearAlgebraicGroups.Arithmetic.CharacteristicZeroCompactness

noncomputable section

section AdjointCoefficients

variable {R S I : Type*} [CommRing R] [CommRing S] [Fintype I] [DecidableEq I]

/-- In a basis with bracket constants b, the matrix for the bracket with x. -/
def bracketMatrix (b : I → I → I → R) (f : R →+* S) (x : I → S) : Matrix I I S :=
  Matrix.of fun i j => ∑ k, x k * f (b k j i)

/-- The universal adjoint matrix on a space given by bracket constants. -/
def universalBracketMatrix (b : I → I → I → R) : Matrix I I (MvPolynomial I R) :=
  bracketMatrix b MvPolynomial.C MvPolynomial.X

/-- The nonleading coefficients of the adjoint characteristic polynomial. -/
def adjointCoefficient (b : I → I → I → R) (r : Fin (Fintype.card I)) : MvPolynomial I R :=
  (universalBracketMatrix b).charpoly.coeff r

theorem adjointCoefficient_eval (b : I → I → I → R) (f : R →+* S) (x : I → S)
    (r : Fin (Fintype.card I)) :
    MvPolynomial.eval₂ f x (adjointCoefficient b r) = (bracketMatrix b f x).charpoly.coeff r := by
  change MvPolynomial.eval₂Hom f x _ = _
  rw [adjointCoefficient, ← Polynomial.coeff_map, ← Matrix.charpoly_map]
  have hm : (universalBracketMatrix b).map (MvPolynomial.eval₂Hom f x) =
      bracketMatrix b f x := by
    ext i j
    simp [universalBracketMatrix, bracketMatrix]
  rw [hm]

theorem adjointCoefficient_homogeneous (b : I → I → I → R) (r : Fin (Fintype.card I)) :
    (adjointCoefficient b r).IsHomogeneous (Fintype.card I - r) := by
  let B := universalBracketMatrix b
  let u : Polynomial (MvPolynomial (I × I) R) := Matrix.charpoly.univ R I
  let z : I × I → MvPolynomial I R := fun ij => B ij.1 ij.2
  have heval :
      adjointCoefficient b r = MvPolynomial.aeval z (u.coeff r) := by
    rw [MvPolynomial.aeval_eq_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  rw [heval]
  have hu : (u.coeff r).IsHomogeneous (Fintype.card I - r) :=
    Matrix.charpoly.univ_coeff_isHomogeneous R I r _ (Nat.add_sub_of_le r.isLt.le)
  have hz (ij : I × I) : (z ij).IsHomogeneous 1 := by
    change (∑ k : I, MvPolynomial.X k * MvPolynomial.C (b k ij.2 ij.1)).IsHomogeneous 1
    apply MvPolynomial.IsHomogeneous.sum
    intro k _
    simpa only [Nat.add_zero] using
      (MvPolynomial.isHomogeneous_X R k).mul (MvPolynomial.isHomogeneous_C I (b k ij.2 ij.1))
  simpa only [one_mul] using hu.aeval z hz

theorem adjointCoefficient_invariant (b : I → I → I → R) (f : R →+* S)
    (g : Matrix.GeneralLinearGroup I S) (x : I → S)
    (h : bracketMatrix b f (g.val.mulVec x) = g.val * bracketMatrix b f x * g⁻¹.val)
    (r : Fin (Fintype.card I)) :
    MvPolynomial.eval₂ f (g.val.mulVec x) (adjointCoefficient b r) =
      MvPolynomial.eval₂ f x (adjointCoefficient b r) := by
  rw [adjointCoefficient_eval, adjointCoefficient_eval, h, Matrix.charpoly_mul_comm,
    ← Matrix.mul_assoc, g.inv_mul, Matrix.one_mul]

theorem isNilpotent_of_adjointCoefficients_zero [Nontrivial S] (b : I → I → I → R) (f : R →+* S)
    (x : I → S) (h : ∀ r, MvPolynomial.eval₂ f x (adjointCoefficient b r) = 0) :
    IsNilpotent (bracketMatrix b f x) := by
  let B := bracketMatrix b f x
  have hp : B.charpoly = Polynomial.X ^ Fintype.card I := by
    ext n
    rcases lt_trichotomy n (Fintype.card I) with hlt | heq | hgt
    · simpa [B, adjointCoefficient_eval, Polynomial.coeff_X_pow, hlt.ne] using
        h ⟨n, hlt⟩
    · subst n
      rw [Polynomial.coeff_X_pow_self, ← Matrix.charpoly_natDegree_eq_dim B]
      exact B.charpoly_monic.leadingCoeff
    · rw [Polynomial.coeff_X_pow, ite_eq_right hgt.ne']
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((Matrix.charpoly_natDegree_eq_dim B).trans_lt hgt)
  refine ⟨Fintype.card I, ?_⟩
  simpa [hp] using Matrix.aeval_self_charpoly B


/-- A change of coordinates preserving the bracket conjugates its adjoint
operators. -/
theorem bracketMatrix_conj (b : I → I → I → R) (f : R →+* S)
    (g : Matrix.GeneralLinearGroup I S)
    (h : ∀ x y : I → S,
      (bracketMatrix b f (g.val.mulVec x)).mulVec (g.val.mulVec y) =
        g.val.mulVec ((bracketMatrix b f x).mulVec y))
    (x : I → S) :
    bracketMatrix b f (g.val.mulVec x) = g.val * bracketMatrix b f x * g⁻¹.val := by
  have hm : bracketMatrix b f (g.val.mulVec x) * g.val = g.val * bracketMatrix b f x := by
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    simpa only [Matrix.mulVec_mulVec] using h x y
  rw [← hm, Matrix.mul_assoc, g.mul_inv, Matrix.mul_one]

/-- Extending coefficients commutes with the adjoint polynomial evaluation. -/
theorem map_adjointCoefficient_eval {T : Type*} [CommRing T] (b : I → I → I → R)
    (f : R →+* S) (g : S →+* T) (x : I → S) (r : Fin (Fintype.card I)) :
    g (MvPolynomial.eval₂ f x (adjointCoefficient b r)) =
      MvPolynomial.eval₂ (g.comp f) (fun i => g (x i)) (adjointCoefficient b r) :=
  MvPolynomial.eval₂_comp_left g f x _

end AdjointCoefficients

section LieCoordinates

variable {k L I : Type*} [Field k] [LieRing L] [LieAlgebra k L]
    [Fintype I] [DecidableEq I]

/-- The coefficients of the Lie bracket in the chosen basis. -/
def bracketConstants (b : Module.Basis I k L) (i j l : I) : k :=
  b.repr ⁅b i, b j⁆ l

theorem bracketMatrix_eq_toMatrix_ad (b : Module.Basis I k L) (x : L) :
    bracketMatrix (bracketConstants b) (RingHom.id k) (b.repr x) =
      LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad k L x) := by
  ext i j
  rw [LinearMap.toMatrixAlgEquiv_apply, LieAlgebra.ad_apply]
  change (∑ l : I, b.repr x l * b.repr ⁅b l, b j⁆ i) = b.repr ⁅x, b j⁆ i
  conv_rhs => rw [← b.sum_repr x, sum_lie]
  simp [smul_lie, map_sum]

theorem exists_nonzero_adjointCoefficient (b : Module.Basis I k L)
    (h : ∀ x : L, IsNilpotent (LieAlgebra.ad k L x) → x = 0) (x : L) (hx : x ≠ 0) :
    ∃ r, (adjointCoefficient (bracketConstants b) r).eval (b.repr x) ≠ 0 := by
  classical
  by_contra! hz
  suffices hn : IsNilpotent (LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad k L x)) from
    hx (h x ((IsNilpotent.map_iff (LinearMap.toMatrixAlgEquiv b).injective).mp hn))
  rw [← bracketMatrix_eq_toMatrix_ad]
  exact isNilpotent_of_adjointCoefficients_zero _ _ _ hz

private theorem exists_nonzero_adjointCoefficient_coordinates (b : Module.Basis I k L)
    (h : ∀ x : L, IsNilpotent (LieAlgebra.ad k L x) → x = 0) (x : I → k) (hx : x ≠ 0) :
    ∃ r, (adjointCoefficient (bracketConstants b) r).eval x ≠ 0 := by
  obtain ⟨y, rfl⟩ := b.equivFun.surjective x
  exact exists_nonzero_adjointCoefficient b h y (fun hy => hx (by simp [hy]))

end LieCoordinates

section CompactQuotients

variable {A B Γ Δ : Type*} [Group A] [Group B] [Group Γ] [Group Δ]
  [TopologicalSpace A] [TopologicalSpace B]

/-- A compact set of right coset representatives gives compactness in the
quotient topology. -/
theorem compactSpace_rightQuotient (d : Γ →* A) {C : Set A} (hC : IsCompact C)
    (h : ∀ a : A, ∃ γ : Γ, a * d γ ∈ C) :
    CompactSpace (A ⧸ d.range) := by
  let q : A → A ⧸ d.range := QuotientGroup.mk
  have hq : Continuous q := QuotientGroup.continuous_mk (N := d.range)
  have hrange : q '' C = Set.univ := by
    refine Set.eq_univ_of_forall ?_
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨γ, hγ⟩ := h a
    refine ⟨a * d γ, hγ, ?_⟩
    symm
    apply QuotientGroup.eq.mpr
    simpa only [inv_mul_cancel_left] using (show d γ ∈ d.range from ⟨γ, rfl⟩)
  exact isCompact_univ_iff.mp (hrange ▸ hC.image hq)

/-- Lift a compact representative set through a homomorphism with compact
inverse images, using finitely many corrections to the rational lifts. -/
theorem lift_compactRepresentatives [ContinuousMul B]
    (dA : Γ →* A) (dB : Δ →* B) (f : A →* B) (φ : Γ →* Δ)
    (hcomm : ∀ γ, f (dA γ) = dB (φ γ))
    (hproper : ∀ C : Set B, IsCompact C → IsCompact (f ⁻¹' C))
    {C : Set B} (hC : IsCompact C) (hcover : ∀ b : B, ∃ δ : Δ, b * dB δ ∈ C)
    {ι : Type*} [Finite ι] (r : ι → Δ)
    (hcorrect : ∀ a δ, f a * dB δ ∈ C → ∃ j γ, δ = φ γ * r j) :
    ∃ A₀ : Set A, IsCompact A₀ ∧ ∀ a : A, ∃ γ : Γ, a * dA γ ∈ A₀ := by
  let B₀ : Set B := ⋃ j, (fun b : B => b * (dB (r j))⁻¹) '' C
  have hB₀ : IsCompact B₀ :=
    isCompact_iUnion fun j => hC.image (continuous_id.mul continuous_const)
  refine ⟨f ⁻¹' B₀, hproper B₀ hB₀, fun a => ?_⟩
  obtain ⟨δ, hδ⟩ := hcover (f a)
  obtain ⟨j, γ, hγ⟩ := hcorrect a δ hδ
  refine ⟨γ, Set.mem_iUnion.mpr ⟨j, f a * dB δ, hδ, ?_⟩⟩
  simp only [map_mul, hcomm, hγ, mul_assoc, mul_inv_cancel, mul_one]

end CompactQuotients

universe u v

open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.Specs.CharacteristicZeroCompactness
open Specs.IntegralModels (MatrixRealization RationalPoints)

/-- Anisotropy supplies a nonzero invariant value for every nonzero rational
Lie vector. -/
theorem exists_nonzero_invariant {K : Type u} [Field K] [CharZero K]
    (G : AffineAlgebraicGroup K) (hG : GeometricRadicals.IsSemisimple G)
    (ha : Specs.AnisotropicAdNilpotents.IsAnisotropic G.val)
    (s : IdentityLieStructure G.val) {I : Type*} [Fintype I] [DecidableEq I] :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (b : Module.Basis I K (Lie K G.val)) (x : I → K), x ≠ 0 →
      ∃ r, (adjointCoefficient (bracketConstants b) r).eval x ≠ 0 := by
  have hzero := congrArg (fun g : AddGroup (PointKernel G.val) => @Zero.zero _ g.toZero)
    s.group_law
  let := s.lieRing
  let := s.lieAlgebra
  intro b x hx
  refine exists_nonzero_adjointCoefficient_coordinates b (fun e he => ?_) x hx
  exact (AnisotropicAdNilpotents.adNilpotentEqZero G hG ha s e he).trans hzero.symm


/-- The coordinate formula for rational translation agrees with multiplication
by the diagonal homomorphism. -/
theorem compactRepresentatives_iff {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    (d : RationalPoints G →* AdelicGroups.Adeles D i ∅)
    (hd : ∀ γ (w : AdelicGroups.Outside D ∅), d γ w = AdelicGroups.localPoint D i w.1 γ) :
    CompactRepresentatives D i ↔
      ∃ C : Set (AdelicGroups.Adeles D i ∅), IsCompact C ∧
        ∀ a : AdelicGroups.Adeles D i ∅, ∃ γ : RationalPoints G, a * d γ ∈ C := by
  constructor
  · rintro ⟨C, hC, hcover⟩
    refine ⟨C, hC, fun a => ?_⟩
    obtain ⟨γ, c, hc, hγ⟩ := hcover a
    have heq : c = a * d γ := by
      apply RestrictedProduct.ext
      intro w
      change c w = a w * d γ w
      rw [hd]
      exact hγ w
    exact ⟨γ, heq ▸ hc⟩
  · rintro ⟨C, hC, hcover⟩
    refine ⟨C, hC, fun a => ?_⟩
    obtain ⟨γ, hγ⟩ := hcover a
    refine ⟨γ, a * d γ, hγ, fun w => ?_⟩
    change a w * d γ w = _
    rw [hd]

theorem compactSpace_of_adelicRepresentatives {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    (d : RationalPoints G →* AdelicGroups.Adeles D i ∅)
    (hd : ∀ γ (w : AdelicGroups.Outside D ∅), d γ w = AdelicGroups.localPoint D i w.1 γ)
    (h : CompactRepresentatives D i) :
    CompactSpace (AdelicGroups.Adeles D i ∅ ⧸ d.range) := by
  obtain ⟨C, hC, hcover⟩ := (compactRepresentatives_iff D i d hd).mp h
  exact compactSpace_rightQuotient d hC hcover

theorem compactAdelicQuotient_of_representatives {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    (diagonal : Specs.AdelicGroups.canonicalDiagonal.{u,v})
    (h : CompactRepresentatives D i) : CompactAdelicQuotient D i := by
  obtain ⟨d, hd, _⟩ := diagonal D i ∅
  exact ⟨d, hd, compactSpace_of_adelicRepresentatives D i d hd h⟩

theorem lift_adelicRepresentatives {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) {G Q : AffineAlgebraicGroup K}
    (i : MatrixRealization G) (j : MatrixRealization Q)
    [ContinuousMul (AdelicGroups.Adeles D j ∅)]
    (dA : RationalPoints G →* AdelicGroups.Adeles D i ∅)
    (dB : RationalPoints Q →* AdelicGroups.Adeles D j ∅)
    (hdA : ∀ γ (w : AdelicGroups.Outside D ∅), dA γ w = AdelicGroups.localPoint D i w.1 γ)
    (hdB : ∀ δ (w : AdelicGroups.Outside D ∅), dB δ w = AdelicGroups.localPoint D j w.1 δ)
    (f : AdelicGroups.Adeles D i ∅ →* AdelicGroups.Adeles D j ∅)
    (φ : RationalPoints G →* RationalPoints Q)
    (hcomm : ∀ γ, f (dA γ) = dB (φ γ))
    (hproper : ∀ C : Set (AdelicGroups.Adeles D j ∅), IsCompact C → IsCompact (f ⁻¹' C))
    (hQ : CompactRepresentatives D j)
    (hfinite : ∀ C : Set (AdelicGroups.Adeles D j ∅), IsCompact C →
      ∃ T : Finset (RationalPoints Q), ∀ a δ, f a * dB δ ∈ C →
        ∃ t ∈ T, ∃ γ : RationalPoints G, δ = φ γ * t) :
    CompactRepresentatives D i := by
  obtain ⟨C, hC, hcover⟩ := (compactRepresentatives_iff D j dB hdB).mp hQ
  obtain ⟨T, hT⟩ := hfinite C hC
  apply (compactRepresentatives_iff D i dA hdA).mpr
  refine lift_compactRepresentatives dA dB f φ hcomm hproper hC hcover
    (fun t : T => t.val) (fun a δ hδ => ?_)
  obtain ⟨t, ht, γ, hγ⟩ := hT a δ hδ
  exact ⟨⟨t, ht⟩, γ, hγ⟩

private theorem bracketMatrix_mulVec {K R I : Type u} [CommRing K] [CommRing R] [Fintype I]
    (c : I → I → I → K) (f : K →+* R) (x y : I → R) :
    (bracketMatrix c f x).mulVec y = Specs.AdjointLieAutomorphisms.coordinateBracket c f x y := by
  funext l
  simp only [bracketMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Specs.AdjointLieAutomorphisms.coordinateBracket, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => by ring

private theorem latticeBracket_eq_coordinateBracket {K R I : Type u}
    [CommRing K] [CommRing R] [Fintype I]
    (c : I → I → I → K) (f : K →+* R) (x y : I → R) :
    BracketLatticeCompactness.bracket c f x y =
      Specs.AdjointLieAutomorphisms.coordinateBracket c f x y :=
  bracketMatrix_mulVec c f x y

private theorem liftThroughCentralIsogeny {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) {G Q : AffineAlgebraicGroup K}
    (q : G.val ⟶ Q.val) (i : MatrixRealization G) (j : MatrixRealization Q)
    (hproper : Specs.FiniteAdelicMorphism.HasProperAdelicMap D q i j)
    (hfinite : Specs.CentralIsogenyRationalCosets.FiniteCosetsFor D q j)
    (hQ : CompactRepresentatives D j) : CompactAdelicQuotient D i := by
  open AdelicGroups in
  obtain ⟨f, hf, _, hcompact⟩ := hproper
  let φ : RationalPoints G →* RationalPoints Q :=
    Specs.CentralIsogenyRationalCosets.pointMap q K
  let dG := diagonal D i ∅
  let dQ := diagonal D j ∅
  have hcomm (γ : RationalPoints G) : f (dG γ) = dQ (φ γ) := by
    apply RestrictedProduct.ext
    intro w
    rw [hf]
    let e := CommAlgCat.ofHom (Algebra.ofId K (D.Completion w.1))
    exact congrArg (fun a => a γ) (((groupPointsFunctor K).map q).naturality e)
  apply compactAdelicQuotient_of_representatives D i canonicalDiagonal
  refine lift_adelicRepresentatives D i j dG dQ (diagonalCoordinates D i ∅)
    (diagonalCoordinates D j ∅) f φ hcomm hcompact hQ ?_
  intro C hC
  obtain ⟨F, hF⟩ := hfinite C hC
  refine ⟨F, fun a δ ha => hF δ ⟨f a * dQ δ, ha, fun w => ⟨a w, ?_⟩⟩⟩
  change f a w * localPoint D j w.1 δ = _
  rw [hf]
  rfl

/-- A globally anisotropic semisimple group over a number field has compact full adelic quotient. -/
theorem anisotropicAdelicCompactness : AnisotropicAdelicCompactness.{u} := by
  classical
  intro K _ hK G hG ha i
  obtain ⟨Z, Q, q, hq, _, hfin, hQ, s, n, b, T, L, l, A, j, ι, _, hclosed, _, _, _,
    hlocal, m, r, _, hcosets⟩ :=
    LinearAlgebraicGroups.AdjointLieAutomorphisms.adjointRealization G hG
  let := s.lieRing
  let := s.lieAlgebra
  let D := GlobalFieldData.number.{u,0} hK
  let (w : D.Place) : Field (D.Completion w) := GlobalFieldData.instFieldCompletion D w
  let (w : D.Place) : Algebra K (D.Completion w) := AdelicGroups.completionAlgebra D w
  let J : MatrixRealization Q := ⟨n, L, l, ι ≫ j, hclosed⟩
  let c := bracketConstants b
  have hcentral : Specs.CentralIsogenies.IsCentralIsogeny q := by
    refine ⟨hfin, hq.2.2.2.1, hq.2.2.2.2.1, Z, hq.2.1, ?_⟩
    exact (hq.1 Z.group.X Z.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hbr : BracketLatticeCompactness.LocalBracketInvariant D J c := by
    intro w g x y
    change BracketLatticeCompactness.bracket c (D.embedding w)
      ((AdelicGroups.asMatrix J (D.Completion w) g).val.mulVec x)
      ((AdelicGroups.asMatrix J (D.Completion w) g).val.mulVec y) = _
    rw [latticeBracket_eq_coordinateBracket, latticeBracket_eq_coordinateBracket]
    exact (hlocal (CommAlgCat.of K (D.Completion w)) g).1 x y
  have hdet : BracketLatticeCompactness.LocalDeterminantOne D J := by
    intro w g
    apply Units.ext
    exact (hlocal (CommAlgCat.of K (D.Completion w)) g).2
  have hinv (a : Fin (Fintype.card (ULift.{u} (Fin n)))) :
      BracketLatticeCompactness.LocalPolynomialInvariant D J (adjointCoefficient c a) := by
    intro w g x
    exact adjointCoefficient_invariant c _ _ x
      (bracketMatrix_conj c _ _ (hbr w g) x) a
  have hreps : CompactRepresentatives D J := by
    refine BracketLatticeCompactness.latticeComparison J c
      (adjointCoefficient c) (fun a => Fintype.card (ULift.{u} (Fin n)) - a) r hdet hbr
      (fun a => ⟨Nat.sub_pos_of_lt a.isLt, adjointCoefficient_homogeneous c a⟩) hinv
      (exists_nonzero_invariant G hG ha s b) ?_
    intro M hM
    exact hcosets M (fun x y => by
      change Specs.AdjointLieAutomorphisms.coordinateBracket c (RingHom.id K)
        (M.val.mulVec x) (M.val.mulVec y) =
          M.val.mulVec (Specs.AdjointLieAutomorphisms.coordinateBracket c (RingHom.id K) x y)
      rw [← latticeBracket_eq_coordinateBracket, ← latticeBracket_eq_coordinateBracket]
      exact hM x y)
  exact liftThroughCentralIsogeny D q i J
    (FiniteAdelicMorphism.finiteAdelicMorphism q hfin i J)
    (CentralIsogenyRationalCosets.finiteRationalCosets G Q hG hQ q hcentral J) hreps

end

end LinearAlgebraicGroups.Arithmetic.CharacteristicZeroCompactness
