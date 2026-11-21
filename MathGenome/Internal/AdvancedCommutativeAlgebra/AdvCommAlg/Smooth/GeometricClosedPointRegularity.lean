import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.StandardPermanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalQuotients
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.GeometricClosedPointRegularity
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.List.OfFn
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.RegularLocalRing.Polynomial

namespace AdvCommAlg.Smooth

universe u v w z
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

/-- The original presentation stays standard smooth over the geometric fiber,
with its original number of variables and relations. -/
theorem geometric_fiber_presentation
    {A : Type u} {B : Type v} {L : Type w}
    [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]
    {n c : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin c))
    (hP : PresentationStandardSmooth P) :
    PresentationStandardSmooth (P.baseChange L) ∧
      (P.baseChange L).dimension = n - c :=
  base_change_presentation P hP

/-- Finiteness of the displayed presentation supplies Noetherianity over any
field, without assuming that the original base is Noetherian. -/
theorem geometric_fiber_noetherian
    {A : Type u} {B : Type v} {L : Type w}
    [CommRing A] [CommRing B] [Field L] [Algebra A B] [Algebra A L]
    {n c : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin c)) :
    IsNoetherianRing (L ⊗[A] B) := by
  letI := (P.baseChange L).toGenerators.finiteType
  exact Algebra.FiniteType.isNoetherianRing L _

theorem geometric_closed_point_noetherian_local
    {A : Type u} {B : Type v} {L : Type w}
    [CommRing A] [CommRing B] [Field L] [Algebra A B] [Algebra A L]
    {n c : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin c))
    (m : Ideal (L ⊗[A] B)) (hm : m.IsMaximal) :
    letI : m.IsPrime := hm.isPrime
    IsNoetherianRing (Localization.AtPrime m) ∧
      IsLocalRing (Localization.AtPrime m) := by
  letI : m.IsPrime := hm.isPrime
  letI := geometric_fiber_noetherian (L := L) P
  exact ⟨inferInstance, inferInstance⟩

/-- The minor controls the rank of differentials over the nonzero geometric
fiber. The comparison with the local cotangent space is still a separate step. -/
theorem geometric_fiber_differential_rank
    {A : Type u} {B : Type v} {L : Type w}
    [CommRing A] [CommRing B] [Field L] [Algebra A B] [Algebra A L]
    [Nontrivial (L ⊗[A] B)]
    {n c : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin c))
    (hP : PresentationStandardSmooth P) :
    Module.rank (L ⊗[A] B) (KaehlerDifferential L (L ⊗[A] B)) = n - c := by
  obtain ⟨Q, hQ⟩ :=
    (presentation_standard_smooth_iff_submersive (P.baseChange L)).mp
      (geometric_fiber_presentation P hP).1
  have hdim : Q.toPresentation.dimension = n - c := by
    rw [hQ]
    exact (geometric_fiber_presentation P hP).2
  exact Q.rank_kaehlerDifferential.trans (congrArg (fun d : ℕ => (d : Cardinal)) hdim)

/-- Independent classes of equations in the cotangent space of a regular local
ring can be placed first in a minimal generating list. Quotienting by them
therefore preserves regularity and subtracts their number from the dimension. -/
theorem regular_quotient_of_cotangent_independent
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {n c : ℕ} (hd : ringKrullDim R = (n : WithBot ℕ∞))
    (f : Fin c → IsLocalRing.maximalIdeal R)
    (hf : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i))) :
    IsRegularLocalRing (R ⧸ Ideal.span (Set.range (fun i => (f i : R)))) ∧
      ringKrullDim (R ⧸ Ideal.span (Set.range (fun i => (f i : R)))) =
        ((n - c : ℕ) : WithBot ℕ∞) := by
  classical
  let K := IsLocalRing.ResidueField R
  let V := IsLocalRing.CotangentSpace R
  let q := (IsLocalRing.maximalIdeal R).toCotangent
  let b := Module.Basis.sumExtend hf
  let J := Module.Basis.sumExtendIndex hf
  letI : Fintype (Fin c ⊕ J) := FiniteDimensional.fintypeBasisIndex b
  letI : Finite J := Finite.of_injective (Sum.inr : J → Fin c ⊕ J) Sum.inr_injective
  letI : Fintype J := Fintype.ofFinite J
  let k := Fintype.card J
  have hb (i : Fin c) : b (Sum.inl i) = q (f i) := by
    simp only [b, Module.Basis.sumExtend, Module.Basis.reindex_apply,
      Module.Basis.extend_apply_self]
    rfl
  choose g hg using fun j : J => (IsLocalRing.maximalIdeal R).toCotangent_surjective
    (b (Sum.inr j))
  let e : Fin c ⊕ Fin k ≃ Fin c ⊕ J :=
    Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin J).symm
  let y : Fin (c + k) → IsLocalRing.maximalIdeal R :=
    fun i => Sum.elim f (fun j => g ((Fintype.equivFin J).symm j))
      (finSumFinEquiv.symm i)
  have hy (i : Fin (c + k)) : q (y i) =
      (b.reindex (e.symm.trans finSumFinEquiv)) i := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rw [Module.Basis.reindex_apply]
    simp only [Equiv.symm_trans_apply, Equiv.symm_symm]
    change q (Sum.elim f (fun j => g ((Fintype.equivFin J).symm j))
      (finSumFinEquiv.symm (finSumFinEquiv i))) =
        b (e (finSumFinEquiv.symm (finSumFinEquiv i)))
    rw [Equiv.symm_apply_apply]
    cases i with
    | inl i => exact (hb i).symm
    | inr j => exact (hg ((Fintype.equivFin J).symm j))
  have hdim : Module.finrank K V = n := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [hd] at h
    exact_mod_cast h
  have hcount : c + k = n := by
    have h := Module.finrank_eq_card_basis (b.reindex (e.symm.trans finSumFinEquiv))
    simpa [K, V, hdim] using h.symm
  let xs : List R := List.ofFn (fun i => (y i : R))
  have hgen : Ideal.ofList xs = IsLocalRing.maximalIdeal R := by
    change Submodule.span R {r | r ∈ xs} = _
    have hspan : Submodule.span K (Set.range (fun i => q (y i))) = ⊤ := by
      simp_rw [hy]
      exact (b.reindex (e.symm.trans finSumFinEquiv)).span_eq
    have hspan' : Submodule.span R (Set.range y) = ⊤ := by
      apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
      rw [← Set.range_comp]
      exact hspan
    have hmap := congrArg (Submodule.map (IsLocalRing.maximalIdeal R).subtype) hspan'
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap
    convert hmap using 2
    ext r
    simp [xs]
  have htake : xs.take c = List.ofFn (fun i => (f i : R)) := by
    have he : xs = List.ofFn (fun i => (f i : R)) ++
        List.ofFn (fun j => (g ((Fintype.equivFin J).symm j) : R)) := by
      dsimp [xs]
      rw [← List.ofFn_fin_append]
      congr 1
      funext i
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      dsimp only [y]
      rw [Equiv.symm_apply_apply]
      cases i with
      | inl i => exact (Fin.append_left (fun i => (f i : R))
          (fun j : Fin k => (g ((Fintype.equivFin J).symm j) : R)) i).symm
      | inr j => exact (Fin.append_right (fun i => (f i : R))
          (fun j : Fin k => (g ((Fintype.equivFin J).symm j) : R)) j).symm
    rw [he]
    simp
  have hI : Ideal.ofList (xs.take c) =
      Ideal.span (Set.range (fun i => (f i : R))) := by
    rw [htake]
    change Ideal.span {r | r ∈ List.ofFn (fun i => (f i : R))} = _
    congr 1
    ext a
    exact List.mem_ofFn
  have h := CohenMacaulay.regularLocal_prefix_quotient R n xs hd
    (by simp [xs, hcount]) hgen c (by omega)
  rwa [hI] at h

/-- Extend a derivation to a localization, using the base change isomorphism
for Kähler differentials. -/
noncomputable def localizedDerivation
    {K : Type u} {R : Type v} {T : Type w}
    [CommRing K] [CommRing R] [CommRing T]
    [Algebra K R] [Algebra R T] [Algebra K T] [IsScalarTower K R T]
    (M : Submonoid R) [IsLocalization M T] (d : Derivation K R R) :
    Derivation K T T := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  exact (((Algebra.linearMap R T ∘ₗ d.liftKaehlerDifferential).liftBaseChange T) ∘ₗ
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K R T).symm.toLinearMap).compDer
      (KaehlerDifferential.D K T)

@[simp]
theorem localizedDerivation_algebraMap
    {K : Type u} {R : Type v} {T : Type w}
    [CommRing K] [CommRing R] [CommRing T]
    [Algebra K R] [Algebra R T] [Algebra K T] [IsScalarTower K R T]
    (M : Submonoid R) [IsLocalization M T] (d : Derivation K R R) (r : R) :
    localizedDerivation (T := T) M d (algebraMap R T r) = algebraMap R T (d r) := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  simp [localizedDerivation,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul]

/-- On the maximal ideal, a derivation followed by the residue map is
linear over the local ring. -/
def derivationOnMaximalIdeal
    {K : Type u} {R : Type v} [CommRing K] [CommRing R]
    [Algebra K R] [IsLocalRing R] (d : Derivation K R R) :
    IsLocalRing.maximalIdeal R →ₗ[R] IsLocalRing.ResidueField R where
  toFun x := IsLocalRing.residue R (d x)
  map_add' x y := by simp
  map_smul' r x := by
    change IsLocalRing.residue R (d (r * x)) =
      r • IsLocalRing.residue R (d x)
    rw [d.leibniz, map_add]
    simp only [smul_eq_mul, map_mul]
    simp [(IsLocalRing.residue_eq_zero_iff (R := R) x).mpr x.2, Algebra.smul_def]

/-- A derivation gives a linear functional on the actual residue-field
cotangent space. Products in the maximal ideal are annihilated by Leibniz. -/
def cotangentFunctional
    {K : Type u} {R : Type v} [CommRing K] [CommRing R]
    [Algebra K R] [IsLocalRing R] (d : Derivation K R R) :
    IsLocalRing.CotangentSpace R →ₗ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField R := by
  let l : IsLocalRing.CotangentSpace R →ₗ[R] IsLocalRing.ResidueField R :=
    Ideal.Cotangent.lift (derivationOnMaximalIdeal d) (by
      intro x y
      change IsLocalRing.residue R (d (x * y)) = 0
      rw [d.leibniz, map_add]
      simp only [smul_eq_mul, map_mul]
      simp [(IsLocalRing.residue_eq_zero_iff (R := R) x).mpr x.2,
        (IsLocalRing.residue_eq_zero_iff (R := R) y).mpr y.2])
  refine { l.toAddMonoidHom with map_smul' := ?_ }
  intro k x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective k
  change l ((algebraMap R (IsLocalRing.ResidueField R) r) • x) =
    (algebraMap R (IsLocalRing.ResidueField R) r) • l x
  simpa only [IsScalarTower.algebraMap_smul] using l.map_smul r x

@[simp]
theorem cotangentFunctional_toCotangent
    {K : Type u} {R : Type v} [CommRing K] [CommRing R]
    [Algebra K R] [IsLocalRing R] (d : Derivation K R R)
    (x : IsLocalRing.maximalIdeal R) :
    cotangentFunctional d ((IsLocalRing.maximalIdeal R).toCotangent x) =
      IsLocalRing.residue R (d x) := rfl

/-- Every maximal ideal of a polynomial ring over a field has the full
height. The induction uses the Jacobson property for the contraction at each
polynomial variable. -/
theorem polynomial_maximal_height
    (K : Type u) [Field K] (ι : Type v) [Finite ι]
    (q : Ideal (MvPolynomial ι K)) (hq : q.IsMaximal) :
    q.height = (Nat.card ι : ℕ∞) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e IH =>
    let Q := q.comap (MvPolynomial.renameEquiv K e).toRingEquiv
    haveI : Q.IsMaximal := Ideal.comap_isMaximal_of_equiv _
    have h := IH Q inferInstance
    simpa [Q, Nat.card_congr e] using h
  | h_empty =>
    let e := MvPolynomial.isEmptyRingEquiv K PEmpty.{v+1}
    let Q := q.comap e.symm
    haveI : Q.IsMaximal := Ideal.comap_isMaximal_of_equiv _
    have hbot : Q = ⊥ := (Ideal.eq_bot_or_top Q).resolve_right (Ideal.IsMaximal.ne_top inferInstance)
    have hheight : Q.height = 0 := hbot ▸ Ideal.height_bot
    simpa [Q] using hheight
  | @h_option α _ IH =>
    let e := (MvPolynomial.optionEquivLeft K α).toRingEquiv
    let Q := q.comap e.symm
    haveI : Q.IsMaximal := Ideal.comap_isMaximal_of_equiv _
    let p := Q.comap Polynomial.C
    have hp : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    letI : Q.LiesOver p := ⟨rfl⟩
    have h := Polynomial.height_eq_height_add_one p Q
    rw [IH p hp] at h
    simpa [Q, e, Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one] using h

/-- The polynomial local ring at a closed point is regular, with dimension
the number of polynomial variables. This holds over every field. -/
theorem polynomial_closed_point_regular
    (K : Type u) [Field K] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) K)) (hq : q.IsMaximal) :
    letI : q.IsPrime := hq.isPrime
    IsRegularLocalRing (Localization.AtPrime q) ∧
      ringKrullDim (Localization.AtPrime q) = (n : WithBot ℕ∞) := by
  letI : q.IsPrime := hq.isPrime
  refine ⟨inferInstance, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  rw [polynomial_maximal_height K (Fin n) q hq]
  simp

/-- Linear functionals with a nonsingular value matrix certify independence.
The functionals used below are induced by localized partial derivatives. -/
theorem linearIndependent_of_functional_det
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    {c : ℕ} (v : Fin c → V) (l : Fin c → V →ₗ[K] K)
    (h : (Matrix.of (fun i j => l i (v j))).det ≠ 0) :
    LinearIndependent K v := by
  let L : V →ₗ[K] (Fin c → K) := LinearMap.pi l
  exact LinearIndependent.of_comp L (Matrix.linearIndependent_cols_of_det_ne_zero h)

/-- A surjection maps the complement of a pulled-back prime onto the original
prime complement. This is the denominator comparison for local quotients. -/
theorem map_primeCompl_of_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (q : Ideal S) [q.IsPrime] :
    (q.comap φ).primeCompl.map φ = q.primeCompl := by
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact hr
  · intro hs
    obtain ⟨r, rfl⟩ := hφ s
    exact ⟨r, hs, rfl⟩

/-- Localizing a surjective homomorphism remains surjective, with kernel the
extension of the original kernel. -/
theorem localRingHom_surjective_ker
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (q : Ideal S) [q.IsPrime] :
    Function.Surjective (Localization.localRingHom (q.comap φ) q φ rfl) ∧
      RingHom.ker (Localization.localRingHom (q.comap φ) q φ rfl) =
        (RingHom.ker φ).map (algebraMap R (Localization.AtPrime (q.comap φ))) := by
  have hM := map_primeCompl_of_surjective φ hφ q
  letI : IsLocalization ((q.comap φ).primeCompl.map φ) (Localization.AtPrime q) :=
    hM.symm ▸ inferInstance
  constructor
  · exact IsLocalization.map_surjective_of_surjective
      (M := (q.comap φ).primeCompl) (S := Localization.AtPrime (q.comap φ))
      (g := φ) (Localization.AtPrime q) hφ
  · exact IsLocalization.ker_map (S := Localization.AtPrime (q.comap φ))
      (Localization.AtPrime q) φ hM

/-- The local ring of a quotient is the quotient of the local ring by the
localized equations. No domain assumption on either ring is necessary. -/
noncomputable def localQuotientEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (q : Ideal S) [q.IsPrime] :
    (Localization.AtPrime (q.comap φ) ⧸
      (RingHom.ker φ).map (algebraMap R (Localization.AtPrime (q.comap φ)))) ≃+*
        Localization.AtPrime q :=
  (Ideal.quotEquivOfEq (localRingHom_surjective_ker φ hφ q).2.symm).trans
    (RingHom.quotientKerEquivOfSurjective (localRingHom_surjective_ker φ hφ q).1)

/-- A kernel element is in the maximal ideal after localization at a prime
pulled back from the target. -/
def localizedKernelElement
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (q : Ideal S) [q.IsPrime] (x : RingHom.ker φ) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap φ)) :=
  ⟨algebraMap R _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime (q.comap φ)) (q.comap φ) x).mpr
    (by change φ x ∈ q; rw [RingHom.mem_ker.mp x.2]; exact q.zero_mem)⟩

/-- Regularity and the dimension drop for a quotient localized at a prime,
provided its localized equations have independent cotangent classes. -/
theorem regular_localization_of_cotangent_independent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (q : Ideal S) [q.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime (q.comap φ))]
    {n c : ℕ}
    (hd : ringKrullDim (Localization.AtPrime (q.comap φ)) = (n : WithBot ℕ∞))
    (f : Fin c → RingHom.ker φ)
    (hgen : Ideal.span (Set.range (fun i => (f i : R))) = RingHom.ker φ)
    (hf : LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime (q.comap φ)))
      (fun i => (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap φ))).toCotangent
        (localizedKernelElement φ q (f i)))) :
    IsRegularLocalRing (Localization.AtPrime q) ∧
      ringKrullDim (Localization.AtPrime q) = ((n - c : ℕ) : WithBot ℕ∞) := by
  let T := Localization.AtPrime (q.comap φ)
  let g := fun i => localizedKernelElement φ q (f i)
  have hI : (RingHom.ker φ).map (algebraMap R T) =
      Ideal.span (Set.range (fun i => (g i : T))) := by
    rw [← hgen, Ideal.map_span, ← Set.range_comp]
    rfl
  let e : (T ⧸ Ideal.span (Set.range (fun i => (g i : T)))) ≃+*
      Localization.AtPrime q :=
    (Ideal.quotEquivOfEq hI.symm).trans (localQuotientEquiv φ hφ q)
  obtain ⟨hreg, hdim⟩ := regular_quotient_of_cotangent_independent hd g hf
  letI := hreg
  exact ⟨IsRegularLocalRing.of_ringEquiv e,
    (ringKrullDim_eq_of_ringEquiv e).symm.trans hdim⟩

/-- At every closed point of a standard smooth algebra over a field, the
local ring is regular and its dimension is the displayed variable count minus
the displayed relation count. -/
theorem standard_smooth_closed_point_regularity
    {K : Type u} {B : Type v} [Field K] [CommRing B] [Algebra K B]
    {n c : ℕ} (P : Algebra.Presentation K B (Fin n) (Fin c))
    (hP : PresentationStandardSmooth P)
    (q : Ideal B) (hq : q.IsMaximal) :
    letI : q.IsPrime := hq.isPrime
    IsRegularLocalRing (Localization.AtPrime q) ∧
      ringKrullDim (Localization.AtPrime q) = ((n - c : ℕ) : WithBot ℕ∞) := by
  classical
  letI : q.IsPrime := hq.isPrime
  let R := MvPolynomial (Fin n) K
  let φ : R →+* B := (MvPolynomial.aeval P.val).toRingHom
  have hφ : Function.Surjective φ := P.aeval_val_surjective
  let p := q.comap φ
  haveI : p.IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  let T := Localization.AtPrime p
  obtain ⟨hreg, hd⟩ := polynomial_closed_point_regular K n p inferInstance
  letI : IsRegularLocalRing T := hreg
  let f : Fin c → RingHom.ker φ :=
    fun j => ⟨P.relation j, P.aeval_val_relation j⟩
  have hgen : Ideal.span (Set.range (fun j => (f j : R))) = RingHom.ker φ :=
    P.span_range_relation_eq_ker.trans P.ker_eq_ker_aeval_val
  apply regular_localization_of_cotangent_independent φ hφ q hd f hgen
  obtain ⟨a, ha⟩ := hP
  let d : Fin c → Derivation K T T :=
    fun i => localizedDerivation p.primeCompl (MvPolynomial.pderiv (a i))
  let g := fun j => localizedKernelElement φ q (f j)
  let D : Matrix (Fin c) (Fin c) R :=
    fun i j => MvPolynomial.pderiv (a i) (P.relation j)
  have hminor : D.map φ = selectedMinor P a := by
    ext i j
    rfl
  have hu : IsUnit (φ D.det) := by
    rw [RingHom.map_det]
    change IsUnit (D.map φ).det
    rw [hminor]
    exact ha
  have hnot : D.det ∉ p := Ideal.notMem_of_isUnit q hu
  have huT : IsUnit (algebraMap R T D.det) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff T p D.det).mpr hnot
  apply linearIndependent_of_functional_det
    (fun j => (IsLocalRing.maximalIdeal T).toCotangent (g j))
    (fun i => cotangentFunctional (d i))
  have heq : Matrix.of (fun i j =>
      cotangentFunctional (d i) ((IsLocalRing.maximalIdeal T).toCotangent (g j))) =
      D.map ((IsLocalRing.residue T).comp (algebraMap R T)) := by
    ext i j
    change IsLocalRing.residue T
      (localizedDerivation p.primeCompl (MvPolynomial.pderiv (a i))
        (algebraMap R T (P.relation j))) = _
    rw [localizedDerivation_algebraMap]
    rfl
  rw [heq]
  change (((IsLocalRing.residue T).comp (algebraMap R T)).mapMatrix D).det ≠ 0
  rw [← RingHom.map_det]
  exact (huT.map (IsLocalRing.residue T)).ne_zero

theorem geometric_closed_point_regularity :
    Specs.AdvCommAlg.Smooth.geometricClosedPointRegularity.{u,v,w,z} := by
  intro A B F L _ _ _ _ _ _ _ _ _ _ n c P hP m hm
  exact standard_smooth_closed_point_regularity (P.baseChange L)
    (geometric_fiber_presentation P hP).1 m hm

end
end AdvCommAlg.Smooth
