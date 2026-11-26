import Specs.LinearAlgebraicGroups.Unipotent.CentralKilledByPCurves
import LinearAlgebraicGroups.Unipotent.CentralSeries
import LinearAlgebraicGroups.Affine.Stabilizers
import LinearAlgebraicGroups.Affine.SmoothnessCriteria
import LinearAlgebraicGroups.Descent.AffineGroups
import LinearAlgebraicGroups.Descent.SmoothPoint
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct IntermediateField.algebraAdjoinAdjoin

universe u

namespace LinearAlgebraicGroups.Unipotent

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.Unipotent
open private GPoints onPoints onPoints_comp onPoints_natural onPoints_injective kernel_points
  from LinearAlgebraicGroups.Unipotent.CentralSeries

noncomputable section

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem onPoints_id {G : GroupScheme k} (R : TestAlgebra k)
    (x : GPoints G R) : onPoints (𝟙 G) R x = x := by
  change x ≫ 𝟙 G.X = x
  exact Category.comp_id x

private theorem bottom_point_eq_one {G : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries G n) (R : TestAlgebra k) (x : GPoints (S.term n).val R) : x = 1 := by
  have h : onPoints S.bottom.hom R x = onPoints S.bottom.hom R 1 :=
    (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  have hi := congrArg (onPoints S.bottom.inv R) h
  simpa only [← onPoints_comp, Iso.hom_inv_id, onPoints_id] using hi

/-- A central series detects a nonidentity element commuting with a given subgroup
of points by successively taking nonidentity commutators. -/
private theorem exists_commuting_point {G : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries G n) (hS : S.IsCentral) {R : TestAlgebra k} {A : Type*} [Group A]
    (a : A →* GPoints G.val R) (b : GPoints G.val R →* A)
    (h : ∃ x, b x = 1 ∧ x ≠ 1) :
    ∃ x, b x = 1 ∧ x ≠ 1 ∧ ∀ g, Commute (a g) x := by
  classical
  by_contra! no
  have deep (i : ℕ) (hi : i ≤ n) :
      ∃ x : GPoints (S.term i).val R,
        b (onPoints (S.inclusion i) R x) = 1 ∧ onPoints (S.inclusion i) R x ≠ 1 := by
    induction i with
    | zero =>
      obtain ⟨x, hz, hx⟩ := h
      refine ⟨onPoints S.top.inv R x, ?_⟩
      change b (onPoints S.top.hom R (onPoints S.top.inv R x)) = 1 ∧
        onPoints S.top.hom R (onPoints S.top.inv R x) ≠ 1
      simpa only [← onPoints_comp, Iso.inv_hom_id, onPoints_id] using And.intro hz hx
    | succ i ih =>
      obtain ⟨y, hy, hy'⟩ := ih (Nat.le_of_succ_le hi)
      obtain ⟨g, hg⟩ := no _ hy hy'
      obtain ⟨z, hz⟩ := hS i (Nat.lt_of_succ_le hi) R (a g) y
      change onPoints (S.inclusion (i + 1)) R z = _ at hz
      refine ⟨z, ?_, ?_⟩
      · rw [hz]
        simp [hy]
      · rw [hz]
        intro he
        apply hg
        change a g * onPoints (S.inclusion i) R y = onPoints (S.inclusion i) R y * a g
        have hh := congrArg (fun t => t * onPoints (S.inclusion i) R y * a g) he
        simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, one_mul, inv_mul_cancel, mul_one] using hh
  obtain ⟨x, _, hx⟩ := deep n le_rfl
  exact hx (by rw [bottom_point_eq_one S R x, map_one])

/-- An additive-factor series supplies a uniform exponent on points in positive characteristic. -/
private theorem pow_eq_one_of_additive_factors {G : AffineAlgebraicGroup k} {n p : ℕ}
    [CharP k p] (S : ClosedSeries G n) (hS : S.HasAdditiveSubgroupFactors)
    (R : TestAlgebra k) (x : GPoints G.val R) : x ^ (p ^ n) = 1 := by
  have hpR : (p : R) = 0 := by
    rw [← map_natCast (algebraMap k R), CharP.cast_eq_zero, map_zero]
  have deep (i : ℕ) (hi : i ≤ n) : ∃ y : GPoints (S.term i).val R,
      onPoints (S.inclusion i) R y = x ^ (p ^ i) := by
    induction i with
    | zero =>
      refine ⟨onPoints S.top.inv R x, ?_⟩
      change onPoints S.top.hom R (onPoints S.top.inv R x) = _
      rw [← onPoints_comp, Iso.inv_hom_id, pow_zero, pow_one, onPoints_id]
    | succ i ih =>
      obtain ⟨y, hy⟩ := ih (Nat.le_of_succ_le hi)
      obtain ⟨Q, V, q, j, ⟨e⟩, hj, hq⟩ := hS i (Nat.lt_of_succ_le hi)
      have hkill : onPoints q R (y ^ p) = 1 := by
        apply onPoints_injective j hj R
        let f : GPoints V.val R →* Multiplicative R := (e.hom.app R).hom
        apply ((CategoryTheory.forget GrpCat).mapIso (e.app R)).toEquiv.injective
        change f (onPoints j R (onPoints q R (y ^ p))) = f (onPoints j R 1)
        rw [map_pow, map_pow, map_pow, map_one, map_one]
        change Multiplicative.ofAdd (p • Multiplicative.toAdd
          (f (onPoints j R (onPoints q R y)))) = Multiplicative.ofAdd (0 : R)
        rw [nsmul_eq_mul, hpR, zero_mul]
      obtain ⟨z, hz⟩ := (kernel_points q ⟨_, S.step i, S.closed i⟩ hq.1 R (y ^ p)).mp hkill
      refine ⟨z, ?_⟩
      change onPoints (S.step i ≫ S.inclusion i) R z = _
      rw [onPoints_comp, hz, map_pow, hy, pow_succ, pow_mul]
  obtain ⟨y, hy⟩ := deep n le_rfl
  rwa [bottom_point_eq_one S R y, map_one, eq_comm] at hy

private theorem exists_last_nonidentity_power {B : Type*} [Group B] {p n : ℕ}
    (x : B) (hx : x ≠ 1) (hpow : x ^ (p ^ n) = 1) :
    ∃ i : ℕ, x ^ (p ^ i) ≠ 1 ∧ (x ^ (p ^ i)) ^ p = 1 := by
  induction n with
  | zero => exact False.elim (hx (by simpa using hpow))
  | succ n ih =>
    by_cases hn : x ^ (p ^ n) = 1
    · exact ih hn
    · exact ⟨n, hn, by simpa only [pow_succ, pow_mul] using hpow⟩

section Specialization

variable {L A : Type u} [Field L] [Algebra k L] [CommRing A] [Algebra k A]

private theorem lift_polynomial_coefficients [Algebra.FiniteType k A]
    (f : A →ₐ[k] Polynomial L) :
    ∃ s : Finset L, ∃ g : A →ₐ[k] Polynomial (Algebra.adjoin k (s : Set L)),
      (Polynomial.mapAlgHom (Algebra.adjoin k (s : Set L)).val).comp g = f := by
  classical
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := k) (A := A)
  let s := t.biUnion fun a => (f a).support.image (f a).coeff
  let B := Algebra.adjoin k (s : Set L)
  let m : Polynomial B →ₐ[k] Polynomial L := Polynomial.mapAlgHom B.val
  have hinj : Function.Injective m := Polynomial.map_injective B.val.toRingHom Subtype.val_injective
  have hr (a : A) : f a ∈ m.range := by
    have hgen : (⊤ : Subalgebra k A) ≤ m.range.comap f := by
      rw [← ht]
      refine Algebra.adjoin_le ?_
      intro a ha
      change ∃ q : Polynomial B, Polynomial.map B.val.toRingHom q = f a
      apply ((f a).mem_lifts (f := B.val.toRingHom)).mp
      refine ((f a).lifts_iff_coeff_lifts (f := B.val.toRingHom)).mpr fun n => ?_
      by_cases hn : n ∈ (f a).support
      · exact ⟨⟨(f a).coeff n, Algebra.subset_adjoin
          (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩)⟩, rfl⟩
      · exact ⟨0, (Polynomial.notMem_support_iff.mp hn).symm⟩
    exact hgen (show a ∈ (⊤ : Subalgebra k A) from trivial)
  let g := (AlgEquiv.ofInjective m hinj).symm.toAlgHom.comp (f.codRestrict m.range hr)
  exact ⟨s, g, by ext1 a; exact congrArg Subtype.val ((AlgEquiv.ofInjective m hinj).apply_symm_apply _)⟩

private theorem smooth_fraction_adjoin [Algebra.IsTranscendentalSeparable k L] (s : Finset L) :
    Algebra.FormallySmooth k (IntermediateField.adjoin k (s : Set L)) := by
  let D := IntermediateField.adjoin k (s : Set L)
  have hD : Algebra.EssFiniteType k D := inferInstanceAs (Algebra.EssFiniteType k (IntermediateField.adjoin k (s : Set L)))
  obtain ⟨basis, hb, hsep⟩ :=
    Algebra.IsTranscendentalSeparable.forall_isSeparablyGenerated D hD
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : basis → D))) D := by
    have eq : Set.range ((↑) : basis → D) = basis := Subtype.range_coe_subtype
    rwa [eq]
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hb.1

private theorem smooth_localization_of_coeff [Algebra.IsTranscendentalSeparable k L]
    (s : Finset L) {b : Algebra.adjoin k (s : Set L)} (hb : b ≠ 0) :
    ∃ d : Algebra.adjoin k (s : Set L), d ≠ 0 ∧ b ∣ d ∧
      Algebra.Smooth k (Localization.Away d) := by
  let B := Algebra.adjoin k (s : Set L)
  let D := IntermediateField.adjoin k (s : Set L)
  have hD : Algebra.FormallySmooth k D := smooth_fraction_adjoin s
  let : IsLocalization ((⊥ : Ideal B).primeCompl) D := by
    rw [Ideal.primeCompl_bot]
    infer_instance
  let : Algebra.IsSmoothAt k (⊥ : Ideal B) :=
    Algebra.FormallySmooth.of_equiv
      ((IsLocalization.algEquiv (⊥ : Ideal B).primeCompl D
        (Localization.AtPrime (⊥ : Ideal B))).restrictScalars k)
  have : Algebra.FiniteType k B := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  have : Algebra.FinitePresentation k B := (Algebra.FinitePresentation.of_finiteType).mp ‹_›
  obtain ⟨e, he, hsmooth⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k (⊥ : Ideal B)
  refine ⟨e * b, mul_ne_zero (by simpa using he) hb, ⟨e, mul_comm e b⟩, ?_⟩
  apply Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp
  intro q hq
  apply Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsmooth
  exact fun heq => hq (Ideal.mul_mem_right b _ heq)

private theorem hom_to_sepClosure_of_smooth {B : Type u} [CommRing B] [Algebra k B]
    [Algebra.Smooth k B] [Nontrivial B] : Nonempty (B →ₐ[k] SeparableClosure k) := by
  let S := SeparableClosure k
  let T := S ⊗[k] B
  have hT : Nontrivial T := (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
    (R := k) (M := S) (N := B)).mpr inferInstance
  let j : CommRingCat.of S ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap S T)
  have hsmooth : Smooth (Spec.map j) := by
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    change (algebraMap S T).Smooth
    exact RingHom.smooth_algebraMap.mpr inferInstance
  obtain ⟨x, hx⟩ := Descent.exists_rational_point_of_smooth (Spec.map j)
    (inferInstance : Nonempty (Spec (CommRingCat.of T)))
  let e := Spec.preimage x
  have he : j ≫ e = 𝟙 _ := by simpa only [← Spec.map_inj, Spec.map_comp, Spec.map_id, e, Spec.map_preimage] using hx
  let E : T →ₐ[S] S :=
    { e.hom with commutes' := fun a => congrArg (fun m : CommRingCat.of S ⟶ _ => m.hom a) he }
  exact ⟨(E.restrictScalars k).comp Algebra.TensorProduct.includeRight⟩

/-- A nonzero chosen coefficient of a curve survives specialization to the separable closure. -/
private theorem exists_polynomial_specialization [Algebra.FiniteType k A]
    [Algebra.IsTranscendentalSeparable k L] (f : A →ₐ[k] Polynomial L)
    (a : A) (n : ℕ) (h : (f a).coeff n ≠ 0) :
    ∃ g : A →ₐ[k] Polynomial (SeparableClosure k), (g a).coeff n ≠ 0 := by
  obtain ⟨s, g, hg⟩ := lift_polynomial_coefficients f
  let B := Algebra.adjoin k (s : Set L)
  let b : B := (g a).coeff n
  have hcoe : B.val b = (f a).coeff n := by
    rw [← hg, AlgHom.comp_apply, Polynomial.coeff_mapAlgHom_apply]
  have hb : b ≠ 0 := fun hb => h (hcoe.symm.trans (hb ▸ map_zero B.val))
  obtain ⟨d, hd, hdiv, hs⟩ := smooth_localization_of_coeff s hb
  let C := Localization.Away d
  let i : B →ₐ[k] C := IsScalarTower.toAlgHom k B C
  have hi : Function.Injective i :=
    IsLocalization.injective C (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hd))
  have : Nontrivial C := Function.Injective.nontrivial (f := i) hi
  have : Algebra.Smooth k C := hs
  obtain ⟨e⟩ := hom_to_sepClosure_of_smooth (k := k) (B := C)
  refine ⟨(Polynomial.mapAlgHom (e.comp i)).comp g, ?_⟩
  rw [AlgHom.comp_apply, Polynomial.coeff_mapAlgHom_apply]
  have hu : IsUnit (i b) :=
    (IsLocalization.Away.algebraMap_isUnit_iff (S := C) d).mpr ⟨1, by simpa using hdiv⟩
  exact (hu.map e).ne_zero


end Specialization

private abbrev scalarPointMap {G : GroupScheme k} {R T : TestAlgebra k} (f : R ⟶ T) :
    GPoints G R →* GPoints G T := (((groupPointsFunctor k).obj G).map f).hom

private theorem scalarPointMap_comp {G : GroupScheme k} {R T V : TestAlgebra k}
    (f : R ⟶ T) (g : T ⟶ V) (x : GPoints G R) :
    scalarPointMap g (scalarPointMap f x) = scalarPointMap (f ≫ g) x := by
  exact (congrArg (fun m => m x) (((groupPointsFunctor k).obj G).map_comp f g)).symm

private theorem origin_constant {G : GroupScheme k} (x : Points G.X (CommAlgCat.of k k)) :
    curveAtZero (constantCurve x) = x := by
  change scalarPointMap (CommAlgCat.ofHom (Polynomial.aeval (0 : k)))
    (scalarPointMap (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k))) x) = x
  rw [scalarPointMap_comp]
  have h : CommAlgCat.ofHom (Algebra.ofId k (Polynomial k)) ≫
      CommAlgCat.ofHom (Polynomial.aeval (0 : k)) = 𝟙 (CommAlgCat.of k k) := by
    apply CommAlgCat.hom_ext
    ext
  rw [h]
  change ((testSpec k).map ((𝟙 (CommAlgCat.of k k)).op) ≫ x) = x
  rw [op_id, (testSpec k).map_id, Category.id_comp]

private theorem exists_normalized_curve {G : GroupScheme k} {x : AffineLineCurve G}
    (hx : IsNonconstantCurve x) :
    ∃ y : AffineLineCurve G, curveAtZero y = 1 ∧ y ≠ 1 := by
  let z := constantCurve (curveAtZero x)
  refine ⟨x * z⁻¹, ?_, ?_⟩
  · let b := scalarPointMap (G := G) (CommAlgCat.ofHom (Polynomial.aeval (0 : k)))
    change b (x * z⁻¹) = 1
    calc
      _ = b x * b z⁻¹ := b.map_mul x z⁻¹
      _ = b x * (b z)⁻¹ := congrArg (b x * ·) (b.map_inv z)
      _ = b x * (b x)⁻¹ := congrArg (fun t => b x * t⁻¹) (origin_constant (curveAtZero x))
      _ = 1 := mul_inv_cancel _
  · intro h
    apply hx
    exact mul_inv_eq_one.mp h

private theorem isNonconstant_of_normalized_ne_one {G : GroupScheme k} {x : AffineLineCurve G}
    (hx : curveAtZero x = 1) (hn : x ≠ 1) : IsNonconstantCurve x := by
  unfold IsNonconstantCurve
  rw [hx]
  change x ≠ scalarPointMap (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k))) 1
  rwa [map_one]

private theorem spec_base_hom :
    ((testSpec k).obj (Opposite.op (CommAlgCat.of k k))).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
  rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from rfl, Spec.map_id]

open private isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria

/-- A smooth source over a separably closed field is schematically detected by its
rational points when the target is separated. -/
private theorem hom_ext_of_sepClosed_points [IsSepClosed k] {X Y : SchemeOver k}
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ x : Points X (CommAlgCat.of k k), x ≫ f = x ≫ g) : f = g := by
  let e := equalizer.ι f g
  have hc : IsClosedImmersion e.left := inferInstanceAs (IsClosedImmersion (equalizer.ι f g).left)
  have hd : Dense (Set.range e.left) := by
    apply dense_iff_inter_open.mpr
    intro W hW hne
    let V : X.left.Opens := ⟨W, hW⟩
    have hV : Nonempty V := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    obtain ⟨s, hs⟩ := Descent.exists_rational_point_of_smooth_open X.hom V hV
    let x : Points X (CommAlgCat.of k k) :=
      Over.homMk (s ≫ V.ι) ((Category.assoc _ _ _).trans (hs.trans spec_base_hom.symm))
    let y := equalizer.lift x (h x)
    let a := IsLocalRing.closedPoint k
    have hy : e.left (y.left a) = x.left a := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    exact ⟨x.left a, (s a).property, ⟨y.left a, hy⟩⟩
  have hr : IsReduced X.left := isReduced_of_smooth_over_field X.hom
  have hs : Surjective e.left := ⟨fun x => by
    have eq := (Scheme.Hom.isClosedEmbedding e.left).isClosed_range.closure_eq.symm.trans hd.closure_eq
    change x ∈ Set.range e.left
    rw [eq]
    trivial⟩
  have he : IsIso e.left := isIso_of_isClosedImmersion_of_surjective e.left
  apply Over.OverMorphism.ext
  apply (cancel_epi e.left).mp
  exact congrArg (fun t => t.left) (equalizer.condition f g)

private theorem smooth_affine_line :
    Smooth ((testSpec k).obj (Opposite.op (CommAlgCat.of k (Polynomial k)))).hom := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change (algebraMap k (Polynomial k)).Smooth
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance,
    Algebra.FinitePresentation.equiv (MvPolynomial.uniqueAlgEquiv k PUnit.{1})⟩

open private comp_conjugateFamily from LinearAlgebraicGroups.Affine.Stabilizers

private theorem centralizes_of_commutes_with_constants [IsSepClosed k]
    (U : AffineAlgebraicGroup k) [Smooth U.val.X.hom] {x : AffineLineCurve U.val}
    (h : ∀ g : Points U.val.X (CommAlgCat.of k k), Commute (constantCurve g) x) :
    Centralizes (𝟙 U.val) x := by
  let G := U.val
  let T := (testSpec k).obj (Opposite.op (CommAlgCat.of k (Polynomial k)))
  let X := G.X ⊗ T
  have : IsAffine G.X.left := U.property.1
  have : IsSeparated G.X.hom := IsSeparated.of_isAffineHom _
  have hT : Smooth T.hom := smooth_affine_line
  have hX : Smooth X.hom := by
    change Smooth (pullback.fst G.X.hom T.hom ≫ G.X.hom)
    infer_instance
  have : IsAffine T.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial k))))
  have : IsAffineHom G.X.hom := inferInstance
  have : IsAffine X.left := by
    change IsAffine (pullback G.X.hom T.hom)
    infer_instance
  have : QuasiCompact X.hom := inferInstance
  unfold Centralizes
  apply hom_ext_of_sepClosed_points
  intro a
  let g := a ≫ fst G.X T
  let t := a ≫ snd G.X T
  have ht : t ≫ (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k))).op =
      𝟙 _ := by
    apply Over.OverMorphism.ext
    have h := Over.w (t ≫ (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k))).op)
    rw [spec_base_hom] at h
    exact (Category.comp_id _).symm.trans h
  rw [comp_conjugateFamily]
  change (t ≫ x) * g * (t ≫ x)⁻¹ = g
  apply mul_inv_eq_iff_eq_mul.mpr
  have hc := (h g).symm
  have eq := congrArg (t ≫ ·) hc.eq
  simpa only [MonObj.comp_mul, constantCurve, mapPoints, ← Category.assoc, ht, Category.id_comp]
    using eq

/-- Over a separably closed field, a nonconstant curve gives a nonidentity
central curve killed by the characteristic. -/
private theorem exists_central_p_curve [IsSepClosed k] (p : ℕ) [CharP k p]
    (U : AffineAlgebraicGroup k) [Smooth U.val.X.hom] (hU : IsUnipotent U)
    {x : AffineLineCurve U.val} (hx : IsNonconstantCurve x) :
    ∃ y : AffineLineCurve U.val, curveAtZero y = 1 ∧ y ≠ 1 ∧
      Centralizes (𝟙 U.val) y ∧ y ^ p = 1 := by
  obtain ⟨x₀, h₀, hx₀⟩ := exists_normalized_curve hx
  obtain ⟨length, S, hS, hfactors⟩ := unipotentCentralSeries U hU
  let a := scalarPointMap (G := U.val) (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k)))
  let b := scalarPointMap (G := U.val) (CommAlgCat.ofHom (Polynomial.aeval (0 : k)))
  obtain ⟨y, hy₀, hy, hcomm⟩ := exists_commuting_point S hS a b ⟨x₀, h₀, hx₀⟩
  obtain ⟨i, hi, hp⟩ := exists_last_nonidentity_power y hy
    (pow_eq_one_of_additive_factors (p := p) S hfactors _ y)
  refine ⟨y ^ (p ^ i), ?_, hi, centralizes_of_commutes_with_constants U ?_, hp⟩
  · change b (y ^ (p ^ i)) = 1
    rw [map_pow, hy₀, one_pow]
  · intro g
    exact (hcomm g).pow_right _

section AffineCoordinates

variable {X : SchemeOver k} {A : TestAlgebra k}

private def affinePointEquiv (e : (testSpec k).obj (op A) ≅ X) (R : TestAlgebra k) :
    (A ⟶ R) ≃ Points X R where
  toFun f := (testSpec k).map f.op ≫ e.hom
  invFun x := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (x ≫ e.inv)).unop
  left_inv f := by
    have h : ((testSpec k).map f.op ≫ e.hom) ≫ e.inv = (testSpec k).map f.op :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e.hom_inv_id).trans (Category.comp_id _))
    exact congrArg Quiver.Hom.unop
      ((congrArg (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage h).trans
        ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage_map _))
  right_inv x := by simp

private theorem affinePointEquiv_natural (e : (testSpec k).obj (op A) ≅ X)
    {R T : TestAlgebra k} (b : R ⟶ T) (f : A ⟶ R) :
    affinePointEquiv e T (f ≫ b) = mapPoints b (affinePointEquiv e R f) := by
  change (testSpec k).map ((f ≫ b).op) ≫ e.hom =
    (testSpec k).map b.op ≫ (testSpec k).map f.op ≫ e.hom
  rw [op_comp, Functor.map_comp, Category.assoc]

private theorem finiteType_of_affine_coordinates (e : (testSpec k).obj (op A) ≅ X)
    (hX : LocallyOfFiniteType X.hom) : Algebra.FiniteType k A := by
  have he : LocallyOfFiniteType ((testSpec k).obj (op A)).hom := by
    rw [← Over.w e.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType e.hom.left X.hom).mpr hX
  exact RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff
    (P := @LocallyOfFiniteType)).mp he)

variable (L : Type u) [Field L] [Algebra k L]

private abbrev restrictedPolynomial :=
  (restrictTestAlgebra k L).obj (CommAlgCat.of L (Polynomial L))

private def coordinateAlgHomEquiv {B : TestAlgebra k} {D : Type u} [CommRing D] [Algebra k D]
    (e : B ≃+* D) (he : ∀ a : k, e (algebraMap k B a) = algebraMap k D a) :
    (A ⟶ B) ≃ (A →ₐ[k] D) :=
  let E : B ≃ₐ[k] D := { e with commutes' := he }
  { toFun := fun f => E.toAlgHom.comp f.hom
    invFun := fun f => ConcreteCategory.ofHom (E.symm.toAlgHom.comp f)
    left_inv := fun f => CommAlgCat.hom_ext (AlgHom.ext fun a => E.symm_apply_apply (f.hom a))
    right_inv := fun f => AlgHom.ext fun a => E.apply_symm_apply (f a) }

private def standardPolynomialHomEquiv :
    (A ⟶ restrictedPolynomial (k := k) L) ≃ (A →ₐ[k] Polynomial L) :=
  coordinateAlgHomEquiv (RingEquiv.refl (Polynomial L)) (fun _ => rfl)

private def curveCoordinates (e : (testSpec k).obj (op A) ≅ X) :
    Points ((baseChange k L).obj X) (CommAlgCat.of L (Polynomial L)) ≃
      (A →ₐ[k] Polynomial L) :=
  (baseChangePointsEquiv L X _).trans
    ((affinePointEquiv e _).symm.trans (standardPolynomialHomEquiv (k := k) L))

private theorem curveCoordinates_isNonconstant {G : GroupScheme k}
    (e : (testSpec k).obj (op A) ≅ G.X)
    (x : AffineLineCurve ((groupBaseChange k L).obj G)) :
    IsNonconstantCurve x ↔ ∃ a : A, ∃ n : ℕ, n ≠ 0 ∧
      ((curveCoordinates L e x) a).coeff n ≠ 0 := by
  let f := curveCoordinates L e x
  let ev : CommAlgCat.of L (Polynomial L) ⟶ CommAlgCat.of L L :=
    CommAlgCat.ofHom (Polynomial.aeval (0 : L))
  let c : CommAlgCat.of L L ⟶ CommAlgCat.of L (Polynomial L) :=
    CommAlgCat.ofHom (Algebra.ofId L (Polynomial L))
  let m : Polynomial L →ₐ[k] Polynomial L :=
    (IsScalarTower.toAlgHom k L (Polynomial L)).comp ((Polynomial.aeval (0 : L)).restrictScalars k)
  have eq : curveCoordinates L e (constantCurve (curveAtZero x)) = m.comp f := by
    let E := affinePointEquiv e (restrictedPolynomial (k := k) L)
    let C := standardPolynomialHomEquiv (A := A) (k := k) L
    let F := C.symm f
    let z := baseChangePoint k L G.X (CommAlgCat.of L (Polynomial L)) x
    have hf : E F = z := by
      change E (C.symm (C (E.symm z))) = z
      rw [C.symm_apply_apply, E.apply_symm_apply]
    have ht : baseChangePoint k L G.X _ (constantCurve (curveAtZero x)) =
        E (F ≫ (restrictTestAlgebra k L).map (ev ≫ c)) := by
      change baseChangePoint k L G.X _ (mapPoints c (mapPoints ev x)) = _
      rw [baseChangePointsNaturality, baseChangePointsNaturality]
      rw [Functor.map_comp, ← Category.assoc,
        affinePointEquiv_natural, affinePointEquiv_natural, hf]
    change C (E.symm (baseChangePoint k L G.X _ (constantCurve (curveAtZero x)))) = _
    rw [ht, E.symm_apply_apply]
    ext1 a
    rfl
  simp only [IsNonconstantCurve, ← (curveCoordinates L e).injective.ne_iff, eq]
  change f ≠ _ ↔ _
  constructor
  · intro h
    by_contra! hz
    apply h
    ext1 a
    apply Polynomial.ext
    intro n
    change (f a).coeff n = (Polynomial.C ((Polynomial.aeval (0 : L)) (f a))).coeff n
    by_cases hn : n = 0
    · subst n
      rw [Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_aeval_zero]
    · rw [hz a n hn, Polynomial.coeff_C_of_ne_zero hn]
  · rintro ⟨a, n, hn, hc⟩ h
    apply hc
    have h' := congrArg (fun f : A →ₐ[k] Polynomial L => (f a).coeff n) h
    exact h'.trans (Polynomial.coeff_C_of_ne_zero hn)

private theorem exists_curve_over_sepClosure [Algebra.IsTranscendentalSeparable k L]
    (U : AffineAlgebraicGroup k) {x : AffineLineCurve ((groupBaseChange k L).obj U.val)}
    (hx : IsNonconstantCurve x) :
    ∃ y : AffineLineCurve ((groupBaseChange k (SeparableClosure k)).obj U.val),
      IsNonconstantCurve y := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr U.property.1
  have : Algebra.FiniteType k A.unop := finiteType_of_affine_coordinates e U.property.2.1
  obtain ⟨a, n, hn, hc⟩ := (curveCoordinates_isNonconstant L e x).mp hx
  obtain ⟨g, hg⟩ := exists_polynomial_specialization (curveCoordinates L e x) a n hc
  refine ⟨(curveCoordinates (SeparableClosure k) e).symm g, ?_⟩
  apply (curveCoordinates_isNonconstant (SeparableClosure k) e _).mpr
  exact ⟨a, n, hn, by simpa only [Equiv.apply_symm_apply] using hg⟩

end AffineCoordinates

open private centralizes_iff mono_over closedSubgroupOfLocus
  from LinearAlgebraicGroups.Affine.Stabilizers

private theorem center_points_commute {G : GroupScheme k}
    (Z : ClosedSubgroup G) (hZ : RepresentsSubgroup Z (fun _ g => Centralizes (𝟙 G) g))
    (T : SchemeOver k) (x y : T ⟶ Z.group.X) : Commute x y := by
  let f := Z.inclusion.hom.hom
  have : Mono f := mono_over f Z.isClosedImmersion
  have hx : Centralizes (𝟙 G) (x ≫ f) := (hZ _ _).mpr ⟨x, rfl⟩
  have hxy := (centralizes_iff (𝟙 G) (x ≫ f)).mp hx T (𝟙 T) (y ≫ f)
  have hcomm : Commute (x ≫ f) (y ≫ f) := by simpa using hxy
  change x * y = y * x
  apply (cancel_mono f).mp
  exact (MonObj.mul_comp x y f).trans (hcomm.eq.trans (MonObj.mul_comp y x f).symm)

private theorem exists_center_power_kernel {G : GroupScheme k}
    (Z : ClosedSubgroup G) (hZ : RepresentsSubgroup Z (fun _ g => Centralizes (𝟙 G) g))
    [IsAffine G.X.left] (p : ℕ) :
    ∃ W : ClosedSubgroup Z.group, RepresentsSubgroup W (fun _ x => x ^ p = 1) := by
  let A := Z.group.X
  let q : A ⟶ A := (𝟙 A) ^ p
  let j := equalizer.ι q (1 : A ⟶ A)
  have : IsClosedImmersion Z.inclusion.hom.hom.left := Z.isClosedImmersion
  have : IsAffine A.left := isAffine_of_isAffineHom Z.inclusion.hom.hom.left
  have : IsSeparated A.hom := IsSeparated.of_isAffineHom _
  let P (T : SchemeOver k) : Subgroup (T ⟶ A) :=
    { carrier := {x | x ^ p = 1}
      one_mem' := one_pow _
      mul_mem' := fun {x y} hx hy => by
        change (x * y) ^ p = 1
        rw [(center_points_commute Z hZ T x y).mul_pow, show x ^ p = 1 from hx,
          show y ^ p = 1 from hy, mul_one]
      inv_mem' := fun {x} hx => by
        change x⁻¹ ^ p = 1
        rw [inv_pow, show x ^ p = 1 from hx, inv_one] }
  refine closedSubgroupOfLocus P j inferInstance fun T x => ?_
  have e₁ : x ≫ q = x ^ p := by
    induction p with
    | zero => exact MonObj.comp_one _
    | succ n ih =>
      simp only [q, pow_succ, MonObj.comp_mul, ih]
      exact congrArg (x ^ n * ·) (Category.comp_id x)
  have e₂ : x ≫ (1 : A ⟶ A) = 1 := MonObj.comp_one _
  change x ^ p = 1 ↔ ∃ z, z ≫ j = x
  rw [← e₁, ← e₂]
  exact ⟨fun h => ⟨equalizer.lift x h, equalizer.lift_ι x h⟩, fun ⟨z, hz⟩ => by
    rw [← hz, Category.assoc, Category.assoc, equalizer.condition]⟩

/-- The center cut out on all scheme families is commutative, so its power
kernel is a closed subgroup. -/
private theorem center_power_kernel (p : ℕ) (U : AffineAlgebraicGroup k) :
    ∃ (Z : ClosedSubgroup U.val) (W : ClosedSubgroup Z.group),
      RepresentsSubgroup Z (fun _ g => Centralizes (𝟙 U.val) g) ∧
      RepresentsSubgroup W (fun _ x => x ^ p = 1) ∧ IsKilledBy p W.group := by
  let H : ClosedSubgroup U.val :=
    ⟨U.val, 𝟙 U.val, inferInstanceAs (IsClosedImmersion (𝟙 U.val.X.left))⟩
  obtain ⟨Z, hZ⟩ := centralizerScheme k U H
  have : IsAffine U.val.X.left := U.property.1
  obtain ⟨W, hW⟩ := exists_center_power_kernel Z hZ p
  refine ⟨Z, W, hZ, hW, ?_⟩
  intro R x
  apply onPoints_injective W.inclusion W.isClosedImmersion R
  change onPoints W.inclusion R (x ^ p) = onPoints W.inclusion R 1
  exact ((onPoints W.inclusion R).map_pow x p).trans
    (((hW _ _).mpr ⟨x, rfl⟩).trans (onPoints W.inclusion R).map_one.symm)

private theorem exists_central_p_curve_over_sepClosure (p : ℕ) [CharP k p]
    (U : AffineAlgebraicGroup k) (hs : Smooth U.val.X.hom) (hu : IsUnipotent U)
    {L : Type u} [Field L] [Algebra k L] [Algebra.IsTranscendentalSeparable k L]
    {x : AffineLineCurve ((groupBaseChange k L).obj U.val)} (hx : IsNonconstantCurve x) :
    let V := (groupBaseChange k (SeparableClosure k)).obj U.val
    ∃ y : AffineLineCurve V, curveAtZero y = 1 ∧ y ≠ 1 ∧ Centralizes (𝟙 V) y ∧ y ^ p = 1 := by
  let S := SeparableClosure k
  obtain ⟨y, hy⟩ := exists_curve_over_sepClosure L U hx
  let V := baseChangedAlgebraicGroup S U
  have : Smooth V.val.X.hom := MorphismProperty.pullback_snd _ _ hs
  exact exists_central_p_curve p V (unipotenceFieldExtension U |>.mpr hu) hy

private theorem exists_finite_galois_polynomial_lift {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (f : A →ₐ[k] Polynomial (SeparableClosure k)) :
    ∃ (K : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k K)
      (_ : IsGalois k K) (g : A →ₐ[k] Polynomial K),
      (Polynomial.mapAlgHom K.val).comp g = f := by
  let S := SeparableClosure k
  obtain ⟨s, g, hg⟩ := lift_polynomial_coefficients f
  let B := Algebra.adjoin k (s : Set S)
  let E := IntermediateField.adjoin k (s : Set S)
  have : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K := IntermediateField.normalClosure k E S
  let i : B →ₐ[k] K := Subalgebra.inclusion
    ((IntermediateField.algebra_adjoin_le_adjoin k (s : Set S)).trans
      (show E ≤ K from IntermediateField.le_normalClosure E))
  have hki : (Polynomial.mapAlgHom K.val).comp (Polynomial.mapAlgHom i) =
      Polynomial.mapAlgHom B.val := by
    have eq : K.val.comp i = B.val := rfl
    exact (Polynomial.mapAlgHom_comp _ _ _).trans (congrArg Polynomial.mapAlgHom eq)
  refine ⟨K, normalClosure.is_finiteDimensional k E S, inferInstance,
    (Polynomial.mapAlgHom i).comp g, ?_⟩
  rw [← AlgHom.comp_assoc, hki, hg]

private theorem exists_normalized_curve_over_finiteGalois (V : AffineAlgebraicGroup k)
    (x : AffineLineCurve ((groupBaseChange k (SeparableClosure k)).obj V.val))
    (hx : IsNonconstantCurve x) :
    ∃ (K : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k K)
      (_ : IsGalois k K) (y : AffineLineCurve ((groupBaseChange k K).obj V.val)),
      curveAtZero y = 1 ∧ IsNonconstantCurve y := by
  let S := SeparableClosure k
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr V.property.1
  have : Algebra.FiniteType k A.unop := finiteType_of_affine_coordinates e V.property.2.1
  obtain ⟨a, n, hn, hc⟩ := (curveCoordinates_isNonconstant S e x).mp hx
  obtain ⟨K, hK, hGal, g, hg⟩ := exists_finite_galois_polynomial_lift (curveCoordinates S e x)
  let z : AffineLineCurve ((groupBaseChange k K).obj V.val) := (curveCoordinates K e).symm g
  have hz : IsNonconstantCurve z := by
    apply (curveCoordinates_isNonconstant K e z).mpr
    refine ⟨a, n, hn, ?_⟩
    rw [show curveCoordinates K e z = g from Equiv.apply_symm_apply _ _]
    rw [← hg, AlgHom.comp_apply, Polynomial.coeff_mapAlgHom_apply] at hc
    exact fun h => hc (by rw [h, map_zero])
  obtain ⟨y, hy, hne⟩ := exists_normalized_curve hz
  exact ⟨K, hK, hGal, y, hy, isNonconstant_of_normalized_ne_one hy hne⟩

private theorem factor_central_p_curve (p : ℕ) (U : AffineAlgebraicGroup k)
    (Z : ClosedSubgroup U.val) (W : ClosedSubgroup Z.group)
    (hZ : RepresentsSubgroup Z (fun _ g => Centralizes (𝟙 U.val) g))
    (hW : RepresentsSubgroup W (fun _ x => x ^ p = 1))
    {L : Type u} [Field L] [Algebra k L]
    {x : AffineLineCurve ((groupBaseChange k L).obj U.val)}
    (hx₀ : curveAtZero x = 1) (hx : x ≠ 1)
    (hxc : Centralizes (𝟙 ((groupBaseChange k L).obj U.val)) x) (hxp : x ^ p = 1) :
    ∃ y : AffineLineCurve ((groupBaseChange k L).obj W.group), IsNonconstantCurve y := by
  let F := groupBaseChange k L
  let R := CommAlgCat.of L (Polynomial L)
  let r := (restrictTestAlgebra k L).obj R
  let r₀ := CommAlgCat.of L L
  obtain ⟨hclosed, hz⟩ := centralizerSchemeBaseChange k L (𝟙 U.val) Z hZ
  have hc' : Centralizes (F.map (𝟙 U.val)) x :=
    (F.map_id U.val).symm ▸ hxc
  obtain ⟨z, hz'⟩ := (hz _ x).mp hc' 
  have hz' : onPoints (F.map Z.inclusion) R z = x := hz'
  have hzp : z ^ p = 1 := by
    apply onPoints_injective (F.map Z.inclusion) hclosed R
    change onPoints (F.map Z.inclusion) R (z ^ p) = onPoints (F.map Z.inclusion) R 1
    rw [map_pow, map_one, hz', hxp]
  let E := baseChangePointGroupEquiv L Z.group R
  have hz₁ : E z ^ p = 1 :=
    ((E.toMonoidHom.map_pow z p).symm.trans ((congrArg E hzp).trans E.map_one))
  obtain ⟨w, hw⟩ := (hW _ (E z)).mp hz₁
  let y := (baseChangePointGroupEquiv L W.group R).symm w
  have hy : onPoints (F.map W.inclusion) R y = z := by
    apply E.injective
    change baseChangePoint k L Z.group.X R (y ≫ (F.map W.inclusion).hom.hom) =
      baseChangePoint k L Z.group.X R z
    refine (baseChangePointsSchemeNaturality k L W.inclusion.hom.hom R y).trans ?_
    exact (congrArg (· ≫ W.inclusion.hom.hom) ((baseChangePointGroupEquiv L W.group R).apply_symm_apply w)).trans hw
  let i := F.map W.inclusion ≫ F.map Z.inclusion
  have hi : onPoints i R y = x := by
    rw [onPoints_comp, hy, hz']
  have hc : IsClosedImmersion (F.map W.inclusion).hom.hom.left :=
    baseChangeClosedSubgroup k L W.inclusion W.isClosedImmersion
  have hci : IsClosedImmersion i.hom.hom.left :=
    IsClosedImmersion.comp _ _
  have hy₀ : curveAtZero y = 1 := by
    apply onPoints_injective i hci r₀
    let a : R ⟶ r₀ := CommAlgCat.ofHom (Polynomial.aeval (0 : L))
    change onPoints i r₀ (scalarPointMap a y) = onPoints i r₀ 1
    rw [onPoints_natural, hi, map_one]
    exact hx₀
  have hne : y ≠ 1 := by
    intro ey
    apply hx
    exact hi.symm.trans ((congrArg (onPoints i R) ey).trans (onPoints i R).map_one)
  exact ⟨y, isNonconstant_of_normalized_ne_one hy₀ hne⟩

open Coalgebra HopfAlgebra WithConv

variable {K : Type u} [Field K] [Algebra k K]

section PolynomialImages

private def extendCoefficients {B P : Type u} [CommRing B] [Algebra k B]
    [CommRing P] [Algebra k P] [Algebra K P] [IsScalarTower k K P] (f : B →ₐ[k] P) :
    K ⊗[k] B →ₐ[K] P :=
  Algebra.TensorProduct.lift (Algebra.ofId K P) f fun _ _ => Commute.all _ _

private theorem extendCoefficients_tmul {B P : Type u} [CommRing B] [Algebra k B]
    [CommRing P] [Algebra k P] [Algebra K P] [IsScalarTower k K P] (f : B →ₐ[k] P)
    (r : K) (b : B) : extendCoefficients (K := K) f (r ⊗ₜ[k] b) = r • f b := by
  rw [extendCoefficients, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]

private def polynomialOrigin (α : Type) : MvPolynomial α K →ₐ[K] K :=
  MvPolynomial.aeval (fun _ => (0 : K))

private def IsPointedFamily {A : HopfAlgebraCategory k} {α : Type}
    (f : A →ₐ[k] MvPolynomial α K) : Prop :=
  ((polynomialOrigin α).restrictScalars k).comp f = (Algebra.ofId k K).comp (Bialgebra.counitAlgHom k A)

private def polynomialProduct {A : HopfAlgebraCategory k} {α β : Type}
    (f : A →ₐ[k] MvPolynomial α K) (g : A →ₐ[k] MvPolynomial β K) :
    A →ₐ[k] MvPolynomial (α ⊕ β) K :=
  (toConv (((MvPolynomial.rename Sum.inl).restrictScalars k).comp f) *
    toConv (((MvPolynomial.rename Sum.inr).restrictScalars k).comp g)).ofConv

private theorem polynomialProduct_comp {A : HopfAlgebraCategory k} {α β : Type}
    (f : A →ₐ[k] MvPolynomial α K) (g : A →ₐ[k] MvPolynomial β K)
    {P : Type u} [CommRing P] [Algebra k P] [Algebra K P] [IsScalarTower k K P]
    (e : MvPolynomial (α ⊕ β) K →ₐ[K] P) :
    (e.restrictScalars k).comp (polynomialProduct f g) =
      (toConv (((e.comp (MvPolynomial.rename Sum.inl)).restrictScalars k).comp f) *
       toConv (((e.comp (MvPolynomial.rename Sum.inr)).restrictScalars k).comp g)).ofConv := by
  rw [polynomialProduct, AlgHom.comp_convMul_distrib]
  rfl

private theorem IsPointedFamily.product {A : HopfAlgebraCategory k} {α β : Type}
    {f : A →ₐ[k] MvPolynomial α K} {g : A →ₐ[k] MvPolynomial β K}
    (hf : IsPointedFamily f) (hg : IsPointedFamily g) :
    IsPointedFamily (polynomialProduct f g) := by
  let e : MvPolynomial (α ⊕ β) K →ₐ[K] K := polynomialOrigin (α ⊕ β)
  change (e.restrictScalars k).comp _ = _
  have hl : e.comp (MvPolynomial.rename Sum.inl) = polynomialOrigin α := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e, polynomialOrigin]
  have hr : e.comp (MvPolynomial.rename Sum.inr) = polynomialOrigin β := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e, polynomialOrigin]
  rw [polynomialProduct_comp, hl, hr, hf, hg]
  exact congrArg WithConv.ofConv (one_mul (1 : WithConv (A →ₐ[k] K)))

private theorem polynomialProduct_restrict_left {A : HopfAlgebraCategory k} {α β : Type}
    (f : A →ₐ[k] MvPolynomial α K) {g : A →ₐ[k] MvPolynomial β K}
    (hg : IsPointedFamily g) :
    ∃ e : MvPolynomial (α ⊕ β) K →ₐ[K] MvPolynomial α K,
      (e.restrictScalars k).comp (polynomialProduct f g) = f := by
  let e : MvPolynomial (α ⊕ β) K →ₐ[K] MvPolynomial α K :=
    MvPolynomial.aeval (Sum.elim MvPolynomial.X fun _ : β => (0 : MvPolynomial α K))
  refine ⟨e, ?_⟩
  have hl : e.comp (MvPolynomial.rename Sum.inl) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e]
  have hr : e.comp (MvPolynomial.rename Sum.inr) =
      (Algebra.ofId K (MvPolynomial α K)).comp (polynomialOrigin β) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e, polynomialOrigin]
  rw [polynomialProduct_comp, hl, hr]
  change (toConv f * toConv (((Algebra.ofId K (MvPolynomial α K)).restrictScalars k).comp
    (((polynomialOrigin β).restrictScalars k).comp g))).ofConv = f
  rw [hg]
  change (toConv f * 1).ofConv = f
  rw [mul_one, ofConv_toConv]

private theorem polynomialProduct_restrict_right {A : HopfAlgebraCategory k} {α β : Type}
    {f : A →ₐ[k] MvPolynomial α K} (g : A →ₐ[k] MvPolynomial β K)
    (hf : IsPointedFamily f) :
    ∃ e : MvPolynomial (α ⊕ β) K →ₐ[K] MvPolynomial β K,
      (e.restrictScalars k).comp (polynomialProduct f g) = g := by
  let e : MvPolynomial (α ⊕ β) K →ₐ[K] MvPolynomial β K :=
    MvPolynomial.aeval (Sum.elim (fun _ : α => (0 : MvPolynomial β K)) MvPolynomial.X)
  refine ⟨e, ?_⟩
  have hl : e.comp (MvPolynomial.rename Sum.inl) =
      (Algebra.ofId K (MvPolynomial β K)).comp (polynomialOrigin α) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e, polynomialOrigin]
  have hr : e.comp (MvPolynomial.rename Sum.inr) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e]
  rw [polynomialProduct_comp, hl, hr]
  change (toConv (((Algebra.ofId K (MvPolynomial β K)).restrictScalars k).comp
    (((polynomialOrigin α).restrictScalars k).comp f)) * toConv g).ofConv = g
  rw [hf]
  change (1 * toConv g).ofConv = g
  rw [one_mul, ofConv_toConv]

private theorem extendCoefficients_comp {B P Q : Type u} [CommRing B] [Algebra k B]
    [CommRing P] [Algebra k P] [Algebra K P] [IsScalarTower k K P]
    [CommRing Q] [Algebra k Q] [Algebra K Q] [IsScalarTower k K Q]
    (f : B →ₐ[k] P) (g : P →ₐ[K] Q) :
    extendCoefficients (K := K) ((g.restrictScalars k).comp f) = g.comp (extendCoefficients (K := K) f) := by
  apply AlgHom.toLinearMap_injective
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext'
  intro r b
  change extendCoefficients (K := K) ((g.restrictScalars k).comp f) (r ⊗ₜ[k] b) =
    g (extendCoefficients (K := K) f (r ⊗ₜ[k] b))
  rw [extendCoefficients_tmul, extendCoefficients_tmul, map_smul]
  rfl

/-- Products of pointed polynomial families give a directed system of prime kernels.
Finite height gives a least kernel, which is realized by one of the families. -/
private theorem exists_least_polynomial_kernel (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] :
    ∃ (α : Type) (f : A →ₐ[k] MvPolynomial α K), IsPointedFamily f ∧
      ∀ (β : Type) (g : A →ₐ[k] MvPolynomial β K), IsPointedFamily g →
        RingHom.ker (extendCoefficients (K := K) f) ≤ RingHom.ker (extendCoefficients (K := K) g) := by
  classical
  have : Algebra.FiniteType K (K ⊗[k] A) := inferInstance
  have : IsNoetherianRing (K ⊗[k] A) := Algebra.FiniteType.isNoetherianRing K _
  let S : Set (Ideal (K ⊗[k] A)) :=
    {I | ∃ (α : Type) (f : A →ₐ[k] MvPolynomial α K), IsPointedFamily f ∧
      RingHom.ker (extendCoefficients (K := K) f) = I}
  have hS : S.Nonempty := by
    let f : A →ₐ[k] MvPolynomial PUnit K := (1 : WithConv (A →ₐ[k] MvPolynomial PUnit K)).ofConv
    refine ⟨RingHom.ker (extendCoefficients (K := K) f), PUnit, f, ?_, rfl⟩
    unfold IsPointedFamily
    ext a
    change polynomialOrigin PUnit (algebraMap k (MvPolynomial PUnit K) (counit a)) =
      algebraMap k K (counit a)
    exact AlgHom.commutes ((polynomialOrigin PUnit).restrictScalars k) _
  obtain ⟨I, ⟨α, f, hf, rfl⟩, hmin⟩ := (InvImage.wf
    (fun I : Ideal (K ⊗[k] A) => I.height.toNat) Nat.lt_wfRel.wf).has_min S hS
  refine ⟨α, f, hf, fun β g hg => ?_⟩
  let h := polynomialProduct f g
  let J := RingHom.ker (extendCoefficients (K := K) h)
  have hJ : J ∈ S := ⟨α ⊕ β, h, hf.product hg, rfl⟩
  obtain ⟨l, hl⟩ := polynomialProduct_restrict_left f hg
  obtain ⟨r, hr⟩ := polynomialProduct_restrict_right g hf
  have ker_le {δ : Type} (a : A →ₐ[k] MvPolynomial δ K)
      (e : MvPolynomial (α ⊕ β) K →ₐ[K] MvPolynomial δ K)
      (he : (e.restrictScalars k).comp h = a) :
      J ≤ RingHom.ker (extendCoefficients (K := K) a) := by
    intro x hx
    change extendCoefficients (K := K) h x = 0 at hx
    change extendCoefficients (K := K) a x = 0
    rw [← he, extendCoefficients_comp, AlgHom.comp_apply, hx, map_zero]
  have hele := ker_le f l hl
  have he : J = RingHom.ker (extendCoefficients (K := K) f) := by
    have : J.IsPrime := RingHom.ker_isPrime _
    have : (RingHom.ker (extendCoefficients (K := K) f)).IsPrime := RingHom.ker_isPrime _
    apply Ideal.eq_of_le_of_height_le J hele
    have hm : (RingHom.ker (extendCoefficients (K := K) f)).height.toNat ≤ J.height.toNat :=
      Nat.le_of_not_gt (hmin J hJ)
    have hc := ENat.natCast_toNat_eq_self.mpr
      (Ideal.height_ne_top_of_isPrime (I := RingHom.ker (extendCoefficients (K := K) f)))
    rw [← hc]
    exact (ENat.natCast_le_natCast.mpr hm).trans (ENat.natCast_toNat_le_self _)
  rw [← he]
  exact ker_le g r hr

open Descent.SemilinearAction

private theorem extendCoefficients_precomp {B C P : Type u} [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [CommRing P] [Algebra k P] [Algebra K P] [IsScalarTower k K P]
    (f : C →ₐ[k] P) (g : B →ₐ[k] C) :
    extendCoefficients (K := K) (f.comp g) =
      (extendCoefficients (K := K) f).comp (Algebra.TensorProduct.map (AlgHom.id K K) g) := by
  apply AlgHom.toLinearMap_injective
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext'
  intro r b
  change extendCoefficients (K := K) (f.comp g) (r ⊗ₜ[k] b) =
    extendCoefficients (K := K) f (Algebra.TensorProduct.map (AlgHom.id K K) g (r ⊗ₜ[k] b))
  rw [Algebra.TensorProduct.map_tmul, extendCoefficients_tmul, extendCoefficients_tmul]
  rfl

private theorem conjugate_preserves_origin {A : HopfAlgebraCategory k} {α : Type}
    {f : A →ₐ[k] MvPolynomial α K} (hf : IsPointedFamily f) (s : Gal(K/k)) :
    IsPointedFamily ((MvPolynomial.mapAlgHom s.toAlgHom).comp f) := by
  apply AlgHom.ext
  intro a
  have he := AlgHom.congr_fun hf a
  change polynomialOrigin α (f a) = algebraMap k K (counit a) at he
  change polynomialOrigin α (MvPolynomial.map (s : K →+* K) (f a)) =
    algebraMap k K (counit a)
  simp only [polynomialOrigin, MvPolynomial.aeval_zero', Algebra.algebraMap_self,
    RingHom.id_apply] at he ⊢
  rw [MvPolynomial.constantCoeff_map, he]
  exact s.commutes _

private theorem extendCoefficients_conjugate {B : Type u} [CommRing B] [Algebra k B]
    {α : Type} (f : B →ₐ[k] MvPolynomial α K) (s : Gal(K/k)) (a : K ⊗[k] B) :
    extendCoefficients (K := K) ((MvPolynomial.mapAlgHom s.toAlgHom).comp f)
        ((scalarExtension (k := k) (K := K) B).act s a) =
      MvPolynomial.map (s : K →+* K) (extendCoefficients (K := K) f a) := by
  let l := extendCoefficients (K := K) ((MvPolynomial.mapAlgHom s.toAlgHom).comp f)
  let r := extendCoefficients (K := K) f
  let m := Algebra.TensorProduct.map s.toAlgHom (AlgHom.id k B)
  let c : MvPolynomial α K →ₐ[k] MvPolynomial α K := MvPolynomial.mapAlgHom s.toAlgHom
  have h : (l.restrictScalars k).comp m = c.comp (r.restrictScalars k) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro b x
    change l (m (b ⊗ₜ[k] x)) = c (r (b ⊗ₜ[k] x))
    rw [show m (b ⊗ₜ[k] x) = s b ⊗ₜ[k] x from rfl]
    change extendCoefficients (K := K) ((MvPolynomial.mapAlgHom s.toAlgHom).comp f)
      (s b ⊗ₜ[k] x) = c (extendCoefficients (K := K) f (b ⊗ₜ[k] x))
    rw [extendCoefficients_tmul, extendCoefficients_tmul]
    simp only [c, Algebra.smul_def, AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply,
      map_mul, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    rfl
  exact AlgHom.congr_fun h a

private theorem least_kernel_stable {A : HopfAlgebraCategory k} {α : Type}
    {f : A →ₐ[k] MvPolynomial α K} (hf : IsPointedFamily f)
    (hle : ∀ (β : Type) (g : A →ₐ[k] MvPolynomial β K), IsPointedFamily g →
        RingHom.ker (extendCoefficients (K := K) f) ≤ RingHom.ker (extendCoefficients (K := K) g)) :
    ∀ (s : Gal(K/k)) (a : K ⊗[k] A), extendCoefficients (K := K) f a = 0 →
      extendCoefficients (K := K) f ((scalarExtension (k := k) (K := K) A).act s a) = 0 := by
  intro s a ha
  let action := scalarExtension (k := k) (K := K) A
  let g := (MvPolynomial.mapAlgHom (s⁻¹).toAlgHom).comp f
  have hg : extendCoefficients (K := K) g a = 0 := hle α g (conjugate_preserves_origin hf s⁻¹) ha
  have e := extendCoefficients_conjugate f s⁻¹ (action.act s a)
  rw [← action.mul_act, inv_mul_cancel, action.one_act] at e
  let r : MvPolynomial α K →+* MvPolynomial α K := MvPolynomial.map (s⁻¹ : Gal(K/k)).toRingHom
  have hr : Function.Injective r := MvPolynomial.map_injective _ (AlgEquiv.injective s⁻¹)
  apply hr
  calc
    _ = extendCoefficients (K := K) g a := e.symm
    _ = 0 := hg
    _ = r 0 := r.map_zero.symm

/-- A Galois-stable kernel with zero fixed part vanishes by semilinear descent. -/
private theorem extendCoefficients_injective_of_stable [FiniteDimensional k K] [IsGalois k K]
    {B P : Type u} [CommRing B] [Algebra k B] [CommRing P] [Algebra k P] [Algebra K P]
    [IsScalarTower k K P] {f : B →ₐ[k] P} (hf : Function.Injective f)
    (hstable : ∀ (s : Gal(K/k)) (a : K ⊗[k] B), extendCoefficients (K := K) f a = 0 →
      extendCoefficients (K := K) f ((scalarExtension (k := k) (K := K) B).act s a) = 0) :
    Function.Injective (extendCoefficients (K := K) f) := by
  let D := scalarExtension (k := k) (K := K) B
  let J : Submodule K (K ⊗[k] B) := LinearMap.ker (extendCoefficients (K := K) f).toLinearMap
  let action : Descent.SemilinearAction k K J :=
    { act := fun s =>
        { toFun := fun z => ⟨D.act s z, hstable s z z.property⟩
          invFun := fun z => ⟨D.act s⁻¹ z, hstable s⁻¹ z z.property⟩
          left_inv := fun z => Subtype.ext (by
            change D.act s⁻¹ (D.act s z) = z
            rw [← D.mul_act, inv_mul_cancel, D.one_act])
          right_inv := fun z => Subtype.ext (by
            change D.act s (D.act s⁻¹ z) = z
            rw [← D.mul_act, mul_inv_cancel, D.one_act])
          map_add' := fun x y => Subtype.ext (map_add (D.act s) (x : K ⊗[k] B) y) }
      one_act := fun z => Subtype.ext (D.one_act z)
      mul_act := fun s t z => Subtype.ext (D.mul_act s t z)
      map_smul := fun s r z => Subtype.ext (D.map_smul s r z) }
  have hbot : Submodule.span K (action.fixed : Set J) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    intro a ha
    let a₀ : D.fixed := ⟨a, fun s => congrArg Subtype.val (ha s)⟩
    obtain ⟨b, hb⟩ := (scalarExtension_bijective (k := k) (K := K) B).surjective a₀
    have hba : (1 : K) ⊗ₜ[k] b = (a : K ⊗[k] B) := congrArg Subtype.val hb
    have hfb : extendCoefficients (K := K) f (a : K ⊗[k] B) = 0 := a.property
    rw [← hba, extendCoefficients_tmul, one_smul] at hfb
    have hb₀ := (injective_iff_map_eq_zero f).mp hf b hfb
    change a ∈ (⊥ : Submodule K J)
    rw [Submodule.mem_bot]
    apply Subtype.ext
    rw [← hba, hb₀, TensorProduct.tmul_zero]
    rfl
  rw [action.span_fixed_eq_top] at hbot
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have he : (⟨a, ha⟩ : J) ∈ (⊥ : Submodule K J) := hbot Submodule.mem_top
  rw [Submodule.mem_bot] at he
  exact congrArg Subtype.val he

private def independentTensor (B C : Type u) [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] :
    B ⊗[k] C →ₐ[k] (K ⊗[k] B) ⊗[K] (K ⊗[k] C) :=
  let e := (Algebra.TensorProduct.cancelBaseChange k K K (K ⊗[k] B) C).trans
    (Algebra.TensorProduct.assoc k k K K B C)
  (e.symm.toAlgHom.restrictScalars k).comp Algebra.TensorProduct.includeRight

private theorem independentTensor_tmul {B C : Type u} [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] (b : B) (c : C) :
    independentTensor (K := K) B C (b ⊗ₜ[k] c) =
      ((1 : K) ⊗ₜ[k] b) ⊗ₜ[K] ((1 : K) ⊗ₜ[k] c) := by
  simp [independentTensor, Algebra.TensorProduct.includeRight_apply]

private theorem independentTensor_injective (B C : Type u) [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] : Function.Injective (independentTensor (k := k) (K := K) B C) := by
  let e := (Algebra.TensorProduct.cancelBaseChange k K K (K ⊗[k] B) C).trans
    (Algebra.TensorProduct.assoc k k K K B C)
  let i : B ⊗[k] C →ₐ[k] K ⊗[k] (B ⊗[k] C) := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  exact e.symm.injective.comp hi

private def polynomialPair {B C : Type u} [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] {α β : Type}
    (f : B →ₐ[k] MvPolynomial α K) (g : C →ₐ[k] MvPolynomial β K) :
    B ⊗[k] C →ₐ[k] MvPolynomial (α ⊕ β) K :=
  let m := (MvPolynomial.tensorEquivSum K α β K).toAlgHom.comp
    (Algebra.TensorProduct.map (extendCoefficients (K := K) f) (extendCoefficients (K := K) g))
  (m.restrictScalars k).comp (independentTensor (K := K) B C)

private theorem polynomialPair_tmul {B C : Type u} [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] {α β : Type}
    (f : B →ₐ[k] MvPolynomial α K) (g : C →ₐ[k] MvPolynomial β K) (b : B) (c : C) :
    polynomialPair f g (b ⊗ₜ[k] c) =
      MvPolynomial.rename Sum.inl (f b) * MvPolynomial.rename Sum.inr (g c) := by
  let e := MvPolynomial.tensorEquivSum K α β K
  have hl : e.toAlgHom.comp Algebra.TensorProduct.includeLeft = MvPolynomial.rename Sum.inl := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e]
  have hr : e.toAlgHom.comp Algebra.TensorProduct.includeRight = MvPolynomial.rename Sum.inr := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e]
  change e (Algebra.TensorProduct.map (extendCoefficients (K := K) f) (extendCoefficients (K := K) g)
    (independentTensor (K := K) B C (b ⊗ₜ[k] c))) = _
  rw [independentTensor_tmul, Algebra.TensorProduct.map_tmul,
    extendCoefficients_tmul, extendCoefficients_tmul, one_smul, one_smul]
  rw [← AlgHom.congr_fun hl, ← AlgHom.congr_fun hr]
  change e (f b ⊗ₜ[K] g c) = e (f b ⊗ₜ[K] 1) * e (1 ⊗ₜ[K] g c)
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem polynomialPair_injective {B C : Type u} [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] {α β : Type}
    {f : B →ₐ[k] MvPolynomial α K} {g : C →ₐ[k] MvPolynomial β K}
    (hf : Function.Injective (extendCoefficients (K := K) f))
    (hg : Function.Injective (extendCoefficients (K := K) g)) :
    Function.Injective (polynomialPair f g) := by
  exact (MvPolynomial.tensorEquivSum K α β K).injective.comp
    ((TensorProduct.map_injective_of_flat_flat (extendCoefficients (K := K) f).toLinearMap
      (extendCoefficients (K := K) g).toLinearMap hf hg).comp (independentTensor_injective (k := k) (K := K) B C))

private theorem polynomialProduct_eq {A : HopfAlgebraCategory k} {α β : Type}
    (f : A →ₐ[k] MvPolynomial α K) (g : A →ₐ[k] MvPolynomial β K) :
    polynomialProduct f g = (polynomialPair f g).comp (Bialgebra.comulAlgHom k A) := by
  let l := ((MvPolynomial.rename (R := K) (Sum.inl : α → α ⊕ β)).restrictScalars k).comp f
  let r := ((MvPolynomial.rename (R := K) (Sum.inr : β → α ⊕ β)).restrictScalars k).comp g
  have eq : Algebra.TensorProduct.lift l r (fun _ _ => Commute.all _ _) = polynomialPair f g := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro a b
    change Algebra.TensorProduct.lift l r (fun _ _ => Commute.all _ _) (a ⊗ₜ[k] b) =
      polynomialPair f g (a ⊗ₜ[k] b)
    rw [Algebra.TensorProduct.lift_tmul, polynomialPair_tmul]
    rfl
  apply AlgHom.ext
  intro x
  change (toConv l * toConv r) x = polynomialPair f g (comul x)
  rw [AlgHom.convMul_apply, eq]

private theorem quotientEmbeds_after_baseChange [FiniteDimensional k K] [IsGalois k K]
    {A : HopfAlgebraCategory k} {α : Type}
    {f : A →ₐ[k] MvPolynomial α K}
    (hf : IsPointedFamily f)
    (hle : ∀ (β : Type) (g : A →ₐ[k] MvPolynomial β K), IsPointedFamily g →
        RingHom.ker (extendCoefficients (K := K) f) ≤ RingHom.ker (extendCoefficients (K := K) g)) :
    ∃ (g : (A ⧸ RingHom.ker f) →ₐ[k] MvPolynomial α K),
      g.comp (Ideal.Quotient.mkₐ k (RingHom.ker f)) = f ∧
      Function.Injective g ∧ Function.Injective (extendCoefficients (K := K) g) := by
  let I := RingHom.ker f
  let q := Ideal.Quotient.mkₐ k I
  let g := Ideal.Quotient.liftₐ I f (fun _ hx => hx)
  have hgf : g.comp q = f := rfl
  have hgi : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hx
  refine ⟨g, hgf, hgi, extendCoefficients_injective_of_stable hgi ?_⟩
  let m := Algebra.TensorProduct.map (AlgHom.id K K) q
  intro s x hx
  have hms : Function.Surjective m := by
    exact Algebra.TensorProduct.map_surjective (f := AlgHom.id K K) (g := q)
      (fun a => ⟨a, rfl⟩) Ideal.Quotient.mk_surjective
  obtain ⟨y, rfl⟩ := hms x
  have he : extendCoefficients (K := K) f = (extendCoefficients (K := K) g).comp m := by
    rw [← hgf, extendCoefficients_precomp]
  have hmy : m ((scalarExtension (k := k) (K := K) A).act s y) =
      (scalarExtension (k := k) (K := K) (A ⧸ I)).act s (m y) :=
    scalarExtension_equivariant (K := K) q.toLinearMap s y
  rw [← hmy]
  have hy : extendCoefficients (K := K) f y = 0 := by simpa only [he, AlgHom.comp_apply] using hx
  have hz := least_kernel_stable hf hle s y hy
  simpa only [he, AlgHom.comp_apply] using hz

/-- The least polynomial kernel defines a subgroup. Two independent copies of the
dominant family test the coproduct, and the inverse family tests the antipode. -/
private theorem least_polynomial_kernel_isHopfIdeal
    {A : HopfAlgebraCategory k} {α : Type} {f : A →ₐ[k] MvPolynomial α K}
    (hf : IsPointedFamily f)
    (hle : ∀ (β : Type) (g : A →ₐ[k] MvPolynomial β K), IsPointedFamily g →
        RingHom.ker (extendCoefficients (K := K) f) ≤ RingHom.ker (extendCoefficients (K := K) g))
    {g : (A ⧸ RingHom.ker f) →ₐ[k] MvPolynomial α K}
    (hg : g.comp (Ideal.Quotient.mkₐ k (RingHom.ker f)) = f)
    (hgi : Function.Injective (extendCoefficients (K := K) g)) :
    (RingHom.ker f).IsHopfIdeal k := by
  let I := RingHom.ker f
  let q := Ideal.Quotient.mkₐ k I
  have vanish {β : Type} {v : A →ₐ[k] MvPolynomial β K} (hv : IsPointedFamily v)
      (a : A) (ha : a ∈ I) : v a = 0 := by
    have hz : (1 : K) ⊗ₜ[k] a ∈ RingHom.ker (extendCoefficients (K := K) f) := by
      change f a = 0 at ha
      change extendCoefficients (K := K) f (1 ⊗ₜ[k] a) = 0
      rw [extendCoefficients_tmul, one_smul, ha]
    have hz' : extendCoefficients (K := K) v (1 ⊗ₜ[k] a) = 0 := hle β v hv hz
    simpa only [extendCoefficients_tmul, one_smul] using hz'
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · intro a ha
    have e := AlgHom.congr_fun hf a
    change polynomialOrigin α (f a) = algebraMap k K (counit a) at e
    rw [show f a = 0 from ha, map_zero] at e
    exact (injective_iff_map_eq_zero (algebraMap k K)).mp (algebraMap k K).injective _ e.symm
  · intro a ha
    change Algebra.TensorProduct.map q q (comul (R := k) a) = 0
    have e : (polynomialPair g g).comp (Algebra.TensorProduct.map q q) = polynomialPair f f := by
      apply AlgHom.toLinearMap_injective
      apply TensorProduct.ext'
      intro x y
      change polynomialPair g g (Algebra.TensorProduct.map q q (x ⊗ₜ[k] y)) =
        polynomialPair f f (x ⊗ₜ[k] y)
      rw [Algebra.TensorProduct.map_tmul, polynomialPair_tmul, polynomialPair_tmul]
      exact congrArg₂ (fun a b => MvPolynomial.rename Sum.inl a * MvPolynomial.rename Sum.inr b)
        (AlgHom.congr_fun hg x) (AlgHom.congr_fun hg y)
    apply (injective_iff_map_eq_zero (polynomialPair g g)).mp (polynomialPair_injective hgi hgi)
    change ((polynomialPair g g).comp (Algebra.TensorProduct.map q q)) (comul a) = 0
    rw [e]
    exact (AlgHom.congr_fun (polynomialProduct_eq f f) a).symm.trans (vanish (hf.product hf) a ha)
  · intro a ha
    let inv := f.comp (antipodeAlgHom k A)
    have hi : IsPointedFamily inv := by
      unfold IsPointedFamily at hf ⊢
      rw [show inv = f.comp (antipodeAlgHom k A) from rfl,
        ← AlgHom.comp_assoc, hf, AlgHom.comp_assoc, AlgHom.counitAlgHom_comp_antipodeAlgHom]
    exact vanish hi a ha

open private extendedSpecIso from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem geometricallyReduced_specGroup_of_polynomial_embedding
    (A : HopfAlgebraCategory k) {α : Type} (m : A →ₐ[k] MvPolynomial α k)
    (hm : Function.Injective m) : GeometricallyReduced (specGroup A).X.hom := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := AlgebraicGeometry.IsReduced)).mpr ?_⟩
  intro L _ _
  let n := Algebra.TensorProduct.map (AlgHom.id L L) m
  have hn : Function.Injective n := Module.Flat.lTensor_preserves_injective_linearMap
    m.toLinearMap hm
  let e : L ⊗[k] MvPolynomial α k ≃ₐ[L] MvPolynomial α L :=
    MvPolynomial.algebraTensorAlgEquiv k L
  have : _root_.IsReduced (L ⊗[k] A) := isReduced_of_injective
    (e.toAlgHom.comp n) (e.injective.comp hn)
  have : AlgebraicGeometry.IsReduced (specGroup (extendedHopf L A)).X.left :=
    inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (L ⊗[k] A))))
  let j := extendedSpecIso L A
  exact isReduced_of_isOpenImmersion j.inv.left

open private smooth_of_smooth_after_fieldExtension
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem smooth_specGroup_of_baseChange_polynomial_embedding
    (A : HopfAlgebraCategory k) [Algebra.FiniteType k A]
    {α : Type} (m : (K ⊗[k] A) →ₐ[K] MvPolynomial α K) (hm : Function.Injective m) :
    Smooth (specGroup A).X.hom := by
  have : Algebra.FiniteType K (K ⊗[k] A) := inferInstance
  have : LocallyOfFiniteType (specGroup (extendedHopf K A)).X.hom :=
    (hopfSpec_locallyOfFiniteType_iff K _).mpr ‹Algebra.FiniteType K (K ⊗[k] A)›
  have hs : Smooth (specGroup (extendedHopf K A)).X.hom :=
    (groupSmoothnessCriteria K (specGroup (extendedHopf K A))).1.mpr
      (geometricallyReduced_specGroup_of_polynomial_embedding (extendedHopf K A) m hm)
  apply smooth_of_smooth_after_fieldExtension (K := K)
  let e := extendedSpecIso K A
  have eq := Over.w e.hom
  change e.hom.left ≫ pullback.snd (specGroup A).X.hom (fieldSpecMap k K) =
    (specGroup (extendedHopf K A)).X.hom at eq
  exact (MorphismProperty.cancel_left_of_respectsIso @Smooth e.hom.left _).mp (by rw [eq]; exact hs)

/-- Over a finite Galois extension, every pointed polynomial family factors
through one smooth connected closed subgroup defined over the ground field. -/
private theorem exists_smooth_hopfQuotient (K : Type u) [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] :
    ∃ (I : Ideal A) (_ : I.IsHopfIdeal k),
      Smooth (specGroup (hopfQuotient A I)).X.hom ∧
      ConnectedSpace (specGroup (hopfQuotient A I)).X.left ∧
      ∀ (α : Type) (f : A →ₐ[k] MvPolynomial α K), IsPointedFamily f → I ≤ RingHom.ker f := by
  obtain ⟨α, f, hf, hle⟩ := exists_least_polynomial_kernel (K := K) A
  obtain ⟨g, hgf, hgi, hgs⟩ := quotientEmbeds_after_baseChange hf hle
  let I := RingHom.ker f
  let : I.IsHopfIdeal k := least_polynomial_kernel_isHopfIdeal hf hle hgf hgs
  let B := hopfQuotient A I
  have : Algebra.FiniteType k B := inferInstanceAs (Algebra.FiniteType k (A ⧸ I))
  have hs : Smooth (specGroup B).X.hom :=
    smooth_specGroup_of_baseChange_polynomial_embedding B (extendCoefficients (K := K) g) hgs
  have : IsDomain (A ⧸ I) := Function.Injective.isDomain g hgi
  have hc : ConnectedSpace (specGroup B).X.left :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum (A ⧸ I)))
  refine ⟨I, inferInstance, hs, hc, fun β w hw a ha => ?_⟩
  have h : (1 : K) ⊗ₜ[k] a ∈ RingHom.ker (extendCoefficients (K := K) f) := by
    change extendCoefficients (K := K) f (1 ⊗ₜ[k] a) = 0
    rw [extendCoefficients_tmul, one_smul]
    exact ha
  have e : extendCoefficients (K := K) w (1 ⊗ₜ[k] a) = 0 := hle β w hw h
  change w a = 0
  simpa only [extendCoefficients_tmul, one_smul] using e

end PolynomialImages

private def counitPointHom (A : HopfAlgebraCategory k) (R : TestAlgebra k) :
    CommAlgCat.of k A ⟶ R :=
  CommAlgCat.ofHom ((Algebra.ofId k R).comp (Bialgebra.counitAlgHom k A))

private theorem affinePointEquiv_counit {A : HopfAlgebraCategory k} {G : GroupScheme k}
    (e : specGroup A ≅ G) (R : TestAlgebra k) :
    affinePointEquiv ((Grp.forget (SchemeOver k)).mapIso e) R (counitPointHom A R) =
      (1 : Points G.X R) := by
  obtain ⟨H, hH, _⟩ := hopfSpecPoints k
  let z : (convolutionPoints A).obj R := 1
  have eq : affinePointEquiv ((Grp.forget (SchemeOver k)).mapIso e) R (counitPointHom A R) =
      onPoints e.hom R ((H A).hom.app R z) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (counitPointHom A R).hom.toRingHom) ≫ e.hom.hom.hom.left =
      ((H A).hom.app R z : Points (specGroup A).X R).left ≫ e.hom.hom.hom.left
    rw [hH]
    rfl
  rw [eq]
  exact (congrArg (onPoints e.hom R) (((H A).hom.app R).hom.map_one)).trans
    (onPoints e.hom R).map_one

private theorem curveCoordinates_origin {A : HopfAlgebraCategory k} {G : GroupScheme k}
    (e : specGroup A ≅ G) (x : AffineLineCurve ((groupBaseChange k K).obj G))
    (hx : curveAtZero x = 1) :
    let ex : (specGroup A).X ≅ G.X := (Grp.forget (SchemeOver k)).mapIso e
    ((Polynomial.aeval (0 : K)).restrictScalars k).comp (curveCoordinates K ex x) =
      (Algebra.ofId k K).comp (Bialgebra.counitAlgHom k A) := by
  let ex : (specGroup A).X ≅ G.X := (Grp.forget (SchemeOver k)).mapIso e
  let R := CommAlgCat.of K (Polynomial K)
  let R₀ := CommAlgCat.of K K
  let r := (restrictTestAlgebra k K).obj R
  let r₀ := (restrictTestAlgebra k K).obj R₀
  let f := curveCoordinates K ex x
  let c : TestAlgebra k := CommAlgCat.of k A
  let a : R ⟶ R₀ := CommAlgCat.ofHom (Polynomial.aeval (0 : K))
  let b := (restrictTestAlgebra k K).map a
  let C := standardPolynomialHomEquiv (A := c) K
  let E := affinePointEquiv ex r
  let fR := C.symm f
  have hfx : affinePointEquiv ex r fR = baseChangePoint k K G.X R x := by
    change E (C.symm (C (E.symm (baseChangePoint k K G.X R x)))) = _
    rw [C.symm_apply_apply, E.apply_symm_apply]
  have hz : affinePointEquiv ex r₀ (fR ≫ b) = (1 : Points G.X r₀) := by
    rw [affinePointEquiv_natural, hfx, ← baseChangePointsNaturality]
    change baseChangePoint k K G.X R₀ (curveAtZero x) = 1
    rw [hx]
    exact (baseChangePointGroupEquiv K G R₀).map_one
  have h := (affinePointEquiv ex r₀).injective (hz.trans (affinePointEquiv_counit e r₀).symm)
  let D : (c ⟶ r₀) ≃ (c →ₐ[k] K) :=
    coordinateAlgHomEquiv (RingEquiv.refl K) fun _ => rfl
  apply AlgHom.ext
  intro t
  exact AlgHom.congr_fun (congrArg D h) t

private theorem exists_smooth_subgroup_with_curve [FiniteDimensional k K] [IsGalois k K]
    (V : AffineAlgebraicGroup k) (x : AffineLineCurve ((groupBaseChange k K).obj V.val))
    (hx₀ : curveAtZero x = 1) (hx : IsNonconstantCurve x) :
    ∃ H : ClosedSubgroup V.val, Smooth H.group.X.hom ∧ ConnectedSpace H.group.X.left ∧
      ∃ y : AffineLineCurve ((groupBaseChange k K).obj H.group),
        curveAtZero y = 1 ∧ IsNonconstantCurve y := by
  obtain ⟨A₀, ⟨e⟩⟩ := essImage_hopfSpec.mpr V.property.1
  let A := A₀.unop
  let ex := (Grp.forget (SchemeOver k)).mapIso e
  have : Algebra.FiniteType k A := finiteType_of_affine_coordinates ex V.property.2.1
  obtain ⟨I, hI, hs, hc, hvan⟩ := exists_smooth_hopfQuotient K A
  let : I.IsHopfIdeal k := hI
  let B := hopfQuotient A I
  let f := curveCoordinates K ex x
  let P : Polynomial K ≃ₐ[K] MvPolynomial PUnit K := (MvPolynomial.uniqueAlgEquiv K PUnit).symm
  let g := (P.toAlgHom.restrictScalars k).comp f
  have hp : (polynomialOrigin PUnit).comp P.toAlgHom = Polynomial.aeval (0 : K) := by
    apply Polynomial.algHom_ext
    have hX : P Polynomial.X = MvPolynomial.X PUnit.unit := by
      change Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (default : PUnit)) Polynomial.X = _
      rw [Polynomial.eval₂_X]
    simp [hX, polynomialOrigin]
  have hg : IsPointedFamily g := by
    unfold IsPointedFamily
    change ((polynomialOrigin PUnit).restrictScalars k).comp
      ((P.toAlgHom.restrictScalars k).comp f) = _
    rw [← AlgHom.comp_assoc]
    have hq := congrArg (AlgHom.restrictScalars k) hp
    change ((polynomialOrigin PUnit).restrictScalars k).comp (P.toAlgHom.restrictScalars k) =
      ((Polynomial.aeval (0 : K)).restrictScalars k) at hq
    rw [hq]
    exact curveCoordinates_origin e x hx₀
  let v : B →ₐ[k] Polynomial K := Ideal.Quotient.liftₐ I f fun a ha =>
    (injective_iff_map_eq_zero P.toAlgHom).mp P.injective _ (hvan PUnit g hg ha)
  let eB : (testSpec k).obj (op (CommAlgCat.of k B)) ≅ (specGroup B).X := Iso.refl _
  let z : AffineLineCurve ((groupBaseChange k K).obj (specGroup B)) :=
    (curveCoordinates K eB).symm v
  have hz : IsNonconstantCurve z := by
    obtain ⟨a, n, hn, hnc⟩ := (curveCoordinates_isNonconstant K ex x).mp hx
    apply (curveCoordinates_isNonconstant K eB z).mpr
    refine ⟨Ideal.Quotient.mk I a, n, hn, ?_⟩
    rw [show curveCoordinates K eB z = v from Equiv.apply_symm_apply _ _]
    exact hnc
  have hclosed : IsClosedImmersion (specGroupMap (hopfQuotientMap A I)).hom.hom.left :=
    (hopfMapClosedImmersion k (hopfQuotientMap A I)).mpr Ideal.Quotient.mk_surjective
  let j := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e
  have : IsClosedImmersion e.hom.hom.hom.left := inferInstanceAs (IsClosedImmersion j.hom)
  have hi : IsClosedImmersion (specGroupMap (hopfQuotientMap A I) ≫ e.hom).hom.hom.left :=
    IsClosedImmersion.comp _ _
  obtain ⟨y, hy, hne⟩ := exists_normalized_curve hz
  exact ⟨⟨specGroup B, specGroupMap (hopfQuotientMap A I) ≫ e.hom, hi⟩,
    hs, hc, y, hy, isNonconstant_of_normalized_ne_one hy hne⟩

/-- A nonconstant affine-line curve after separable extension survives in a smooth
connected central subgroup killed by the characteristic over the original field. -/
theorem centralKilledByPCurves : Specs.Unipotent.CentralKilledByPCurves.{u} := by
  intro k _ p _ _ U hs _ hU L _ _ _ x hx
  obtain ⟨y, hy₀, hy, hyc, hyp⟩ := exists_central_p_curve_over_sepClosure p U hs hU hx
  obtain ⟨Z, W, hZ, hW, hp⟩ := center_power_kernel p U
  obtain ⟨w, hw⟩ := factor_central_p_curve p U Z W hZ hW hy₀ hy hyc hyp
  have : IsAffine U.val.X.left := U.property.1
  have : LocallyOfFiniteType U.val.X.hom := U.property.2.1
  have : IsClosedImmersion Z.inclusion.hom.hom.left := Z.isClosedImmersion
  have : IsClosedImmersion W.inclusion.hom.hom.left := W.isClosedImmersion
  have hZW : IsClosedImmersion (W.inclusion ≫ Z.inclusion).hom.hom.left :=
    IsClosedImmersion.comp _ _
  have hiW : IsAffine W.group.X.left :=
    isAffine_of_isAffineHom (W.inclusion ≫ Z.inclusion).hom.hom.left
  have htW : LocallyOfFiniteType W.group.X.hom := by
    rw [← Over.w (W.inclusion ≫ Z.inclusion).hom.hom]
    infer_instance
  let V : AffineAlgebraicGroup k := ⟨W.group, hiW, htW, inferInstance⟩
  obtain ⟨K, hK, hGal, z, hz₀, hz⟩ := exists_normalized_curve_over_finiteGalois V w hw
  let : FiniteDimensional k K := hK
  let : IsGalois k K := hGal
  obtain ⟨H, hHs, hHc, v, hv₀, hv⟩ := exists_smooth_subgroup_with_curve V z hz₀ hz
  have : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  let i := H.inclusion ≫ (W.inclusion ≫ Z.inclusion)
  have hi : IsClosedImmersion i.hom.hom.left := IsClosedImmersion.comp _ _
  refine ⟨⟨H.group, i, hi⟩, hHs, hHc, ?_, ?_, K, inferInstance, inferInstance,
    hK, hGal, v, hv₀, hv⟩
  · exact (hZ _ _).mpr ⟨H.inclusion.hom.hom ≫ W.inclusion.hom.hom, Category.assoc ..⟩
  · intro R a
    let j := onPoints H.inclusion R
    apply onPoints_injective H.inclusion H.isClosedImmersion R
    change j (a ^ p) = j 1
    rw [map_pow, map_one]
    exact hp R (j a)

end

end LinearAlgebraicGroups.Unipotent
