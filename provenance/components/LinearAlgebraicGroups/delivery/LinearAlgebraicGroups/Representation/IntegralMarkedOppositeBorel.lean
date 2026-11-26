import Specs.LinearAlgebraicGroups.Representation.IntegralMarkedOppositeBorel
import LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import LinearAlgebraicGroups.Classification.RationalRealization
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial TensorProduct

universe u v

namespace LinearAlgebraicGroups.Representation.IntegralMarkedOppositeBorel

noncomputable section

section LaurentOrbit

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- Equations on an affine scheme for a Laurent orbit to extend to the affine line. -/
def limitIdeal (orbit : A →ₐ[R] LaurentPolynomial A) : Ideal A :=
  Ideal.span {c | ∃ a n, n < 0 ∧ c = (orbit a).coeff n}

private theorem hasPolynomial_iff {b : LaurentPolynomial B} :
    (∃ q : Polynomial B, q.toLaurent = b) ↔ ∀ n < 0, b.coeff n = 0 := by
  have h : (∃ q : Polynomial B, q.toLaurent = b) ↔
      b.coeff ∈ Set.range (Finsupp.mapDomain ((↑) : ℕ → ℤ)) := by
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.toFinsupp.coeff, LaurentPolynomial.coeff_toLaurent q |>.symm⟩
    · rintro ⟨q, hq⟩
      refine ⟨Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff q), LaurentPolynomial.ext ?_⟩
      intro n
      exact DFunLike.congr_fun hq n
  have hi : Function.Injective ((↑) : ℕ → ℤ) := Nat.cast_injective
  refine h.trans ((Finsupp.mem_range_mapDomain_iff ((↑) : ℕ → ℤ) hi b.coeff).trans ?_)
  have hr (n : ℤ) : n ∉ Set.range ((↑) : ℕ → ℤ) ↔ n < 0 := by
    constructor
    · intro h
      by_contra! hn
      exact h ⟨n.toNat, Int.toNat_of_nonneg hn⟩
    · rintro hn ⟨k, rfl⟩
      exact (not_lt_of_ge (Int.natCast_nonneg k)) hn
  simp only [hr]

/-- The equations detect polynomial extensions on all affine test algebras. -/
theorem limitIdeal_le_ker_iff (orbit : A →ₐ[R] LaurentPolynomial A) (g : A →ₐ[R] B) :
    limitIdeal orbit ≤ RingHom.ker g.toRingHom ↔
      ∃ p : A →ₐ[R] Polynomial B,
        (Polynomial.toLaurentAlg.restrictScalars R).comp p =
          (AddMonoidAlgebra.mapAlgHom ℤ g).comp orbit := by
  let f := (AddMonoidAlgebra.mapAlgHom ℤ g).comp orbit
  let j : Polynomial B →ₐ[R] LaurentPolynomial B :=
    Polynomial.toLaurentAlg.restrictScalars R
  have hc (a : A) (n : ℤ) : (f a).coeff n = g ((orbit a).coeff n) :=
    AddMonoidAlgebra.coeff_mapAlgHom g (orbit a) n
  change limitIdeal orbit ≤ RingHom.ker g.toRingHom ↔ ∃ p, j.comp p = f
  rw [limitIdeal, Ideal.span_le]
  constructor
  · intro h
    let e := AlgEquiv.ofInjective j Polynomial.toLaurent_injective
    let fr := f.codRestrict j.range fun a ↦ by
      apply (AlgHom.mem_range j).mpr
      apply hasPolynomial_iff.mpr
      intro n hn
      rw [hc]
      exact h ⟨a, n, hn, rfl⟩
    refine ⟨e.symm.toAlgHom.comp fr, ?_⟩
    ext a : 1
    exact congrArg Subtype.val (e.apply_symm_apply (fr a))
  · rintro ⟨p, hp⟩ c ⟨a, n, hn, rfl⟩
    change g ((orbit a).coeff n) = 0
    rw [← hc, ← hp]
    exact hasPolynomial_iff.mp ⟨p a, rfl⟩ n hn

/-- The polynomial extension is unique, including over nonreduced test rings. -/
theorem polynomialExtension_unique {p q : A →ₐ[R] Polynomial B}
    (h : (Polynomial.toLaurentAlg.restrictScalars R).comp p =
      (Polynomial.toLaurentAlg.restrictScalars R).comp q) : p = q := by
  ext a : 1
  apply Polynomial.toLaurent_injective
  exact DFunLike.congr_fun h a

/-- The universal polynomial orbit over the closed limit locus. -/
def limitPolynomial (orbit : A →ₐ[R] LaurentPolynomial A) :
    A →ₐ[R] Polynomial (A ⧸ limitIdeal orbit) :=
  ((limitIdeal_le_ker_iff orbit (Ideal.Quotient.mkₐ R (limitIdeal orbit))).mp
    (by rw [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker])).choose

theorem toLaurent_limitPolynomial (orbit : A →ₐ[R] LaurentPolynomial A) :
    (Polynomial.toLaurentAlg.restrictScalars R).comp (limitPolynomial orbit) =
      (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R (limitIdeal orbit))).comp orbit :=
  ((limitIdeal_le_ker_iff orbit (Ideal.Quotient.mkₐ R (limitIdeal orbit))).mp
    (by rw [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker])).choose_spec

section ScalarExtension

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Extend an affine Laurent orbit by extending its coefficients and fixing its parameter. -/
def extendLaurentOrbit (orbit : A →ₐ[R] LaurentPolynomial A) :
    S ⊗[R] A →ₐ[S] LaurentPolynomial (S ⊗[R] A) :=
  AlgHom.liftEquiv R S A _ ((AddMonoidAlgebra.mapAlgHom ℤ
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)).comp orbit)

private theorem coeff_extendLaurentOrbit_tmul (orbit : A →ₐ[R] LaurentPolynomial A)
    (s : S) (a : A) (n : ℤ) :
    (extendLaurentOrbit S orbit (s ⊗ₜ[R] a)).coeff n = s ⊗ₜ[R] (orbit a).coeff n := by
  simp only [extendLaurentOrbit, AlgHom.liftEquiv_tmul, AlgHom.comp_apply,
    AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_mapAlgHom]
  change s • ((1 : S) ⊗ₜ[R] (orbit a).coeff n) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Formation of the coefficient equations commutes with arbitrary base change.
In particular, this applies to residue fields, where the base map need not be flat. -/
theorem limitIdeal_extendLaurentOrbit (orbit : A →ₐ[R] LaurentPolynomial A) :
    limitIdeal (extendLaurentOrbit S orbit) =
      (limitIdeal orbit).map (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom := by
  let i : A →ₐ[R] S ⊗[R] A := Algebra.TensorProduct.includeRight
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro c ⟨x, n, hn, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      rw [coeff_extendLaurentOrbit_tmul]
      change s ⊗ₜ[R] (orbit a).coeff n ∈ (limitIdeal orbit).map i.toRingHom
      rw [show s ⊗ₜ[R] (orbit a).coeff n =
        (s ⊗ₜ[R] (1 : A)) * i ((orbit a).coeff n) by
          simp [i, Algebra.TensorProduct.tmul_mul_tmul]]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, n, hn, rfl⟩))
    | add x y hx hy =>
      rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      exact Ideal.add_mem _ hx hy
  · change (limitIdeal orbit).map i.toRingHom ≤ _
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro c ⟨a, n, hn, rfl⟩
    change (1 : S) ⊗ₜ[R] (orbit a).coeff n ∈ limitIdeal (extendLaurentOrbit S orbit)
    rw [← coeff_extendLaurentOrbit_tmul S orbit 1 a n]
    exact Ideal.subset_span ⟨1 ⊗ₜ[R] a, n, hn, rfl⟩

end ScalarExtension

end LaurentOrbit

section AffinePoints

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

private abbrev affinePoint (g : A →ₐ[R] B) :=
  (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op

private theorem affinePoint_comp (g : A →ₐ[R] B) (f : C →ₐ[R] A) :
    affinePoint (g.comp f) = affinePoint g ≫ affinePoint f := by
  let F := algSpec (CommRingCat.of R)
  change F.map ((CommAlgCat.ofHom g).op ≫ (CommAlgCat.ofHom f).op) = _
  rw [Functor.map_comp]

private theorem affinePoint_factorsThrough_iff (I : Ideal A) (g : A →ₐ[R] B) :
    (∃ s : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R B)) ⟶
      (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (A ⧸ I))),
      s ≫ affinePoint (Ideal.Quotient.mkₐ R I) = affinePoint g) ↔
    I ≤ RingHom.ker g.toRingHom := by
  let j := Ideal.Quotient.mkₐ R I
  let E := algSpec.fullyFaithful (R := CommRingCat.of R)
  constructor
  · rintro ⟨s, hs⟩
    let g' : A ⧸ I →ₐ[R] B := (E.preimage s).unop.hom
    have w : affinePoint g' = s := E.map_preimage s
    have hs' : affinePoint (g'.comp j) = affinePoint g :=
      (affinePoint_comp g' j).trans ((congrArg (· ≫ affinePoint j) w).trans hs)
    have hg := E.map_injective hs'
    have hg' : g'.comp j = g :=
      congrArg (fun k : op (CommAlgCat.of R B) ⟶ op (CommAlgCat.of R A) => k.unop.hom) hg
    intro x hx
    have hzero : j x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    change g x = 0
    rw [← hg', AlgHom.comp_apply, hzero, map_zero]
  · intro hg
    let g' := Ideal.Quotient.liftₐ I g hg
    exact ⟨affinePoint g', (affinePoint_comp g' j).symm⟩

end AffinePoints

section HopfLimits

open WithConv Coalgebra HopfAlgebra Algebra.TensorProduct

variable {R A B C : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

local instance convolutionGroup : Group (WithConv (A →ₐ[R] B)) where
  toMonoid := inferInstance
  inv f := toConv (f.ofConv.comp (antipodeAlgHom R A))
  inv_mul_cancel f := by
    have h := AlgHom.comp_convMul_distrib f.ofConv
      (toConv (antipodeAlgHom R A)) (toConv (AlgHom.id R A))
    rw [AlgHom.antipode_id_cancel, AlgHom.comp_id] at h
    apply ofConv_injective
    refine h.symm.trans ?_
    exact AlgHom.ext fun x => f.ofConv.commutes (counit x)

/-- Postcomposition of points of an affine group with a map of test algebras. -/
private def mapConvolution (f : B →ₐ[R] C) :
    WithConv (A →ₐ[R] B) →* WithConv (A →ₐ[R] C) where
  toFun g := toConv (f.comp g.ofConv)
  map_one' := ofConv_injective (AlgHom.ext fun a => f.commutes (counit a))
  map_mul' g h := ofConv_injective (AlgHom.comp_convMul_distrib f g h)

/-- The orbit of a point under conjugation by the universal Laurent point. -/
def conjugateLaurentPoint (c : A →ₐ[R] LaurentPolynomial R) :
    WithConv (A →ₐ[R] B) →* WithConv (A →ₐ[R] LaurentPolynomial B) := by
  let t := toConv ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R B)).comp c)
  exact (MulAut.conj t).toMonoidHom.comp
    (mapConvolution (IsScalarTower.toAlgHom R B (LaurentPolynomial B)))

private theorem mapAlgHom_comp_coefficients (f : B →ₐ[R] C) :
    (AddMonoidAlgebra.mapAlgHom ℤ f).comp (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R B)) =
      AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R C) := by
  apply AlgHom.ext
  intro x
  apply LaurentPolynomial.ext
  intro n
  simp only [AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom, Algebra.ofId_apply, f.commutes]

private theorem mapAlgHom_comp_constants (f : B →ₐ[R] C) :
    (AddMonoidAlgebra.mapAlgHom ℤ f).comp (IsScalarTower.toAlgHom R B (LaurentPolynomial B)) =
      (IsScalarTower.toAlgHom R C (LaurentPolynomial C)).comp f := by
  ext b : 1
  change AddMonoidAlgebra.mapAlgHom ℤ f (LaurentPolynomial.C b) = LaurentPolynomial.C (f b)
  simp only [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapAlgHom_single]

private theorem conjugateLaurentPoint_natural (c : A →ₐ[R] LaurentPolynomial R)
    (f : B →ₐ[R] C) (g : WithConv (A →ₐ[R] B)) :
    mapConvolution (AddMonoidAlgebra.mapAlgHom ℤ f) (conjugateLaurentPoint c g) =
      conjugateLaurentPoint c (mapConvolution f g) := by
  let tB := toConv ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R B)).comp c)
  let tC := toConv ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R C)).comp c)
  let jB := IsScalarTower.toAlgHom R B (LaurentPolynomial B)
  let jC := IsScalarTower.toAlgHom R C (LaurentPolynomial C)
  let l := mapConvolution (A := A) (AddMonoidAlgebra.mapAlgHom ℤ f)
  have hT : l tB = tC := by
    apply ofConv_injective
    change (AddMonoidAlgebra.mapAlgHom ℤ f).comp
      ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R B)).comp c) = _
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_coefficients]
  have hG : l (mapConvolution jB g) = mapConvolution jC (mapConvolution f g) := by
    apply ofConv_injective
    change (AddMonoidAlgebra.mapAlgHom ℤ f).comp (jB.comp g.ofConv) =
      jC.comp (f.comp g.ofConv)
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_constants, AlgHom.comp_assoc]
  change l (tB * mapConvolution jB g * tB⁻¹) =
    tC * mapConvolution jC (mapConvolution f g) * tC⁻¹
  simp only [map_mul, map_inv, hT, hG]

/-- The universal Laurent orbit map of the affine group on itself. -/
def conjugationOrbit (c : A →ₐ[R] LaurentPolynomial R) : A →ₐ[R] LaurentPolynomial A :=
  (conjugateLaurentPoint c (toConv (AlgHom.id R A))).ofConv

/-- The limit locus functor is the inverse image of the subgroup of polynomial
points inside the Laurent points under the conjugated inclusion of constant points. -/
private def polynomialLimitSubgroup (c : A →ₐ[R] LaurentPolynomial R) :
    Subgroup (WithConv (A →ₐ[R] B)) :=
  (mapConvolution (A := A) (Polynomial.toLaurentAlg.restrictScalars R)).range.comap
    (conjugateLaurentPoint c)

private theorem mem_polynomialLimitSubgroup_iff (c : A →ₐ[R] LaurentPolynomial R)
    (f : A →ₐ[R] B) :
    toConv f ∈ polynomialLimitSubgroup c ↔
      limitIdeal (conjugationOrbit c) ≤ RingHom.ker f.toRingHom := by
  rw [limitIdeal_le_ker_iff]
  have he := congrArg WithConv.ofConv
    (conjugateLaurentPoint_natural c f (toConv (AlgHom.id R A)))
  change (AddMonoidAlgebra.mapAlgHom ℤ f).comp (conjugationOrbit c) =
    (conjugateLaurentPoint c (toConv (f.comp (AlgHom.id R A)))).ofConv at he
  rw [AlgHom.comp_id] at he
  rw [he]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.ofConv, congrArg WithConv.ofConv hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨toConv g, ofConv_injective hg⟩

/-- The coefficient equations for conjugation cut out a closed subgroup over
an arbitrary commutative base, with no flatness requirement on the test algebra. -/
theorem conjugationLimit_isHopfIdeal (c : A →ₐ[R] LaurentPolynomial R) :
    (limitIdeal (conjugationOrbit c)).IsHopfIdeal R := by
  let I := limitIdeal (conjugationOrbit c)
  let Q := A ⧸ I
  let j := Ideal.Quotient.mkₐ R I
  have hj : toConv j ∈ polynomialLimitSubgroup c :=
    (mem_polynomialLimitSubgroup_iff c j).mpr (by rw [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker])
  have hε : toConv (Bialgebra.counitAlgHom R A) ∈ polynomialLimitSubgroup c := by
    change (1 : WithConv (A →ₐ[R] R)) ∈ polynomialLimitSubgroup c
    exact (polynomialLimitSubgroup c).one_mem
  let j₁ : A →ₐ[R] Q ⊗[R] Q := includeLeft.comp j
  let j₂ : A →ₐ[R] Q ⊗[R] Q := includeRight.comp j
  have hmap {T : Type u} [CommRing T] [Algebra R T] (f : Q →ₐ[R] T) :
      toConv (f.comp j) ∈ polynomialLimitSubgroup c := by
    apply (mem_polynomialLimitSubgroup_iff c (f.comp j)).2
    intro x hx
    change f (j x) = 0
    rw [show j x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  have hm : toConv j₁ * toConv j₂ ∈ polynomialLimitSubgroup c :=
    (polynomialLimitSubgroup c).mul_mem
      (hmap (includeLeft : Q →ₐ[R] Q ⊗[R] Q)) (hmap (includeRight : Q →ₐ[R] Q ⊗[R] Q))
  have hl :
      lift j₁ j₂ (fun _ _ => Commute.all _ _) = Algebra.TensorProduct.map j j := by
    ext x <;> simp [j₁, j₂]
  have : (I.restrictScalars R).IsCoideal := by
    refine ⟨(mem_polynomialLimitSubgroup_iff c _).mp hε, ?_⟩
    intro x hx
    have h := (mem_polynomialLimitSubgroup_iff c _).mp hm hx
    change (toConv j₁ * toConv j₂) x = 0 at h
    rw [AlgHom.convMul_apply, hl] at h
    exact h
  constructor
  intro x hx
  have h := (mem_polynomialLimitSubgroup_iff c _).mp
    ((polynomialLimitSubgroup c).inv_mem hj) hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp h

/-- The value at zero of the universal limit polynomial. -/
def limitAtZero (c : A →ₐ[R] LaurentPolynomial R) :
    A →ₐ[R] A ⧸ limitIdeal (conjugationOrbit c) :=
  (Polynomial.aevalTower (AlgHom.id R _) 0).comp (limitPolynomial (conjugationOrbit c))

private abbrev polynomialToLaurent : Polynomial B →ₐ[R] LaurentPolynomial B :=
  Polynomial.toLaurentAlg.restrictScalars R

private theorem polynomialToLaurent_comp_map (f : B →ₐ[R] C) :
    (AddMonoidAlgebra.mapAlgHom ℤ f).comp polynomialToLaurent =
      polynomialToLaurent.comp (Polynomial.mapAlgHom f) := by
  apply AlgHom.ext
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
  | monomial n b =>
    change AddMonoidAlgebra.mapAlgHom ℤ f (Polynomial.monomial n b).toLaurent =
      ((Polynomial.monomial n b).map f.toRingHom).toLaurent
    rw [Polynomial.map_monomial]
    simp only [← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.toLaurent_C_mul_X_pow, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.mapAlgHom_single]
    rfl

private theorem eval_zero_comp_map (f : B →ₐ[R] C) :
    (Polynomial.aevalTower (AlgHom.id R C) 0).comp (Polynomial.mapAlgHom f) =
      f.comp (Polynomial.aevalTower (AlgHom.id R B) 0) := by
  apply AlgHom.ext
  intro p
  change Polynomial.eval 0 (p.map f.toRingHom) = f (Polynomial.eval 0 p)
  simp

private abbrev polynomialConvolutionMap :=
  mapConvolution (A := A) (polynomialToLaurent (R := R) (B := B))

private def polynomialConvolutionEquiv :
    WithConv (A →ₐ[R] Polynomial B) ≃*
      (polynomialConvolutionMap (R := R) (A := A) (B := B)).range := by
  let j := polynomialConvolutionMap (A := A) (B := B) (R := R)
  exact MulEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => ofConv_injective (polynomialExtension_unique
      (congrArg (fun t : j.range => t.val.ofConv) h)),
      fun y => by
        obtain ⟨z, hz⟩ := y.property
        exact ⟨z, Subtype.ext hz⟩⟩

/-- Polynomial extension of the conjugation orbit on the closed subgroup. -/
private def polynomialOrbitHom (c : A →ₐ[R] LaurentPolynomial R) :
    polynomialLimitSubgroup (B := B) c →* WithConv (A →ₐ[R] Polynomial B) :=
  polynomialConvolutionEquiv.symm.toMonoidHom.comp
    { toFun := fun x => ⟨conjugateLaurentPoint c x.val, x.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }

private theorem polynomialOrbitHom_spec (c : A →ₐ[R] LaurentPolynomial R)
    (g : polynomialLimitSubgroup (B := B) c) :
    polynomialToLaurent.comp (polynomialOrbitHom c g).ofConv =
      (conjugateLaurentPoint c g.val).ofConv := by
  let j := polynomialConvolutionMap (A := A) (B := B) (R := R)
  let y : j.range := ⟨conjugateLaurentPoint c g.val, g.property⟩
  exact congrArg (fun t : j.range => t.val.ofConv)
    ((polynomialConvolutionEquiv (R := R) (A := A) (B := B)).apply_symm_apply y)

private abbrev limitPoint (c : A →ₐ[R] LaurentPolynomial R) :=
  (mapConvolution (A := A) (Polynomial.aevalTower (AlgHom.id R B) 0)).comp
    (polynomialOrbitHom c)

private theorem polynomialOrbitHom_universal (c : A →ₐ[R] LaurentPolynomial R)
    (f : (A ⧸ limitIdeal (conjugationOrbit c)) →ₐ[R] B)
    (h : toConv (f.comp (Ideal.Quotient.mkₐ R (limitIdeal (conjugationOrbit c)))) ∈
      polynomialLimitSubgroup c) :
    (polynomialOrbitHom c ⟨_, h⟩).ofConv =
      (Polynomial.mapAlgHom f).comp (limitPolynomial (conjugationOrbit c)) := by
  let j := Ideal.Quotient.mkₐ R (limitIdeal (conjugationOrbit c))
  apply polynomialExtension_unique
  rw [polynomialOrbitHom_spec, ← AlgHom.comp_assoc, ← polynomialToLaurent_comp_map f,
    AlgHom.comp_assoc, toLaurent_limitPolynomial]
  have p : (AddMonoidAlgebra.mapAlgHom ℤ f).comp (AddMonoidAlgebra.mapAlgHom ℤ j) =
      AddMonoidAlgebra.mapAlgHom ℤ (f.comp j) := by
    apply AlgHom.ext
    intro x
    apply LaurentPolynomial.ext
    intro n
    simp only [AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom]
  rw [← AlgHom.comp_assoc, p]
  exact (congrArg WithConv.ofConv
    (conjugateLaurentPoint_natural c (f.comp j) (toConv (AlgHom.id R A)))).symm

private theorem factor_mem_polynomialLimitSubgroup (c : A →ₐ[R] LaurentPolynomial R)
    (f : (A ⧸ limitIdeal (conjugationOrbit c)) →ₐ[R] B) :
    toConv (f.comp (Ideal.Quotient.mkₐ R (limitIdeal (conjugationOrbit c)))) ∈
      polynomialLimitSubgroup c :=
  (mem_polynomialLimitSubgroup_iff c _).mpr fun x hx => show f (Ideal.Quotient.mk _ x) = 0 by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem limitPoint_universal (c : A →ₐ[R] LaurentPolynomial R)
    (f : (A ⧸ limitIdeal (conjugationOrbit c)) →ₐ[R] B)
    (h : toConv (f.comp (Ideal.Quotient.mkₐ R (limitIdeal (conjugationOrbit c)))) ∈
      polynomialLimitSubgroup c) :
    (limitPoint c ⟨_, h⟩).ofConv = f.comp (limitAtZero c) := by
  change (Polynomial.aevalTower (AlgHom.id R _) 0).comp
      (polynomialOrbitHom c ⟨_, h⟩).ofConv = _
  rw [polynomialOrbitHom_universal c f h, ← AlgHom.comp_assoc, eval_zero_comp_map f,
    AlgHom.comp_assoc]
  rfl

private theorem conv_of_tensorProduct {Q : Type u} [CommRing Q] [Algebra R Q]
    (f : A →ₐ[R] Q) :
    (toConv ((includeLeft : Q →ₐ[R] Q ⊗[R] Q).comp f) *
      toConv ((includeRight : Q →ₐ[R] Q ⊗[R] Q).comp f)).ofConv =
      (Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom R A) := by
  have h : lift ((includeLeft : Q →ₐ[R] Q ⊗[R] Q).comp f)
      ((includeRight : Q →ₐ[R] Q ⊗[R] Q).comp f) (fun _ _ => Commute.all _ _) =
      Algebra.TensorProduct.map f f := by
    ext x <;> simp
  apply AlgHom.ext
  intro x
  exact (AlgHom.convMul_apply _ _ x).trans (congrArg (fun g : A ⊗[R] A →ₐ[R] Q ⊗[R] Q =>
    g (comul x)) h)

/-- Evaluating the universal polynomial at zero gives a homomorphism from
the limit subgroup to the original group. -/
def limitAtZeroBialgHom (c : A →ₐ[R] LaurentPolynomial R) :
    letI := conjugationLimit_isHopfIdeal c
    A →ₐc[R] A ⧸ limitIdeal (conjugationOrbit c) := by
  let I := limitIdeal (conjugationOrbit c)
  let Q := A ⧸ I
  letI : I.IsHopfIdeal R := conjugationLimit_isHopfIdeal c
  let j := Ideal.Quotient.mkₐ R I
  refine BialgHom.ofAlgHom (limitAtZero c) ?_ ?_
  · let f := Bialgebra.counitAlgHom R Q
    let g : polynomialLimitSubgroup (B := R) c := ⟨toConv (f.comp j),
      factor_mem_polynomialLimitSubgroup c f⟩
    have h : g = 1 := by
      apply Subtype.ext
      change toConv (f.comp j) = (1 : WithConv (A →ₐ[R] R))
      rw [AlgHom.convOne_def]
      rfl
    have w := limitPoint_universal c f g.property
    change (limitPoint c g).ofConv = _ at w
    rw [h, map_one] at w
    exact w.symm
  · let A₁ : Q →ₐ[R] Q ⊗[R] Q := includeLeft
    let A₂ : Q →ₐ[R] Q ⊗[R] Q := includeRight
    let f := Bialgebra.comulAlgHom R Q
    let g : polynomialLimitSubgroup (B := Q ⊗[R] Q) c :=
      ⟨toConv (f.comp j), factor_mem_polynomialLimitSubgroup c f⟩
    let g₁ : polynomialLimitSubgroup (B := Q ⊗[R] Q) c :=
      ⟨toConv (A₁.comp j), factor_mem_polynomialLimitSubgroup c A₁⟩
    let g₂ : polynomialLimitSubgroup (B := Q ⊗[R] Q) c :=
      ⟨toConv (A₂.comp j), factor_mem_polynomialLimitSubgroup c A₂⟩
    have hg : g₁ * g₂ = g := by
      apply Subtype.ext
      apply ofConv_injective
      change (toConv (A₁.comp j) * toConv (A₂.comp j)).ofConv = f.comp j
      exact conv_of_tensorProduct j
    have h₁ := limitPoint_universal c A₁ g₁.property
    have h₂ := limitPoint_universal c A₂ g₂.property
    have h := limitPoint_universal c f g.property
    change (limitPoint c g₁).ofConv = _ at h₁
    change (limitPoint c g₂).ofConv = _ at h₂
    change (limitPoint c g).ofConv = _ at h
    rw [← hg, map_mul] at h
    have h₁' : limitPoint c g₁ = toConv (A₁.comp (limitAtZero c)) := ofConv_injective h₁
    have h₂' : limitPoint c g₂ = toConv (A₂.comp (limitAtZero c)) := ofConv_injective h₂
    rw [h₁', h₂', conv_of_tensorProduct] at h
    exact h

/-- The closed group scheme represented by the conjugation limit locus. -/
def conjugationLimit (c : A →ₐ[R] LaurentPolynomial R) :
    Grp (Over (Spec (CommRingCat.of R))) :=
  letI := conjugationLimit_isHopfIdeal c
  (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R (A ⧸ limitIdeal (conjugationOrbit c))))

/-- Its inclusion into the original affine group scheme. -/
def conjugationLimitInclusion (c : A →ₐ[R] LaurentPolynomial R) :
    conjugationLimit c ⟶ (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R A)) :=
  letI := conjugationLimit_isHopfIdeal c
  (hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom
    (Bialgebra.Quotient.mkBialgHom (R := R) (limitIdeal (conjugationOrbit c)))).op

theorem conjugationLimitInclusion_isClosedImmersion (c : A →ₐ[R] LaurentPolynomial R) :
    IsClosedImmersion (conjugationLimitInclusion c).hom.hom.left := by
  change IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (limitIdeal (conjugationOrbit c)))))
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The limit at zero, viewed as a homomorphism of group schemes. -/
def conjugationLimitEvaluation (c : A →ₐ[R] LaurentPolynomial R) :
    conjugationLimit c ⟶ (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R A)) :=
  letI := conjugationLimit_isHopfIdeal c
  (hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom (limitAtZeroBialgHom c)).op

/-- The affine scheme cut out by the limit ideal represents polynomial
extensions of the orbit on all test algebras over the base. -/
theorem conjugationLimit_point_iff (c : A →ₐ[R] LaurentPolynomial R) (g : A →ₐ[R] B) :
    (∃ s : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R B)) ⟶
      (conjugationLimit c).X, s ≫ (conjugationLimitInclusion c).hom.hom = affinePoint g) ↔
    ∃ p : A →ₐ[R] Polynomial B,
      polynomialToLaurent.comp p = (conjugateLaurentPoint c (toConv g)).ofConv := by
  have h : (AddMonoidAlgebra.mapAlgHom ℤ g).comp (conjugationOrbit c) =
      (conjugateLaurentPoint c (toConv g)).ofConv := by
    have h' := congrArg WithConv.ofConv (conjugateLaurentPoint_natural c g (toConv (AlgHom.id R A)))
    change (AddMonoidAlgebra.mapAlgHom ℤ g).comp (conjugationOrbit c) =
      (conjugateLaurentPoint c (toConv (g.comp (AlgHom.id R A)))).ofConv at h'
    rwa [AlgHom.comp_id] at h'
  rw [← h, ← limitIdeal_le_ker_iff]
  exact affinePoint_factorsThrough_iff _ _

end HopfLimits
/-- A constructible subset of an integral affine base missing its generic point
is contained in the zero locus of a single nonzero element. -/
theorem exists_nonzero_zeroLocus_of_constructible {R : Type u} [CommRing R] [IsDomain R]
    {Z : Set (PrimeSpectrum R)} (hZ : IsConstructible Z) (hη : (⊥ : PrimeSpectrum R) ∉ Z) :
    ∃ a : R, a ≠ 0 ∧ Z ⊆ PrimeSpectrum.zeroLocus {a} := by
  classical
  obtain ⟨C, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hZ
  have hEach (c : C) :
      ∃ a : R, a ≠ 0 ∧ c.val.toSet ⊆ PrimeSpectrum.zeroLocus {a} := by
    by_cases hf : c.val.f = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [PrimeSpectrum.BasicConstructibleSetData.toSet, hf]
      simp
    · have h : ¬ ∀ j, c.val.g j = 0 := by
        intro h
        apply hη
        rw [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion₂]
        refine ⟨c.val, c.property, ?_⟩
        change (⊥ : PrimeSpectrum R) ∈
          PrimeSpectrum.zeroLocus (Set.range c.val.g) \ PrimeSpectrum.zeroLocus {c.val.f}
        simp [PrimeSpectrum.mem_zeroLocus, h, hf]
      obtain ⟨j, hj⟩ := not_forall.mp h
      refine ⟨c.val.g j, hj, ?_⟩
      intro x hx
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact hx.1 (Set.mem_range_self j)
  choose a hne ha using hEach
  refine ⟨∏ c : C, a c, Finset.prod_ne_zero_iff.mpr fun c _ ↦ hne c, ?_⟩
  intro x hx
  rw [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion₂] at hx
  obtain ⟨c, hc, hx⟩ := hx
  have hh := ha ⟨c, hc⟩ hx
  rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hh ⊢
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (Finset.mem_univ ⟨c, hc⟩)) hh

/-- A constructible bad locus on a finitely presented scheme can be removed from the base
by a single principal localization if it misses the generic fibre. -/
theorem exists_principal_open_avoiding {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    {Z : Set X} (hZ : IsConstructible Z) (hη : ∀ x ∈ Z, f x ≠ (⊥ : PrimeSpectrum R)) :
    ∃ a : R, a ≠ 0 ∧
      Disjoint Z (Set.range (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a)))))) := by
  obtain ⟨a, ha, h⟩ := exists_nonzero_zeroLocus_of_constructible
    (f.isConstructible_image hZ) (by
      rintro ⟨x, hx, he⟩
      exact hη x hx he)
  refine ⟨a, ha, Set.disjoint_left.mpr fun x hx hxf ↦ ?_⟩
  rw [IsOpenImmersion.range_pullbackFst] at hxf
  have hax : a ∈ (f x).asIdeal := by
    have he : (f x : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus {a} :=
      h (Set.mem_image_of_mem f hx)
    exact ((PrimeSpectrum.mem_zeroLocus (f x : PrimeSpectrum R) {a}).mp he) (Set.mem_singleton a)
  change f x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away a))) at hxf
  rw [PrimeSpectrum.localization_away_comap_range _ a] at hxf
  exact (PrimeSpectrum.mem_basicOpen a (f x : PrimeSpectrum R)).mp hxf hax



section ScalarChange

open Specs.IntegralMarkedOppositeBorel (BaseRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection)
open Specs.OrderedCechComparison (SchemeOverRing)

variable {A B : Type u} [CommRing A] [CommRing B]

private def pullbackCompOfEq {X Y Z : Scheme.{u}} {h : X ⟶ Z}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hh : h = f ≫ g) :
    Over.pullback h ≅ Over.pullback g ⋙ Over.pullback f := by
  subst h
  exact Over.pullbackComp f g

/-- Pullback of schemes along successive scalar maps agrees with pullback
along their composite. -/
def changeBaseComp {C : Type u} [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    changeBase (ψ.comp φ) ≅ changeBase φ ⋙ changeBase ψ :=
  pullbackCompOfEq (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom φ))
    (by rw [CommRingCat.ofHom_comp, Spec.map_comp])

/-- The scalar composition comparison preserves the group scheme laws. -/
def changeBaseGrpComp {C : Type u} [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    (changeBase (ψ.comp φ)).mapGrp ≅ (changeBase φ).mapGrp ⋙ (changeBase ψ).mapGrp :=
  Functor.mapGrpNatIso (changeBaseComp φ ψ) ≪≫ Functor.mapGrpCompIso

/-- Changing the base of a morphism in the slice gives the same
cartesian square as pulling back over its target. -/
theorem changeBaseMap_isPullback (φ : A →+* B) {X Y : SchemeOverRing A} (q : X ⟶ Y) :
    IsPullback ((changeBase φ).map q).left (fibreProjection φ X)
      (fibreProjection φ Y) q.left := by
  let b := Spec.map (CommRingCat.ofHom φ)
  have h : IsPullback (fibreProjection φ X) (pullback.snd X.hom b) (q.left ≫ Y.hom) b := by
    rw [Over.w q]
    exact IsPullback.of_hasPullback _ _
  have hf : ((changeBase φ).map q).left ≫ fibreProjection φ Y =
      fibreProjection φ X ≫ q.left := pullback.lift_fst _ _ _
  have hs : ((changeBase φ).map q).left ≫ pullback.snd Y.hom b =
      pullback.snd X.hom b := pullback.lift_snd _ _ _
  exact (IsPullback.of_bot (hs.symm ▸ h) hf.symm (IsPullback.of_hasPullback Y.hom b)).flip
private theorem flat_fibreProjection (M : Submonoid A) [Algebra A B] [IsLocalization M B]
    (X : SchemeOverRing A) : Flat (fibreProjection (algebraMap A B) X) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B M))
  change Flat (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap A B))))
  infer_instance

private theorem isIso_stalkMap_of_flat_of_surjectiveOnStalks {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [SurjectiveOnStalks f] (x : X) : IsIso (f.stalkMap x) := by
  have hr := Flat.stalkMap f x
  have hf : (f.stalkMap x).hom.FaithfullyFlat := by
    algebraize [(f.stalkMap x).hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := f.prop x
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hf.injective, f.stalkMap_surjective x⟩

private theorem isIso_stalkMap_fibreProjection (M : Submonoid A) [Algebra A B]
    [IsLocalization M B] (X : SchemeOverRing A) (x : ((changeBase (algebraMap A B)).obj X).left) :
    IsIso ((fibreProjection (algebraMap A B) X).stalkMap x) := by
  have := IsPreimmersion.of_isLocalization M (S := B)
  have : IsPreimmersion (fibreProjection (algebraMap A B) X) :=
    inferInstanceAs (IsPreimmersion (pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))))
  have := flat_fibreProjection (B := B) M X
  exact isIso_stalkMap_of_flat_of_surjectiveOnStalks _ x

private def stalkMapIso_of_square {X' Y' X Y : Scheme.{u}}
    {a : X' ⟶ X} {r : X' ⟶ Y'} {q : X ⟶ Y} {b : Y' ⟶ Y}
    (h : a ≫ q = r ≫ b) (x : X') [IsIso (a.stalkMap x)] [IsIso (b.stalkMap (r x))] :
    Arrow.mk (q.stalkMap (a x)) ≅ Arrow.mk (r.stalkMap x) :=
  Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by
      rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]) ≪≫ asIso (b.stalkMap (r x)))
    (asIso (a.stalkMap x))
    (by
      simp only [Iso.trans_hom, asIso_hom, Category.assoc, ← Scheme.Hom.stalkMap_comp]
      exact (Scheme.Hom.stalkMap_congr_hom _ _ h x).symm)

private theorem formallySmooth_iff_of_localization (M : Submonoid A) [Algebra A B]
    [IsLocalization M B] {X Y : SchemeOverRing A} (q : X ⟶ Y)
    (x : ((changeBase (algebraMap A B)).obj X).left) :
    (q.left.stalkMap (fibreProjection (algebraMap A B) X x)).hom.FormallySmooth ↔
      (((changeBase (algebraMap A B)).map q).left.stalkMap x).hom.FormallySmooth := by
  let φ := algebraMap A B
  letI := isIso_stalkMap_fibreProjection M X x
  letI := isIso_stalkMap_fibreProjection M Y (((changeBase φ).map q).left x)
  let e := stalkMapIso_of_square (changeBaseMap_isPullback φ q).w.symm x
  exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff e

variable (A) [IsDomain A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]

private theorem genericPoint_mem_range :
    (⊥ : PrimeSpectrum A) ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A K)

/-- Smoothness of a finitely presented morphism on the generic fibre
persists after a principal restriction of its arithmetic base. -/
theorem exists_smooth_principal_restriction {X Y : SchemeOverRing A} (q : X ⟶ Y)
    [LocallyOfFinitePresentation q.left] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact X.hom] [TopologicalSpace.NoetherianSpace X.left]
    (hq : Smooth ((changeBase (algebraMap A K)).map q).left) :
    ∃ a : A, a ≠ 0 ∧
      Smooth ((changeBase (algebraMap A (Localization.Away a))).map q).left := by
  let Z := (q.left.smoothLocus : Set X.left)ᶜ
  have hZ : IsConstructible Z := isConstructible_compl.mpr
    ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible q.left.smoothLocus.2)
  have hη (x : X.left) (hx : x ∈ Z) : X.hom x ≠ (⊥ : PrimeSpectrum A) := by
    intro hxη
    have hm : x ∈ Set.range (fibreProjection (algebraMap A K) X) := by
      change x ∈ Set.range (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hxη]
      exact genericPoint_mem_range A K
    obtain ⟨y, rfl⟩ := hm
    apply hx
    apply (formallySmooth_iff_of_localization (nonZeroDivisors A) q y).mpr
    let := hq
    change y ∈ ((changeBase (algebraMap A K)).map q).left.smoothLocus
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  obtain ⟨a, ha, h⟩ := exists_principal_open_avoiding X.hom hZ hη
  refine ⟨a, ha, ?_⟩
  let φ := algebraMap A (Localization.Away a)
  let r := ((changeBase φ).map q).left
  have : LocallyOfFinitePresentation r :=
    MorphismProperty.of_isPullback (changeBaseMap_isPullback φ q).flip ‹_›
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  apply (formallySmooth_iff_of_localization (Submonoid.powers a) q x).mp
  by_contra hn
  exact Set.disjoint_left.mp h hn ⟨x, rfl⟩


end ScalarChange

section IntegralTorus

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Integers IntegralGroup IntegralAlgebra IntegralPoints
  splitTorus integralSpec torusPoint cocharacter)
open Specs.DiagonalizableGroups (IntegerCharacters)

/-- The multiplicative group over the integral base of the marked group. -/
abbrev integralMultiplicativeGroup : IntegralGroup.{u} :=
  (hopfSpec (CommRingCat.of Integers.{u})).obj
    (op (CommHopfAlgCat.of Integers.{u} (MonoidAlgebra Integers.{u} IntegerCharacters.{u})))

private def integralCocharacterExponents (D : BasedRootDatum.{u}) (y : D.Y) :
    Multiplicative D.X →* IntegerCharacters.{u} where
  toFun x := ⟨Multiplicative.ofAdd (D.datum.toLinearMap x.toAdd y)⟩
  map_one' := by
    change ULift.up (Multiplicative.ofAdd (D.datum.toLinearMap 0 y)) = _
    simp
    rfl
  map_mul' x z := by
    change ULift.up (Multiplicative.ofAdd (D.datum.toLinearMap (x.toAdd + z.toAdd) y)) =
      ULift.up (Multiplicative.ofAdd
        (D.datum.toLinearMap x.toAdd y + D.datum.toLinearMap z.toAdd y))
    simp

/-- The scheme cocharacter associated to an element of the full integral
cocharacter lattice. -/
def integralCocharacter (D : BasedRootDatum.{u}) (y : D.Y) :
    integralMultiplicativeGroup ⟶ splitTorus D :=
  (hopfSpec (CommRingCat.of Integers.{u})).map (CommHopfAlgCat.ofHom
    (MonoidAlgebra.mapDomainBialgHom Integers.{u} (integralCocharacterExponents D y))).op

private def integralUnitCoordinates (R : IntegralAlgebra.{u}) (s : Rˣ) :
    MonoidAlgebra Integers.{u} IntegerCharacters.{u} →ₐ[Integers.{u}] R :=
  MonoidAlgebra.lift Integers.{u} R IntegerCharacters <|
    (Units.coeHom R).comp ((zpowersHom Rˣ s).comp MulEquiv.ulift.toMonoidHom)

/-- Evaluation of the multiplicative group at a unit of any integral test algebra. -/
def integralUnitPoint (R : IntegralAlgebra.{u}) (s : Rˣ) :
    IntegralPoints integralMultiplicativeGroup R :=
  integralSpec.map (CommAlgCat.ofHom (integralUnitCoordinates R s)).op

theorem integralCocharacter_points (D : BasedRootDatum.{u}) (y : D.Y)
    (R : IntegralAlgebra.{u}) (s : Rˣ) :
    integralUnitPoint R s ≫ (integralCocharacter D y).hom.hom =
      torusPoint D R (cocharacter D y R s) := by
  let g := MonoidAlgebra.mapDomainBialgHom Integers.{u} (integralCocharacterExponents D y)
  let p := integralUnitCoordinates R s
  let a := MonoidAlgebra.lift Integers.{u} R (Multiplicative D.X)
    ((Units.coeHom R).comp (cocharacter D y R s))
  have h : p.comp g.toAlgHom = a := by
    apply MonoidAlgebra.algHom_ext
    · intro x
      rw [AlgHom.comp_apply]
      change integralUnitCoordinates R s (g (MonoidAlgebra.single x 1)) =
        MonoidAlgebra.lift Integers.{u} R _ _ (MonoidAlgebra.single x 1)
      rw [show g (MonoidAlgebra.single x 1) =
        MonoidAlgebra.single (integralCocharacterExponents D y x) 1 from
        MonoidAlgebra.mapDomainBialgHom_single .., integralUnitCoordinates,
        MonoidAlgebra.lift_single, MonoidAlgebra.lift_single]
      simp only [MonoidHom.comp_apply, one_smul]
      rfl
    · exact Subsingleton.elim _ _
  change integralSpec.map (CommAlgCat.ofHom p).op ≫
    integralSpec.map (CommAlgCat.ofHom g.toAlgHom).op = integralSpec.map (CommAlgCat.ofHom a).op
  rw [← Functor.map_comp, ← op_comp]
  exact congrArg (fun b => integralSpec.map (CommAlgCat.ofHom b).op) h

private def integralCharacterExponents (D : BasedRootDatum.{u}) (w : D.X) :
    IntegerCharacters.{u} →* Multiplicative D.X where
  toFun n := Multiplicative.ofAdd (n.down.toAdd • w)
  map_one' := by change Multiplicative.ofAdd ((0 : ℤ) • w) = _; simp
  map_mul' x y := by
    change Multiplicative.ofAdd ((x.down.toAdd + y.down.toAdd) • w) =
      Multiplicative.ofAdd (x.down.toAdd • w + y.down.toAdd • w)
    rw [add_smul]

/-- The character of the split integral torus corresponding to the given weight. -/
def integralCharacter (D : BasedRootDatum.{u}) (w : D.X) :
    splitTorus D ⟶ integralMultiplicativeGroup :=
  (hopfSpec (CommRingCat.of Integers.{u})).map (CommHopfAlgCat.ofHom
    (MonoidAlgebra.mapDomainBialgHom Integers.{u} (integralCharacterExponents D w))).op

end IntegralTorus


section OppositeBorel

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (Realization)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.BorelsAndChambers
open CocharacterDynamics (LimitDecomposition)

variable {k : Type u} [Field k] {D : BasedRootDatum.{u}}
  {L : Specs.RootGroups.AdditiveLine k}

/-- Read a cocharacter of the integral lattice on the marked field torus. -/
def realizedCocharacter (F : Realization D L) (y : D.Y) :
    Cocharacter F.pinned.pair.T.group :=
  Additive.toMul (F.datumIso.val.coweightEquiv.symm y)

set_option backward.isDefEq.respectTransparency false in
theorem realizedCocharacter_pairing (F : Realization D L) (y : D.Y) (i : D.I) :
    pairing F.pinned.pair.T.group (F.datumIso.val.indexEquiv i).val
      (realizedCocharacter F y) = D.datum.root' i y := by
  let : IsCommMonObj F.pinned.pair.T.group.X := F.attached.comm
  rw [← F.attached.datum.pairing_eq, ← F.attached.datum.root_eq]
  change F.attached.toBased.datum.root' (F.datumIso.val.indexEquiv i)
    (F.datumIso.val.coweightEquiv.symm y) = _
  exact F.datumIso.val.root'_coweightEquiv i y

set_option backward.isDefEq.respectTransparency false in
private theorem marking_matches_positiveRoots (hChambers : BorelsThroughT.{u})
    (F : Realization D L) (i : D.I) :
    F.datumIso.val.indexEquiv i ∈ subgroupRoots F.pinned.pair.T F.pinned.pair.B ↔
      D.base.IsPos i := by
  classical
  let P := F.pinned.pair
  let : IsCommMonObj P.T.group.X := F.attached.comm
  let : Finite D.I := D.finiteRoots
  let := D.reduced
  obtain ⟨c, _, _, _, hc⟩ :=
    (hChambers P.G P.reductive P.T P.split P.maximal).1 P.B P.borel P.containsTorus
  let y := F.datumIso.val.coweightEquiv (Additive.ofMul c)
  have hy : realizedCocharacter F y = c := by
    exact congrArg (fun v : F.attached.toBased.Y => Additive.toMul v)
      (F.datumIso.val.coweightEquiv.symm_apply_apply (Additive.ofMul c))
  let l := D.datum.toLinearMap.flip y
  have hmem (a : D.I) :
      F.datumIso.val.indexEquiv a ∈ subgroupRoots P.T P.B ↔ 0 < l (D.datum.root a) := by
    rw [hc]
    change 0 < pairing P.T.group (F.datumIso.val.indexEquiv a).val c ↔ 0 < D.datum.root' a y
    rw [← hy, realizedCocharacter_pairing]
  have hsimple (a : D.I) (ha : a ∈ D.base.support) : 0 < l (D.datum.root a) := by
    apply (hmem a).mp
    have h' : F.datumIso.val.indexEquiv a ∈ F.attached.base.support := by
      exact Eq.mp (congrArg (fun S : Set F.attached.toBased.I =>
        F.datumIso.val.indexEquiv a ∈ S) F.datumIso.property) ⟨a, ha, rfl⟩
    exact ((F.attached.simple_iff _).mp h').1
  have hpos (a : D.I) (ha : D.base.IsPos a) : 0 < l (D.datum.root a) := by
    refine ha.induction_on_add hsimple ?_
    intro b c d hd hb hc
    rw [hd, map_add]
    exact add_pos hb (hsimple c hc)
  rw [hmem]
  refine ⟨?_, hpos i⟩
  intro hi
  by_contra hn
  let j := D.datum.reflectionPerm i i
  have hj := (RootPairing.Base.IsPos.neg_iff_not D.base i).mpr hn
  have hneg := hpos j hj
  have hroot : D.datum.root j = -D.datum.root i := D.datum.root_eq_neg_iff.mpr rfl
  rw [hroot, map_neg, neg_pos] at hneg
  exact (not_lt_of_ge hi.le) hneg

/-- Negating a cocharacter with the signs of the given base produces the
opposite chamber in every marked realization, including an empty root system. -/
theorem realizedCocharacter_negativeChamber (hChambers : BorelsThroughT.{u})
    (F : Realization D L) (y : D.Y) (n : ℤ) (hn : 0 < n)
    (hy : ∀ i : D.I, D.datum.root' i y = n * D.base.height i) :
    IsRegular F.pinned.pair.T (realizedCocharacter F (-y)) ∧
      positiveRoots F.pinned.pair.T (realizedCocharacter F (-y)) =
        (subgroupRoots F.pinned.pair.T F.pinned.pair.B)ᶜ := by
  have h (i : D.I) :
      pairing F.pinned.pair.T.group (F.datumIso.val.indexEquiv i).val
        (realizedCocharacter F (-y)) = -(n * D.base.height i) := by
    rw [realizedCocharacter_pairing, map_neg, hy]
  constructor
  · intro a
    obtain ⟨i, rfl⟩ := F.datumIso.val.indexEquiv.surjective a
    rw [h, neg_ne_zero]
    exact mul_ne_zero hn.ne' (D.base.height_ne_zero i)
  · ext a
    obtain ⟨i, rfl⟩ := F.datumIso.val.indexEquiv.surjective a
    change 0 < pairing F.pinned.pair.T.group (F.datumIso.val.indexEquiv i).val
      (realizedCocharacter F (-y)) ↔
        ¬ F.datumIso.val.indexEquiv i ∈ subgroupRoots F.pinned.pair.T F.pinned.pair.B
    rw [h, marking_matches_positiveRoots hChambers F, neg_pos]
    change n * D.base.height i < 0 ↔ ¬ 0 < D.base.height i
    rw [mul_neg_iff]
    simp only [hn, not_lt_of_ge hn.le, true_and, false_and, or_false]
    exact ⟨fun hlt hgt => (not_lt_of_ge hgt.le) hlt, fun hn' =>
      lt_of_le_of_ne (le_of_not_gt hn') (D.base.height_ne_zero i)⟩

private theorem iso_of_sameSubgroup {G : Specs.GroupScheme k} {H J : Specs.ClosedSubgroup G}
    (h : Specs.RankOneFlag.SameSubgroup H J) :
    ∃ e : H.group ≅ J.group, e.hom ≫ J.inclusion = H.inclusion ∧
      e.inv ≫ H.inclusion = J.inclusion := by
  obtain ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := h
  have hm (S : Specs.ClosedSubgroup G) : Mono S.inclusion := by
    have := S.isClosedImmersion
    have : Mono S.inclusion.hom.hom := Over.mono_of_mono_left S.inclusion.hom.hom
    exact (Grp.forget _).mono_of_mono_map (f := S.inclusion) this
  letI := hm H
  letI := hm J
  exact ⟨⟨f, g, (cancel_mono H.inclusion).mp (by rw [Category.assoc, hg, hf, Category.id_comp]),
    (cancel_mono J.inclusion).mp (by rw [Category.assoc, hf, hg, Category.id_comp])⟩, hf, hg⟩

/-- For the negative chamber the scheme-theoretic limit map is the projection
onto the marked torus in the opposite Borel. -/
theorem oppositeBorelProjection_of_limit (hChambers : BorelsThroughT.{u})
    (hRegular : RegularCocharacterBorel.{u}) (F : Realization D L)
    (y : D.Y) (n : ℤ) (hn : 0 < n)
    (hy : ∀ i : D.I, D.datum.root' i y = n * D.base.height i)
    (C : LimitDecomposition (realizedCocharacter F (-y) ≫ F.pinned.pair.T.inclusion)) :
    ∃ (hB : Specs.GeometricBorelConjugacy.IsKBorel C.parabolic)
      (hT : Specs.SchemeDerivedGroup.IsSubgroupOf F.pinned.pair.T C.parabolic)
      (hop : Specs.OpenCell.AreOpposite F.pinned.pair.T F.pinned.pair.B C.parabolic)
      (e : C.centralizer.group ≅ F.pinned.pair.T.group),
      e.hom ≫ F.pinned.pair.T.inclusion = C.centralizer.inclusion ∧
      let P : Specs.FlagLineBundle.OppositeBorelPair F.pinned.pair.G :=
        ⟨F.pinned.pair.T, F.pinned.pair.B, C.parabolic, F.pinned.pair.reductive,
          F.pinned.pair.split, F.pinned.pair.maximal, F.pinned.pair.borel,
          hB, F.pinned.pair.containsTorus, hT, hop⟩
      ∃ p : Specs.FlagLineBundle.BorelProjection P, p.projection = C.limit ≫ e.hom := by
  let P := F.pinned.pair
  obtain ⟨hr, hp⟩ := realizedCocharacter_negativeChamber hChambers F y n hn hy
  obtain ⟨hc, hB, hT, hcRoots, hU, _⟩ :=
    hRegular P.G P.reductive P.T P.split P.maximal _ hr C
  obtain ⟨e, he, hei⟩ := iso_of_sameSubgroup hc
  refine ⟨hB, hT, hcRoots.trans hp, e, he, ?_⟩
  refine ⟨{
    inclusion := e.inv ≫ C.sectionMap
    inclusion_comp := by rw [Category.assoc, C.section_in_G, hei]
    projection := C.limit ≫ e.hom
    section_projection := by simp only [← Category.assoc, Category.assoc e.inv C.sectionMap C.limit,
      C.section_limit, Category.comp_id, Iso.inv_hom_id]
    radical := contractingSubgroup C
    isRadical := hU
    isKernel := ?_ }, rfl⟩
  let e' : C.centralizer.group.X ≅ P.T.group.X := (Grp.forget _).mapIso e
  change IsPullback C.contractingToParabolic.hom.hom (toUnit C.contracting.group.X)
    (C.limit.hom.hom ≫ e'.hom) η[P.T.group.X]
  exact C.isKernel.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _) e'.symm
    (by simp) (by simp)
    (by
      change 𝟙 _ ≫ C.limit.hom.hom = (C.limit.hom.hom ≫ e'.hom) ≫ e'.inv
      rw [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id])
    (by
      change 𝟙 _ ≫ η[C.centralizer.group.X] = η[P.T.group.X] ≫ e.inv.hom.hom
      rw [Category.id_comp, IsMonHom.one_hom])

end OppositeBorel

section MarkedFibres

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Specs.IntegralSemisimpleModel
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (Realization)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue pairing)
open CocharacterDynamics
open WithConv

attribute [local instance] convolutionGroup
attribute [local instance 50] integerAlgebra

open private exists_markedTorusIso forgetFibrePoint_comp fibrePointsEquiv
  restrictToIntegers torusPoint_natural cocharacter_natural
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

set_option backward.isDefEq.respectTransparency false in
private theorem realizedCocharacter_value {k : Type u} [Field k]
    {D : BasedRootDatum.{u}} {L : Specs.RootGroups.AdditiveLine k}
    (F : Realization D L) (y : D.Y) (x : D.X)
    (R : TestAlgebra k) (s : Rˣ) :
    characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
      (cocharacterPoint (realizedCocharacter F y) R s) =
      (s ^ D.datum.toLinearMap x y : Rˣ).val := by
  rw [(LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition
    F.pinned.pair.T.group _ _).2]
  have h := F.datumIso.val.toLinearMap_weightEquiv x (F.datumIso.val.coweightEquiv.symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  letI := F.attached.comm
  rw [← F.attached.datum.pairing_eq]
  change (s ^ F.attached.toBased.datum.toLinearMap (F.datumIso.val.weightEquiv x)
    (F.datumIso.val.coweightEquiv.symm y) : Rˣ).val = _
  rw [h]

/-- Testing the characters in the marked lattice detects points of the torus
even on nonreduced test rings. -/
private theorem markedTorus_point_ext {k : Type u} [Field k]
    {D : BasedRootDatum.{u}} {L : Specs.RootGroups.AdditiveLine k}
    (F : Realization D L) (R : TestAlgebra k)
    {p q : GroupPoints F.pinned.pair.T.group R}
    (h : ∀ x : D.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R p =
      characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R q) : p = q := by
  obtain ⟨e, he⟩ := exists_markedTorusIso F
  let S := MonoidAlgebra k (Multiplicative D.X)
  let E := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a : S →ₐ[k] R := (E.preimage (p ≫ e.inv.hom.hom)).unop.hom
  let b : S →ₐ[k] R := (E.preimage (q ≫ e.inv.hom.hom)).unop.hom
  have ha : affinePoint a ≫ e.hom.hom.hom = p := by
    have H : affinePoint a = p ≫ e.inv.hom.hom := E.map_preimage _
    rw [H, Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hb : affinePoint b ≫ e.hom.hom.hom = q := by
    have H : affinePoint b = q ≫ e.inv.hom.hom := E.map_preimage _
    rw [H, Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hab : a = b := by
    apply MonoidAlgebra.algHom_ext
    · intro x
      have h₁ := he R a x.toAdd
      have h₂ := he R b x.toAdd
      change characterValue _ R (affinePoint a ≫ e.hom.hom.hom) = _ at h₁
      change characterValue _ R (affinePoint b ≫ e.hom.hom.hom) = _ at h₂
      rw [ha] at h₁
      rw [hb] at h₂
      exact h₁.symm.trans ((h x.toAdd).trans h₂)
    · exact Subsingleton.elim _ _
  rw [← ha, ← hb, hab]

private theorem forgetPoint_realizedCocharacter {k : Type u} [Field k]
    {D : BasedRootDatum.{u}} {L : Specs.RootGroups.AdditiveLine k}
    (F : Realization D L) (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
    (ht : ∀ (R : TestAlgebra k)
        (p : GroupPoints ((fibre k).obj (splitTorus D)) R)
        (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
      forgetFibrePoint (splitTorus D) R p = torusPoint D _ v →
      ∀ x : D.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
        (p ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R))
    (y : D.Y) (R : TestAlgebra k) (s : Rˣ) :
    forgetFibrePoint (splitTorus D) R
      (cocharacterPoint (realizedCocharacter F y) R s ≫ t.inv.hom.hom) =
        torusPoint D _ (cocharacter D y _ s) := by
  let v := cocharacter D y (CommAlgCat.of Integers.{u} R) s
  obtain ⟨p, hp⟩ := (LinearAlgebraicGroups.Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective (splitTorus D) R).surjective (torusPoint D _ v)
  have h : p ≫ t.hom.hom.hom = cocharacterPoint (realizedCocharacter F y) R s := by
    apply markedTorus_point_ext F R
    intro x
    rw [ht R p v hp x, realizedCocharacter_value]
    rfl
  rw [← h, Category.assoc, ← Grp.comp_hom_hom, t.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  exact hp

/-- The generic unit used for conjugation can be formed over any base ring. -/
private def laurentUnit (B : Type u) [CommRing B] : (LaurentPolynomial B)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num [LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num [LaurentPolynomial.T_zero]

variable {A : Type u} [CommRing A] [HopfAlgebra Integers.{u} A]

private abbrev integralHopfGroup :=
  (hopfSpec (CommRingCat.of Integers.{u})).obj (op (CommHopfAlgCat.of Integers.{u} A))

/-- In integral Hopf coordinates the chosen point is the marked cocharacter
evaluated at the unit of the punctured affine line. -/
private def laurentCocharacter {D : BasedRootDatum.{u}} (I : Model D) (y : D.Y)
    (e : integralHopfGroup (A := A) ≅ I.group) : A →ₐ[Integers.{u}] LaurentPolynomial Integers.{u} :=
  let R := CommAlgCat.of Integers.{u} (LaurentPolynomial Integers.{u})
  ((algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).preimage
    (torusPoint D R (cocharacter D y R (laurentUnit Integers.{u})) ≫ I.torus.hom.hom ≫
      e.inv.hom.hom)).unop.hom

private theorem laurentCocharacter_apply {D : BasedRootDatum.{u}} (I : Model D) (y : D.Y)
    (e : integralHopfGroup (A := A) ≅ I.group)
    (B : Type u) [CommRing B] [Algebra Integers.{u} B] :
    affinePoint ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId Integers.{u} B)).comp
      (laurentCocharacter I y e)) ≫ e.hom.hom.hom =
      torusPoint D (CommAlgCat.of Integers.{u} (LaurentPolynomial B))
        (cocharacter D y _ (laurentUnit B)) ≫ I.torus.hom.hom := by
  let R := CommAlgCat.of Integers.{u} (LaurentPolynomial Integers.{u})
  let S := CommAlgCat.of Integers.{u} (LaurentPolynomial B)
  let f : R ⟶ S := CommAlgCat.ofHom (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId Integers.{u} B))
  rw [affinePoint_comp]
  have h : affinePoint (laurentCocharacter I y e) =
      torusPoint D R (cocharacter D y R (laurentUnit Integers.{u})) ≫ I.torus.hom.hom ≫
        e.inv.hom.hom :=
    (algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).map_preimage _
  rw [h, Category.assoc, Category.assoc, Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]
  rw [← Category.assoc, torusPoint_natural f, cocharacter_natural]
  congr 3
  apply Units.ext
  change AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId Integers.{u} B)
    (LaurentPolynomial.T 1) = LaurentPolynomial.T 1
  rw [LaurentPolynomial.T, AddMonoidAlgebra.mapAlgHom_single, map_one]
  rfl

private theorem integerHom_unique {B : Type u} [CommRing B] (f g : Integers.{u} →+* B) :
    f = g := by
  ext x
  let i : ℤ →+* Integers.{u} := ULift.ringEquiv.symm.toRingHom
  have hf : (f.comp i) x.down = (x.down : B) := map_intCast (f.comp i) x.down
  have hg : (g.comp i) x.down = (x.down : B) := map_intCast (g.comp i) x.down
  exact hf.trans hg.symm

/-- A scheme point over the integers can be rebundled with any scalar tower
from the integers. This handles the induced algebras on polynomial rings. -/
private def integerPoint {B : Type u} [CommRing B] [Algebra Integers.{u} B]
    (G : IntegralGroup.{u}) (p : Spec (CommRingCat.of B) ⟶ G.X.left) :
    IntegralPoints G (CommAlgCat.of Integers.{u} B) :=
  Over.homMk p (by
    let f := Spec.preimage (p ≫ G.X.hom)
    have h : f = CommRingCat.ofHom (algebraMap Integers.{u} B) :=
      CommRingCat.hom_ext (integerHom_unique f.hom _)
    exact (Spec.map_preimage _).symm.trans (congrArg Spec.map h))

private theorem integerPoint_mul {B : Type u} [CommRing B] [Algebra Integers.{u} B]
    (G : IntegralGroup.{u}) (p q : Spec (CommRingCat.of B) ⟶ G.X.left) :
    (integerPoint G p * integerPoint G q).left =
      ((@integerPoint B _ (integerAlgebra B) G p) *
       (@integerPoint B _ (integerAlgebra B) G q)).left := rfl

private def pointOverIntegers {k : Type u} [Field k] {H : Specs.GroupScheme k}
    {G : IntegralGroup.{u}} (e : (fibre k).obj G ≅ H)
    (R : TestAlgebra k) [Algebra Integers.{u} R] (p : GroupPoints H R) :
    IntegralPoints G (CommAlgCat.of Integers.{u} R) :=
  integerPoint G (forgetFibrePoint G R (p ≫ e.inv.hom.hom)).left

private theorem pointOverIntegers_bijective {k : Type u} [Field k] {H : Specs.GroupScheme k}
    {G : IntegralGroup.{u}} (e : (fibre k).obj G ≅ H)
    (R : TestAlgebra k) [Algebra Integers.{u} R] :
    Function.Bijective (pointOverIntegers e R) := by
  let w : GroupPoints H R ≃ GroupPoints ((fibre k).obj G) R :=
    { toFun := fun p => p ≫ e.inv.hom.hom
      invFun := fun p => p ≫ e.hom.hom.hom
      left_inv := fun p => by
        change (p ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = p
        rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
      right_inv := fun p => by
        change (p ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = p
        rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] }
  let v : IntegralPoints G ((restrictToIntegers k).obj R) ≃
      IntegralPoints G (CommAlgCat.of Integers.{u} R) :=
    ⟨fun p => integerPoint G p.left, fun p => Over.homMk p.left
      (by exact (@integerPoint R _ (integerAlgebra R) G p.left).w),
      fun _ => Over.OverMorphism.ext rfl, fun _ => Over.OverMorphism.ext rfl⟩
  exact (w.trans ((fibrePointsEquiv G R).toEquiv.trans v)).bijective

private theorem pointOverIntegers_mul {k : Type u} [Field k] {H : Specs.GroupScheme k}
    {G : IntegralGroup.{u}} (e : (fibre k).obj G ≅ H)
    (R : TestAlgebra k) [Algebra Integers.{u} R] (p q : GroupPoints H R) :
    pointOverIntegers e R (p * q) = pointOverIntegers e R p * pointOverIntegers e R q := by
  apply Over.OverMorphism.ext
  unfold pointOverIntegers
  rw [integerPoint_mul]
  have h := (fibrePointsEquiv G R).map_mul (p ≫ e.inv.hom.hom) (q ≫ e.inv.hom.hom)
  change (forgetFibrePoint G R ((p * q) ≫ e.inv.hom.hom)).left = _
  rw [MonObj.mul_comp]
  exact congrArg Over.Hom.left h

private theorem pointOverIntegers_inv {k : Type u} [Field k] {H : Specs.GroupScheme k}
    {G : IntegralGroup.{u}} (e : (fibre k).obj G ≅ H)
    (R : TestAlgebra k) [Algebra Integers.{u} R] (p : GroupPoints H R) :
    pointOverIntegers e R p⁻¹ = (pointOverIntegers e R p)⁻¹ := by
  apply Over.OverMorphism.ext
  unfold pointOverIntegers
  rw [show (p⁻¹ : GroupPoints H R) ≫ e.inv.hom.hom = (p ≫ e.inv.hom.hom)⁻¹
    from GrpObj.inv_comp _ _]
  change (forgetFibrePoint G R (p ≫ e.inv.hom.hom)⁻¹).left =
    ((forgetFibrePoint G R (p ≫ e.inv.hom.hom))⁻¹).left
  exact congrArg Over.Hom.left ((fibrePointsEquiv G R).map_inv (p ≫ e.inv.hom.hom))

private theorem pointOverIntegers_map {k : Type u} [Field k] {H : Specs.GroupScheme k}
    {G : IntegralGroup.{u}} (e : (fibre k).obj G ≅ H)
    {R S : TestAlgebra k} [Algebra Integers.{u} R] [Algebra Integers.{u} S]
    (f : R ⟶ S) (g : R →ₐ[Integers.{u}] S) (hfg : f.hom.toRingHom = g.toRingHom)
    (p : GroupPoints H R) :
    pointOverIntegers e S (mapPoints f p) = affinePoint g ≫ pointOverIntegers e R p := by
  apply Over.OverMorphism.ext
  change (Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ p.left ≫ e.inv.hom.hom.left) ≫
      pullback.fst G.X.hom _ =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (p.left ≫ e.inv.hom.hom.left) ≫
      pullback.fst G.X.hom _
  simp only [Category.assoc, hfg]

private theorem pointOverIntegers_comp {k : Type u} [Field k]
    {G J : IntegralGroup.{u}} {H : Specs.GroupScheme k} (e : (fibre k).obj G ≅ H)
    (f : J ⟶ G) (R : TestAlgebra k) [Algebra Integers.{u} R]
    (p : GroupPoints ((fibre k).obj J) R) :
    pointOverIntegers e R (p ≫ (((fibre k).map f) ≫ e.hom).hom.hom) =
      pointOverIntegers (Iso.refl ((fibre k).obj J)) R p ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  change (forgetFibrePoint G R ((p ≫ (((fibre k).map f) ≫ e.hom).hom.hom) ≫
    e.inv.hom.hom)).left = (forgetFibrePoint J R (p ≫ 𝟙 _) ≫ f.hom.hom).left
  simp only [Grp.comp_hom_hom, Category.assoc, ← Grp.comp_hom_hom e.hom e.inv, e.hom_inv_id,
    Grp.id_hom_hom, Category.comp_id, forgetFibrePoint_comp]

/-- The marked field cocharacter and the universal Laurent point of the
integral Hopf presentation give the same conjugating element. -/
private theorem markedLaurentPoint {k : Type u} [Field k]
    {D : BasedRootDatum.{u}} {L : Specs.RootGroups.AdditiveLine k}
    (I : Model D) (F : Realization D L) (y : D.Y)
    (e : integralHopfGroup (A := A) ≅ I.group)
    (E : (fibre k).obj I.group ≅ F.pinned.pair.G.val)
    (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
    (hT : ((fibre k).map I.torus) ≫ E.hom = t.hom ≫ F.pinned.pair.T.inclusion)
    (ht : ∀ (R : TestAlgebra k) (p : GroupPoints ((fibre k).obj (splitTorus D)) R)
        (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
      forgetFibrePoint (splitTorus D) R p = torusPoint D _ v →
      ∀ x : D.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
        (p ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R))
    (B : TestAlgebra k) :
    let cochar := realizedCocharacter F y ≫ F.pinned.pair.T.inclusion
    let j := (fibre k).mapIso e ≪≫ E
    pointOverIntegers j (laurentAlgebra B) (cocharacterPoint cochar _ (laurentParameter B)) =
      affinePoint ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId Integers.{u} B)).comp
        (laurentCocharacter I y e)) := by
  let C := laurentAlgebra B
  let s := laurentParameter B
  let p := cocharacterPoint (realizedCocharacter F y) C s ≫ t.inv.hom.hom
  have hp := forgetPoint_realizedCocharacter F t ht y C s
  let E' := (fibre k).mapIso e ≪≫ E
  have hp' : p ≫ t.hom.hom.hom = cocharacterPoint (realizedCocharacter F y) C s := by
    dsimp only [p]
    rw [Category.assoc, ← Grp.comp_hom_hom, t.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hh : cocharacterPoint (realizedCocharacter F y ≫ F.pinned.pair.T.inclusion) C s =
      p ≫ (((fibre k).map I.torus) ≫ E.hom).hom.hom := by
    rw [hT, Grp.comp_hom_hom, ← Category.assoc p, hp']
    change unitPoint C s ≫
      ((realizedCocharacter F y).hom.hom ≫ F.pinned.pair.T.inclusion.hom.hom) =
      (unitPoint C s ≫ (realizedCocharacter F y).hom.hom) ≫ F.pinned.pair.T.inclusion.hom.hom
    rw [Category.assoc]
  have h₁ : pointOverIntegers E C (cocharacterPoint
      (realizedCocharacter F y ≫ F.pinned.pair.T.inclusion) C s) =
      pointOverIntegers (Iso.refl ((fibre k).obj (splitTorus D))) C p ≫ I.torus.hom.hom := by
    rw [hh, pointOverIntegers_comp]
  have h₃ := laurentCocharacter_apply I y e B
  apply (cancel_mono e.hom.hom.hom).mp
  apply Over.OverMorphism.ext
  -- Both underlying morphisms are the integral torus point followed by its inclusion.
  have h₄ := forgetFibrePoint_comp e.hom C
    (cocharacterPoint (realizedCocharacter F y ≫ F.pinned.pair.T.inclusion) C s ≫ E'.inv.hom.hom)
  have h₅ := congrArg Over.Hom.left h₁
  have h₆ := congrArg Over.Hom.left hp
  have h₇ := congrArg Over.Hom.left h₃
  change (forgetFibrePoint (integralHopfGroup (A := A)) C
    (cocharacterPoint (realizedCocharacter F y ≫ F.pinned.pair.T.inclusion) C s ≫
      E'.inv.hom.hom)).left ≫ e.hom.hom.hom.left = _
  rw [← Over.comp_left, ← h₄]
  change (forgetFibrePoint I.group C ((cocharacterPoint _ C s ≫
    (E.inv.hom.hom ≫ ((fibre k).map e.inv).hom.hom)) ≫
      ((fibre k).map e.hom).hom.hom)).left = _
  simp only [Category.assoc, ← Grp.comp_hom_hom ((fibre k).map e.inv) ((fibre k).map e.hom),
    ← Functor.map_comp, e.inv_hom_id]
  rw [show (fibre k).map (𝟙 I.group) = 𝟙 _ from (fibre k).map_id I.group,
    Grp.id_hom_hom, Category.comp_id]
  exact h₅.trans (congrArg (· ≫ I.torus.hom.hom.left) h₆ |>.trans h₇.symm)


/-- The scheme point corresponding to a convolution point. -/
private abbrev specPoint (B : Type u) [CommRing B] [Algebra Integers.{u} B] :=
  Spec.mapMulEquiv (R := Integers.{u}) (S := A) (T := B)

private theorem restrictOrbit {k : Type u} [Field k] {H : Specs.GroupScheme k}
    (E : (fibre k).obj (integralHopfGroup (A := A)) ≅ H)
    (c : A →ₐ[Integers.{u}] LaurentPolynomial Integers.{u})
    (cochar : Specs.CharacterDescent.Cocharacter H)
    (B : TestAlgebra k) (g : A →ₐ[Integers.{u}] B)
    (p : GroupPoints H B) (hp : pointOverIntegers E B p = affinePoint g)
    (hCochar : pointOverIntegers E (laurentAlgebra B)
      (cocharacterPoint cochar _ (laurentParameter B)) =
        affinePoint ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId Integers.{u} B)).comp c)) :
    pointOverIntegers E (laurentAlgebra B) (orbit cochar p) =
      affinePoint (conjugateLaurentPoint c (toConv g)).ofConv := by
  let t := cocharacterPoint cochar (laurentAlgebra B) (laurentParameter B)
  let t' := (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId Integers.{u} B)).comp c
  let j := IsScalarTower.toAlgHom Integers.{u} B (LaurentPolynomial B)
  let p' : GroupPoints H (laurentAlgebra B) := mapPoints (laurentConstants B) p
  change pointOverIntegers E (laurentAlgebra B) (t * p' * t⁻¹) = _
  have hj := pointOverIntegers_map E (laurentConstants B) j rfl p
  change pointOverIntegers E (laurentAlgebra B) p' = _ at hj
  rw [hp, ← affinePoint_comp] at hj
  rw [pointOverIntegers_mul, pointOverIntegers_mul, pointOverIntegers_inv, hCochar, hj]
  change (specPoint (LaurentPolynomial B)) (toConv t') *
      (specPoint (LaurentPolynomial B)) (toConv (j.comp g)) *
      ((specPoint (LaurentPolynomial B)) (toConv t'))⁻¹ =
        (specPoint (LaurentPolynomial B)) (toConv t' * toConv (j.comp g) * (toConv t')⁻¹)
  simp only [map_mul, map_inv]

private theorem fieldExtension_iff {k : Type u} [Field k] {H : Specs.GroupScheme k}
    (E : (fibre k).obj (integralHopfGroup (A := A)) ≅ H)
    (c : A →ₐ[Integers.{u}] LaurentPolynomial Integers.{u})
    (cochar : Specs.CharacterDescent.Cocharacter H)
    (R : TestAlgebra k) (g : GroupPoints H R)
    (v : A →ₐ[Integers.{u}] R) (hv : pointOverIntegers E R g = affinePoint v)
    (hCochar : pointOverIntegers E (laurentAlgebra R)
      (cocharacterPoint cochar _ (laurentParameter R)) =
        affinePoint ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId Integers.{u} R)).comp c)) :
    HasExtension cochar g ↔
      ∃ p : A →ₐ[Integers.{u}] Polynomial R,
        polynomialToLaurent.comp p = (conjugateLaurentPoint c (toConv v)).ofConv := by
  let P := polynomialAlgebra R
  let L := laurentAlgebra R
  let j : Polynomial R →ₐ[Integers.{u}] LaurentPolynomial R := polynomialToLaurent
  let d := (algSpec.fullyFaithful (R := CommRingCat.of Integers.{u}))
  have ho := restrictOrbit E c cochar R v g hv hCochar
  have he (y : GroupPoints H P) (p : A →ₐ[Integers.{u}] Polynomial R)
      (hp : pointOverIntegers E P y = affinePoint p) :
      mapPoints (CocharacterDynamics.polynomialToLaurent R) y = orbit cochar g ↔
        j.comp p = (conjugateLaurentPoint c (toConv v)).ofConv := by
    have hh := pointOverIntegers_map E (CocharacterDynamics.polynomialToLaurent R) j rfl y
    rw [hp, ← affinePoint_comp] at hh
    constructor
    · intro h
      rw [h, ho] at hh
      exact congrArg WithConv.ofConv ((specPoint (LaurentPolynomial R)).injective hh.symm)
    · intro h
      apply (pointOverIntegers_bijective E L).injective
      rw [hh, ho, h]
  constructor
  · rintro ⟨_, y, hy, _⟩
    let p : A →ₐ[Integers.{u}] Polynomial R := (d.preimage (pointOverIntegers E P y)).unop.hom
    exact ⟨p, (he y p (d.map_preimage _).symm).mp hy⟩
  · rintro ⟨p, hp⟩
    obtain ⟨y, hy⟩ := (pointOverIntegers_bijective E P).surjective (affinePoint p)
    exact ⟨mapPoints (polynomialEvaluate R 0) y, y, (he y p hy).mpr hp, rfl⟩

private theorem fieldLimitAtZero {k : Type u} [Field k] {H : Specs.GroupScheme k}
    (E : (fibre k).obj (integralHopfGroup (A := A)) ≅ H)
    (c : A →ₐ[Integers.{u}] LaurentPolynomial Integers.{u})
    (cochar : Specs.CharacterDescent.Cocharacter H)
    (R : TestAlgebra k)
    (hCochar : pointOverIntegers E (laurentAlgebra R)
      (cocharacterPoint cochar _ (laurentParameter R)) =
        affinePoint ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId Integers.{u} R)).comp c))
    (s : GroupPoints ((fibre k).obj (conjugationLimit c)) R) :
    HasLimit cochar
      (s ≫ (((fibre k).map (conjugationLimitInclusion c)) ≫ E.hom).hom.hom)
      (s ≫ (((fibre k).map (conjugationLimitEvaluation c)) ≫ E.hom).hom.hom) := by
  let P := polynomialAlgebra R
  let L := laurentAlgebra R
  let j : Polynomial R →ₐ[Integers.{u}] LaurentPolynomial R := polynomialToLaurent
  let d := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
  let S := (fibre k).obj (conjugationLimit c)
  let s' := pointOverIntegers (Iso.refl S) R s
  let I := limitIdeal (conjugationOrbit c)
  let f : (A ⧸ I) →ₐ[Integers.{u}] R := (d.preimage s').unop.hom
  have hf : affinePoint f = s' := d.map_preimage _
  let v := f.comp (Ideal.Quotient.mkₐ Integers.{u} I)
  let p := (polynomialOrbitHom c ⟨toConv v, factor_mem_polynomialLimitSubgroup c f⟩).ofConv
  let g := s ≫ (((fibre k).map (conjugationLimitInclusion c)) ≫ E.hom).hom.hom
  have hg : pointOverIntegers E R g = affinePoint v := by
    rw [pointOverIntegers_comp]
    change s' ≫ (conjugationLimitInclusion c).hom.hom = affinePoint v
    rw [← hf]
    exact (affinePoint_comp f _).symm
  obtain ⟨y, hy⟩ := (pointOverIntegers_bijective E P).surjective (affinePoint p)
  refine ⟨y, ?_, ?_⟩
  · apply (pointOverIntegers_bijective E L).injective
    rw [pointOverIntegers_map E (CocharacterDynamics.polynomialToLaurent R) j rfl y, hy,
      ← affinePoint_comp, restrictOrbit E c cochar R v g hg hCochar]
    exact congrArg affinePoint (polynomialOrbitHom_spec c _)
  · apply (pointOverIntegers_bijective E R).injective
    let eval := Polynomial.aevalTower (AlgHom.id Integers.{u} R) (0 : R)
    rw [pointOverIntegers_map E (polynomialEvaluate R 0) eval rfl y, hy,
      ← affinePoint_comp, pointOverIntegers_comp]
    change affinePoint (eval.comp p) = s' ≫ (conjugationLimitEvaluation c).hom.hom
    rw [← hf]
    change affinePoint (eval.comp p) = affinePoint f ≫ affinePoint (limitAtZero c)
    rw [← affinePoint_comp]
    exact congrArg affinePoint (limitPoint_universal c f (factor_mem_polynomialLimitSubgroup c f))

open private subgroupInclusionFactors from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

/-- The fibre of the closed limit locus represents the field parabolic, with
its zero evaluation agreeing with the field limit homomorphism. -/
private theorem compareConjugationLimit {k : Type u} [Field k] {H : Specs.GroupScheme k}
    (hH : IsAffine H.X.left)
    (E : (fibre k).obj (integralHopfGroup (A := A)) ≅ H)
    (c : A →ₐ[Integers.{u}] LaurentPolynomial Integers.{u})
    (cochar : Specs.CharacterDescent.Cocharacter H) (C : LimitDecomposition cochar)
    (hCochar : ∀ R : TestAlgebra k, pointOverIntegers E (laurentAlgebra R)
      (cocharacterPoint cochar _ (laurentParameter R)) =
        affinePoint ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId Integers.{u} R)).comp c)) :
    ∃ e : (fibre k).obj (conjugationLimit c) ≅ C.parabolic.group,
      ((fibre k).map (conjugationLimitInclusion c)) ≫ E.hom = e.hom ≫ C.parabolic.inclusion ∧
      ((fibre k).map (conjugationLimitEvaluation c)) ≫ E.hom =
        e.hom ≫ C.limit ≫ C.centralizer.inclusion := by
  let S := (fibre k).obj (conjugationLimit c)
  let i := ((fibre k).map (conjugationLimitInclusion c)) ≫ E.hom
  let ar : IsClosedImmersion i.hom.hom.left := by
    have : IsClosedImmersion ((fibre k).map (conjugationLimitInclusion c)).hom.hom.left :=
      MorphismProperty.of_isPullback
        (changeBaseMap_isPullback (algebraMap Integers.{u} k)
          (conjugationLimitInclusion c).hom.hom).flip
        (conjugationLimitInclusion_isClosedImmersion c)
    have : IsIso E.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso E.hom
    exact IsClosedImmersion.comp _ _
  let P : Specs.ClosedSubgroup H := ⟨S, i, ar⟩
  have hcrit (R : TestAlgebra k) (g : GroupPoints H R) :
      HasExtension cochar g ↔ ∃ s : GroupPoints S R, s ≫ i.hom.hom = g := by
    let d := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
    let v : A →ₐ[Integers.{u}] R := (d.preimage (pointOverIntegers E R g)).unop.hom
    have hv : affinePoint v = pointOverIntegers E R g := d.map_preimage _
    rw [fieldExtension_iff E c cochar R g v hv.symm (hCochar R), ← conjugationLimit_point_iff c v]
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨s, hs⟩ := (pointOverIntegers_bijective (Iso.refl S) R).surjective p
      refine ⟨s, (pointOverIntegers_bijective E R).injective ?_⟩
      rw [pointOverIntegers_comp, hs, hp, hv]
    · rintro ⟨s, rfl⟩
      refine ⟨pointOverIntegers (Iso.refl S) R s, ?_⟩
      rw [hv, pointOverIntegers_comp]
  have haS : IsAffine S.X.left := by
    letI := hH
    letI := ar
    exact isAffine_of_isAffineHom i.hom.hom.left
  have haP : IsAffine C.parabolic.group.X.left := by
    letI := hH
    letI := C.parabolic.isClosedImmersion
    exact isAffine_of_isAffineHom C.parabolic.inclusion.hom.hom.left
  obtain ⟨f, hf⟩ := subgroupInclusionFactors haS C.parabolic i
    (fun R s => (C.parabolic_points R _).mp ((hcrit R _).mpr ⟨s, rfl⟩))
  obtain ⟨g, hg⟩ := subgroupInclusionFactors haP P C.parabolic.inclusion
    (fun R s => (hcrit R _).mp ((C.parabolic_points R _).mpr ⟨s, rfl⟩))
  obtain ⟨e, he, _⟩ := iso_of_sameSubgroup (show Specs.RankOneFlag.SameSubgroup P C.parabolic from
    ⟨⟨f, hf⟩, ⟨g, hg⟩⟩)
  refine ⟨e, he.symm, (groupHomComparison k S H haS).1 ?_⟩
  ext R s
  letI : IsAffine H.X.left := hH
  apply CocharacterDynamics.limitIsUnique (G := H) cochar
    (fieldLimitAtZero E c cochar R (hCochar R) s)
  have h := C.limit_points R (s ≫ e.hom.hom.hom)
  change HasLimit cochar ((s ≫ e.hom.hom.hom) ≫ C.parabolic.inclusion.hom.hom)
    ((s ≫ e.hom.hom.hom) ≫ (C.limit ≫ C.centralizer.inclusion).hom.hom) at h
  rw [Category.assoc, ← Grp.comp_hom_hom, he] at h
  change HasLimit cochar (s ≫ P.inclusion.hom.hom)
    (s ≫ (e.hom ≫ C.limit ≫ C.centralizer.inclusion).hom.hom)
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

/-- The Borel and its projection chosen using the supplied pinning in a
field fibre of the integral group. -/
private structure IntegralBorelFibre {D : BasedRootDatum.{u}} (I : Model D)
    (J : IntegralGroup.{u}) (inclusion limit : J ⟶ I.group) (k : Type u) [Field k] where
  additive : Specs.RootGroups.AdditiveLine k
  realization : Realization D additive
  integralIso : (fibre k).obj I.group ≅ realization.pinned.pair.G.val
  torusIso : (fibre k).obj (splitTorus D) ≅ realization.pinned.pair.T.group
  torus_marking : ((fibre k).map I.torus) ≫ integralIso.hom =
    torusIso.hom ≫ realization.pinned.pair.T.inclusion
  rootCoordinate : ∀ a : D.I, Specs.Pinning.RootCoordinate additive realization.pinned.pair.T
    (realization.pinned.roots (realization.datumIso.val.indexEquiv a)).val
    (realization.datumIso.val.indexEquiv a).val
  simple_marking : ∀ a : D.base.support,
    rootCoordinate a.val = realization.pinned.pin (realization.simpleRoot a)
  root_marking : ∀ (a : D.I) (R : TestAlgebra k) (r : R),
    forgetFibrePoint I.group R
      (Specs.RootGroups.rootPoint ((rootCoordinate a).val.hom ≫
        (realization.pinned.roots (realization.datumIso.val.indexEquiv a)).val.inclusion ≫
          integralIso.inv) R r) =
      I.line.point (@CommAlgCat.of Integers _ R _ (integerAlgebra R)) r ≫ (I.root a).hom.hom
  weight_marking : ∀ (R : TestAlgebra k) (p : GroupPoints ((fibre k).obj (splitTorus D)) R),
    letI : Algebra Integers.{u} R := integerAlgebra R
    ∀ (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
      forgetFibrePoint (splitTorus D) R p = torusPoint D _ v →
      ∀ x : D.X, characterValue (Additive.toMul (realization.datumIso.val.weightEquiv x)) R
        (p ≫ torusIso.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R)
  negative : Specs.ClosedSubgroup realization.pinned.pair.G.val
  negativeBorel : Specs.GeometricBorelConjugacy.IsKBorel negative
  inNegative : Specs.SchemeDerivedGroup.IsSubgroupOf realization.pinned.pair.T negative
  opposite : Specs.OpenCell.AreOpposite realization.pinned.pair.T realization.pinned.pair.B negative
  borelIso : (fibre k).obj J ≅ negative.group
  inclusion_eq : ((fibre k).map inclusion) ≫ integralIso.hom = borelIso.hom ≫ negative.inclusion
  projection : Specs.FlagLineBundle.BorelProjection
    ⟨realization.pinned.pair.T, realization.pinned.pair.B, negative,
      realization.pinned.pair.reductive, realization.pinned.pair.split,
      realization.pinned.pair.maximal, realization.pinned.pair.borel, negativeBorel,
      realization.pinned.pair.containsTorus, inNegative, opposite⟩
  limit_eq : ((fibre k).map limit) ≫ integralIso.hom =
    borelIso.hom ≫ projection.projection ≫ realization.pinned.pair.T.inclusion

private theorem integralBorelFibre {D : BasedRootDatum.{u}} (I : Model D)
    (y : D.Y) (n : ℤ) (hn : 0 < n)
    (hy : ∀ a : D.I, D.datum.root' a y = n * D.base.height a)
    (e : integralHopfGroup (A := A) ≅ I.group) (k : Type u) [Field k] :
    let c := laurentCocharacter I (-y) e
    Nonempty (IntegralBorelFibre I (conjugationLimit c)
      (conjugationLimitInclusion c ≫ e.hom) (conjugationLimitEvaluation c ≫ e.hom) k) := by
  obtain ⟨L, F, E, t, z, hT, hz, ht, hroot⟩ := I.fieldFibre k
  let cochar := realizedCocharacter F (-y) ≫ F.pinned.pair.T.inclusion
  obtain ⟨C⟩ := CocharacterDynamics.existsLimitDecomposition F.pinned.pair.G cochar
  obtain ⟨hB, hIn, hOp, eT, heT, p, hp⟩ := oppositeBorelProjection_of_limit
    LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
    LinearAlgebraicGroups.RootData.BorelsAndChambers.regularCocharacterBorel F y n hn hy C
  let c := laurentCocharacter I (-y) e
  let E' := (fibre k).mapIso e ≪≫ E
  obtain ⟨eB, hi, hl⟩ := compareConjugationLimit F.pinned.pair.G.property.1 E' c cochar C
    (markedLaurentPoint I F (-y) e E t hT ht)
  refine ⟨{
    additive := L
    realization := F
    integralIso := E
    torusIso := t
    torus_marking := hT
    rootCoordinate := z
    simple_marking := hz
    root_marking := hroot
    weight_marking := ht
    negative := C.parabolic
    negativeBorel := hB
    inNegative := hIn
    opposite := hOp
    borelIso := eB
    inclusion_eq := ?_
    projection := p
    limit_eq := ?_ }⟩
  · rw [Functor.map_comp, Category.assoc]
    exact hi
  · rw [Functor.map_comp, Category.assoc]
    change (fibre k).map (conjugationLimitEvaluation c) ≫ E'.hom =
      eB.hom ≫ p.projection ≫ F.pinned.pair.T.inclusion
    rw [hl, hp, Category.assoc C.limit, heT]


end MarkedFibres


section ArithmeticGeometry

open Specs.IntegralSemisimpleModel (Integers IntegralGroup integerAlgebra fibre splitTorus)
open Specs.IntegralMarkedOppositeBorel
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection)
open Specs.OrderedCechComparison (SchemeOverRing)
open Specs.Pinning (BasedRootDatum)

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 150000

/-- Iterated pullback identified with pullback along the composite. -/
private def overPullbackComp {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Over.pullback g ⋙ Over.pullback f ≅ Over.pullback (f ≫ g) :=
  NatIso.ofComponents
    (fun P => Over.isoMk (pullbackLeftPullbackSndIso P.hom g f)
      (pullbackLeftPullbackSndIso_hom_snd P.hom g f)) fun {P Q} q => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Functor.comp_map, Over.pullback_map_left, Over.pullback_obj_hom, Over.isoMk_hom_left,
        Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
        pullbackLeftPullbackSndIso_hom_fst_assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [Over.comp_left, Functor.comp_map, Over.pullback_map_left, Over.pullback_obj_hom, Over.isoMk_hom_left,
        Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd]

private def overPullbackCompOfEq {X Y Z : Scheme.{u}} {h : X ⟶ Z}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hh : h = f ≫ g) :
    Over.pullback h ≅ Over.pullback g ⋙ Over.pullback f := by
  subst h
  exact (overPullbackComp f g).symm

private theorem overPullbackCompOfEq_projection {X Y Z : Scheme.{u}} {h : X ⟶ Z}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hh : h = f ≫ g) (P : Over Z) :
    ((overPullbackCompOfEq f g hh).hom.app P).left ≫
      pullback.fst ((Over.pullback g).obj P).hom f ≫ pullback.fst P.hom g =
        pullback.fst P.hom h := by
  subst h
  exact pullbackLeftPullbackSndIso_inv_fst P.hom g f

private def changeBaseGroupCompOfEq {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) {θ : R →+* T} (h : θ = ψ.comp φ) :
    (changeBase θ).mapGrp ≅ (changeBase φ).mapGrp ⋙ (changeBase ψ).mapGrp :=
  by
    have h' : Spec.map (CommRingCat.ofHom θ) =
        Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [h, CommRingCat.ofHom_comp, Spec.map_comp]
    let e : changeBase θ ≅ changeBase φ ⋙ changeBase ψ :=
      overPullbackCompOfEq _ _ h'
    exact Functor.mapGrpNatIso e ≪≫ Functor.mapGrpCompIso

private theorem changeBaseGroupCompOfEq_projection {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) {θ : R →+* T} (h : θ = ψ.comp φ)
    (G : Grp (SchemeOverRing R)) :
    ((changeBaseGroupCompOfEq φ ψ h).hom.app G).hom.hom.left ≫
      fibreProjection ψ ((changeBase φ).obj G.X) ≫ fibreProjection φ G.X =
        fibreProjection θ G.X := by
  have h' : Spec.map (CommRingCat.ofHom θ) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [h, CommRingCat.ofHom_comp, Spec.map_comp]
  let e : changeBase θ ≅ changeBase φ ⋙ changeBase ψ :=
    overPullbackCompOfEq _ _ h'
  have he : ((changeBaseGroupCompOfEq φ ψ h).hom.app G).hom.hom.left =
      (e.hom.app G.X).left := by
    change ((e.hom.app G.X) ≫ 𝟙 ((changeBase ψ).obj ((changeBase φ).obj G.X))).left = _
    exact congrArg Over.Hom.left (Category.comp_id (e.hom.app G.X))
  rw [he]
  exact overPullbackCompOfEq_projection _ _ h' G.X

private abbrev changeGroupBase {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    Grp (SchemeOverRing R) ⥤ Grp (SchemeOverRing S) :=
  (changeBase φ).mapGrp

attribute [local instance 50] integerAlgebra


private theorem comp_integerMap {m : ℕ} {k : Type u} [Field k] (φ : BaseRing.{u} m →+* k) :
    φ.comp (integerMap m) = algebraMap Integers.{u} k :=
  integerHom_unique _ _

/-- The group comparison is induced by composition of pullback squares. -/
private def integerFibreComposition {m : ℕ} {k : Type u} [Field k] (φ : BaseRing.{u} m →+* k) :
    fibre k ≅ (changeBase (integerMap m)).mapGrp ⋙ (changeBase φ).mapGrp :=
  changeBaseGroupCompOfEq (integerMap m) φ (comp_integerMap φ).symm

private theorem integerFibreComposition_projection {m : ℕ} {k : Type u} [Field k]
    (φ : BaseRing.{u} m →+* k) (G : IntegralGroup.{u}) :
    ((integerFibreComposition φ).hom.app G).hom.hom.left ≫
      fibreProjection φ ((changeBase (integerMap m)).obj G.X) ≫ fibreProjection (integerMap m) G.X =
    fibreProjection (algebraMap Integers.{u} k) G.X :=
  changeBaseGroupCompOfEq_projection (integerMap m) φ (comp_integerMap φ).symm G

end ArithmeticGeometry

section ArithmeticGeometry

open Specs.IntegralSemisimpleModel (Integers IntegralGroup integerAlgebra fibre splitTorus)
open Specs.IntegralMarkedOppositeBorel
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection)
open Specs.OrderedCechComparison (SchemeOverRing)
open Specs.Pinning (BasedRootDatum)

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

/-- Factorization of a homomorphism through a closed subgroup upgrades
a factorization of its underlying schemes. -/
private theorem groupFactor_of_schemeFactor {R : Type u} [CommRing R]
    {G H J : Grp (SchemeOverRing R)} (i : H ⟶ G) (f : J ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left)
    (r : J.X.left ⟶ H.X.left) (hr : r ≫ i.hom.hom.left = f.hom.hom.left) :
    ∃ p : J ⟶ H, p ≫ i = f := by
  let q : J.X ⟶ H.X := Over.homMk r (by rw [← Over.w i.hom.hom, ← Category.assoc, hr, Over.w])
  have hq : q ≫ i.hom.hom = f.hom.hom := Over.OverMorphism.ext hr
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have h₁ : η[J.X] ≫ q = η[H.X] := by
    apply (cancel_mono i.hom.hom).mp
    simp only [Category.assoc, hq, IsMonHom.one_hom]
  have h₂ : μ[J.X] ≫ q = (q ⊗ₘ q) ≫ μ[H.X] := by
    apply (cancel_mono i.hom.hom).mp
    rw [Category.assoc, hq, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      ← Category.assoc, tensorHom_comp_tensorHom, hq]
  refine ⟨Grp.homMk'' q h₁ h₂, Grp.hom_ext _ _ hq⟩

/-- A morphism factors through a closed immersion if its restriction along a
schematically dominant map does. -/
private theorem factorsThrough_of_schemeTheoreticallyDominant {X Y Z X' : Scheme.{u}}
    (r : X' ⟶ X) [IsSchemeTheoreticallyDominant r]
    (f : X ⟶ Y) (i : Z ⟶ Y) [IsClosedImmersion i]
    (t : X' ⟶ Z) (ht : t ≫ i = r ≫ f) : ∃ p : X ⟶ Z, p ≫ i = f := by
  have h : i.ker ≤ f.ker := by
    have he : (r ≫ f).ker = f.ker := by
      rw [Scheme.Hom.ker_comp, r.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← he, ← ht]
    exact t.le_ker_comp i
  exact ⟨IsClosedImmersion.lift i f h, IsClosedImmersion.lift_fac i f h⟩

private theorem structureFormallySmooth_iff {R S : Type u} [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S] (X : SchemeOverRing R)
    (x : ((changeBase (algebraMap R S)).obj X).left) :
    (X.hom.stalkMap (fibreProjection (algebraMap R S) X x)).hom.FormallySmooth ↔
      (((changeBase (algebraMap R S)).obj X).hom.stalkMap x).hom.FormallySmooth := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R S))
  letI : IsPreimmersion b := IsPreimmersion.of_isLocalization M (S := S)
  letI : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S M))
  letI := isIso_stalkMap_fibreProjection M X x
  letI := isIso_stalkMap_of_flat_of_surjectiveOnStalks b (((changeBase (algebraMap R S)).obj X).hom x)
  let e := stalkMapIso_of_square
    (Specs.ArithmeticCohomologyBaseChange.fibreProjection_over (algebraMap R S) X) x
  exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff e

attribute [local instance 50] integerAlgebra

open private integers_isFractionRing from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

/-- A finite presentation over the integers that is generically smooth
becomes smooth after inverting one positive integer. -/
private theorem exists_smooth_integerRestriction (X : SchemeOverRing Integers.{u})
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [TopologicalSpace.NoetherianSpace X.left]
    (hX : Smooth ((changeBase (algebraMap Integers.{u} Specs.RationalRealization.RationalField.{u})).obj
      X).hom) :
    ∃ m : ℕ, m ≠ 0 ∧ Smooth ((changeBase (integerMap m)).obj X).hom := by
  let R := Integers.{u}
  let K := Specs.RationalRealization.RationalField.{u}
  letI : IsDomain R := (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  letI : Algebra R K := integerAlgebra K
  letI : IsFractionRing R K := integers_isFractionRing
  let Z := (X.hom.smoothLocus : Set X.left)ᶜ
  have hZ : IsConstructible Z := isConstructible_compl.mpr
    ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible X.hom.smoothLocus.2)
  have avoids (x : X.left) (hx : x ∈ Z) : X.hom x ≠ (⊥ : PrimeSpectrum R) := by
    intro h
    have hm : x ∈ Set.range (fibreProjection (algebraMap R K) X) := by
      change x ∈ Set.range (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, h]
      exact genericPoint_mem_range R K
    obtain ⟨y, rfl⟩ := hm
    apply hx
    apply (structureFormallySmooth_iff (nonZeroDivisors R) X y).mpr
    letI := hX
    change y ∈ ((changeBase (algebraMap R K)).obj X).hom.smoothLocus
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  obtain ⟨a, ha, h⟩ := exists_principal_open_avoiding X.hom hZ avoids
  let m := a.down.natAbs
  have hm : m ≠ 0 := by
    intro e
    apply ha
    apply ULift.ext
    exact Int.natAbs_eq_zero.mp e
  have hAssoc : Associated a (m : R) :=
    (Int.associated_natAbs a.down).map (ULift.ringEquiv : R ≃+* ℤ).symm.toMonoidHom
  letI : IsLocalization.Away a (BaseRing.{u} m) := IsLocalization.Away.of_associated hAssoc.symm
  let φ := integerMap.{u} m
  let Y := (changeBase φ).obj X
  letI : LocallyOfFinitePresentation Y.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ))))
  refine ⟨m, hm, Scheme.Hom.smoothLocus_eq_top_iff.mp ?_⟩
  apply top_le_iff.mp
  intro x _
  apply (structureFormallySmooth_iff (S := BaseRing.{u} m) (Submonoid.powers a) X x).mp
  by_contra hn
  apply Set.disjoint_left.mp h hn
  have hr : Set.range (fibreProjection φ X) =
      Set.range (fibreProjection (algebraMap R (Localization.Away a)) X) := by
    change Set.range (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) =
      Set.range (pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a)))))
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
    congr 1
    exact (PrimeSpectrum.localization_away_comap_range (BaseRing.{u} m) a).trans
      (PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).symm
  exact hr ▸ Set.mem_range_self x

end ArithmeticGeometry

section CharacterSections

open Specs.IntegralSemisimpleModel (Integers IntegralPoints TorusValues splitTorus torusPoint)
open Specs.Pinning (BasedRootDatum)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection)
open Specs.OrderedCechComparison (SchemeOverRing)

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

private theorem specMap_appTop_coordinate {R S : CommRingCat.{u}} (f : R ⟶ S) (a : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv a) = (Scheme.ΓSpecIso S).inv (f a) :=
  congrArg (fun g : R ⟶ Γ(Spec S, ⊤) => g a) (Scheme.ΓSpecIso_inv_naturality f).symm

private def IsMultiplicativeSection {R : Type u} [CommRing R]
    (G : Grp (SchemeOverRing R)) (c : Γ(G.X.left, ⊤)) : Prop :=
  μ[G.X].left.appTop c = (fst G.X G.X).left.appTop c * (snd G.X G.X).left.appTop c

private theorem isMultiplicativeSection_pullback {R S : Type u} [CommRing R] [CommRing S]
    {G : Grp (SchemeOverRing R)} {H : Grp (SchemeOverRing S)}
    (q : H.X.left ⟶ G.X.left) (q₂ : (H.X ⊗ H.X).left ⟶ (G.X ⊗ G.X).left)
    (hμ : μ[H.X].left ≫ q = q₂ ≫ μ[G.X].left)
    (h₁ : (fst H.X H.X).left ≫ q = q₂ ≫ (fst G.X G.X).left)
    (h₂ : (snd H.X H.X).left ≫ q = q₂ ≫ (snd G.X G.X).left)
    {c : Γ(G.X.left, ⊤)} (hc : IsMultiplicativeSection G c) :
    IsMultiplicativeSection H (q.appTop c) := by
  unfold IsMultiplicativeSection at hc ⊢
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hμ, h₁, h₂]
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_mul] using
    congrArg (fun a => q₂.appTop a) hc

private theorem isMultiplicativeSection_comp {R : Type u} [CommRing R]
    {G H : Grp (SchemeOverRing R)} (q : H ⟶ G)
    {c : Γ(G.X.left, ⊤)} (hc : IsMultiplicativeSection G c) :
    IsMultiplicativeSection H (q.hom.hom.left.appTop c) := by
  let f := q.hom.hom
  refine isMultiplicativeSection_pullback f.left (f ⊗ₘ f).left ?_ ?_ ?_ hc
  · exact congrArg Over.Hom.left (IsMonHom.mul_hom (f := f))
  · exact congrArg Over.Hom.left (tensorHom_fst f f).symm
  · exact congrArg Over.Hom.left (tensorHom_snd f f).symm

private theorem isMultiplicativeSection_changeBase {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (G : Grp (SchemeOverRing R)) {c : Γ(G.X.left, ⊤)}
    (hc : IsMultiplicativeSection G c) :
    IsMultiplicativeSection ((changeBase φ).mapGrp.obj G) ((fibreProjection φ G.X).appTop c) := by
  let F := changeBase φ
  let a := Functor.LaxMonoidal.μ F G.X G.X
  let q₂ := a.left ≫ fibreProjection φ (G.X ⊗ G.X)
  have cube {Y : SchemeOverRing R} (f : G.X ⊗ G.X ⟶ Y) :
      (a ≫ F.map f).left ≫ fibreProjection φ Y = q₂ ≫ f.left := by
    have h := (changeBaseMap_isPullback φ f).w
    change (F.map f).left ≫ fibreProjection φ Y = fibreProjection φ (G.X ⊗ G.X) ≫ f.left at h
    simp only [Over.comp_left, Category.assoc, h, q₂]
  refine isMultiplicativeSection_pullback (G := G) (H := F.mapGrp.obj G)
    (fibreProjection φ G.X) q₂ ?_ ?_ ?_ hc
  · exact cube μ[G.X]
  · change (fst (F.obj G.X) (F.obj G.X)).left ≫ _ = _
    rw [← Functor.Monoidal.μ_fst (F := F) G.X G.X]
    exact cube (fst G.X G.X)
  · change (snd (F.obj G.X) (F.obj G.X)).left ≫ _ = _
    rw [← Functor.Monoidal.μ_snd (F := F) G.X G.X]
    exact cube (snd G.X G.X)

private theorem groupLikeSection_multiplicative {R A : Type u} [CommRing R] [CommRing A]
    [HopfAlgebra R A] {a : A} (ha : IsGroupLikeElem R a) :
    IsMultiplicativeSection
      ((hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R A)))
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := by
  unfold IsMultiplicativeSection
  let f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  change (μ[(Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))].left).appTop _ =
    (pullback.fst f f).appTop _ * (pullback.snd f f).appTop _
  rw [mul_spec_asOver_spec_left, ← pullbackSpecIso_hom_fst R A A, ← pullbackSpecIso_hom_snd R A A]
  let P := pullbackSpecIso R A A
  let C := CommRingCat.of A
  let E := CommRingCat.of (A ⊗[R] A)
  let Δ : C ⟶ E := CommRingCat.ofHom (Bialgebra.comulAlgHom R A).toRingHom
  let l : C ⟶ E := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let r : C ⟶ E := CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
  let z := (Scheme.ΓSpecIso C).inv a
  have coord (e : C ⟶ E) : (P.hom ≫ Spec.map e).appTop z =
      P.hom.appTop ((Scheme.ΓSpecIso E).inv (e a)) := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact congrArg (fun x => P.hom.appTop x) (specMap_appTop_coordinate e a)
  change (P.hom ≫ Spec.map Δ).appTop z = (P.hom ≫ Spec.map l).appTop z * (P.hom ≫ Spec.map r).appTop z
  rw [coord Δ, coord l, coord r, ← map_mul, ← map_mul]
  apply congrArg (fun x : E => P.hom.appTop ((Scheme.ΓSpecIso E).inv x))
  change Coalgebra.comul (R := R) a = (a ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] a)
  rw [ha.comul_eq_tmul_self, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private def torusMonomial (D : BasedRootDatum.{u}) (w : D.X) :
    Γ((splitTorus D).X.left, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (MonoidAlgebra Integers.{u}
    (Multiplicative D.X)))).inv.hom.toMonoidHom
    ((MonoidAlgebra.of Integers.{u} (Multiplicative D.X)).toHomUnits (Multiplicative.ofAdd w))

private theorem torusMonomial_val (D : BasedRootDatum.{u}) (w : D.X) :
    (torusMonomial D w : Γ((splitTorus D).X.left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of (MonoidAlgebra Integers.{u}
        (Multiplicative D.X)))).inv (MonoidAlgebra.single (Multiplicative.ofAdd w) 1) := rfl

private theorem torusMonomial_multiplicative (D : BasedRootDatum.{u}) (w : D.X) :
    IsMultiplicativeSection (splitTorus D) (torusMonomial D w) := by
  rw [torusMonomial_val]
  exact groupLikeSection_multiplicative (MonoidAlgebra.isGroupLikeElem_single_one _)

open private torusEvaluation_single from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private theorem torusMonomial_apply (D : BasedRootDatum.{u}) (w : D.X)
    (R : Specs.IntegralSemisimpleModel.IntegralAlgebra.{u}) (v : TorusValues D R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      ((torusPoint D R v).left.appTop (torusMonomial D w)) = (v (Multiplicative.ofAdd w) : R) := by
  rw [torusMonomial_val]
  let g := MonoidAlgebra.lift Integers.{u} R (Multiplicative D.X) ((Units.coeHom R).comp v)
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    ((Spec.map (CommRingCat.ofHom g.toRingHom)).appTop
      ((Scheme.ΓSpecIso _).inv (MonoidAlgebra.single (Multiplicative.ofAdd w) 1))) = _
  rw [specMap_appTop_coordinate, ← CommRingCat.comp_apply, Iso.inv_hom_id]
  change g (MonoidAlgebra.single (Multiplicative.ofAdd w) 1) = _
  letI : Algebra Integers.{u} R := CommAlgCat.instAlgebraObjForgetAlgHomCarrier
  exact torusEvaluation_single (k := Integers.{u}) v (Multiplicative.ofAdd w)

private theorem torusMonomial_inv_apply (D : BasedRootDatum.{u}) (w : D.X)
    (R : Specs.IntegralSemisimpleModel.IntegralAlgebra.{u}) (v : TorusValues D R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      ((torusPoint D R v).left.appTop (↑((torusMonomial D w)⁻¹) :
        Γ((splitTorus D).X.left, ⊤))) = ((v⁻¹) (Multiplicative.ofAdd w) : R) := by
  let f := Units.map (((torusPoint D R v).left.appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toMonoidHom)
  have h : f (torusMonomial D w) = v (Multiplicative.ofAdd w) :=
    Units.ext (torusMonomial_apply D w R v)
  exact congrArg Units.val ((map_inv f (torusMonomial D w)).trans (congrArg Inv.inv h))

open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralSemisimpleModel (fibre forgetFibrePoint integerAlgebra)
open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator groupAlgebra)

attribute [local instance 50] integerAlgebra

open private fibrePointsEquiv restrictToIntegers affineTorusPointEquiv affineTorusPointEquiv_apply
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private theorem characterValue_eq_appTop {k : Type u} [Field k] {T : Specs.GroupScheme k}
    (χ : Character T) (R : TestAlgebra k) (p : GroupPoints T R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      ((p ≫ χ.hom.hom).left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (groupAlgebra k IntegerCharacters))).inv
          (MonoidAlgebra.single integerGenerator (1 : k)))) = characterValue χ R p := by
  let E := algSpec.fullyFaithful (R := CommRingCat.of k)
  let L := groupAlgebra k IntegerCharacters
  let j := p ≫ χ.hom.hom
  let f : CommAlgCat.of k L ⟶ R := (E.preimage j).unop
  let f' : CommRingCat.of L ⟶ CommRingCat.of R := CommRingCat.ofHom f.hom.toRingHom
  let z : L := MonoidAlgebra.single integerGenerator 1
  have h : Spec.map f' = j.left := congrArg Over.Hom.left (E.map_preimage j)
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    (j.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv z)) = f.hom z
  rw [← h]
  have ev := specMap_appTop_coordinate f' z
  exact (congrArg (fun x => (Scheme.ΓSpecIso (CommRingCat.of R)).hom x) ev).trans (by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl)

/-- Evaluation on affine test algebras identifies the inverse of an integral
weight coordinate with the inverse of the marked field character. -/
private theorem inverseWeightCoordinate {k : Type u} [Field k] (D : BasedRootDatum.{u})
    {T B : Specs.GroupScheme k} [IsAffine B.X.left]
    (t : (fibre k).obj (splitTorus D) ≅ T) (p : B ⟶ T) (w : D.X) (χ : Character T)
    (hχ : ∀ (R : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) R)
      (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
      forgetFibrePoint (splitTorus D) R s = torusPoint D _ v →
      characterValue χ R (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd w) : R)) :
    let a := (p ≫ t.inv).hom.hom.left ≫ fibreProjection (algebraMap Integers.{u} k) (splitTorus D).X
    let r := (𝟙 B.X)⁻¹ ≫ (p ≫ χ).hom.hom
    a.appTop (↑((torusMonomial D w)⁻¹) : Γ((splitTorus D).X.left, ⊤)) =
      ((Scheme.ΓSpecIso (CommRingCat.of (groupAlgebra k IntegerCharacters))).inv ≫ r.left.appTop)
        (MonoidAlgebra.single integerGenerator (1 : k)) := by
  let a := (p ≫ t.inv).hom.hom.left ≫ fibreProjection (algebraMap Integers.{u} k) (splitTorus D).X
  let r := (𝟙 B.X)⁻¹ ≫ (p ≫ χ).hom.hom
  obtain ⟨S, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (show IsAffine B.X.left from inferInstance)
  let R : TestAlgebra k := S.unop
  let q : GroupPoints B R := e.hom
  haveI : IsIso q.left := (Over.forget _).map_isIso e.hom
  haveI : IsIso q.left.appTop := by
    rw [← Scheme.Γ_map_op]
    infer_instance
  apply (ConcreteCategory.bijective_of_isIso q.left.appTop).1
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  let s : GroupPoints ((fibre k).obj (splitTorus D)) R := q ≫ (p ≫ t.inv).hom.hom
  let eT := affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X)
    ((restrictToIntegers k).obj R)
  obtain ⟨v, hv⟩ := eT.surjective (forgetFibrePoint (splitTorus D) R s)
  have hv₀ : forgetFibrePoint (splitTorus D) R s =
      torusPoint D (CommAlgCat.of Integers.{u} R) v := hv.symm
  have hv₁ : forgetFibrePoint (splitTorus D) R s⁻¹ = torusPoint D _ (v⁻¹) := by
    change (fibrePointsEquiv (splitTorus D) R) s⁻¹ = eT (v⁻¹)
    change eT v = (fibrePointsEquiv (splitTorus D) R) s at hv
    rw [map_inv, ← hv]
    exact (map_inv eT v).symm
  have hs : s ≫ t.hom.hom.hom = q ≫ p.hom.hom := by
    change (q ≫ (p ≫ t.inv).hom.hom) ≫ t.hom.hom.hom = _
    simp only [Category.assoc, Grp.comp_hom_hom, ← Grp.comp_hom_hom t.inv t.hom,
      t.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hsInv : s⁻¹ ≫ t.hom.hom.hom = q⁻¹ ≫ p.hom.hom := by
    calc
      s⁻¹ ≫ t.hom.hom.hom = (s ≫ t.hom.hom.hom : GroupPoints T R)⁻¹ :=
        GrpObj.inv_comp s t.hom.hom.hom
      _ = (q ≫ p.hom.hom : GroupPoints T R)⁻¹ := congrArg Inv.inv hs
      _ = _ := (GrpObj.inv_comp q p.hom.hom).symm
  have hValue := hχ R s⁻¹ (v⁻¹) hv₁
  rw [hsInv] at hValue
  have ha : q.left ≫ a = (forgetFibrePoint (splitTorus D) R s).left := by
    change q.left ≫ (p ≫ t.inv).hom.hom.left ≫ _ =
      (q ≫ (p ≫ t.inv).hom.hom).left ≫ _
    rw [Over.comp_left, Category.assoc]
  have hr : q.left ≫ r.left = (q⁻¹ ≫ (p ≫ χ).hom.hom).left := by
    rw [← Over.comp_left]
    apply congrArg Over.Hom.left
    change q ≫ (𝟙 B.X)⁻¹ ≫ (p ≫ χ).hom.hom = _
    rw [← Category.assoc, GrpObj.comp_inv, Category.comp_id]
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    (q.left.appTop (a.appTop (↑((torusMonomial D w)⁻¹) : Γ((splitTorus D).X.left, ⊤)))) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (q.left.appTop (r.left.appTop ((Scheme.ΓSpecIso _).inv (MonoidAlgebra.single _ (1 : k)))))
  rw [← CommRingCat.comp_apply a.appTop, ← Scheme.Hom.comp_appTop, ha, hv₀,
    ← CommRingCat.comp_apply r.left.appTop, ← Scheme.Hom.comp_appTop, hr]
  have hRight : characterValue (p ≫ χ) R q⁻¹ = characterValue χ R (q⁻¹ ≫ p.hom.hom) := by
    unfold characterValue
    rw [Grp.comp_hom_hom, Category.assoc]
  exact (torusMonomial_inv_apply D w (CommAlgCat.of Integers.{u} R) v).trans
    ((characterValue_eq_appTop (p ≫ χ) R q⁻¹).trans (hRight.trans hValue)).symm

end CharacterSections

section RelativeConstruction

open Specs.IntegralSemisimpleModel (Integers IntegralGroup Model integerAlgebra fibre splitTorus)
open Specs.IntegralMarkedOppositeBorel
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection rationalMap)
open Specs.OrderedCechComparison (SchemeOverRing)
open Specs.RationalRealization (RationalField)
open Specs.Pinning (BasedRootDatum)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 420000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance 50] integerAlgebra

open private kBorel_smooth_connected from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private integers_isPrincipalIdealRing integers_isFractionRing
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private abbrev IntegralBorelFibre.pair {D : BasedRootDatum.{u}} {I : Model D}
    {J : IntegralGroup.{u}} {i l : J ⟶ I.group} {k : Type u} [Field k]
    (F : IntegralBorelFibre I J i l k) :
    Specs.FlagLineBundle.OppositeBorelPair F.realization.pinned.pair.G :=
  ⟨F.realization.pinned.pair.T, F.realization.pinned.pair.B, F.negative,
    F.realization.pinned.pair.reductive, F.realization.pinned.pair.split,
    F.realization.pinned.pair.maximal, F.realization.pinned.pair.borel, F.negativeBorel,
    F.realization.pinned.pair.containsTorus, F.inNegative, F.opposite⟩

private abbrev arithmeticFibreMap {m : ℕ} (hm : m ≠ 0) : BaseRing.{u} m →+* RationalField.{u} :=
  rationalMap (m := (m : ℤ)) (Nat.cast_ne_zero.mpr hm)

private theorem genericProjection_isSchemeTheoreticallyDominant
    {m : ℕ} (hm : m ≠ 0) (X : SchemeOverRing (BaseRing.{u} m)) [Flat X.hom] :
    IsSchemeTheoreticallyDominant (fibreProjection (arithmeticFibreMap hm) X) := by
  let A := BaseRing.{u} m
  let K := RationalField.{u}
  let φ := arithmeticFibreMap.{u} hm
  letI : Algebra Integers.{u} K := integerAlgebra K
  letI : IsDomain Integers.{u} := (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  letI : IsFractionRing Integers.{u} K := integers_isFractionRing
  letI : Algebra A K := φ.toAlgebra
  letI : @IsScalarTower Integers.{u} A K Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq'
    (integerHom_unique _ _)
  letI : IsDomain A := Localization.Away.isDomain
    (show (m : Integers.{u}) ≠ 0 by
      intro h
      exact hm (Int.ofNat_eq_zero.mp (congrArg ULift.down h)))
  letI : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (m : Integers.{u})) A K
  let b := Spec.map (CommRingCat.ofHom φ)
  haveI : IsDominant b := by
    refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr ?_⟩
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp (IsFractionRing.injective A K)]
    exact bot_le
  haveI : IsSchemeTheoreticallyDominant b := IsSchemeTheoreticallyDominant.of_isDominant b
  haveI : QuasiCompact b := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom φ)))
  change IsSchemeTheoreticallyDominant (pullback.fst X.hom b)
  infer_instance

private theorem relativeSmoothness {D : BasedRootDatum.{u}} {I : Model D}
    {J : IntegralGroup.{u}} {i l : J ⟶ I.group}
    (hi : IsClosedImmersion i.hom.hom.left) (F : IntegralBorelFibre I J i l RationalField.{u}) :
    ∃ m : ℕ, m ≠ 0 ∧ Smooth ((changeBase (integerMap m)).obj J.X).hom := by
  let K := RationalField.{u}
  letI : LocallyOfFinitePresentation I.group.X.hom := I.locallyOfFinitePresentation
  letI : IsAffine I.group.X.left := I.affine
  letI : IsClosedImmersion i.hom.hom.left := hi
  letI : IsAffine J.X.left := isAffine_of_isAffineHom i.hom.hom.left
  letI : LocallyOfFiniteType J.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  letI : IsPrincipalIdealRing Integers.{u} := integers_isPrincipalIdealRing
  letI : IsLocallyNoetherian J.X.left := LocallyOfFiniteType.isLocallyNoetherian J.X.hom
  letI : IsNoetherian J.X.left := AlgebraicGeometry.IsNoetherian.mk
  let q := F.borelIso.hom.hom.hom
  haveI : IsIso q.left := (Grp.forget _ ⋙ Over.forget _).map_isIso F.borelIso.hom
  haveI : Smooth F.negative.group.X.hom :=
    (kBorel_smooth_connected _ _ F.negativeBorel).1
  apply exists_smooth_integerRestriction J.X
  change Smooth ((fibre K).obj J).X.hom
  rw [← Over.w q]
  infer_instance

private theorem integerFibreLimitFactors {D : BasedRootDatum.{u}} {I : Model D}
    {J : IntegralGroup.{u}} {i l : J ⟶ I.group} {k : Type u} [Field k]
    (F : IntegralBorelFibre I J i l k) :
    (F.borelIso.hom ≫ F.projection.projection ≫ F.torusIso.inv) ≫ (fibre k).map I.torus =
      (fibre k).map l := by
  apply (cancel_mono F.integralIso.hom).mp
  simp only [Category.assoc, F.torus_marking, Iso.inv_hom_id_assoc, F.limit_eq]

private theorem fibreFactorization {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {X Y Z : SchemeOverRing R}
    (i : Z ⟶ Y) (l : X ⟶ Y) [IsClosedImmersion i.left]
    [IsSchemeTheoreticallyDominant (fibreProjection φ X)]
    (g : (changeBase φ).obj X ⟶ (changeBase φ).obj Z)
    (hg : g ≫ (changeBase φ).map i = (changeBase φ).map l) :
    ∃ r : X.left ⟶ Z.left, r ≫ i.left = l.left := by
  apply factorsThrough_of_schemeTheoreticallyDominant (fibreProjection φ X) l.left i.left
    (g.left ≫ fibreProjection φ Z)
  rw [Category.assoc, ← (changeBaseMap_isPullback φ i).w, ← Category.assoc, ← Over.comp_left, hg]
  exact (changeBaseMap_isPullback φ l).w

/-- Smoothness makes the generic restriction schematically dominant, so the
generic factorization of evaluation through the marked torus descends. -/
private theorem relativeLimitFactors {D : BasedRootDatum.{u}} {I : Model D}
    {J : IntegralGroup.{u}} {i l : J ⟶ I.group}
    (F : IntegralBorelFibre I J i l RationalField.{u})
    {m : ℕ} (hm : m ≠ 0) (hJ : Smooth ((changeBase (integerMap m)).obj J.X).hom) :
    ∃ p : (changeGroupBase (integerMap m)).obj J ⟶
        (changeGroupBase (integerMap m)).obj (splitTorus D),
      p ≫ (changeGroupBase (integerMap m)).map I.torus =
        (changeGroupBase (integerMap m)).map l := by
  let φ := arithmeticFibreMap.{u} hm
  let C := (changeGroupBase (integerMap m))
  let C' := (changeGroupBase φ)
  let e := integerFibreComposition φ
  let q := F.borelIso.hom ≫ F.projection.projection ≫ F.torusIso.inv
  let q' := e.inv.app J ≫ q ≫ e.hom.app (splitTorus D)
  have he (f : J ⟶ I.group) :
      (fibre RationalField.{u}).map f ≫ e.hom.app I.group = e.hom.app J ≫ C'.map (C.map f) :=
    e.hom.naturality f
  have ht : e.hom.app (splitTorus D) ≫ C'.map (C.map I.torus) =
      (fibre RationalField.{u}).map I.torus ≫ e.hom.app I.group :=
    (e.hom.naturality I.torus).symm
  have hq₀ : q ≫ (fibre RationalField.{u}).map I.torus = (fibre RationalField.{u}).map l :=
    integerFibreLimitFactors F
  have hq : q' ≫ C'.map (C.map I.torus) = C'.map (C.map l) := by
    unfold q'
    rw [Category.assoc, Category.assoc, ht, ← Category.assoc q, hq₀, he, ← Category.assoc,
      Iso.inv_hom_id_app, Category.id_comp]
  have hc : IsClosedImmersion (C.map I.torus).hom.hom.left :=
    MorphismProperty.of_isPullback
      (changeBaseMap_isPullback (integerMap m) I.torus.hom.hom).flip I.torusClosed
  letI : Smooth (C.obj J).X.hom := hJ
  haveI : Flat (C.obj J).X.hom := inferInstance
  haveI := genericProjection_isSchemeTheoreticallyDominant hm (C.obj J).X
  have hc' : q'.hom.hom ≫ (changeBase φ).map (C.map I.torus).hom.hom =
      (changeBase φ).map (C.map l).hom.hom := congrArg (fun a => a.hom.hom) hq
  letI := hc
  obtain ⟨r, hr⟩ := fibreFactorization φ (C.map I.torus).hom.hom (C.map l).hom.hom
    q'.hom.hom hc'
  exact groupFactor_of_schemeFactor (C.map I.torus) (C.map l) hc r hr

end RelativeConstruction

section Assembly

open Specs.IntegralSemisimpleModel (Integers IntegralGroup Model integerAlgebra fibre splitTorus)
open Specs.IntegralMarkedOppositeBorel
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection)
open Specs.CharacterDescent (Character)
open Specs.Pinning (BasedRootDatum)

attribute [local instance 50] integerAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000
set_option synthInstance.maxHeartbeats 100000

private def arithmeticFibreIso {m : ℕ} {k : Type u} [Field k] (φ : BaseRing.{u} m →+* k)
    {Q : IntegralGroup.{u}} {G : Specs.GroupScheme k} (e : (fibre k).obj Q ≅ G) :
    ((changeGroupBase (integerMap m)) ⋙ (changeGroupBase φ)).obj Q ≅ G :=
  ((integerFibreComposition φ).app Q).symm ≪≫ e

private theorem arithmeticFibreIso_projection {m : ℕ} {k : Type u} [Field k]
    (φ : BaseRing.{u} m →+* k) {Q : IntegralGroup.{u}} {G : Specs.GroupScheme k}
    (e : (fibre k).obj Q ≅ G) :
    (arithmeticFibreIso φ e).inv.hom.hom.left ≫
      fibreProjection φ ((changeBase (integerMap m)).obj Q.X) ≫
        fibreProjection (integerMap m) Q.X =
      e.inv.hom.hom.left ≫ fibreProjection (algebraMap Integers.{u} k) Q.X := by
  change (e.inv ≫ (integerFibreComposition φ).hom.app Q).hom.hom.left ≫ _ = _
  rw [Grp.comp_hom_hom, Over.comp_left, Category.assoc, integerFibreComposition_projection φ Q]

private theorem arithmeticInclusion {D : BasedRootDatum.{u}} {I : Model D}
    {m : ℕ} {k : Type u} [Field k] (φ : BaseRing.{u} m →+* k)
    {J : IntegralGroup.{u}} {i l : J ⟶ I.group} (F : IntegralBorelFibre I J i l k) :
    (changeGroupBase φ).map ((changeGroupBase (integerMap m)).map i) ≫
      (arithmeticFibreIso φ F.integralIso).hom =
      (arithmeticFibreIso φ F.borelIso).hom ≫ F.negative.inclusion := by
  let e := integerFibreComposition φ
  have hn : (changeGroupBase φ).map ((changeGroupBase (integerMap m)).map i) ≫ e.inv.app I.group =
    e.inv.app J ≫ (fibre k).map i := e.inv.naturality i
  change (changeGroupBase φ).map ((changeGroupBase (integerMap m)).map i) ≫
      (e.inv.app I.group ≫ F.integralIso.hom) =
      (e.inv.app J ≫ F.borelIso.hom) ≫ F.negative.inclusion
  rw [← Category.assoc, hn, Category.assoc, F.inclusion_eq, ← Category.assoc]

private theorem mapMarkedTorus_closed {D : BasedRootDatum.{u}} (I : Model D)
    {S : Type u} [CommRing S] (φ : Integers.{u} →+* S) :
    IsClosedImmersion ((changeGroupBase φ).map I.torus).hom.hom.left :=
  MorphismProperty.of_isPullback (changeBaseMap_isPullback φ I.torus.hom.hom).flip I.torusClosed

private theorem relativeProjection_comparison {D : BasedRootDatum.{u}} {I : Model D}
    {m : ℕ} {k : Type u} [Field k] (φ : BaseRing.{u} m →+* k)
    {J : IntegralGroup.{u}} {i l : J ⟶ I.group} (F : IntegralBorelFibre I J i l k)
    (p : (changeGroupBase (integerMap m)).obj J ⟶
        (changeGroupBase (integerMap m)).obj (splitTorus D))
    (hp : p ≫ (changeGroupBase (integerMap m)).map I.torus =
        (changeGroupBase (integerMap m)).map l) :
    let b := arithmeticFibreIso φ F.borelIso
    b.inv.hom.hom.left ≫ fibreProjection φ ((changeBase (integerMap m)).obj J.X) ≫
        p.hom.hom.left ≫ fibreProjection (integerMap m) (splitTorus D).X =
      (F.projection.projection ≫ F.torusIso.inv).hom.hom.left ≫
        fibreProjection (algebraMap Integers.{u} k) (splitTorus D).X := by
  let C := (changeGroupBase (integerMap m))
  let C' := (changeGroupBase φ)
  let e := integerFibreComposition φ
  let b := arithmeticFibreIso φ F.borelIso
  let t := splitTorus D
  let f := (fibre k).map I.torus
  let r := F.projection.projection ≫ F.torusIso.inv
  haveI : IsClosedImmersion f.hom.hom.left := mapMarkedTorus_closed I (algebraMap Integers.{u} k)
  have hmono : Mono f.hom.hom := Over.mono_of_mono_left _
  haveI : Mono f := (Grp.forget _).mono_of_mono_map (f := f) hmono
  have hnT : e.inv.app t ≫ f = C'.map (C.map I.torus) ≫ e.inv.app I.group :=
    (e.inv.naturality I.torus).symm
  have hnJ : C'.map (C.map l) ≫ e.inv.app I.group = e.inv.app J ≫ (fibre k).map l :=
    e.inv.naturality l
  have h : b.inv ≫ C'.map p ≫ e.inv.app t = r := by
    apply (cancel_mono f).mp
    calc
      (b.inv ≫ C'.map p ≫ e.inv.app t) ≫ f =
          b.inv ≫ C'.map p ≫ C'.map (C.map I.torus) ≫ e.inv.app I.group := by
        simp only [Category.assoc, hnT]
      _ = b.inv ≫ C'.map (C.map l) ≫ e.inv.app I.group := by
        rw [← Category.assoc (C'.map p), ← C'.map_comp, hp]
      _ = F.borelIso.inv ≫ (fibre k).map l := by
        rw [hnJ]
        change (F.borelIso.inv ≫ e.hom.app J) ≫ e.inv.app J ≫ (fibre k).map l = _
        rw [Category.assoc, ← Category.assoc (e.hom.app J), Iso.hom_inv_id_app, Category.id_comp]
      _ = r ≫ f := by
        rw [← integerFibreLimitFactors F]
        simp only [r, f, Category.assoc, Iso.inv_hom_id_assoc]
  have h' : b.inv ≫ C'.map p = r ≫ e.hom.app t := calc
    _ = (b.inv ≫ C'.map p) ≫ 𝟙 (C'.obj (C.obj t)) :=
      (Category.comp_id (b.inv ≫ C'.map p)).symm
    _ = (b.inv ≫ C'.map p ≫ e.inv.app t) ≫ e.hom.app t := by
      have ht : e.inv.app t ≫ e.hom.app t = 𝟙 (C'.obj (C.obj t)) := Iso.inv_hom_id_app e t
      rw [← ht]
      simp only [Category.assoc]
    _ = _ := congrArg (· ≫ e.hom.app t) h
  have hs : b.inv.hom.hom.left ≫ (C'.map p).hom.hom.left =
      r.hom.hom.left ≫ (e.hom.app t).hom.hom.left :=
    congrArg (fun g => g.hom.hom.left) h'
  change b.inv.hom.hom.left ≫ fibreProjection φ (C.obj J).X ≫ p.hom.hom.left ≫
      fibreProjection (integerMap m) t.X = r.hom.hom.left ≫ _
  have hn : (C'.map p).hom.hom.left ≫ fibreProjection φ (C.obj t).X =
      fibreProjection φ (C.obj J).X ≫ p.hom.hom.left :=
    (changeBaseMap_isPullback φ p.hom.hom).w
  calc
    _ = (b.inv.hom.hom.left ≫ (C'.map p).hom.hom.left) ≫
        fibreProjection φ (C.obj t).X ≫ fibreProjection (integerMap m) t.X := by
      simpa only [Category.assoc] using
        congrArg (fun a => b.inv.hom.hom.left ≫ a ≫ fibreProjection (integerMap m) t.X) hn.symm
    _ = _ := by
      rw [hs, Category.assoc]
      exact congrArg (r.hom.hom.left ≫ ·) (integerFibreComposition_projection φ t)

private def relativeBorel {D : BasedRootDatum.{u}} {I : Model D}
    {m : ℕ} {J : IntegralGroup.{u}} (i : J ⟶ I.group)
    (hi : IsClosedImmersion i.hom.hom.left)
    (hJ : Smooth ((changeBase (integerMap m)).obj J.X).hom) (w : D.X)
    (p : (changeGroupBase (integerMap m)).obj J ⟶
        (changeGroupBase (integerMap m)).obj (splitTorus D)) : RelativeBorel I m := by
  let C := (changeGroupBase (integerMap m))
  letI : IsAffine I.group.X.left := I.affine
  letI : IsClosedImmersion (C.map i).hom.hom.left :=
    MorphismProperty.of_isPullback (changeBaseMap_isPullback (integerMap m) i.hom.hom).flip hi
  letI : IsAffine (C.obj I.group).X.left := inferInstanceAs
    (IsAffine (pullback I.group.X.hom (Spec.map (CommRingCat.ofHom (integerMap m)))))
  let q := p.hom.hom.left ≫ fibreProjection (integerMap m) (splitTorus D).X
  refine
    { borel := C.obj J
      inclusion := C.map i
      closed := inferInstance
      smooth := hJ
      affine := isAffine_of_isAffineHom (C.map i).hom.hom.left
      character := Units.map q.appTop.hom.toMonoidHom (torusMonomial D w)
      characterMultiplicative := ?_ }
  have h := isMultiplicativeSection_comp p (isMultiplicativeSection_changeBase (integerMap m)
    (splitTorus D) (torusMonomial_multiplicative D w))
  change IsMultiplicativeSection (C.obj J) (q.appTop (torusMonomial D w))
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact h

private theorem compareRelativeBorel {D : BasedRootDatum.{u}} {I : Model D}
    {m : ℕ} {J : IntegralGroup.{u}} {i l : J ⟶ I.group} (hi : IsClosedImmersion i.hom.hom.left)
    (hJ : Smooth ((changeBase (integerMap m)).obj J.X).hom) (w : D.X)
    (p : (changeGroupBase (integerMap m)).obj J ⟶
        (changeGroupBase (integerMap m)).obj (splitTorus D))
    (hp : p ≫ (changeGroupBase (integerMap m)).map I.torus =
        (changeGroupBase (integerMap m)).map l)
    {k : Type u} [Field k] (φ : BaseRing.{u} m →+* k) (F : IntegralBorelFibre I J i l k) :
    Nonempty (FieldComparison I φ w (relativeBorel i hi hJ w p)) := by
  refine ⟨{
    additive := F.additive
    realization := F.realization
    pair := F.pair
    torus_eq := rfl
    positive_eq := rfl
    projection := F.projection
    integralIso := F.integralIso
    torusIso := F.torusIso
    torus_marking := F.torus_marking
    rootCoordinate := F.rootCoordinate
    simple_marking := F.simple_marking
    root_marking := F.root_marking
    weight_marking := F.weight_marking
    groupIso := arithmeticFibreIso φ F.integralIso
    group_composition := arithmeticFibreIso_projection φ F.integralIso
    borelIso := arithmeticFibreIso φ F.borelIso
    inclusion_eq := arithmeticInclusion φ F
    character_eq := ?_ }⟩
  letI : IsAffine F.realization.pinned.pair.G.val.X.left := F.realization.pinned.pair.G.property.1
  letI : IsClosedImmersion F.negative.inclusion.hom.hom.left := F.negative.isClosedImmersion
  letI : IsAffine F.negative.group.X.left := isAffine_of_isAffineHom F.negative.inclusion.hom.hom.left
  let χ : Character F.realization.pinned.pair.T.group :=
    Additive.toMul (F.realization.datumIso.val.weightEquiv w)
  let q : ((changeBase (integerMap m)).obj J.X).left ⟶ (splitTorus D).X.left :=
    p.hom.hom.left ≫ fibreProjection (integerMap m) (splitTorus D).X
  let b : F.negative.group.X.left ⟶ ((changeBase (integerMap m)).obj J.X).left :=
    (arithmeticFibreIso φ F.borelIso).inv.hom.hom.left ≫
      fibreProjection φ ((changeBase (integerMap m)).obj J.X)
  change b.appTop ((Units.map q.appTop.hom.toMonoidHom (torusMonomial D w))⁻¹).val = _
  rw [← map_inv (Units.map q.appTop.hom.toMonoidHom) (torusMonomial D w)]
  let z : Γ((splitTorus D).X.left, ⊤) := ((torusMonomial D w)⁻¹).val
  change b.appTop (q.appTop z) = _
  have h : b ≫ q = (F.projection.projection ≫ F.torusIso.inv).hom.hom.left ≫
      fibreProjection (algebraMap Integers.{u} k) (splitTorus D).X := by
    dsimp only [b, q]
    rw [Category.assoc]
    exact relativeProjection_comparison φ F p hp
  rw [← CommRingCat.comp_apply q.appTop b.appTop, ← Scheme.Hom.comp_appTop, h]
  exact inverseWeightCoordinate D F.torusIso F.projection.projection w χ
    (fun R s v hv => F.weight_marking R s v hv w)

/-- A single integer localization carries the marked opposite Borel and the
prescribed character, with comparison over every field of that base. -/
theorem exists_integralMarkedOppositeBorel : Statement.{u} := by
  intro D _ _ I w
  obtain ⟨y, n, hn, hy⟩ := LinearAlgebraicGroups.RationalRealization.positiveIntegralCocharacter D
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (R := CommRingCat.of Integers.{u})).mpr I.affine
  let c := laurentCocharacter (A := A.unop) I (-y) e
  let J := conjugationLimit c
  let i : J ⟶ I.group := conjugationLimitInclusion c ≫ e.hom
  let l : J ⟶ I.group := conjugationLimitEvaluation c ≫ e.hom
  have hi : IsClosedImmersion i.hom.hom.left := by
    change IsClosedImmersion ((conjugationLimitInclusion c).hom.hom.left ≫ e.hom.hom.hom.left)
    letI := conjugationLimitInclusion_isClosedImmersion c
    letI : IsIso e.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
    exact IsClosedImmersion.comp _ _
  have fieldData (k : Type u) [Field k] : Nonempty (IntegralBorelFibre I J i l k) :=
    integralBorelFibre I y n hn hy e k
  obtain ⟨F₀⟩ := fieldData Specs.RationalRealization.RationalField.{u}
  obtain ⟨m, hm, hJ⟩ := relativeSmoothness hi F₀
  obtain ⟨p, hp⟩ := relativeLimitFactors F₀ hm hJ
  refine ⟨m, hm, relativeBorel i hi hJ w p, fun k _ φ => ?_⟩
  obtain ⟨F⟩ := fieldData k
  exact compareRelativeBorel hi hJ w p hp φ F

end Assembly


end

end LinearAlgebraicGroups.Representation.IntegralMarkedOppositeBorel
