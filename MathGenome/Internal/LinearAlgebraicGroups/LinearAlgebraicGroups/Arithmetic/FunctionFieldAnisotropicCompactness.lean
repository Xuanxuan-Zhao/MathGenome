import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecomposition
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilGroupStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilAdelicPoints
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FunctionFieldClosedOrbitWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RationalFunctionSLAdelicReduction
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Field.Shrink
import Mathlib.Order.WellQuasiOrder
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Homeomorph.Quotient

open CategoryTheory Topology
open scoped RatFunc RestrictedProduct TensorProduct

universe u v v'

noncomputable section

namespace LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
set_option linter.style.haveILetI false

open Specs.FunctionFieldAnisotropicCompactness
open Specs.IntegralModels (RationalPoints)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A fixed support of weight coordinates allows only finitely many exponent vectors
when each active weight is bounded above and the opposite inequalities admit no
nonzero cocharacter. -/
theorem finite_exponents_of_weight_bounds {M I : Type*} [AddGroup M] [Finite I]
    (S : Set M) (weight : I → M →+ ℤ) (bound : I → ℤ)
    (bounded : ∀ n ∈ S, ∀ i, weight i n ≤ bound i)
    (noDirection : ∀ n : M, (∀ i, 0 ≤ weight i n) → n = 0) :
    S.Finite := by
  by_contra h
  let f : ℕ ↪ S := (show S.Infinite from h).natEmbedding _
  let a (j : ℕ) (i : I) := (bound i - weight i (f j)).toNat
  obtain ⟨j, l, hjl, horder⟩ := wellQuasiOrdered_le a
  have hdir : ∀ i, 0 ≤ weight i ((f j : M) - (f l : M)) := by
    intro i
    have hj := Int.toNat_of_nonneg (sub_nonneg.mpr (bounded _ (f j).property i))
    have hl := Int.toNat_of_nonneg (sub_nonneg.mpr (bounded _ (f l).property i))
    have hi : (a j i : ℤ) ≤ a l i := by exact_mod_cast (horder i)
    dsimp [a] at hi
    rw [hj, hl] at hi
    rw [map_sub]
    omega
  have heq := sub_eq_zero.mp (noDirection _ hdir)
  exact hjl.ne (f.injective (Subtype.ext heq))

/-- Finitely many active support patterns give a finite set of exponent vectors. -/
theorem finite_exponents {M I : Type*} [AddGroup M] [Finite I]
    (S : Set M) (support : M → Set I) (weight : I → M →+ ℤ) (bound : I → ℤ)
    (bounded : ∀ n ∈ S, ∀ i ∈ support n, weight i n ≤ bound i)
    (noDirection : ∀ n ∈ S, ∀ m : M, (∀ i ∈ support n, 0 ≤ weight i m) → m = 0) :
    S.Finite := by
  classical
  have h (J : Set I) : (S ∩ {n | support n = J}).Finite := by
    by_cases hJ : (S ∩ {n | support n = J}).Nonempty
    · obtain ⟨n, hn, hsupport⟩ := hJ
      exact finite_exponents_of_weight_bounds _ (fun i : J => weight i) (fun i => bound i)
        (fun m hm i => bounded m hm.1 i (hm.2.symm ▸ i.property))
        (fun m hm => noDirection n hn m (fun i hi => hm ⟨i, hsupport ▸ hi⟩))
    · rw [Set.not_nonempty_iff_eq_empty.mp hJ]
      exact Set.finite_empty
  have heq : S = ⋃ J : Set I, S ∩ {n | support n = J} := by
    ext n
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun hn => ⟨support n, hn, rfl⟩, fun ⟨_, hn, _⟩ => hn⟩
  rw [heq]
  exact Set.finite_iUnion h

/-- A compact set containing a representative of every right coset gives a compact
quotient. The subgroup need not be normal. -/
theorem compactSpace_of_coset_representatives {A : Type*} [Group A] [TopologicalSpace A]
    (H : Subgroup A) {C : Set A} (hC : IsCompact C)
    (hcovers : ∀ a : A, ∃ h : H, a * (h : A) ∈ C) :
    CompactSpace (A ⧸ H) := by
  constructor
  have himage := hC.image (QuotientGroup.continuous_mk (N := H))
  rwa [Set.eq_univ_of_forall (s := QuotientGroup.mk '' C) (fun q => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨h, ha⟩ := hcovers a
    exact ⟨a * h, ha, QuotientGroup.mk_mul_of_mem a h.property⟩)] at himage

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the represented scalar restriction at the ground field gives the
rational point group over the extension. -/
theorem exists_rational_point_comparison {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : Specs.AffineAlgebraicGroup K} {W : Specs.AffineAlgebraicGroup k}
    (ρ : (groupPointsFunctor k).obj W.val ≅
      WeilRestriction.extendScalars k K ⋙ (groupPointsFunctor K).obj G.val) :
    ∃ e : RationalPoints W ≃* RationalPoints G,
      ∀ g, e g = restrictionPoint ρ (tensorPointMap (R := k) (L := K)
        (algebraMap k K) (by ext; simp)) g := by
  let c : k ⊗[k] K ≃ₐ[K] K :=
    (Algebra.TensorProduct.commRight k K k).symm.trans (Algebra.TensorProduct.rid k K K)
  have hc : c.toAlgHom = tensorPointMap (R := k) (L := K)
        (algebraMap k K) (by ext; simp) := by
    ext z : 1
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      simp [c, tensorPointMap, Algebra.smul_def, mul_comm]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  let e : CommAlgCat.of K (k ⊗[k] K) ≅ CommAlgCat.of K K := CommAlgCat.isoMk c
  let e' := (ρ.app (CommAlgCat.of k k)) ≪≫ (groupPointsFunctor K |>.obj G.val).mapIso e
  refine ⟨e'.groupIsoToMulEquiv, ?_⟩
  intro g
  rw [← hc]
  rfl

/-- A topological group isomorphism identifying the two subgroups induces a
homeomorphism of their right coset spaces. -/
def rightCosetHomeomorph {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ* B)
    (H : Subgroup A) (J : Subgroup B) (he : ∀ a, e a ∈ J ↔ a ∈ H) :
    A ⧸ H ≃ₜ B ⧸ J := by
  have hr (a b : A) :
      QuotientGroup.leftRel H a b ↔ QuotientGroup.leftRel J (e a) (e b) := by
    simp only [QuotientGroup.leftRel_apply, ← map_inv, ← map_mul, he]
  exact Homeomorph.Quotient.congr e.toHomeomorph hr

@[simp]
theorem rightCosetHomeomorph_mk {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ* B)
    (H : Subgroup A) (J : Subgroup B) (he : ∀ a, e a ∈ J ↔ a ∈ H) (a : A) :
    rightCosetHomeomorph e H J he (QuotientGroup.mk a) = QuotientGroup.mk (e a) := rfl

/-- The finite orbit comparison step. Each reduction in the compact matrix
set has one of finitely many orbit values. Rational elements with the same
orbit value differ by a rational stabilizer, which gives the coset correction. -/
theorem compactSpace_of_finite_orbit_reduction
    {H A P X : Type*} [Group H] [Group A] [Group P]
    [TopologicalSpace H] [TopologicalSpace A] [ContinuousMul A]
    (i : H →* A) (ι : P →* A) (Γ : Subgroup H) (orbit : P → X)
    (hi : IsClosedEmbedding i) {C : Set A} (hC : IsCompact C)
    {V : Set X} (hV : V.Finite)
    (hstab : ∀ p q : P, orbit p = orbit q → ι (p * q⁻¹) ∈ Γ.map i)
    (hred : ∀ h : H, ∃ p : P, i h * ι p ∈ C ∧ orbit p ∈ V) :
    CompactSpace (H ⧸ Γ) := by
  classical
  let S : Set X := V ∩ Set.range orbit
  have hS : S.Finite := hV.subset Set.inter_subset_left
  let := hS.fintype
  let representative (x : S) : P := x.property.2.choose
  have hrep (x : S) : orbit (representative x) = x := x.property.2.choose_spec
  let C' : Set A := ⋃ x : S, (fun a => a * ι (representative x)⁻¹) '' C
  have hC' : IsCompact C' :=
    isCompact_iUnion fun x : S => hC.image (continuous_id.mul continuous_const)
  apply compactSpace_of_coset_representatives Γ (hi.isCompact_preimage hC')
  intro h
  obtain ⟨p, hp, hpV⟩ := hred h
  let x : S := ⟨orbit p, hpV, ⟨p, rfl⟩⟩
  obtain ⟨s, hs, hsi⟩ := hstab p (representative x) (hrep x).symm
  refine ⟨⟨s, hs⟩, Set.mem_iUnion.mpr ⟨x, i h * ι p, hp, ?_⟩⟩
  change (i h * ι p) * ι ((representative x)⁻¹) = i (h * s)
  rw [map_mul i, hsi, map_mul ι, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem tensorPointMap_tmul {k K R L : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [CommRing L] [Algebra K L] (f : R →+* L)
    (hf : f.comp (algebraMap k R) = (algebraMap K L).comp (algebraMap k K))
    (r : R) (x : K) :
    tensorPointMap f hf (r ⊗ₜ[k] x) = f r * algebraMap K L x :=
  Specs.FunctionFieldWeilAdelicPoints.tensorSpecialization_tmul f hf r x

private theorem tensorPointMap_groundSquare
    {k K B C : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing B] [Algebra k B] [CommRing C] [Algebra K C]
    (f : B →+* C)
    (hf : f.comp (algebraMap k B) = (algebraMap K C).comp (algebraMap k K)) :
    (tensorPointMap f hf).comp (WeilRestriction.tensorMap k K (Algebra.ofId k B)) =
      (Algebra.ofId K C).comp (tensorPointMap (R := k) (L := K)
        (algebraMap k K) (by ext; simp)) := by
  ext z : 1
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    change tensorPointMap f hf
        (Algebra.TensorProduct.map (Algebra.ofId k B) (AlgHom.id k K) (r ⊗ₜ[k] x)) =
      algebraMap K C (tensorPointMap (algebraMap k K) (by ext; simp) (r ⊗ₜ[k] x))
    rw [Algebra.TensorProduct.map_tmul, tensorPointMap_tmul, tensorPointMap_tmul, map_mul]
    exact congrArg (· * algebraMap K C x) (DFunLike.congr_fun hf r)
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

/-- Naturality square for restriction of scalars followed by evaluation in a
factor of the scalar extension. -/
theorem restrictionPoint_naturalAtGround
    {k K B C : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing B] [Algebra k B] [CommRing C] [Algebra K C]
    {U : CommAlgCat.{u} k ⥤ GrpCat.{u}} {V : CommAlgCat.{u} K ⥤ GrpCat.{u}}
    (ρ : U ⟶ WeilRestriction.extendScalars k K ⋙ V)
    (f : B →+* C)
    (hf : f.comp (algebraMap k B) = (algebraMap K C).comp (algebraMap k K)) :
    let a : CommAlgCat.of k k ⟶ CommAlgCat.of k B := CommAlgCat.ofHom (Algebra.ofId k B)
    let b : CommAlgCat.of K K ⟶ CommAlgCat.of K C := CommAlgCat.ofHom (Algebra.ofId K C)
    let s : CommAlgCat.of K (B ⊗[k] K) ⟶ CommAlgCat.of K C :=
      CommAlgCat.ofHom (tensorPointMap f hf)
    let q : CommAlgCat.of K (k ⊗[k] K) ⟶ CommAlgCat.of K K :=
      CommAlgCat.ofHom (tensorPointMap (algebraMap k K) (by ext; simp))
    U.map a ≫ ρ.app _ ≫ V.map s = ρ.app _ ≫ V.map q ≫ V.map b := by
  intro a b s q
  have hsq : (WeilRestriction.extendScalars k K).map a ≫ s = q ≫ b :=
    CommAlgCat.hom_ext (tensorPointMap_groundSquare f hf)
  rw [← Category.assoc, ρ.naturality, Category.assoc]
  change ρ.app _ ≫ V.map ((WeilRestriction.extendScalars k K).map a) ≫ V.map s =
    ρ.app _ ≫ V.map q ≫ V.map b
  rw [← Functor.map_comp, ← Functor.map_comp, hsq]

section WeightCoordinates

open LatticeCompletionDecompositionSpec
open scoped Polynomial

/-- A nonzero rational function with a fixed polynomial denominator has
a uniform positive lower bound at infinity. -/
theorem inverse_denominator_norm_le {F : Type u} [Field F] [Finite F]
    (d x : F⟮X⟯) (hd : d ≠ 0) (hx : x ≠ 0)
    (h : ∀ p : IsDedekindDomain.HeightOneSpectrum F[X], p.valuation F⟮X⟯ (d * x) ≤ 1) :
    letI := infinityNormedField F
    ‖infinityEmbedding F d‖⁻¹ ≤ ‖infinityEmbedding F x‖ := by
  let := infinityNormedField F
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F⟮X⟯ (d * x) h
  have hdeg : 0 ≤ (d * x).intDegree := by rw [← ha, RatFunc.intDegree_polynomial]; positivity
  have hq : 1 ≤ (Nat.card F : ℝ) := by exact_mod_cast Finite.one_lt_card (α := F) |>.le
  have hnorm := LatticeCompletionDecomposition.functionInfinityBaseNorm F _ (mul_ne_zero hd hx)
  have hlow : 1 ≤ ‖infinityEmbedding F (d * x)‖ := by
    rw [hnorm]
    exact one_le_zpow₀ hq hdeg
  have hpos : 0 < ‖infinityEmbedding F d‖ :=
    norm_pos_iff.mpr ((infinityEmbedding F).injective.ne (by simpa using hd))
  rw [← one_div, div_le_iff₀ hpos, mul_comm, ← norm_mul, ← map_mul]
  exact hlow

/-- Uniform denominators at the finite places and the norm estimates at the
pole give finitely many exponents when the supported weights admit no
nonzero cocharacter with a limit. -/
theorem finite_exponents_of_rational_weight_coordinates {F : Type u} [Field F] [Finite F]
    {M I : Type*} [AddGroup M] [Finite I]
    (S : Set M) (coord : M → I → F⟮X⟯) (wt : I → M →+ ℤ)
    (d : I → F⟮X⟯) (hd : ∀ i, d i ≠ 0) (C : I → ℝ)
    (hfinite : ∀ n ∈ S, ∀ i, ∀ p : IsDedekindDomain.HeightOneSpectrum F[X],
      p.valuation F⟮X⟯ (d i * coord n i) ≤ 1)
    (hinfty : letI := infinityNormedField F
      ∀ n ∈ S, ∀ i, ‖infinityEmbedding F (coord n i)‖ ≤
        C i * (Nat.card F : ℝ) ^ (-wt i n : ℤ))
    (hlimit : ∀ n ∈ S, ∀ m : M, (∀ i, coord n i ≠ 0 → 0 ≤ wt i m) → m = 0) :
    S.Finite := by
  let := infinityNormedField F
  let q : ℝ := Nat.card F
  have hq : 1 < q := by
    change 1 < (Nat.card F : ℝ)
    exact_mod_cast Finite.one_lt_card (α := F)
  have hq0 : 0 < q := zero_lt_one.trans hq
  let D (i : I) : ℝ := ‖infinityEmbedding F (d i)‖
  have hD (i : I) : 0 < D i :=
    norm_pos_iff.mpr ((infinityEmbedding F).injective.ne (by simpa using hd i))
  choose N hN using fun i => pow_unbounded_of_one_lt (C i * D i) hq
  refine finite_exponents S (fun n => {i | coord n i ≠ 0}) wt (fun i => (N i : ℤ)) ?_ hlimit
  intro n hn i hi
  have hlow := inverse_denominator_norm_le (d i) (coord n i) (hd i) hi (hfinite n hn i)
  have hb : (D i)⁻¹ ≤ C i * q ^ (-wt i n : ℤ) := hlow.trans (hinfty n hn i)
  have hb' : ((D i)⁻¹ * q ^ wt i n) ≤ C i := by
    have hh := mul_le_mul_of_nonneg_right hb (zpow_nonneg hq0.le (wt i n))
    rwa [mul_assoc, ← zpow_add₀ hq0.ne', neg_add_cancel, zpow_zero, mul_one] at hh
  have hb'' : q ^ wt i n ≤ C i * D i := by
    have hh := mul_le_mul_of_nonneg_right hb' (hD i).le
    rw [mul_right_comm (D i)⁻¹, inv_mul_cancel₀ (hD i).ne', one_mul] at hh
    exact hh
  apply (zpow_le_zpow_iff_right₀ hq).mp
  exact hb''.trans (by simpa only [zpow_natCast] using (hN i).le)

/-- A bound at infinity gives a finite set of rational functions with fixed
common denominator away from infinity. -/
theorem finite_rational_functions_of_integral_bounds {F : Type u} [Field F] [Finite F]
    (d : F⟮X⟯) (hd : d ≠ 0) (C : ℝ) :
    letI := infinityNormedField F
    {x : F⟮X⟯ | (∀ p : IsDedekindDomain.HeightOneSpectrum F[X],
      p.valuation F⟮X⟯ (d * x) ≤ 1) ∧ ‖infinityEmbedding F x‖ ≤ C}.Finite := by
  classical
  let := infinityNormedField F
  let q : ℝ := Nat.card F
  have hq : 1 < q := by
    change 1 < (Nat.card F : ℝ)
    exact_mod_cast (Finite.one_lt_card (α := F))
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (‖infinityEmbedding F d‖ * C) hq
  let r : Polynomial.degreeLT F N → F⟮X⟯ := fun a => d⁻¹ * algebraMap F[X] F⟮X⟯ a.val
  let : Finite (Polynomial.degreeLT F N) :=
    Finite.of_injective (Polynomial.degreeLTEquiv F N) (Polynomial.degreeLTEquiv F N).injective
  refine (Set.finite_range r).subset ?_
  rintro x ⟨hfinite, hinfty⟩
  obtain ⟨a, ha⟩ :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F⟮X⟯ (d * x) hfinite
  have haN : a ∈ Polynomial.degreeLT F N := by
    by_cases hz : a = 0
    · rw [hz]
      exact Submodule.zero_mem _
    have hn : d * x ≠ 0 := by
      rw [← ha]
      simpa only [map_zero] using (IsFractionRing.injective F[X] F⟮X⟯).ne hz
    have hbound : ‖infinityEmbedding F (d * x)‖ < q ^ N := by
      rw [map_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left hinfty (norm_nonneg _)).trans_lt hN
    rw [LatticeCompletionDecomposition.functionInfinityBaseNorm F (d * x) hn,
      ← ha, RatFunc.intDegree_polynomial, ← zpow_natCast] at hbound
    have hdeg : (a.natDegree : ℤ) < (N : ℤ) :=
      (zpow_lt_zpow_iff_right₀ hq).mp hbound
    exact Polynomial.mem_degreeLT.mpr
      ((Polynomial.natDegree_lt_iff_degree_lt hz).mp (Int.ofNat_lt.mp hdeg))
  exact ⟨⟨a, haN⟩, by simp [r, ha, hd]⟩

/-- Only finitely many exponents and inverse orbit vectors can occur in a
family of reductions satisfying the coordinate and contraction bounds. -/
private theorem finite_reduction_values {F : Type u} [Field F] [Finite F]
    {P M I : Type*} [AddGroup M] [Finite I] (admissible : P → M → Prop)
    (orbit : P → I → F⟮X⟯) (wt : I → M →+ ℤ)
    (d : I → F⟮X⟯) (hd : ∀ i, d i ≠ 0) (C : I → ℝ)
    (hfinite : ∀ p n, admissible p n → ∀ i (v : IsDedekindDomain.HeightOneSpectrum F[X]),
      v.valuation F⟮X⟯ (d i * orbit p i) ≤ 1)
    (hinfty : letI := infinityNormedField F
      ∀ p n, admissible p n → ∀ i, ‖infinityEmbedding F (orbit p i)‖ ≤
        C i * (Nat.card F : ℝ) ^ (-wt i n : ℤ))
    (hlimit : ∀ p m, (∀ i, orbit p i ≠ 0 → 0 ≤ wt i m) → m = 0) :
    {n | ∃ p, admissible p n}.Finite ∧
      ∃ V : Set (I → F⟮X⟯), V.Finite ∧ ∀ p n, admissible p n → orbit p ∈ V := by
  classical
  letI := infinityNormedField F
  let E : Set M := {n | ∃ p, admissible p n}
  let coord (n : M) : I → F⟮X⟯ := if h : n ∈ E then orbit h.choose else 0
  have hE : E.Finite := by
    apply finite_exponents_of_rational_weight_coordinates E coord wt d hd C
    · intro n hn
      rw [show coord n = orbit hn.choose from dite_eq_left hn]
      exact hfinite hn.choose n hn.choose_spec
    · intro n hn
      rw [show coord n = orbit hn.choose from dite_eq_left hn]
      exact hinfty hn.choose n hn.choose_spec
    · intro n hn
      rw [show coord n = orbit hn.choose from dite_eq_left hn]
      exact hlimit hn.choose
  let bound (i : I) (n : M) := C i * (Nat.card F : ℝ) ^ (-wt i n : ℤ)
  choose U hU using fun i => (hE.image (bound i)).bddAbove
  let V (i : I) := {x : F⟮X⟯ | (∀ p : IsDedekindDomain.HeightOneSpectrum F[X],
    p.valuation F⟮X⟯ (d i * x) ≤ 1) ∧ ‖infinityEmbedding F x‖ ≤ U i}
  refine ⟨hE, {v | ∀ i, v i ∈ V i}, Set.Finite.pi' (fun i =>
    finite_rational_functions_of_integral_bounds (d i) (hd i) (U i)), ?_⟩
  intro p n hn i
  exact ⟨hfinite p n hn i, (hinfty p n hn i).trans
    (hU i (Set.mem_image_of_mem (bound i) ⟨p, hn⟩))⟩

end WeightCoordinates

section Reindex

open Filter
open scoped RestrictedProduct

variable {I J : Type*} {A : I → Type*} {B : J → Type*}
    [∀ i, Group (A i)] [∀ j, Group (B j)]
    [∀ i, TopologicalSpace (A i)] [∀ j, TopologicalSpace (B j)]
    (p : J ≃ I) (U : ∀ i, Subgroup (A i)) (V : ∀ j, Subgroup (B j))
    (e : ∀ i j, p j = i → A i ≃ₜ* B j)

/-- Reindexing the local points preserves the topology of a restricted product
when the integral subgroups are carried to one another. -/
theorem exists_reindexRestrictedProduct
    (he : ∀ i j (h : p j = i) (a : A i), e i j h a ∈ V j ↔ a ∈ U i) :
    ∃ E : (Πʳ i, [A i, U i]) ≃ₜ* (Πʳ j, [B j, V j]),
      ∀ a j, E a j = e (p j) j rfl (a (p j)) := by
  let φ (j : J) : A (p j) →* B j := (e (p j) j rfl).toMonoidHom
  let ψ (i : I) : B (p.symm i) →* A i := (e i _ (p.apply_symm_apply i)).symm.toMonoidHom
  have hφ : ∀ᶠ j in cofinite, Set.MapsTo (φ j) (U (p j)) (V j) :=
    Eventually.of_forall fun j a ha => (he (p j) j rfl a).mpr ha
  have hψ : ∀ᶠ i in cofinite, Set.MapsTo (ψ i) (V (p.symm i)) (U i) :=
    Eventually.of_forall fun i b hb => (he i _ (p.apply_symm_apply i) _).mp (by
      change e i (p.symm i) _ ((e i (p.symm i) _).symm b) ∈ V _
      rwa [ContinuousMulEquiv.apply_symm_apply])
  let E := RestrictedProduct.mapAlongMonoidHom A B p p.injective.tendsto_cofinite φ hφ
  let E' := RestrictedProduct.mapAlongMonoidHom B A p.symm p.symm.injective.tendsto_cofinite ψ hψ
  have hleft (a : Πʳ i, [A i, U i]) : E' (E a) = a := by
    ext i
    change (e i (p.symm i) (p.apply_symm_apply i)).symm
      (e (p (p.symm i)) (p.symm i) rfl (a (p (p.symm i)))) = a i
    have h (j : J) (i' : I) (hj : p j = i') :
        (e i' j hj).symm (e (p j) j rfl (a (p j))) = a i' := by
      subst i'
      exact ContinuousMulEquiv.symm_apply_apply _ _
    exact h (p.symm i) i (p.apply_symm_apply i)
  have hright (b : Πʳ j, [B j, V j]) : E (E' b) = b := by
    ext j
    change e (p j) j rfl ((e (p j) (p.symm (p j)) _).symm (b (p.symm (p j)))) = b j
    have h (j' : J) (heq : p j' = p j) (hj : j' = j) :
        e (p j) j rfl ((e (p j) j' heq).symm (b j')) = b j := by
      subst j'
      exact ContinuousMulEquiv.apply_symm_apply _ _
    exact h (p.symm (p j)) (p.apply_symm_apply (p j)) (p.symm_apply_apply j)
  let f := MulEquiv.ofBijective E ⟨Function.LeftInverse.injective hleft,
    Function.RightInverse.surjective hright⟩
  have h' : (f.symm : _ → _) = E' := funext fun b =>
    f.injective (by rw [MulEquiv.apply_symm_apply]; exact (hright b).symm)
  refine ⟨{ f with continuous_toFun := ?_, continuous_invFun := ?_ }, fun _ _ => rfl⟩
  · exact RestrictedProduct.mapAlong_continuous A B p p.injective.tendsto_cofinite _ hφ
      (fun j => (e (p j) j rfl).continuous)
  · change Continuous (f.symm : _ → _)
    rw [h']
    exact RestrictedProduct.mapAlong_continuous B A p.symm p.symm.injective.tendsto_cofinite _ hψ
      (fun i => (e i (p.symm i) (p.apply_symm_apply i)).symm.continuous)

end Reindex

section FunctionPlaces

open scoped RestrictedProduct

open Arithmetic.AdelicGroups
open Specs.IntegralModels (MatrixRealization)
open Specs.FunctionFieldAnisotropicCompactness
open private adelesTopology quotientTopology from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness

variable {F : Type v} {F' : Type v'} {K : Type u}
  [Field F] [Finite F] [Field F'] [Finite F'] [Field K] [Algebra F K] [Algebra F' K]

/-- Each intrinsic function place appears once in the full adelic product. -/
def outsideFunctionPlaceEquiv (t : SeparatingParameter F K) :
    FunctionPlace K ≃ Outside (GlobalFieldData.function F t) ∅ where
  toFun w := ⟨Sum.inl w, Finset.notMem_empty _⟩
  invFun w := w.val.elim id PEmpty.elim
  left_inv _ := rfl
  right_inv := by
    rintro ⟨w|w, hw⟩
    · rfl
    · exact w.elim

/-- Changing the constant-field presentation of a function field preserves
its full adelic group, with the corresponding coordinates kept fixed. -/
theorem exists_functionAdeles_reindex (t : SeparatingParameter F K) (s : SeparatingParameter F' K)
    {G : Specs.AffineAlgebraicGroup K} (i : MatrixRealization G) :
    let D := GlobalFieldData.function F t
    let D' := GlobalFieldData.function F' s
    letI := adelesTopology D i
    letI := adelesTopology D' i
    ∃ E : Adeles D i ∅ ≃ₜ* Adeles D' i ∅,
      ∀ a w, E a (outsideFunctionPlaceEquiv s w) = a (outsideFunctionPlaceEquiv t w) := by
  let D := GlobalFieldData.function F t
  let D' := GlobalFieldData.function F' s
  let p := (outsideFunctionPlaceEquiv s).symm.trans (outsideFunctionPlaceEquiv t)
  let A (w : Outside D ∅) := LocalPoints D i w.1
  let B (w : Outside D' ∅) := LocalPoints D' i w.1
  let (w : Outside D ∅) : TopologicalSpace (A w) :=
    let : Field (D.Completion w.1) := GlobalFieldData.instFieldCompletion D w.1
    let : Algebra K (D.Completion w.1) := completionAlgebra D w.1
    let : TopologicalSpace (D.Completion w.1) := GlobalFieldData.instTopologicalSpaceCompletion D w.1
    inferInstanceAs (TopologicalSpace (PointsIn i (D.Completion w.1)))
  let (w : Outside D' ∅) : TopologicalSpace (B w) :=
    let : Field (D'.Completion w.1) := GlobalFieldData.instFieldCompletion D' w.1
    let : Algebra K (D'.Completion w.1) := completionAlgebra D' w.1
    let : TopologicalSpace (D'.Completion w.1) := GlobalFieldData.instTopologicalSpaceCompletion D' w.1
    inferInstanceAs (TopologicalSpace (PointsIn i (D'.Completion w.1)))
  let U (w : Outside D ∅) := localSubgroup D i w.1
  let V (w : Outside D' ∅) := localSubgroup D' i w.1
  let e (x : Outside D ∅) (y : Outside D' ∅) (h : p y = x) : A x ≃ₜ* B y := by
    subst x
    rcases y with ⟨w|w, hw⟩
    · exact ContinuousMulEquiv.refl _
    · exact w.elim
  have he (x : Outside D ∅) (y : Outside D' ∅) (h : p y = x) (a : A x) :
      e x y h a ∈ V y ↔ a ∈ U x := by
    subst x
    rcases y with ⟨w|w, hw⟩
    · rfl
    · exact w.elim
  obtain ⟨E, hE⟩ := exists_reindexRestrictedProduct p U V e he
  exact ⟨E, fun a w => hE a (outsideFunctionPlaceEquiv s w)⟩

/-- The place reindexing identifies the diagonally embedded rational points. -/
theorem exists_functionQuotient_reindex (t : SeparatingParameter F K) (s : SeparatingParameter F' K)
    {G : Specs.AffineAlgebraicGroup K} (i : MatrixRealization G) :
    let D := GlobalFieldData.function F t
    let D' := GlobalFieldData.function F' s
    letI := quotientTopology D i
    letI := quotientTopology D' i
    Nonempty (AdelicQuotient D i ≃ₜ AdelicQuotient D' i) := by
  let D := GlobalFieldData.function F t
  let D' := GlobalFieldData.function F' s
  let := adelesTopology D i
  let := adelesTopology D' i
  obtain ⟨E, hE⟩ := exists_functionAdeles_reindex t s i
  have he (a : Adeles D i ∅) : E a ∈ rationalDiagonal D' i ↔ a ∈ rationalDiagonal D i := by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, fun y => ?_⟩
      obtain ⟨w, rfl⟩ := (outsideFunctionPlaceEquiv t).surjective y
      exact (hE a w).symm.trans (hg (outsideFunctionPlaceEquiv s w))
    · rintro ⟨g, hg⟩
      refine ⟨g, fun y => ?_⟩
      obtain ⟨w, rfl⟩ := (outsideFunctionPlaceEquiv s).surjective y
      exact (hE a w).trans (hg (outsideFunctionPlaceEquiv t w))
  exact ⟨rightCosetHomeomorph E (rationalDiagonal D i) (rationalDiagonal D' i) he⟩

end FunctionPlaces

section CompactnessTransfer

open Specs.GeometricRadicals (IsSemisimple)
open Specs.IntegralModels (MatrixRealization)
open Specs.FunctionFieldAnisotropicCompactness
open private quotientTopology from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness

private theorem exists_small_parameter {F : Type v} {K : Type u} [Field F] [Finite F]
    [Field K] [Algebra F K] (t : SeparatingParameter F K) :
    ∃ (F₀ : Type u) (_ : Field F₀) (_ : Finite F₀) (_ : Algebra F₀ K)
      (s : SeparatingParameter F₀ K), s.element = t.element := by
  let : Small.{u} F := small_of_injective (algebraMap F K).injective
  let H := Shrink.{u} F
  let e : H ≃+* F := Shrink.ringEquiv F
  let : Finite H := Finite.of_injective e e.injective
  let : Algebra H F := e.toRingHom.toAlgebra
  let : Algebra H K := ((algebraMap F K).comp (algebraMap H F)).toAlgebra
  let : IsScalarTower H F K := IsScalarTower.of_algebraMap_eq' rfl
  let e' : H ≃ₐ[H] F := { e with commutes' := fun x => by simp; rfl }
  let L := IntermediateField.adjoin F {t.element}
  let L' := IntermediateField.adjoin H {t.element}
  have he₀ : L'.restrictScalars H = L' := by ext x; rfl
  have he : L' = L.restrictScalars H := he₀.symm.trans
    (IntermediateField.restrictScalars_adjoin_of_algEquiv e' rfl {t.element})
  refine ⟨H, inferInstance, inferInstance, inferInstance,
    ⟨t.element, Transcendental.of_tower_top H t.transcendental, ?_, ?_⟩, rfl⟩
  · change Module.Finite L' K
    rw [he]
    exact t.finite
  · change Algebra.IsSeparable L' K
    rw [he]
    exact t.separable

/-- Compactness over the rational function field transfers to any finite
separable extension through the placewise quotient comparison. -/
theorem compactness_of_rational_function_field
    (hWeil : WeilRestrictionComparison.{u})
    (hRational : ∀ (F : Type u) [Field F] [Finite F]
      (G : Specs.AffineAlgebraicGroup F⟮X⟯) (i : MatrixRealization G),
      IsSemisimple G → IsAnisotropic G →
        let D := GlobalFieldData.function F (rationalParameter F)
        @CompactSpace (AdelicQuotient D i) (quotientTopology D i))
    {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) (G : Specs.AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hs : IsSemisimple G) (ha : IsAnisotropic G) :
    let D := GlobalFieldData.function F t
    @CompactSpace (AdelicQuotient D i) (quotientTopology D i) := by
  obtain ⟨W, ρ, j, b, e, he, eK, eA, eQ, hsemi, haniso, _, _, _, _⟩ := hWeil t G i
  let := quotientTopology (GlobalFieldData.function F (rationalParameter F)) j
  let := quotientTopology (GlobalFieldData.function F t) i
  let := hRational F W j (hsemi hs) (haniso ha)
  exact eQ.compactSpace

/-- The rational case and canonical Weil comparison imply the compactness
statement with arbitrary universes for the constant field and function field. -/
theorem functionFieldCompactness_of_weilComparison
    (hWeil : WeilRestrictionComparison.{u})
    (hRational : ∀ (F : Type u) [Field F] [Finite F]
      (G : Specs.AffineAlgebraicGroup F⟮X⟯) (i : MatrixRealization G),
      IsSemisimple G → IsAnisotropic G →
        let D := GlobalFieldData.function F (rationalParameter F)
        @CompactSpace (AdelicQuotient D i) (quotientTopology D i)) :
    FunctionFieldCompactness.{u, v} := by
  intro F K _ _ _ _ t G i hs ha D
  obtain ⟨F₀, hF₀, fF₀, alg, s, _⟩ := exists_small_parameter t
  let := hF₀
  let := fF₀
  let := alg
  let := quotientTopology (GlobalFieldData.function F₀ s) i
  let := quotientTopology D i
  obtain ⟨E⟩ := exists_functionQuotient_reindex s t i
  let := compactness_of_rational_function_field hWeil hRational s G i hs ha
  exact E.compactSpace

end CompactnessTransfer

section WeilComparison

open Arithmetic.AdelicGroups
open Specs.IntegralModels (MatrixRealization)
open private adelesTopology quotientTopology from
  MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness

/-- Scalar restriction identifies the full adelic quotients through its
canonical local and rational point maps. -/
theorem weilRestrictionComparison : WeilRestrictionComparison.{u} := by
  intro F K _ _ _ _ t G i
  letI := t.rationalAlgebra
  let D : GlobalFieldData.{u, u} K := GlobalFieldData.function F t
  let D₀ : GlobalFieldData.{u, u} F⟮X⟯ := GlobalFieldData.function F (rationalParameter F)
  letI := adelesTopology D i
  letI := quotientTopology D i
  obtain ⟨W, ρ⟩ := WeilRestriction.groupRepresentation F⟮X⟯ K G
  obtain ⟨m, L, ⟨l⟩, f, hf⟩ := faithfulLinearization F⟮X⟯ W
  let j : MatrixRealization W := ⟨m, L, l, f, hf⟩
  letI := adelesTopology D₀ j
  letI := quotientTopology D₀ j
  obtain ⟨C⟩ := FunctionFieldWeilAdelicPoints.weilAdelicComparison t G W i j ρ
  let ext (w : FunctionPlace K) := C.completionMap (C.below w) ⟨w, rfl⟩
  have hcomp (w : FunctionPlace K) :
      (ext w).comp (C.below w).embedding = w.embedding.comp t.rationalMap.toRingHom :=
    C.completionMap_comp (C.below w) ⟨w, rfl⟩
  obtain ⟨eK, heK⟩ := exists_rational_point_comparison ρ
  let eA : Adeles D₀ j ∅ ≃ₜ* Adeles D i ∅ := C.adelicEquiv
  have hcoord (g : Adeles D₀ j ∅) (w : FunctionPlace K) :
      let v := outsideFunctionPlaceEquiv (rationalParameter F) (C.below w)
      let z := outsideFunctionPlaceEquiv t w
      letI : Field (D₀.Completion v.1) := GlobalFieldData.instFieldCompletion D₀ v.1
      letI : Field (D.Completion z.1) := GlobalFieldData.instFieldCompletion D z.1
      letI := completionAlgebra D₀ v.1
      letI := completionAlgebra D z.1
      eA g z = restrictionPoint ρ (R := D₀.Completion v.1) (L := D.Completion z.1)
        (tensorPointMap (ext w) (hcomp w)) (g v) := by
    exact (C.adelicEquiv_apply g w).trans
      (C.localEquiv_apply (C.below w) _ ⟨w, rfl⟩)
  have hdiag (g : RationalPoints W) :
      eA (AdelicGroups.diagonal D₀ j ∅ g) = AdelicGroups.diagonal D i ∅ (eK g) := by
    apply RestrictedProduct.ext
    intro z
    obtain ⟨w, rfl⟩ := (outsideFunctionPlaceEquiv t).surjective z
    refine (hcoord (AdelicGroups.diagonal D₀ j ∅ g) w).trans ?_
    let v := outsideFunctionPlaceEquiv (rationalParameter F) (C.below w)
    let z := outsideFunctionPlaceEquiv t w
    letI : Field (D₀.Completion v.1) := GlobalFieldData.instFieldCompletion D₀ v.1
    letI : Field (D.Completion z.1) := GlobalFieldData.instFieldCompletion D z.1
    letI := completionAlgebra D₀ v.1
    letI := completionAlgebra D z.1
    have h := restrictionPoint_naturalAtGround (B := D₀.Completion v.1)
      (C := D.Completion z.1) ρ.hom (ext w) (hcomp w)
    change restrictionPoint ρ (R := D₀.Completion v.1) (L := D.Completion z.1)
      (tensorPointMap (ext w) (hcomp w)) (localPoint D₀ j v.1 g) = localPoint D i z.1 (eK g)
    rw [heK]
    exact ConcreteCategory.congr_hom h g
  have hrange (a : Adeles D₀ j ∅) : eA a ∈ rationalDiagonal D i ↔ a ∈ rationalDiagonal D₀ j := by
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := eK.surjective x
      have hy : a = AdelicGroups.diagonal D₀ j ∅ y := by
        apply eA.injective
        rw [hdiag]
        exact RestrictedProduct.ext _ _ hx
      exact ⟨y, fun w => congrArg (fun z : Adeles D₀ j ∅ => z w) hy⟩
    · rintro ⟨y, hy⟩
      have hy' : a = AdelicGroups.diagonal D₀ j ∅ y := RestrictedProduct.ext _ _ hy
      rw [hy', hdiag]
      exact ⟨eK y, fun _ => rfl⟩
  exact ⟨W, ρ, j, C.below, ext, hcomp, eK, eA,
    rightCosetHomeomorph eA (rationalDiagonal D₀ j) (rationalDiagonal D i) hrange,
    FunctionFieldWeilGroupStructure.weilRestrictionPreservesSemisimplicity G W ρ,
    FunctionFieldWeilGroupStructure.weilRestrictionPreservesAnisotropy G W ρ,
    fun w => ⟨C.below_val w, C.completionMap_continuous (C.below w) ⟨w, rfl⟩⟩,
    heK, hcoord, rightCosetHomeomorph_mk eA _ _ hrange⟩

end WeilComparison

section SpecialLinear

open AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.GeometricRadicals (IsSemisimple)
open Specs.IntegralModels (MatrixRealization)
open Specs.RationalFunctionSLAdelicReduction (SpecialLinearRealization)
open private sl_is_det_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private multiplicativeGroup_isCommutative from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits
open private Unipotent.onPoints Unipotent.kernel_points Unipotent.factor_through_closed from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

/-- A faithful matrix realization of a semisimple group factors as a closed
immersion into the determinant-one group. -/
private theorem exists_specialLinear_embedding {k : Type u} [Field k]
    (G : Specs.AffineAlgebraicGroup k) (i : MatrixRealization G) (hG : IsSemisimple G)
    (P : SpecialLinearRealization k i.size) :
    ∃ f : G.val ⟶ P.group.val, IsClosedImmersion f.hom.hom.left := by
  obtain ⟨q, j, hj, hker, _⟩ := sl_is_det_kernel i.matrix P.specialPoints
  have hq := ClosedHomogeneousOrbits.hom_to_commutative_eq_one G
    (StandardGroups.multiplicativeGroup k) hG multiplicativeGroup_isCommutative (i.embedding ≫ q)
  obtain ⟨f, hf⟩ := Unipotent.factor_through_closed (A := G) (B := P.group) (C := i.ambient)
    i.embedding j hj (fun R x => (Unipotent.kernel_points q ⟨P.group.val, j, hj⟩ hker R _).mp (by
      change x ≫ (i.embedding ≫ q).hom.hom = 1
      rw [hq, MonObj.comp_one]))
  letI := hj
  haveI : IsClosedImmersion (f.hom.hom.left ≫ j.hom.hom.left) := by
    change IsClosedImmersion (f ≫ j).hom.hom.left
    rw [hf]
    exact i.closed
  exact ⟨f, IsClosedImmersion.of_comp_isClosedImmersion _ j.hom.hom.left⟩

end SpecialLinear

section OrbitCoordinates

open AlgebraicGeometry Opposite
open Specs.AdjointRepresentation (GroupPoints)
open Specs.FunctionFieldClosedOrbitWeights (coordinates)
open Specs.RootWeightAction (Representation act extendVector)
open Specs.RationalFunctionSLAdelicReduction (SpecialLinearRealization)
open Specs.StandardGroups (GLCoordinates)
open Specs.Unipotent (Index)
open Arithmetic.AdelicGroups
open private coordinates_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FunctionFieldClosedOrbitWeights
open private map_act from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits
open private coordinateMap coordinateMap_spec clearPolynomialDenominators from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private matrixPresentation glEvaluation_fraction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation matrixEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private polynomialPlace from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RationalFunctionSLAdelicReduction
open scoped Polynomial

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
  {m : ℕ} {P : SpecialLinearRealization k m}

/-- The coordinates of the inverse translate of a fixed rational vector. -/
private def inverseOrbitCoordinates (ρ : Representation P.group.val I)
    (B : Matrix.GeneralLinearGroup I k) (b : I → k)
    (R : TestAlgebra k) (g : GroupPoints P.group.val R) : I → R :=
  coordinates B R (act ρ R g⁻¹ (extendVector R b))

private theorem inverseOrbitCoordinates_map (ρ : Representation P.group.val I)
    (B : Matrix.GeneralLinearGroup I k) (b : I → k) {R S : TestAlgebra k}
    (f : R ⟶ S) (g : GroupPoints P.group.val R) (i : I) :
    f.hom (inverseOrbitCoordinates ρ B b R g i) =
      inverseOrbitCoordinates ρ B b S (mapPoints f g) i := by
  let s : GroupPoints P.group.val R →* GroupPoints P.group.val S :=
    (((groupPointsFunctor k).obj P.group.val).map f).hom
  have hVec : (fun i => f.hom (extendVector R b i)) = extendVector S b :=
    funext fun i => f.hom.commutes (b i)
  unfold inverseOrbitCoordinates
  rw [← congrFun (coordinates_map B f _) i]
  have h := map_act ρ f (g⁻¹ : GroupPoints P.group.val R) (extendVector R b)
  change _ = act ρ S (s g⁻¹) _ at h
  rw [h, s.map_inv, hVec]
  rfl

/-- The inverse orbit coordinates are regular functions of the entries and
inverse determinant in the given closed matrix realization. -/
private theorem exists_orbit_coordinate_functions (P : SpecialLinearRealization k m)
    (ρ : Representation P.group.val I) (B : Matrix.GeneralLinearGroup I k) (b : I → k) :
    ∃ a : I → GLCoordinates k (Index.{u} m),
      ∀ (R : Type u) [CommRing R] [Algebra k R] (g : PointsIn P.realization R) (i : I),
        inverseOrbitCoordinates ρ B b (CommAlgCat.of k R) g i =
          glEvaluation (asMatrix P.realization R g) (a i) := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr P.group.prop.1
  obtain ⟨f, hf, he⟩ := matrixPresentation A.unop e P.realization
  choose a ha using fun i => hf (inverseOrbitCoordinates ρ B b A.unop e.hom i)
  refine ⟨a, fun R _ _ g i => ?_⟩
  let q := coordinateMap (k := k) (g ≫ e.inv)
  have hq : mapPoints q e.hom = g := by
    change (testSpec k).map q.op ≫ e.hom = g
    rw [coordinateMap_spec, Category.assoc, e.inv_hom_id, Category.comp_id]
  have h := inverseOrbitCoordinates_map ρ B b q e.hom i
  rw [hq, ← ha i] at h
  exact h.symm.trans (DFunLike.congr_fun (he R g).symm (a i))

/-- Clearing the coefficients of a regular matrix function gives a single
denominator valid on the integral matrix group at every polynomial prime. -/
private theorem exists_finite_place_denominator {F : Type u} [Field F]
    (a : GLCoordinates F⟮X⟯ (Index.{u} m)) :
    ∃ d : F⟮X⟯, d ≠ 0 ∧
      ∀ p : IsDedekindDomain.HeightOneSpectrum F[X],
        let w := polynomialPlace F p
        letI : Algebra F⟮X⟯ w.Completion := w.embedding.toAlgebra
        ∀ M : Matrix.GeneralLinearGroup (Index.{u} m) w.integers,
          w.embedding d * glEvaluation
            (Matrix.GeneralLinearGroup.map w.integers.subtype M) a ∈ w.integers := by
  obtain ⟨P, n, hP⟩ := glEvaluation_fraction a
  obtain ⟨d, hd, Q, hQ⟩ := clearPolynomialDenominators (D := F[X]) P
  have hd' : algebraMap F[X] F⟮X⟯ d ≠ 0 :=
    fun h => hd (IsFractionRing.injective F[X] F⟮X⟯ (h.trans (map_zero _).symm))
  refine ⟨algebraMap _ _ d, hd', ?_⟩
  intro p w M
  letI : Algebra F⟮X⟯ w.Completion := w.embedding.toAlgebra
  let f : F[X] →+* w.Completion := w.embedding.comp (algebraMap F[X] F⟮X⟯)
  let N := Matrix.GeneralLinearGroup.map w.integers.subtype M
  have heval : MvPolynomial.eval₂ f (fun ij => N.val ij.1 ij.2) Q =
      f d * matrixEvaluation N.val P := by
    have h := congrArg (matrixEvaluation N.val) hQ
    rw [map_mul] at h
    change MvPolynomial.eval₂ w.embedding (fun ij => N.val ij.1 ij.2)
      (MvPolynomial.map (algebraMap F[X] F⟮X⟯) Q) =
      matrixEvaluation N.val (MvPolynomial.C (algebraMap F[X] F⟮X⟯ d)) *
        matrixEvaluation N.val P at h
    rw [MvPolynomial.eval₂_map] at h
    simp only [matrixEvaluation, MvPolynomial.aeval_C] at h
    exact h
  have hInt : MvPolynomial.eval₂ f (fun ij => N.val ij.1 ij.2) Q ∈ w.integers := by
    refine MvPolynomial.eval₂_mem (s := w.integers.toSubring) (fun i _ => ?_) (fun ij => ?_)
    · exact (FunctionPlace.embedding_mem_integers w _).mpr (p.valuation_le_one (Q.coeff i))
    · exact (M.val ij.1 ij.2).property
  have hdet : N⁻¹.val.det ∈ w.integers := by
    rw [show N⁻¹ = Matrix.GeneralLinearGroup.map w.integers.subtype M⁻¹ from map_inv _ _ |>.symm]
    change (w.integers.subtype.mapMatrix M⁻¹.val).det ∈ w.integers
    rw [← RingHom.map_det]
    exact (M⁻¹.val.det).property
  change f d * glEvaluation N a ∈ w.integers
  rw [hP w.Completion N, ← mul_assoc, ← heval]
  exact w.integers.toSubring.mul_mem hInt (w.integers.pow_mem hdet n)

end OrbitCoordinates

section NormalForms

open AlgebraicGeometry
open Specs.AdjointRepresentation (GroupPoints)
open Specs.FunctionFieldClosedOrbitWeights (DiagonalWeightCoordinates coordinates)
open Specs.RationalContraction (groundField)
open Specs.RationalFunctionSLAdelicReduction
  (SpecialLinearRealization baseFieldData pole adelicPlace localMatrix HasNormalForm)
open Specs.RootWeightAction (Representation act extendVector)
open Specs.SpecialLinearDatum (CocharacterLattice)
open Specs.StandardGroups (GLCoordinates)
open Specs.Unipotent (Index)
open Arithmetic.AdelicGroups
open LatticeCompletionDecompositionSpec (infinityField infinityEmbedding infinityNormedField)
open CocharacterDynamics (cocharacterPoint)
open private cocharacterPoint_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private act_mul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits
open private asMatrix_eq_toGL integralSpecial_iff polynomialPlace polynomialPlace_ne_pole
  mem_integral_iff completionEquivOfSubring completionEquivOfSubring_embedding
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RationalFunctionSLAdelicReduction
open private glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private continuous_glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open scoped Polynomial

variable {F I : Type u} [Field F] [Finite F] [Fintype I] [DecidableEq I] {m : ℕ}

local instance rationalCompletionField (w : (baseFieldData F).Place) :
    Field ((baseFieldData F).Completion w) :=
  GlobalFieldData.instFieldCompletion (baseFieldData F) w

local instance rationalCompletionTopology (w : (baseFieldData F).Place) :
    TopologicalSpace ((baseFieldData F).Completion w) :=
  GlobalFieldData.instTopologicalSpaceCompletion (baseFieldData F) w

local instance rationalCompletionAlgebra (w : (baseFieldData F).Place) :
    Algebra F⟮X⟯ ((baseFieldData F).Completion w) :=
  completionAlgebra (baseFieldData F) w

private abbrev poleComparison (F : Type u) [Field F] :
    (pole F).Completion ≃+* infinityField F := by
  classical
  exact completionEquivOfSubring (pole F) (RatFunc.inftyValuation F) rfl

private theorem poleComparison_embedding (F : Type u) [Field F] (x : F⟮X⟯) :
    poleComparison F ((pole F).embedding x) = infinityEmbedding F x := by
  classical
  exact completionEquivOfSubring_embedding (pole F) (RatFunc.inftyValuation F) rfl x

private theorem poleComparison_continuous (F : Type u) [Field F] [Finite F] :
    letI := infinityNormedField F
    Continuous (poleComparison F) := by
  classical
  letI := infinityNormedField F
  change Continuous (UniformSpace.Completion.map
    (WithVal.congr (pole F).val.valuation (RatFunc.inftyValuation F) (RingEquiv.refl F⟮X⟯)))
  exact UniformSpace.Completion.continuous_map

private abbrev completionTest (w : FunctionPlace F⟮X⟯) : TestAlgebra F⟮X⟯ :=
  letI : Algebra F⟮X⟯ w.Completion := w.embedding.toAlgebra
  CommAlgCat.of F⟮X⟯ w.Completion

/-- The coefficient-free part of the infinity estimate is bounded on the
compact subgroup of integral matrices. -/
private theorem inverseOrbit_pole_bound (P : SpecialLinearRealization F⟮X⟯ m)
    (ρ : Representation P.group.val I) (B : Matrix.GeneralLinearGroup I F⟮X⟯)
    (b : I → F⟮X⟯) (a : I → GLCoordinates F⟮X⟯ (Index.{u} m))
    (ha : ∀ (R : Type u) [CommRing R] [Algebra F⟮X⟯ R] (g : PointsIn P.realization R) (i : I),
      inverseOrbitCoordinates ρ B b (CommAlgCat.of F⟮X⟯ R) g i =
        glEvaluation (asMatrix P.realization R g) (a i)) :
    letI := infinityNormedField F
    ∃ C : I → ℝ, ∀ i (g : LocalPoints (baseFieldData F) P.realization (.inl (pole F))),
      g ∈ integralPoints (baseFieldData F) P.realization (pole F) →
      ‖poleComparison F (inverseOrbitCoordinates ρ B b (completionTest (pole F)) g i)‖ ≤ C i := by
  letI := infinityNormedField F
  let D := baseFieldData F
  let w := pole F
  letI : Algebra F⟮X⟯ w.Completion := w.embedding.toAlgebra
  have h (i : I) : Continuous (fun g : PointsIn P.realization w.Completion =>
      poleComparison F (inverseOrbitCoordinates ρ B b (completionTest w) g i)) := by
    simp_rw [ha w.Completion]
    have hMatrix : Continuous (asMatrix P.realization w.Completion) := continuous_induced_dom
    exact (poleComparison_continuous F).comp
      ((continuous_glEvaluation (a i)).comp hMatrix)
  choose C hC using fun i =>
    (integralCompactOpen D P.realization w).1.exists_bound_of_continuousOn (h i).continuousOn
  exact ⟨C, hC⟩

/-- Left multiplication by an adelic point fixing the vector preserves the
inverse orbit coordinates of the reducing rational point at every place. -/
private theorem inverseOrbit_reduction_at_place (P : SpecialLinearRealization F⟮X⟯ m)
    (ρ : Representation P.group.val I) (B : Matrix.GeneralLinearGroup I F⟮X⟯)
    (b : I → F⟮X⟯) (g : Adeles (baseFieldData F) P.realization ∅)
    (p : RationalPoints P.group) (w : FunctionPlace F⟮X⟯)
    (hfix : act ρ (completionTest w) (g (adelicPlace w))⁻¹
      (extendVector (completionTest w) b) = extendVector (completionTest w) b)
    (i : I) :
    w.embedding (inverseOrbitCoordinates ρ B b (groundField F⟮X⟯) p i) =
      inverseOrbitCoordinates ρ B b (completionTest w)
        ((g * AdelicGroups.diagonal (baseFieldData F) P.realization ∅ p) (adelicPlace w)) i := by
  let R := completionTest w
  letI : Algebra F⟮X⟯ w.Completion := w.embedding.toAlgebra
  let f : groundField F⟮X⟯ ⟶ R := CommAlgCat.ofHom (Algebra.ofId F⟮X⟯ w.Completion)
  have h := inverseOrbitCoordinates_map ρ B b f p i
  refine h.trans ?_
  let g₀ : GroupPoints P.group.val R := g (adelicPlace w)
  let p₀ : GroupPoints P.group.val R := mapPoints f p
  change inverseOrbitCoordinates ρ B b R p₀ i = inverseOrbitCoordinates ρ B b R (g₀ * p₀) i
  change act ρ R g₀⁻¹ (extendVector R b) = extendVector R b at hfix
  unfold inverseOrbitCoordinates
  rw [mul_inv_rev, act_mul, hfix]

/-- For a determinant-one normal form at the pole, the norm of the inverse
orbit coordinate is multiplied by the inverse of the corresponding weight. -/
private theorem inverseOrbit_pole_normal_form (P : SpecialLinearRealization F⟮X⟯ m)
    (ρ : Representation P.group.val I) (W : DiagonalWeightCoordinates P.specialPoints ρ)
    (b : I → F⟮X⟯) (g : Adeles (baseFieldData F) P.realization ∅) (n : CocharacterLattice m)
    (h : HasNormalForm P g (fun j => n.val j.down)) :
    letI := infinityNormedField F
    ∃ k : LocalPoints (baseFieldData F) P.realization (.inl (pole F)),
      k ∈ integralPoints (baseFieldData F) P.realization (pole F) ∧
      ∀ i, ‖poleComparison F
        (inverseOrbitCoordinates ρ W.changeBasis b (completionTest (pole F)) (g (adelicPlace (pole F))) i)‖ =
        ‖poleComparison F (inverseOrbitCoordinates ρ W.changeBasis b (completionTest (pole F)) k i)‖ *
          (Nat.card F : ℝ) ^ (-W.weight i n : ℤ) := by
  letI := infinityNormedField F
  let w := pole F
  let R := completionTest w
  letI : Algebra F⟮X⟯ w.Completion := w.embedding.toAlgebra
  obtain ⟨k₀, hk₀⟩ := h.2
  let e : GroupPoints P.group.val R ≃* Matrix.SpecialLinearGroup (Index.{u} m) w.Completion :=
    (P.specialPoints.app R).groupIsoToMulEquiv
  let k : LocalPoints (baseFieldData F) P.realization (.inl w) :=
    e.symm (Matrix.SpecialLinearGroup.map w.integers.subtype k₀)
  have hAs : asMatrix P.realization w.Completion k = Matrix.SpecialLinearGroup.toGL (e k) :=
    asMatrix_eq_toGL P k
  have hk : k ∈ integralPoints (baseFieldData F) P.realization w := by
    change asMatrix P.realization w.Completion k ∈
      (Matrix.GeneralLinearGroup.map w.integers.subtype).range
    rw [hAs]
    exact (integralSpecial_iff w.integers.toSubring (e k)).mp
      ⟨k₀, e.apply_symm_apply _ |>.symm⟩
  let t : w.Completionˣ :=
    Units.mk0 (w.embedding RatFunc.X) ((map_ne_zero w.embedding).2 RatFunc.X_ne_zero)
  let c : GroupPoints P.group.val R := cocharacterPoint (W.cocharacter n) R t
  let k' : GroupPoints P.group.val R := k
  let g₀ : GroupPoints P.group.val R := g (adelicPlace w)
  have hmul : g₀ = k' * c := by
    apply e.injective
    rw [map_mul]
    apply Subtype.ext
    change (localMatrix P g w).val = (e k).val * (e c).val
    rw [hk₀, show e k = Matrix.SpecialLinearGroup.map w.integers.subtype k₀ from
      e.apply_symm_apply _]
    change _ = _ * (P.specialPoints.hom.app R c).val
    rw [W.cocharacter_matrix]
    simp only [Units.val_zpow_eq_zpow_val, t, Units.val_mk0, w]
  refine ⟨k, hk, fun i => ?_⟩
  change ‖poleComparison F (inverseOrbitCoordinates ρ W.changeBasis b R g₀ i)‖ = _
  rw [hmul, inverseOrbitCoordinates, mul_inv_rev, act_mul, ← cocharacterPoint_inv,
    W.cocharacter_action, map_mul, norm_mul]
  have ht : ‖poleComparison F (t.val : w.Completion)‖ = (Nat.card F : ℝ) := by
    change ‖poleComparison F (w.embedding RatFunc.X)‖ = _
    rw [poleComparison_embedding, LatticeCompletionDecomposition.functionInfinityBaseNorm F _ RatFunc.X_ne_zero,
      RatFunc.intDegree_X, zpow_one]
  rw [mul_comm, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, map_zpow₀, map_inv₀,
    norm_zpow, norm_inv, ht, inv_zpow']
  rfl

/-- The resulting uniform denominators and weight estimates apply to every
normal form obtained by right multiplication by a rational point. -/
private theorem inverseOrbit_normal_form_bounds (P : SpecialLinearRealization F⟮X⟯ m)
    (ρ : Representation P.group.val I) (W : DiagonalWeightCoordinates P.specialPoints ρ)
    (b : I → F⟮X⟯) :
    letI := infinityNormedField F
    ∃ (d : I → F⟮X⟯) (C : I → ℝ), (∀ i, d i ≠ 0) ∧
      ∀ (g : Adeles (baseFieldData F) P.realization ∅) (p : RationalPoints P.group)
        (n : CocharacterLattice m),
        (∀ w : FunctionPlace F⟮X⟯, act ρ (completionTest w) (g (adelicPlace w))⁻¹
          (extendVector (completionTest w) b) = extendVector (completionTest w) b) →
        HasNormalForm P (g * AdelicGroups.diagonal (baseFieldData F) P.realization ∅ p)
          (fun j => n.val j.down) →
        (∀ i (v : IsDedekindDomain.HeightOneSpectrum F[X]),
          v.valuation F⟮X⟯ (d i * inverseOrbitCoordinates ρ W.changeBasis b (groundField F⟮X⟯) p i) ≤ 1) ∧
        ∀ i, ‖infinityEmbedding F (inverseOrbitCoordinates ρ W.changeBasis b (groundField F⟮X⟯) p i)‖
          ≤ C i * (Nat.card F : ℝ) ^ (-W.weight i n : ℤ) := by
  letI := infinityNormedField F
  obtain ⟨a, ha⟩ := exists_orbit_coordinate_functions P ρ W.changeBasis b
  choose d hd hdint using fun i => exists_finite_place_denominator (a i)
  obtain ⟨C, hC⟩ := inverseOrbit_pole_bound P ρ W.changeBasis b a ha
  refine ⟨d, C, hd, fun g p n hfix hnormal => ⟨?_, ?_⟩⟩
  · intro i v
    let w := polynomialPlace F v
    let y := g * AdelicGroups.diagonal (baseFieldData F) P.realization ∅ p
    letI : Algebra F⟮X⟯ w.Completion := w.embedding.toAlgebra
    obtain ⟨M, hM⟩ := (mem_integral_iff P y w).mpr (hnormal.1 w (polynomialPlace_ne_pole v))
    change Matrix.GeneralLinearGroup.map w.integers.subtype M =
      asMatrix P.realization w.Completion (y (adelicPlace w)) at hM
    change (d i * inverseOrbitCoordinates ρ W.changeBasis b (groundField F⟮X⟯) p i) ∈ w.val
    apply (FunctionPlace.embedding_mem_integers w _).mp
    rw [map_mul, inverseOrbit_reduction_at_place P ρ W.changeBasis b g p w (hfix w),
      ha w.Completion, ← hM]
    exact hdint i v M
  · intro i
    obtain ⟨k, hk, he⟩ := inverseOrbit_pole_normal_form P ρ W b _ n hnormal
    rw [← poleComparison_embedding,
      inverseOrbit_reduction_at_place P ρ W.changeBasis b g p (pole F) (hfix (pole F)),
      he i]
    exact mul_le_mul_of_nonneg_right (hC i k hk) (zpow_nonneg (by positivity) _)

end NormalForms

section RationalCompactness

open AlgebraicGeometry CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators Polynomial
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ClosedHomogeneousOrbits (vectorPoint)
open Specs.FunctionFieldClosedOrbitWeights (coordinates HasNoPositiveRankSplitTorus)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.IntegralModels (MatrixRealization)
open Specs.RationalContraction (groundField)
open Specs.RationalFunctionSLAdelicReduction (SpecialLinearRealization baseFieldData adelicPlace HasNormalForm)
open Specs.RootWeightAction (act extendVector)
open Specs.SpecialLinearDatum (CocharacterLattice sumExponents)
open Specs.Unipotent (Index closedSubgroupAlgebraicGroup)
open Arithmetic.AdelicGroups
open LatticeCompletionDecompositionSpec (infinityEmbedding infinityNormedField)
open private adelesTopology quotientTopology from
  MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness
open private vectorPoint_bijective map_vectorPoint act_one act_mul from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits
open private coordinates_inverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FunctionFieldClosedOrbitWeights

variable {F : Type u} [Field F] [Finite F] {m : ℕ}

private theorem sum_cocharacter_exponents (n : CocharacterLattice m) :
    (∑ j : Index.{u} m, n.val j.down) = 0 := by
  calc
    _ = ∑ j : Fin m, n.val j :=
      Fintype.sum_equiv (Equiv.ulift : Index.{u} m ≃ Fin m) _ _ (fun _ => rfl)
    _ = 0 := by
      simpa only [sumExponents, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply] using n.2

private theorem exists_normal_form (P : SpecialLinearRealization F⟮X⟯ m)
    (g : Adeles (baseFieldData F) P.realization ∅) :
    ∃ (p : RationalPoints P.group) (n : CocharacterLattice m),
      HasNormalForm P (g * AdelicGroups.diagonal (baseFieldData F) P.realization ∅ p)
        (fun j => n.val j.down) := by
  obtain ⟨p, δ, a, hδ, _, ha, hn⟩ := RationalFunctionSLAdelicReduction.orderedReduction P g
  have hδ' : δ = AdelicGroups.diagonal (baseFieldData F) P.realization ∅ (P.rationalPoint p) :=
    RestrictedProduct.ext _ _ hδ
  have hs : (∑ j : Fin m, a (ULift.up j)) = 0 := by
    exact (Fintype.sum_equiv (Equiv.ulift : Index.{u} m ≃ Fin m).symm
      _ _ (fun _ => rfl)).trans ha
  let n : CocharacterLattice m :=
    ⟨fun j => a (ULift.up j), by
      simpa only [sumExponents, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply] using hs⟩
  exact ⟨P.rationalPoint p, n, hδ' ▸ hn⟩

/-- The closed orbit and its weight coordinates yield compact coset
representatives for a semisimple anisotropic subgroup of special linear matrices. -/
private theorem compactness_of_closed_special_linear_subgroup
    (P : SpecialLinearRealization F⟮X⟯ m) (H : Specs.ClosedSubgroup P.group.val)
    (hsemi : IsSemisimple (closedSubgroupAlgebraicGroup H))
    (haniso : HasNoPositiveRankSplitTorus H.group) :
    @CompactSpace (AdelicQuotient (baseFieldData F) (P.subgroupRealization H))
      (quotientTopology (baseFieldData F) (P.subgroupRealization H)) := by
  classical
  let k := F⟮X⟯
  let D := baseFieldData F
  let jH := P.subgroupRealization H
  let jP := P.realization
  letI := adelesTopology D jH
  letI := adelesTopology D jP
  letI : IsTopologicalGroup (Adeles D jP ∅) := AdelicGroups.adelicTopology D jP ∅
  letI : Fact (ringChar F).Prime := ⟨CharP.prime_ringChar F⟩
  letI : CharP k (ringChar F) := inferInstanceAs (CharP F⟮X⟯ (ringChar F))
  obtain ⟨Q, I, hI, hDec, ρ, a, _, j, W, v, _, _, _, _, hAction, _, hproj, hstab, hv, hlimit⟩ :=
    FunctionFieldClosedOrbitWeights.closedOrbitWeightCriterion k (ringChar F) m
      P.group P.specialPoints H hsemi
  letI := hI
  letI := hDec
  letI := infinityNormedField F
  let b := v 1
  let x := η[P.group.val.X] ≫ Q.projection ≫ j
  have hb : vectorPoint (groundField k) b = toUnit _ ≫ x := by
    dsimp only [b]
    rw [hv, inv_one]
    change (toUnit _ ≫ η[P.group.val.X]) ≫ Q.projection ≫ j = toUnit _ ≫ x
    simp only [x, Category.assoc]
  have hbR (R : TestAlgebra k) : vectorPoint R (extendVector R b) = toUnit _ ≫ x := by
    let f : groundField k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have h := congrArg (mapPoints f) hb
    rw [map_vectorPoint] at h
    change vectorPoint R (extendVector R b) =
      (testSpec k).map f.op ≫ toUnit _ ≫ x at h
    rwa [comp_toUnit_assoc] at h
  have hfix (R : TestAlgebra k) (s : GroupPoints H.group R) :
      act ρ R (s ≫ H.inclusion.hom.hom) (extendVector R b) = extendVector R b := by
    apply (vectorPoint_bijective R).1
    rw [← hAction, hbR]
    exact (hstab _ _).mpr ⟨s, rfl⟩
  have hvAct (p : RationalPoints P.group) :
      v p = act ρ (groundField k) p⁻¹ (extendVector (groundField k) b) := by
    apply (vectorPoint_bijective (groundField k)).1
    rw [hv, ← hAction, hbR, hproj, Specs.SmoothOrbit.orbitMap,
      comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
    rfl
  let orbit := inverseOrbitCoordinates ρ W.changeBasis b (groundField k)
  have horbit (p : RationalPoints P.group) : orbit p = coordinates W.changeBasis (groundField k) (v p) :=
    congrArg (coordinates W.changeBasis (groundField k)) (hvAct p).symm
  have hcriterion (p : RationalPoints P.group) (n : CocharacterLattice m)
      (hn : ∀ i, orbit p i ≠ 0 → 0 ≤ W.weight i n) : n = 0 :=
    (hlimit p n (by simpa only [horbit p] using hn)).2 haniso
  obtain ⟨e, he, heLocal, heDiag⟩ := RationalFunctionSLAdelicReduction.adelicClosedSubgroupEmbedding P H
  let δ := AdelicGroups.diagonal D jP ∅
  let Γ := rationalDiagonal D jH
  have hstabRat (p q : RationalPoints P.group) (hpq : orbit p = orbit q) :
      δ (p * q⁻¹) ∈ Γ.map e := by
    have hvec := (Function.LeftInverse.injective (coordinates_inverse W.changeBasis (groundField k))) hpq
    have hAct : act ρ (groundField k) (p * q⁻¹) (extendVector (groundField k) b) =
        extendVector (groundField k) b := by
      rw [act_mul, ← hvec, ← act_mul, mul_inv_cancel, act_one]
    have hStabilizes : Stabilizes a.smul x (p * q⁻¹ : RationalPoints P.group) := by
      calc
        lift (p * q⁻¹ : GroupPoints P.group.val (groundField k)) (toUnit _ ≫ x) ≫ a.smul =
            lift (p * q⁻¹ : GroupPoints P.group.val (groundField k))
              (vectorPoint (groundField k) (extendVector (groundField k) b)) ≫ a.smul :=
          congrArg (fun y => lift (p * q⁻¹ : GroupPoints P.group.val (groundField k)) y ≫ a.smul)
            (hbR (groundField k)).symm
        _ = vectorPoint (groundField k)
            (act ρ (groundField k) (p * q⁻¹) (extendVector (groundField k) b)) := hAction _ _ _
        _ = vectorPoint (groundField k) (extendVector (groundField k) b) :=
          congrArg (vectorPoint (groundField k)) hAct
        _ = toUnit _ ≫ x := hbR (groundField k)
    obtain ⟨s, hs⟩ := (hstab _ _).mp hStabilizes
    let s' : RationalPoints (closedSubgroupAlgebraicGroup H) := s
    let dH := AdelicGroups.diagonal D jH ∅
    refine ⟨dH s', ⟨s', fun _ => rfl⟩, ?_⟩
    have h := DFunLike.congr_fun (heDiag AdelicGroups.diagonal AdelicGroups.diagonalCoordinates) s'
    exact h.trans (congrArg δ hs)
  let admissible (p : RationalPoints P.group) (n : CocharacterLattice m) : Prop :=
    ∃ g : Adeles D jH ∅, HasNormalForm P (e g * δ p) (fun j => n.val j.down)
  obtain ⟨d, C, hd, hBounds⟩ := inverseOrbit_normal_form_bounds P ρ W b
  have hEst (p : RationalPoints P.group) (n : CocharacterLattice m) (hn : admissible p n) :
      (∀ i (v : IsDedekindDomain.HeightOneSpectrum F[X]), v.valuation k (d i * orbit p i) ≤ 1) ∧
      ∀ i, ‖infinityEmbedding F (orbit p i)‖ ≤ C i * (Nat.card F : ℝ) ^ (-W.weight i n : ℤ) := by
    obtain ⟨g, hg⟩ := hn
    refine hBounds (e g) p n (fun w => ?_) hg
    let s : GroupPoints H.group (completionTest w) := g (adelicPlace w)
    let φ : GroupPoints H.group (completionTest w) →* GroupPoints P.group.val (completionTest w) :=
      (((groupPointsFunctor k).map H.inclusion).app (completionTest w)).hom
    have h := heLocal g (adelicPlace w)
    change (e g (adelicPlace w) : GroupPoints P.group.val (completionTest w)) = φ s at h
    rw [h, ← φ.map_inv s]
    exact hfix (completionTest w) s⁻¹
  obtain ⟨hE, V, hV, hmemV⟩ := finite_reduction_values admissible orbit W.weight d hd C
    (fun p n hn => (hEst p n hn).1) (fun p n hn => (hEst p n hn).2) hcriterion
  let E := (fun (n : CocharacterLattice m) (j : Index.{u} m) => n.val j.down) ''
    {n | ∃ p, admissible p n}
  obtain ⟨C', hC', hmemC⟩ := RationalFunctionSLAdelicReduction.compactNormalForms P E
    (hE.image _) (by rintro _ ⟨n, _, rfl⟩; exact sum_cocharacter_exponents n)
  refine compactSpace_of_finite_orbit_reduction e δ Γ orbit he hC' hV hstabRat ?_
  intro g
  obtain ⟨p, n, hn⟩ := exists_normal_form P (e g)
  exact ⟨p, hmemC _ _ ⟨n, ⟨p, g, hn⟩, rfl⟩ hn, hmemV p n ⟨g, hn⟩⟩

/-- An arbitrary closed matrix realization gives the same full adelic
quotient as the realization through the determinant-one group. -/
private theorem rationalFunctionFieldCompactness (F : Type u) [Field F] [Finite F]
    (G : Specs.AffineAlgebraicGroup F⟮X⟯) (i : MatrixRealization G)
    (hsemi : IsSemisimple G) (haniso : IsAnisotropic G) :
    @CompactSpace (AdelicQuotient (baseFieldData F) i) (quotientTopology (baseFieldData F) i) := by
  let D := baseFieldData F
  obtain ⟨P⟩ := RationalFunctionSLAdelicReduction.standardMatrixRealization F⟮X⟯ i.size
  obtain ⟨f, hf⟩ := exists_specialLinear_embedding G i hsemi P
  let H : Specs.ClosedSubgroup P.group.val := ⟨G.val, f, hf⟩
  let j : MatrixRealization G := P.subgroupRealization H
  letI := adelesTopology D j
  letI := adelesTopology D i
  let E := AdelicGroups.changeRealization D j i ∅
  have hE (a : Adeles D j ∅) : E a ∈ rationalDiagonal D i ↔ a ∈ rationalDiagonal D j := by
    constructor <;> rintro ⟨p, hp⟩ <;> exact ⟨p, fun w => hp w⟩
  letI := compactness_of_closed_special_linear_subgroup P H hsemi haniso
  exact (rightCosetHomeomorph E (rationalDiagonal D j) (rationalDiagonal D i) hE).compactSpace

/-- The full adelic right quotient of a semisimple anisotropic group over a
global function field is compact. -/
theorem functionFieldCompactness : FunctionFieldCompactness.{u, v} :=
  functionFieldCompactness_of_weilComparison weilRestrictionComparison rationalFunctionFieldCompactness

end RationalCompactness

end LinearAlgebraicGroups.Arithmetic.FunctionFieldAnisotropicCompactness
