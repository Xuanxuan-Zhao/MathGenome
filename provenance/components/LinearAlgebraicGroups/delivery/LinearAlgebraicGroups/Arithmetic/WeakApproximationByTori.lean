import Specs.LinearAlgebraicGroups.Arithmetic.WeakApproximationByTori
import LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import LinearAlgebraicGroups.Arithmetic.AdditiveStrongApproximation
import LinearAlgebraicGroups.Arithmetic.WeakApproximationTorusParameters
import LinearAlgebraicGroups.Arithmetic.WeakApproximationLocalSmoothImage
import LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
import LinearAlgebraicGroups.Flag.TorsorObstruction
import LinearAlgebraicGroups.Solvable.AffineAdditiveTorsors
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.GroupTheory.OrderOfElement
import Batteries.Tactic.OpenPrivate

open Set Topology Filter AlgebraicGeometry CategoryTheory IsDedekindDomain
open scoped NumberField RestrictedProduct CategoryTheory.MonObj CategoryTheory.GrpObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.WeakApproximationByTori

open AdelicGroups ArithmeticLatticeProjection
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.Specs.IntegralModels (RationalPoints)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)
open private insideProjection insideProjection_continuous splitAdeles
  cosetMap continuous_cosetMap surjective_cosetMap
  from LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

noncomputable section
set_option linter.style.haveILetI false

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
variable (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (T : Finset D.Place)

/-- Group structure on the closure of the diagonal image. -/
private def closureSubgroup : Subgroup (FinitePoints D i T) :=
  (rationalProjection D i T).range.topologicalClosure

private theorem closureSubgroup_coe :
    (closureSubgroup D i T : Set (FinitePoints D i T)) = diagonalClosure D i T := rfl

/-- A finite-product factor sends the identity component into the open diagonal closure. -/
theorem factor_connectedComponent_mem (h : IsOpen (diagonalClosure D i T))
    (w : (↑T : Set D.Place)) {x : LocalPoints D i w.1}
    (hx : x ∈ connectedComponent 1) :
    factor D i T w x ∈ diagonalClosure D i T := by
  classical
  have hc : Continuous (factor D i T w) :=
    continuous_mulSingle (A := fun z : (↑T : Set D.Place) => LocalPoints D i z.1) w
  let H := closureSubgroup D i T
  have hclosed : IsClosed (diagonalClosure D i T) := isClosed_closure
  have hclopen : IsClopen (diagonalClosure D i T) := ⟨hclosed, h⟩
  refine hclopen.connectedComponent_subset ?_ (hc.mapsTo_connectedComponent 1 hx)
  rw [map_one, ← closureSubgroup_coe]
  exact H.one_mem

/-- Compactness descends to the quotient by the finite diagonal closure. -/
theorem compact_quotient_diagonalClosure
    [CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i)] :
    CompactSpace (FinitePoints D i T ⧸ closureSubgroup D i T) := by
  let H := closureSubgroup D i T
  let f := insideProjection D i T
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x, hx⟩ := (splitAdeles D i T).surjective (a, 1)
    exact ⟨x, congrArg Prod.fst hx⟩
  have h : diagonalSubgroup D i ≤ H.comap f := by
    rintro x ⟨g, hg⟩
    apply Subgroup.le_topologicalClosure
    exact ⟨g, funext fun w => (hg ⟨w.1, by simp⟩).symm⟩
  exact (surjective_cosetMap f h hf).compactSpace
    (continuous_cosetMap f h (insideProjection_continuous D i T))

theorem finiteIndex_diagonalClosure_of_open (h : IsOpen (diagonalClosure D i T))
    [CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i)] :
    ∃ H : Subgroup (FinitePoints D i T),
      (H : Set _) = diagonalClosure D i T ∧ H.FiniteIndex := by
  let H := closureSubgroup D i T
  letI : CompactSpace (FinitePoints D i T ⧸ H) := compact_quotient_diagonalClosure D i T
  letI : DiscreteTopology (FinitePoints D i T ⧸ H) := QuotientGroup.discreteTopology h
  letI : Finite (FinitePoints D i T ⧸ H) := finite_of_compact_of_discrete
  exact ⟨H, closureSubgroup_coe D i T, H.finiteIndex_of_finite_quotient⟩

/-- A subgroup with roots of all positive orders acts trivially on any finite coset space
of the ambient group. -/
theorem le_of_pow_surjective_of_finiteIndex {P : Type*} [Group P]
    (H L : Subgroup P) [H.FiniteIndex]
    (hL : ∀ n : ℕ, 0 < n → Function.Surjective (fun x : L => x ^ n)) :
    L ≤ H := by
  let ρ := MulAction.toPermHom P (P ⧸ H)
  intro x hx
  obtain ⟨y, hy⟩ := hL (Nat.card (Equiv.Perm (P ⧸ H))) Nat.card_pos ⟨x, hx⟩
  have hx' : ρ x = 1 := by
    have he : (y : P) ^ Nat.card (Equiv.Perm (P ⧸ H)) = x := congrArg Subtype.val hy
    rw [← he, map_pow, pow_card_eq_one']
  apply H.normalCore_le
  rwa [H.normalCore_eq_ker]

theorem range_le_of_pow_surjective_of_finiteIndex {P A : Type*} [Group P] [Group A]
    (H : Subgroup P) [H.FiniteIndex] (f : A →* P)
    (hA : ∀ n : ℕ, 0 < n → Function.Surjective (fun x : A => x ^ n)) :
    f.range ≤ H := by
  apply le_of_pow_surjective_of_finiteIndex
  intro n hn x
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := hA n hn a
  refine ⟨⟨f b, ⟨b, rfl⟩⟩, Subtype.ext ?_⟩
  change f b ^ n = x.val
  change b ^ n = a at hb
  rw [← map_pow, hb, ha]

private theorem infinite_numberFinitePlace (K : Type u) [Field K] [NumberField K] :
    Infinite (NumberFinitePlace K) := by
  classical
  let Z (p : {p : ℕ // Nat.Prime p}) : Ideal ℤ := Ideal.span {(p.1 : ℤ)}
  have hnorm (p : {p : ℕ // Nat.Prime p}) : Ideal.absNorm (Z p) = p.1 := by
    change Nat.card (ℤ ⧸ Z p) = p.1
    exact Int.card_ideal_quot p.1
  have choose (p : {p : ℕ // Nat.Prime p}) :
      ∃ w : NumberFinitePlace K, w.asIdeal.under ℤ = Z p := by
    letI : Fact p.1.Prime := ⟨p.2⟩
    letI : (Z p).IsMaximal := Int.ideal_span_isMaximal_of_prime p.1
    have hZ : Z p ≠ ⊥ := by
      intro h
      exact p.2.ne_zero (((Ideal.absNorm_bot (S := ℤ)).symm.trans
        ((congrArg Ideal.absNorm h).symm.trans (hnorm p))).symm)
    obtain ⟨Q, hQ, hL⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (Z p)
    have he : Q.under ℤ = Z p := (Ideal.liesOver_iff _ _).mp hL |>.symm
    have neBot : Q ≠ ⊥ := by
      intro hb
      have hn : (⊥ : Ideal (𝓞 K)).under ℤ = ⊥ := by
        change (⊥ : Ideal (𝓞 K)).comap (algebraMap ℤ (𝓞 K)) = ⊥
        rw [← RingHom.ker_eq_comap_bot]
        exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
      exact hZ (he.symm.trans (hb ▸ hn))
    exact ⟨⟨Q, hQ.isPrime, neBot⟩, he⟩
  let f (p : {p : ℕ // Nat.Prime p}) : NumberFinitePlace K := (choose p).choose
  haveI : Infinite {p : ℕ // Nat.Prime p} := Nat.infinite_setOfPred_prime.to_subtype
  refine Infinite.of_injective f fun p q h => Subtype.ext ?_
  have hZ : Z p = Z q :=
    (choose p).choose_spec.symm.trans
      ((congrArg (fun w : NumberFinitePlace K => w.asIdeal.under ℤ) h).trans (choose q).choose_spec)
  exact (hnorm p).symm.trans ((congrArg Ideal.absNorm hZ).trans (hnorm q))

/-- The scalar diagonal is dense in each finite product of completions,
by projection from the restricted product with a further place omitted. -/
theorem scalarFiniteDiagonal_dense (w₀ : D.Place) (hw₀ : w₀ ∉ T) :
    DenseRange (fun a : K => fun w : (↑T : Set D.Place) => D.embedding w.1 a) := by
  classical
  let S : Set D.Place := {w₀}
  let emb (w : (↑T : Set D.Place)) : (Sᶜ : Set D.Place) :=
    ⟨w.1, fun h => hw₀ ((mem_singleton_iff.mp h) ▸ w.property)⟩
  let proj (a : D.AwayAdeleRing S) (w : (↑T : Set D.Place)) := a (emb w)
  have hc : Continuous proj := continuous_pi fun w => RestrictedProduct.continuous_eval
    (R := fun w : (Sᶜ : Set D.Place) => D.Completion w.1)
    (A := fun w => (D.localIntegerSubring w.1 : Set _)) (emb w)
  have hs : Function.Surjective proj := by
    intro x
    let a (w : (Sᶜ : Set D.Place)) : D.Completion w.1 :=
      if h : w.1 ∈ T then x ⟨w.1, h⟩ else 0
    refine ⟨⟨a, ?_⟩, funext fun w => dite_eq_left w.property⟩
    apply eventually_cofinite.mpr
    apply (T.finite_toSet.preimage Subtype.val_injective.injOn).subset
    intro w hw
    change w.1 ∈ T
    by_contra hn
    apply hw
    change a w ∈ D.localIntegerSubring w.1
    dsimp only [a]
    rw [dite_eq_right hn]
    exact (D.localIntegerSubring w.1).zero_mem
  have hd : DenseRange (D.awayDiagonal S) := by
    rw [DenseRange, D.range_awayDiagonal]
    exact additiveStrongApproximation D w₀
  exact hs.denseRange.comp hd hc

private def ScalarFiniteDiagonalDense {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (T : Finset D.Place) : Prop :=
  DenseRange (fun a : K => fun w : (↑T : Set D.Place) => D.embedding w.1 a)

private theorem numberScalarFiniteDiagonal_dense {K : Type u} [Field K] [NumberField K]
    (T : Finset (numberData.{u, v} K).Place) :
    ScalarFiniteDiagonalDense (numberData.{u, v} K) T := by
  classical
  let D : GlobalFieldData.{u, v} K := numberData K
  letI : Infinite D.FinitePlace := infinite_numberFinitePlace K
  let j : D.FinitePlace ↪ D.Place := ⟨Sum.inl, Sum.inl_injective⟩
  have hi : Infinite D.Place := Infinite.of_injective j j.injective
  obtain ⟨w, hw⟩ := T.exists_notMem
  exact scalarFiniteDiagonal_dense D T w hw

/-- Density of rational parameters transfers identity neighborhoods from the local maps. -/
private theorem open_of_dense_parameters {W A B : Type*} [Finite W] [Group B]
    {E L : W → Type*} [∀ w, TopologicalSpace (E w)] [∀ w, TopologicalSpace (L w)]
    [∀ w, Group (L w)] [∀ w, IsTopologicalGroup (L w)]
    (δ : B →* (∀ w, L w)) (Δ : A → ∀ w, E w) (hDense : DenseRange Δ)
    (U : ∀ w, Set (E w)) (hU : ∀ w, IsOpen (U w))
    (f : ∀ w, U w → L w) (hf : ∀ w, Continuous (f w))
    (himage : ∀ w, Set.range (f w) ∈ 𝓝 (1 : L w))
    (hcompat : ∀ (a : A) (ha : ∀ w, Δ a w ∈ U w),
      ∃ g : B, ∀ w, f w ⟨Δ a w, ha w⟩ = δ g w) :
    IsOpen (δ.range.topologicalClosure : Set (∀ w, L w)) := by
  classical
  let V := (univ : Set W).pi U
  have hopen : IsOpen V := isOpen_set_pi Set.finite_univ (fun w _ => hU w)
  let ev (w : W) (x : V) : U w := ⟨x.val w, x.property w trivial⟩
  let F (x : V) (w : W) := f w (ev w x)
  have hF : Continuous F := continuous_pi fun w =>
    (hf w).comp (((continuous_apply w).comp continuous_subtype_val).subtype_mk _)
  let I := (univ : Set W).pi (fun w => Set.range (f w))
  have hI : I ∈ 𝓝 (1 : ∀ w, L w) := set_pi_mem_nhds Set.finite_univ (fun w _ => himage w)
  have hIC : I ⊆ closure (Set.range δ) := by
    intro g hg
    have hgw (w : W) : g w ∈ Set.range (f w) := hg w trivial
    choose x hx using hgw
    let y : V := ⟨fun w => (x w).val, fun w _ => (x w).property⟩
    have hy : F y = g := funext hx
    apply mem_closure_iff.mpr
    intro O hO hgO
    let N : Set (∀ w, E w) := Subtype.val '' (F ⁻¹' O)
    have hN : IsOpen N := hopen.isOpenMap_subtype_val _ (hO.preimage hF)
    have hymem : F y ∈ O := by rwa [hy]
    obtain ⟨z, hzN, a, rfl⟩ :=
      hDense.inter_open_nonempty N hN ⟨y.val, y, hymem, rfl⟩
    obtain ⟨b, hbO, hba⟩ := hzN
    have hm : Δ a ∈ V := hba ▸ b.property
    obtain ⟨c, hc⟩ := hcompat a (fun w => hm w trivial)
    have hb : b = ⟨Δ a, hm⟩ := Subtype.ext hba
    refine ⟨F b, hbO, c, ?_⟩
    rw [hb]
    exact (funext hc).symm
  exact δ.range.topologicalClosure.isOpen_of_mem_nhds (Filter.mem_of_superset hI hIC)

private theorem denseRange_transpose {W J K : Type*} {F : W → Type*}
    [∀ w, TopologicalSpace (F w)] (d : ∀ w, K → F w)
    (h : DenseRange (fun x w => d w x)) :
    DenseRange (fun a : J → K => fun w j => d w (a j)) := by
  let transpose (a : J → ∀ w, F w) (w : W) (j : J) := a j w
  have hsurj : Function.Surjective transpose := fun a => ⟨fun j w => a w j, rfl⟩
  have hcont : Continuous transpose :=
    continuous_pi fun _ => continuous_pi fun _ => (continuous_apply _).comp (continuous_apply _)
  exact hsurj.denseRange.comp (DenseRange.piMap fun _ => h) hcont

section PrincipalOpen

open Opposite
open LinearAlgebraicGroups.Specs.StandardGroups (universalMatrix)
open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private matrixPresentation from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation_entry from LinearAlgebraicGroups.Affine.StandardGroups

variable {J : Type u} (p : MvPolynomial J K)

private abbrev principalOpen :=
  (testSpec K).obj (op (CommAlgCat.of K (Localization.Away p)))

private def principalParameters (R : Type u) [Field R] [Algebra K R] : Set (J → R) :=
  {a | MvPolynomial.aeval a p ≠ 0}

private def principalEval {R : Type u} [Field R] [Algebra K R]
    (a : principalParameters p R) : Localization.Away p →ₐ[K] R :=
  IsLocalization.Away.liftAlgHom p (f := MvPolynomial.aeval a.val) (isUnit_iff_ne_zero.mpr a.property)

private theorem principalEval_base {R : Type u} [Field R] [Algebra K R]
    (a : principalParameters p R) (c : MvPolynomial J K) :
    principalEval p a (algebraMap _ (Localization.Away p) c) = MvPolynomial.aeval a.val c :=
  IsLocalization.Away.lift_eq p (isUnit_iff_ne_zero.mpr a.property) c

private theorem continuous_parameterEval {R : Type u} [Field R] [Algebra K R]
    [TopologicalSpace R] [IsTopologicalRing R] (c : MvPolynomial J K) :
    Continuous (fun a : J → R => MvPolynomial.aeval a c) := by
  induction c using MvPolynomial.induction_on with
  | C x =>
    simp only [MvPolynomial.aeval_C]
    exact continuous_const
  | add c d hc hd =>
    simp only [map_add]
    exact hc.add hd
  | mul_X c j hc =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hc.mul (continuous_apply j)

private theorem continuous_principalEval {R : Type u} [Field R] [Algebra K R]
    [TopologicalSpace R] [IsTopologicalDivisionRing R] (c : Localization.Away p) :
    Continuous (fun a : principalParameters p R => principalEval p a c) := by
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj p c
  have he (a : principalParameters p R) :
      principalEval p a c = MvPolynomial.aeval a.val b / (MvPolynomial.aeval a.val p) ^ n := by
    have e := congrArg (principalEval p a) hb
    simp only [map_mul, map_pow, principalEval_base] at e
    exact (eq_div_iff (pow_ne_zero _ a.property)).2 e
  simp_rw [he]
  exact ((continuous_parameterEval b).comp continuous_subtype_val).div₀
    (((continuous_parameterEval p).comp continuous_subtype_val).pow n)
    (fun a => pow_ne_zero _ a.property)

private def principalPoint {R : Type u} [Field R] [Algebra K R]
    (a : principalParameters p R) : Points (principalOpen p) (CommAlgCat.of K R) :=
  (testSpec K).map (CommAlgCat.ofHom (principalEval p a)).op

private theorem principalPoint_surjective {R : Type u} [Field R] [Algebra K R] :
    Function.Surjective (principalPoint p (R := R)) := by
  intro y
  let q : Localization.Away p →ₐ[K] R := (coordinateMap y).hom
  let a (j : J) : R := q (algebraMap (MvPolynomial J K) (Localization.Away p) (MvPolynomial.X j))
  have hq (b : MvPolynomial J K) :
      MvPolynomial.aeval a b = q (algebraMap (MvPolynomial J K) (Localization.Away p) b) := by
    have hh : MvPolynomial.aeval a =
        q.comp (IsScalarTower.toAlgHom K (MvPolynomial J K) (Localization.Away p)) := by
      apply MvPolynomial.algHom_ext
      intro j
      exact MvPolynomial.aeval_X a j
    exact congrArg (fun f : MvPolynomial J K →ₐ[K] R => f b) hh
  have ha : a ∈ principalParameters p R := by
    change MvPolynomial.aeval a p ≠ 0
    rw [hq]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away p) p).map q).ne_zero
  have he : principalEval p ⟨a, ha⟩ = q := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers p)
    apply RingHom.ext
    intro b
    exact (principalEval_base p ⟨a, ha⟩ b).trans (hq b)
  refine ⟨⟨a, ha⟩, ?_⟩
  unfold principalPoint
  rw [he]
  exact coordinateMap_spec y

private theorem continuous_parameterPoint (f : principalOpen p ⟶ G.val.X) (w : D.Place) :
    let g : principalParameters p (D.Completion w) → LocalPoints D i w :=
      fun a => principalPoint p a ≫ f
    Continuous g := by
  dsimp only
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨b, _, hb⟩ := matrixPresentation A.unop e i
  let fstar := coordinateMap (f ≫ e.inv)
  let g (a : principalParameters p (D.Completion w)) : LocalPoints D i w := principalPoint p a ≫ f
  have hg (a : principalParameters p (D.Completion w)) :
      coordinateMap (g a ≫ e.inv) = fstar ≫ CommAlgCat.ofHom (principalEval p a) := by
    apply Quiver.Hom.op_inj
    apply (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of K)).map_injective
    rw [coordinateMap_spec, op_comp, Functor.map_comp, coordinateMap_spec]
    exact Category.assoc _ _ _
  apply (usualLocalTopology D i w).isInducing.continuous_iff.mpr
  refine continuous_matrix fun l m => ?_
  let c := fstar.hom (b.hom (universalMatrix K _ l m))
  have h (a : principalParameters p (D.Completion w)) :
      (asMatrix i (D.Completion w) (g a)).val l m = principalEval p a c := by
    rw [← glEvaluation_entry (k := K) (asMatrix i (D.Completion w) (g a)) l m, hb, hg]
    rfl
  change Continuous (fun a => (asMatrix i (D.Completion w) (g a)).val l m)
  simp_rw [h]
  exact continuous_principalEval p c

private theorem principalEval_natural {R S : Type u} [Field R] [Field S]
    [Algebra K R] [Algebra K S] (e : R →ₐ[K] S) (a : principalParameters p R)
    (b : principalParameters p S) (hb : ∀ j, b.val j = e (a.val j)) :
    e.comp (principalEval p a) = principalEval p b := by
  have he : e.comp (MvPolynomial.aeval a.val) = MvPolynomial.aeval b.val := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, hb]
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers p)
  apply RingHom.ext
  intro c
  change e (principalEval p a (algebraMap (MvPolynomial J K) (Localization.Away p) c)) =
    principalEval p b (algebraMap (MvPolynomial J K) (Localization.Away p) c)
  rw [principalEval_base, principalEval_base]
  exact congrArg (fun q : MvPolynomial J K →ₐ[K] S => q c) he

private def LocalPrincipalImage (f : principalOpen p ⟶ G.val.X) : Prop :=
  ∀ w : (↑T : Set D.Place),
    Set.range (fun x : Points (principalOpen p) (CommAlgCat.of K (D.Completion w.1)) =>
      (x ≫ f : LocalPoints D i w.1)) ∈ 𝓝 (1 : LocalPoints D i w.1)

/-- A principal affine parameter domain supplying local identity neighborhoods
implies openness in the finite product. -/
private theorem open_of_principalOpen (hscalar : ScalarFiniteDiagonalDense D T)
    (f : principalOpen p ⟶ G.val.X) (hlocal : LocalPrincipalImage D i T p f) :
    IsOpen (diagonalClosure D i T) := by
  classical
  let W := (↑T : Set D.Place)
  let e (w : W) : K →ₐ[K] D.Completion w.1 := Algebra.ofId K (D.Completion w.1)
  let Δ (a : J → K) (w : W) (j : J) := e w (a j)
  let U (w : W) := principalParameters p (D.Completion w.1)
  let F (w : W) (a : U w) : LocalPoints D i w.1 := principalPoint p a ≫ f
  have hU (w : W) : IsOpen (U w) := by
    change IsOpen ((fun a : J → D.Completion w.1 => MvPolynomial.aeval a p) ⁻¹' ({0}ᶜ))
    exact isClosed_singleton.isOpen_compl.preimage (continuous_parameterEval p)
  have hF (w : W) : Set.range (F w) ∈ 𝓝 (1 : LocalPoints D i w.1) := by
    let fR : Points (principalOpen p) (CommAlgCat.of K (D.Completion w.1)) →
        LocalPoints D i w.1 := fun x => x ≫ f
    have hr : Set.range (F w) = Set.range fR :=
      (principalPoint_surjective p (R := D.Completion w.1)).range_comp fR
    rw [hr]
    exact hlocal w
  have hΔ : DenseRange Δ := denseRange_transpose (fun w : W => e w) hscalar
  apply open_of_dense_parameters (rationalProjection D i T) Δ hΔ U hU F
    (fun w => continuous_parameterPoint D i p f w.1) hF
  intro a ha
  by_cases h : T.Nonempty
  · obtain ⟨w₀, hw₀⟩ := h
    let w : W := ⟨w₀, hw₀⟩
    have hAp : MvPolynomial.aeval a p ≠ 0 := by
      have hE : (e w).comp (MvPolynomial.aeval a) = MvPolynomial.aeval (Δ a w) := by
        apply MvPolynomial.algHom_ext
        simp [Δ]
      intro hzero
      apply (ha w)
      rw [← congrArg (fun q : MvPolynomial J K →ₐ[K] D.Completion w.1 => q p) hE]
      change e w (MvPolynomial.aeval a p) = 0
      rw [hzero, map_zero]
    let a₀ : principalParameters p K := ⟨a, hAp⟩
    refine ⟨principalPoint p a₀ ≫ f, ?_⟩
    intro w
    have hE := principalEval_natural p (e w) a₀ ⟨Δ a w, ha w⟩ (fun _ => rfl)
    change principalPoint p ⟨Δ a w, ha w⟩ ≫ f =
      (testSpec K).map (CommAlgCat.ofHom (e w)).op ≫ principalPoint p a₀ ≫ f
    rw [← Category.assoc]
    apply congrArg (· ≫ f)
    simp only [principalPoint]
    rw [← Functor.map_comp, ← op_comp]
    exact congrArg (fun f : Localization.Away p →ₐ[K] D.Completion w.1 =>
      (testSpec K).map (CommAlgCat.ofHom f).op) hE.symm
  · exact ⟨1, fun w => False.elim (h ⟨w.1, w.2⟩)⟩

end PrincipalOpen

section UnipotentRoots

open Opposite
open LinearAlgebraicGroups.Specs (ClosedSubgroup GroupScheme fppfOver schemeFppfSheaf)
open LinearAlgebraicGroups.Specs.Fppf (fieldBase fieldTest)
open LinearAlgebraicGroups.Specs.TorsorObstruction (FibreSection)
open LinearAlgebraicGroups.Specs (projectSection)
open LinearAlgebraicGroups.AdditiveDescent (additiveTorsorFieldSection)
open LinearAlgebraicGroups.TorsorObstruction (fibreTorsor)
open LinearAlgebraicGroups.Unipotent (faithfullyFlatQuotientsUnipotent)
open private identityDimension identityDimension_lt exists_central_additive_charZero central_normal
  sections_eq_one_of_trivial from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {k : Type u} [Field k]

/-- Spec of the ground field as a test object is the terminal object of the slice. -/
private def rationalTestIso (k : Type u) [Field k] :
    (testSpec k).obj (op (CommAlgCat.of k k)) ≅ fieldBase k :=
  have e : fieldBase k ≅ (testSpec k).obj (op (CommAlgCat.of k k)) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 (Spec (CommRingCat.of k))) ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
      rw [Category.id_comp]
      exact Spec.map_id (CommRingCat.of k))
  e.symm

/-- The quotient map by a central copy of the additive group lifts every rational point.
The fibre of the quotient sheaf is an additive torsor over the field. -/
private theorem additiveQuotient_surjective {U Q : AffineAlgebraicGroup k}
    (j : (StandardGroups.additiveGroup k).val ⟶ U.val)
    (hj : IsClosedImmersion j.hom.hom.left) (q : U.val ⟶ Q.val)
    (e : rightQuotientSheaf (⟨_, j, hj⟩ : ClosedSubgroup U.val) ≅ schemeFppfSheaf Q.val.X)
    (he : rightQuotientProjection (⟨_, j, hj⟩ : ClosedSubgroup U.val) ≫ e.hom =
      (fppfOver k).uliftYoneda.map q.hom.hom) :
    Function.Surjective (fun x : fieldBase k ⟶ U.val.X => x ≫ q.hom.hom) := by
  intro y
  let H : ClosedSubgroup U.val := ⟨_, j, hj⟩
  let b : (schemeFppfSheaf Q.val.X).obj.obj (op (fieldBase k)) := ULift.up y
  let x := e.inv.hom.app (op (fieldBase k)) b
  obtain ⟨p⟩ := additiveTorsorFieldSection (fibreTorsor H x)
  change FibreSection H x (fieldTest k) at p
  refine ⟨p.val.down, ?_⟩
  have hp : projectSection H p.val.down = x := by
    have hid : (Over.mkIdTerminal.from (fieldTest k)).left = 𝟙 (fieldBase k) :=
      congrArg Over.Hom.left (Over.mkIdTerminal.hom_ext
        (Over.mkIdTerminal.from (fieldTest k)) (𝟙 (fieldTest k)))
    have hmap : (rightQuotientSheaf H).obj.map
        (Over.mkIdTerminal.from (fieldTest k)).left.op x = x := by
      rw [hid]
      change (rightQuotientSheaf H).obj.map (𝟙 (op (fieldBase k))) x = x
      rw [(rightQuotientSheaf H).obj.map_id]
      rfl
    exact p.property.trans hmap
  have heval (g : fieldBase k ⟶ U.val.X) :
      e.hom.hom.app (op (fieldBase k)) (projectSection H g) = ULift.up (g ≫ q.hom.hom) :=
    congrArg (fun m => m.hom.app (op (fieldBase k)) (ULift.up g)) he
  have hy : e.hom.hom.app (op (fieldBase k)) x = b :=
    congrArg (fun m => m.hom.app (op (fieldBase k)) b) e.inv_hom_id
  exact congrArg ULift.down ((heval _).symm.trans ((congrArg _ hp).trans hy))

private theorem additive_rational_roots [CharZero k] {n : ℕ} (hn : 0 < n)
    (a : fieldBase k ⟶ (StandardGroups.additiveGroup k).val.X) :
    ∃ b : fieldBase k ⟶ (StandardGroups.additiveGroup k).val.X, b ^ n = a := by
  let R := CommAlgCat.of k k
  let E : Points (StandardGroups.additiveGroup k).val.X R ≃* Multiplicative k :=
    ((StandardGroups.additiveGroupPointsIso k).app R).groupIsoToMulEquiv
  let e := rationalTestIso k
  let x : Multiplicative k := E (e.hom ≫ a)
  let y : Multiplicative k := Multiplicative.ofAdd (x.toAdd / (n : k))
  have hy : y ^ n = x := by
    change n • (x.toAdd / (n : k)) = x.toAdd
    rw [nsmul_eq_mul, mul_div_cancel₀]
    exact_mod_cast hn.ne'
  refine ⟨e.inv ≫ E.symm y, ?_⟩
  rw [← MonObj.comp_pow, ← map_pow, hy]
  change e.inv ≫ E.symm (E (e.hom ≫ a)) = a
  simp

/-- Powers of every positive order are surjective on rational points of a unipotent
group in characteristic zero. Use a central additive kernel and induction on dimension. -/
private theorem unipotent_terminalRoots [CharZero k] (U : AffineAlgebraicGroup k)
    (hU : Specs.Unipotent.IsUnipotent U) (n : ℕ) (hn : 0 < n) :
    ∀ a : fieldBase k ⟶ U.val.X, ∃ b : fieldBase k ⟶ U.val.X, b ^ n = a := by
  suffices h : ∀ d : ℕ, ∀ U : AffineAlgebraicGroup k, identityDimension U = d →
      Specs.Unipotent.IsUnipotent U →
      ∀ a : fieldBase k ⟶ U.val.X, ∃ b : fieldBase k ⟶ U.val.X, b ^ n = a from
    h (identityDimension U) U rfl hU
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro U hdim hU a
    by_cases ht : Nonempty (U.val ≅ Grp.trivial (SchemeOver k))
    · exact ⟨1, (one_pow n).trans (sections_eq_one_of_trivial ht a).symm⟩
    obtain ⟨j, hj, hc⟩ := exists_central_additive_charZero U hU ht
    let H : ClosedSubgroup U.val := ⟨_, j, hj⟩
    obtain ⟨M, p, Q, q, f, _, hker, hfac, _, e, he⟩ :=
      LinearAlgebraicGroups.normalAffineQuotient U H (central_normal hc)
    letI : Flat q.hom.hom.left := hfac.2.1
    have hd : identityDimension Q < d := hdim ▸ identityDimension_lt q j hj hker
    have hQ := faithfullyFlatQuotientsUnipotent U Q q hfac.2.1 hfac.2.2.1 hU
    let σ := IsMonHom.monoidHom q.hom.hom (fieldBase k)
    obtain ⟨b, hb⟩ := ih _ hd Q rfl hQ (σ a)
    obtain ⟨y, hy⟩ := additiveQuotient_surjective j hj q e he b
    change σ y = b at hy
    have hmem : σ (a * (y ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hy, hb, mul_inv_cancel]
    obtain ⟨c, hec⟩ := (schemeKernel_sections hker (a * (y ^ n)⁻¹)).mpr hmem
    obtain ⟨t, ht⟩ := additive_rational_roots hn c
    let inc := IsMonHom.monoidHom j.hom.hom (fieldBase k)
    refine ⟨inc t * y, ?_⟩
    have hcomm : Commute (inc t) y := (hc (fieldBase k) y t).symm
    change inc c = a * (y ^ n)⁻¹ at hec
    rw [hcomm.mul_pow, ← map_pow, ht, hec, inv_mul_cancel_right]

theorem unipotent_rationalRoots [CharZero k] (U : AffineAlgebraicGroup k)
    (hU : Specs.Unipotent.IsUnipotent U) (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun a : RationalPoints U => a ^ n) := by
  intro a
  change Points U.val.X (CommAlgCat.of k k) at a
  let e := rationalTestIso k
  obtain ⟨b, hb⟩ := unipotent_terminalRoots U hU n hn (e.inv ≫ a)
  change ∃ y : Points U.val.X (CommAlgCat.of k k), y ^ n = a
  exact ⟨e.hom ≫ b, by rw [← MonObj.comp_pow, hb, ← Category.assoc, e.hom_inv_id, Category.id_comp]⟩

end UnipotentRoots

/-- In characteristic zero each unipotent radical has all positive roots,
so its image acts trivially on the cosets, as does the subgroup they generate. -/
private theorem localPlus_le_of_finiteIndex [CharZero K] (H : Subgroup (FinitePoints D i T))
    [H.FiniteIndex] (w : D.FinitePlace) (hw : Sum.inl w ∈ T) :
    (localPlus D i w).map (factor D i T ⟨.inl w, hw⟩) ≤ H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  rw [localPlus, Subgroup.closure_le]
  rintro g ⟨P, U, _, hU, x, rfl⟩
  let F := D.Completion (.inl w)
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let UU := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup P) U
  let incl : RationalPoints UU →* LocalPoints D i (.inl w) :=
    (baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)).toMonoidHom.comp
      (((groupPointsFunctor F).map (U.inclusion ≫ P.inclusion)).app (CommAlgCat.of F F)).hom
  let f := (factor D i T ⟨.inl w, hw⟩).comp incl
  exact range_le_of_pow_surjective_of_finiteIndex H f (unipotent_rationalRoots UU hU.2.1) ⟨x, rfl⟩

/-- The diagonal closure is open in the finite product. -/
theorem identityNeighborhood : Specs.WeakApproximationByTori.IdentityNeighborhood.{u, v} := by
  intro K _ _ G hG i T
  let D : GlobalFieldData.{u, v} K := numberData K
  obtain ⟨_, p, a, f, ha, hf⟩ :=
    WeakApproximationTorusParameters.smoothPointedParametrization G hG
  refine open_of_principalOpen D i T p (numberScalarFiniteDiagonal_dense T) f ?_
  intro w
  have hOne : localPoint D i w.1 (a ≫ f) = 1 :=
    (congrArg (localPoint D i w.1) ha).trans (map_one (localPoint D i w.1))
  exact hOne ▸ WeakApproximationLocalSmoothImage.localSmoothImage.{u, v} G hG.1 i p f hf a w.1

theorem archimedeanComponents : Specs.WeakApproximationByTori.ArchimedeanComponents.{u, v} := by
  intro K _ _ G hG i T w hw x hx
  exact factor_connectedComponent_mem (numberData K) i T
    (identityNeighborhood G hG i T) ⟨.inr w, hw⟩ hx

theorem finiteIndex : Specs.WeakApproximationByTori.FiniteIndex.{u, v} := by
  intro K _ _ G hG _ i T hc
  letI := hc
  exact finiteIndex_diagonalClosure_of_open (numberData K) i T (identityNeighborhood G hG i T)

theorem finitePlaceRadicals : Specs.WeakApproximationByTori.FinitePlaceRadicals.{u, v} := by
  intro K _ _ G hG ha i T hc w hw _
  obtain ⟨H, hH, hfin⟩ := finiteIndex G hG ha i T hc
  let D : GlobalFieldData.{u, v} K := numberData K
  letI := hfin
  rw [← hH]
  exact localPlus_le_of_finiteIndex D i T H w hw

end

end LinearAlgebraicGroups.Arithmetic.WeakApproximationByTori
