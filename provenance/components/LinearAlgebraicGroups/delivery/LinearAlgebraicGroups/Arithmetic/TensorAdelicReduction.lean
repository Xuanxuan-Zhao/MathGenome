import Specs.LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction
import LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
import LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals
import Batteries.Tactic.OpenPrivate

open scoped BigOperators NumberField Polynomial RatFunc LaurentSeries RestrictedProduct nonZeroDivisors WithZero
open IsDedekindDomain

namespace LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction

open AdelicLatticeBounds Filter Set

noncomputable section
open private coe_matrixLattice isLattice_matrixLattice from
  LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds

private theorem clearCoefficients {A K I : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (p : MvPolynomial I K) :
    ∃ (a : A⁰) (q : MvPolynomial I A),
      MvPolynomial.map (algebraMap A K) q = MvPolynomial.C (algebraMap A K (a : A)) * p := by
  classical
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples A⁰ p.support p.coeff
  have h (m : p.support) : ∃ r : A,
      algebraMap A K r = algebraMap A K (a : A) * p.coeff m := by
    have hh := ha m m.property
    change ∃ r : A, algebraMap A K r = (a : A) • p.coeff m at hh
    simpa only [Algebra.smul_def] using hh
  choose r hr using h
  refine ⟨a, ∑ m ∈ p.support.attach, MvPolynomial.monomial (m : I →₀ ℕ) (r m), ?_⟩
  rw [map_sum]
  simp only [MvPolynomial.map_monomial, hr]
  rw [p.support.sum_attach (fun m => MvPolynomial.monomial m
    (algebraMap A K (a : A) * p.coeff m))]
  calc
    _ = MvPolynomial.C (algebraMap A K (a : A)) *
        (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) := by
      simp only [Finset.mul_sum, MvPolynomial.C_mul_monomial]
    _ = _ := congrArg (MvPolynomial.C (algebraMap A K (a : A)) * ·) p.as_sum.symm

private theorem completedReference {A K I : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype I] [DecidableEq I]
    (v : HeightOneSpectrum A) :
    (completedLattice v (referenceLattice A K I) : Set (I → v.adicCompletion K)) =
      {x | ∀ i, x i ∈ v.adicCompletionIntegers K} := by
  unfold referenceLattice
  simpa only [map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, Set.image_id']
    using completedBasisLattice (1 : Matrix.GeneralLinearGroup I K) v

theorem integralInvariantPolynomials : Specs.TensorAdelicReduction.integralInvariantPolynomials := by
  classical
  intro A K I P _ _ _ _ _ _ _ p d hp
  choose a q hq using fun j => clearCoefficients (A := A) (p j)
  let pol := fun j => MvPolynomial.map (algebraMap A K) (q j)
  have ha (j : P) : algebraMap A K (a j : A) ≠ 0 :=
    fun h => (IsFractionRing.injective A K).ne
      (mem_nonZeroDivisors_iff_ne_zero.mp (a j).property) (h.trans (map_zero _).symm)
  refine ⟨pol, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(hp j).1, by
      rw [show pol j = _ from hq j]
      simpa using (MvPolynomial.isHomogeneous_C (σ := I) (algebraMap A K (a j : A))).mul (hp j).2⟩
  · intro j v x hx
    rw [SetLike.mem_coe.symm, completedReference] at hx
    let O := v.adicCompletionIntegers K
    let y : I → O := fun i => ⟨x i, hx i⟩
    change (MvPolynomial.map (algebraMap A K) (q j)).eval₂
      (algebraMap K (v.adicCompletion K)) x ∈ O
    rw [MvPolynomial.eval₂_map]
    let t : O := (q j).eval₂ (algebraMap A O) y
    have ht : (t : v.adicCompletion K) =
        (q j).eval₂ ((algebraMap K (v.adicCompletion K)).comp (algebraMap A K)) x := by
      rw [show ((algebraMap K (v.adicCompletion K)).comp (algebraMap A K)) =
          O.subtype.comp (algebraMap A O) by
            apply RingHom.ext
            intro z
            exact (IsScalarTower.algebraMap_apply A K (v.adicCompletion K) z).symm.trans
              (IsScalarTower.algebraMap_apply A O (v.adicCompletion K) z)]
      exact MvPolynomial.eval₂_comp_left O.subtype (algebraMap A O) y (q j)
    rw [← ht]
    exact t.property
  · intro j x
    change (MvPolynomial.map (algebraMap A K) (q j)).eval x = 0 ↔ _
    rw [hq, map_mul, MvPolynomial.eval_C]
    simp [ha]
  · intro J L _ e g h j w x
    change (MvPolynomial.map (algebraMap A K) (q j)).eval₂ _ _ =
      (MvPolynomial.map (algebraMap A K) (q j)).eval₂ _ _
    simp only [hq, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
    exact congrArg (fun y => e w (algebraMap A K (a j : A)) * y) (h j w x)

theorem transportedLattices : Specs.TensorAdelicReduction.transportedLattices := by
  intro A K I _ _ _ _ _ _ _ g Q
  have hQ (v : HeightOneSpectrum A) :
      (Q v : Set (I → v.adicCompletion K)) =
        (g v)⁻¹.val.mulVec '' {x | ∀ i, x i ∈ v.adicCompletionIntegers K} := by
    rw [show Q v = matrixLattice (g v)⁻¹ from rfl, coe_matrixLattice, basisVectors]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, fun i => (z i).property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨fun i => ⟨z i, hz i⟩, rfl⟩
  refine ⟨fun v => isLattice_matrixLattice (g v)⁻¹, ?_, ?_⟩
  · apply (Filter.eventually_cofinite.mp g.property).subset
    intro v hv hg
    apply hv
    apply SetLike.coe_injective
    rw [hQ, completedReference]
    exact (integralMatrixIffPreservesBox _ _).mp
      ((Matrix.GeneralLinearGroup.map (n := I) (v.adicCompletionIntegers K).subtype).range.inv_mem hg)
  · intro v
    rw [hQ, completedReference, Set.image_image]
    have hid : (g v).val.mulVec ∘ (g v)⁻¹.val.mulVec = id := by
      funext x
      change (g v).val.mulVec ((g v)⁻¹.val.mulVec x) = x
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    change ((g v).val.mulVec ∘ (g v)⁻¹.val.mulVec) '' _ = _
    rw [hid, Set.image_id]

theorem numberBoundedTensorBases : Specs.TensorAdelicReduction.numberBoundedTensorBases := by
  classical
  intro K I P _ _ _ _ _ p d hd h₀ N
  let L₀ := referenceLattice (𝓞 K) K I
  let : Submodule.IsLattice K L₀ := isLattice_matrixLattice _
  obtain ⟨q, hq, hInt, hZero, hInv⟩ := integralInvariantPolynomials (A := 𝓞 K) p d hd
  obtain ⟨b, a, E, hb, hE, _, _, C, _, _, hC, hreduce⟩ :=
    numberAdelicLatticeBounds L₀ q d hq hInt
  refine ⟨b, a, E, hb, hE, C, hC, ?_⟩
  intro g gInf hg hgInf hFin hInf
  let Q := fun v => transportedLattice v (g v)
  obtain ⟨hL, hQ, hImage⟩ := transportedLattices g
  let (v : NumberFinitePlace K) : Submodule.IsLattice (v.adicCompletion K) (Q v) := hL v
  have hAnis x (hx : x ≠ 0) : ∃ r, (q r).eval x ≠ 0 := by
    obtain ⟨r, hr⟩ := h₀ x hx
    exact ⟨r, fun he => hr ((hZero r x).mp he)⟩
  obtain ⟨_, _, _, hBasis⟩ := hreduce Q hQ
  obtain ⟨G, GInf, M, hI, hG, hDet, hAction, hM, hdM, _, _, _, _, _, hMem⟩ :=
    hBasis g gInf hg hImage hgInf (hInv _ g hFin) (hInv _ gInf hInf)
      (fun x _ hx => hAnis x hx)
  exact ⟨G, GInf, M, hI, hG, hDet, hAction, hM, hdM, hMem⟩

open LatticeCompletionDecompositionSpec in
theorem functionBoundedTensorBases : Specs.TensorAdelicReduction.functionBoundedTensorBases := by
  classical
  intro F K I P _ _ _ _ _ _ _ t p d hd h₀ N B J
  let (w : J) : Field w.val.Completion := inferInstance
  let L₀ := referenceLattice t.integerRing K I
  let : Submodule.IsLattice K L₀ := isLattice_matrixLattice _
  obtain ⟨q, hq, hInt, hZero, hInv⟩ :=
    integralInvariantPolynomials (A := t.integerRing) p d hd
  obtain ⟨b, a, E, e, h, hb, hE, he, hf, _, _, _, _, _, C, _, hC, hreduce⟩ :=
    functionAdelicLatticeBounds t L₀ q d hq hInt
  refine ⟨b, a, E, e, h, hb, hE, he, hf, C, hC, ?_⟩
  intro g gInf hg hgInf hFin hInf
  let Q := fun v => transportedLattice v (g v)
  obtain ⟨hL, hQ, hImage⟩ := transportedLattices g
  let (v : HeightOneSpectrum t.integerRing) :
      Submodule.IsLattice (v.adicCompletion K) (Q v) := hL v
  have hAnis x (hx : x ≠ 0) : ∃ r, (q r).eval x ≠ 0 := by
    obtain ⟨r, hr⟩ := h₀ x hx
    exact ⟨r, fun he => hr ((hZero r x).mp he)⟩
  obtain ⟨_, _, _, hBasis⟩ := hreduce Q hQ
  obtain ⟨G, GInf, M, hI, _, _, hG, hDet, hAction, hM, hdM, _, _, _, _, _, _, hBound⟩ :=
    hBasis g gInf hg hImage hgInf
  have hMem := (hBound (hInv _ g hFin) (hInv _ gInf hInf) (fun x _ hx => hAnis x hx)).2.2.2
  exact ⟨G, GInf, M, hI, hG, hDet, hAction, hM, hdM, hMem⟩

open private compactLocalBasisBox from LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds

theorem compactLocalMatrixTransport : Specs.TensorAdelicReduction.compactLocalMatrixTransport := by
  classical
  intro B I N J _ _ _ _ _ _ _ L _ _ _ _ _ E C hC
  let v (j : J) (i : I) : ∀ j, I → L j := Pi.single j (Pi.single i 1)
  let coord (j : J) (s t : I) (M : Matrix.GeneralLinearGroup N B) :=
    E (M.val.mulVec (E.symm (v j t))) j s
  have hCoord (j : J) (s t : I) : Continuous (coord j s t) := by
    have hMul : Continuous (fun M : Matrix.GeneralLinearGroup N B =>
        M.val.mulVec (E.symm (v j t))) := by
      apply continuous_pi
      intro n
      exact continuous_finsetSum _ fun a _ => ((continuous_apply a).comp
        (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id n)).mul continuous_const
    exact (continuous_apply s).comp ((continuous_apply j).comp (E.continuous.comp hMul))
  let D (j : J) : Set (L j) := ⋃ s : I, ⋃ t : I,
    (coord j s t '' C) ∪ (coord j s t '' ((fun M => M⁻¹) '' C))
  have hD (j : J) : IsCompact (D j) :=
    isCompact_iUnion fun s => isCompact_iUnion fun t =>
      (hC.image (hCoord j s t)).union ((hC.image continuous_inv).image (hCoord j s t))
  refine ⟨_, fun j => compactLocalBasisBox (D j) (hD j), ?_⟩
  intro M m hM h j
  have hInv (z : N → B) (w : J) : E (M⁻¹.val.mulVec z) w = (m w)⁻¹.val.mulVec (E z w) := by
    have he := h (M⁻¹.val.mulVec z) w
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at he
    rw [he, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have hEntry (M : Matrix.GeneralLinearGroup N B)
      (m : ∀ j, Matrix.GeneralLinearGroup I (L j))
      (h : ∀ z j, E (M.val.mulVec z) j = (m j).val.mulVec (E z j)) (s t : I) :
      coord j s t M = (m j).val s t := by
    dsimp only [coord]
    rw [h, E.apply_symm_apply]
    simp [v, Matrix.mulVec_single]
  constructor
  · intro s t
    apply mem_iUnion.mpr
    refine ⟨s, mem_iUnion.mpr ⟨t, Or.inl ?_⟩⟩
    exact ⟨M, hM, hEntry M m h s t⟩
  · intro s t
    apply mem_iUnion.mpr
    refine ⟨s, mem_iUnion.mpr ⟨t, Or.inr ?_⟩⟩
    exact ⟨M⁻¹, ⟨M, hM, rfl⟩, hEntry M⁻¹ (fun j => (m j)⁻¹) hInv s t⟩

theorem compactRepresentativesOfFiniteLabels :
    Specs.TensorAdelicReduction.compactRepresentativesOfFiniteLabels := by
  classical
  intro B H P T X _ _ _ _ _ S i j G r t hS hFin hCompare hStab hCompact
  let L := Set.range (t ∘ r)
  let : Finite L := hFin.to_subtype
  let rep (s : L) : X := s.property.choose
  have hRep (s : L) : t (r (rep s)) = s.val := s.property.choose_spec
  choose C hC hMem using hCompact
  let D := ⋃ s : L, C (rep s)
  have hD : IsCompact D := isCompact_iUnion fun s => hC (rep s)
  refine ⟨D ∩ S, hD.inter_right hS, inter_subset_right, ?_⟩
  intro x
  let s : L := ⟨t (r x), ⟨x, rfl⟩⟩
  have he : t (r x) = t (r (rep s)) := (hRep s).symm
  obtain ⟨h, hh⟩ := hCompare x (rep s) he
  exact ⟨h, mem_iUnion.mpr ⟨s, hMem (rep s) x he h hh⟩, S.mul_mem (G x).property (hStab h)⟩

open private addSubgroup_closedDiscrete_of_isolating_identity from
  LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals

theorem baseDiagonalClosedDiscrete : Specs.TensorAdelicReduction.baseDiagonalClosedDiscrete := by
  intro R k B _ _ _ _ _ _ _ _ _ f U hU h0 hIso
  let D := baseScalarDiagonal (R := R) f
  let L := D.toAddMonoidHom.range
  let V : Set (FiniteAdeleRing R k) := {x | ∀ p, x p ∈ p.adicCompletionIntegers k}
  have hV : IsOpen V := by
    change IsOpen {x : Πʳ p : HeightOneSpectrum R, [p.adicCompletion k,
      p.adicCompletionIntegers k] | ∀ p, x p ∈ p.adicCompletionIntegers k}
    exact RestrictedProduct.isOpen_forall_mem
      (fun p : HeightOneSpectrum R => adicIntegers_isOpen (K := k) p)
  let : T2Space (FiniteAdeleRing R k) := inferInstanceAs
    (T2Space (Πʳ p : HeightOneSpectrum R, [p.adicCompletion k, p.adicCompletionIntegers k]))
  let : Fact (∀ p : HeightOneSpectrum R, IsOpen (p.adicCompletionIntegers k :
      Set (p.adicCompletion k))) := ⟨fun p => adicIntegers_isOpen p⟩
  let : IsTopologicalRing (FiniteAdeleRing R k) := inferInstanceAs
    (IsTopologicalRing (Πʳ p : HeightOneSpectrum R, [p.adicCompletion k, p.adicCompletionIntegers k]))
  change IsClosed (L : Set (BaseScalarAdeles R k B)) ∧ IsDiscrete (L : Set (BaseScalarAdeles R k B))
  refine addSubgroup_closedDiscrete_of_isolating_identity L (V ×ˢ U) (hV.prod hU)
    ⟨fun p => (p.adicCompletionIntegers k).zero_mem, h0⟩ ?_
  rintro _ ⟨x, rfl⟩ hx
  have hxInt (p : HeightOneSpectrum R) : p.valuation k x ≤ 1 := by
    have hp : algebraMap k (p.adicCompletion k) x ∈ p.adicCompletionIntegers k := hx.1 p
    change Valued.v (x : p.adicCompletion k) ≤ 1 at hp
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hp
    exact hp
  obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one k x hxInt
  have hr : r = 0 := hIso r hx.2
  change D (algebraMap R k r) = 0
  rw [hr, map_zero, map_zero]

theorem finiteDiagonalTuples : Specs.TensorAdelicReduction.finiteDiagonalTuples := by
  intro k A J _ _ f hf hc hd C hC
  let S (j : J) := (fun x : J → A => x j) '' C ∩ range f
  have hS (j : J) : (S j).Finite :=
    ((hC.image (continuous_apply j)).inter_right hc).finite (hd.mono inter_subset_right)
  refine (Set.Finite.pi fun j => (hS j).preimage hf.injOn).subset ?_
  intro x hx j _
  exact ⟨⟨f ∘ x, hx, rfl⟩, ⟨x j, rfl⟩⟩

section MatrixEntries

variable {R k B N : Type*} [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Field B] [TopologicalSpace B]
    [IsTopologicalRing B] [Fintype N] [DecidableEq N]

private theorem integralEntry (i j : N) (p : HeightOneSpectrum R) :
    MapsTo (fun m : Matrix.GeneralLinearGroup N (p.adicCompletion k) => m.val i j)
      (Matrix.GeneralLinearGroup.map (n := N) (p.adicCompletionIntegers k).subtype).range
      (p.adicCompletionIntegers k) := by
  rintro _ ⟨m, rfl⟩
  exact (m.val i j).property

private def finiteEntry (i j : N) (x : FiniteBasisAdeles R k N) : FiniteAdeleRing R k :=
  RestrictedProduct.map (fun p (m : Matrix.GeneralLinearGroup N (p.adicCompletion k)) =>
    m.val i j) (Filter.Eventually.of_forall (integralEntry i j)) x

private theorem continuousFiniteEntry (i j : N) :
    Continuous (finiteEntry (R := R) (k := k) i j) :=
  RestrictedProduct.mapAlong_continuous
    (fun p : HeightOneSpectrum R => Matrix.GeneralLinearGroup N (p.adicCompletion k))
    (fun p : HeightOneSpectrum R => p.adicCompletion k)
    (A₁ := fun p => ↑(Matrix.GeneralLinearGroup.map
      (n := N) (p.adicCompletionIntegers k).subtype).range)
    (A₂ := fun p => ↑(p.adicCompletionIntegers k))
    id Filter.tendsto_id
    (fun _ m => m.val i j)
    (Filter.Eventually.of_forall (integralEntry i j))
    (fun _ => (continuous_apply j).comp (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id i))

private theorem continuousFiniteInv :
    Continuous (fun a : FiniteBasisAdeles R k N => a⁻¹) := by
  let G (p : HeightOneSpectrum R) := Matrix.GeneralLinearGroup N (p.adicCompletion k)
  let U (p : HeightOneSpectrum R) : Subgroup (G p) :=
    (Matrix.GeneralLinearGroup.map (p.adicCompletionIntegers k).subtype).range
  exact RestrictedProduct.mapAlong_continuous G G
    (A₁ := fun p => (U p : Set (G p))) (A₂ := fun p => (U p : Set (G p)))
    id Filter.tendsto_id (fun _ a => a⁻¹)
    (Filter.Eventually.of_forall fun p _ ha => (U p).inv_mem ha) (fun _ => continuous_inv)

private def matrixEntries (a : BasisAdeles R k B N) : Matrix N N (BaseScalarAdeles R k B) :=
  fun i j => (finiteEntry i j a.1, a.2.val i j)

omit [TopologicalSpace B] [IsTopologicalRing B] in
private theorem matrixEntries_one :
    matrixEntries (1 : BasisAdeles R k B N) = 1 := by
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · apply DFunLike.ext
    intro p
    change (1 : Matrix.GeneralLinearGroup N (p.adicCompletion k)).val i j =
      (((1 : Matrix N N (BaseScalarAdeles R k B)) i j).1) p
    by_cases e : i = j <;> simp [Matrix.one_apply, e] <;> rfl
  · by_cases e : i = j <;> simp [matrixEntries, Matrix.one_apply, e]

omit [TopologicalSpace B] [IsTopologicalRing B] in
private theorem matrixEntries_mul (a b : BasisAdeles R k B N) :
    matrixEntries (a * b) = matrixEntries a * matrixEntries b := by
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · apply DFunLike.ext
    intro p
    change ((a.1 p).val * (b.1 p).val) i j = _
    simp only [matrixEntries, Matrix.mul_apply, Prod.fst_sum, Prod.fst_mul]
    rw [show (∑ x, finiteEntry i x a.1 * finiteEntry x j b.1) p =
        ∑ x, (finiteEntry i x a.1 * finiteEntry x j b.1) p from
      map_sum (RestrictedProduct.evalRingHom _ p) _ _]
    rfl
  · simp [matrixEntries, Matrix.mul_apply, Prod.snd_sum]

private def matrixEntryHom :
    BasisAdeles R k B N →* Matrix.GeneralLinearGroup N (BaseScalarAdeles R k B) where
  toFun a :=
    ⟨matrixEntries a, matrixEntries a⁻¹,
      by rw [← matrixEntries_mul, mul_inv_cancel, matrixEntries_one],
      by rw [← matrixEntries_mul, inv_mul_cancel, matrixEntries_one]⟩
  map_one' := Units.ext matrixEntries_one
  map_mul' a b := Units.ext (matrixEntries_mul a b)

end MatrixEntries

theorem adelicMatrixEntries : Specs.TensorAdelicReduction.adelicMatrixEntries := by
  intro R k B N _ _ _ _ _ _ _ _ _ _
  refine ⟨matrixEntryHom, ?_, ?_, fun a p i j => rfl, fun a i j => rfl⟩
  · rw [Units.continuous_iff]
    constructor
    · exact continuous_matrix fun i j =>
        ((continuousFiniteEntry i j).comp continuous_fst).prodMk
          ((continuous_apply j).comp (Matrix.GeneralLinearGroup.continuous_apply _ continuous_snd i))
    · have hInv : Continuous (fun m : Matrix.GeneralLinearGroup N B => m⁻¹.val) :=
        Units.continuous_coe_inv (M := Matrix N N B)
      exact continuous_matrix fun i j =>
        ((continuousFiniteEntry i j).comp (continuousFiniteInv.comp continuous_fst)).prodMk
          ((continuous_apply j).comp ((continuous_apply i).comp
            (hInv.comp continuous_snd)))
  · intro a b h
    have hc : matrixEntries a = matrixEntries b := congrArg Units.val h
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro p
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact congrArg (fun (m : Matrix N N (BaseScalarAdeles R k B)) => (m i j).1 p) hc
    · apply Units.ext
      apply Matrix.ext
      intro i j
      exact congrArg (fun (m : Matrix N N (BaseScalarAdeles R k B)) => (m i j).2) hc

private theorem coordinateTensor_apply {A X I O : Type*} [CommRing A] [Fintype X] [Fintype I]
    (c : TensorCoefficients A X I O) (v : X → I → A) (o : O) :
    coordinateTensor c v o = (open Classical in ∑ w : X → I, (∏ x, v x (w x)) * c w o) := by
  simp [coordinateTensor, MultilinearMap.smulRight_apply, MultilinearMap.compLinearMap_apply]

private theorem coordinateTensor_basis {A X I O : Type*} [CommRing A]
    [Fintype X] [Fintype I] [DecidableEq I]
    (c : TensorCoefficients A X I O) (w : X → I) :
    coordinateTensor c (fun x => (Pi.basisFun A I) (w x)) = c w := by
  funext o
  rw [coordinateTensor_apply, Finset.sum_eq_single w]
  · simp [Pi.basisFun_apply]
  · intro v _ h
    obtain ⟨x, hx⟩ := Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (i := x) (Finset.mem_univ x), zero_mul]
    simp [Pi.basisFun_apply, hx]
  · simp

theorem coordinateTensorMap : Specs.TensorAdelicReduction.coordinateTensorMap := by
  intro A B X I O _ _ _ _ f c v
  funext o
  simp only [coordinateTensor_apply, map_sum, map_mul, map_prod]

theorem transformedTensorContinuous : Specs.TensorAdelicReduction.transformedTensorContinuous := by
  intro A X I O _ _ _ _ _ _ _ _ c
  have h₁ : Continuous (fun m : Matrix.GeneralLinearGroup I A => m.val) := Units.continuous_val
  have h₂ : Continuous (fun u : Matrix.GeneralLinearGroup O A => u⁻¹.val) :=
    Units.continuous_coe_inv (M := Matrix O O A)
  apply continuous_pi
  intro w
  apply continuous_pi
  intro o
  simp only [transformedTensor, Matrix.mulVec, dotProduct, coordinateTensor_apply, Matrix.col_apply]
  apply continuous_finsetSum
  intro j _
  have h₂' : Continuous (fun a : Matrix.GeneralLinearGroup I A × Matrix.GeneralLinearGroup O A =>
      a.2⁻¹.val o j) := (continuous_apply j).comp ((continuous_apply o).comp (h₂.comp continuous_snd))
  refine h₂'.mul ?_
  apply continuous_finsetSum
  intro v _
  refine (continuous_finsetProd _ fun x _ => ?_).mul continuous_const
  exact ((continuous_apply (w x)).comp (continuous_apply (v x))).comp
    (h₁.comp (continuous_fst : Continuous (Prod.fst :
      Matrix.GeneralLinearGroup I A × Matrix.GeneralLinearGroup O A → _)))

theorem localTensorComparison : Specs.TensorAdelicReduction.localTensorComparison := by
  classical
  intro k K B X I O N M J _ _ _ _ _ _ _ _ L _ _ f e b c E F hE hF T v j
  let p := coordinateTensor (fun w o => f (restrictedTensor b c T w o))
  let q := coordinateTensor (fun w o => e j (T w o))
  let linE : (N → B) →ₗ[B] (I → L j) := (LinearMap.proj j).comp E.toLinearMap
  let linF : (M → B) →ₗ[B] (O → L j) := (LinearMap.proj j).comp F.toLinearMap
  have h : linF.compMultilinearMap p = (q.restrictScalars B).compLinearMap (fun _ => linE) := by
    apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun B N)
    intro w
    change F (p (fun x => Pi.basisFun B N (w x))) j = q (fun x => E (Pi.basisFun B N (w x)) j)
    have hb (n : N) : (Pi.basisFun B N) n = fun i => f (b.equivFun (b n) i) := by
      funext i
      rw [Module.Basis.equivFun_self]
      by_cases h : i = n
      · subst i
        simp [Pi.basisFun_apply]
      · simp [Pi.basisFun_apply, h, Ne.symm h]
    rw [show p (fun x => Pi.basisFun B N (w x)) = _ from coordinateTensor_basis _ w]
    change F (fun m => f (c.equivFun (coordinateTensor T (fun x => b (w x))) m)) j = _
    have hInputs : (fun x => E (Pi.basisFun B N (w x)) j) =
        fun x i => e j (b (w x) i) := by
      funext x i
      rw [hb]
      exact hE _ _ _
    rw [hInputs, coordinateTensorMap (e j) T (fun x => b (w x))]
    exact funext fun o => hF _ _ _
  exact DFunLike.congr_fun h v

private theorem mulVec_action {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]
    (m n : Matrix.GeneralLinearGroup I A) (x : I → A) :
    (m * n).val.mulVec x = m.val.mulVec (n.val.mulVec x) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

private theorem mulVec_inv_action {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]
    (m : Matrix.GeneralLinearGroup I A) (x : I → A) :
    m.val.mulVec (m⁻¹.val.mulVec x) = x := by
  rw [← mulVec_action, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

private theorem mulVec_basis {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]
    (m : Matrix.GeneralLinearGroup I A) (i : I) : m.val.mulVec (Pi.basisFun A I i) = m.val.col i := by
  ext j
  simp [Pi.basisFun_apply, Matrix.mulVec_single]

theorem tensorTransport : Specs.TensorAdelicReduction.tensorTransport := by
  intro A B X I O _ _ _ _ _ _ _ e T m u
  constructor
  · intro w o
    unfold transformedTensor
    have hCol (x : X) (i : I) : (Matrix.GeneralLinearGroup.map e m).val.col (w x) i =
        e (m.val.col (w x) i) := rfl
    have hCols : (fun x => (Matrix.GeneralLinearGroup.map e m).val.col (w x)) =
        fun x i => e (m.val.col (w x) i) := funext fun x => funext (hCol x)
    rw [hCols, coordinateTensorMap e T (fun x => m.val.col (w x))]
    rw [← map_inv]
    exact (RingHom.map_mulVec e u⁻¹.val _ o).symm
  · intro g v h
    funext w
    have hCol (x : X) : (g * m).val.col (w x) = g.val.mulVec (m.val.col (w x)) := by
      rw [← mulVec_basis, mulVec_action, mulVec_basis]
    have hEval := h (fun x => m.val.col (w x))
    change coordinateTensor T (fun x => g.val.mulVec (m.val.col (w x))) = _ at hEval
    simp only [transformedTensor, hCol, hEval, mul_inv_rev, mulVec_action]
    rw [← mulVec_action v⁻¹ v, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

theorem tensorLabelComparison : Specs.TensorAdelicReduction.tensorLabelComparison := by
  intro A X I O _ _ _ _ _ _ T m n u v h
  let f (p : Matrix.GeneralLinearGroup I A) (q : Matrix.GeneralLinearGroup O A) :=
    (Matrix.mulVecLin q⁻¹.val).compMultilinearMap
      ((coordinateTensor T).compLinearMap fun _ => Matrix.mulVecLin p.val)
  have he : f m u = f n v := by
    apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun A I)
    intro w
    change u⁻¹.val.mulVec (coordinateTensor T (fun x => m.val.mulVec (Pi.basisFun A I (w x)))) =
      v⁻¹.val.mulVec (coordinateTensor T (fun x => n.val.mulVec (Pi.basisFun A I (w x))))
    simp only [mulVec_basis]
    exact congrFun h w
  intro z
  have hEval := DFunLike.congr_fun he (fun x => n⁻¹.val.mulVec (z x))
  change u⁻¹.val.mulVec (coordinateTensor T (fun x => m.val.mulVec (n⁻¹.val.mulVec (z x)))) =
    v⁻¹.val.mulVec (coordinateTensor T (fun x => n.val.mulVec (n⁻¹.val.mulVec (z x)))) at hEval
  simp only [mulVec_inv_action] at hEval
  have hh := congrArg u.val.mulVec hEval
  simpa only [mulVec_inv_action, mulVec_action] using hh

open LatticeCompletionDecompositionSpec in
theorem finitePrimeFibres : Specs.TensorAdelicReduction.finitePrimeFibres := by
  classical
  intro R A _ _ _ _ _ _ _ _
  let Z := Σ p : HeightOneSpectrum R, p.asIdeal.primesOver A
  let e (z : Z) := primeAbove z.1 z.2
  have hUnder (z : Z) : primeBelow (R := R) (e z) = z.1 := by
    apply HeightOneSpectrum.ext
    exact z.2.property.2.over.symm
  have hp (v : HeightOneSpectrum A) :
      v.asIdeal ∈ (primeBelow (R := R) v).asIdeal.primesOver A :=
    ⟨v.isPrime, ⟨rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨p, x⟩ ⟨q, y⟩ h
      have hpq : p = q := (hUnder ⟨p, x⟩).symm.trans
        ((congrArg (primeBelow (R := R)) h).trans (hUnder ⟨q, y⟩))
      subst q
      exact congrArg (Sigma.mk p) (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h))
    · intro v
      exact ⟨⟨primeBelow v, ⟨v.asIdeal, hp v⟩⟩, HeightOneSpectrum.ext rfl⟩
  refine ⟨he, ?_⟩
  rw [Filter.tendsto_def]
  intro S hS
  have hS' : Sᶜ.Finite := Filter.eventually_cofinite.mp hS
  apply Filter.eventually_cofinite.mpr
  have hEach (p : HeightOneSpectrum R) : {v : HeightOneSpectrum A | primeBelow v = p}.Finite := by
    let W := p.asIdeal.primesOver A
    have hw : Finite W := Algebra.QuasiFinite.finite_primesOver (S := A) p.asIdeal
    apply (Set.finite_range (primeAbove p)).subset
    intro v hv
    have hv' : primeBelow (R := R) v = p := hv
    exact ⟨⟨v.asIdeal, hv' ▸ hp v⟩, HeightOneSpectrum.ext rfl⟩
  apply (hS'.biUnion (fun p _ => hEach p)).subset
  intro v hv
  exact Set.mem_iUnion₂.mpr ⟨primeBelow v, hv, rfl⟩

private theorem integralIffMapsBox {A I : Type*} [Field A] [Fintype I] [DecidableEq I]
    (O : Subring A) (m : Matrix.GeneralLinearGroup I A) :
    m ∈ integralMatrices O ↔ ∀ x, (∀ i, x i ∈ O) →
      (∀ i, m.val.mulVec x i ∈ O) ∧ (∀ i, m⁻¹.val.mulVec x i ∈ O) := by
  let U : Set (I → A) := {x | ∀ i, x i ∈ O}
  constructor
  · intro hm x hx
    have hf := (integralMatrixIffPreservesBox O m).mp hm
    have hi := (integralMatrixIffPreservesBox O m⁻¹).mp ((integralMatrices O).inv_mem hm)
    change m.val.mulVec '' U = U at hf
    change m⁻¹.val.mulVec '' U = U at hi
    refine ⟨?_, ?_⟩
    · change m.val.mulVec x ∈ U
      rw [← hf]
      exact Set.mem_image_of_mem _ hx
    · change m⁻¹.val.mulVec x ∈ U
      rw [← hi]
      exact Set.mem_image_of_mem _ hx
  · intro h
    apply (integralMatrixIffPreservesBox O m).mpr
    apply subset_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (h x hx).1
    · intro x hx
      exact ⟨m⁻¹.val.mulVec x, (h x hx).2, mulVec_inv_action m x⟩

theorem integralMatrixTransport : Specs.TensorAdelicReduction.integralMatrixTransport := by
  classical
  intro B N I J _ _ _ _ _ L _ _ E O U hBox M m h
  have hInv (z : N → B) (j : J) :
      E (M⁻¹.val.mulVec z) j = (m j)⁻¹.val.mulVec (E z j) := by
    have h' := h (M⁻¹.val.mulVec z) j
    rw [mulVec_inv_action] at h'
    rw [h', ← mulVec_action, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mulVec]
  constructor
  · intro hM j
    apply (integralIffMapsBox (U j) (m j)).mpr
    intro y hy
    let z := E.symm (Pi.single j y)
    have hz : E z = Pi.single j y := E.apply_symm_apply _
    have hzInt : ∀ n, z n ∈ O := (hBox z).mpr fun k i => by
      rw [hz]
      by_cases hkj : k = j
      · subst k
        simpa using hy i
      · simp [Pi.single_eq_of_ne hkj]
    obtain ⟨h1, h2⟩ := (integralIffMapsBox O M).mp hM z hzInt
    have h1' := (hBox _).mp h1 j
    have h2' := (hBox _).mp h2 j
    rw [h, hz, Pi.single_eq_same] at h1'
    rw [hInv, hz, Pi.single_eq_same] at h2'
    exact ⟨h1', h2'⟩
  · intro hm
    apply (integralIffMapsBox O M).mpr
    intro z hz
    have hzInt := (hBox z).mp hz
    refine ⟨(hBox _).mpr fun j i => ?_, (hBox _).mpr fun j i => ?_⟩
    · rw [h]
      exact ((integralIffMapsBox (U j) (m j)).mp (hm j) (E z j) (hzInt j)).1 i
    · rw [hInv]
      exact ((integralIffMapsBox (U j) (m j)).mp (hm j) (E z j) (hzInt j)).2 i

theorem compactOriginalMatrixBox : Specs.TensorAdelicReduction.compactOriginalMatrixBox := by
  intro A K I J _ _ _ _ _ _ _ L _ _ D E hD hE hsub
  have hFin := compactRestrictedProductBox
    (fun (v : HeightOneSpectrum A) => (↑(integralMatrices (I := I)
      (v.adicCompletionIntegers K).toSubring) : Set (Matrix.GeneralLinearGroup I (v.adicCompletion K))))
    D hD hsub
  have hInf : IsCompact (Set.pi Set.univ E) := isCompact_univ_pi hE
  have hEq : {g : FiniteMatrices A K I × (∀ j, Matrix.GeneralLinearGroup I (L j)) |
      (∀ v, g.1 v ∈ D v) ∧ (∀ j, g.2 j ∈ E j)} =
      {g : FiniteMatrices A K I | ∀ v, g v ∈ D v} ×ˢ Set.pi Set.univ E := by
    ext g
    simp [Set.mem_pi]
  rw [hEq]
  exact hFin.prod hInf

open private positivePart_open from LinearAlgebraicGroups.Arithmetic.LaurentLatticeReduction

open LaurentLattice WithZero in
theorem arithmeticBaseDiagonals : Specs.TensorAdelicReduction.arithmeticBaseDiagonals := by
  constructor
  · apply baseDiagonalClosedDiscrete (algebraMap ℚ ℝ) (Metric.ball 0 1) Metric.isOpen_ball
      (Metric.mem_ball_self zero_lt_one)
    intro z hz
    have hz' : |(z : ℝ)| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hz
    have hi : |z| < 1 := by exact_mod_cast hz'
    obtain ⟨h1, h2⟩ := abs_lt.mp hi
    omega
  · intro F _ _ f hf
    apply baseDiagonalClosedDiscrete f (positivePart F) (positivePart_open F)
      (by simp [positivePart])
    intro p hp
    by_contra hne
    have he : f (algebraMap F[X] F⟮X⟯ p) = polynomialEmbedding F p := DFunLike.congr_fun hf p
    rw [he] at hp
    change baseValuation F (polynomialEmbedding F p) < 1 at hp
    rw [polynomial_valuation p hne, ← exp_zero, exp_lt_exp] at hp
    omega

theorem compactUniformIntegrality : Specs.TensorAdelicReduction.compactUniformIntegrality := by
  intro J G _ U hOpen C hC
  let V (x : Πʳ j, [G j, U j]) := {y : Πʳ j, [G j, U j] | ∀ i, x i ∈ U i → y i ∈ U i}
  have hCover : C ⊆ ⋃ x, V x := fun x _ => mem_iUnion.mpr ⟨x, fun _ hx => hx⟩
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover V
    (fun _ => RestrictedProduct.isOpen_forall_imp_mem hOpen) hCover
  have hEv : ∀ᶠ j in Filter.cofinite, ∀ x ∈ s, x j ∈ U j :=
    (Filter.eventually_all_finset s).mpr fun x _ => x.property
  filter_upwards [hEv] with j hj x hx
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨hys, hxy⟩ := mem_iUnion.mp hy
  exact hxy j (hj y hys)

private theorem integralIffEntries {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]
    (O : Subring A) (g : Matrix.GeneralLinearGroup I A) :
    g ∈ integralMatrices O ↔
      (∀ i j, g.val i j ∈ O) ∧ (∀ i j, g⁻¹.val i j ∈ O) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨fun i j => (u.val i j).property, fun i j => (u⁻¹.val i j).property⟩
  · rintro ⟨h₁, h₂⟩
    let a : Matrix I I O := fun i j => ⟨g.val i j, h₁ i j⟩
    let b : Matrix I I O := fun i j => ⟨g⁻¹.val i j, h₂ i j⟩
    let f := O.subtype.mapMatrix (m := I)
    have hf : Function.Injective f := fun a b h => Matrix.ext fun i j =>
      Subtype.val_injective (congrFun (congrFun h i) j)
    let u : Matrix.GeneralLinearGroup I O := ⟨a, b,
      hf (by rw [map_mul, map_one]; exact g.val_inv),
      hf (by rw [map_mul, map_one]; exact g.inv_val)⟩
    exact ⟨u, Units.ext rfl⟩

private theorem integralMatrices_isOpen {A I : Type*} [Field A] [TopologicalSpace A]
    [IsTopologicalRing A] [Fintype I] [DecidableEq I] (O : ValuationSubring A)
    (ho : IsOpen (O : Set A)) :
    IsOpen (↑(integralMatrices (I := I) O.toSubring) : Set (Matrix.GeneralLinearGroup I A)) := by
  have he : (↑(integralMatrices (I := I) O.toSubring) : Set (Matrix.GeneralLinearGroup I A)) =
      (⋂ s, ⋂ t, {m : Matrix.GeneralLinearGroup I A | m.val s t ∈ O}) ∩
        (⋂ s, ⋂ t, {m : Matrix.GeneralLinearGroup I A | m⁻¹.val s t ∈ O}) := by
    ext m
    change m ∈ integralMatrices O.toSubring ↔ _
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    change m ∈ integralMatrices O.toSubring ↔
      (∀ i j, m.val i j ∈ O.toSubring) ∧ (∀ i j, m⁻¹.val i j ∈ O.toSubring)
    exact integralIffEntries O.toSubring m
  rw [he]
  refine (isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t => ?_).inter
    (isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t => ?_)
  · exact ho.preimage ((continuous_apply t).comp (Matrix.GeneralLinearGroup.continuous_apply _
      continuous_id s))
  · exact ho.preimage ((continuous_apply t).comp (Matrix.GeneralLinearGroup.continuous_apply _
      continuous_inv s))

open LatticeCompletionDecompositionSpec in
theorem compactFiniteMatrixTransport : Specs.TensorAdelicReduction.compactFiniteMatrixTransport := by
  classical
  intro R A k K I N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b hb C hC
  let W (p : HeightOneSpectrum R) := p.asIdeal.primesOver A
  let B (p : HeightOneSpectrum R) := p.adicCompletion k
  let V (p : HeightOneSpectrum R) (w : W p) := (primeAbove p w).adicCompletion K
  let O (p : HeightOneSpectrum R) := (p.adicCompletionIntegers k).toSubring
  have hOpen (p : HeightOneSpectrum R) :
      IsOpen (↑(integralMatrices (I := N) (O p)) : Set (Matrix.GeneralLinearGroup N (B p))) :=
    integralMatrices_isOpen (p.adicCompletionIntegers k) (adicIntegers_isOpen p)
  have hEv := compactUniformIntegrality
    (G := fun p : HeightOneSpectrum R => Matrix.GeneralLinearGroup N (B p))
    (fun p => ↑(integralMatrices (I := N) (O p))) hOpen C hC
  have hLocal (p : HeightOneSpectrum R) :
      ∃ D : ∀ w : W p, Set (Matrix.GeneralLinearGroup I (V p w)),
        (∀ w, IsCompact (D w)) ∧
        (∀ G ∈ C, ∀ g : FiniteMatrices A K I, FiniteMatrixAction b g p (G p) →
          ∀ w, g (primeAbove p w) ∈ D w) ∧
        ((∀ G ∈ C, G p ∈ integralMatrices (O p)) →
          ∀ w, D w ⊆ (↑(integralMatrices (I := I)
            ((primeAbove p w).adicCompletionIntegers K).toSubring) : Set _)) := by
    obtain ⟨a, _, E, hDiag, hCompare⟩ := finiteCoordinateLatticeComparison (A := A) p b
    let := a
    let (w : W p) : Field (V p w) := inferInstance
    let (w : W p) : T1Space (V p w) := inferInstance
    let (w : W p) : IsTopologicalRing (V p w) := inferInstance
    let f := algebraMap k (B p)
    let b₀ := referenceLattice A K I
    let : Submodule.IsLattice K b₀ := isLattice_matrixLattice _
    let U (w : W p) := ((primeAbove p w).adicCompletionIntegers K).toSubring
    let S : Set (N → B p) := {x | ∀ i, x i ∈ O p}
    have hClosed : closure (range fun x : b₀ => embedCoordinates f (b.equivFun (x : I → K))) = S := by
      have hRange : (range fun x : b₀ => embedCoordinates f (b.equivFun (x : I → K))) =
          embedCoordinates f '' (b.equivFun '' (b₀ : Set (I → K))) := by
        rw [Set.image_image]
        ext y
        exact ⟨fun ⟨x, hx⟩ => ⟨x, x.property, hx⟩, fun ⟨x, hx, he⟩ => ⟨⟨x, hx⟩, he⟩⟩
      rw [hRange, hb, ← coe_matrixLattice]
      let : Submodule.IsLattice k (referenceLattice R k N) := isLattice_matrixLattice _
      exact (completedLattice_eq_closure (referenceLattice R k N) p).trans
        (completedReference p)
    have hRef : E '' S = Set.pi Set.univ (fun w : W p => {x | ∀ i, x i ∈ U w}) := by
      rw [← hClosed, hCompare b₀]
      congr 1
      funext w
      exact completedReference (primeAbove p w)
    have hBox (x : N → B p) : (∀ n, x n ∈ O p) ↔ ∀ w i, E x w i ∈ U w := by
      have hmem : E x ∈ Set.pi Set.univ (fun w : W p => {y | ∀ i, y i ∈ U w}) ↔
          ∀ w i, E x w i ∈ U w := by simp [Set.mem_pi]
      rw [← hmem, ← hRef]
      exact (E.injective.mem_set_image (s := S)).symm
    have hEq (g : FiniteMatrices A K I) (H : Matrix.GeneralLinearGroup N (B p))
        (hAction : FiniteMatrixAction b g p H) :
        ∀ z (w : W p), E (H.val.mulVec z) w = (g (primeAbove p w)).val.mulVec (E z w) := by
      let E₀ : (N → B p) → ∀ w : W p, I → V p w := E
      have hCont₀ : Continuous E₀ := E.continuous
      change ∀ z w, E₀ (H.val.mulVec z) w = (g (primeAbove p w)).val.mulVec (E₀ z w)
      obtain ⟨a', E', hDiag', hAction'⟩ := hAction
      let := a'
      let E₁ : (N → B p) → ∀ w : W p, I → V p w := E'
      have hCont₁ : Continuous E₁ := E'.continuous
      have hDense : DenseRange (embedCoordinates f : (N → k) → (N → B p)) :=
        DenseRange.piMap (fun _ => p.denseRange_algebraMap (K := k))
      have hSame : E₀ = E₁ := by
        apply hDense.equalizer hCont₀ hCont₁
        funext x w
        have hh := (hDiag (b.equivFun.symm x) w).trans (hDiag' (b.equivFun.symm x) w).symm
        simpa only [Function.comp_apply, b.equivFun.apply_symm_apply] using hh
      rw [hSame]
      exact hAction'
    let CP := (fun G : FiniteMatrices R k N => G p) '' C
    have hCP : IsCompact CP := hC.image (RestrictedProduct.continuous_eval p)
    obtain ⟨D, hD, hLift⟩ := compactLocalMatrixTransport E CP hCP
    by_cases hint : ∀ G ∈ C, G p ∈ integralMatrices (O p)
    · let D' (w : W p) := D w ∩ ↑(integralMatrices (I := I) (U w))
      have hClosed' (w : W p) : IsClosed (↑(integralMatrices (I := I) (U w)) :
          Set (Matrix.GeneralLinearGroup I (V p w))) :=
        (integralMatrices (I := I) (U w)).isClosed_of_isOpen
          (integralMatrices_isOpen ((primeAbove p w).adicCompletionIntegers K)
            (adicIntegers_isOpen (primeAbove p w)))
      refine ⟨D', fun w => (hD w).inter_right (hClosed' w), ?_, fun _ _ => inter_subset_right⟩
      intro G hG g hA w
      exact ⟨hLift _ _ ⟨G, hG, rfl⟩ (hEq g (G p) hA) w,
        (integralMatrixTransport E.toLinearEquiv (O p) U hBox (G p) _
          (hEq g (G p) hA)).mp (hint G hG) w⟩
    · exact ⟨D, hD, fun G hG g hA => hLift _ _ ⟨G, hG, rfl⟩ (hEq g (G p) hA),
        fun h => (hint h).elim⟩
  choose D hD hLift hInt using hLocal
  have hFib := (finitePrimeFibres (R := R) (A := A))
  let e : (Σ p : HeightOneSpectrum R, W p) ≃ HeightOneSpectrum A :=
    Equiv.ofBijective (fun z : Σ p : HeightOneSpectrum R, W p => primeAbove z.1 z.2) hFib.1
  let P (v : HeightOneSpectrum A) := Set (Matrix.GeneralLinearGroup I (v.adicCompletion K))
  let D₀ (z : Σ p : HeightOneSpectrum R, W p) : P (e z) := D z.1 z.2
  let D' : (v : HeightOneSpectrum A) → P v := (Equiv.piCongrLeft P e) D₀
  have hRewrite (p : HeightOneSpectrum R) (w : W p) :
      D' (primeAbove p w) = D p w := by
    change D' (e ⟨p, w⟩) = _
    exact Equiv.piCongrLeft_apply_apply P e D₀ ⟨p, w⟩
  have hCompact (v : HeightOneSpectrum A) : IsCompact (D' v) := by
    obtain ⟨⟨p, w⟩, rfl⟩ := e.surjective v
    exact hRewrite p w ▸ hD p w
  have hAlmost : ∀ᶠ v : HeightOneSpectrum A in Filter.cofinite,
      D' v ⊆ (↑(integralMatrices (I := I) (v.adicCompletionIntegers K).toSubring) : Set _) := by
    filter_upwards [hFib.2.eventually hEv] with v hv
    obtain ⟨⟨p, w⟩, rfl⟩ := e.surjective v
    let Good (q : HeightOneSpectrum R) := ∀ G ∈ C, G q ∈ integralMatrices (O q)
    change Good (primeBelow (R := R) (primeAbove p w)) at hv
    have heq : primeBelow (R := R) (primeAbove p w) = p := HeightOneSpectrum.ext w.property.2.over.symm
    have hp : Good p := heq ▸ hv
    change D' (primeAbove p w) ⊆ _
    rw [hRewrite]
    exact hInt p hp w
  refine ⟨{g | ∀ v, g v ∈ D' v}, compactRestrictedProductBox _ D' hCompact hAlmost, ?_⟩
  intro G g hG hA v
  obtain ⟨⟨p, w⟩, rfl⟩ := e.surjective v
  change g (primeAbove p w) ∈ D' (primeAbove p w)
  rw [hRewrite]
  exact hLift p G hG g (hA p) w

private theorem restrictMatrix_mulVec {k K I N : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (b : Module.Basis N k (I → K)) (m : Matrix.GeneralLinearGroup I K) (x : I → K) :
    (restrictMatrix b m).val.mulVec (b.equivFun x) = b.equivFun (m.val.mulVec x) := by
  change (Matrix.GeneralLinearGroup.toLin (restrictMatrix b m)).val (b.equivFun x) = _
  simp [restrictMatrix]

private theorem mapMatrix_mulVec {S T P : Type*} [Field S] [Field T]
    [Fintype P] [DecidableEq P] (e : S →+* T) (m : Matrix.GeneralLinearGroup P S) (x : P → S) :
    (Matrix.GeneralLinearGroup.map e m).val.mulVec (embedCoordinates e x) =
      embedCoordinates e (m.val.mulVec x) :=
  (funext (RingHom.map_mulVec e m.val x)).symm

theorem rationalMatrixComparison : Specs.TensorAdelicReduction.rationalMatrixComparison := by
  intro k K B N I J _ _ _ _ _ _ _ _ L _ _ f e b E hE m z j
  let M := Matrix.GeneralLinearGroup.map f (restrictMatrix b m)
  let g := Matrix.GeneralLinearGroup.map (e j) m
  let E₀ := (LinearMap.proj j).comp E.toLinearMap
  have h : E₀.comp (Matrix.mulVecLin M.val) =
      ((Matrix.mulVecLin g.val).restrictScalars B).comp E₀ := by
    apply (Pi.basisFun B N).ext
    intro i
    change E (M.val.mulVec (Pi.basisFun B N i)) j = g.val.mulVec (E (Pi.basisFun B N i) j)
    have hBasis : (Pi.basisFun B N i) = embedCoordinates f (b.equivFun (b i)) := by
      ext n
      simp only [embedCoordinates, Module.Basis.equivFun_self, Pi.basisFun_apply]
      by_cases h : i = n <;> simp [h]
    rw [hBasis, hE]
    dsimp only [M, g]
    rw [mapMatrix_mulVec f (restrictMatrix b m) (b.equivFun (b i)), mapMatrix_mulVec (e j) m (b i),
      restrictMatrix_mulVec, hE]
  exact DFunLike.congr_fun h z

theorem localTensorPreservation : Specs.TensorAdelicReduction.localTensorPreservation := by
  intro k K B X I O N M J _ _ _ _ _ _ _ _ _ _ _ _ _ L _ _
    f e b c E F hE hF T g h G H hG hH hInv z
  let p := coordinateTensor (fun w o => f (restrictedTensor b c T w o))
  have hComp := localTensorComparison f e b c E F hE hF T
  apply F.injective
  funext j
  change F (p (fun x => G.val.mulVec (z x))) j = F (H.val.mulVec (p z)) j
  rw [hH, hComp, hComp]
  simp only [hG]
  exact hInv j (fun x => E (z x) j)

theorem finiteMatrixDiagonal : Specs.TensorAdelicReduction.finiteMatrixDiagonal := by
  intro R k N _ _ _ _ _ _ _
  let E (m : Matrix.GeneralLinearGroup N k) : FiniteMatrices R k N :=
    ⟨fun p => Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) m, by
      have hInt (z : k) : ∀ᶠ p : HeightOneSpectrum R in Filter.cofinite,
          algebraMap k (p.adicCompletion k) z ∈ p.adicCompletionIntegers k :=
        (algebraMap k (FiniteAdeleRing R k) z).cofinite_mem_adicCompletionIntegers
      have h (g : Matrix.GeneralLinearGroup N k) : ∀ᶠ p : HeightOneSpectrum R in Filter.cofinite,
          ∀ i j, algebraMap k (p.adicCompletion k) (g.val i j) ∈ p.adicCompletionIntegers k :=
        Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hInt (g.val i j)
      filter_upwards [h m, h m⁻¹] with p hp hpInv
      apply (integralIffEntries (p.adicCompletionIntegers k).toSubring _).mpr
      rw [← map_inv]
      exact ⟨hp, hpInv⟩⟩
  let e : Matrix.GeneralLinearGroup N k →* FiniteMatrices R k N :=
    { toFun := E
      map_one' := by
        apply RestrictedProduct.ext
        intro p
        exact map_one (Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)))
      map_mul' m n := by
        apply RestrictedProduct.ext
        intro p
        exact map_mul (Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k))) m n }
  exact ⟨e, fun _ _ => rfl⟩

private theorem isCompact_transformedTensor_image {B A X N : Type*} [TopologicalSpace B]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Fintype X] [Fintype N]
    [DecidableEq N] (C : Set B) (hC : IsCompact C) (m : B → Matrix.GeneralLinearGroup N A)
    (hm : Continuous m) (T : TensorCoefficients A X N N) :
    IsCompact ((fun z => transformedTensor T (m z) (m z)) '' C) :=
  hC.image ((transformedTensorContinuous T).comp (hm.prodMk hm))

set_option maxHeartbeats 800000 in
theorem finiteTransformedTensorLabels : Specs.TensorAdelicReduction.finiteTransformedTensorLabels := by
  classical
  intro R k B N J _ _ _ _ _ _ _ _ _ _ _ X _ f hc hd S C hC T r G H hH hFin hInf hFix hFixInf
  let A := BaseScalarAdeles R k B
  let D := baseScalarDiagonal (R := R) f
  have hRing : IsTopologicalRing A := by
    let : Fact (∀ p : HeightOneSpectrum R, IsOpen (p.adicCompletionIntegers k :
        Set (p.adicCompletion k))) := ⟨fun p => adicIntegers_isOpen p⟩
    let : IsTopologicalRing (FiniteAdeleRing R k) := inferInstanceAs
      (IsTopologicalRing (Πʳ p : HeightOneSpectrum R, [p.adicCompletion k, p.adicCompletionIntegers k]))
    infer_instance
  have hev (j : J) :
      {a : TensorCoefficients k (X j) N N |
        (fun w i => D (a w i)) ∈
          (fun H => transformedTensor (fun w i => D (T j w i))
            (matrixEntryHom H) (matrixEntryHom H)) '' C}.Finite := by
    let M : BasisAdeles R k B N → Matrix.GeneralLinearGroup N A := matrixEntryHom
    have hM : Continuous M := by
      rw [Units.continuous_iff]
      constructor
      · exact continuous_matrix fun i l =>
          ((continuousFiniteEntry i l).comp continuous_fst).prodMk
            ((continuous_apply l).comp (Matrix.GeneralLinearGroup.continuous_apply _ continuous_snd i))
      · have hinv : Continuous (fun m : Matrix.GeneralLinearGroup N B => m⁻¹.val) :=
          Units.continuous_coe_inv (M := Matrix N N B)
        exact continuous_matrix fun i l =>
          ((continuousFiniteEntry i l).comp (continuousFiniteInv.comp continuous_fst)).prodMk
            ((continuous_apply l).comp ((continuous_apply i).comp (hinv.comp continuous_snd)))
    let C' := (fun H => transformedTensor (fun w i => D (T j w i)) (M H) (M H)) '' C
    have hC' : IsCompact C' := isCompact_transformedTensor_image C hC M hM
      (fun w i => D (T j w i))
    let e (z : (X j → N) → N → A) (a : (X j → N) × N) := z a.1 a.2
    let E' := e '' C'
    have he : Continuous e := continuous_pi fun a =>
      (continuous_apply a.2).comp (continuous_apply a.1)
    have hFin' := finiteDiagonalTuples D D.injective hc hd E' (hC'.image he)
    let g (a : TensorCoefficients k (X j) N N) (w : (X j → N) × N) := a w.1 w.2
    have hg : Function.Injective g := fun a b he => funext fun w => funext fun i =>
      congrFun he (w, i)
    refine (hFin'.preimage hg.injOn).subset (fun a ha => ?_)
    change (fun p => D (g a p)) ∈ E'
    exact Set.mem_image_of_mem e ha
  let Y (j : J) := {a : TensorCoefficients k (X j) N N |
        (fun w i => D (a w i)) ∈
          (fun H => transformedTensor (fun w i => D (T j w i))
            (matrixEntryHom H) (matrixEntryHom H)) '' C}
  refine (Set.Finite.pi hev).subset ?_
  rintro _ ⟨x, rfl⟩ j _
  refine ⟨H x, hH x, ?_⟩
  funext w i
  apply Prod.ext
  · apply DFunLike.ext
    intro p
    let e : A →+* p.adicCompletion k :=
      (RestrictedProduct.evalRingHom _ p).comp (RingHom.fst _ _)
    have he : ∀ z, e (D z) = algebraMap k (p.adicCompletion k) z := fun _ => rfl
    have hMatrix : Matrix.GeneralLinearGroup.map e (matrixEntryHom (H x)) = (H x).1 p :=
      Units.ext (Matrix.ext fun _ _ => rfl)
    change e (transformedTensor _ _ _ w i) = _
    rw [← (tensorTransport e _ _ _).1, hMatrix, hFin]
    simp_rw [he]
    let f₀ := algebraMap k (p.adicCompletion k)
    let m := Matrix.GeneralLinearGroup.map f₀ (r x)
    rw [(tensorTransport (RingHom.id _) (fun w i => f₀ (T j w i)) m m).2 _ _ (hFix j x p)]
    exact (tensorTransport f₀ (T j) (r x) (r x)).1 _ _
  · let e : A →+* B := RingHom.snd _ _
    have hMatrix : Matrix.GeneralLinearGroup.map e (matrixEntryHom (H x)) = (H x).2 :=
      Units.ext (Matrix.ext fun _ _ => rfl)
    change e (transformedTensor _ _ _ w i) = _
    rw [← (tensorTransport e _ _ _).1, hMatrix, hInf]
    change transformedTensor (fun w i => f (T j w i)) _ _ w i = _
    let m := Matrix.GeneralLinearGroup.map f (r x)
    rw [(tensorTransport (RingHom.id _) (fun w i => f (T j w i)) m m).2 _ _ (hFixInf j x)]
    exact (tensorTransport f (T j) (r x) (r x)).1 _ _

theorem scalarLinearMatrix : Specs.TensorAdelicReduction.scalarLinearMatrix := by
  intro k K I N A _ _ _ _ _ _ _ _ b c m hm
  let e := b.equivFun.trans ((Matrix.GeneralLinearGroup.toLin m).toLinearEquiv.trans b.equivFun.symm)
  have hE (j : A) (x : I → K) : e (c j • x) = c j • e x := hm j x
  have hs (a : K) (x : I → K) : e (a • x) = a • e x := by
    conv => lhs; rw [← c.sum_repr a]
    conv => rhs; rw [← c.sum_repr a]
    simp only [Finset.sum_smul, smul_assoc, map_sum, map_smul, hE]
  let f : (I → K) →ₗ[K] (I → K) :=
    { toFun := e, map_add' := e.map_add, map_smul' := hs }
  let g := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.ofBijective f e.bijective))
  refine ⟨g, ?_⟩
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply Units.ext
  apply LinearMap.ext
  intro x
  let y := b.equivFun.symm x
  have hy : b.equivFun y = x := b.equivFun.apply_symm_apply _
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  rw [← hy]
  rw [restrictMatrix_mulVec]
  have hg (z : I → K) : g.val.mulVec z = e z := by
    change (Matrix.GeneralLinearGroup.toLin g).val z = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hg]
  exact b.equivFun.apply_symm_apply _

theorem restrictedProductSplit : Specs.TensorAdelicReduction.restrictedProductSplit := by
  classical
  intro J G _ U S hS hOpen
  let X := Πʳ j : S, [G j, U j]
  let Y := ∀ j : (Sᶜ : Set J), G j
  let Z := Πʳ j, [G j, U j]
  let restrict : Z → X :=
    RestrictedProduct.mapAlong G (fun j : S => G j) Subtype.val
      Subtype.val_injective.tendsto_cofinite (fun _ g => g)
      (Filter.Eventually.of_forall fun _ => Set.mapsTo_id _)
  have hRestrict : Continuous restrict :=
    RestrictedProduct.mapAlong_continuous G (fun j : S => G j) Subtype.val
      Subtype.val_injective.tendsto_cofinite (fun _ g => g)
      (Filter.Eventually.of_forall fun _ => Set.mapsTo_id _) (fun _ => continuous_id)
  let split (a : Z) : X × Y := (restrict a, fun j => a j)
  let value (a : X × Y) (j : J) : G j :=
    if h : j ∈ S then a.1 ⟨j, h⟩ else a.2 ⟨j, h⟩
  have hCofinite (T : Set S) (hT : Tᶜ.Finite) : (Subtype.val '' T : Set J)ᶜ.Finite := by
    apply (hS.union (hT.image Subtype.val)).subset
    intro j hj
    by_cases h : j ∈ S
    · right
      exact ⟨⟨j, h⟩, fun hj' => hj ⟨⟨j, h⟩, hj', rfl⟩, rfl⟩
    · left
      exact h
  let glue (a : X × Y) : Z := ⟨value a, by
    let T : Set S := {j | a.1 j ∈ U j}
    have hT : Tᶜ.Finite := Filter.mem_cofinite.mp a.1.property
    refine Filter.mem_of_superset (Filter.mem_cofinite.mpr (hCofinite T hT)) ?_
    rintro j ⟨w, hw, rfl⟩
    change value a w.val ∈ U w.val
    rw [show value a w.val = a.1 w by simp [value, w.property]]
    exact hw⟩
  have hGlue : Continuous glue := by
    apply (RestrictedProduct.continuous_dom_prod_right (fun j : S => hOpen j)).mpr
    intro T hT
    have hT' : Filter.cofinite ≤ 𝓟 (Subtype.val '' T : Set J) :=
      Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr
        (hCofinite T (Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hT))))
    let v (a : (Πʳ j : S, [G j, U j]_[𝓟 T]) × Y) :
        Πʳ j, [G j, U j]_[𝓟 (Subtype.val '' T)] :=
      ⟨value ((RestrictedProduct.inclusion _ _ hT a.1), a.2), by
        rw [Filter.eventually_principal]
        rintro _ ⟨w, hw, rfl⟩
        change value (RestrictedProduct.inclusion _ _ hT a.1, a.2) w.val ∈ U w.val
        rw [show value (RestrictedProduct.inclusion _ _ hT a.1, a.2) w.val =
            a.1 w by simp only [value, dite_eq_left w.property]; rfl]
        exact a.1.property hw⟩
    have hv : Continuous v := by
      apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
      intro j
      by_cases hj : j ∈ S
      · change Continuous (fun a : (Πʳ j : S, [G j, U j]_[𝓟 T]) × Y =>
          value (RestrictedProduct.inclusion _ _ hT a.1, a.2) j)
        simp only [value, dite_eq_left hj]
        let f : (Πʳ j : S, [G j, U j]_[𝓟 T]) → G j := fun a => a ⟨j, hj⟩
        have hf : Continuous f := RestrictedProduct.continuous_eval (⟨j, hj⟩ : S)
        exact hf.comp continuous_fst
      · change Continuous (fun a : (Πʳ j : S, [G j, U j]_[𝓟 T]) × Y =>
          value (RestrictedProduct.inclusion _ _ hT a.1, a.2) j)
        simp only [value, dite_eq_right hj]
        exact (continuous_apply (⟨j, hj⟩ : (Sᶜ : Set J))).comp continuous_snd
    exact (RestrictedProduct.continuous_inclusion hT').comp hv
  let e : Z ≃ₜ X × Y :=
    { toFun := split
      invFun := glue
      left_inv := by
        intro a
        apply RestrictedProduct.ext
        intro j
        change value (split a) j = a j
        by_cases hj : j ∈ S
        · simp only [value, hj, dite_eq_left, split]
          rfl
        · simp [value, hj, split]
      right_inv := by
        intro a
        apply Prod.ext
        · apply RestrictedProduct.ext
          intro j
          change value a j = a.1 j
          simp [value, j.property]
        · funext j
          change value a j = a.2 j
          simp [value, show (j : J) ∉ S from j.property]
      continuous_toFun := hRestrict.prodMk (continuous_pi fun j => RestrictedProduct.continuous_eval j.val)
      continuous_invFun := hGlue }
  exact ⟨e, fun _ _ => rfl, fun _ _ => rfl⟩

private def changeIndexHomeomorph {J : Type*} (A : J → Type*)
    [∀ j, TopologicalSpace (A j)] {i j : J} (h : i = j) : A i ≃ₜ A j := by
  subst j
  exact Homeomorph.refl _

private theorem restrictedReindex {I J : Type*} {A : I → Type*} {B : J → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ j, TopologicalSpace (B j)]
    (e : I ≃ J) (f : ∀ i, A i ≃ₜ B (e i)) (U : ∀ i, Set (A i)) (V : ∀ j, Set (B j))
    (hf : ∀ i x, f i x ∈ V (e i) ↔ x ∈ U i) :
    ∃ E : (Πʳ j, [B j, V j]) ≃ₜ (Πʳ i, [A i, U i]),
      ∀ b i, E b i = (f i).symm (b (e i)) := by
  let q : (Πʳ j, [B j, V j]) → (Πʳ i, [A i, U i]) :=
    RestrictedProduct.mapAlong B A e e.injective.tendsto_cofinite (fun i => (f i).symm)
      (Filter.Eventually.of_forall fun i x hx => (hf i _).mp (by simpa using hx))
  have hq : Continuous q :=
    RestrictedProduct.mapAlong_continuous B A e e.injective.tendsto_cofinite (fun i => (f i).symm)
      _ (fun i => (f i).symm.continuous)
  let f' (j : J) := (f (e.symm j)).trans (changeIndexHomeomorph B (e.apply_symm_apply j))
  have hCast (i j : J) (h : i = j) (x : B i) :
      changeIndexHomeomorph B h x ∈ V j ↔ x ∈ V i := by
    subst j
    rfl
  let p : (Πʳ i, [A i, U i]) → (Πʳ j, [B j, V j]) :=
    RestrictedProduct.mapAlong A B e.symm e.symm.injective.tendsto_cofinite (fun j => f' j)
      (Filter.Eventually.of_forall fun j x hx =>
        (hCast _ _ _ _).mpr ((hf (e.symm j) x).mpr hx))
  have hp : Continuous p :=
    RestrictedProduct.mapAlong_continuous A B e.symm e.symm.injective.tendsto_cofinite (fun j => f' j)
      _ (fun j => (f' j).continuous)
  have hqInj : Function.Injective q := by
    intro x y h
    apply RestrictedProduct.ext
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact (f i).symm.injective (congrArg (fun z : Πʳ i, [A i, U i] => z i) h)
  have hright (b : Πʳ j, [B j, V j]) : p (q b) = b := by
    apply RestrictedProduct.ext
    intro j
    change changeIndexHomeomorph B (e.apply_symm_apply j)
      (f (e.symm j) ((f (e.symm j)).symm (b (e (e.symm j))))) = b j
    rw [(f (e.symm j)).apply_symm_apply]
    have h (i j : J) (hij : i = j) : changeIndexHomeomorph B hij (b i) = b j := by
      subst j
      rfl
    exact h _ _ _
  have hleft (a : Πʳ i, [A i, U i]) : q (p a) = a := by
    apply RestrictedProduct.ext
    intro i
    apply (f i).injective
    change f i ((f i).symm (f' (e i) (a (e.symm (e i))))) = f i (a i)
    rw [(f i).apply_symm_apply]
    have h (i' : I) (hi : i' = i) (h' : e i' = e i) :
        changeIndexHomeomorph B h' (f i' (a i')) = f i (a i) := by
      subst i'
      rfl
    exact h _ (e.symm_apply_apply i) _
  exact ⟨⟨⟨q, p, hright, hleft⟩, hq, hp⟩, fun _ _ => rfl⟩

private def generalLinearHomeomorph {A B I : Type*} [CommRing A] [CommRing B]
    [Fintype I] [DecidableEq I] [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃+* B) (h : Continuous e) (h' : Continuous e.symm) :
    Matrix.GeneralLinearGroup I A ≃ₜ Matrix.GeneralLinearGroup I B :=
  { toFun := Matrix.GeneralLinearGroup.map e.toRingHom
    invFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
    left_inv := fun m => Units.ext (Matrix.ext fun i j => e.symm_apply_apply (m.val i j))
    right_inv := fun m => Units.ext (Matrix.ext fun i j => e.apply_symm_apply (m.val i j))
    continuous_toFun := h.generalLinearGroup_map
    continuous_invFun := h'.generalLinearGroup_map }

theorem functionMatrixAdeleComparison :
    Specs.TensorAdelicReduction.functionMatrixAdeleComparison := by
  classical
  intro F K I _ _ _ _ _ _ t P
  let S := {w : FunctionPlace K | t.element ∈ w.val}
  have hS : Sᶜ.Finite := t.finite_poles
  let U (v : FunctionPlace K) := (↑(integralMatrices (I := I) v.integers.toSubring) :
    Set (Matrix.GeneralLinearGroup I v.Completion))
  let V (v : HeightOneSpectrum t.integerRing) :=
    (↑(integralMatrices (I := I) (v.adicCompletionIntegers K).toSubring) :
      Set (Matrix.GeneralLinearGroup I (v.adicCompletion K)))
  obtain ⟨e, hFin, hInf⟩ := restrictedProductSplit U S hS (fun v =>
    integralMatrices_isOpen v.integers (FunctionPlace.completionIntegers_properties t v).2.1)
  let place (v : HeightOneSpectrum t.integerRing) : S :=
    ⟨t.placeOfPrime v, by
      change t.placeOfPrime v ∈ {w : FunctionPlace K | t.element ∈ w.val}
      rw [← t.range_placeOfPrime]
      exact Set.mem_range_self v⟩
  let hBij : Function.Bijective place :=
    ⟨fun _ _ h => t.placeOfPrime_injective (congrArg Subtype.val h),
      fun w => by
        obtain ⟨v, hv⟩ := (show w.val ∈ Set.range t.placeOfPrime from
          t.range_placeOfPrime.symm ▸ w.property)
        exact ⟨v, Subtype.ext hv⟩⟩
  let E := Equiv.ofBijective place hBij
  let f (v : HeightOneSpectrum t.integerRing) : (E v).val.Completion ≃+* v.adicCompletion K :=
    t.completionEquiv v
  have hf (v : HeightOneSpectrum t.integerRing) : Continuous (f v) :=
    (t.completionEquiv_isUniformInducing v).uniformContinuous.continuous
  have hf' (v : HeightOneSpectrum t.integerRing) : Continuous (f v).symm := by
    change Continuous (t.completionEquiv v).symm
    apply (t.completionEquiv_isUniformInducing v).isInducing.continuous_iff.mpr
    rw [show (t.completionEquiv v : _ → _) ∘ (t.completionEquiv v).symm = id from
      funext (t.completionEquiv v).apply_symm_apply]
    exact continuous_id
  let chart (v : HeightOneSpectrum t.integerRing) :=
    generalLinearHomeomorph (I := I) (f v).symm (hf' v) (hf v)
  have hChart (v : HeightOneSpectrum t.integerRing)
      (m : Matrix.GeneralLinearGroup I (v.adicCompletion K)) :
      chart v m ∈ U (E v) ↔ m ∈ V v := by
    change Matrix.GeneralLinearGroup.map (t.completionEquiv v).symm.toRingHom m ∈
      integralMatrices (I := I) (t.placeOfPrime v).integers.toSubring ↔
      m ∈ integralMatrices (v.adicCompletionIntegers K).toSubring
    rw [integralIffEntries, integralIffEntries]
    change ((∀ i j, (f v).symm (m.val i j) ∈ (t.placeOfPrime v).integers) ∧
      ∀ i j, (chart v m)⁻¹.val i j ∈ (t.placeOfPrime v).integers) ↔ _
    have h (u : v.adicCompletion K) :
        (f v).symm u ∈ (t.placeOfPrime v).integers ↔ u ∈ v.adicCompletionIntegers K := by
      change (t.completionEquiv v).symm u ∈ (t.placeOfPrime v).integers ↔
        u ∈ v.adicCompletionIntegers K
      simpa only [RingEquiv.apply_symm_apply] using
        (t.completionEquiv_mem_integers v ((t.completionEquiv v).symm u)).symm
    have hi : (chart v m)⁻¹ = chart v m⁻¹ :=
      (map_inv (Matrix.GeneralLinearGroup.map (f v).symm.toRingHom) m).symm
    rw [hi]
    change ((∀ i j, (f v).symm (m.val i j) ∈ (t.placeOfPrime v).integers) ∧
      ∀ i j, (f v).symm (m⁻¹.val i j) ∈ (t.placeOfPrime v).integers) ↔
      ((∀ i j, m.val i j ∈ v.adicCompletionIntegers K) ∧
        ∀ i j, m⁻¹.val i j ∈ v.adicCompletionIntegers K)
    simp only [h]
  obtain ⟨e', he'⟩ := restrictedReindex E chart V (fun w => U w.val) hChart
  refine ⟨e.trans (e'.prodCongr (Homeomorph.refl _)), hInf, ?_⟩
  intro v
  refine ⟨t.completionEquiv v, t.completionEquiv_embedding v, ?_⟩
  intro g
  change e' (e g).1 v = _
  rw [he', hFin]
  rfl


private theorem transformedTensor_one {A X I O : Type*} [CommRing A] [Fintype X]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (T : TensorCoefficients A X I O) : transformedTensor T 1 1 = T := by
  funext w
  have hcol (i : I) : (1 : Matrix I I A).col i = Pi.basisFun A I i := by
    ext j
    simp [Matrix.one_apply, Pi.basisFun_apply, Pi.single_apply]
  simp only [transformedTensor, inv_one, Matrix.GeneralLinearGroup.coe_one,
    Matrix.one_mulVec, hcol, coordinateTensor_basis]

private theorem preservesTensor_iff {A X I O : Type*} [CommRing A] [Fintype X]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (T : TensorCoefficients A X I O) (m : Matrix.GeneralLinearGroup I A)
    (n : Matrix.GeneralLinearGroup O A) :
    PreservesTensor T m n ↔ transformedTensor T m n = T := by
  constructor
  · intro h
    simpa only [mul_one, transformedTensor_one] using
      (tensorTransport (RingHom.id A) T 1 1).2 m n h
  · intro h
    have ht : transformedTensor T m n = transformedTensor T 1 1 :=
      h.trans (transformedTensor_one T).symm
    simpa only [inv_one, mul_one] using tensorLabelComparison T m 1 n 1 ht

private theorem preservesTensor_map {A B X I O : Type*} [CommRing A] [CommRing B] [Fintype X]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (f : A →+* B) (T : TensorCoefficients A X I O) (m : Matrix.GeneralLinearGroup I A)
    (n : Matrix.GeneralLinearGroup O A) (h : PreservesTensor T m n) :
    PreservesTensor (fun w i => f (T w i))
      (Matrix.GeneralLinearGroup.map f m) (Matrix.GeneralLinearGroup.map f n) := by
  apply (preservesTensor_iff _ _ _).mpr
  have hT := (preservesTensor_iff _ _ _).mp h
  funext w i
  rw [(tensorTransport f T m n).1, hT]

private theorem preservesTensor_mul {A X I : Type*} [CommRing A] [Fintype X]
    [Fintype I] [DecidableEq I] (T : TensorCoefficients A X I I)
    (m n : Matrix.GeneralLinearGroup I A)
    (hm : PreservesTensor T m m) (hn : PreservesTensor T n n) :
    PreservesTensor T (m * n) (m * n) := by
  intro v
  simp only [mulVec_action]
  rw [hm, hn]

/-- A fixed scalar coordinate of a tensor can be tested by scaling one extra vector. -/
private def fixedCoordinateTensor {A X I O : Type*} [CommRing A] [Fintype I] [DecidableEq I]
    (T : TensorCoefficients A X I O) (o : O) : TensorCoefficients A (Option X) I I :=
  fun w i => T (w ∘ some) o * (Pi.basisFun A I (w none)) i

private theorem fixedCoordinateTensor_apply {A X I O : Type*} [CommRing A] [Fintype X]
    [Fintype I] [DecidableEq I] (T : TensorCoefficients A X I O) (o : O)
    (v : Option X → I → A) :
    coordinateTensor (fixedCoordinateTensor T o) v =
      (coordinateTensor T (v ∘ some) o) • v none := by
  funext i
  classical
  let : DecidableEq (Option X) := fun _ _ => Classical.propDecidable _
  let : DecidableEq X := fun _ _ => Classical.propDecidable _
  rw [coordinateTensor_apply]
  let e : (Option X → I) ≃ I × (X → I) := Equiv.piOptionEquivProd
  let a (w : Option X → I) := (∏ x, v x (w x)) * fixedCoordinateTensor T o w i
  change (∑ w, a w) = _
  rw [← e.symm.sum_comp a, Fintype.sum_prod_type]
  simp only [a, fixedCoordinateTensor, Fintype.prod_option]
  change (∑ k : I, ∑ w : X → I,
    (v none k * ∏ x : X, v (some x) (w x)) * (T w o * (Pi.basisFun A I k) i)) = _
  rw [Finset.sum_eq_single i]
  · simp only [Pi.basisFun_apply, Pi.single_eq_same, mul_one, Pi.smul_apply, smul_eq_mul]
    rw [coordinateTensor_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Function.comp_apply]
    ring
  · intro k _ hk
    simp [Pi.basisFun_apply, Ne.symm hk]
  · simp

private theorem fixedCoordinateTensor_map {A B X I O : Type*} [CommRing A] [CommRing B]
    [Fintype I] [DecidableEq I] (f : A →+* B) (T : TensorCoefficients A X I O) (o : O) :
    (fun w i => f (fixedCoordinateTensor T o w i)) =
      fixedCoordinateTensor (fun w j => f (T w j)) o := by
  funext w i
  by_cases hi : i = w none <;> simp [fixedCoordinateTensor, Pi.basisFun_apply, hi]

private theorem fixedCoordinateTensor_preserves {A X I O : Type*} [Field A] [Fintype X]
    [Fintype I] [DecidableEq I]
    (T : TensorCoefficients A X I O) (o : O) (m : Matrix.GeneralLinearGroup I A) :
    PreservesTensor (fixedCoordinateTensor T o) m m ↔
      ∀ v : X → I → A, coordinateTensor T (fun x => m.val.mulVec (v x)) o =
        coordinateTensor T v o := by
  constructor
  · intro h v
    cases isEmpty_or_nonempty I with
    | inl hI =>
      let := hI
      exact congrArg (fun z => coordinateTensor T z o) (Subsingleton.elim _ _)
    | inr hI =>
      let i := hI.some
      let z : Option X → I → A := fun a => a.elim (m⁻¹.val.mulVec (Pi.basisFun A I i)) v
      have hz := h z
      simp only [fixedCoordinateTensor_apply, Matrix.mulVec_smul, z, Option.elim_none,
        mulVec_inv_action, Function.comp_def, Option.elim_some] at hz
      simpa [Pi.basisFun_apply] using congrFun hz i
  · intro h z
    simp only [fixedCoordinateTensor_apply, Matrix.mulVec_smul, Function.comp_def]
    rw [h (fun x => z (some x))]

universe u

private def scalarTensor {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I] (a : A) :
    TensorCoefficients A (Option PEmpty.{u + 1}) I I :=
  fixedCoordinateTensor (fun _ (_ : Unit) => a) ()

private theorem scalarTensor_apply {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]
    (a : A) (v : Option PEmpty.{u + 1} → I → A) :
    coordinateTensor (scalarTensor a) v = a • v none := by
  rw [scalarTensor, fixedCoordinateTensor_apply, coordinateTensor_apply]
  simp

private abbrev TensorLabelIndex (J H : Type*) (O : H → Type*) (D : Type*) :=
  (J ⊕ (Σ h, O h)) ⊕ D

private abbrev tensorLabelSlots {J H : Type*} {O : H → Type*} {D : Type*}
    (X : J → Type u) (Y : H → Type u) : TensorLabelIndex J H O D → Type u
  | .inl (.inl j) => X j
  | .inl (.inr o) => Option (Y o.1)
  | .inr _ => Option PEmpty.{u + 1}

private instance {J H : Type*} {O : H → Type*} {D : Type*}
    (X : J → Type u) (Y : H → Type u) [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)] :
    ∀ a : TensorLabelIndex J H O D, Fintype (tensorLabelSlots X Y a)
  | .inl (.inl j) => inferInstanceAs (Fintype (X j))
  | .inl (.inr o) => inferInstanceAs (Fintype (Option (Y o.1)))
  | .inr _ => inferInstanceAs (Fintype (Option PEmpty.{u + 1}))

private def tensorLabelSystem {K I J H D : Type*} {O : H → Type*}
    {X : J → Type u} {Y : H → Type u} [CommRing K] [Fintype I] [DecidableEq I]
    (T : TensorSystem K I X Y O) (c : D → K) :
    ∀ a : TensorLabelIndex J H O D, TensorCoefficients K (tensorLabelSlots X Y a) I I
  | .inl (.inl j) => T.moving j
  | .inl (.inr o) => fixedCoordinateTensor (T.fixed o.1) o.2
  | .inr j => scalarTensor (c j)

private theorem tensorLabelSystem_preserves {K L I J H D : Type*} {O : H → Type*}
    {X : J → Type u} {Y : H → Type u} [Field K] [Field L] [Fintype I] [DecidableEq I]
    [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)]
    (T : TensorSystem K I X Y O) (c : D → K) (e : K →+* L)
    (m : Matrix.GeneralLinearGroup I L) :
    T.Preserves e m ↔ ∀ a : TensorLabelIndex J H O D,
      PreservesTensor (fun w i => e (tensorLabelSystem T c a w i)) m m := by
  constructor
  · intro h a
    rcases a with (j | o) | j
    · exact h.1 j
    · rw [show (fun w i => e (tensorLabelSystem T c (.inl (.inr o)) w i)) =
          fixedCoordinateTensor (fun w k => e (T.fixed o.1 w k)) o.2 from
          fixedCoordinateTensor_map e _ _]
      apply (fixedCoordinateTensor_preserves _ _ _).mpr
      exact fun v => congrFun (h.2 o.1 v) o.2
    · intro v
      change coordinateTensor (fun w i => e (scalarTensor (c j) w i))
        (fun x : Option PEmpty.{u + 1} => m.val.mulVec (v x)) =
        m.val.mulVec (coordinateTensor (fun w i => e (scalarTensor (c j) w i)) v)
      rw [show (fun w i => e (scalarTensor (c j) w i)) = scalarTensor (e (c j)) from
        fixedCoordinateTensor_map e _ _]
      simp only [scalarTensor_apply, Matrix.mulVec_smul]
  · intro h
    refine ⟨fun j => h (.inl (.inl j)), ?_⟩
    intro j v
    funext o
    have hj := h (.inl (.inr ⟨j, o⟩))
    change PreservesTensor (fun w i => e (fixedCoordinateTensor (T.fixed j) o w i)) m m at hj
    rw [fixedCoordinateTensor_map] at hj
    exact (fixedCoordinateTensor_preserves _ _ _).mp hj v

private theorem restrictedTensor_apply {k K X I N : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype X] [Fintype I] [Fintype N]
    (b : Module.Basis N k (I → K)) (T : TensorCoefficients K X I I) (v : X → I → K) :
    coordinateTensor (restrictedTensor b b T) (fun x => b.equivFun (v x)) =
      b.equivFun (coordinateTensor T v) := by
  let E := b.equivFun.symm.trans (LinearEquiv.funUnique Unit k (I → K)).symm
  have hE (x : I → K) (j : Unit) (i : I) :
      E (fun n => (RingHom.id k) (b.equivFun x n)) j i = (RingHom.id K) (x i) :=
    congrFun (b.equivFun.symm_apply_apply x) i
  have ht := localTensorComparison (RingHom.id k) (fun _ : Unit => RingHom.id K) b b E E hE hE
    T (fun x => b.equivFun (v x)) ()
  apply b.equivFun.symm.injective
  change b.equivFun.symm (coordinateTensor (restrictedTensor b b T) _) = _
  rw [b.equivFun.symm_apply_apply]
  change b.equivFun.symm (coordinateTensor (restrictedTensor b b T) _) =
    coordinateTensor T (fun x => b.equivFun.symm (b.equivFun (v x))) at ht
  simpa only [LinearEquiv.symm_apply_apply] using ht

private theorem restrictedTensor_intertwines {k K X I N : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype X] [Fintype I] [Fintype N] [DecidableEq N]
    (b : Module.Basis N k (I → K)) (T : TensorCoefficients K X I I)
    (m : Matrix.GeneralLinearGroup N k) (h : PreservesTensor (restrictedTensor b b T) m m)
    (v : X → I → K) :
    coordinateTensor T (fun x => b.equivFun.symm (m.val.mulVec (b.equivFun (v x)))) =
      b.equivFun.symm (m.val.mulVec (b.equivFun (coordinateTensor T v))) := by
  apply b.equivFun.injective
  rw [← restrictedTensor_apply, LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.apply_symm_apply, restrictedTensor_apply] using
    h (fun x => b.equivFun (v x))

private theorem rationalTensorLabelComparison {k K I N J H D : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    [Fintype D] {O : H → Type*} {X : J → Type u} {Y : H → Type u}
    [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)]
    (b : Module.Basis N k (I → K)) (c : Module.Basis D k K) (T : TensorSystem K I X Y O)
    (m n : Matrix.GeneralLinearGroup N k)
    (h : (fun a : TensorLabelIndex J H O D =>
      transformedTensor (restrictedTensor b b (tensorLabelSystem T c a)) m m) =
      (fun a => transformedTensor (restrictedTensor b b (tensorLabelSystem T c a)) n n)) :
    ∃ r : Matrix.GeneralLinearGroup I K, restrictMatrix b r = m * n⁻¹ ∧ T.Preserves (RingHom.id K) r := by
  let S (a : TensorLabelIndex J H O D) := tensorLabelSystem T c a
  let M := m * n⁻¹
  have hPres (a : TensorLabelIndex J H O D) : PreservesTensor (restrictedTensor b b (S a)) M M :=
    tensorLabelComparison _ _ _ _ _ (congrFun h a)
  have hScalar (j : D) (x : I → K) :
      b.equivFun.symm (M.val.mulVec (b.equivFun (c j • x))) =
        c j • b.equivFun.symm (M.val.mulVec (b.equivFun x)) := by
    have ht := restrictedTensor_intertwines b (S (.inr j)) M (hPres (.inr j)) (fun _ => x)
    change coordinateTensor (scalarTensor (c j))
      (fun _ : Option PEmpty.{u + 1} => b.equivFun.symm (M.val.mulVec (b.equivFun x))) =
      b.equivFun.symm (M.val.mulVec (b.equivFun
        (coordinateTensor (scalarTensor (c j)) (fun _ : Option PEmpty.{u + 1} => x)))) at ht
    rw [scalarTensor_apply, scalarTensor_apply] at ht
    exact ht.symm
  obtain ⟨r, hr⟩ := scalarLinearMatrix b c M hScalar
  refine ⟨r, hr, (tensorLabelSystem_preserves T c (RingHom.id K) r).mpr fun a v => ?_⟩
  have ht := restrictedTensor_intertwines b (S a) _ (hr.symm ▸ hPres a) v
  change coordinateTensor (S a) (fun x => r.val.mulVec (v x)) =
    r.val.mulVec (coordinateTensor (S a) v)
  simpa only [restrictMatrix_mulVec, LinearEquiv.symm_apply_apply] using ht

private theorem continuousFinite_mul_const {R k N : Type*} [CommRing R] [IsDedekindDomain R]
    [Field k] [Algebra R k] [IsFractionRing R k] [Fintype N] [DecidableEq N]
    (g : FiniteMatrices R k N) : Continuous (fun a : FiniteMatrices R k N => a * g) := by
  let G (q : HeightOneSpectrum R) := Matrix.GeneralLinearGroup N (q.adicCompletion k)
  let U (q : HeightOneSpectrum R) : Subgroup (G q) :=
    (Matrix.GeneralLinearGroup.map (q.adicCompletionIntegers k).subtype).range
  have h : ∀ᶠ q in Filter.cofinite, MapsTo (fun a : G q => a * g q) (U q) (U q) :=
    g.property.mono fun q hq _ ha => (U q).mul_mem ha hq
  exact RestrictedProduct.mapAlong_continuous G G
    (A₁ := fun q => (U q : Set (G q))) (A₂ := fun q => (U q : Set (G q)))
    id Filter.tendsto_id (fun q (a : G q) => a * g q) h
    (fun q => show Continuous (fun a : G q => a * g q) from continuous_id.mul continuous_const)

open LatticeCompletionDecompositionSpec in
private theorem finiteTensorPreservation {R A k K I N X : Type*}
    [CommRing R] [IsDedekindDomain R] [CommRing A] [IsDedekindDomain A]
    [Algebra R A] [Module.IsTorsionFree R A] [Field k] [Field K] [Algebra k K]
    [Algebra R k] [IsFractionRing R k] [Algebra A K] [IsFractionRing A K]
    [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N] [Fintype X]
    (b : Module.Basis N k (I → K))
    (g : ∀ v : HeightOneSpectrum A, Matrix.GeneralLinearGroup I (v.adicCompletion K))
    (p : HeightOneSpectrum R) (G : Matrix.GeneralLinearGroup N (p.adicCompletion k))
    (h : FiniteMatrixAction b g p G) (T : TensorCoefficients K X I I)
    (hT : ∀ v, PreservesTensor (fun w i => algebraMap K (v.adicCompletion K) (T w i)) (g v) (g v)) :
    PreservesTensor
      (fun w i => algebraMap k (p.adicCompletion k) (restrictedTensor b b T w i)) G G := by
  obtain ⟨a, E, hE, hG⟩ := h
  let := a
  exact localTensorPreservation (algebraMap k (p.adicCompletion k))
    (fun j => algebraMap K ((primeAbove p j).adicCompletion K)) b b
    E.toLinearEquiv E.toLinearEquiv
    (fun x j i => congrFun (hE x j) i) (fun x j i => congrFun (hE x j) i)
    T _ _ G G hG hG (fun j => hT (primeAbove p j))

open LatticeCompletionDecompositionSpec in
private theorem finiteMatrixAction_mul_diagonal {R A k K I N : Type*}
    [CommRing R] [IsDedekindDomain R] [CommRing A] [IsDedekindDomain A]
    [Algebra R A] [Module.IsTorsionFree R A] [Field k] [Field K] [Algebra k K]
    [Algebra R k] [IsFractionRing R k] [Algebra A K] [IsFractionRing A K]
    [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (b : Module.Basis N k (I → K))
    (g : ∀ v : HeightOneSpectrum A, Matrix.GeneralLinearGroup I (v.adicCompletion K))
    (p : HeightOneSpectrum R) (G : Matrix.GeneralLinearGroup N (p.adicCompletion k))
    (h : FiniteMatrixAction b g p G) (r : Matrix.GeneralLinearGroup I K) :
    FiniteMatrixAction b
      (fun v => g v * Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) r) p
      (G * Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) (restrictMatrix b r)) := by
  obtain ⟨a, E, hE, hG⟩ := h
  let := a
  have hr := rationalMatrixComparison (algebraMap k (p.adicCompletion k))
    (fun j => algebraMap K ((primeAbove p j).adicCompletion K)) b E.toLinearEquiv hE r
  refine ⟨a, E, hE, ?_⟩
  intro z j
  change E ((G * Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k))
    (restrictMatrix b r)).val.mulVec z) j =
      (g (primeAbove p j) * Matrix.GeneralLinearGroup.map
        (algebraMap K ((primeAbove p j).adicCompletion K)) r).val.mulVec (E z j)
  rw [mulVec_action, hG, mulVec_action]
  exact congrArg (g (primeAbove p j)).val.mulVec (hr z j)

private theorem isClosed_preservesTensor {A X I : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [Fintype X] [Fintype I] [DecidableEq I] (T : TensorCoefficients A X I I) :
    IsClosed {m : Matrix.GeneralLinearGroup I A | PreservesTensor T m m} := by
  simp only [preservesTensor_iff]
  exact isClosed_eq ((transformedTensorContinuous T).comp (continuous_id.prodMk continuous_id))
    continuous_const

set_option maxHeartbeats 1200000 in
/-- Combine compact bounds in base coordinates with tensor and scalar labels.
Equality of labels gives a relative change of basis over the original field. -/
private theorem splitTensorAdelicReduction {R A k K B I N W P J H : Type*}
    [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [Module.Finite R A]
    [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K]
    [Algebra R k] [IsFractionRing R k] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K] [Fintype I] [DecidableEq I]
    [Fintype N] [DecidableEq N] [Field B] [TopologicalSpace B] [IsTopologicalRing B]
    {L : W → Type*} [∀ w, Field (L w)] [∀ w, TopologicalSpace (L w)]
    [∀ w, T2Space (L w)] [∀ w, IsTopologicalRing (L w)] [∀ w, Algebra B (L w)]
    [Finite J] [Finite H] {X : J → Type u} {Y : H → Type u} {O : H → Type*}
    [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)] [∀ h, Finite (O h)]
    (f : k →+* B) (e : ∀ w, K →+* L w) (b : Module.Basis N k (I → K))
    (E : (N → B) ≃L[B] (∀ w, I → L w))
    (hb : IsBasisMatrix R b (referenceLattice A K I : Set (I → K)) 1)
    (hE : ∀ x w, E (embedCoordinates f (b.equivFun x)) w = embedCoordinates (e w) x)
    (hc : IsClosed (Set.range (baseScalarDiagonal (R := R) f)))
    (hd : IsDiscrete (Set.range (baseScalarDiagonal (R := R) f)))
    (p : P → MvPolynomial I K) (T : TensorSystem K I X Y O)
    (C : Set (BasisAdeles R k B N)) (hC : IsCompact C)
    (hBound : ∀ (g : FiniteMatrices A K I) (gInf : ∀ w, Matrix.GeneralLinearGroup I (L w)),
      (∀ v, (g v).det = 1) → (∀ w, (gInf w).det = 1) →
      PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g →
      PreservesPolynomials e p gInf →
      ∃ (G : ∀ q : HeightOneSpectrum R, Matrix.GeneralLinearGroup N (q.adicCompletion k))
        (GInf : Matrix.GeneralLinearGroup N B) (M : Matrix.GeneralLinearGroup N k)
        (hI : FiniteBasisIntegral G M),
        (∀ q, FiniteMatrixAction b g q (G q)) ∧
        (∀ z w, E (GInf.val.mulVec z) w = (gInf w).val.mulVec (E z w)) ∧
        (finiteBasisRepresentative G M hI, GInf * Matrix.GeneralLinearGroup.map f M) ∈ C) :
    ∃ δ : Matrix.GeneralLinearGroup I K →* SplitMatrixAdeles A K I L,
      (∀ r v, (δ r).1 v = Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) r) ∧
      (∀ r w, (δ r).2 w = Matrix.GeneralLinearGroup.map (e w) r) ∧
      ∃ C' : Set (SplitMatrixAdeles A K I L), IsCompact C' ∧
        (∀ h ∈ C', T.PreservesSplit e h) ∧
        ∀ g : SplitMatrixAdeles A K I L,
          (∀ v, (g.1 v).det = 1) → (∀ w, (g.2 w).det = 1) →
          PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g.1 →
          PreservesPolynomials e p g.2 → T.PreservesSplit e g →
          ∃ r : Matrix.GeneralLinearGroup I K, T.Preserves (RingHom.id K) r ∧ g * δ r ∈ C' := by
  classical
  obtain ⟨δFin, hδFin⟩ := finiteMatrixDiagonal (R := A) (k := K) (N := I)
  let δ : Matrix.GeneralLinearGroup I K →* SplitMatrixAdeles A K I L :=
    δFin.prod (MonoidHom.pi fun w => Matrix.GeneralLinearGroup.map (e w))
  obtain ⟨δBase, hδBase⟩ := finiteMatrixDiagonal (R := R) (k := k) (N := N)
  let δ₀ := δBase.prod (Matrix.GeneralLinearGroup.map f)
  let U := {g : SplitMatrixAdeles A K I L |
    (∀ v, (g.1 v).det = 1) ∧ (∀ w, (g.2 w).det = 1) ∧
    PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g.1 ∧
    PreservesPolynomials e p g.2 ∧ T.PreservesSplit e g}
  choose G₀ GInf M hI hAct hInf hMem using fun x : U =>
    hBound x.val.1 x.val.2 x.property.1 x.property.2.1 x.property.2.2.1 x.property.2.2.2.1
  let Z (x : U) : BasisAdeles R k B N :=
    (finiteBasisRepresentative (G₀ x) (M x) (hI x), GInf x * Matrix.GeneralLinearGroup.map f (M x))
  let G (x : U) := Z x * δ₀ ((M x)⁻¹)
  have hGFin (x : U) (q : HeightOneSpectrum R) : (G x).1 q = G₀ x q := by
    change G₀ x q * Matrix.GeneralLinearGroup.map (algebraMap k (q.adicCompletion k)) (M x) *
      δBase ((M x)⁻¹) q = G₀ x q
    rw [hδBase, map_inv, mul_inv_cancel_right]
  have hGInf (x : U) : (G x).2 = GInf x := by
    change GInf x * Matrix.GeneralLinearGroup.map f (M x) *
      Matrix.GeneralLinearGroup.map f ((M x)⁻¹) = _
    rw [map_inv, mul_inv_cancel_right]
  have hZ (x : U) : Z x = G x * δ₀ (M x) := by
    simp only [G, map_inv, inv_mul_cancel_right]
  let D := Fin (Module.finrank k K)
  let c : Module.Basis D k K := Module.finBasis k K
  let S (a : TensorLabelIndex J H O D) := tensorLabelSystem T c a
  let T₀ (a : TensorLabelIndex J H O D) := restrictedTensor b b (S a)
  let label (x : U) := fun a => transformedTensor (T₀ a) (M x) (M x)
  have hPres (x : U) := x.property.2.2.2.2
  have hLabel : (Set.range label).Finite := by
    apply finiteTransformedTensorLabels f hc hd C hC T₀ M G Z hMem
    · intro x q
      have he := congrArg (fun a : BasisAdeles R k B N => a.1 q) (hZ x)
      change (Z x).1 q = (G x).1 q * δBase (M x) q at he
      rwa [hδBase] at he
    · exact fun x => congrArg Prod.snd (hZ x)
    · intro a x q
      rw [hGFin]
      exact finiteTensorPreservation b x.val.1 q (G₀ x q) (hAct x q) (S a)
        (fun v => (tensorLabelSystem_preserves T c _ _).mp ((hPres x).1 v) a)
    · intro a x
      rw [hGInf]
      exact localTensorPreservation f e b b E.toLinearEquiv E.toLinearEquiv
        (fun z w i => congrFun (hE z w) i) (fun z w i => congrFun (hE z w) i)
        (S a) x.val.2 x.val.2 (GInf x) (GInf x) (hInf x) (hInf x)
        (fun w => (tensorLabelSystem_preserves T c _ _).mp ((hPres x).2 w) a)
  let SAd : Set (SplitMatrixAdeles A K I L) := {g |
    (∀ v a, PreservesTensor (fun w i => algebraMap K (v.adicCompletion K) (S a w i))
      (g.1 v) (g.1 v)) ∧
    ∀ w a, PreservesTensor (fun x i => e w (S a x i)) (g.2 w) (g.2 w)}
  have hSAd (g : SplitMatrixAdeles A K I L) : g ∈ SAd ↔ T.PreservesSplit e g := by
    exact and_congr
      (forall_congr' fun v => (tensorLabelSystem_preserves T c _ (g.1 v)).symm)
      (forall_congr' fun w => (tensorLabelSystem_preserves T c _ (g.2 w)).symm)
  have hClosed : IsClosed SAd := by
    have hEq : SAd = (⋂ v : HeightOneSpectrum A, ⋂ a : TensorLabelIndex J H O D,
        (fun g : SplitMatrixAdeles A K I L => g.1 v) ⁻¹'
          {m | PreservesTensor (fun w i => algebraMap K (v.adicCompletion K) (S a w i)) m m}) ∩
        (⋂ w : W, ⋂ a : TensorLabelIndex J H O D, (fun g : SplitMatrixAdeles A K I L => g.2 w) ⁻¹'
          {m | PreservesTensor (fun x i => e w (S a x i)) m m}) := by
      ext g
      simp only [SAd, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rw [hEq]
    exact (isClosed_iInter fun v => isClosed_iInter fun a =>
      (isClosed_preservesTensor _).preimage ((RestrictedProduct.continuous_eval v).comp continuous_fst)).inter
      (isClosed_iInter fun w => isClosed_iInter fun a =>
        (isClosed_preservesTensor _).preimage ((continuous_apply w).comp continuous_snd))
  have hTranslate (y : U) :
      ∃ D' : Set (SplitMatrixAdeles A K I L), IsCompact D' ∧
        ∀ x : U, ∀ r : Matrix.GeneralLinearGroup I K,
          restrictMatrix b r = M x * (M y)⁻¹ → x.val * δ r ∈ D' := by
    let C₀ := (fun z : BasisAdeles R k B N => z * δ₀ ((M y)⁻¹)) '' C
    have hC₀ : IsCompact C₀ :=
      hC.image (((continuousFinite_mul_const (δ₀ ((M y)⁻¹)).1).comp continuous_fst).prodMk
        (continuous_snd.mul continuous_const))
    obtain ⟨Dfin, hDfin, hFin⟩ :=
      compactFiniteMatrixTransport b hb (Prod.fst '' C₀) (hC₀.image continuous_fst)
    obtain ⟨Dinf, hDinf, hDist⟩ :=
      compactLocalMatrixTransport E (Prod.snd '' C₀) (hC₀.image continuous_snd)
    refine ⟨Dfin ×ˢ Set.pi Set.univ Dinf, hDfin.prod (isCompact_univ_pi hDinf), ?_⟩
    intro x r hr
    let z := Z x * δ₀ ((M y)⁻¹)
    have hz : z ∈ C₀ := ⟨Z x, hMem x, rfl⟩
    have hzEq : z = G x * δ₀ (restrictMatrix b r) := by
      rw [hr, map_mul, ← mul_assoc, ← hZ]
    have hFinEq (q : HeightOneSpectrum R) :
        z.1 q = G₀ x q * Matrix.GeneralLinearGroup.map
          (algebraMap k (q.adicCompletion k)) (restrictMatrix b r) := by
      have he := congrArg (fun a : BasisAdeles R k B N => a.1 q) hzEq
      change z.1 q = (G x).1 q * δBase (restrictMatrix b r) q at he
      rwa [hGFin, hδBase] at he
    have hInfEq : z.2 = GInf x * Matrix.GeneralLinearGroup.map f (restrictMatrix b r) := by
      have he := congrArg Prod.snd hzEq
      change z.2 = (G x).2 * Matrix.GeneralLinearGroup.map f (restrictMatrix b r) at he
      rwa [hGInf] at he
    constructor
    · refine hFin z.1 (x.val * δ r).1 (Set.mem_image_of_mem _ hz) fun q => ?_
      rw [hFinEq]
      have hEq : (fun v => (x.val * δ r).1 v) = fun v =>
          x.val.1 v * Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) r := by
        funext v
        change x.val.1 v * δFin r v = _
        rw [hδFin]
      change FiniteMatrixAction b (fun v => (x.val * δ r).1 v) q _
      rw [hEq]
      exact finiteMatrixAction_mul_diagonal b x.val.1 q (G₀ x q) (hAct x q) r
    · refine Set.mem_pi.mpr fun w _ => hDist z.2 (x.val * δ r).2
        (Set.mem_image_of_mem _ hz) (fun v j => ?_) w
      change E (z.2.val.mulVec v) j =
        (x.val.2 j * Matrix.GeneralLinearGroup.map (e j) r).val.mulVec (E v j)
      rw [hInfEq, mulVec_action, hInf x, mulVec_action]
      exact congrArg (x.val.2 j).val.mulVec
        (rationalMatrixComparison f e b E.toLinearEquiv hE r v j)
  choose D' hD' hTranslate' using hTranslate
  let Labels := Set.range label
  let : Finite Labels := hLabel.to_subtype
  let rep (a : Labels) : U := a.property.choose
  let C' := (⋃ a : Labels, D' (rep a)) ∩ SAd
  refine ⟨δ, hδFin, fun _ _ => rfl, C',
    (isCompact_iUnion fun a => hD' (rep a)).inter_right hClosed,
    fun g hg => (hSAd g).mp hg.2, ?_⟩
  intro g hdet hdetInf hp hpInf hT
  let x : U := ⟨g, hdet, hdetInf, hp, hpInf, hT⟩
  let a : Labels := ⟨label x, x, rfl⟩
  have ha : label x = label (rep a) := a.property.choose_spec.symm
  obtain ⟨r, hr, hrT⟩ := rationalTensorLabelComparison b c T (M x) (M (rep a)) ha
  refine ⟨r, hrT, mem_iUnion.mpr ⟨a, hTranslate' (rep a) x r hr⟩, ?_⟩
  have hrPres (j : TensorLabelIndex J H O D) : PreservesTensor (S j) r r := by
    have h := (tensorLabelSystem_preserves T c (RingHom.id K) r).mp hrT j
    exact h
  constructor
  · intro v j
    change PreservesTensor _ (g.1 v * δFin r v) (g.1 v * δFin r v)
    rw [hδFin]
    exact preservesTensor_mul _ _ _ ((tensorLabelSystem_preserves T c _ _).mp (hT.1 v) j)
      (preservesTensor_map _ _ _ _ (hrPres j))
  · intro w j
    exact preservesTensor_mul _ _ _ ((tensorLabelSystem_preserves T c _ _).mp (hT.2 w) j)
      (preservesTensor_map _ _ _ _ (hrPres j))

theorem numberTensorAdelicReduction : Specs.TensorAdelicReduction.numberTensorAdelicReduction := by
  classical
  intro K I P J H _ _ _ _ _ _ _ X Y O _ _ _ p d T hd hAnis e
  obtain ⟨b, a, E, hb, hE, C, hC, hBound⟩ := numberBoundedTensorBases p d hd hAnis
  let := a
  let (w : NumberField.InfinitePlace K) : Field w.Completion := inferInstance
  let (w : NumberField.InfinitePlace K) : T2Space w.Completion := inferInstance
  let (w : NumberField.InfinitePlace K) : IsTopologicalRing w.Completion := inferInstance
  obtain ⟨hc, hdisc⟩ := arithmeticBaseDiagonals.{0}.1
  refine splitTensorAdelicReduction (R := ℤ) (A := 𝓞 K) (algebraMap ℚ ℝ) e
    b E hb hE hc hdisc p T C hC ?_
  intro g gInf hg hgInf hp hpInf
  obtain ⟨G, GInf, M, hI, hAct, _, hInf, _, _, hMem⟩ := hBound g gInf hg hgInf hp hpInf
  exact ⟨G, GInf, M, hI, fun q => (hAct q).2, hInf, hMem⟩

private theorem tensorSystem_preserves_map {K A B I J H : Type*} [Field K] [Field A] [Field B]
    {O : H → Type*} {X : J → Type u} {Y : H → Type u} [Fintype I] [DecidableEq I]
    [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)] (T : TensorSystem K I X Y O)
    (e : K →+* A) (f : A →+* B) (m : Matrix.GeneralLinearGroup I A)
    (h : T.Preserves e m) :
    T.Preserves (f.comp e) (Matrix.GeneralLinearGroup.map f m) := by
  let c : Empty → K := Empty.elim
  apply (tensorLabelSystem_preserves T c _ _).mpr
  intro a
  exact preservesTensor_map f _ _ _ ((tensorLabelSystem_preserves T c _ _).mp h a)

private theorem preservesPolynomial_map {K A B I : Type*} [Field K] [Field A] [Field B]
    [Fintype I] [DecidableEq I] (p : MvPolynomial I K) (e : K →+* A) (f : A ≃+* B)
    (g : Matrix.GeneralLinearGroup I A)
    (h : ∀ x, p.eval₂ e (g.val.mulVec x) = p.eval₂ e x) :
    ∀ y, p.eval₂ (f.toRingHom.comp e)
      ((Matrix.GeneralLinearGroup.map f.toRingHom g).val.mulVec y) =
      p.eval₂ (f.toRingHom.comp e) y := by
  intro y
  let x : I → A := fun i => f.symm (y i)
  have hy : embedCoordinates f.toRingHom x = y := funext fun i => f.apply_symm_apply (y i)
  rw [← hy, mapMatrix_mulVec]
  exact (MvPolynomial.eval₂_comp_left f.toRingHom e (g.val.mulVec x) p).symm.trans
    ((congrArg f (h x)).trans (MvPolynomial.eval₂_comp_left f.toRingHom e x p))

open LatticeCompletionDecompositionSpec in
set_option maxHeartbeats 900000 in
private theorem functionSplitTensorAdelicReduction {F K I P J H : Type*}
    [Field F] [Finite F] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I] [Fintype P] [Finite J] [Finite H]
    {X : J → Type u} {Y : H → Type u} {O : H → Type*}
    [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)] [∀ h, Finite (O h)]
    (t : SeparatingParameter F K) (p : P → MvPolynomial I K) (d : P → ℕ)
    (T : TensorSystem K I X Y O)
    (hd : ∀ j, 0 < d j ∧ (p j).IsHomogeneous (d j))
    (hAnis : ∀ x, x ≠ 0 → ∃ j, (p j).eval x ≠ 0) :
    let W := {w : FunctionPlace K // t.element ∉ w.val}
    let L := fun w : W => w.val.Completion
    letI (w : W) : Field (L w) := inferInstance
    let e := fun w : W => w.val.embedding
    ∃ δ : Matrix.GeneralLinearGroup I K →* SplitMatrixAdeles t.integerRing K I L,
      (∀ r v, (δ r).1 v = Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) r) ∧
      (∀ r w, (δ r).2 w = Matrix.GeneralLinearGroup.map (e w) r) ∧
      ∃ C : Set (SplitMatrixAdeles t.integerRing K I L), IsCompact C ∧
        (∀ h ∈ C, T.PreservesSplit e h) ∧
        ∀ g : SplitMatrixAdeles t.integerRing K I L,
          (∀ v, (g.1 v).det = 1) → (∀ w, (g.2 w).det = 1) →
          PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g.1 →
          PreservesPolynomials e p g.2 → T.PreservesSplit e g →
          ∃ r : Matrix.GeneralLinearGroup I K, T.Preserves (RingHom.id K) r ∧ g * δ r ∈ C := by
  classical
  intro W L e
  let (w : W) : Field (L w) := inferInstance
  let := t.rationalAlgebra
  let := t.polynomialAlgebra
  let := parameterIntegerRing_torsionFree t
  let : Algebra.IsIntegral F[X] t.integerRing :=
    inferInstanceAs (Algebra.IsIntegral F[X] (integralClosure F[X] K))
  let : Module.Finite F[X] t.integerRing :=
    IsIntegralClosure.finite F[X] F⟮X⟯ K (↥(integralClosure F[X] K))
  let B := infinityField F
  let f := infinityEmbedding F
  let N := Fin (Module.finrank F⟮X⟯ (I → K))
  let (w : W) : T2Space (L w) := inferInstance
  let (w : W) : IsTopologicalRing (L w) := inferInstance
  obtain ⟨b, a, E, φ, homeo, hb, hE, hφ, hf, C, hC, hBound⟩ :=
    functionBoundedTensorBases t p d hd hAnis
  let := a
  let f' := φ.toRingHom.comp f
  obtain ⟨hc', hdisc'⟩ := arithmeticBaseDiagonals.2 F f' hf
  let ψ : BaseScalarAdeles F[X] F⟮X⟯ B ≃ₜ BaseScalarAdeles F[X] F⟮X⟯ F⸨X⸩ :=
    (Homeomorph.refl _).prodCongr homeo
  have hRange : ψ '' Set.range (baseScalarDiagonal (R := F[X]) f) =
      Set.range (baseScalarDiagonal (R := F[X]) f') := by
    rw [← Set.range_comp]
    congr 1
    funext x
    apply Prod.ext
    · rfl
    · change homeo (f x) = φ (f x)
      exact congrFun hφ.symm (f x)
  have hClosed : IsClosed (Set.range (baseScalarDiagonal (R := F[X]) f)) :=
    ψ.isClosed_image.mp (hRange ▸ hc')
  have hDiscrete : IsDiscrete (Set.range (baseScalarDiagonal (R := F[X]) f)) := by
    rw [← hRange] at hdisc'
    have hPre : ψ.symm '' (ψ '' Set.range (baseScalarDiagonal (R := F[X]) f)) =
        Set.range (baseScalarDiagonal (R := F[X]) f) := by
      rw [Set.image_image]
      simp
    rw [← hPre]
    exact hdisc'.image ψ.symm.isInducing
  have hCont : Continuous φ := hφ.symm ▸ homeo.continuous
  have hInv (x : F⸨X⸩) : φ.symm x = homeo.symm x :=
    homeo.injective ((congrFun hφ (φ.symm x)).symm.trans
      ((φ.apply_symm_apply x).trans (homeo.apply_symm_apply x).symm))
  have hContInv : Continuous φ.symm := (funext hInv).symm ▸ homeo.symm.continuous
  let Φ : BasisAdeles F[X] F⟮X⟯ B N ≃ₜ BasisAdeles F[X] F⟮X⟯ F⸨X⸩ N :=
    (Homeomorph.refl _).prodCongr (generalLinearHomeomorph φ hCont hContInv)
  refine splitTensorAdelicReduction (A := t.integerRing) f e b E hb hE hClosed hDiscrete
    p T (Φ ⁻¹' C) (Φ.isCompact_preimage.mpr hC) ?_
  intro g gInf hg hgInf hp hpInf
  obtain ⟨G, GInf, M, hI, hAct, _, hInf, _, _, hMem⟩ := hBound g gInf hg hgInf hp hpInf
  refine ⟨G, GInf, M, hI, fun q => (hAct q).2, hInf, ?_⟩
  change (finiteBasisRepresentative G M hI,
    Matrix.GeneralLinearGroup.map φ.toRingHom (GInf * Matrix.GeneralLinearGroup.map f M)) ∈ C
  rw [map_mul]
  exact hMem

open GlobalPlacesSpec in
set_option maxHeartbeats 1100000 in
theorem functionTensorAdelicReduction :
    Specs.TensorAdelicReduction.functionTensorAdelicReduction := by
  classical
  intro F K I P J H _ _ _ _ _ _ _ _ _ X Y O _ _ _ t p d T hd hAnis
  let W := {w : FunctionPlace K // t.element ∉ w.val}
  let L (w : W) := w.val.Completion
  let (w : W) : Field (L w) := inferInstance
  let e (w : W) := w.val.embedding
  let vOf := placeOfPrimeValue t
  obtain ⟨chart, hChartInf, hChartFin⟩ := functionMatrixAdeleComparison (I := I) t
  choose c hc hChart using hChartFin
  let E : FunctionMatrixAdeles K I ≃* SplitMatrixAdeles t.integerRing K I L :=
    { __ := chart.toEquiv
      map_mul' g g' := by
        apply Prod.ext
        · apply RestrictedProduct.ext
          intro v
          change (chart (g * g')).1 v = (chart g).1 v * (chart g').1 v
          rw [hChart, hChart, hChart, ← map_mul]
          rfl
        · funext w
          change (chart (g * g')).2 w = (chart g).2 w * (chart g').2 w
          rw [hChartInf, hChartInf, hChartInf]
          rfl }
  obtain ⟨δ, hδFin, hδInf, C, hC, hCpres, hReduce⟩ :=
    functionSplitTensorAdelicReduction t p d T hd hAnis
  let δ' := E.symm.toMonoidHom.comp δ
  have hCases (v : FunctionPlace K) :
      (∃ q, vOf q = v) ∨ ∃ w : W, w.val = v := by
    by_cases h : t.element ∈ v.val
    · left
      change v ∈ Set.range vOf
      exact t.range_placeOfPrime.symm ▸ h
    · exact Or.inr ⟨⟨v, h⟩, rfl⟩
  have hEmb (v : HeightOneSpectrum t.integerRing) :
      (c v).toRingHom.comp (vOf v).embedding = algebraMap K (v.adicCompletion K) :=
    RingHom.ext (hc v)
  have hEmbInv (v : HeightOneSpectrum t.integerRing) :
      (c v).symm.toRingHom.comp (algebraMap K (v.adicCompletion K)) = (vOf v).embedding := by
    ext x
    change (c v).symm (algebraMap K (v.adicCompletion K) x) = (vOf v).embedding x
    rw [← hc, RingEquiv.symm_apply_apply]
  have hMatInv (g : FunctionMatrixAdeles K I) (v : HeightOneSpectrum t.integerRing) :
      Matrix.GeneralLinearGroup.map (c v).symm.toRingHom ((E g).1 v) = g (vOf v) := by
    change Matrix.GeneralLinearGroup.map (c v).symm.toRingHom ((chart g).1 v) = _
    rw [hChart]
    exact Units.ext (Matrix.ext fun i j => (c v).symm_apply_apply _)
  have hδ' (r : Matrix.GeneralLinearGroup I K) (v : FunctionPlace K) :
      δ' r v = Matrix.GeneralLinearGroup.map v.embedding r := by
    rcases hCases v with ⟨q, rfl⟩ | ⟨w, rfl⟩
    · rw [← hMatInv (δ' r) q]
      change Matrix.GeneralLinearGroup.map (c q).symm.toRingHom ((E (E.symm (δ r))).1 q) = _
      rw [MulEquiv.apply_symm_apply, hδFin, ← hEmbInv]
      rfl
    · have he := hChartInf (δ' r) w
      change (E (E.symm (δ r))).2 w = δ' r w.val at he
      rw [MulEquiv.apply_symm_apply, hδInf] at he
      exact he.symm
  have hTensor (g : FunctionMatrixAdeles K I) :
      T.PreservesSplit e (E g) ↔ ∀ v, T.Preserves v.embedding (g v) := by
    constructor
    · intro hg v
      rcases hCases v with ⟨q, rfl⟩ | ⟨w, rfl⟩
      · have ht := tensorSystem_preserves_map T (algebraMap K (q.adicCompletion K))
          (c q).symm.toRingHom ((E g).1 q) (hg.1 q)
        rwa [hMatInv, hEmbInv] at ht
      · have ht := hg.2 w
        change T.Preserves (w.val.embedding) ((chart g).2 w) at ht
        rwa [hChartInf] at ht
    · intro hg
      constructor
      · intro q
        have ht := tensorSystem_preserves_map T (vOf q).embedding
          (c q).toRingHom (g (vOf q)) (hg (vOf q))
        change T.Preserves (algebraMap K (q.adicCompletion K)) ((chart g).1 q)
        rwa [hChart, ← hEmb]
      · intro w
        change T.Preserves w.val.embedding ((chart g).2 w)
        simpa only [hChartInf] using hg w.val
  refine ⟨δ', hδ', chart ⁻¹' C, chart.isCompact_preimage.mpr hC,
    fun g hg => (hTensor g).mp (hCpres _ hg), ?_⟩
  intro g hDet hPoly hT
  have hDetFin (v : HeightOneSpectrum t.integerRing) : ((E g).1 v).det = 1 := by
    change ((chart g).1 v).det = 1
    rw [hChart, Matrix.GeneralLinearGroup.map_det, hDet, map_one]
  have hDetInf (w : W) : ((E g).2 w).det = 1 := by
    change ((chart g).2 w).det = 1
    rw [hChartInf, hDet]
  have hPolyFin : PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p (E g).1 := by
    intro j v x
    change (p j).eval₂ (algebraMap K (v.adicCompletion K)) (((chart g).1 v).val.mulVec x) =
      (p j).eval₂ (algebraMap K (v.adicCompletion K)) x
    rw [hChart, ← hEmb]
    exact preservesPolynomial_map (p j) (vOf v).embedding (c v) (g (vOf v)) (hPoly j (vOf v)) x
  have hPolyInf : PreservesPolynomials e p (E g).2 := by
    intro j w x
    change (p j).eval₂ (w.val.embedding) (((chart g).2 w).val.mulVec x) = _
    rw [hChartInf]
    exact hPoly j w.val x
  obtain ⟨r, hr, hMem⟩ := hReduce (E g) hDetFin hDetInf hPolyFin hPolyInf ((hTensor g).mpr hT)
  refine ⟨r, hr, ?_⟩
  change E (g * E.symm (δ r)) ∈ C
  simpa only [map_mul, MulEquiv.apply_symm_apply] using hMem

end

end LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction
