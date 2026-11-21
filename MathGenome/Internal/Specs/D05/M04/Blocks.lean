import MathGenome.Internal.Specs.D05.M04.Composition
import MathGenome.Internal.Specs.D05.M06.DirectSum
import MathGenome.Internal.Specs.D05.M06.Invariant

/-! K05.04.blocks, paper.tex:670–671. Products represent finite external
sums. Their summands may have unequal dimensions, and may be zero. `sumEquiv`
uses the accepted unique-expression predicate for actual internal subspaces.
All coordinate matrices have codomain rows and domain columns. -/
namespace Specs.D05.M04.Blocks
universe a b c d e f g h i j

section Components
variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {I J : Type*} [DecidableEq J]
  {E : J → Type*} {F : I → Type*}
  [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
  [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]

/-- Inclusion of input component, followed by the map and output projection. -/
noncomputable def block (e : (∀ j, E j) ≃ₗ[R] V)
    (f : (∀ i, F i) ≃ₗ[R] W) (T : V →ₗ[R] W) (i : I) (j : J) :
    E j →ₗ[R] F i :=
  (LinearMap.proj i).comp (f.symm.toLinearMap.comp
    (T.comp (e.toLinearMap.comp (LinearMap.single R E j))))
end Components

/-- The canonical summation equivalence is constructed from unique expansion;
its forward map is the accepted summation map, not a chosen coordinate map. -/
noncomputable def sumEquiv {K V I : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (U : I → Submodule K V)
    (h : Specs.D05.M06.DirectSum.UniqueDecomposition U) :
    (∀ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (Specs.D05.M06.DirectSum.summationMap U)
    ((Function.bijective_iff_existsUnique _).mpr h)

/-- The explicit inclusion/map/projection formula. -/
def block_apply : Prop :=
  ∀ {R V W I J : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : J → Type*} {F : I → Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)],
  ∀ (e : (∀ j, E j) ≃ₗ[R] V) (f : (∀ i, F i) ≃ₗ[R] W)
    (T : V →ₗ[R] W) (i : I) (j : J) (x : E j),
    block e f T i j x = f.symm (T (e (Pi.single j x))) i

/-- Each output component is the sum of the block images of input components. -/
def apply_eq_sum : Prop :=
  ∀ {R V W I J : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : J → Type*} {F : I → Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)],
  ∀ (e : (∀ j, E j) ≃ₗ[R] V) (f : (∀ i, F i) ≃ₗ[R] W)
    (T : V →ₗ[R] W) (x : ∀ j, E j) (i : I),
    f.symm (T (e x)) i = ∑ j, block e f T i j (x j)

/-- The intermediate component sizes need not equal either endpoint size. -/
def block_comp : Prop :=
  ∀ {R : Type a} {V : Type b} {W : Type c} {X : Type d}
    {I : Type e} {J : Type f} {L : Type g} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Fintype I] [Fintype J] [Fintype L] [DecidableEq I] [DecidableEq J]
    [AddCommGroup X] [Module R X]
    {G : L → Type h} [∀ l, AddCommGroup (G l)] [∀ l, Module R (G l)]
    {E : J → Type i} {F : I → Type j}
    [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)],
  ∀ (e : (∀ j, E j) ≃ₗ[R] V) (f : (∀ i, F i) ≃ₗ[R] W)
    (g : (∀ l, G l) ≃ₗ[R] X) (S : W →ₗ[R] X) (T : V →ₗ[R] W)
    (l : L) (j : J),
    block e g (S.comp T) l j =
      ∑ i, (block f g S l i).comp (block e f T i j)

/-- The block law in independently sized finite ordered summand bases. -/
def block_matrix_comp : Prop :=
  ∀ {R : Type a} {V : Type b} {W : Type c} {X : Type d}
    {I : Type e} {J : Type f} {L : Type g} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Fintype I] [Fintype J] [Fintype L] [DecidableEq I] [DecidableEq J]
    [AddCommGroup X] [Module R X]
    {G : L → Type h} [∀ l, AddCommGroup (G l)] [∀ l, Module R (G l)]
    {E : J → Type i} {F : I → Type j}
    [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)],
  ∀ (e : (∀ j, E j) ≃ₗ[R] V) (f : (∀ i, F i) ≃ₗ[R] W)
    (g : (∀ l, G l) ≃ₗ[R] X) (S : W →ₗ[R] X) (T : V →ₗ[R] W)
    {n : J → ℕ} {m : I → ℕ} {p : L → ℕ}
    (b : ∀ j, Module.Basis (Fin (n j)) R (E j))
    (c : ∀ i, Module.Basis (Fin (m i)) R (F i))
    (d : ∀ l, Module.Basis (Fin (p l)) R (G l)) (l : L) (j : J),
    LinearMap.toMatrix (b j) (d l) (block e g (S.comp T) l j) =
      ∑ i, LinearMap.toMatrix (c i) (d l) (block f g S l i) *
        LinearMap.toMatrix (b j) (c i) (block e f T i j)

/-- With ordered bases in each summand, the entries are precisely coordinates
of the included input basis vector's image in the output component. -/
def block_matrix_entry : Prop :=
  ∀ {R V W I J : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : J → Type*} {F : I → Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)],
  ∀ (e : (∀ j, E j) ≃ₗ[R] V) (f : (∀ i, F i) ≃ₗ[R] W)
    (T : V →ₗ[R] W) (i : I) (j : J) {n m : ℕ}
    (b : Module.Basis (Fin n) R (E j)) (c : Module.Basis (Fin m) R (F i))
    (a : Fin m) (d : Fin n),
    LinearMap.toMatrix b c (block e f T i j) a d =
      c.repr (f.symm (T (e (Pi.single j (b d)))) i) a

/-- Slicing a rectangular matrix by finite component indices gives the same
block multiplication law, over any commutative ring, including empty shapes. -/
def matrix_mul_blocks : Prop :=
  ∀ {R I J L : Type*} [CommRing R] [Fintype I]
    {r : L → Type*} {s : I → Type*} {t : J → Type*} [∀ i, Fintype (s i)]
    (A : Matrix (Sigma r) (Sigma s) R) (B : Matrix (Sigma s) (Sigma t) R)
    (l : L) (j : J),
    (A * B).submatrix (Sigma.mk l) (Sigma.mk j) =
      ∑ i, A.submatrix (Sigma.mk l) (Sigma.mk i) *
        B.submatrix (Sigma.mk i) (Sigma.mk j)

/-- For internal decompositions, the input inclusion really is the subspace
inclusion, and the output is the unique component projection. -/
def internal_block_apply : Prop :=
  ∀ {K V W I J : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
  ∀ (U : J → Submodule K V) (Z : I → Submodule K W)
    (hU : Specs.D05.M06.DirectSum.UniqueDecomposition U)
    (hZ : Specs.D05.M06.DirectSum.UniqueDecomposition Z)
    (T : V →ₗ[K] W) (i : I) (j : J) (u : U j),
    block (sumEquiv U hU) (sumEquiv Z hZ) T i j u =
      (sumEquiv Z hZ).symm (T (u : V)) i

/-- Invariance of one summand is equivalent to vanishing of every block
leaving it for a different summand. -/
def invariant_iff_off_diagonal : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] [DecidableEq I],
  ∀ (U : I → Submodule K V) (h : Specs.D05.M06.DirectSum.UniqueDecomposition U)
    (T : V →ₗ[K] V) (j : I),
    Specs.D05.M06.Invariant.invariant_value K V (U j) T ↔
      ∀ i, i ≠ j → block (sumEquiv U h) (sumEquiv U h) T i j = 0

/-- In ordered summand bases, the same condition is vanishing of the
corresponding rectangular matrices. Sizes may be zero or unequal. -/
def invariant_iff_matrix_off_diagonal : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] [DecidableEq I]
    (U : I → Submodule K V) (h : Specs.D05.M06.DirectSum.UniqueDecomposition U)
    (T : V →ₗ[K] V) {n : I → ℕ}
    (b : ∀ i, Module.Basis (Fin (n i)) K (U i)) (j : I),
    Specs.D05.M06.Invariant.invariant_value K V (U j) T ↔
      ∀ i, i ≠ j → LinearMap.toMatrix (b j) (b i)
        (block (sumEquiv U h) (sumEquiv U h) T i j) = 0

/-- Simultaneous invariance is precisely block diagonality, for any finite
number of summands, including the empty direct sum. -/
def all_invariant_iff_block_diagonal : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] [DecidableEq I],
  ∀ (U : I → Submodule K V) (h : Specs.D05.M06.DirectSum.UniqueDecomposition U)
    (T : V →ₗ[K] V),
    (∀ j, Specs.D05.M06.Invariant.invariant_value K V (U j) T) ↔
      ∀ i j, i ≠ j → block (sumEquiv U h) (sumEquiv U h) T i j = 0

/-- In the binary ordering `false = U`, `true = W`, the lower-left block
vanishes exactly when U is invariant. -/
def invariant_iff_lower_left_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V)
    (h : Specs.D05.M06.DirectSum.UniqueDecomposition (fun b : Bool => if b then W else U))
    (T : V →ₗ[K] V),
    Specs.D05.M06.Invariant.invariant_value K V U T ↔
      block (sumEquiv _ h) (sumEquiv _ h) T true false = 0

/-- Both invariant summands force both off-diagonal blocks, with no condition
on either diagonal block. -/
def both_invariant_iff_off_diagonal_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V)
    (h : Specs.D05.M06.DirectSum.UniqueDecomposition (fun b : Bool => if b then W else U))
    (T : V →ₗ[K] V),
    (Specs.D05.M06.Invariant.invariant_value K V U T ∧
      Specs.D05.M06.Invariant.invariant_value K V W T) ↔
      (block (sumEquiv _ h) (sumEquiv _ h) T true false = 0 ∧
       block (sumEquiv _ h) (sumEquiv _ h) T false true = 0)

end Specs.D05.M04.Blocks
