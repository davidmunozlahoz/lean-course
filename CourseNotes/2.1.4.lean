import Mathlib

/- 2.1.4 Subobjects and coercions -/

/-
A submonoid of a monoid M is a subset of M which contains 1 and is
closed under multiplication. As usual, this is a structure: a set,
together with two properties. From now on we use the monoids of
mathlib, [Monoid M], since we already know how they work:
-/

structure Submonoid₁ (M : Type*) [Monoid M] where
  carrier : Set M
  mul_mem {a b : M} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier

/-
Note that we put the arguments {a b : M} before the colon in the
field mul_mem: this is the same as writing
mul_mem : ∀ {a b : M}, a ∈ carrier → ... For instance, the even
natural numbers form a submonoid of (ℕ, +, 0)... but this is an
additive monoid, so let us take instead the powers of 2 in (ℕ, *, 1):
-/

def powersOfTwo : Submonoid₁ ℕ where
  carrier := {n | ∃ k, n = 2 ^ k}
  mul_mem := by
    rintro a b ⟨k, rfl⟩ ⟨l, rfl⟩
    use k + l
    rw [pow_add]
  one_mem := ⟨0, rfl⟩

/-
Here rfl in a pattern means: replace a by 2 ^ k everywhere (we can do
this when we have a hypothesis a = 2 ^ k).

Now, we would like to say x ∈ powersOfTwo, instead of
x ∈ powersOfTwo.carrier. That is, we would like to treat a submonoid
as if it were a set. We would also like to treat a morphism f as a
function, writing f x instead of f.toFun x. In mathematics, we do this
all the time without even noticing. In Lean, this is done with
coercions.

A coercion is a way of converting a term of a type into a term of
another type, which Lean inserts automatically when the types do not
match. The most familiar example is that of numbers: a natural number
is not an integer (they are different terms, of different types, see
1.1.2), but Lean converts it when needed:
-/

section

variable (n : ℕ) (z : ℤ)

#check n + z  -- ↑n + z : ℤ
#check (n : ℝ)  -- ↑n : ℝ

/-
The arrow ↑ (typed \u) indicates that Lean has inserted a coercion:
↑n is the integer corresponding to n. We can also ask for a coercion
explicitly, with a type ascription such as (n : ℝ).

Coercions are tricky: ↑(m + n) and ↑m + ↑n are different terms, even
if they are equal. To deal with them, mathlib has the tactics
push_cast, which pushes the arrows towards the leaves of the
expression, and norm_cast, which moves them up and tries to get rid
of them.
-/

example (m n : ℕ) : ((m + n : ℕ) : ℝ) = (m : ℝ) + (n : ℝ) := by
  push_cast
  rfl

example (m n : ℕ) (h : (m : ℝ) < (n : ℝ)) : m < n := by
  norm_cast at h

example (m n : ℕ) : ((m * n + 1 : ℕ) : ℝ) = m * n + 1 := by
  sorry

example (m n : ℕ) (h : m ≤ n) : (m : ℝ) ≤ n := by
  sorry

example (a : ℕ) (h : (a : ℤ) = 3) : a = 3 := by
  sorry

end

/-
How does Lean know how to coerce? With type classes, of course. If
there is an instance of Coe α β, then Lean can convert terms of type
α into terms of type β. There are a few variants:
    - Coe α β: from terms of α to terms of β, as for ℕ and ℤ.
    - CoeFun α: from terms of α to functions, so we can write f x.

For submonoids, and for subobjects in general, we use instead the
class SetLike S M. It says that each term of S has an underlying set
of elements of M, and that two terms of S with the same underlying
set are equal (i.e., the map S → Set M is injective). To give an
instance, we have to provide these two things:
-/

namespace Submonoid₁

variable {M : Type*} [Monoid M]

instance : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective := by
    intro N P h
    cases N
    cases P
    congr

instance : PartialOrder (Submonoid₁ M) := .ofSetLike (Submonoid₁ M)

/-
In the proof of injectivity, cases N takes N apart into its fields,
so that h becomes an equality between the two carriers, and congr
reduces the goal to it (the other fields are proofs, and any two
proofs of the same proposition are equal).

The second instance orders submonoids by inclusion, using the
SetLike instance (this is exactly what mathlib does for its
subobjects). In return, SetLike gives us, all at once:
    - a coercion to sets: if N : Submonoid₁ M, then (N : Set M), or
      ↑N, is N.carrier,
    - membership: x ∈ N means x ∈ (N : Set M),
    - with the second instance, an order: N ≤ P means that N is
      contained in P, i.e., ∀ x ∈ N, x ∈ P,
    - extensionality: SetLike.ext says that two submonoids with the
      same elements are equal,
    - a coercion to types: N can be used as the type of its elements.
-/

example (N : Submonoid₁ M) {a b : M} (ha : a ∈ N) (hb : b ∈ N) :
    a * b ∈ N :=
  N.mul_mem ha hb

example (N P : Submonoid₁ M) (h : ∀ x, x ∈ N ↔ x ∈ P) : N = P :=
  SetLike.ext h

example (N P : Submonoid₁ M) (h : ∀ x ∈ N, x ∈ P) : N ≤ P :=
  h

/-
Now it is your turn. Define the intersection of two submonoids, and
the submonoid containing only 1 (replace all sorries).
-/

def inter (N P : Submonoid₁ M) : Submonoid₁ M where
  carrier := sorry
  mul_mem := sorry
  one_mem := sorry

def bot : Submonoid₁ M where
  carrier := sorry
  mul_mem := sorry
  one_mem := sorry

example (N P : Submonoid₁ M) (x : M) : x ∈ inter N P ↔ x ∈ N ∧ x ∈ P := by
  sorry

/-
You may find it useful below to use the change tactic, which can be
used to change the goal (or a hypothesis, using the at) by a term that
is definitionally equal. For instance, x ∈ {1} is definitionally equal
to x=1.
-/

example (N : Submonoid₁ M) : bot ≤ N := by
  sorry

example (N P : Submonoid₁ M) : inter N P ≤ N := by
  sorry

end Submonoid₁

/-
Now let us go back to morphisms. As in 2.1.2, a morphism of monoids
is a structure, and we give it a CoeFun instance, so that we can
write f x:
-/

structure MonoidHom₁ (M N : Type*) [Monoid M] [Monoid N] where
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y

namespace MonoidHom₁

variable {M N : Type*} [Monoid M] [Monoid N]

instance : CoeFun (MonoidHom₁ M N) (fun _ => M → N) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun

/-
The second argument of CoeFun says what the type of the function
is (it could depend on f, but here it is always M → N). And the line
attribute [coe] tells Lean to display f.toFun x as ⇑f x, or simply f x,
in the infoview.
-/

example (f : MonoidHom₁ M N) (x y : M) : f (x * y) = f x * f y :=
  f.map_mul x y

/-
Now we can define the kernel of a morphism, as a submonoid. Prove that
the preimage of a submonoid by a morphism is a submonoid, and that the
image of a submonoid is a submonoid (replace all sorries):
-/

def ker (f : MonoidHom₁ M N) : Submonoid₁ M where
  carrier := {x | f x = 1}
  mul_mem := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [f.map_mul, ha, hb, one_mul]
  one_mem := f.map_one

def comap (f : MonoidHom₁ M N) (P : Submonoid₁ N) : Submonoid₁ M where
  carrier := sorry
  mul_mem := sorry
  one_mem := sorry

def map (f : MonoidHom₁ M N) (P : Submonoid₁ M) : Submonoid₁ N where
  carrier := sorry
  mul_mem := sorry
  one_mem := sorry

end MonoidHom₁

/-
Mathlib has submonoids, subgroups, subrings,
subspaces, ... for all its structures, and they work as ours: they
are structures with a carrier set, and they are instances of
SetLike, so we can use ∈, ≤, the coercions, SetLike.ext, and so on.
For instance, for subgroups:
-/

section

variable {G H : Type*} [Group G] [Group H]

example (K : Subgroup G) {x y : G} (hx : x ∈ K) (hy : y ∈ K) : x * y⁻¹ ∈ K :=
  K.mul_mem hx (K.inv_mem hy)

example (K L : Subgroup G) (x : G) : x ∈ K ⊓ L ↔ x ∈ K ∧ x ∈ L :=
  Subgroup.mem_inf

example (f : G →* H) (x : G) : x ∈ f.ker ↔ f x = 1 :=
  MonoidHom.mem_ker

/-
Note that the intersection of subgroups is written K ⊓ L (typed
\inf): subgroups form a lattice, and the infimum is the intersection.
Note also that f.ker is MonoidHom.ker f, by the dot notation of 2.1.1.
And K ≤ L means that K is contained in L, as for our submonoids.
-/

example (K : Subgroup G) {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    x⁻¹ * y * x ∈ K := by
  sorry

example (f : G →* H) {x y : G} (hx : x ∈ f.ker) (hy : y ∈ f.ker) :
    x * y ∈ f.ker := by
  sorry

example (K L : Subgroup G) (h : K ≤ L) {x : G} (hx : x ∈ K) : x ∈ K ⊓ L := by
  sorry

/-
For rings and vector spaces, we have Subring R and Submodule K V:
-/

variable {R : Type*} [Ring R] {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V]

example (S : Subring R) {a b : R} (ha : a ∈ S) (hb : b ∈ S) : a * b + 1 ∈ S :=
  S.add_mem (S.mul_mem ha hb) S.one_mem

example (W : Submodule K V) (a : K) {u v : V} (hu : u ∈ W) (hv : v ∈ W) :
    a • u + v ∈ W := by
  sorry

example (W : Submodule K V) {u v : V} (hu : u ∈ W) (hv : v ∈ W) :
    u - v ∈ W := by
  sorry

/-
And, as with our submonoids, a subgroup is also a group, a subring a
ring, and a subspace a vector space, through the coercion to types:
-/

example (W : Submodule K V) : Module K W := inferInstance

end
