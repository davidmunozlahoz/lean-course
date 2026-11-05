import Mathlib

/- 2.1.1 Structures -/

/-
In mathematics, many objects are, formally, tuples (even if we don't
think of them as such): a point of ℝ³ is a triple of real numbers, a
group is a set together with an operation, a unit and an inverse map
satisfying some axioms, a ring is a... In Lean, tuples with named
components are called structures. Here is a point of ℝ³ (this example
is from [MIL, 7.1]):
-/

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point     -- Type
#check Point.mk  -- Point.mk (x y z : ℝ) : Point
#check Point.x   -- Point.x (self : Point) : ℝ

/-
A few remarks:
    - structure Point creates a new type, Point. Its terms are built
      with the constructor Point.mk, which takes the three fields x,
      y and z. And we get the three projections Point.x, Point.y and
      Point.z back.
    - @[ext] is an attribute: it tells Lean to generate the theorem
      Point.ext, which says that two points are equal if their three
      fields are equal. Then the tactic ext works with points, as it
      did with sets in 1.2.4.

There are several ways of building a point:
-/

def p₁ : Point := Point.mk 2 (-1) 4

def p₂ : Point := ⟨2, -1, 4⟩

def p₃ : Point where
  x := 2
  y := -1
  z := 4

def p₄ : Point := { x := 2, y := -1, z := 4 }

example : p₁ = p₂ := rfl

example : p₁.x = 2 := rfl

/-
The second one is the anonymous constructor of 1.1, and this is no
coincidence: ⟨_, _⟩ works for any structure, and p ∧ q is precisely
a structure, with two fields, left : p and right : q. This is why we
could build proofs of p ∧ q with ⟨hp, hq⟩, and use h.1 and h.2 (we can
also refer to the fields by number).

Note the dot notation: p₁.x is short for Point.x p₁. In general, if p
: Point, then p.foo means Point.foo p, so we can define a function Foo in
the namespace Point, which in principle would require it to be
called by its full name Point.Foo, and use it with the dot.
Let us define the sum of two points, and prove it is commutative:
-/

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def zero : Point := ⟨0, 0, 0⟩

#check add p₁ p₂  -- inside the namespace, add is Point.add
#check p₁.add p₂  -- and this is also Point.add p₁ p₂

theorem add_comm (a b : Point) : a.add b = b.add a := by
  ext
  · simp only [add]
    ring
  · simp only [add]
    ring
  · simp only [add]
    ring

/-
Look at the infoview after ext: we get three goals, one for each
field. Then simp only [add] unfolds the definition of add, and the
goal becomes, e.g., a.x + b.x = b.x + a.x. When all goals can be
closed in the same way, we can write ext <;> simp only [add] <;> ring:
the combinator t₁ <;> t₂ applies t₂ to every goal produced by t₁.
-/

theorem add_zero (a : Point) : a.add zero = a := by
  ext <;> simp only [add, zero] <;> ring

theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  ext <;> simp only [add] <;> ring

theorem zero_add (a : Point) : zero.add a = a := by
  ext <;> simp only [add, zero] <;> ring

/-
Now define the multiplication of a point by a scalar, and prove the
following properties (replace the sorrys in the definition too!):
-/

def smul (r : ℝ) (a : Point) : Point where
  x := r * a.x
  y := r * a.y
  z := r * a.z

theorem smul_add (r : ℝ) (a b : Point) :
    smul r (a.add b) = (smul r a).add (smul r b) := by
  ext <;> simp only [add, smul] <;> rw [mul_add]

theorem one_smul (a : Point) : smul 1 a = a := by
  ext <;> simp only [smul] <;> rw [one_mul]

end Point

/-
The fields of a structure can also be proofs. This allows us to
bundle data together with its properties. For instance, a closed
interval [lo, hi] of ℝ is given by two real numbers, together with
the fact that lo ≤ hi (we use the subscript ₁ since mathlib already
has its own Interval, and we do not want to clash with it):
-/

structure Interval₁ where
  lo : ℝ
  hi : ℝ
  lo_le_hi : lo ≤ hi -- remember: we interpret lo_le_hi as a proof of lo ≤ hi

namespace Interval₁

def unit : Interval₁ := ⟨0, 1, by norm_num⟩

def length (I : Interval₁) : ℝ := I.hi - I.lo

theorem length_nonneg (I : Interval₁) : 0 ≤ I.length := by
  unfold length
  linarith [I.lo_le_hi]

/-
To build an interval, we have to provide a proof that lo ≤ hi: there
is no way of building a "wrong" interval. Conversely, for every
I : Interval₁ we can use I.lo_le_hi : I.lo ≤ I.hi. Let us define the
sum of intervals, [a, b] + [c, d] = [a + c, b + d]:
-/

def add (I J : Interval₁) : Interval₁ where
  lo := I.lo + J.lo
  hi := I.hi + J.hi
  -- we provide the term directly, without entering tactic mode
  lo_le_hi := add_le_add I.lo_le_hi J.lo_le_hi

theorem length_add (I J : Interval₁) :
    (I.add J).length = I.length + J.length := by
  unfold length add
  dsimp
  ring

/-
Now define the opposite of an interval, -[a, b] = [-b, -a], and the
interval [a, a] for every a : ℝ. Then prove the theorems below.
-/

def neg (I : Interval₁) : Interval₁ where
  lo := - I.hi
  hi := - I.lo
  lo_le_hi := by
    rw [neg_le, neg_neg]
    exact I.lo_le_hi

def point (a : ℝ) : Interval₁ where
  lo := a
  hi := a
  lo_le_hi := le_refl a

theorem length_neg (I : Interval₁) : I.neg.length = I.length := by
  unfold length neg
  dsimp
  ring

theorem length_point (a : ℝ) : (point a).length = 0 := by
  unfold length point
  dsimp
  rw [sub_eq_zero]

end Interval₁

/-
    (*) Structures are a particular case of inductive types (remember
    the (**) about Eq in 1.1.4): they are inductive types with a
    single constructor. For instance, Point could have been defined
    as

        inductive Point' where
          | mk (x y z : ℝ) : Point'

    and Lean would have given us the same type, but not the
    projections Point'.x, ..., nor the notation { x := ... }. Try
    #print And and #print Exists: the first one is a structure, the
    second one is an inductive type with a single constructor, and
    this is why the anonymous constructor works for both.
-/

/-
Let us now bundle more interesting structures. A monoid is a type M,
with an associative operation and a unit. Since structures can take
parameters, just like functions, we can define the structure of a
monoid on a given type α:
-/

structure Monoid₁ (α : Type) where
  mul : α → α → α
  one : α
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x

/-
Let me be clear about what is going on here: Monoid₁ α encodes a
monoid structure on α by keeping track, explicitly, of all the
operations and axioms. In math, we identify the structure of a monoid
with the underlying set, by just saying "Let M be a monoid.". In Lean,
to say that α has a monoid structure, we need to explicitly provide
h : Monoid₁ α. In other words, a monoid structure on α is a term of
type Monoid₁ α. Being so explicit about structures quickly becomes
cumbersome. In 2.1.2 we will see how Lean solves this.
-/

/-
Now, for instance, (ℕ, +, 0) is a monoid:
-/

def natAdd : Monoid₁ ℕ where
  mul := fun m n => m + n
  one := 0
  mul_assoc := Nat.add_assoc
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero

/-
And we can prove theorems about all monoids. For instance, the unit
is unique (the dot in the name acts as if we defined the theorem
one_unique inside the namespace Monoid₁):
-/

theorem Monoid₁.one_unique {α : Type} (M : Monoid₁ α) (e : α)
    (h : ∀ x, M.mul e x = x) : e = M.one := by
  rw [← M.mul_one e]
  exact h M.one

/-
In particular, we can specialize the result to ℕ, which is a monoid.
-/
#check natAdd.one_unique  -- here natAdd.one_unique = Monoid₁.one_unique natAdd

/-
Now it is your turn. Define the monoid (ℕ, *, 1), and the monoid of
functions α → α with the composition (as usual, replace the sorries).
-/

def natMul : Monoid₁ ℕ where
  mul := fun n m => n * m
  one := 1
  mul_assoc := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

def endo (α : Type) : Monoid₁ (α → α) where
  mul := fun f g => f ∘ g
  one := fun a => a
  mul_assoc := by
    intro f g h
    ext a
    simp
  one_mul := by
    intro f
    ext a
    simp
  mul_one := by
    intro f
    ext a
    simp

/-
Now prove that, in any monoid, if an element y is a right inverse of
x and z is a left inverse of x, then y = z (look at the infoview to
see how M.mul works):
-/

theorem Monoid₁.inv_unique {α : Type} (M : Monoid₁ α) (x y z : α)
    (hy : M.mul x y = M.one) (hz : M.mul z x = M.one) : y = z := by
  calc
    y = M.mul M.one y := (M.one_mul y).symm
    _ = M.mul (M.mul z x) y := by rw [hz]
    _ = M.mul z (M.mul x y) := M.mul_assoc z x y
    _ = M.mul z M.one := by rw [hy]
    _ = z := M.mul_one z

/-
This works, but it is far from the way we write mathematics:
    - we have to write M.mul x y instead of x * y,
    - we have to carry the structure M around explicitly, and
      to tell Lean which monoid structure we mean every single
      time, even if there is only one reasonable choice, as for
      the functions α → α. On paper, we just say "the monoid α → α".
    - Worse: ℝ is a monoid, a group, a ring, a field, a topological
      space, a metric space, ... If we had to give all these
      structures explicitly to each theorem about real numbers,
      formalization would be impossible.
We would like Lean to find the structure by itself, whenever it is
clear from the context. This is what classes and type class
inference do, as we shall see in the next section.
-/
