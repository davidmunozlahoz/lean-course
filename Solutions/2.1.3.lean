import Mathlib

/- 2.1.3 Extension of classes-/

/-
In mathematics, structures are built on top of each other: a group
is a monoid with inverses, a monoid is a semigroup with a unit, a
ring is an abelian group with a multiplication, and so on. In Lean,
we express this with the keyword extends. Let us build our own
(small) algebraic hierarchy, as in [MIL, 8.1]:
-/

class Semigroup₃ (α : Type*) extends Mul α where
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class Monoid₃ (α : Type*) extends Semigroup₃ α, One α where
  one_mul₃ : ∀ a : α, 1 * a = a
  mul_one₃ : ∀ a : α, a * 1 = a

class Group₃ (α : Type*) extends Monoid₃ α, Inv α where
  inv_mul₃ : ∀ a : α, a⁻¹ * a = 1

/-
A few remarks:
    - Mul α, One α and Inv α are small clases only with the
      information that α has a map α → α → α (a multiplication), a
      distinguished element (a one), and a map α → α (an inversion).
      They are convenient because they immediately give us the notation
      *, 1 and ⁻¹. So, by extending them, we can use the usual notation
      from now on.
    - A class extending Semigroup₃ α contains all the fields of
      Semigroup₃ α, plus the new ones. Try #print Group₃ to see all
      the fields of Group₃.
    - Moreover, Lean automatically defines the projection
      Monoid₃.toSemigroup₃ : Monoid₃ α → Semigroup₃ α, and makes it an
      instance. So every time Lean looks for a Semigroup₃ α, it can
      also look for a Monoid₃ α, or a Group₃ α. In other words, every
      group is automatically a monoid and a semigroup.
-/

#print Group₃
#check @Monoid₃.toSemigroup₃
#check @Group₃.toMonoid₃

/-
Thus, the theorems that we prove for monoids work for groups, with no
extra effort:
-/

theorem Monoid₃.one_unique {α : Type*} [Monoid₃ α] (e : α)
    (h : ∀ x : α, e * x = x) : e = 1 := by
  rw [← Monoid₃.mul_one₃ e]
  exact h 1

example {α : Type*} [Group₃ α] (e : α) (h : ∀ x : α, e * x = x) : e = 1 :=
  Monoid₃.one_unique e h

/-
Here, Lean needed an instance of Monoid₃ α, and it found it from the
instance of Group₃ α, through Group₃.toMonoid₃.

As in 2.1.2, we can declare instances. When the fields of a parent
class (here, the multiplication, unit and inverse) already have
instances, Lean finds them by itself, so we only have to give the
axioms. For instance, the permutations of α form a group, and
mathlib already gives us the multiplication (composition), the unit
and the inverse, and the proofs of the axioms:
-/

instance {α : Type*} : Group₃ (Equiv.Perm α) where
  mul_assoc₃ := mul_assoc
  one_mul₃ := one_mul
  mul_one₃ := mul_one
  inv_mul₃ := inv_mul_cancel
