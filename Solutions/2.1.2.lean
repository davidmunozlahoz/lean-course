import Mathlib

/- 2.1.2 Classes and type class inference -/

/-
At the end of 2.1.1 we wanted Lean to find the monoid structure of a
type by itself. To do so, we replace the keyword structure by class:
-/

class Monoid₂ (α : Type) where
  mul : α → α → α
  one : α
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x

/-
A class is just a structure, with one difference: Lean keeps a
database of terms of this structure, called instances, and it
searches this database whenever it needs one. We add a term to the
database with the keyword instance (instead of def):
-/

instance natAdd : Monoid₂ ℕ where
  mul := fun m n => m + n
  one := 0
  mul_assoc := Nat.add_assoc
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero

instance (α : Type) : Monoid₂ (α → α) where
  mul := fun f g => f ∘ g
  one := id
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl

/-
Note that instances do not even need a name (Lean invents one). Now
we can write Monoid₂.mul m n, and Lean finds the structure by itself:
-/

#eval Monoid₂.mul 2 3                     -- 5
#check Monoid₂.mul (id : ℕ → ℕ) Nat.succ  -- uses the second instance
#check (Monoid₂.one : ℕ → ℕ)              -- id

/-
This process of finding instances is called type class inference.
Let us see how we state theorems about all monoids:
-/

theorem Monoid₂.one_unique {α : Type} [Monoid₂ α] (e : α)
    (h : ∀ x, Monoid₂.mul e x = x) : e = Monoid₂.one := by
  rw [← Monoid₂.mul_one e]
  exact h Monoid₂.one

/-
The square brackets [Monoid₂ α] mean: "assume that α has a structure
of monoid, and find it by type class inference". Now is a good moment
to review the three kinds of arguments in Lean we have seen so far:
    - (x : α) is an explicit argument: we have to give it every time
      we use the theorem (or the function).
    - {x : α} is an implicit argument: Lean figures it out from the
      other arguments. For instance, in one_unique above, α can be
      deduced from e : α, so we do not need to write it.
    - [inst : Monoid₂ α] is an instance argument: Lean synthesizes it
      using type class inference. Since the whole point of such
      arguments is that we generally do not need to refer to them
      explicitly, Lean allows us to write [Monoid₂ α] and leave the
      name anonymous.
If we really need to give all arguments explicitly, we write @ before
the name of the theorem:
-/

#check Monoid₂.one_unique   -- α and the instance are hidden
#check @Monoid₂.one_unique  -- everything is explicit

example (e : ℕ) (h : ∀ x, Monoid₂.mul e x = x) : e = 0 :=
  Monoid₂.one_unique e h

example (e : ℕ) (h : ∀ x, Monoid₂.mul e x = x) : e = 0 :=
  @Monoid₂.one_unique ℕ natAdd e h

/-
The first example is how we write mathematics; the second one is
what Lean sees. Note that Lean knows that Monoid₂.one is 0 for ℕ,
since it unfolds the instance natAdd.

Instances can depend on other instances. This is where type class
inference really shines. For instance, the product of two monoids is
a monoid:

(Below α × β is the product type; its set-theoretical analogue
is the Cartesian product. You can take for granted that every term of type
α × β is constructed from a term of type α and a term of type β using
the anonymous constructor (in other words, it works exactly like ∧).)
-/

instance {α β : Type} [Monoid₂ α] [Monoid₂ β] : Monoid₂ (α × β) where
  mul := fun p q => (Monoid₂.mul p.1 q.1, Monoid₂.mul p.2 q.2)
  one := (Monoid₂.one, Monoid₂.one)
  mul_assoc := by
    intro p q r
    ext
    · exact Monoid₂.mul_assoc p.1 q.1 r.1
    · exact Monoid₂.mul_assoc p.2 q.2 r.2
  one_mul := by
    intro p
    ext
    · exact Monoid₂.one_mul p.1
    · exact Monoid₂.one_mul p.2
  mul_one := by
    intro p
    ext
    · exact Monoid₂.mul_one p.1
    · exact Monoid₂.mul_one p.2

#eval Monoid₂.mul (1, 2) (3, 4)               -- (4, 6)
#eval (Monoid₂.one : ℕ × (ℕ × ℕ))             -- (0, 0, 0)
#synth Monoid₂ (ℕ × (ℕ → ℕ))                  -- the instance found

/-
To find an instance of Monoid₂ (ℕ × (ℕ × ℕ)), Lean uses the product
instance, and then it has to find instances of Monoid₂ ℕ and of
Monoid₂ (ℕ × ℕ): the first one is natAdd, and the second one is
again the product instance, and so on. The command #synth shows us
which instance Lean finds.
-/

/-
Define an instance of Monoid₂ on the type Bool of booleans, with
the "or" operation (written a || b) and unit false. Hint: you can
prove the axioms using cases (cases a splits into the cases a = true
and a = false), or using decide, which checks all the cases by
itself.
-/

instance : Monoid₂ Bool where
  mul := sorry
  one := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

example : Monoid₂.mul false (Monoid₂.mul true false) = true := by
  sorry
  -- Careful: a simple rw will not work here, because rw does
  -- not identify false with Monoid₂.one automaticaaly. You need to use
  -- something more powerful, like simp.

/-
Notation. Writing Monoid₂.mul x y is still far from x * y. Luckily,
Lean lets us introduce notation. For instance:
-/

infixl:70 " ⋆ " => Monoid₂.mul

notation "𝟙" => Monoid₂.one

/-
Now x ⋆ y (⋆ is typed \star) means Monoid₂.mul x y, and 𝟙 (typed
\b1) means Monoid₂.one. The number 70 is the precedence, which says how
strongly ⋆ binds, and infixl means that x ⋆ y ⋆ z is (x ⋆ y) ⋆ z.
For instance, + has precedence 65 and * has 70, so a + b * c is
a + (b * c).
-/

example {α : Type} [Monoid₂ α] (x y z : α) :
    x ⋆ y ⋆ z = x ⋆ (y ⋆ z) :=
  Monoid₂.mul_assoc x y z

example {α : Type} [Monoid₂ α] (x : α) : 𝟙 ⋆ x ⋆ 𝟙 = x := by
  rw [Monoid₂.mul_one, Monoid₂.one_mul]

/-
Now prove the following with our notation:
-/

example {α : Type} [Monoid₂ α] (w x y z : α) :
    (w ⋆ x) ⋆ (y ⋆ z) = w ⋆ ((x ⋆ y) ⋆ z) := by
  sorry

/-
Now we can understand how algebra works in
mathlib. Groups, rings, fields, vector spaces, ... are all classes,
with the usual notation, and ℝ, ℤ, ... are instances of them. Thus,
to work in a group G, we write [Group G], and all the theorems about
groups in mathlib are available:
-/

section

variable {G : Type} [Group G]

#check mul_assoc      -- mul_assoc (a b c : G) : a * b * c = a * (b * c)
#check one_mul        -- one_mul (a : M) : 1 * a = a
#check inv_mul_cancel -- inv_mul_cancel (a : G) : a⁻¹ * a = 1
#check mul_inv_rev    -- mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹

example (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

example (a b c : G) (h : a * b = a * c) : b = c := by
  calc
    b = a⁻¹ * (a * b) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = c := by rw [← mul_assoc, inv_mul_cancel, one_mul]

/-
Mathlib also knows that some concrete types are groups. For
instance, the permutations of a type α form a group, Equiv.Perm α,
with the composition:
-/

end

/-
Rings work in the same way. Recall that ring proves identities in
commutative rings: now we know that it works for any type R with an
instance [CommRing R].
-/

section

variable {R : Type} [CommRing R]

example (a b : R) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

#synth CommRing ℤ
#synth Field ℝ

example (a b : R) (h : a + b = 0) : a ^ 2 = b ^ 2 := by
  have : a = -b := by
    rw [← sub_eq_zero, sub_neg_eq_add]
    exact h
  rw [this]
  ring

example (a b c : R) (h : a = b + c) : a * a - b * a = c * a := by
  rw [h]
  ring

example (a b : R) (h : a * b = 0) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  ring_nf
  rw [h]
  ring

end

/-
Finally, vector spaces. In mathlib, a vector space over a field K is
a module over K, i.e., an additive commutative group V with a scalar
multiplication K → V → V (written a • v, typed \smul) satisfying the
usual axioms. Thus, a vector space is given by three instances
[Field K] [AddCommGroup V] [Module K V] (we will understand why in
2.1.3):
-/

section

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

#check smul_add  -- smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
#check add_smul  -- add_smul (r s : R) (x : M) : (r + s) • x = r • x + s • x
#check smul_smul -- smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
#check one_smul  -- one_smul (M : Type u_1) (b : α) : 1 • b = b

example (a : K) (u v : V) : a • (u + v) - a • v = a • u := by
  rw [smul_add, add_sub_cancel_right]

example (a b : K) (v : V) : (a + b) • v - b • v = a • v := by
  sorry

example (a : K) (ha : a ≠ 0) (v : V) : a⁻¹ • a • v = v := by
  sorry

example (v : V) : (2 : K) • v = v + v := by
  calc
    (2 : K) • v = ((1 : K) + (1 : K)) • v := by rw [one_add_one_eq_two]
              _ = (1 : K) • v + (1 : K) • v := by rw [add_smul]
              _ = v + v := by rw [one_smul]

end

/-
Structures are usually accompanied by maps preserving
them. These maps are, again, structures: a monoid morphism is a
function, together with the proofs that it preserves the operation
and the unit. Let us define them for our monoids:
-/

structure MonoidHom₂ (α β : Type) [Monoid₂ α] [Monoid₂ β] where
  toFun : α → β
  map_one : toFun 𝟙 = 𝟙
  map_mul : ∀ x y, toFun (x ⋆ y) = toFun x ⋆ toFun y

/-
Note that MonoidHom₂ is a structure, not a class: there may be many
morphisms between two monoids, so we do not want Lean to choose one
for us. For instance, doubling is a morphism of (ℕ, +, 0):
-/

def double : MonoidHom₂ ℕ ℕ where
  toFun := fun n => 2 * n
  map_one := rfl
  map_mul := by
    intro x y
    exact Nat.mul_add 2 x y

#eval double.toFun 21  -- 42

namespace MonoidHom₂

variable {α β γ : Type} [Monoid₂ α] [Monoid₂ β] [Monoid₂ γ]

/-
The identity of α is always a monoid homomorphism.
-/

def id : MonoidHom₂ α α where
  toFun := fun x => x
  map_one := rfl
  map_mul := fun _ _ => rfl

/-
Now define the composition of morphisms (the composition of the
functions g.toFun and f.toFun is g.toFun ∘ f.toFun), and prove that
a morphism maps inverses (if they exist) to inverses:
-/

def comp (g : MonoidHom₂ β γ) (f : MonoidHom₂ α β) : MonoidHom₂ α γ where
  toFun := g.toFun ∘ f.toFun
  map_one := by
    dsimp
    repeat rw [map_one]
  map_mul := by
    intro x y
    dsimp
    rw [map_mul, map_mul]

theorem map_of_mul_eq_one (f : MonoidHom₂ α β) (x y : α) (h : x ⋆ y = 𝟙) :
    f.toFun x ⋆ f.toFun y = 𝟙 := by
  rw [← map_mul, h, map_one]

end MonoidHom₂

/-
Writing f.toFun x instead of f x is annoying. We will fix this in
2.1.4, with coercions.

Mathlib has morphisms for all its structures, with their own
notation:
    - G →* H is the type of monoid (or group) morphisms,
    - R →+* S is the type of ring morphisms,
    - V →ₗ[K] W is the type of K-linear maps.
For them, we can already write f x, instead of f.toFun x (again, we will see this in 2.1.4):
-/

section

variable {G H : Type} [Group G] [Group H]

example (f : G →* H) (x y : G) : f (x * y) = f x * f y :=
  f.map_mul x y

example (f : G →* H) : f 1 = 1 :=
  f.map_one

example (f : G →* H) (x : G) : f x⁻¹ = (f x)⁻¹ :=
  map_inv f x

example (f : G →* H) (x y : G) : f (x * y⁻¹) = f x * (f y)⁻¹ := by
  rw [map_mul, map_inv]

variable {R S : Type} [Ring R] [Ring S]

example (f : R →+* S) (a b : R) : f (a * b + 1) = f a * f b + 1 := by
  rw [map_add, map_mul, map_one]

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

example (f : V →ₗ[K] W) (a : K) (u v : V) :
    f (a • u + v) = a • f u + f v := by
  rw [map_add, map_smul]

end

/-
    (*) The actual definitions in mathlib are more general than ours.
    For instance, MonoidHom M N extends two structures: OneHom M N,
    which contains toFun and map_one', and MulHom M N, which contains
    toFun and map_mul'. And it only assumes [MulOneClass M], which is
    a monoid without associativity. Moreover, theorems such as
    map_mul do not talk about MonoidHom, but about any type F of
    "morphism-like" things, with an instance [MonoidHomClass F M N].
    In this way, map_mul works at the same time for monoid morphisms,
    ring morphisms, linear maps, isomorphisms, ... This is why we
    could use map_mul and map_inv above both for groups and rings.
    Try #check @map_mul, and look at the definitions of MonoidHom and
    MonoidHomClass with Ctrl+click. In MonoidHomClass, M and N are
    outParams: this tells type class inference that M and N are
    determined by F, so that Lean can find them from f : F.
-/
