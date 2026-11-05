/- 1.1.3 Propositions as types -/

/-
We have seen that Lean has types and terms, but what about
statements and proofs? Here comes the key idea: a proposition is a
type, and a proof of a proposition is a term of that type. There is a
special type Prop, whose terms are propositions:
-/

#check 2 + 2 = 4    -- Prop
#check 2 + 2 = 5    -- Prop

/-
Note that 2 + 2 = 5 is a perfectly good proposition, it is just false,
so we will never be able to construct a term of it. Proving a
proposition p therefore means constructing a term h : p. There are two
ways of reading h : p, and you should get used to both:
    - The logical one: h is a proof of p. If we have h : p, then p is
      true, and h is the evidence. This is why we usually call proofs
      h, for "hypothesis".
    - The set-theoretic one: p is a type, a sort of set whose
      elements are the proofs of p, and h is one of these elements.
      Then p is true if it has some element, and false if it is empty.
      So 2 + 2 = 5 is an empty type.

    (*) In mathematics we do not distinguish between two proofs of
    the same statement: what matters is that there is one. Lean
    agrees: any two proofs h₁ h₂ : p are equal by definition. This is
    called proof irrelevance, and it is the main thing that makes
    Prop different from Type.

How do we tell Lean that we are proving something? Remember that we
named terms with def name (arguments) : type := term. Theorems are
written in exactly the same way, with theorem instead of def:
    theorem name (hypotheses) : statement := proof

The only difference is that the statement is a proposition, i.e.,
lives in Prop. when we do not care about the name of the theorem, for
instance in examples and exercises, we use example, which is just an
anonymous theorem (or def) that is checked and then forgotten:
    example (hypotheses) : statement := proof

  (*) A proof is just a term, so we could even
  write def instead, but it is good practice to use theorem for proofs
  and def for everything else. For instance, Lean never unfolds a
  theorem to compute with it, since only its statement matters, not
  how it was proven.
-/

theorem two_plus_two : 2 + 2 = 4 := rfl

/-
Here rfl is a proof that a term is equal to itself, and Lean is happy
because 2 + 2 and 4 compute to the same thing. We will come back to
equality later.

The most important consequence of this point of view is about
implication. A proof of p → q is a function that takes a proof of p
and returns a proof of q. So implication is just the function type,
and the rules of logic become rules to build terms:
-/

example (p q : Prop) (hpq : p → q) (hp : p) : q := hpq hp

/-
Function application in Lean does not use parentheses.
So the application of the function hpq to hp is hpq hp.
-/

/-
And now, the sorry. When you do not know how to prove something (yet),
you can write sorry. Lean will accept it, but it will warn you with
"declaration uses 'sorry'". This is very useful to sketch a proof,
leave the details for later, and check that the rest makes sense. It
is also how exercises in this course are presented: replace each
sorry by an actual proof.
-/

example : 2 + 2 = 4 := sorry   -- Lean accepts this, with a warning!

/-
sorry is actually an axiom, called sorryAx, which proves
anything. This is why a finished proof should never contain one.
-/

/-
Let us now introduce the propositional connectives. For each of them
you have to know two things: how to prove it (introduction), and how
to use it (elimination). The following is an overview of these
connectives. Don't feel intimidated by it: we'll go through them one
by one, with lots of examples and exercises.

    Connective  Typed   Introduction            Elimination
    ----------  ------  ----------------------  -------------------------
    p → q       \to     fun hp => ...           hpq hp
    p ∧ q       \and    ⟨hp, hq⟩                h.1, h.2
    p ∨ q       \or     Or.inl hp, Or.inr hq    Or.elim h (fun hp => ...)
                                                          (fun hq => ...)
    ¬p          \not    fun hp => ...           hnp hp : False
    p ↔ q       \iff    ⟨hpq, hqp⟩              h.mp, h.mpr
    True                trivial
    False                                       False.elim h : r, for any r

The angle brackets ⟨ ⟩ are typed \< and \>. They are called the
anonymous constructor, and can be used whenever Lean knows which
structure it has to build. Note that ¬p is defined as p → False, so
to prove ¬p you assume p and reach a contradiction. The binding of
these connectors follows the usual mathematical convention; from
strongest to weakest, they are: negation, conjunction, disjunction,
implication, and biconditional.

Some examples and exercises:
-/

/-
The line variable (p q r : Prop) tells Lean that p, q, r are
propositions in everything that follows, until the end of the
section.
-/

section

variable (p q r : Prop)

/-
Implication. To prove p → q, we assume p and prove q, i.e., we write
a function fun hp => ... that takes a proof hp : p and returns a
proof of q. To use h : p → q, we apply it to a proof hp : p, and get
h hp : q. This is modus ponens.
-/

example : (p → q → r) → (q → p → r) := fun h hq hp => h hp hq

/-
Note that fun h hq hp => ... is short for
fun h => fun hq => fun hp => ..., and that p → q → r means
p → (q → r).
-/

example : (p → q) → (q → r) → (p → r) := sorry

example : (p → p → q) → p → q := sorry

/-
And. To prove p ∧ q, we prove both: given hp : p and hq : q, we get
⟨hp, hq⟩ : p ∧ q (this is And.intro hp hq). To use h : p ∧ q, we take
any of its two components: h.1 : p and h.2 : q (these are
And.left h and And.right h).
-/

#check And.intro

example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

example (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩

example : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
  fun ⟨hp, hq, hr⟩ => ⟨⟨hp, hq⟩, hr⟩

example : (p → q → r) → (p ∧ q → r) :=
  fun hpqr => (fun ⟨hp, hq⟩ => hpqr hp hq)

example : (p → q) → p ∧ r → q ∧ r :=
  fun hpq => (fun ⟨hp, hr⟩ => ⟨hpq hp, hr⟩)

/-
Most of the time, we don't write Lean terms directly, but use tactics
instead.
At this point of the course, you can continue reading to actually
learn the Lean fundamentals and how to construct terms, or jump
directly to 1.2.0 to start working with tactics and more tangible
mathematics quicker.
-/

/-
Or. To prove p ∨ q, we prove one of the two, and we have to say
which: given hp : p we get Or.inl hp : p ∨ q, and given hq : q we
get Or.inr hq : p ∨ q (inl and inr stand for "injection left" and
"injection right"). To use h : p ∨ q to prove some r, we argue by
cases: we prove r assuming p, and r assuming q. This is
Or.elim h (fun hp => ...) (fun hq => ...) : r.

Note that we cannot construct Or using the anonymous constructor; the reason is
that Or has more than one possible constructor.
-/

example : p → p ∨ q := fun hp => Or.inl hp

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

example : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
  fun hpqr => Or.elim hpqr (fun hp => Or.inl (Or.inl hp)) (fun hqr =>
    Or.elim hqr (fun hq => Or.inl (Or.inr hq)) (fun hr => Or.inr hr))

example : (p → r) → (q → r) → p ∨ q → r := sorry

example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := sorry

/-
Negation, True, and False. Remember that ¬p is p → False, so it
works exactly like an implication: to prove ¬p we assume hp : p and
prove False, and to use hnp : ¬p we apply it to some hp : p, getting
hnp hp : False. True is always provable, with trivial, and there is
nothing to gain from using it. False, on the contrary, cannot be
proven (unless our hypotheses are contradictory), but from h : False
we get False.elim h : r, for any proposition r. This is the principle
of explosion: from a contradiction, anything follows.
-/

example : True := trivial

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

example : False → p := fun hf => False.elim hf

example : p → ¬¬p :=
  fun hp => (fun hnp => hnp hp)

example : (p → q) → ¬q → ¬p :=
  fun hpq => (fun hnq => (fun hp => hnq (hpq hp)))

example : ¬(p ∧ ¬p) :=
  fun hpnp => hpnp.2 hpnp.1

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hnpnq => (fun ⟨hp, hq⟩ => Or.elim hnpnq (fun hnp => hnp hp) (fun hnq => hnq hq))

/-
If and only if. To prove p ↔ q, we prove both implications: given
hpq : p → q and hqp : q → p, we get ⟨hpq, hqp⟩ : p ↔ q (this is
Iff.intro hpq hqp). To use h : p ↔ q, we take any of the two
implications: h.mp : p → q and h.mpr : q → p (these are Iff.mp h and
Iff.mpr h, where mp stands for modus ponens, and mpr for its
reverse).
-/

example : p ∧ q ↔ q ∧ p :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

example (h : p ↔ q) (hp : p) : q := h.mp hp

example : (p ↔ q) → (q ↔ p) := sorry

example : (p ↔ q) → (q ↔ r) → (p ↔ r) := sorry

example : (p → q → r) ↔ (p ∧ q → r) := sorry

example : (p ∨ q → r) ↔ (p → r) ∧ (q → r) :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
   fun ⟨h1, h2⟩ => (fun hporq => Or.elim hporq h1 h2)⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
    fun ⟨hnp, hnq⟩ => (fun hpq => Or.elim hpq (fun hp => hnp hp) (fun
    hq => hnq hq))⟩
