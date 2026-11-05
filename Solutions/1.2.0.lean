import Mathlib

/- 1.2 Tactics and mathlib [MIL, Chapters 2, 3, 4] -/

/- Careful!! This file imports Mathlib, a big library, and you don't
   want Lean to compile it from scratch. For this reason, if you are
   running this file locally, you should run the command
    lake exe cache get
   on your terminal. This will fetch the compiled Mathlib files
   directly, and save them into your project folder. If it works
   properly, you only have to run it once.
-/

/-
In this section you will learn how Lean can automate the process of
writing proofs through tactics. You will use this automation to solve
exercises similar to those in the previous section, but much more
easily. Then we will jump to some real mathematics: after
introducing mathlib, you will be able to prove basic properties of
limits by yourself. Finally, we shall explain how sets and
functions, the foundations of usual mathematics, work in Lean.
-/

/-
The line import Mathlib at the top of this file loads the whole of
mathlib (more on it in 1.2.2). Imports must always come first in a
file.
-/
