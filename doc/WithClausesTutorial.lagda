(this is a literate Agda file)

============
Introduction
============

This file demonstrates the usage of the agda2-add-with-exp* functions.
The basic idea is to allow a more convenient way to add with expressions 
during interactive development.

==========
An example
==========

Suppose we're working with nats and booleans.

\begin{code}
module WithClausesTutorial where

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; zero; suc; _≟_; _+_)
open import Relation.Nullary

\end{code}

And we want/need to write a comparison function from nats to bool.

\begin{code}
equal? : ℕ → ℕ → Bool
\end{code}

I would now create a stub by naming all arguments.

equal? n m = \?      -- the backslash is needed to evade a lagda bug

Let's say I recalled the _≟_ function. To use it, we have to add
a with clause. Since we have already created a goal, we have to:

1) delete everything starting from the '=' character
2) write the with clause
3) type '... | res = ?' in the next line or type/copy paste 'equal? n m'
4) load the file and request a case analize on res

This seems to be a very common use case, and going through all of this
quickly gets mundane. One wishes to have it automated!

That's what agda2-add-with-exp* functions are exactly for.

Write the expression you want to analyze using a with expression
in the goal: 

\begin{code}
equal? n m = {! n ≟ m !}

\end{code}

1) type C-c C-w   (w stands for 'with') to get:

equal? n m with n ≟ m
... | cond0 = \?

2) type C-u C-c C-w to get:

equal? n m with n ≟ m
equal? n m | cond0 = \?

For convenience, the file will be loaded, and the cursor will be located
inside the new goal

Actually, both 1 & 2 can work with more that one clause, you only have to
separate them with the usual '|'. For example, try C-c C-w in the goal below:

\begin{code}
equal?' : ℕ → ℕ → Bool
equal?' n m = {!n ≟ m | n + m!}
\end{code}

We will get this:

equal?' : ℕ → ℕ → Bool
equal?' n m with n ≟ m | n + m
... | cond0 | cond1 = {!!}


3) type C-c C-x C-w to get:

equal? n m with n ≟ m
equal? n m | yes p = {!!}
equal? n m | no ¬p = {!!}

so 3) is just 2) combined with C-c C-c on the (first) introduced name

========================
Mnemonics for keybidings
========================

C-c C-w
  generates the shortest code so it uses the shortest binding

C-u C-c c-w 
  generates a more detailed version, so a prefix is needed

C-c C-x C-w
  combines C-c C-w with one another command, so it has C-x in the middle

========================================
That's all! I hope you find this useful!

Wojtek Jedynak
wjedynak@gmail.com
