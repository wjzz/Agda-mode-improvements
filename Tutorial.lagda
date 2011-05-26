( This is a literate Agda file )

============
Introduction
============

This is very short tutorial introduction to a experimental emacs-mode feature.
The basic idea is that we would like to emulate hint databases that are present
in the Coq Proof Assistant. For reference, I will call this feature auto-with-dbs.

<introduction to Agsy>
Agda has a automation utility called Agsy. After placing the cursor in the goal,
we can ask Agsy to try solving it by C-c C-a (using Agda-mode for Emacs). From
my short experience with this tool, it seems that this way we can only build
terms build with constructors and recursive calls. If an auxilary theorem is
needed we have to either manually give it as a hint (by typing it's name in the
goal and using C-c C-a) or by asking it to check the contents of the current 
module by typing -m. 
</introduction to Agsy>

This works in many cases, but sometimes we want to prove a couple of theorems 
by case analysis/structural induction and some cases are either trivial or
follow by congruence + induction hypothesis. It has been my experience that
in those cases one has to give hints such as cong, cong₂, sym each and every
time. This could be avoided if we could collect useful and often used lemmas
in some kind of theorem databases. After that we would only type the name
of the database that we want auto to try theorems from. 

I have prototyped this feature in emacs-lisp and in this tutorial I will 
describe how it can be used in practise. So far I have only tested it on 
Agda 2.2.10.

============
Installation
============

All you need to do is to replace the agda2-mode.el file with the version
from my repository:
https://github.com/wjzz/Agda-mode-improvements
To locate the directory with the emacs-lisp files for agda-mode type:
 agda-mode locate
in your terminal.

===============================
Using the auto-with-dbs feature
===============================

To use auto with a given database(s) you have to:
1) place the cursor in a goal
2) type the name(s) of the database(s) you want to use (this can be combined with 
the standard agsy options, such as -c and -t 10)
3) enter C-u C-c C-a    (this will invoke the agda2-solve-with-db function)

For examples please look below.

If multiple databases' names are inputed then all lemmas included in at least
one of them will be tried.

If auto will be able to solve the goal with the given hints, then the solution
will be inserted in place of the goal automatically (just as will normal auto),
if not then the lists of hints will show up in the goal (if this behavior will
prove inconvenient I will change it).

=====================================================
Creating databases and adding theorems/lemmas to them
=====================================================

Databases do not have to be declared. All you need to do is to insert
a comment of the form: 
{- BASE name-of-database lemma_1 lemma_2 ... lemma_n -}

in the Agda source file that you want to use auto-with-dbs with.
The declaration should be placed below the proofs of the lemmas (otherwise
you will get an 'unknown name error'). The name of the database can be
any string not starting with a digit or the '-' character. Theorems can be
added to the same db incrementally, just by inserting multiple comments of
the form showed above. There is one default database called 'global'. The
only special thing about it is that if no name will be inputed in the goal
and the agda2-solve-with-db action will be run (with C-u C-c C-a) then
the db called "global" will be used.

For now, the databases are local to a file and have to be written in every
file. If the whole feature will prove useful, I will try to desing a more
modular solution.

=======================
auto-with-dbs in action
=======================

Let's try to prove that addition on natural numbers is commutative using some
automations. We will need two lemmas two prove on the way.

We'll need nats, ≡ and some properties of the equality.

\begin{code}

module Tutorial where

open import Data.Nat                              using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

\end{code}

The first lemma we will try to prove is

\begin{code}

lem-0 : (n : ℕ) → n + 0 ≡ n
lem-0 n = {!!}

\end{code}

This goal can't be solved by auto, as a case analysis is needed.
We can try to enter -c -t 15 into the goal and run auto, but still it won't be solved.
If we go ahead to prove lem-0 by hand we'll notice that the zero case is trivial, but
in the suc n case we need to go from 
lem-0 n : n + 0 ≡ n 
to 
lem-0 (suc n) : suc (n + 0) ≡ suc n

This can be done by using writing cong suc t, so if we type '-c cong' in the goal then
this time auto will handle it and we will get: (primes added to avoid duplicated definitions)

\begin{code}

lem-0' : (n : ℕ) → n + 0 ≡ n
lem-0' zero = refl
lem-0' (suc n) = cong suc (lem-0' n)

\end{code}

This approach works, but as our theorems get more complicated we might have to 
give more hints to auto. This is repetetive and boring. 

cong is a very useful and frequently used lemma. Let's add it to the global database,
along with sym and trans, and let's try to prove it using the db.

\begin{code}
{- BASE global cong sym trans -}

lem-0-r : (n : ℕ) → n + 0 ≡ n
lem-0-r n = {!!}

\end{code}

Go the the above goal, type '-c global' and press C-u C-c C-a. Voila!
Actualy, since we're using the global database, you may shorten '-c global'
just to '-c'!

Now that we are done with this lemma, we can add it to some databases,
for example: 

\begin{code}

{- BASE global lem-0-r -}
{- BASE arith lem-0-r -}

\end{code}

So at this point the global db will use cong, trans, sym and lem
while arith consists only of lem.

Now it's time for the second lemma. We won't go into details this time,
it suffices to mention that we need to use induction/recursion on n and
once again wrap the recursive call with cong suc. So we can again solve it by
typing '-c' and C-u C-c C-a. 

\begin{code}

lem-suc-n-m : (n m : ℕ) → suc (n + m) ≡ n + suc m
lem-suc-n-m n m = {!!}

\end{code}

Did it work?

!Important!

If at this place you get an error about inistantiated metavariables or an 
internal error message (this happens when you make a case analyze by hand 
on n the standard way (C-c C-c) and try to use the auto-with-dbs in a subgoal)
make sure that you have proven the lem-0-r lemma. It seems that auto can't work 
with incomplete lemmas, so be sure to  add only completed ones to the databases.

Now, that we've proven all the necessary helper lemmas, let's add it to the
global db and prove the final theorem.

\begin{code}

{- BASE global lem-suc-n-m -}

lem-comm : (n m : ℕ) → n + m ≡ m + n
lem-comm n m = {!!}

\end{code}

If you try the same '-c' and then C-u C-c C-a trick you might be a little
surprised by the generated term:

\begin{code}

lem3 : (n m : ℕ) → n + m ≡ m + n
lem3 zero m = cong (λ x → x) (sym (lem-0-r m))
lem3 (suc n) m = trans (cong suc (lem3 n m)) (lem-suc-n-m m n)

\end{code}

The term in the zero case can of course be simplified to
lem3 zero m = sym (lem-0-r m)

I know of one way to generate the clean version:
* perform a manual case analysis on n and then do
  C-u C-c C-a once on each goal (you don't have to input anything inside the goal)

I tried to swap cong and sym in the very first db declaration of this file to change the order
in which hints are processed by auto, but then we get

lem-comm zero m = sym (cong (λ x → x) (lem-0-r m))

:-)

OK, this is it! I hope you like this small feature!

Wojtek Jedynak
wjedynak@gmail.com
