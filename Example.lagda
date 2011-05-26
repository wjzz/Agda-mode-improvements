This is a literate Agda file. 

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

Installation
============

All you need to do is to replace the agda2-mode.el file with the version
from my repository/attached to the e-mail. To locate the directory in
which you emacs-file files for agda-mode type
$ agda-mode locate
in your terminal.

Creating theorems/lemma to databases
====================================

Databases do not have to be declared. All you need to do is to insert
a comment of the form: 
{- BASE name-of-database lemma1 lemma2 ... lemman -}

anywhere in the Agda source file that you want to use auto-with-dbs.
The declaration should be placed below the proofs of the lemmas (otherwise
you will get an 'unknown name error'). The name of the database can be
any string not starting with a digit or the '-' character.

\begin{code}

module Example where

open import Data.Nat

open import Relation.Binary.PropositionalEquality

{- BASE global sym cong trans -}

lem : (n : ℕ) → n + 0 ≡ n
lem n = {!!}

{- BASE global lem -}

lem2 : (n m : ℕ) → suc (n + m) ≡ n + suc m
lem2 n m = {!!}

{- BASE global lem2 -}

lem3 : (n m : ℕ) → n + m ≡ m + n
lem3 n m = {!!}

\end{code}