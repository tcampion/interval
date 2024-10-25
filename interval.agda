{-# OPTIONS --type-in-type --without-K --guardedness --prop --show-implicit #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat


record ∧ (P Q : Prop) : Prop where
    field
        fst : P
        snd : Q

data ∨ (P Q : Prop) : Prop where
    inl : P → ∨ P Q
    inr : Q → ∨ P Q

∨-rec : {P Q R : Prop} (p : P → R) (q : Q → R) (a : ∨ P Q) → R
∨-rec p q (inl x) = p x
∨-rec p q (inr x) = q x

record LinearlyOrdered (I : Set) : Set where
    field
        le : (i j : I) → Prop
        trans : {i j k : I} (a : le i j) (b : le j k) → le i k
        ref : (i : I) → (le i i)
        asym : {i j : I} (a : le i j) (b : le j i) → i ≡ j
        lin : (i j : I) → ∨ (le i j) (le j i)

record Bounded {I : Set} (linOrd : LinearlyOrdered I) : Set where
    open LinearlyOrdered linOrd
    field
        bot top : I
        botbelow : (i : I) → le bot i
        topabove : (i : I) → le i top

module Basic 
    {I : Set}
    {li : LinearlyOrdered I}
    (bd : Bounded li)
    where
    open LinearlyOrdered li
    open Bounded bd
    botbot : {i : I} (a : le i bot) → bot ≡ i
    botbot {i} a = asym (botbelow i) a
    toptop : {i : I} (a : le top i) → top ≡ i
    toptop {i} a = asym a (topabove i)

module Simplicial
    (I : Set)
    (li : LinearlyOrdered I)
    (bd : Bounded li)
    where
    open LinearlyOrdered li
    open Bounded bd
    open Basic bd

    {- Define the simplices : A simplex in positive degree consists of a simplex S of one dimension down, plus an additional coordinate leq the last coordinate of S -}
    data Delta : (n : Nat) → Set 
    Last : {n : Nat} (d : Delta n) → I
    data Delta where
        triv : Delta zero
        cons : {n : Nat} (d : Delta n) {i : I} (a : le i (Last d)) → Delta (suc n)
    Last triv = top
    Last (cons d {i} a) = i

    {- The following is perhaps a misnomer -}
    Nerve : (C : Set) (n : Nat) → Set
    Nerve C n = (d : Delta n) → C

    {- Now define some simplicial operators as well as some maps between simplices -}
    Ob : (C : Set) → Set
    Ob C = Nerve C 0

    Mor : (C : Set) → Set
    Mor C = Nerve C 1

    d00 : (d : Delta 0) → Delta 1
    d00 triv = cons triv (ref top)
    
    d01 : (d : Delta 0) → Delta 1
    d01 triv = cons triv (botbelow top) -- awkward -- have to choose between botbelow top and topabove bot. But so far looks like it doesn't matter given that le is Prop-valued!

    dom : {C : Set} (f : Mor C) → Ob C
    dom f d = f (d01 d)

    cod : {C : Set} (f : Mor C) → Ob C
    cod f d = f (d00 d)

    Triangle : (C : Set) → Set
    Triangle C = Nerve C 2

    d10 : (d : Delta 1) → Delta 2
    d10 (cons triv a) = cons (d00 triv) a

    d11 : (d : Delta 1) → Delta 2
    d11 d = cons d (ref (Last d))
    
    d12 : (d : Delta 1) → Delta 2
    d12 d = cons d (botbelow (Last d))

    fstof : {C : Set} (t : Triangle C) → Mor C
    fstof t d = t (d12 d)

    sndof : {C : Set} (t : Triangle C) → Mor C
    sndof t d = t (d10 d)

    compof : {C : Set} (t : Triangle C) → Mor C
    compof t d = t (d11 d)

    {- SIMPLICIAL IDENTITIES (only a few fo them so far) -}

    -- look at these sweet, sweet refl identities!
    globId : d10 (d00 triv) ≡ d11 (d00 triv)
    globId = refl
    
    simpId : d10 (d01 triv) ≡ d12 (d00 triv)
    simpId = refl 

    globId' : d11 (d01 triv) ≡ d12 (d01 triv)
    globId' = refl -- if le is Set-valued, this fails becauase topabove bot ≠ botbelow top, but works when it's Prop-valued!

    record hornIn (C : Set) : Set where
        pattern
        constructor argh
        field
            fst snd : Mor C 
            compat : cod fst triv ≡ dom snd triv

    res : {C : Set} (t : Triangle C) → hornIn C
    hornIn.fst (res t) = fstof t
    hornIn.snd (res t) = sndof t
    hornIn.compat (res t) = refl -- BOOYAKASHAH! didn't need to explicitly invoke simpId and even worked before putting in d as an argument
                   
