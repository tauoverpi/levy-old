-*- coding: utf-8 -*-
Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
License  : GNU AGPL, version 3 or later;http://www.gnu.org/licenses/agpl.html

> module Temporal.Combinators

> import public Control.Category
> import public Control.Arrow

> import Temporal.Core

> %default total
> %access public export

> Category (SF r t) where

 A >----------------------------------------> A

>   id    = SFId

 C <----- (b -> c) ---------- (a -> b) -----< A

>   x . y = SFComp x y

> Arrow (SF r t) where

 A >--------------- (a -> b) ---------------> B

>   arrow f = SFArr f

 A >--------------- (a -> b) ---------------> B
 C >----------------------------------------> C

>   first f = SFPair f SFId

 A >----------------------------------------> A
 C >--------------- (c -> d) ---------------> D

>   second  = SFPair SFId

 A >--------------- (a -> b) ---------------> B
 C >--------------- (c -> d) ---------------> D

>   (***)   = SFPair

> ArrowChoice (SF r t) where

 A? >-------------- (a -> b) ---------------> B?
 C? >---------------------------------------> C?

>   left f  = SFChoice f SFId

 A? >---------------------------------------> A?
 C? >-------------- (c -> d) ---------------> D?

>   right g = SFChoice SFId g

 A? >-------------- (a -> b) ---------------> B?
 C? >-------------- (c -> d) ---------------> D?

>   (+++)   = SFChoice

> Functor (SF r t a) where
>   map f sf = SFMap sf f
>

> Applicative (SF r t a) where

 _ >--------------- (_ -> a) ---------------> A

>   pure = SFConst

 (a -> b) >-----------------,
                            |---------------> B
 A >------------------------'

>   (<*>) = SFAp

> Semigroup b => Semigroup (SF r t a b) where

 A >--------------- (a -> a) ---------------> B

>   (<+>) = liftA2 (<+>)

> Monoid b => Monoid (SF r t a b) where

 A >--------------- (a -> a) ---------------> B

>   neutral = SFConst neutral

                         B
                          \
 A >---------------------, '----------------> B
            next frame   '------------------> B

> delayA : b -> SF r t a b -> SF r t a b
> delayA b f = SFGen $ \r, t, x =>
>              let (n, b') = stepSF f r t x in
>              (delayA b' n, b)

 A >-------,-------- (a, c) --------,-------> B
            \                      /
             '--------< c <---,---'
                             /
                            C

TBD: Implement everything in terms of feedback

> feedbackA : c -> SF r t (a, c) (b, c) -> SF r t a b
> feedbackA = SFFeedback

 A >-------,-------- a + c --------,--------> B
            \                     /
             '-------< c <---,---'
                            /
                           C

> accumA : (a -> b -> b) -> b -> SF r t a b
> accumA (+) b = feedbackA b $ arrow sum
>   where sum (a, c) = let r = a + c in (r, r)

 A >-------,--------- fn c ---------,-------> B
            \                      /
             '--------< c <---,---'
                             /
                            C

> iteratorA : (b -> b) -> b -> SF r t a b
> iteratorA fn = accumA (const fn)

 A >------------ (a -> Bool) ---------------> Either A A

> testA : (a -> Bool) -> SF r t a (Either a a)
> testA p = arrow (\x => if p x then Left x else Right x)
