-*- coding: utf-8 -*-
Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
License  : GNU AGPL, version 3 or later;http://www.gnu.org/licenses/agpl.html

> module Temporal.Event

> import Temporal.Core
> import Temporal.Combinators

> %default total
> %access public export

> data Event a
>  = NotNow
>  | Now a

> Interval : (r, t, a, b : Type) -> Type
> Interval r t a b = SF r t a (Event b)

> Functor Event where
>   map f NotNow = NotNow
>   map f (Now a) = Now (f a)

> Applicative Event where
>   pure = Now
>   (Now f) <*> (Now x) = Now (f x)
>   _       <*> _       = NotNow

> Monad Event where
>   join NotNow = NotNow
>   join (Now a) = a

> Semigroup a => Semigroup (Event a) where
>   NotNow  <+> e        = e
>   e       <+> NotNow   = e
>   (Now e) <+> (Now e') = Now (e <+> e')
>   _       <+> _        = NotNow

 _ >--------------- (_ -> _) ---------------> Event _

> ||| Inhibit forever
> neverE : Interval r t a b
> neverE = SFConst NotNow

                            B
                             \
 A >------------------------, '-------------> Event B
                next frame  '---------------> Event _

> ||| Produce once then inhibit forever
> ||| ```idris example
> ||| exampleSF (nowE 0) 0 0 0
> ||| ```
> nowE : b -> Interval r t a b
> nowE b = SFGen $ \_, _, _ => (neverE, Now b)

 A >------------------------,---------------> Event A
                next frame  '---------------> Event _

> onceE : Interval r t a b -> Interval r t a b
> onceE a = SFGen $ \r, t, x => case stepSF a r t x of
>   (n, NotNow) => (onceE n, NotNow)
>   (_, Now x) => (neverE, Now x)

 A >-----------------------,----------------> A
                      now   \
 A >-------------------------'--------------> A

> holdA : b -> SF r t (Event b) b
> holdA b = SFGen $ \_, _, x => case x of
>   NotNow => (holdA b, b)
>   Now b  => (holdA b, b)

                         A
                          \
 A >---------------------, '----------------> A
            next frame   '----,-------------> A
                         now   \
 A >----------------------------'-----------> A

> holdNextA : b -> SF r t (Event b) b
> holdNextA b = delayA b (holdA b)

 Event A >-- F E E D B A C K ---------------> B

            [ (+) : a -> b -> b ]

> accumE : (a -> b -> b) -> b -> SF r t (Event a) b
> accumE {b} (+) k = feedbackA k $ arrow event
>   where event : (Event a, b) -> (b, b)
>         event (NotNow, b) = (b, b)
>         event (Now x, b) = let r = x + b in (r, r)

 A >------------ (a -> Bool) ---------------> Event A

> filterA : (a -> Bool) -> SF r t a (Event a)
> filterA p = testA p >>> arrow Now \|/ neverE
