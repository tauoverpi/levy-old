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
> neverE : SF r t a (Event b)
> neverE = SFConst NotNow

                            B
                             \
 A >------------------------, '-------------> Event B
                next frame  '---------------> Event _

> ||| Produce once then inhibit forever
> ||| ```idris example
> ||| exampleSF (nowE 0) 0 0 0
> ||| ```
> nowE : b -> SF r t a (Event b)
> nowE b = SFGen $ \_, _, _ => (neverE, Now b)

 A >------------------------,---------------> Event A
                next frame  '---------------> Event _

> onceE : SF r t a (Event b) -> SF r t a (Event b)
> onceE a = SFGen $ \r, t, x => case stepSF a r t x of
>   (n, NotNow) => (onceE n, NotNow)
>   (_, Now x) => (neverE, Now x)

 A >------------------------,---------------> B
                  notnow     \
 A >--------------------------'-------------> B

> becomeA : SF r t a (Event b) -> SF r t a b -> SF r t a b
> becomeA a b = SFGen $ \r, t, x => case stepSF a r t x of
>   (_, NotNow) => stepSF b r t x
>   (a, Now x)  => (becomeA a b, x)

> infixr 7 ->>
> (->>) : SF r t a (Event b) -> SF r t a b -> SF r t a b
> (->>) = becomeA

 A >------------------------,---------------> Event B
                  notnow     \
 A >--------------------------'-------------> Event B

> becomeE : SF r t a (Event b) -> SF r t a (Event b) -> SF r t a (Event b)
> becomeE a b = SFGen $ \r, t, x => case stepSF a r t x of
>   (_, NotNow) => stepSF b r t x
>   (a, Now x)  => (becomeE a b, Now x)

> (>>) : SF r t a (Event b) -> SF r t a (Event b) -> SF r t a (Event b)
> (>>) = becomeE

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

 A >------------------,---------------------> B
            (b, now)   \
                        '-------------------> B


> switchA : SF r t a (b, Event $ SF r t a b) -> SF r t a b
> switchA sf = SFGen $ \r, t, x => case stepSF sf r t x of
>   (sf, b, NotNow) => (switchA sf, b)
>   (_, b, Now sf) => stepSF sf r t x

                            now
 A >------------,---------------,-----------> B
         notnow  \             /
 A >--------------'-----------'-------------> B

> altA : SF r t a (Event b) -> SF r t a b -> SF r t a b
> altA a b = SFGen $ \r, t, x => case stepSF a r t x of
>   (n, NotNow) => let (m, x) = stepSF b r t x in (altA n m, x)
>   (n, Now x)  => (altA n b, x)

> infixr 2 </>
> (</>) : SF r t a (Event b) -> SF r t a b -> SF r t a b
> (</>) = altA

                            now
 A >------------,---------------,-----------> Event B
         notnow  \             /
 A >--------------'-----------'-------------> Event B

> altE : SF r t a (Event b) -> SF r t a (Event b) -> SF r t a (Event b)
> altE a b = SFGen $ \r, t, x => case stepSF a r t x of
>   (n, NotNow) => let (m, x) = stepSF b r t x in (altE n m, x)
>   (n, x)  => (altE n b, x)

> (<|>) : SF r t a (Event b) -> SF r t a (Event b) -> SF r t a (Event b)
> (<|>) = altE

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
