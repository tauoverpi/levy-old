-*- coding: utf-8 -*-
Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

> module Temporal.Switch

> import Temporal.Core
> import Temporal.Event

> %default total
> %access public export

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

                            now
 A >------------,---------------,-----------> B
         notnow  \             /
 A >--------------'-----------'-------------> B

> ||| Act as the second signal function upon inhibition
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

 A >------------------,---------------------> B
            (b, now)   \
                        '-------------------> B

> ||| Switch to a new signal function produced by the initial upon event
> switchA : SF r t a (b, Event $ SF r t a b) -> SF r t a b
> switchA sf = SFGen $ \r, t, x => case stepSF sf r t x of
>   (sf, b, NotNow) => (switchA sf, b)
>   (_, b, Now sf)  => stepSF sf r t x

 A >------------------,---------------------> B
            (b, now)   \
                        '-------------------> B

> ||| Construct and switch to the newly constructed signal function upon event
> switchFA : (c -> SF r t a b) -> SF r t a b -> SF r t (a, Event c) b
> switchFA sw sf = SFGen $ \r, t, x => case x of
>   (a, NotNow) => let (sf, b) = stepSF sf r t a in (switchFA sw sf, b)
>   (a, Now c)  => let (sf, b) = stepSF (sw c) r t a in (switchFA sw sf, b)

> ||| Reset the given signal function upon event
> resetA : SF r t a b -> SF r t (a, Event c) b
> resetA old = gen old where
>   gen sf = SFGen $ \r, t, x => case x of
>     (a, NotNow) => let (sf, b) = stepSF sf r t a in (gen sf, b)
>     (a, Now _)  => let (sf, b) = stepSF old r t a in (gen sf, b)

> ||| Allow the given signal function to reset itself for the next frame
> resetSelfA : SF r t a (b, Event c) -> SF r t a b
> resetSelfA old = gen old where
>   gen sf = SFGen $ \r, t, x => case stepSF sf r t x of
>     (sf, b, NotNow) => (gen sf, b)
>     (sf, b, Now _)  => (gen old, b)
