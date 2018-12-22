-*- coding: utf-8 -*-
Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
License  : GNU AGPL, version 3 or later;http://www.gnu.org/licenses/agpl.html

> module Temporal.Time

> import Temporal.Core
> import Temporal.Event

> %default total
> %access public export

> time : SF r t a t
> time = SFGen $ \_, t, _ => (time, t)

> timed : (t -> t -> Bool) -> SF r t a (Event a)
> timed p = SFGen $ \r, t, x =>
>           if p t t then (go t, Now x) else (go t, NotNow)
>   where go : t -> SF r t a (Event a)
>         go o = SFGen $ \r, t, x =>
>           if p o t then (go o, Now x) else (go o, NotNow)

> at : (Eq t, Num t) => t -> SF r t a (Event a)
> at n = timed $ \o, t => t == o + n

> for : (Ord t, Num t) => t -> SF r t a (Event a)
> for n = timed $ \o, t => t > o + n

> after : (Ord t, Num t) => t -> SF r t a (Event a)
> after n = timed $ \o, t => t < o + n

