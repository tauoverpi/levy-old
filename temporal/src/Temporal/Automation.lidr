-*- coding: utf-8 -*-
Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
License  : GNU AGPL, version 3 or later;http://www.gnu.org/licenses/agpl.html

> module Temporal.Automation

> import public Temporal.Core
> import public Temporal.Event
> import public Temporal.Combinators

> %default total
> %access public export

> ||| Automation
> Auto : Type -> Type -> Type
> Auto = SF () ()

> ||| Automation with the reader monad
> AutoR : Type -> Type -> Type -> Type
> AutoR r = SF r ()
