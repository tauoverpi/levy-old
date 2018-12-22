-*- coding: utf-8 -*-
Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
License  : GNU AGPL, version 3 or later;http://www.gnu.org/licenses/agpl.html

> module Temporal.Reader

> import Temporal.Core

> %default total
> %access public export

> asks : (r -> b) -> SF r t a b
> asks get = SFGen $ \r, _, _ => (asks get, get r)

> ask : SF r t a r
> ask = asks id
