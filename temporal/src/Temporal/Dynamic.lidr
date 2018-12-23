-*- coding: utf-8 -*-
Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

> module Temporal.Dynamic

> import Temporal.Core
> import Data.SortedMap

> %default total
> %access public export

> memoizeA : Ord a => SF r t a b -> SF r t a b

> multiplexA : Ord k => (k -> SF r t a b) -> SF r t (k, a) b
