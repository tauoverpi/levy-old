-*- coding: utf-8 -*-
Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
License  : GNU AGPL, version 3 or later;http://www.gnu.org/licenses/agpl.html

> module Temporal.Core

> %default total
> %access public export

> ||| Stream function
> ||| @r reader
> ||| @t delta time
> ||| @a input
> ||| @b output
> data SF : (r, t, a, b : Type) -> Type where

Generic signals for the case when the result doesn't fit any other shape.
Since this format lacks structure it can't be optimized furter.

>   SFGen   : (sf : r -> t -> a -> (Inf $ Lazy $ SF r t a b, b)) -> SF r t a b

Pure signals carry an additional parameter for the function they apply for
better behaviour with composition.

>   SFArr   : (fn : a -> b) -> SF r t a b
>   SFMap   : (sf : SF r t a b) -> (b -> c) -> SF r t a c
>   SFAp    : (sf : SF r t a (b -> c)) -> (sx : SF r t a b) -> SF r t a c

Constant signals carry only a constant. When composed they either replace the
right hand wire (if on the left) or combine with the right to give a constant
value. This prevents recomputing the value which results in overall better
performance.

>   SFConst : (val : b) -> SF r t a b

The identity signal becomes any signal it's composed with regardless of order.
It's only behaviour, to pass the value given untouched, makes it valuable to
eliminate to reduce overhead.

>   SFId    : SF r t a a

Composition of two signal function may reduce to a constant, identity, or other
suitable signal. Otherwise it threads the output of the first to the input of
the second.

>   SFComp  : (sf : SF r t b c) -> (sg : SF r t a b) -> SF r t a c

>   SFPair  : (sL : SF r t a b) -> (sR : SF r t c d) -> SF r t (a, c) (b, d)

>   SFChoice : (sL : SF r t a b) -> (sR : SF r t c d) -> SF r t (Either a c) (Either b d)

>   SFFeedback : c -> (sf : SF r t (a, c) (b, c)) -> SF r t a b

> simplifySF : SF r t a b -> SF r t a b
> simplifySF (SFMap (SFConst x) f) = SFConst (f x)
> simplifySF (SFAp (SFConst f) (SFConst x)) = SFConst (f x)
> simplifySF (SFComp (SFConst val) _) = SFConst val
> simplifySF (SFComp (SFArr f) (SFConst val)) = SFConst (f val)
> simplifySF (SFComp SFId x) = x
> simplifySF (SFComp x SFId) = x
> simplifySF (SFPair (SFConst a) (SFConst b)) = SFConst (a, b)
> simplifySF (SFPair SFId SFId) = SFId
> simplifySF (SFChoice SFId SFId) = SFId
> simplifySF (SFFeedback x SFId) = SFId
> simplifySF (SFFeedback x (SFConst val)) = SFConst (fst val)
> simplifySF x = x

> stepSF : SF r t a b -> r -> t -> a -> (Inf $ Lazy $ SF r t a b, b)
> stepSF sig reader dt input =
>   case sig of
>        SFGen sf => sf reader dt input
>        SFArr fn => (SFArr fn, fn input)
>        SFMap sf f =>
>          let (sf, b) = stepSF sf reader dt input
>           in (SFMap sf f, f b)
>        SFAp sf sx =>
>          let (sf, f) = stepSF sf reader dt input
>              (sx, x) = stepSF sx reader dt input
>           in (SFAp sf sx, f x)
>        SFConst val => (SFConst val, val)
>        SFId => (SFId, input)
>        SFComp sf sg =>
>          let (sg, b) = stepSF sg reader dt input
>              (sf, c) = stepSF sf reader dt b
>           in (SFComp sf sg, c)
>        SFPair sf sg =>
>          let (sf, a) = stepSF sf reader dt (fst input)
>              (sg, c) = stepSF sg reader dt (snd input)
>           in (SFPair sf sg, (a, c))
>        SFChoice sf sg  =>
>          case input of
>               Left x =>
>                 let (sf, b) = stepSF sf reader dt x
>                  in (SFChoice sf sg, Left b)
>               Right x =>
>                 let (sg, d) = stepSF sg reader dt x
>                  in (SFChoice sf sg, Right d)
>        SFFeedback c sf =>
>          let (sf, (b, c)) = stepSF sf reader dt (input, c)
>           in (SFFeedback c sf, b)

> ||| Produce a stream of values by evaluating the signal function over streams of
> ||| input
> streamSF : SF r t a b -> (a -> b -> a) -> b -> Stream r -> Stream t -> Stream a -> Stream b
> streamSF fn (+) b (r :: rs) (t :: ts) (a :: as) =
>   let (n, b) = stepSF (simplifySF fn) r t (a + b) in
>   b :: streamSF fn (+) b rs ts as
