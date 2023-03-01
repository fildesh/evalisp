; - Parsing grammars
; - Transpiling macros
; - Configuration with mixins (Python)
; - Side effect freedom
; - Module system (Python)
; - Explicit polymorphism
; - Code is data (dictionary)
; - No null

(: name value)
(: name Type value)
(: (MyType (member1 Type) (member2 Type)))
(: (MyType) Option1 Option2)
(: (my_func (arg1 Type) (arg2 Type))
  (+ arg1 arg2))
(: ((my_func ResultType) (arg1 Type) (arg2 Type))
  (+ arg1 arg2))

(: name Type (: swag help) (+ swag 5))
(: (f x (y ..)
  (.. y))
(.. lol)

; how to decide what function to call? or whether it's too ambiguous and there should be an error?
:: how to import
:: scope resolution
:: change scope

:. function

, tuple
.. rest type
.. expand in output

"" string

(. (:. whatever) (do stuff))

; dynamic scope variables start with dot .
. for named parameters

(: ((MyObject . protobuf::myproto)
    mixin1 mixin2 mixin3)
  (: .swaggy.baggy ?? "mydefault"))
  (: .qos (by (. prod "tryhard") (. dev "besteffort")))
  (: .continent.NA 500)
  (: .continent.AP 5)
)

(: ((parseme Int) ""))

; Can we require rules to have literals at the start so parsing is faster?