;;;; Common Declaration

;;; Variable
(: name Type value)

;;; Function
(: (f x y)
  (+ x y))
(: ((f Int) (x Int) (y Int))
  (+ x y))
(: ((f Int) (x Int) ...)
  (+ x ...))

;;; Type
; Type singleton.
(: Bit0)
(: Bit1)
(: (MyType) Option1 Option2)
; Type structure.
(: (MyType (member1 Type) (member2 Type)))

;;; Parsing
(: ((parse_ascii_bit Bit) "0") 0)
(: ((parse_ascii_bit Bit) "1") 1)

;;; Macro
(: ((f ...) lhs rhs)
  (+ lhs rhs))


; Type singleton.
(: (True))
(: (MyType) Option1 Option2)
; Type structure.
(: (MyType (member1 Type) (member2 Type)))

; Untyped function.
(: (f x)
  (+ x x))

(: ((mixin . protobufname) mixin1 mixin2)
  (: .x Int 5)
  (: .y (?? .z 6))
)

(: ((fib Nat) (0 Nat)) 1)
(: ((fib Nat) (1 Nat)) 1)
(: ((fib Nat) (x Nat))
  (+ (fib (- x 1)) (fib (- x 2))))

; todo:
;  list arg
;  macro
;  parsing
;  output
