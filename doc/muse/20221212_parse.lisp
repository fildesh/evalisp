
(: ((parse_digit Nat) "0") 0)
(: ((parse_digit Nat) "1") 1)
(: ((parse_digit Nat) "2") 2)
; ...

(: ((parse_nat (, Nat Nat))
    ""
    (d Nat (parse_digit ...)))
  (, 10 mag))
(: ((parse_nat (, Nat Nat))
    ""
    (d Nat (parse_digit ...))
    (result_mag (, Nat Nat) (parse_nat ...)))
  (: (result x mag)
    (, (+ (* mag d) x)
       (* mag 10)))
  (result (... result_mag)))

; from context it's called
(: (parse_int (carry Int)
    ""
    (d Nat (parse_digit ...))
    ...)
  (parse_int (+ (* 10 carry) d) ...))
(: ((parse_int Int) (carry Int)
    ""
    (d Nat (parse_digit ...)))
  (+ (* 10 carry) d))
(: ((parse_int Int) "" ...)
  (parse_int 0 ...))


; lisp grammar?
(: ((SYMBOL Str) (building Str) "" (c SYMBOLCHAR))
  (++ building c))
(: ((SYMBOL Str) (building Str) "" (c SYMBOLCHAR) ...)
  (SYMBOL (++ building c) ...))
(: ((SYMBOL Str) "" (c SYMBOLCHAR) ...)
  (SYMBOL c ...))
