;; All but these first 2 lines are are from eva.lsp,
;; committed on Mon Sep 24 02:02:20 2012 -0400

;; If you want to do imperative things,
;; do it in a different language or establish
;; a protocol, connect an output to an input and go for it!

; eva lisp
; I'm happy with all syntax and constructs until the END_EVA label.

; Identity
(def (I x) x)
(def (' 'I x) x)

;;; Boolean logic
(def (nil))
(def (yes))
(def bool nil yes)

(def (or (a yes) (b yes)) (yes))
(def (or (a yes) (b nil)) (yes))
(def (or (a nil) (b yes)) (yes))
(def (or (a nil) (b nil)) (nil))

(def (and (a yes) (b yes)) (yes))
(def (and (a yes) (b nil)) (nil))
(def (and (a nil) (b yes)) (nil))
(def (and (a nil) (b nil)) (nil))

(def (imp (a yes) (b yes)) (yes))
(def (imp (a yes) (b nil)) (nil))
(def (imp (a nil) (b yes)) (yes))
(def (imp (a nil) (b nil)) (yes))

(def (eql (a yes) (b yes)) (yes))
(def (eql (a yes) (b nil)) (nil))
(def (eql (a nil) (b yes)) (yes))
(def (eql (a nil) (b nil)) (nil))

(def (not (a yes)) (nil))
(def (not (a nil)) (yes))

(def (xor (a bool) (b bool))  (not (eql a b)))

;;; List stuff
(def (cons car (cdr cons nil)))
(def list cons nil)
; Note that types are invisible except for where types are used.

(def (list ' L) L)

(def (cons a b c ' L)
  (cons a ((cons cons (cons b (cons c L))))))

(def (cat (A list)) A)
(def (cat (A nil) (B list)) B)
(def (cat (A cons) (B list))
  (cons (car A)
        (cat (cdr A) B)))
(def (cat (A list) (B list) (C list) ' D)
  (cat A (cat B ((cons cat C D)))))

(def (last (' a)) a)
(def (last (' a b ' L))
  (last (cons b L)))

(def (eql (a cons) (b nil)) (nil))
(def (eql (a nil) (b cons)) (nil))
(def (eql (a cons) (b cons))
  (and (eql (car a) (car b))
       (eql (cdr a) (cdr b))))

(def (map f (L nil)) (nil))
(def (map f (L cons))
  (cons (f (car L))
        (cdr L)))

(def (map f (L1 nil) (L2 nil) ' (M (' nil))) (nil))
(def (map f (L1 cons) (L2 cons) ' (M (' cons)))
  (cons ((cons f (car L1) (car L2) (map car M)))
        ((cons map (cdr L1) (cdr L2) (map cdr M)))))


;;; Lambda functions!

;; Lambda function example:
('example
 ((('n a b) (xor a b))
  (yes)
  (nil))
 ; Do variable substitution.
 (xor (yes) (nil))
 ; Evaluate /xor/.
 (yes))

;; Lambda macro example:
('example
 (((''n a b)
   (+ ((list 'int a)) ((list 'int b))))
  1 2)
 (+ ((list 'int ('I 1))) ((list 'int ('I 2))))
 (+ ((' 'int 1)) ((' 'int 2)))
 (+ ('int 1) ('int 2))
 ('int 3)
 )


; So let can be defined as:
(def (' 'let a b)
  (('n body)
   ((list ((list (list 'n a) body))
           b))))
; The eval parens around the lambda function are not needed to evaluate it,
; since there are more eval parens to evaluate /b/.

('example
 (('let a (nil))
  (xor a (yes)))

 (((''n body)
   ((list ((list (list 'n ('I a)) body))
           (' nil))))
  (xor a (yes)))

 ((list ((list (list 'n ('I a))
               (' xor a (yes))))
        (' nil)))

 ((list ((list (' 'n a)
               (' xor a (yes))))
        (' nil)))

 ((list ((' ('n a) (xor a (yes))))
        (' nil)))

 ((list (('n a) (xor a (yes)))
        (' nil)))
 ((' (('n a) (xor a (yes)))
   (nil)))

 (('n a) (xor a (yes))
   (nil))

 (xor (nil) (yes))

 (nil))


(def (if (a nil) b c) c)
(def (if (a yes) b c) b)

(def (' 'if a b c)
  (list (list if a
              (list ' I b)
              (list ' I c))))

('example
 (def (fib (a int))
   ('if (<= a ('int 1)) a
    (+ (fib (- a ('int 1)))
       (fib (- a ('int 2))))))

 (def (x) ('int 7))
 (def (y) ('int 7))

 (('if (= (x) (y)) (fib ('int 3)) (fib ('int 5))))
 ; Macro is called, notice args are quoted now.
 ((list (list if (' = (x) (y))
              (list ' I (' fib ('int 3)))
              (list ' I (' fib ('int 5))))))
 ; /list/ invoked, so /(' fib)/ terms are part of a bigger tree.
 ((list (list if (' = (x) (y))
              (' ' I (fib ('int 3)))
              (' ' I (fib ('int 5))))))
 ; /list/ invoked again, quoted terms lose some quotes.
 ((list (' if (= (x) (y))
         (' I (fib ('int 3)))
         (' I (fib ('int 5))))))
 ((' (if (= (x) (y))
       (' I (fib ('int 3)))
       (' I (fib ('int 5))))))
 ((if (yes)
       (' I (fib ('int 3)))
       (' I (fib ('int 5)))))
 (I (fib ('int 3)))
 (I ('int 2))
 ('int 2)
 )

; Or this
(def (fac (a int))
  ('if (= a ('int 0))
   ('int 1)
   (* a (fac (- a ('int 1))))))

(def (0))
(def (++ (-- ++ 0)))

(def nat 0 ++)

(def (-- (++ -- 0)))
(def int nat --)

(def (+ (a int) (b 0)) a)
(def (+ (a int) (b ++)) (++ (+ a (-- b))))
(def (+ (a int) (b --)) (-- (+ a (++ b))))

(def (- (a 0)) a)
(def (- (a ++)) (-- (- (-- a))))
(def (- (a --)) (++ (- (++ a))))

(def (- (a int) (b int))
  (+ a (- b)))

; END_EVA
; Stuff below here is testing.


;; TYPEDEF
(def (or (a type) ' (b (' type)))
  ((('n )))
  )
(def list ' cons)
(def list ' nil)

(def (' 'and a b)
  ((list 'if a b (nil))))




; What is the formal definition of:
; (' f a b)
; (list f a b)
; ((' f a b))
; ((list f a b))