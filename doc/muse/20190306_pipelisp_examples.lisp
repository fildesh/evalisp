;; MAIN DEFS:
(deftype bool yes nil)

(def (or (a yes) (b yes)) (yes))
(def (or (a yes) (b nil)) (yes))
(def (or (a nil) (b yes)) (yes))
(def (or (a nil) (b nil)) (nil))

(def (and (a yes) (b yes)) (yes))
(def (and (a yes) (b nil)) (nil))
(def (and (a nil) (b yes)) (nil))
(def (and (a nil) (b nil)) (nil))

(def (impl (a yes) (b yes)) (yes))
(def (impl (a yes) (b nil)) (nil))
(def (impl (a nil) (b yes)) (yes))
(def (impl (a nil) (b nil)) (yes))

(def (eql (a yes) (b yes)) (yes))
(def (eql (a yes) (b nil)) (nil))
(def (eql (a nil) (b yes)) (nil))
(def (eql (a nil) (b nil)) (yes))

(def (not (a nil)) (yes))
(def (not (a yes)) (nil))

(def (if (a nil) b c) c)
(def (if (a yes) b c) b)

(def (eql (a cons) (b nil )) (nil))
(def (eql (a nil ) (b cons)) (nil))
(def (eql (a cons) (b cons))
  (and (eql (car a) (car b))
       (eql (cdr a) (cdr b))))

(def (cat (a nil ) (b list)) b)
(def (cat (a cons) (b list))
  (cons (car a)
        (cat (cdr a) b)))

(def (list a) (cons a (nil)))

(def (rev (L nil)) (nil))
(def (rev (L cons))
  (cat (rev (cdr L))
       (list (car L))))

(def (map (f func) (L nil)) (nil))
(def (map (f func) (L cons))
  (cons (f (car L))
           (map f (cdr L))))

(def (consif (pred func) e L)
  (if (pred e) (cons e L) L))

(def (filter (f func) (L nil)) (nil))
(def (filter (f func) (L cons)) (consif f (car L) (filter f (cdr L))))

(deftype (set (elements list)))
(deftype int zero nonzero-int)

(def (+ (a zero) (b zero)) a)
(def (+ (a zero) (b nonzero-int)) b)
(def (+ (a nonzero-int) (b zero)) a)

(def (- (a zero)) a)

(def (zero (a zero)) (yes))
(def (zero (a nonzero-int)) (nil))

(def (- (a int) (b int))
  (+ a (- b)))
(def (eql (a int) (b int))
  (zero (- a b)))

;; TEST CASES

(assert_eql (yes)
            (or (nil) (yes)))

(assert_eql (cons (yes) (nil))
            (list (yes)))

(assert_eql (nil)
            (map list (nil)))

(assert_eql (cons (nil) (cons (yes) (list (nil))))
            (map not (cons (yes) (cons (nil) (cons (yes) (nil))))))

(assert_eql (list (yes))
            (car (list (list (yes)))))

(assert_eql (cons (nil) (list (yes)))
            (rev (cons (yes) (cons (nil) (nil)))))

(assert_eql (yes)
            (in (nil) (set (cons (yes) (cons (nil) (list (yes)))))))

(assert_eql ('int -5)
            (- (+ ('int 1) ('int 1)) (+ ('int 2) ('int 5))))
