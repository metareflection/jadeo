;; tests layout
;; 0. tests for helper relations
;; 1. tests involving no tower, just relational leve
;; 2. tests involving going up one level, to another relational level
;; 3. tests involving going up two levels, testing the functional level
;; 4. tests involving going up and down


;; tests for helper relations

(test "lookupo-1"
      (run* (q) (lookupo 'a '((b . 3) (a . 5) (a . 6)) q))
      '(5))

(test "eval-listo-1"
      (run* (q) (eval-listo '((quote mouse) a 7) '((a . catte)) q))
      '((mouse catte 7)))

(test "evalo-1"
      (run* (q) (evalo '(list (quote mouse) a 7) '((a . catte)) q))
      '((mouse catte 7)))

(test "evalo-1"
  (run* (q) (evalo '(list (cons (quote mouse) (quote ())) a 7) '((a . catte)) q))
  '(((mouse) catte 7)))

;; tests involving no tower
(jadeo-meaning answer-count vars gexp)
(run 2 (out)
     (eval-programo
      '(fresh (a b) (conj (== a b) (== b 3)))
      out))

(test "mko-1"
  (run* (out) (runo 'all '(fresh (b) (== 42 b)) out))
  '(42))

(test "mko-2"
  (run* (a) (runo 'all '(fresh (b) (== (quote cat) b)) a))
  '(cat))

(test "mko-3"
  (run* (a) (runo '() '(fresh (b) (symbolo b) (== (quote cat) b)) a))
  '(cat))

(test "mko-4"
  (run* (a) (runo '() '(fresh (b) (symbolo b)) a))
  '((_.0 (sym _.0))))

(test "mko-5"
  (run* (a) (runo '() '(fresh (b) (numbero b)) a))
  '((_.0 (num _.0))))

(test "mko-6"
  (run* (a) (runo '() '(fresh (b) (symbolo b) (numbero b)) a))
  '())

(test "mko-6a"
 (run* (a) (runo '() '(fresh (b) (== 5 5)) a))
  '(_.0))

(test "mko-6b"
 (run* (a) (runo '() '(fresh (b) (== 5 5)) 42))
  '(_.0))

(test "mko-7"
 (run* (a) (mko '(run 1 (b) (== (list 'cat 'dog) b)) a))
  '((cat dog)))

(test "mko-7b"
 (run* (a) (mko '(run 1 (b) (=/= (list 'cat 'dog) b) (== (list 'cat 'dog) b)) a))
  '())

(test "mko-7c"
 (run* (a) (mko '(run 1 (b) (== (list 'cat 'dog) b) (=/= (list 'cat 'dog) b)) a))
 '())

;; tests involving going up one level, to another relational level
(fresh (a b c) ((muo (e s/c r st k) (meaning-mk e s/c r st k)) ge1 ge2 ..))
;; tests involving going up two levels, testing the functional level
(fresh (a b c) ((muo (e s/c r st k) ((muos (e s/c r st k) scm) ge2)) ge1)
;; tests involving going up and down

