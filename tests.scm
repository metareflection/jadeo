(load "jadeo.scm")

(define test-failed #f)

(define-syntax test
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (begin
               (set! test-failed #t)
               (printf "Failed: ~s~%Expected: ~s~%Computed: ~s~%"
                     'tested-expression expected produced))))))))
;; tests layout
;; 0. tests for helper relations
;; 1. tests involving no tower, just relational leve
;; 2. tests involving going up one level, to another relational level
;; 3. tests involving going up two levels, testing the functional level
;; 4. tests involving going up and down


;; tests for helper relations

(test "lookupo-1"
      (run* (q) (lookupo 'a '((b a a) (3 2 1)) '((3 2 1) (3 5 6)) q))
      '(5))

(test "eval-list-scmo-1"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto peano-zero mc)
		   (eval-list-scmo
		    '(5 a 7)
		    '((a) (1))
		    '((1) (catte))
		    'id-cont
		    mc
		    out
		    q)))
      '((5 catte 7)))
(test "eval-scm-auxo-1"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto peano-zero mc)
		   (eval-scm-auxo
		    (list 'list 5 'a 7)
		    '((a) (1))
		    '((1) (catte))
		    'id-cont
		    mc
		    out
		    q)))
      '((5 catte 7)))


(test "eval-scm-auxo-2"
  (run* (q) (eval-scm-auxo '(list (cons (quote mouse) (quote ())) a 7) '((a . catte)) q))
  '(((mouse) catte 7)))

;; tests involving no tower

(run 2 (out)
     (eval-programo
      '(fresh (a b) (conj (== a b) (== b 3)))
      out))

(test "runo-1"
  (run* (out) (runo 'all '(fresh (b) (== 42 b)) out))
  '(42))

(test "runo-2"
  (run* (a) (runo 'all '(fresh (b) (== (quote cat) b)) a))
  '(cat))

(test "runo-3"
  (run* (a) (runo peano-zero '(fresh (b) (symbolo b) (== (quote cat) b)) a))
  '(cat))

(test "runo-4"
  (run* (a) (runo peano-zero '(fresh (b) (symbolo b)) a))
  '((_.0 (sym _.0))))

(test "runo-5"
  (run* (a) (runo peano-zero '(fresh (b) (numbero b)) a))
  '((_.0 (num _.0))))

(test "runo-6"
  (run* (a) (runo peano-zero '(fresh (b) (symbolo b) (numbero b)) a))
  '())

(test "runo-6a"
 (run* (a) (runo peano-zero '(fresh (b) (== 5 5)) a))
  '(_.0))

(test "runo-6b"
 (run* (a) (runo peano-zero '(fresh (b) (== 5 5)) 42))
  '(_.0))

(test "runo-7"
 (run* (a) (runo peano-zero '(fresh (b) (== (list 'cat 'dog) b)) a))
  '((cat dog)))

(test "runo-7b"
 (run* (a) (runo peano-zero '(fresh (b) (=/= (list 'cat 'dog) b) (== (list 'cat 'dog) b)) a))
  '())

(test "runo-7c"
 (run* (a) (runo peano-zero '(fresh (b) (== (list 'cat 'dog) b) (=/= (list 'cat 'dog) b)) a))
 '())

;; tests involving going up one level, to another relational level
;;(fresh (a b c) ((muo (e s/c r st k) (meaning-mk e s/c r st k)) ge1 ge2 ..))
;; tests involving going up two levels, testing the functional level
;;(fresh (a b c) ((muo (e s/c r st k) ((muos (e s/c r st k) scm) ge2)) ge1)
;; tests involving going up and down

