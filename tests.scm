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
;; 1. tests involving no tower, just relational level
;; 2. tests involving going up one level, to another relational level
;; 3. tests involving going up two levels, testing the functional level
;; 4. tests involving going up and down


;; tests for helper relations

(test "lookupo-1"
      (run* (q) (lookupo 'a `((b a a) ,(map peano (list 3 2 1)))
			 `(,(map peano (list 3 2 1)) (3 5 6)) q))
      '(5))


(test "eval-list-scmo-1"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto peano-zero mc)
		   (eval-list-scmo
		    '(5 a 7)
		    `((a) (,(peano 1)))
		    `((,(peano 1)) (catte))
		    'id-cont
		    mc
		    out
		    q)))
      '((5 catte 7)))
(test "eval-scm-auxo-0"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto peano-zero mc)
		   (eval-scm-auxo
		    8
		    `((a) (,(peano 1)))
		    `((,(peano 1)) (catte))
		    'id-cont
		    mc
		    out
		    q)))
      '(8))

(test "eval-scm-auxo-1"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto peano-zero mc)
		   (eval-scm-auxo
		    'a
		    '((a) (1))
		    '((1) (catte))
		    'id-cont
		    mc
		    out
		    q)))
      '(catte))
(test "eval-scm-auxo-2"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto peano-zero mc)
		   (eval-scm-auxo
		    '(list 5 a 7)
		    '((list a) (2 1))
		    '((2 1) ((fsubr list) catte))
		    'id-cont
		    mc
		    out
		    q)))
      '((5 catte 7)))

(test "eval-scm-auxo-3"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto peano-zero mc)
		   (eval-scm-auxo
		    '(list (cons (quote mouse) (quote ())) a 7)
		    '((quote list cons a) (4 3 2 1))
		    '((4 3 2 1) ((fsubr quote) (fsubr list) (subr cons) catte))
		    'id-cont
		    mc
		    out
		    q)))
      '(((mouse) catte 7)))
;; car cdr set! let letrec
;; if define case cond

;; tests involving no tower

(test "runo-1"
  (run* (out) (runo 'all '(call/fresh (b) (==mk 42 b)) out))
  '((42)))
(test "runo-2"
      (run* (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) (call/fresh
				    (c) (conj (==mk 42 b) (conj (==mk 100 c) (==mk a (b c))))))) out))
      '(((42 100))))

(test "runo-3"
 (run* (a) (runo 'all '(call/fresh (b) (==mk 5 5)) a))
  '(((_.))))

(test "runo-4"
      (run* (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) (call/fresh
				    (c) (conj (==mk 42 b)
					      (conj (==mk 100 c)
						    (disj (==mk a b)
							  (==mk a (b c)))))))) out))
      '((42 (42 100))))

(test "runo-5"
      (run* (out) (runo 'all
			'(call/fresh
			  (tm3) (call/fresh
			       (tm2) (call/fresh
				    (tm1)
				    (==mk (tm2 tm3) (42 (42 tm2)))))) out))
      '(((42 42))))
#|
eval-gexp:
 rel-e: ==mk
 args: ((tm2 tm3) (42 (42 tm2)))
 s/c: (() ((())))
 env: ((tm1 tm2 tm3 ==mk conj disj call/fresh rel-abs muo muos meaning-scm meaning-mk open-scm open-mk) (#((unbound) (scope) 9527) #((unbound) (scope) 9206) #((unbound) (scope) 8905) 11 10 9 8 7 6 5 4 3 2 1))
 store: ((#((unbound) (scope) 9527) #((unbound) (scope) 9206) #((unbound) (scope) 8905) 11 10 9 8 7 6 5 4 3 2 1) ((var (())) (var ()) (var) (rel-subr ==mk) (rel-subr conj) (rel-subr disj) (rel-subr call/fresh) (rel-subr rel-abs) (rel-subr muo) (rel-subr muos) (rel-subr meaning-scm) (rel-subr meaning-mk) (rel-subr open-scm) (rel-subr open-mk)))
 cont: id-cont
 v-out: #((unbound) (scope) 8765)
|#
(test "runo-6"
      (run* (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) ((rel-abs (tm1 tm2 tm3) (==mk (tm2 tm3) (tm1 (tm1 tm2))))
			  42 b a))) out))
      '(((42 42))))
;; rel-abs, let

;;|#

;; tests involving going up one level, to another relational level
;;(call/fresh (a b c) ((muo (e s/c r st k) (meaning-mk e s/c r st k)) ge1 ge2 ..))
;; tests involving going up two levels, testing the functional level
;;(call/fresh (a b c) ((muo (e s/c r st k) ((muos (e s/c r st k) scm) ge2)) ge1)
;; tests involving going up and down

