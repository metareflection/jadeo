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


;; tests for helper relations
(test "lookupo-1"
      (run* (q) (lookupo 'a `((b a a) ,(map peano (list 3 2 1)))
			 `(,(map peano (list 3 2 1)) (3 5 6)) q))
      '(5))


(test "eval-list-scmo-1"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto (peano 1) mc)
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
		   (gen-meta-conto (peano 1) mc)
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
		   (gen-meta-conto (peano 1) mc)
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
		   (gen-meta-conto (peano 1) mc)
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
		   (gen-meta-conto (peano 1) mc)
		   (eval-scm-auxo
		    '(list (cons (quote mouse) (quote ())) a 7)
		    '((quote list cons a) (4 3 2 1))
		    '((4 3 2 1) ((fsubr quote) (fsubr list) (subr cons) catte))
		    'id-cont
		    mc
		    out
		    q)))
      '(((mouse) catte 7)))
(test "eval-scm-auxo-4"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto (peano 1) mc)
		   (eval-scm-auxo
		    '(let ((e2 (list 42 24 e1)))
		       ((lambda (a) (list a e2))
			99))
		    '((e1 let lambda quote list a) (6 5 4 3 2 1))
		    '((6 5 4 3 2 1)
		      ((99 88 777) (fsubr let) (fsubr lambda)
		       (fsubr quote) (fsubr list) catte))
		    'id-cont
		    mc
		    out
		    q)))
      '((99 (42 24 (99 88 777)))))
(test "eval-scm-auxo-5"
      (run* (q)
	    (fresh (mc out)
		   (gen-meta-conto (peano 1) mc)
		   (eval-scm-auxo
		    '(letrec ([length-peano
			       (lambda (lst)
				 (if (null? lst)
				     '()
				     (cons (length-peano (cdr lst)) '())))])
		       (list (length-peano (list 1 2 8 9))
			     (length-peano (list 4 5 1 2 3 10 9 8))
			     (length-peano (list 4))
			     (length-peano '())))
	            '((cons cdr null? letrec if lambda quote list a) (9 8 7 6 5 4 3 2 1))
		    '((9 8 7 6 5 4 3 2 1)
		      ((subr cons)
		       (subr cdr)
		       (subr null?)
		       (fsubr letrec)
		       (fsubr if) (fsubr lambda)
		       (fsubr quote) (fsubr list) catte))
		    'id-cont
		    mc
		    out
		    q)))
      `(,(map peano (list 4 8 1 0))))

(test "conj*-expando-1"
      (run* (out) (conj*-expando
		   '((meaning-mk e s/c r st k)
		     (eval-scmo '(rei-lookup 'a r st) tm))
		   out))
      '((conj (meaning-mk e s/c r st k) (eval-scmo (quote (rei-lookup (quote a) r st)) tm))))
(test "fresh-expando-1"
      (run* (out) (fresh-expando
		   '(tm)
		   '((meaning-mk e s/c r st k)
		     (eval-scmo '(rei-lookup 'a r st) tm))
		   out))
      '((call/fresh (tm) (conj* (meaning-mk e s/c r st k) (eval-scmo (quote (rei-lookup (quote a) r st)) tm)))))
(test "fresh-expando-2"
      (run* (out) (fresh-expando
		   '(a b)
		   '(((muo (e s/c r st k)
			  (fresh (tm)
				 (meaning-mk e s/c r st k)
				 (eval-scmo '(rei-lookup 'a r st) tm)))
		     conj (==mk 42 b) (==mk a (b (b 3)))))
		   out))
      '((call/fresh (a) (call/fresh (b) (conj* ((muo (e s/c r st k) (fresh (tm) (meaning-mk e s/c r st k) (eval-scmo (quote (rei-lookup (quote a) r st)) tm))) conj (==mk 42 b) (==mk a (b (b 3)))))))))

;; tests involving no tower

(test "runo-1"
  (run* (out) (runo 'all '(call/fresh (b) (==mk 42 b)) out))
  '((level: () result: (42))))
(test "runo-2"
      (run* (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) (call/fresh
				    (c) (conj (==mk 42 b) (conj (==mk 100 c) (==mk a (b c))))))) out))
      '((level: () result: ((42 100)))))

(test "runo-3"
 (run* (a) (runo 'all '(call/fresh (b) (==mk 5 5)) a))
  '((level: () result: ((_.)))))

(test "runo-4"
      (run* (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) (call/fresh
				    (c) (conj (==mk 42 b)
					      (conj (==mk 100 c)
						    (disj (==mk a b)
							  (==mk a (b c)))))))) out))
      '((level: () result: (42 (42 100)))))

(test "runo-5"
      (run* (out) (runo 'all
			'(call/fresh
			  (tm3) (call/fresh
			       (tm2) (call/fresh
				    (tm1)
				    (==mk (tm2 tm3) (42 (42 tm2)))))) out))
      '((level: () result: ((42 42)))))

(test "runo-6"
      (run* (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) ((rel-abs (tm1 tm2 tm3) (==mk (tm2 tm3) (tm1 (tm1 tm2))))
			  42 b a))) out))
      '((level: () result: ((42 42)))))

(test "fresh-1"
  (run* (out) (runo 'all '(fresh (b) (==mk 42 b)) out))
  '((level: () result: (42))))
(test "fresh-2"
      (run* (out) (runo 'all
			'(fresh (a b c)
				(==mk 42 b)
				(==mk 100 c)
				(==mk a (b c))) out))
      '((level: () result: ((42 100)))))

(test "fresh-3"
 (run* (a) (runo 'all '(fresh (b) (==mk 5 5)) a))
  '((level: () result: ((_.)))))

(test "fresh-4"
      (run* (out) (runo 'all
			'(fresh (a b c)
				(==mk 42 b)
				(==mk 100 c)
				(conde
				 [(==mk a b)]
				 [(==mk a (b c))])) out))
      '((level: () result: (42 (42 100)))))

(test "fresh-5"
      (run* (out) (runo 'all
			'(fresh (tm3 tm2 tm1)
				(==mk (tm2 tm3) (42 (42 tm2)))) out))
      '((level: () result: ((42 42)))))
(test "let-1"
      (run* (out) (runo 'all
			'(fresh (tm3 tm2 tm1)
				(let ((tm4 tm3))
				(==mk (tm2 tm4) (42 (42 tm2))))) out))
      '((level: () result: ((42 42)))))
(test "let-2"
      (run* (out) (runo 'all
			'(fresh (tm3 tm2 tm1)
				(let ((ge
				       (==mk (tm2 tm3) (42 (42 tm2)))
				       ))
				  ge)) out))
      '((level: () result: ((42 42)))))
(test "let-2"
      (run* (out) (runo 'all
			'(fresh (tm3 tm2 tm1)
				(let ((ge
				       (==mk (tm2 tm3) (42 (42 tm2)))
				       ))
				  ge)) out))
      '((level: () result: ((42 42)))))
;; tests involving going up one level, to another relational level

(test "muo-1"
      (run 1 (out) (runo 'all
			 '(fresh (a b)
				 ((muo (e s/c r st k)
				       (fresh (tm) (==mk tm e)))
				  42 b a)) out))
      '((level: (()) result: ((42 b a)))))
(test "muo-1a"
      (run 1 (out) (runo 'all
			 '(fresh (a b)
				 ((muo (e s/c r st k)
				       (fresh (tm) (==mk tm s/c)))
				  42 b a)) out))
      '((level: (()) result: ((() (()))))))
;;

(test "muo-2"
      (run 1 (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) ((muo (e s/c r st k)
					 (call/fresh (tm)
						     (==mk tm (e s/c r st k))))
				    42 b a))) out))
      '((level: (()) result: (((42 b a) (() (())) ((b a ==mk conj disj call/fresh fresh conj* conde rel-abs muo muos meaning-scm meaning-mk eval-scm eval-scmo new-scm new-mk apply-cont-jmp apply-cont-psh add-exit-lv-conto) ((((((((((((((((((((((()))))))))))))))))))))) ((((((((((((((((((((())))))))))))))))))))) 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) (((((((((((((((((((((((()))))))))))))))))))))) ((((((((((((((((((((())))))))))))))))))))) 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1) ((_.) (_. ()) (rel-subr ==mk) (goal-comb conj) (goal-comb disj) (goal-comb call/fresh) (goal-comb fresh) (goal-comb conj*) (goal-comb conde) (app-gen rel-abs) (app-gen muo) (app-gen muos) (rel-subr meaning-scm) (rel-subr meaning-mk) (rel-subr eval-scm) (rel-subr eval-scmo) (rel-subr new-scm) (rel-subr new-mk) (rel-subr apply-cont-jmp) (rel-subr apply-cont-psh) (rel-subr add-exit-lv-conto))) id-cont)))))

(test "muo-3"
      (run 1 (out) (runo 'all
			 '(fresh (a)
				 ((muo (e s/c r st k)
				       (fresh (b) ((muos (e1 s/c1 r1 st1 k1)
							 (list 'env: r1 'store: st1))
						   1 2 3 4)))
				  a b c d))
			 out))
      '((level: ((())) result: (env: ((b k st r s/c e ==mk conj disj call/fresh fresh conj* conde rel-abs muo muos meaning-scm meaning-mk eval-scm eval-scmo new-scm new-mk apply-cont-jmp apply-cont-psh add-exit-lv-conto) ((((((((((((((((((((((((((()))))))))))))))))))))))))) ((((((((((((((((((((())))))))))))))))))))) (((((((((((((((((((((()))))))))))))))))))))) ((((((((((((((((((((((())))))))))))))))))))))) (((((((((((((((((((((((()))))))))))))))))))))))) ((((((((((((((((((((((((())))))))))))))))))))))))) 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) store: (((((((((((((((((((((((((((()))))))))))))))))))))))))) ((((((((((((((((((((())))))))))))))))))))) (((((((((((((((((((((()))))))))))))))))))))) ((((((((((((((((((((((())))))))))))))))))))))) (((((((((((((((((((((((()))))))))))))))))))))))) ((((((((((((((((((((((((())))))))))))))))))))))))) 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1) ((var (()) ()) id-cont ((((((((((((((((((((((())))))))))))))))))))) 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1) ((var () ()) (rel-subr ==mk) (goal-comb conj) (goal-comb disj) (goal-comb call/fresh) (goal-comb fresh) (goal-comb conj*) (goal-comb conde) (app-gen rel-abs) (app-gen muo) (app-gen muos) (rel-subr meaning-scm) (rel-subr meaning-mk) (rel-subr eval-scm) (rel-subr eval-scmo) (rel-subr new-scm) (rel-subr new-mk) (rel-subr apply-cont-jmp) (rel-subr apply-cont-psh) (rel-subr add-exit-lv-conto))) ((a ==mk conj disj call/fresh fresh conj* conde rel-abs muo muos meaning-scm meaning-mk eval-scm eval-scmo new-scm new-mk apply-cont-jmp apply-cont-psh add-exit-lv-conto) (((((((((((((((((((((())))))))))))))))))))) 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) (() ()) (a b c d) (rel-subr ==mk) (goal-comb conj) (goal-comb disj) (goal-comb call/fresh) (goal-comb fresh) (goal-comb conj*) (goal-comb conde) (app-gen rel-abs) (app-gen muo) (app-gen muos) (rel-subr meaning-scm) (rel-subr meaning-mk) (rel-subr eval-scm) (rel-subr eval-scmo) (rel-subr new-scm) (rel-subr new-mk) (rel-subr apply-cont-jmp) (rel-subr apply-cont-psh) (rel-subr add-exit-lv-conto)))))))


(test "muo-4"
      (run 1 (out) (runo 'all
			 '(fresh (a)
				 ((muo (e s/c r st k)
				       (fresh (b) ((muos (e1 s/c1 r1 st1 k1)
							 (let ((e2 (list 42 24 e1)))
							   ((lambda (a) (list a e2))
							    99)))
						   1 2 3 4)))
				  a b c d))
			 out))
      '((level: ((())) result: (99 (42 24 (1 2 3 4))))))
(test "muo-5"
      (run 1 (out) (runo 'all
			 '(fresh (a)
				 ((muo (e s/c r st k)
				       (fresh (b) ((muos (e1 s/c1 r1 st1 k1)
							 (let ((e2 (list 42 24
									 (cons (car (cdr e1))
									       (cdr (cdr (cdr e1)))))))
							   ((lambda (a) (list a e2))
							    99)))
						   1 2222 3 4)))
				  a b c d))
			 out))
      '((level: ((())) result: (99 (42 24 (2222 4))))))

(test "meaning-mk-1"
      (run 1 (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) ((muo (e s/c r st k)
					 (meaning-mk e s/c r st k))
				    conj (==mk 42 b) (==mk a (b (b 3)))
				    ))) out))
      '((level: () result: ((42 (42 3))))))

(test "meaning-mk-2"
      (run 1 (out) (runo 'all
			 '(fresh (a b)
				 ((muo (e s/c r st k)
				       (fresh (tm k^)
					      (add-exit-lv-conto k k^)
					      (meaning-mk e s/c r st k^)
					      (eval-scmo '(rei-lookup 'a r st) tm)))
				  conj (==mk 42 b) (==mk a (b (b 3)))
				  )) out))
      '((level: (()) result: ((42 (42 3))))))


(test "meaning-mk-3"
      (run 1 (out) (runo 'all
			 '(fresh (a b c d)
				 ((muo (e s/c r st k)
				       (fresh (tm)
					      (==mk tm e)
					      (meaning-mk tm s/c r st k)
					      ))
				  conj (==mk 42 d) (==mk c (d (d 3)))
				  )
				 (==mk (d b) c)
				 (==mk a (c b))
				 ) out))
      '((level: () result: (((42 (42 3)) (42 3))))))

(test "meaning-mk-4"
      (run 1 (out) (runo 'all
			 '(fresh (a b c d e)
				 (==mk e (b b 42 (b (c 29))))
				 ((muo (e s/c r st k) (meaning-mk e s/c r st k))
				  ==mk c 42)
				 (conde
				  [(==mk d c)
				   ((muo (e s/c r st k) (meaning-mk e s/c r st k))
				    ==mk (b b) ((d 23) b))]
				  [(==mk d b)
				   ((muo (e s/c r st k) (meaning-mk e s/c r st k))
				    ==mk (d d) ((42 24) d))])
				 ((muo (e s/c r st k) (meaning-mk e s/c r st k))
				  ==mk a (e e))
				 )
			 out))
      '((level: () result: ((((42 23) (42 23) 42 ((42 23) (42 29)))
			     ((42 23) (42 23) 42 ((42 23) (42 29))))
			    (((42 24) (42 24) 42 ((42 24) (42 29)))
			     ((42 24) (42 24) 42 ((42 24) (42 29))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
STEP 0:
(s/c is (() . ()) = (())
     env and store only has built in relations

     level 0 currently)

(fresh (a b)
       ((muo (e s/c r st k)
	     (fresh (tm)
		    (meaning-mk e s/c r st k)
		    (eval-scmo '(rei-lookup 'a r st) tm)))
	conj (==mk 42 b) (==mk a (b (b 3)))
	))
STEP 1:
(s/c now is to (() . ((()))),
     env now stores symbols a and b with their addresses
     store map addresses to (var () ()) and (var () (()))
     cont is id-cont

     at level 0
)
 ((muo (e s/c r st k)
	     (fresh (tm)
		    (meaning-mk e s/c r st k)
		    (eval-scmo '(rei-lookup 'a r st) tm)))
  conj (==mk 42 b) (==mk a (b (b 3)))
  ))

STEP 1.5:
still level 0
get "muo-reifier" from "muo"
(muo (e s/c r st k)
	     (fresh (tm)
		    (meaning-mk e s/c r st k)
		    (eval-scmo '(rei-lookup 'a r st) tm)))

to

(muo-reifier (e s/c r st k)
	     (fresh (tm)
		    (meaning-mk e s/c r st k)
		    (eval-scmo '(rei-lookup 'a r st) tm)))
STEP 2:

we apply muo-reifier  to  the argument (quoted expression)
(conj (==mk 42 b) (==mk a (b (b 3))))

then we get to level 1, evaluating expression:
(fresh (tm)
  (meaning-mk e s/c r st k)
  (eval-scmo '(rei-lookup 'a r st) tm))

s/c at level 1: a default s/c with counter being 0
env at level 1: default mk env plus reified e, reified s/c reified r, reified st, reified k


cont for rel: stream of s/c -> meta-continuation -> (stream of s/c * store)
cont for func: val (any val that can be returned from scheme exp) -> meta-cont -> val/store

(fresh (a b)
   ((muo (e s/c r st k) (meaning e s/c r st k)) ==mk a b)
   (==mk a 5))

k supplied to meaning is

;;;;;;;;;;;;;;;
example where k is passed across multiple levels
- showing tower with relation

wherer to put logic vars:

unquote goal expression to runo

most part not quoted?

minikanren var representing partially unknown
synthesis


repl?


---

tracers for human readable traces

---

steps
- more examples
  -- justify why there are levels, reified cont etc.
  -- translating interesting examples from Blond to jadeo
  -- mutation to store, showing use case
     --- or get rid of store, see if it's possible
|#

