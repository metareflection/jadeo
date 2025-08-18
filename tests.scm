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

;; tests involving going up one level, to another relational level

(test "muo-1"
      (run 1 (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) ((muo (e s/c r st k) (call/fresh (tm) (==mk tm e)))
			  42 b a))) out))
      '((level: (()) result: ((42 b a)))))
;;
(test "muo-2"
      (run 1 (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) ((muo (e s/c r st k)
					 (call/fresh (tm)
						     (==mk tm (e s/c r st k))))
				    42 b a))) out))
      '((level: (()) result: (((42 b a) (() (())) ((b a ==mk conj disj call/fresh fresh conj* conde rel-abs muo muos meaning-scm meaning-mk eval-scm eval-scmo new-scm new-mk) (((((((((((((((((((())))))))))))))))))) (((((((((((((((((()))))))))))))))))) 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) ((((((((((((((((((((())))))))))))))))))) (((((((((((((((((()))))))))))))))))) 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1) ((_.) (_. ()) (rel-subr ==mk) (rel-subr conj) (rel-subr disj) (rel-subr call/fresh) (rel-subr fresh) (rel-subr conj*) (rel-subr conde) (rel-subr rel-abs) (rel-subr muo) (rel-subr muos) (rel-subr meaning-scm) (rel-subr meaning-mk) (rel-subr eval-scm) (rel-subr eval-scmo) (rel-subr new-scm) (rel-subr new-mk))) id-cont)))))

(test "meaning-mk-1"
      (run 1 (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) ((muo (e s/c r st k)
					 (call/fresh (tm)
						     (conj (meaning-mk e s/c r st k)
							   (eval-scmo '(rei-lookup 'a r st) tm))))
				    conj (==mk 42 b) (==mk a (b (b 3)))
				    ))) out))
      '((level: (()) result: ((42 (42 3))))))


(test "meaning-mk-2"
      (run 1 (out) (runo 'all
			 '(fresh (a b)
				 ((muo (e s/c r st k)
				       (fresh (tm)
					      (meaning-mk e s/c r st k)
					      (eval-scmo '(rei-lookup 'a r st) tm)))
				  conj (==mk 42 b) (==mk a (b (b 3)))
				  )) out))
      '((level: (()) result: ((42 (42 3))))))
