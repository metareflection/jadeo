(define test-failed #f)

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

(test "eval-scmo-==-1"
      (run* (out) (runo 'all
			'(fresh (x)
				(let ([== (rel-abs (a b)
						   (fresh (out)
							  (eval-scmo a out)
							  (eval-scmo b out)))])
		        	  (== 'x '(cons 2 3))
				  ))
			out))
      '((level: () result: ((2 . 3)))))

(test "eval-scmo-==-2"
      (run* (out) (runo 'all
			'(fresh (a x y z)
				(let ([== (rel-abs (a b)
						   (fresh (out)
							  (eval-scmo a out)
							  (eval-scmo b out)))])
		        	  (conj
				   (== '((lambda (x y) (list x y)) x z)
				       '(cons (cons 2 3) y))
				   (==mk a (x y z)))
				  ))
			out))
      '((level: () result: (((2 . 3) ((_.)) (_.))))))

(test "letrec-1"
      (run* (out) (runo (peano 3)
			'(fresh (x)
				(letrec ([fives
					  (rel-abs (x)
						   (conde
						    [(==mk x 5)]
						    [(fives x)])
						   )])
				  (fives x)))
		        out))
      '((level: () result: (5 5 5))))

(test "letrec-2"
      (run* (out) (runo (peano 8)
			'(fresh (x)
				(letrec ([fives-sixes
					  (rel-abs (x)
						   (conde
						    [(==mk x 5)]
						    [(==mk x 6)]
						    [(fives-sixes x)])
						   )])
				  (fives-sixes x)))
		        out))
      '((level: () result: (5 6 5 6 5 6 5 6))))

(test "letrec-3"
      (run* (out) (runo 'all
			'(fresh (x)
				(letrec ([appendo
					  (rel-abs (l1 l2 l)
						   (conde
						    [(==mk '() l1) (==mk l2 l)]
						    [(fresh (a d l3)
							    (==mk (a . d) l1)
							    (==mk (a . l3) l)
							    (appendo d l2 l3))]))])
				  (appendo '(1 2) '(3 4) x)))
		        out))
      '((level: () result: ((1 2 3 4)))))


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

(test "muo-2"
      (run 1 (out) (runo 'all
			'(call/fresh
			  (a) (call/fresh
			       (b) ((muo (e s/c r st k)
					 (call/fresh (tm)
						     (==mk tm (e s/c r st k))))
				    42 b a))) out))
      '((level: (()) result: (((42 b a) (() (())) ((b a ==mk ==q conj disj call/fresh fresh conj* conde let letrec common-let delay rel-abs muo muos meaning-scm meaning-scmo meaning-mk eval-scm eval-scmo new-scm new-mk rei-substo apply-cont-jmp apply-cont-psh add-exit-lv-conto) (((((((((((((((((((((((((((((())))))))))))))))))))))))))))) (((((((((((((((((((((((((((()))))))))))))))))))))))))))) 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) ((((((((((((((((((((((((((((((())))))))))))))))))))))))))))) (((((((((((((((((((((((((((()))))))))))))))))))))))))))) 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1) (((rei . var) () (())) ((rei . var) () ()) (rel-subr ==mk) (rel-fsubr ==q) (goal-comb conj) (goal-comb disj) (goal-comb call/fresh) (goal-comb fresh) (goal-comb conj*) (goal-comb conde) (goal-comb let) (goal-comb letrec) (goal-comb common-let) (goal-comb delay) (app-gen rel-abs) (app-gen muo) (app-gen muos) (rel-subr meaning-scm) (rel-subr meaning-scmo) (rel-subr meaning-mk) (rel-subr eval-scm) (rel-subr eval-scmo) (rel-subr new-scm) (rel-subr new-mk) (rel-subr rei-substo) (rel-subr apply-cont-jmp) (rel-subr apply-cont-psh) (rel-subr add-exit-lv-conto))) id-cont)))))

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

(test "common-let-0"
      (run 1 (out) (runo 'all
			 '(common-let
			   ([f
			     (rel-abs (x1 x2)
				      (==mk x1 (42 x2 x2 42)))])
			   (fresh (x1 x2 x)
				  ((muo (e s/c r st k)
					(fresh (y)
					       (f y e)))
				   xx)
				  ))
			 out))
      '((level: (()) result: ((42 (xx) (xx) 42)))))

(test "common-let-1"
      (run 1 (out) (runo 'all
			 '(common-let
			   ([appendo
			     (rel-abs (l1 l2 l)
				      (conde
				       [(==mk '() l1) (==mk l2 l)]
				       [(fresh (a d l3)
					       (==mk (a . d) l1)
					       (==mk (a . l3) l)
					       (appendo d l2 l3))]))])
			   (fresh (x1 x2 x)
				  ((muo (e s/c r st k)
					(fresh (yyy)
					       (appendo '(1 2) yyy '(1 2 42 45 47))))
				   xx)
				  ))
			 out))
      '((level: (()) result: ((42 45 47)))))
