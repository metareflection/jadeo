(define test-failed #f)
(test "eval-scmo-synth-0"
      (run 1 (arg)
	    (runo (peano 1)
		  `(fresh (a x y z)
			  (eval-scmo '(,arg 40 a)
				     (40 2)
				     ))
		  '(level: () result: (2))
		  ))
      '(list)
      )
(test "eval-scmo-synth-1"
      (run* (out)
	    (runo 'all
		  '(fresh (a x y z)
			  (eval-scmo '(list 40 a)
				     (40 2)
				     ))
		  out))
      '((level: () result: (2)))
      )
(test "meaning-scmo-2"
      (run* (out)
	    (runo 'all
		  '(fresh (a x y z)
			  (eval-scmo '(a 40 2)
				     (40 2)
				     ))
		  out))
      '())

(test "runo-reverse-1"
      (run 3 (x) (runo (peano 1)
		       `(fresh (a)
		             (==mk ,x a))
		       `(level: () result: ((cat)))
		       ))
      '((quote (cat)) ((quote cat) quote ()) ((quote cat))))
      
(test "appendo-synth"
      (run 1 (x) (runo 'all
			`(fresh (z)
				(letrec ([appendo
					  (rel-abs (l1 l2 l)
						   (conde
						    [(==mk '() l1) (==mk l2 l)]
						    [(call/fresh
						      (a) (call/fresh
							   (d) (call/fresh
								(l3) (,x
								      (==mk (a . d) l1)
								      (==mk (a . l3) l)
								      (appendo d l2 l3)))))]))])
				  (appendo '(1 2) '(3 4) '(1 2 3 4))))
			'(level: () result: ((_.)))
			))
      '(conj*)
      )

(test "five-synth-1"
      (run 1 (e1 e2) (runo 'all
			`(fresh (x)
				(let ([five
				       (rel-abs (x)
						(==mk ,e1 ,e2))])
				  (five 5)))
		        '(level: () result: ((_.)))
			))
      '((((quote _.0) (quote _.0)) (sym _.0)))
      ;;'((level: () result: (5 5 5)))
      )
(test "five-synth-2"
      (run 1 (e1 e2)
	   (symbolo e1)
	   (numbero e2)
	   (runo 'all
		 `(fresh (z)
			 (let ([five
				(rel-abs (x)
					 (==mk ,e1 ,e2))])
			   (five z)))
		 '(level: () result: (5))
		 ))
      '((x 5))
      )
(test "meaning-mko-five-synth-1"
      (run 1 (e1 e2) (runo 'all
			`(fresh (x)
				(let ([five
				       (rel-abs (x)
						(==mk ,e1 ,e2))])
				  (five 5)))
		        '(level: () result: ((_.)))
			))
      '((((quote _.0) (quote _.0)) (sym _.0))))
(test "count-synth"
      (run* (count answers)
	   (runo count
		 `(fresh (z)
			 (disj (==mk z 1)
			       (==mk z 2)))
		 answers
		 ))
      '((() (level: () result: ()))
	((()) (level: () result: (1)))
	(all (level: () result: (1 2)))
	(((())) (level: () result: (1 2)))
	((((_.0)) (level: () result: (1 2))) (=/= ((_.0 ())))))
      )
