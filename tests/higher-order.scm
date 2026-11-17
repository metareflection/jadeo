(define test-failed #f)


(test
 "mapo"
  (run 1 (out)
      (runo 'all
	    '(common-let
	      ([map1o
		(rel-abs (rel lst lst-out)
			 (fresh (fst rst fst-out rst-out)
				(conde
				 [(==mk '() lst)
				  (==mk '() lst-out)]
				 ;; somehow keep passing same arg to map1o
				 [(== (cons fst rst) lst)
				  ;; somehow lst-out is var from level (())
				  ;; rst: var1-3, rst-out: var1-5
				  #|
 s/c: ((((var () (((())))) (var () (())) (var () (()))) ((var () ()) (var () (((())))) var () ((((()))))) ((var () ((()))) 2 3 4) ((var () (())) . 1)) ((((())))))
|#
				  (== (cons fst-out rst-out) lst-out)
				  (rel fst fst-out)
				  (map1o rel rst rst-out)])
				))]
	       [double
		(rel-abs (one two)
			 (==mk (one one) two)
			 )]
	       [== 
		(muo (e s/c r st k)
		     (fresh (a b out0 out1)
			    (==mk (a b) e)
			    (meaning-scmo a r st 'exit-level-k out0)
			    (meaning-scmo b r st 'exit-level-k out1)
			    (meaning-mk ('==mk ('quote out0) ('quote out1)) s/c r st k)
			    ))])
	      (fresh
	       (doubled)
	       (map1o double '(1 2 3 4) doubled)
	       ))
	    out
	    ))
  '((level: () result: (((1 1) (2 2) (3 3) (4 4))))))



(test
 "vari-mapo"
 (run 1 (out)
      (runo (peano 4)
	    '(common-let
	      ([map1o
		(rel-abs (rel lst lst-out)
			 (fresh (fst rst fst-out rst-out)
				(conde
				 [(==mk '() lst)
				  (==mk '() lst-out)]
				 [(== (cons fst rst) lst)
		        	  (== (cons fst-out rst-out) lst-out)
				  (rel fst fst-out)
				  (map1o rel rst rst-out)])
				))]
	       [all-nils
		(rel-abs (lsts)
			 (fresh (fst rst)
				(conde
				 [(==mk '() lsts)]
				 [(== (cons fst rst) lsts)
				  (==mk '() fst)
				  (all-nils rst)])
				))]
	       [map-auxo
		(rel-abs (rel lsts lst-out)
			 (conde
			  [(all-nils lsts)
			   (==mk lst-out '())]
			  [(map1o caro lsts fsts)
			   (map1o cdro lsts rsts)
			   (eval (cons 'rel (cons fst-out fsts)))
			   (== (cons fst-out rst-out) lst-out)
			   (map-auxo rel rsts rst-out)])
			 )]
	       [mapo
		(muo (e s/c r st k)
		     (fresh (lst-out rel lsts)
			    (== (cons rel (cons lsts lst-out)) e)
			    (meaning-mk ('map-auxo lsts lst-out) s/c r st k)
			    ))]
	       [zip
		(rel-abs (zipped ele1 ele2)
			 (==mk (ele1 ele2) zipped)
			 )]
	       [== 
		(muo (e s/c r st k)
		     (fresh (a b out0 out1)
			    (==mk (a b) e)
			    (meaning-scmo a r st 'exit-level-k out0)
			    (meaning-scmo b r st 'exit-level-k out1)
			    (meaning-mk ('==mk ('quote out0) ('quote out1)) s/c r st k)
			    ))])
	      (fresh (something)
		     (map-auxo zip something '((1 2) (3 4)))
		     ))
	    out))
 'result)
