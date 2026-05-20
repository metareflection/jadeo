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

(test
 "meta-unify"
 (run 1 (out)
      (runo 'all
	    '(common-let
	      ([==meta
		(muo (e s/c r st k)
		     (fresh (exp0 exp1 tm0 sub count tm1 sub^)
			    ((muo (e1 s/c1 r1 st1 k1)
				  (fresh (exp exp0 exp1)
					 (eval-scmo '(rei-lookup 'e r1 st1) exp)
					 (==mk (exp0 exp1) exp)
					 (meaning-mk ('==mk 'tm1 exp1) s/c1 r1 st1 k1)
					 )
				  ))
			    (==mk (exp0 exp1) e)
			    (meaning-mk ('==mk exp0 tm1) s/c r st k)
			    ))]
	       [set-meta-a-and-eval
		(muo (e s/c r st k)
		     (fresh (meta-a)
			    (==mk (42 43) meta-a)
			    (meaning-mk e s/c r st k)))])
	      (fresh (a b)
		     (set-meta-a-and-eval ==mk (b b) a)
		     (==meta b (meta-a meta-a))))
	    out))
 '((level: () result: ((((42 43) (42 43)) ((42 43) (42 43)))))))

(test
 "multi-meta-unify"
 (run 1 (out)
      (runo 'all
	    '(common-let
	      ([== 
		(muo (e s/c r st k)
		     (fresh (a b out0 out1)
			    (==mk (a b) e)
			    (meaning-scmo a r st 'exit-level-k out0)
			    (meaning-scmo b r st 'exit-level-k out1)
			    (meaning-mk ('==mk ('quote out0) ('quote out1)) s/c r st k)
			    ))]
	       [==meta
		(muo (e s/c r st k)
		     (fresh (exp0 exp1 tm0 sub count tm1 sub^)
			    ((muo (e1 s/c1 r1 st1 k1)
				  (fresh (exp exp0 exp1)
					 (eval-scmo '(rei-lookup 'e r1 st1) exp)
					 (==mk (exp0 exp1) exp)
					 (meaning-mk ('==mk 'tm1 exp1) s/c1 r1 st1 k1)
					 )
				  ))
			    (==mk (exp0 exp1) e)
			    (meaning-mk ('==mk exp0 tm1) s/c r st k)
			    ))]
	       [eval 
		(muo (e s/c r st k)
		     (fresh (e-fst out out-var)
			    (== (cons e-fst '()) e)
			    (meaning-scmo e-fst r st 'exit-level-k out-var)
			    (rei-substo out-var s/c out)
			    (meaning-mk out s/c r st k)
			    ))]
	       ;; (==lv e1 ... en) unify en till e1 from different levels and updates current level substitution
	       [==lv
		(muo (e s/c r st k)
		     (fresh (e-fst e-snd)
			    (conde
			     [(==mk (e-fst e-snd) e)
			      (meaning-mk ('==meta e-fst e-snd) s/c r st k)]
			     [(fresh (e-rst e^)
				     (== (cons e-fst (cons e-snd e-rst)) e)
				     (eval (cons '==lv (cons e-snd e-rst)))
				     (meaning-mk ('==meta e-fst e-snd) s/c r st k)
				     )])
			    ))]
	       [set-meta-and-eval
		(muo (e s/c r st k)
		     (fresh (meta-a meta-b meta-c)
			    ((muo (e s/c r st k)
				 (fresh (mma mmb)
					(==mk (42 43) mma)
					(==mk (24 42) mmb)
					(meaning-mk e s/c r st k)))
			     ==mk meta-b 42)
			    (meaning-mk e s/c r st k)))])
	      (fresh (a b)
		     (set-meta-and-eval ==mk (b b) a)
		     (==lv b (meta-c (meta-a meta-b)) (mma mmb))))
	    out))
 '((level: () result: ((((42 43) (24 42)) ((42 43) (24 42)))))))

