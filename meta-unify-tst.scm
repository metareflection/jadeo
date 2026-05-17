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

#|
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
;;|#
(test
 "variadic-arg"
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
	       [eval 
		(muo (e s/c r st k)
		     (fresh (e-fst out out-var)
			    (== (cons e-fst '()) e)
			    (meaning-scmo e-fst r st 'exit-level-k out-var)
			    ;; doesn't work, want out-var's corresponding thing in this level's s/c (g e-snd e-rst) to subst with (
			    (rei-substo out-var s/c out)
			    ;;(eval-scmo '(rei-subst out-var s/c) out)
			    ;; 8-11, 9-e^, 8isout1
			    ;; meaning-scmo e-fst is working and gives e^'s var, but after uni with out-var
			    ;; out-var stores e^'s var's sub, which is out1
			    (meaning-mk out s/c r st k)
			    ))]
	       [f
		(muo (e s/c r st k)
		     (fresh (e-fst e-snd e-rst e^)
			    (== (cons e-fst (cons e-snd e-rst)) e)
			    (eval (cons 'g (cons e-snd e-rst)))
			    (meaning-mk ('== e-fst e-snd) s/c r st k)
			    ))]
	       [g
		(muo (e s/c r st k)
		     (fresh (e-fst e-snd)
			    (== (cons e-fst (cons e-snd '())) e)
			    ;;(eval-mk (eval-scm (cons 'g (cons e-snd e-rst))))
			    (meaning-mk ('== e-fst e-snd) s/c r st k)
			    ))])
	      (fresh
	       (a b c)
	       (f (list b a) c (list (cons 42 43) (cons 44 45)))
	       ))
	    out))
 '((level: () result: (42))))
;;|#
#|

(test
 "multi-meta-unify"
 (run 1 (out)
      (runo 'all
	    '(common-let
	      ([== 
		(rel-abs
		 (a b)
		 (fresh (out)
			(eval-scmo a out)
			(eval-scmo b out)))]

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
	       ;; (==lv e1 ... en) unify e1 till en and updates current level substitution
	       ;; todo: what if meta level term contains free var
	       [==lv
		(muo (e s/c r st k)
		     (conde
		      [(==mk '() e)
		       (apply-cont-psh k '())]
		      [(fresh (exp)
			      (==mk (exp) e)
			      (apply-cont-psh k '()))]
		      [(fresh (e-fst e-snd e-rst)
			      (== (cons e-fst (cons e-snd e-rst)) e)
			      (eval-mk (eval-scm (cons '==lv (cons e-snd e-rst))))
			      (meaning-mk ('==meta e-fst e-snd) s/c r st k))]
		      ))]
	       [==lv^
		(muo (e s/c r st k)
		     (fresh (e-fst e-snd)
			    (== (cons e-fst (cons e-snd '())) e)
			    ;;(eval-mk (eval-scm (cons '==lv (cons e-snd e-rst))))
			    (meaning-mk ('==meta e-fst e-snd) s/c r st k))
		     )]

	       [set-meta-a-and-eval
		(muo (e s/c r st k)
		     (fresh (meta-a)
			    (==mk (42 43) meta-a)
			    (meaning-mk e s/c r st k)))])
	      (fresh (a b)
		     (set-meta-a-and-eval ==mk (b b) a)
		     (==lv^ b meta-a)))
	    out))
 '((level: () result: (((42 43) (42 43))))))
|#
#|
	       [set-meta-and-eval
		(muo (e s/c r st k)
		     (fresh (meta-a)
			    (==mk (42 43) meta-a)
			    (meaning-mk e s/c r st k)))])
	      (fresh (a b)
		     (set-meta-and-eval ==mk (b b) a)
		     (==meta b meta-a mm-a)))
	    out))
 '((level: () result: ((((42 43) (42 43)) ((42 43) (42 43)))))))
|#
