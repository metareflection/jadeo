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
		(rel-abs
		 (a b)
		 (fresh (out)
			(eval-scmo a out)
			(eval-scmo b out)))]
	       [f
		(muo (e s/c r st k)
		     (fresh (e-fst e-snd e-rst)
			    ;;(== (cons e-fst (cons e-snd '())) e)
			    (==mk (e-fst e-snd) e)
			    ;;(eval-mk (eval-scm (cons 'g (cons e-snd e-rst))))
			    (meaning-mk ('== ('quote e-fst) ('quote e-snd)) s/c r st k)
			    ))])
	      (fresh
	       (c d)
	       (f c 42)
	       ))
	    out))
 '())
;;|#
#|
non-terminate:
eval-gexp:
 current-level: ()
 gexp: (== c 42)
 s/c: (() (()))
 env-ids: (d c ==mk ==q conj disj call/fresh fresh conj* conde let letrec common-let delay rel-abs muo muos meaning-scm meaning-mk eval-scm eval-scmo new-scm new-mk apply-cont-jmp apply-cont-psh add-exit-lv-conto)
 cenv-ids: (g f ==)
 cont: id-cont
 mc: ((kanren (()) ((((var (()) (())) . 42) ((var (()) ()) . c)) ((()))) ((e-rst e-snd e-fst k st r s/c e ==mk ==q conj disj call/fresh fresh conj* conde let letrec common-let delay rel-abs muo muos meaning-scm meaning-mk eval-scm eval-scmo new-scm new-mk apply-cont-jmp apply-cont-psh add-exit-lv-conto) (((((((((((((((((((((((((((((((((())))))))))))))))))))))))))))))))) (((((((((((((((((((((((((((((((()))))))))))))))))))))))))))))))) ((((((((((((((((((((((((((((((())))))))))))))))))))))))))))))) (((((((((((((((((((((((((()))))))))))))))))))))))))) ((((((((((((((((((((((((((())))))))))))))))))))))))))) (((((((((((((((((((((((((((()))))))))))))))))))))))))))) ((((((((((((((((((((((((((((())))))))))))))))))))))))))))) (((((((((((((((((((((((((((((()))))))))))))))))))))))))))))) 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) ((((((((((((((((((((((((((((((((((())))))))))))))))))))))))))))))))) (((((((((((((((((((((((((((((((()))))))))))))))))))))))))))))))) ((((((((((((((((((((((((((((((())))))))))))))))))))))))))))))) (((((((((((((((((((((((((()))))))))))))))))))))))))) ((((((((((((((((((((((((((())))))))))))))))))))))))))) (((((((((((((((((((((((((((()))))))))))))))))))))))))))) ((((((((((((((((((((((((((((())))))))))))))))))))))))))))) (((((((((((((((((((((((((((((()))))))))))))))))))))))))))))) 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1) ((var (()) ((()))) (var (()) (())) (var (()) ()) id-cont ((((((((((((((((((((((((((((())))))))))))))))))))))))))) (((((((((((((((((((((((((()))))))))))))))))))))))))) 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1) (((rei . var) () (())) ((rei . var) () ()) (rel-subr ==mk) (rel-fsubr ==q) (goal-comb conj) (goal-comb disj) (goal-comb call/fresh) (goal-comb fresh) (goal-comb conj*) (goal-comb conde) (goal-comb let) (goal-comb letrec) (goal-comb common-let) (goal-comb delay) (app-gen rel-abs) (app-gen muo) (app-gen muos) (rel-subr meaning-scm) (rel-subr meaning-mk) (rel-subr eval-scm) (rel-subr eval-scmo) (rel-subr new-scm) (rel-subr new-mk) (rel-subr apply-cont-jmp) (rel-subr apply-cont-psh) (rel-subr add-exit-lv-conto))) ((d c ==mk ==q conj disj call/fresh fresh conj* conde let letrec common-let delay rel-abs muo muos meaning-scm meaning-mk eval-scm eval-scmo new-scm new-mk apply-cont-jmp apply-cont-psh add-exit-lv-conto) (((((((((((((((((((((((((((())))))))))))))))))))))))))) (((((((((((((((((((((((((()))))))))))))))))))))))))) 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) (() (())) (c 42) (rel-subr ==mk) (rel-fsubr ==q) (goal-comb conj) (goal-comb disj) (goal-comb call/fresh) (goal-comb fresh) (goal-comb conj*) (goal-comb conde) (goal-comb let) (goal-comb letrec) (goal-comb common-let) (goal-comb delay) (app-gen rel-abs) (app-gen muo) (app-gen muos) (rel-subr meaning-scm) (rel-subr meaning-mk) (rel-subr eval-scm) (rel-subr eval-scmo) (rel-subr new-scm) (rel-subr new-mk) (rel-subr apply-cont-jmp) (rel-subr apply-cont-psh) (rel-subr add-exit-lv-conto))) (bind-rec-k (() (meaning-mk ((quote ==) e-fst e-snd) s/c r st k) ((e-rst e-snd e-fst k st r s/c e ==mk ==q conj disj call/fresh fresh conj* conde let letrec common-let delay rel-abs muo muos meaning-scm meaning-mk eval-scm eval-scmo new-scm new-mk apply-cont-jmp apply-cont-psh add-exit-lv-conto) (((((((((((((((((((((((((((((((((())))))))))))))))))))))))))))))))) (((((((((((((((((((((((((((((((()))))))))))))))))))))))))))))))) ((((((((((((((((((((((((((((((())))))))))))))))))))))))))))))) (((((((((((((((((((((((((()))))))))))))))))))))))))) ((((((((((((((((((((((((((())))))))))))))))))))))))))) (((((((((((((((((((((((((((()))))))))))))))))))))))))))) ((((((((((((((((((((((((((((())))))))))))))))))))))))))))) (((((((((((((((((((((((((((((()))))))))))))))))))))))))))))) 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) ((g f ==) ((()) ((())) (((()))))) #((unbound) (scope) 1)) id-cont)) next-meta-cont ((())))
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
terminate:
eval-gexp:
 current-level: ()
 gexp: (== c 42)
 s/c: (() (()))
 env-ids: (d c ==mk ==q conj disj call/fresh fresh conj* conde let letrec common-let delay rel-abs muo muos meaning-scm meaning-mk eval-scm eval-scmo new-scm new-mk apply-cont-jmp apply-cont-psh add-exit-lv-conto)
 cenv-ids: (g f ==)
 cont: id-cont
 mc: (next-meta-cont (()))
 rel-val: #((unbound) (scope) 4007)
 out: #((unbound) (scope) 2)
 v-out: #((unbound) (scope) 1)

 rel-val: #((unbound) (scope) 158782)
 out: #((unbound) (scope) 8410)
 v-out: #((unbound) (scope) 158764)
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
