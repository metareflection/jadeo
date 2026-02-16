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
(run 1 (out)
     (runo 'all
	   '(common-let
	     ([appendo
	       (rel-abs (l1 l2 l)
			(conde
			 [(==mk '() l1) (==mk l2 l)]
			 [(fresh (a d l3)
				 (==mk (a . d) l1)
				 (==mk (a . l3) l)
				 (appendo d l2 l3))]))]
	      [==meta
	       (muo (e s/c r st k)
		    (fresh (tm0 sub count)
			   (==mk (sub count) s/c)
			   ;;rather than unify, set env
			   ((muo (e1 s/c1 r1 st1 k1)
				 (fresh (sub1 c1)
					(eval-scmo (rei-lookup 'e r1 st1) tms-exp)
					(==mk (tm0-exp tm1-exp) tms-exp)
					(eval-scmo (rei-lookup tm1-exp r1 st1) tm1)
					(meaning-mk ('==mk 'tm1 tm1) s/c1 r1 st1 k1))
				 ))
			   
			   ((muo (e1 s/c1 r1 st1 k1)
				 (fresh (sub1 c1)
					(eval-scmo (rei-lookup 'e r1 st1) tms-exp)
					(==mk (tm0-exp tm1-exp) tms-exp)
					(eval-scmo (rei-lookup tm1-exp r1 st1) tm1)
					(meaning-mk ('==mk 'tm1 tm1) s/c1 r1 st1 k1))
				 ))
			    ((muo (e1 s/c1 r1 st1 k1)
				 (fresh (sub0 c0 sub1 c1)
					(eval-scmo (rei-lookup 's/c r1 st1) (sub0 c0))
					(==mk (sub1 c1) s/c1)
					(appendo sub0 sub1 sub^)
					(meaning-mk ('==mk 'sub^ sub^) s/c1 r1 st1 k1)
					)
				 
				 ))
			  
			   
			   ;;(rei-unifyo tm0 tm1 sub^ sub^^)
			   ;;(apply-cont-psh k sub^^ st)
			   (meaning-mk
			    ('==q (eval-scm (rei-lookup (car e) r st))
				  tm1)
			    (sub^ count) r st k)
			   ))]
	      [set-meta-a-and-eval
	       (muo (e s/c r st k)
		    (fresh (meta-a e0 e1 e2)
			   (==mk e (e0 e1 e2))
			   (==mk meta-a ((42 43) (42 43)))
			   (meaning-mk (e1 e0 e2) s/c r st k)))])
	      (fresh (a b)
		     ;; first go to meta level to set up a var
		     (set-meta-a-and-eval (a a) ==mk b)
		     (==meta b meta-a)))
	   out))

|#
;;#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;#|
(test "meaning-mk-3"
      (run 1 (out) (runo 'all
			 '(fresh (a b c d)
				 ((muo (e s/c r st k)
				       (fresh (tm tm0 tm1 tm2)
					      (==mk (tm0 tm1 tm2) e)
					      (==mk tm (tm0 tm1 tm2))
					      (meaning-mk tm s/c r st k)
					      ))
				  conj (==mk 42 d) (==mk c (d (d 3)))
				  )
				 (==mk (d b) c)
				 (==mk a (c b))
				 ) out))
      '((level: () result: (((42 (42 3)) (42 3))))))

;;|#


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
      '((level: (()) result: ((1 2 3 4)))))

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
      '((level: (()) result: ((1 2 3 4)))))

(trace-off)
(test
 "meta-unify"
 (run 1 (out)
      (runo 'all
	    '(common-let
	      ([appendo
		(rel-abs (l1 l2 l)
			 (conde
			  [(==mk '() l1) (==mk l2 l)]
			  [(fresh (a d l3)
				  (==mk (a . d) l1)
				  (==mk (a . l3) l)
				  (appendo d l2 l3))]))]
	       [append
		(eval-scm
		 '(lambda (l1 l2)
		   (if (null? l1) l2
		       (append (cdr l1) (cons (car l1) l2)))))]
	       [==meta
		(muo (e s/c r st k)
		     (fresh (tm0 sub count tm1 sub^)
			    ((muo (e1 s/c1 r1 st1 k1)
				  (eval-scm
				   '(let ([tm1 (rei-lookup
					       (car (cdr (rei-lookup 'e r1 st1)))
					       r1 st1)]
					 [sub0 (car (rei-lookup 's/c r1 st1))]
					 [sub1 (car s/c1)])
				     (let
					 ([st1^ (rei-set-st 'sub^ r1
							    (rei-set-st 'tm1 r1 st1 tm1)
							    (append sub0 sub1))])
				       (meaning-mk e1 s/c1 r1 st1^ k1)))))
			     ==mk (sub count) s/c)
			    ;; s/c is cons
			    (meaning-mk
			     ('==q (eval-scm '(rei-lookup (car e) r st))
				   tm1)
			     (sub^ count) r st k)
			    ))]
	       [set-meta-a-and-eval
		(muo (e s/c r st k)
		     (fresh (meta-a e0 e1 e2 e^)
			    (==mk e (e0 e1 e2))
			    (==mk e^ (e1 e2 e2))
			    (==mk meta-a ((42 43) (42 43)))
			    (meaning-mk e^ s/c r st k)))])
	      (fresh (a b)
		     ;; first go to meta level to set up a var
		     (set-meta-a-and-eval (a a) ==mk b)
		     (==meta b meta-a)))
	    out))
 '(1 2 3))
;;|#
;; should give (42 43)
