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
			   #|
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
			  |#
			   
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

;; should give (42 43)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
		(lambda (l1 l2)
		  (if (null? l1) l2
		      (append (cdr l1) (cons (car l1) l2)))))]
	      [==meta
	       (muo (e s/c r st k)
		    (fresh (tm0 sub count tm1 sub^)
			   ((muo (e1 s/c1 r1 st1 k1)
				 (eval-scm
				  (let ([tm1 (rei-lookup
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

;; should give (42 43)
