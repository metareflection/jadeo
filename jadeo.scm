;; evaluator for microkanren
;; goal expression * substitution-counter pair
;; * scheme env * scheme store * meta-continuation * (stream store) * stream
(define (eval-gexp-auxo gexp s/c env store cont mc out $)
  (conde
   [(fresh (rel ans)
           (symbolo gexp)         
           (lookupo gexp env store rel)
           (== (answer rel store) ans)
           (apply-rel-ko cont ans mc out))]
   [(fresh (rel args rel-val-ignore)
	   (== (rel . args) gexp)
	   (eval-gexp-auxo rel s/c env store
			  (list 'application-rel-k args s/c env cont mc $)
			  mc out rel-val-ignore))]))
(define (apply-rel-ko cont val/store mc out)
  (conde
   [(fresh (rel store)
           (== empty-k cont)
           (== val/store out)
           (== (answer rel store) val/store))]
   [(fresh (args s/c env k $)
	   (== (list 'application-rel-k args s/c env k mc $) cont)
	   (== (answer rel store) val/store)
	   (conde
	    [(== rel (list 'rel-subr rel-subr-name))
	     (apply-rel-subr rel-subr-name args s/c env store k mc out $)]
	    [(== rel (list 'rel-abs paras body))
	     (apply-rel-abs paras body args s/c env store k mc out $)]
	    [(== rel (list 'muo-reifier paras body))
	     (apply-rel-reifier paras body args s/c env store k mc out $)]))]
   [(fresh (g1-$ ge2 k)
	   (== (list 'bind-k ge2 s/c env k mc $) cont)
	   (== (answer g1-$ store) val/store)
	   (bindo g1-$ ge2 s/c env mc $)	   
	   (apply-rel-ko k (cons $ store) mc out))]
   [(fresh ($1 $2 k)
	   (== (list 'mplus-k s/c env k mc $) cont)
	   (== (answer (list $1 $2) store) val/store)
	   (mpluso $1 $2 s/c env mc $)
	   (apply-rel-ko k (cons $ store) mc out))]
   [(fresh (env k $ store gexp*-rst $*-rst)
           (== (list 'eval-list-k gexp*-rst env k $*-rst) cont)
           (== (answer $ store) val/store)
           (eval-list-gexpo gexp*-rst s/c env store
			    (list 'cons-k $ k) mc out $*-rst))]
   [(fresh ($ k $* s^^ ans)
           (== (list 'cons-k $ k) cont)
           (== (answer $* store) val/store)
           (== (answer (cons $ $*) store) ans)
           (apply-rel-ko k ans out))]
   ))

(define (apply-rel-subr rel-name args s/c env store cont mc out $)
  (conde
   [(fresh (v1 v2 sub count sub' $)
	   (== '==mk rel-name)
	   (== (list v1 v2) args)
	   (== (cons sub count) s/c)
	   (conde
            [(== #f sub') (== '() $)]
            [(=/= #f sub') (== `((,sub' . ,count)) $)])
	   (unifyo v1 v2 sub sub')
	   (apply-rel-ko cont (cons $ store) mc out)]
   [(fresh (ge1 ge2 ge1-$ ge$)
	   (== 'conj rel-name)
	   (== (list ge1 ge2) args)
	   (eval-gexp-auxo ge1 s/c env store
			   (list 'bind-k ge2 s/c env cont mc $)
			   mc out ge1-$))]
   [(fresh (ge1 ge2 ge1-$ ge2-$ ge$)
	   (== 'disj rel-name)
	   (== (list ge1 ge2) args)
	   (eval-list-gexpo (list ge1 ge2) s/c env store
			   (list 'mplus-k s/c env cont mc $)
			   mc out ge1-ge2-$-lst))]
   [(fresh (x1 x2 ge sub count)
	   (== 'call/fresh rel-name)
	   (== (list x1 ge) args)
	   (== (cons sub count) s/c)
	   (eval-gexp-auxo ge (cons sub (+ 1 count)) (cons (cons x1 x2) env) store
			   cont mc out $))]
   [(fresh (paras body val ans)
	   (== 'rel-abs rel-name)
	   (== (list paras body) args)
	   (== (list 'rel-abs paras body s/c env) val)
	   (== (answer val store) ans)
           (apply-rel-ko cont ans out))]
   [(fresh (paras body val ans e-para s/c-para r-para st-para k-para out-para)
	   (== 'muo rel-name)
	   (== paras (list e-para s/c-para r-para st-para k-para out-para))
	   (== (list paras body) args)
	   (== (list 'muo-reifier paras body) val)
	   (== (answer val store) ans)
           (apply-rel-ko cont ans out))]
   [(fresh (paras body val ans e-para s/c-para r-para st-para k-para out-para)
	   (== 'muos rel-name)
	   (== paras (list e-para s/c-para r-para st-para k-para out-para))
	   (== (list paras body) args)
	   (== (list 'muos-reifier paras body) val)
	   (== (answer val store) ans)
           (apply-rel-ko cont ans out))
    ]))))
(define (eval-list-gexpo gexp* s/c env store cont mc out $*)
  (conde
    [(fresh (ans)
         (== '() e*)
         (== '() v-out*) ; v-out*         
         (== (answer '() s) ans)
         (apply-ko k ans out))]
    [(fresh (gexp gexp-rst $1 $-rst)
	    (== (cons gexp gexp-rst) gexp*)
	    (== (cons $1 $-rst) $*)
	    (eval-gexp-auxo gexp s/c env store
			    (list 'eval-list-k gexp-rst env cont $-rst)
			    out $1))]))

(define (apply-rel-abso para* body arg* s/c env store cont mc out $)
  (fresh (addr* env^ store^)
	 (ext-envo para* addr* env env^)
	 (ext-storeo addr* arg* store store^)
	 (map-relo numbero addr*)
	 (map-relo symbolo para*) ;; do this on all element of list
	 (map-relo (not-in-storeo store) addr*) ; not-in-storeo also calls numbero on addr--is this redundancy desireable?
	 (eval-gexp-auxo body s/c env^ store^ cont mc out $)))
(define (map-relo rel lst)
  (if (null? lst) #s
      (conj (rel (car lst)) (map-relo rel (cdr lst)))))

(define (apply-muo-reifier paras body args s/c env store cont mc out $)
  (fresh (e-para s/c-para r-para st-para k-para)
	 (== paras (list e-para s/c-para r-para st-para k-para))
	 (== (cons (list upper-s/c upper-env upper-store upper-cont) upper-meta-cont) forced-mc)
	 (exto paras (list args s/c env store cont) upper-s/c s/c-res)
	 (meta-cont-forceo mc forced-mc)
	 (eval-gexp-auxo body s/c-res upper-env upper-store upper-cont upper-meta-cont out $)
	 ))

;; expression * environment * state * continuation * value -> goal
(define eval-schemeo
  (lambda (exp env s k v-out)
    (fresh (ans s^ v-out')
      (== (answer v-out s^) ans)
      (conde
        [(== empty-k k)
         (== v-out v-out')
         ]
        [(=/= empty-k k)])      
      (eval-scheme-auxo exp env s k ans v-out'))))
;; expression * environment * state * continuation * (value * state) * value -> goal
;; v-out is the value of exp under environment env and store s,
;; out is final value-state pair after applying continuation k
(define eval-exp-auxo
  (lambda (exp env s k out v-out)
    (conde
     [(fresh (val)
	     (== exp v-out)
	     (== ans (answer exp s))
	     (conde
	      [(numbero exp)]
	      [(booleano exp)]
	      [(== '() exp)])
	     (apply-ko k ans out))]
     [(fresh (v ans)
             (symbolo exp)         
             (lookupo exp env s v)
             (== v v-out) ; v-out
             (== (answer v s) ans)
             (apply-ko k ans out))]
     [(fresh (val)
	     (== (f . args) exp)
	     (eval-scm-auxo f env s
			    (list 'application-k args env k v-out)
			    out v-out-ignore))])))
(define list-auxo
  (lambda (e* env s k out v-out*)
    (conde
      [(fresh (ans)
         (== '() e*)
         (== '() v-out*) ; v-out*         
         (== (answer '() s) ans)
         (apply-ko k ans out))]
      [(fresh (e ignore v-out v-out^ v-out-rest v-out-e)
         (== `(,e . ,ignore) e*)
         (== `(,v-out-e . ,v-out-rest) v-out*) ; v-out*
         (eval-exp-auxo e env s `(list-aux-outer-k ,e* ,env ,k ,v-out-rest) out v-out-e))])))
(define apply-ko
  (lambda (k^ v/s out)
    (conde
     [(fresh (v s)
             (== empty-k k^)
             (== v/s out)
             (== (answer v s) v/s))]
     [(fresh (args env k v-out)
	     (== (list 'application-k args env k v-out) k^)
	     (== (answer fval s^) v/s)
	     (conde
	      [(== fval (list 'subr subr-name))
	       (eval-scm-listo args v* (list 'fsubr))
	       (apply-subr subr-name args env out v-out)]
	      [(== fval (list 'fsubr fsubr-name))
	       (apply-fsubr subr-name args env out v-out)]
	      [(== fval (list 'lambda-abstraction para body))
	       (conde
		[(== args '())
		 (apply-proco )]
		[(== args (arg . args-rst))]
	       (eval-scmo args v* (list 'lambda-continuation))
	       ;; evaluate arguments, apply-lambda as continuation
	       ]))]
      [(fresh (x env k v s^ addr s^^)
         (== (set!-k x env k) k^)
         (== (answer v s^) v/s)
         (numbero addr)
         (ext-storeo addr v s^ s^^)
         (lookup-env-only-auxo x env addr)
         (apply-ko k (answer 'void s^^) out)
         )]
      [(fresh (p k a s^^ v-out^)
         (== (application-inner-k p k v-out^) k^)
         (== (answer a s^^) v/s)
         (apply-proco p a s^^ k out v-out^)
         )]
      [(fresh (rand env k p s^ v-out^ v-out-ignore)
         (== (application-outer-k rand env k v-out^) k^)
         (== (answer p s^) v/s)
     
         (fresh (x body env^)
           (== (make-proc x body env^) p))

         (eval-exp-auxo rand env s^ (application-inner-k p k v-out^) out v-out-ignore) 
         )]
      [(fresh (v k v* s^^ ans)
         (== (list-aux-inner-k v k) k^)
         (== (answer v* s^^) v/s)
         (== (answer (cons v v*) s^^) ans)
         (apply-ko k ans out))]
      [(fresh (e* env k v s^ e*-rest ignore v-out-rest)
         (== (list-aux-outer-k e* env k v-out-rest) k^)
         (== (answer v s^) v/s)
         (== `(,ignore . ,e*-rest) e*)
         (list-auxo e*-rest env s^ (list-aux-inner-k v k) out v-out-rest) 
         )])))
(define apply-proco
  (lambda (p a s^ k^ out v-out)
    (fresh (x body env addr env^ s^^)
      (== (make-proc x body env) p)
      (ext-envo x addr env env^)
      (ext-storeo addr a s^ s^^)
      (numbero addr)
      (symbolo x)
      (not-in-storeo addr s^) ; not-in-storeo also calls numbero on addr--is this redundancy desireable?
      (eval-exp-auxo body env^ s^^ k^ out v-out) ; v-out (this use is essential--passing a fresh variable breaks ability to generate quines in a reasonable time)
      )))

#|

      [(fresh (x body ans)
         (== `(lambda (,x) ,body) exp)
         (== (make-proc x body env) v-out) ; v-out
         (== (answer (make-proc x body env) s) ans)
         (not-in-envo 'lambda env)
         (symbolo x) ; interesting: adding this symbolo constraint increased the runtime by ~7%
         (apply-ko k ans out))]
   
       [(fresh (x e v-out-ignore)
         (== `(set! ,x ,e) exp)
         (not-in-envo 'set! env)
         (symbolo x)
         (== 'void v-out) ; v-out
         (eval-exp-auxo e env s `(set!-k ,x ,env ,k) out v-out-ignore))]
     
      [(fresh (e*)
         (== `(list . ,e*) exp)
         (not-in-envo 'list env)
         (list-auxo e* env s k out v-out) ; v-out
         )])))
|#
