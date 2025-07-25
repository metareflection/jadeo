(define (ext-so u v s s1)
  (== `((,u . ,v) . ,s) s1))

(define (meta-cont-forceo mc fc)
  (conde
    [(fresh (level)
       (== mc `(next-meta-cont ,level))
       (gen-meta-conto `(s ,level) fc))]
    [(fresh (a d)
       (== (cons a d) mc)
       (=/= a 'next-meta-cont)
       (== mc fc))]))
(define (gen-meta-conto level mc)
  (== `((kanren ,mini-init-env ,mini-init-store ,init-cont)
	(kanren ,micro-init-env ,micro-init-store ,init-cont)
	(scheme ,scm-init-env ,scm-init-store ,init-cont)
	. (next-meta-cont ,level)) mc))

(define (mpluso $1 $2 $)
  (conde
    [(== '() $1) (== $2 $)]
    [(fresh (d)
       (== `(delayed . ,d) $1)
       (== `(delayed mplus ,$1 ,$2) $))]
    [(fresh (a d r1)
       (== `(,a . ,d) $1)
       (=/= 'delayed a)
       (== `(,a . ,r1) $)
       (mpluso d $2 r1))]))
(define (bind $ g)
  (cond
    ((null? $) mzero)
    ((procedure? $) (lambda () (bind ($) g)))
    (else (mplus (g (car $)) (bind (cdr $) g)))))
(define (bindo $ ge env store cont mc out $-out)
  (conde
   [(== '() $)
    (== mzero $-out)
    (apply-rel-ko cont (answer $-out store) mc out)]
   [(fresh (d)
	   (== `(delayed . ,d) $)
	   (== `(delayed bind ,$ ,ge ,env) $-out)
	   (apply-rel-ko cont (answer $-out store) mc out))]
   [(fresh (s/c $-rst v-a v-d)
	   (== (cons s/c $-rst) $)
	   (=/= 'delayed s/c)
	   (eval-gexp-auxo ge s/c env store
			   (list 'bind-rec-k (list $-rst ge env $-out) cont)
			   mc out ge-out)
	   )]))
(define (unifyo u-unwalked v-unwalked s s1)
  (fresh (u v)
	 (walko u-unwalked s u)
	 (walko v-unwalked s v)
	 (conde
	  [(var?o u) (var?o v) (var=?o u v) (== s s1)]
	  [(var?o u) (var?o v) (var=/=o u v) (ext-so u v s s1)]
	  [(var?o u) (numbero v) (ext-so u v s s1)]
	  [(var?o u) (symbolo v) (ext-so u v s s1)]
	  [(var?o u) (booleano v) (ext-so u v s s1)]
	  [(var?o u) (== '() v) (ext-so u v s s1)]
	  [(var?o u)
	   (fresh (a d)
		  (== `(,a . ,d) v)
		  (=/= 'var a))
	   (ext-so u v s s1)]
	  [(numbero u) (var?o v) (ext-so v u s s1)]
	  [(numbero u) (numbero v) (== u v) (== s s1)]
	  [(numbero u) (numbero v) (=/= u v) (== #f s1)]
	  [(numbero u) (symbolo v) (== #f s1)]
	  [(numbero u) (booleano v) (== #f s1)]
	  [(numbero u) (== '() v) (== #f s1)]
	  [(numbero u)
	   (fresh (a d)
		  (== `(,a . ,d) v)
		  (=/= 'var a))
	   (== #f s1)]
	  [(symbolo u) (var?o v) (ext-so v u s s1)]
	  [(symbolo u) (numbero v) (== #f s1)]
	  [(symbolo u) (symbolo v) (== u v) (== s s1)]
	  [(symbolo u) (symbolo v) (=/= u v) (== #f s1)]
	  [(symbolo u) (booleano v) (== #f s1)]
	  [(symbolo u) (== '() v) (== #f s1)]
	  [(symbolo u)
	   (fresh (a d)
		  (== `(,a . ,d) v)
		  (=/= 'var a))
	   (== #f s1)]
	  [(booleano u) (var?o v) (ext-so v u s s1)]
	  [(booleano u) (numbero v) (== #f s1)]
	  [(booleano u) (symbolo v) (== #f s1)]
	  [(booleano u) (booleano v) (== u v) (== s s1)]
	  [(booleano u) (booleano v) (=/= u v) (== #f s1)]
	  [(booleano u) (== '() v) (== #f s1)]
	  [(booleano u)
	   (fresh (a d)
		  (== `(,a . ,d) v)
		  (=/= 'var a))
	   (== #f s1)]
	  [(== '() u) (var?o v) (ext-so v u s s1)]
	  [(== '() u) (numbero v) (== #f s1)]
	  [(== '() u) (symbolo v) (== #f s1)]
	  [(== '() u) (booleano v) (== #f s1)]
	  [(== '() u) (== '() v) (== s s1)]
	  [(== '() u)
	   (fresh (a d)
		  (== `(,a . ,d) v)
		  (=/= 'var a))
	   (== #f s1)]
	  [(var?o v)
	   (fresh (a d)
		  (== `(,a . ,d) u)
		  (=/= 'var a))
	   (ext-so v u s s1)]
	  [(numbero v)
	   (fresh (a d)
		  (== `(,a . ,d) u)
		  (=/= 'var a))
	   (== #f s1)]
	  [(symbolo v)
	   (fresh (a d)
		  (== `(,a . ,d) u)
		  (=/= 'var a))
	   (== #f s1)]
	  [(booleano v)
	   (fresh (a d)
		  (== `(,a . ,d) u)
		  (=/= 'var a))
	   (== #f s1)]
	  [(== '() v)
	   (fresh (a d)
		  (== `(,a . ,d) u)
		  (=/= 'var a))
	   (== #f s1)]
	  [(fresh (u-a u-d v-a v-d s-a)
		  (== `(,u-a . ,u-d) u)
		  (== `(,v-a . ,v-d) v)
		  (=/= 'var u-a)
		  (=/= 'var v-a)
		  (conde
		   [(== s-a #f) (== #f s1) (unifyo u-a v-a s s-a)]
		   [(=/= s-a #f)
		    (unifyo u-a v-a s s-a)
		    (unifyo u-d v-d s-a s1)]))])))
;; evaluator for microkanren
(define (eval-gexp-auxo gexp s/c env store cont mc out v-out)
  (conde
   [(fresh (rel ans)
           (symbolo gexp)         
           (lookupo gexp env store rel)
	   (== v-out rel)
           (== (answer v-out store) ans)
           (apply-rel-ko cont ans mc out))]
   [(fresh (rel-e args rel-val-ignore)
	   (== (rel-e . args) gexp)
	   (eval-gexp-auxo rel-e s/c env store
			  (list 'application-rel-k (list args s/c env v-out) cont)
			  mc out rel-val-ignore))]))
(define empty-k (list 'empty-k '() '()))
(define (apply-rel-ko cont val/store mc out)
  (conde
   [(fresh (rel store)
           (== empty-k cont)
           (== val/store out)
           (== (answer rel store) val/store))]
   [(fresh (args s/c env k v-out)
	   (== (list 'application-rel-k (list args s/c env v-out) k) cont)
	   (== (answer rel store) val/store)
	   (conde
	    [(== rel (list 'rel-subr rel-subr-name))
	     (apply-rel-subr rel-subr-name args s/c env store k mc out v-out)]
	    [(== rel (list 'rel-abs paras body env))
	     (apply-rel-abs paras body args s/c env store k mc out v-out)]
	    [(== rel (list 'muo-reifier paras body))
	     (apply-muo-reifier paras body args s/c env store k mc out v-out)]
	    [(== rel (list 'muos-reifier paras body))
	     (apply-muos-reifier paras body args s/c env store k mc out v-out)]))]
   [(fresh (g1-$ ge2 env k v-out)
	   (== (list 'bind-k (list ge2 env v-out) k) cont)
	   (== (answer g1-$ store) val/store)
	   (bindo g1-$ ge2 s/c env store k mc out v-out))]
   [(fresh ($-rst ge env k full-bind-out ge-out1 store $-rst-out)
	   (== (list 'bind-rec-k (list $-rst ge env full-bind-out) k) cont)
	   (== (answer ge-out1 store) val/store)
	   (bindo $-rst ge env store
		  (list 'mplus-with-k (list ge-out1 full-bind-out) k)
		  mc out $-rst-out))]
   [(fresh (ge-out1 full-bind-out $-rst-out k store)
	   (== (list 'mplus-with-k (list ge-out1 full-bind-out) k) cont)
	   (== (answer $-rst-out store) val/store)
	   (mpluso ge-out1 $-rst-out full-bind-out)
	   (apply-rel-ko k (answer full-bind-out store) mc out)
	   )]
   [(fresh ($1 $2 k v-out)
	   (== (list 'mplus-k (list v-out) k) cont)
	   (== (answer (list $1 $2) store) val/store)
	   (mpluso $1 $2 v-out)
	   (apply-rel-ko k (answer v-out store) mc out))]
   [(fresh (env k v-out store gexp*-rst $*-rst)
           (== (list 'eval-list-k (list gexp*-rst env $*-rst) k) cont)
           (== (answer v-out store) val/store)
           (eval-list-gexpo gexp*-rst s/c env store
			    (list 'cons-k (list v-out) k) mc out $*-rst))]
   [(fresh (v-out k $* store ans)
           (== (list 'cons-k (list v-out) k) cont)
           (== (answer $* store) val/store)
           (== (answer (cons v-out $*) store) ans)
           (apply-rel-ko k ans mc out))]
  
   ))

(define (apply-rel-subr rel-name args s/c env store cont mc out v-out)
  (conde
   [(fresh (v1 v2 sub count sub' v-out)
	   (== '==mk rel-name)
	   (== (list v1 v2) args)
	   (== (cons sub count) s/c)
	   (conde
            [(== #f sub') (== '() v-out)]
            [(=/= #f sub') (== `((,sub' . ,count)) v-out)])
	   (unifyo v1 v2 sub sub')
	   (apply-rel-ko cont (cons v-out store) mc out)]
   [(fresh (ge1 ge2 ge1-$ ge$)
	   (== 'conj rel-name)
	   (== (list ge1 ge2) args)
	   (eval-gexp-auxo ge1 s/c env store
			   (list 'bind-k (list ge2 env v-out) cont)
			   mc out ge1-$))]
   [(fresh (ge1 ge2 ge1-$ ge2-$ ge$)
	   (== 'disj rel-name)
	   (== (list ge1 ge2) args)
	   (eval-list-gexpo (list ge1 ge2) s/c env store
			   (list 'mplus-k (list v-out) cont)
			   mc out ge1-ge2-$-lst))]
   [(fresh (x1 x2 ge sub count)
	   (== 'call/fresh rel-name)
	   (== (list x1 ge) args)
	   (== (cons sub count) s/c)
	   (eval-gexp-auxo ge (cons sub (+ 1 count)) (cons (cons x1 x2) env) store
			   cont mc out v-out))]
   [(fresh (paras body ans)
	   (== 'rel-abs rel-name)
	   (== (list paras body) args)
	   (== (list 'rel-abs paras body s/c env) v-out)
	   (== (answer v-out store) ans)
           (apply-rel-ko cont ans mc out))]
     
   [(fresh (paras body val ans e-para s/c-para r-para st-para k-para)
	   (== 'muo rel-name)
	   (== paras (list e-para s/c-para r-para st-para k-para))
	   (== (list paras body) args)
	   (== (list 'muo-reifier paras body) val)
	   (== (answer val store) ans)
           (apply-rel-ko cont ans out))]
   [(fresh (paras body val ans e-para s/c-para r-para st-para k-para)
	   (== 'muos rel-name)
	   (== paras (list e-para s/c-para r-para st-para k-para))
	   (== (list paras body) args)
	   (== (list 'muos-reifier paras body) val)
	   (== (answer val store) ans)
           (apply-rel-ko cont ans out))]
   [(fresh (e r st k)
	   (== 'meaning-scm rel-name)
	   (== (list e r st k) args)
	   (meaning-scm-o e r st k s/c env store cont mc out v-out)
	   )]
   [(fresh (e s/c-arg r st k)
	   (== 'meaning-mk rel-name)
	   (== (list e s/c-arg r st k) args)
	   (meaning-mk-o e s/c-arg r st k s/c env store cont mc out v-out)
	   )])))

(define (eval-list-gexpo gexp* s/c env store cont mc out $*)
  (conde
    [(fresh (ans)
         (== '() gexp*)
         (== '() $*) ; v-out*         
         (== (answer '() store) ans)
         (apply-ko cont ans out))]
    [(fresh (gexp gexp-rst $1 $-rst)
	    (== (cons gexp gexp-rst) gexp*)
	    (== (cons $1 $-rst) $*)
	    (eval-gexp-auxo gexp s/c env store
			    (list 'eval-list-k (list gexp-rst env $-rst) cont)
			    out $1))]))

(define (apply-rel-abso para* body arg* s/c env store cont mc out $)
  (fresh (addr* env^ store^)
	 (exts-envo para* addr* env env^)
	 (exts-storeo addr* arg* store store^)
	 (map-relo numbero addr*)
	 (map-relo symbolo para*) ;; do this on all element of list
	 (map-relo (not-in-storeo store) addr*)
	 (eval-gexp-auxo body s/c env^ store^ cont mc out $)))
(define (map-relo rel lst)
  (if (null? lst) #s
      (conj (rel (car lst)) (map-relo rel (cdr lst)))))

(define not-in-storeo
  (lambda (store addr)
    (fresh (addr*)
      (numbero addr)
      (store->addr*o store addr*)
      (absento addr addr*))))

(define (apply-muo-reifier paras body args s/c env store cont mc out $)
  (fresh (e-para s/c-para r-para st-para k-para
		 upper-s/c upper-env upper-store upper-cont upper-meta-cont
		 forced-mc env-res)
	 (== paras (list e-para s/c-para r-para st-para k-para))
	 (== (cons (list 'kanren upper-s/c upper-env upper-store upper-cont)
		   upper-meta-cont) forced-mc)
	 (exts-s/co paras (list args s/c env store cont) upper-s/c s/c-res)
	 (meta-cont-forceo mc forced-mc)
	 (eval-gexp-auxo body s/c-res upper-env upper-store upper-cont upper-meta-cont out $)
	 ))
(define (apply-muos-reifier paras body args s/c env store cont mc out v-out)
  (fresh (e-para s/c-para r-para st-para k-para
		 upper-env upper-store upper-cont upper-meta-cont forced-mc env-res)
	 (== paras (list e-para s/c-para r-para st-para k-para))
	 (== (cons (list 'scheme upper-env upper-store upper-cont) upper-meta-cont) forced-mc)
	 (exts-envo paras (list args s/c env store cont) upper-env env-res)
	 (meta-cont-forceo mc forced-mc)
	 (eval-scm-auxo body env-res upper-store upper-cont upper-meta-cont out v-out)
	 ))
;; needs to look up substitution for possible values of e r st k s/c, before using them
(define  (meaning-scm-o e r st k s/c env store cont mc out v-out)
  (fresh (forced-new-mc new-mc new-k)
	 (== (cons (list 'kanren s/c env store cont) mc) forced-new-mc)
	 (meta-cont-forceo new-mc forced-new-mc)
	 (add-end-scm-conto k (list 'exit-level-k v-out) new-k)
	 (apply-substitution s/c (list e r st k))
	 (eval-scm-auxo e r st new-k new-mc out e-out)
	 ))
(define (meaning-mk-o e s/c-arg r st k s/c env store cont mc out $)
   (fresh (forced-new-mc new-mc new-k)
	 (== (cons (list 'kanren s/c env store cont) mc) forced-new-mc)
	 (meta-cont-forceo new-mc forced-new-mc)
	 (add-end-mk-conto k (list 'exit-level-k $) new-k)
	 (apply-substitution s/c (list e s/c-arg r st k))
	 (eval-gexp-auxo e r st new-k new-mc out e-out)
	 ))
;; use a substitution to give additional constraints to terms
;; update the substitution of the program using a reified substitution and a list of terms
(define (apply-substitution s/c tms)
  )
(define (add-end-scm-conto k end-k new-k)
  (conde []
	 ))
(define (add-end-scm-conto k end-k new-k)
  (conde []
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
      (eval-scm-auxo exp env s k ans v-out'))))
;; expression * environment * state * continuation * (value * state) * value -> goal
;; v-out is the value of exp under environment env and store s,
;; out is final value-state pair after applying continuation k
(define eval-scm-auxo
  (lambda (exp env store cont out v-out)
    (conde
     [(fresh (val)
	     (== exp v-out)
	     (== ans (answer exp store))
	     (conde
	      [(numbero exp)]
	      [(booleano exp)]
	      [(== '() exp)])
	     (apply-ko cont ans out))]
     [(fresh (v ans)
             (symbolo exp)         
             (lookupo exp env store v)
             (== v v-out)
             (== (answer v store) ans)
             (apply-ko cont ans out))]
     [(fresh (val)
	     (== (f . args) exp)
	     (eval-scm-auxo f env store
			    (list 'application-k args env cont v-out)
			    out v-out-ignore))])))

(define (apply-exit-level-conto v-out mc out)
  (fresh (upper-s/c upper-env upper-store upper-cont upper-meta-cont
		    forced-mc)
	 (== (cons (list 'kanren upper-s/c upper-env upper-store upper-cont)
		   upper-meta-cont) forced-mc)
	 (meta-cont-forceo mc forced-mc)
	 (apply-rel-ko upper-cont (cons v-out upper-store) upper-meta-cont out)
         ))
(define apply-ko
  (lambda (cont v/s mc out)
    (conde
     [(fresh (v s)
             (== empty-k cont)
             (== v/s out)
             (== (answer v s) v/s))]
     
     [(fresh (args env k v-out)
	     (== (list 'application-k (list args env v-out) k) cont)
	     (== (answer fval store) v/s)
	     (conde
	      [(== fval (list 'subr subr-name))
	       (eval-list-scmo args env store
			       (list 'apply-subr-k (list subr-name v-out) k)
			       mc out v-out)]
	      [(== fval (list 'fsubr fsubr-name))
	       (apply-fsubro fsubr-name args env store k mc out v-out)]
	      [(== fval (list 'lambda-abstraction paras body lambda-env))
	       (eval-list-scmo args env store
			       (list 'apply-lambda-k (list paras body lambda-env v-out) k)
			       mc out v-out)]))]
     [(fresh (subr-name v-out k vals store)
	     (== (list 'apply-subr-k (list subr-name v-out) k) cont)
	     (== (answer vals store) v/s)
	     (apply-subro subr-name vals store k mc out v-out))]
     [(fresh (paras body env v-out k vals store)
	     (== (list 'apply-lambda-k (list paras body env v-out) k) cont)
	     (== (answer vals store) v/s)
	     (apply-proco paras body env vals store k mc out v-out))]
     [(fresh (v-out store)
	     (== (list 'exit-level-k v-out) cont)
	     (== (answer v-out store) v/s)
	     (apply-exit-level-conto v-out mc out))]
     [(fresh (env k v-out store exp*-rst v*-rst)
             (== (list 'eval-list-k (list exp*-rst env v*-rst) k) cont)
             (== (answer v-out store) val/store)
             (eval-list-scmo exp*-rst env store
			     (list 'cons-k (list v-out) k) mc out v*-rst))]
     [(fresh (v-out k v* store ans)
             (== (list 'cons-k (list v-out) k) cont)
             (== (answer v* store) val/store)
             (== (answer (cons v-out v*) store) ans)
             (apply-ko k ans mc out))]
     [(fresh (x env k v store addr store^)
             (== (list 'set!-k (list x env) k) cont)
             (== (answer v store) v/s)
             (numbero addr)
             (exts-storeo addr v store store^)
             (lookup-env-only-auxo x env addr)
             (apply-ko k (answer 'void store^) mc out)
             )])))
(define (eval-list-scmo exp* env store cont mc out v-out*)
  (conde
   [(fresh (ans)
	   (== '() exp*)
	   (== '() v-out*)
	   (== (answer '() store) ans)
	   (apply-ko cont ans mc out))]
   [(fresh (exp exp-rst v1 v-rst)
	   (== (cons exp exp-rst) exp*)
	   (== (cons v1 v-rst) v-out*)
	   (eval-scm-auxo exp env store
			  (list 'eval-list-k (list exp-rst env v-rst) cont)
			  out v1))]))
(define (apply-fsubro fsubr-name args env store cont mc out v-out)
  (conde
   [(fresh (x e v-out-ignore)
	   (== 'set! fsubr-name)
           (== (list x e) args)
           (symbolo x)
           (== 'void v-out)
           (eval-scm-auxo e env store (list 'set!-k (list x env) cont) mc out v-out-ignore))]
   [(fresh (paras body ans)
	   (== 'lambda fsubr-name)
           (== (list paras body) args)
           (== (list 'lambda-abstraction paras body env) v-out)
           (== (answer v-out store) ans)
           (apply-ko cont ans mc out))]
   [(== 'list fsubr-name)
    (eval-list-scmo args env store cont mc out v-out)]
   
   ))   




(define (apply-proco paras body env vals store cont mc out v-out)
  (fresh (addrs env^ store^)
	 (exts-envo paras addrs env env^)
	 (exts-storeo addrs vals store store^)
	 (map-relo numbero addrs)
	 (map-relo symbolo paras)
	 (map-relo (not-in-storeo store) addrs)
	 (eval-scm-auxo body env^ store^ cont mc out v-out) 
	 ))

#|
  [(fresh (x e v ge ge* env^)
       (== `(let ((,x ,e)) ,ge . ,ge*) expr)
       (symbolo x)
       (== `((,x . ,v) . ,env) env^)
       (eval-scmo e env mc v)
       (eval-gexpro `(conj* ,ge . ,ge*) s/c env^ mc $))]
    [(fresh (id params geb ge ge* env^)
       (== `(letrec-rel ((,id ,params ,geb)) ,ge . ,ge*) expr)
       (symbolo id)
       (== `((rec (closr ,id ,params (delay ,geb))) . ,env) env^)
       (eval-gexpro `(conj* ,ge . ,ge*) s/c env^ mc $))]    
    [(fresh (id params body-expr ge ge* env^)
       (== `(letrec-func ((,id ,params ,body-expr)) ,ge . ,ge*) expr)
       (symbolo id)
       (== `((rec (scheme-closr ,id ,params ,body-expr)) . ,env) env^)
       (eval-gexpro `(conj* ,ge . ,ge*) s/c env^ mc $))]
|#

(define eval-prog-auxo
    (lambda (exp s/c env)
        ((_generate_toplevel-continuation initial-level
                                          (make-initial-environment)
					  (make-initial-evaluator))
             lavender-banner (initial-meta-continuation initial-level))))
