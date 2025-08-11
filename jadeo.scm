(load "lookupo-lib.scm")
;;(load "mk-lib.scm")
(load "mk-vicare.scm")
(load "faster-mk.scm")
(define debug #t)
(define debug-printfo
  (lambda args
    (lambda (st)
  (if debug
      (begin
        (apply printf (map (lambda (x) (walk* x (state-S st))) args))
        st)
      st))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Basic Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define answer cons)
(define peano-zero '())
(define (peano-incr n) `(,n))
(define (peano n)
  (if (zero? n) '() `(,(peano (- n 1)))))

(define (var?o x)
  (fresh (val)
    ;; `val` is a Peano numeral    
    (== `(var . ,val) x)))

(define (var=?o x y)  
  (fresh (val)
    ;; `val` is a Peano numeral
    (== `(var . ,val) x)
    (== `(var . ,val) y)))

(define (var=/=o x y)
  (fresh (val1 val2)
    ;; `val1` and `val2` are Peano numerals
    (== `(var . ,val1) x)
    (== `(var . ,val2) y)
    (=/= val1 val2)))

(define (booleano b)
  (conde
    [(== #t b)]
    [(== #f b)]))

(define (walko u s v)
  (conde
    [(== u v)
     (conde
       [(symbolo u) (== u v)]
       [(numbero u) (== u v)]
       [(booleano u) (== u v)]
       [(== '() u) (== u v)])]
    [(fresh (a d)
       (== `(,a . ,d) u)
       (=/= a 'var)
       (== u v))]
    [(var?o u)
     (conde
       [(== u v) (not-assp-subo u s)]
       [(fresh (pr-d)
          (assp-subo u s `(,u . ,pr-d))
          (walko pr-d s v))])]))
(define (assp-subo v s out)
  (fresh (h t h-a h-d)
    (== `(,h . ,t) s)
    (== `(,h-a . ,h-d) h)
    (var?o v)
    (var?o h-a)
    (conde
      [(== h-a v) (== h out)]
      [(=/= h-a v) (assp-subo v t out)])))

(define (not-assp-subo v s)
  (fresh ()
    (var?o v)
    (conde
      [(== '() s)]
      [(fresh (t h-a h-d)
        (== `((,h-a . ,h-d) . ,t) s)
        (var?o h-a)
        (=/= h-a v)
        (not-assp-subo v t))])))


(define (ext-so u v s s1)
  (== `((,u . ,v) . ,s) s1))

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

(define (bindo $ ge env store cont mc out $-out)
  (conde
   [(== '() $)
    (== '() $-out)
    (apply-rel-ko cont (answer $-out store) mc out)]
   [(fresh (d)
	   (== `(delayed . ,d) $)
	   (== `(delayed bind ,$ ,ge ,env ,store) $-out)
	   (apply-rel-ko cont (answer $-out store) mc out))]
   [(fresh (s/c $-rst v-a v-d)
	   (== (cons s/c $-rst) $)
	   (=/= 'delayed s/c)
	   (eval-gexp-auxo ge s/c env store
			   (list 'bind-rec-k (list $-rst ge env $-out) cont)
			   mc out ge-out)
	   )]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Core Evaluators ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
	   (== (cons rel-e args) gexp)
	   (eval-gexp-auxo rel-e s/c env store
			  (list 'application-rel-k (list args s/c env v-out) cont)
			  mc out rel-val-ignore))]))

(define (apply-rel-ko cont val/store mc out)
  (conde
   [(fresh (rel store level)
           (== 'id-cont cont)
	   ;;(== mc `(next-meta-cont ,level))
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
	   (bindo g1-$ ge2 env store k mc out v-out))]
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
           (== (list 'eval-list-k (list gexp*-rst env s/c $*-rst) k) cont)
           (== (answer v-out store) val/store)
           (eval-list-gexpo gexp*-rst s/c env store
			    (list 'cons-k (list v-out) k) mc out $*-rst))]
   [(fresh (v-out k $* store ans)
           (== (list 'cons-k (list v-out) k) cont)
           (== (answer $* store) val/store)
           (== (answer (cons v-out $*) store) ans)
           (apply-rel-ko k ans mc out))]
   [(fresh (v-out store)
	   (== (list 'exit-level-k v-out) cont)
	   (== (answer v-out store) v/s)
	   (apply-exit-level-conto v-out mc out))]
  
   ))

(define (apply-rel-subr rel-name args s/c env store cont mc out v-out)
  (conde
   [(fresh (v1 v2 sub count sub^ v-out)
	   (== '==mk rel-name)
	   (== (list v1 v2) args)
	   (== (cons sub count) s/c)
	   (conde
            [(== #f sub^) (== '() v-out)]
            [(=/= #f sub^) (== `((,sub^ . ,count)) v-out)])
	   (unifyo v1 v2 sub sub^)
	   (apply-rel-ko cont (cons v-out store) mc out))]
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
	   (eval-gexp-auxo ge (cons sub (peano-incr count)) (cons (cons x1 x2) env) store
			   cont mc out v-out))]
   [(fresh (paras body ans)
	   (== 'rel-abs rel-name)
	   (== (list paras body) args)
	   (== (list 'rel-abs paras body s/c env) v-out)
	   (== (answer v-out store) ans)
           (apply-rel-ko cont ans mc out))]
     
   [(fresh (paras body ans e-para s/c-para r-para st-para k-para)
	   (== 'muo rel-name)
	   (== paras (list e-para s/c-para r-para st-para k-para))
	   (== (list paras body) args)
	   (== (list 'muo-reifier paras body) v-out)
	   (== (answer v-out store) ans)
           (apply-rel-ko cont ans mc out))]
   [(fresh (paras body ans e-para s/c-para r-para st-para k-para)
	   (== 'muos rel-name)
	   (== paras (list e-para s/c-para r-para st-para k-para))
	   (== (list paras body) args)
	   (== (list 'muos-reifier paras body) v-out)
	   (== (answer v-out store) ans)
           (apply-rel-ko cont ans mc out))]
   [(fresh (e r st k)
	   (== 'meaning-scm rel-name)
	   (== (list e r st k) args)
	   ;;(apply-substitution s/c (list e r st k))
	   (meaning-scm-o e r st k (list 'kanren s/c env store cont) mc out v-out)
	   )]
   [(fresh (e s/c-arg r st k)
	   (== 'meaning-mk rel-name)
	   (== (list e s/c-arg r st k) args)
	   ;;(apply-substitution s/c (list e s/c-arg r st k))
	   (meaning-mk-o e s/c-arg r st k (list 'kanren s/c env store cont) mc out v-out)
	   )]))
;; use a substitution to give additional constraints to terms
;; update the substitution of the program using a reified substitution and a list of terms
;; (define (apply-substitution s/c tms)  )

(define (apply-exit-level-conto v-out mc out)
  (conde
   [(fresh (upper-s/c upper-env upper-store upper-cont upper-meta-cont
		      forced-mc)
	   (== (cons (list 'kanren upper-s/c upper-env upper-store upper-cont)
		     upper-meta-cont) forced-mc)
	   (meta-cont-forceo mc forced-mc)
	   (apply-rel-ko upper-cont (cons v-out upper-store) upper-meta-cont out)
           )]
   [(fresh (upper-env upper-store upper-cont upper-meta-cont forced-mc)
	   (== (cons (list 'scheme upper-env upper-store upper-cont)
		     upper-meta-cont) forced-mc)
	   (meta-cont-forceo mc forced-mc)
	   (apply-ko upper-cont (cons v-out upper-store) upper-meta-cont out)
           )]))
(define (eval-list-gexpo gexp* s/c env store cont mc out $*)
  (conde
    [(fresh (ans)
         (== '() gexp*)
         (== '() $*)
         (== (answer '() store) ans)
         (apply-rel-ko cont ans out))]
    [(fresh (gexp gexp-rst $1 $-rst)
	    (== (cons gexp gexp-rst) gexp*)
	    (== (cons $1 $-rst) $*)
	    (eval-gexp-auxo gexp s/c env store
			    (list 'eval-list-k (list gexp-rst env s/c $-rst) cont)
			    out $1))]))

(define (apply-rel-abso para* body arg* s/c env store cont mc out $)
  (fresh (addr* env^ store^)
	 (exts-envo para* addr* env env^)
	 (exts-storeo addr* arg* store store^)
	 (number*o addr*)
	 (symbol*o para*)
	 (not-in-storeo store addr*)
	 (eval-gexp-auxo body s/c env^ store^ cont mc out $)))
(define (number*o ns)
  (conde
   [(== ns '())]
   [(fresh (n ns-rst)
	   (== (cons n ns-rst) ns)
	   (numbero n)
	   (number*o ns-rst))]))
(define (symbol*o ids)
  (conde
   [(== ids '())]
   [(fresh (id ids-rst)
	   (== (cons id ids-rst) ids)
	   (symbolo id)
	   (symbol*o ids-rst))]))

(define (not-in-storeo store addrs)
  (fresh (addr*)
	 (store->addr*o store addr*)
	 (no-same-addrs addrs* addrs)))
(define (no-same-addrs addrs1 addrs2)
  (conde
   [(== addrs2 '())]
   [(fresh (addr addrs2-rst)
	   (== (cons addr addrs2-rst) addrs2)
	   (numbero addr)
	   (absento addr addrs1)
	   (no-same-addrs addrs1 addrs2-rst))]))
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
(define  (meaning-scm-o e r st k cur-level mc out v-out)
  (fresh (forced-new-mc new-mc new-k)
	 (== (cons cur-level mc) forced-new-mc)
	 (meta-cont-forceo new-mc forced-new-mc)
	 (add-end-conto k (list 'exit-level-k v-out) new-k)
	 (eval-scm-auxo e r st new-k new-mc out e-out)
	 ))
(define (meaning-mk-o e s/c-arg r st k cur-level mc out $)
   (fresh (forced-new-mc new-mc new-k)
	 (== (cons cur-level mc) forced-new-mc)
	 (meta-cont-forceo new-mc forced-new-mc)
	 (add-end-conto k (list 'exit-level-k $) new-k)
	 (eval-gexp-auxo e r st new-k new-mc out e-out)
	 ))

(define (add-end-conto k end-k new-k)
  (conde
   [(== k 'id-cont) (== new-k end-k)]
   [(fresh (k-name k-args k-rst new-k-rst)
	   (== k (list k-name k-args k-rst))
	   (== new-k (list k-name k-args new-k-rst))
	   (add-end-conto k-rst end-k new-k-rst))]))

;; expression * environment * state * continuation * value -> goal
;(define eval-schemeo
 ; (lambda (exp env s k v-out)
  ;  (fresh (ans s^ v-out^)
   ;   (== (answer v-out s^) ans)
    ;  (conde
     ;   [(== 'id-cont k)
      ;   (== v-out v-out^)
       ;  ]
        ;[(=/= 'id-cont k)])      
      ;(eval-scm-auxo exp env s k ans mc v-out^))))
;; expression * environment * state * continuation * (value * state) * value -> goal
;; v-out is the value of exp under environment env and store s,
;; out is final value-state pair after applying continuation k
(define eval-scm-auxo
  (lambda (exp env store cont mc out v-out)
   ;; (display (list 'eval-scm-auxo exp env store cont mc out v-out))
    ;;(display "\n")
    (conde
     [(fresh (val ans)
	     (== exp v-out)
	     (== ans (answer exp store))
	     (conde
	      [(numbero exp)]
	      [(booleano exp)]
	      [(== '() exp)])
	     (apply-ko cont ans mc out))]
     [(fresh (v ans)
             (symbolo exp)         
             (lookupo exp env store v)
             (== v v-out)
             (== (answer v store) ans)
             (apply-ko cont ans mc out))]
     [(fresh (f args v-out-ignore)
	     (== (cons f args) exp)
	     (debug-printfo
	      "\neval-scm-auxo:\n exp: ~s\n env: ~s\n cont: ~s\n v-out: ~s\n\n"
	      exp env cont v-out)
	     (eval-scm-auxo f env store
			    (list 'application-k (list args env v-out) cont)
			    mc out v-out-ignore))])))

(define apply-ko
  (lambda (cont v/s mc out)
    ;;(display (list 'apply-ko cont v/s mc out))
    ;;(display "\n")
    (conde
     [(fresh (v s level)
             (== 'id-cont cont)
	     ;;(== mc `(next-meta-cont ,level))
             (== v/s out)
             (== (answer v s) v/s))]
     
     [(fresh (fval args env store k v-out)
	     (== (list 'application-k (list args env v-out) k) cont)
	     (== (answer fval store) v/s)
	     (debug-printfo
	      "\napplication-k:\n fval: ~s\n args: ~s\n env: ~s\n cont/k: ~s\n v-out: ~s\n\n"
	      fval args env k v-out)
	     (conde
	      [(fresh (subr-name args-vals)
		      (== fval (list 'subr subr-name))
		      (eval-list-scmo args env store
				      (list 'apply-subr-k (list subr-name v-out) k)
				      mc out args-vals))]
	      [(fresh (fsubr-name)
		      (== fval (list 'fsubr fsubr-name))
		      (apply-fsubro fsubr-name args env store k mc out v-out))]
	      [(fresh (paras body lambda-env args-vals)
		      (== fval (list 'lambda-abstraction paras body lambda-env))
		      (eval-list-scmo args env store
				      (list 'apply-lambda-k
					    (list paras body lambda-env v-out) k)
				      mc out args-vals))]
	      [(fresh (paras body)
		      (== fval (list 'muso-reifier paras body))
		      (apply-muso-reifier paras body args env store k mc out v-out))]
	      ))]
     [(fresh (subr-name v-out k vals store)
	     (== (list 'apply-subr-k (list subr-name v-out) k) cont)
	     (== (answer vals store) v/s)
	     (debug-printfo
	      "\napply-subr-k:\n subr-name: ~s\n v-out: ~s\n vals: ~s\n cont: ~s\n\n"
	      subr-name v-out vals cont)
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
             (== (answer v-out store) v/s)
	     (debug-printfo
	      "\neval-list-k:\n v-out: ~s\n exp*-rst: ~s\n v*-rst: ~s\n k: ~s\n\n"
	      v-out exp*-rst v*-rst k)
             (eval-list-scmo exp*-rst env store
			     (list 'cons-k (list v-out) k) mc out v*-rst))]
     [(fresh (v-out k v* store ans)
             (== (list 'cons-k (list v-out) k) cont)
             (== (answer v* store) v/s)
             (== (answer (cons v-out v*) store) ans)
	     (debug-printfo
	      "\ncons-k:\n v-out: ~s\n v*: ~s\n k: ~s\n\n"
	      v-out v* k)
             (apply-ko k ans mc out))]
     [(fresh (x env k v store addr store^)
             (== (list 'set!-k (list x env) k) cont)
             (== (answer v store) v/s)
             (numbero addr)
             (exts-storeo addr v store store^)
             (lookup-env-only-auxo x env addr)
             (apply-ko k (answer 'void store^) mc out)
             )]
     [(fresh (env k e-v r-v st-v k-v store v-out)
	     (== (list 'spawn-scm-k (list env) k) cont)
	     (== (answer (list e-v r-v st-v k-v) store) v/s)
	     (meaning-scm-o e-v r-v st-v k-v
			    (list 'scheme env store k) mc out v-out))]
     [(fresh (env k e-v s/c-v r-v st-v k-v store v-out)
	     (== (list 'spawn-mk-k (list env) k) cont)
	     (== (answer (list e-v s/c-v r-v st-v k-v) store) v/s)
	     (meaning-mk-o e-v s/c-v r-v st-v k-v
			   (list 'scheme env store k) mc out v-out))]
     [(fresh (ids addrs let-args-vals body env store k env^ store^ v-out)
	     (== (list 'let-k (list ids body) k) cont)
	     (== (answer let-args-vals store) v/s)
	     (exts-envo ids addrs env env^)
	     (exts-storeo addrs let-args-vals store store^)
	     (number*o addrs)
	     (symbol*o ids)
	     (not-in-storeo store addrs)
	     (eval-scm-auxo body env^ store^ k mc out v-out)
	     )]
     )))

(define (eval-list-scmo exp* env store cont mc out v-out*)
  (conde
   [(fresh (ans)
	   (== '() exp*)
	   (== '() v-out*)
	   (== (answer '() store) ans)
	   (debug-printfo
	    "\neval-list-scmo nil:\n exp*: ~s\n v-out*: ~s\n cont: ~s\n\n"
	    exp* v-out* cont)
	   (apply-ko cont ans mc out))]
   [(fresh (exp exp-rst v1 v-rst)
	   (== (cons exp exp-rst) exp*)
	   (== (cons v1 v-rst) v-out*)
	   (debug-printfo
	    "\neval-list-scmo:\n exp: ~s\n exp-rst: ~s\n v1: ~s\n v-rst: ~s\n cont: ~s\n\n"
	    exp exp-rst v1 v-rst cont)
	   (eval-scm-auxo exp env store
			  (list 'eval-list-k (list exp-rst env v-rst) cont)
			  mc out v1))]))
(define (apply-subro subr-name vals store cont mc out v-out)
  (conde
   [(fresh (a d ans)
	   (== subr-name 'cons)
	   (== (list a d) vals)
	   (== (cons a d) v-out)
	   (== (answer v-out store) ans)
	   (debug-printfo
	    "\napply-cons:\n a: ~s\n d: ~s\n v-out: ~s\n cont: ~s\n\n"
	    a d v-out cont)
	   (apply-ko cont ans mc out))]
   [(fresh (a d ans)
	   (== (list (cons a d)) vals)
	   (conde
	    [(== subr-name 'car)
	     (== v-out a)]
	    [(== subr-name 'cdr)
	     (== v-out d)])
	   (== (answer v-out store) ans)
	   (apply-ko cont ans mc out))]
   [(fresh (ans)
	   (== subr-name 'null?)
	   (== (list '()) vals)
	   (== v-out #t)
	   (== (answer v-out store) ans)
	   (apply-ko cont ans mc out))]))
(define (apply-fsubro fsubr-name args env store cont mc out v-out)
  ;;(display (list 'apply-fsubro fsubr-name args "\n"))
  (conde
   [(fresh (ans)
	   (== 'quote fsubr-name)
	   (== (list v-out) args)
	   (== (answer v-out store) ans)
	   (absento 'var v-out)
	   (absento 'lambda-abstraction v-out)
	   (absento 'muo-reifier v-out)
	   (absento 'muos-reifier v-out)
	   (absento 'muso-reifier v-out)
	   (debug-printfo
	    "\napply-fsubr quote:\n v-out: ~s\n cont: ~s\n\n"
	    v-out cont)
	   (apply-ko cont ans mc out))]
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
   [(fresh (paras body ans e-para r-para st-para k-para)
	   (== 'muso fsubr-name)
	   (== paras (list e-para r-para st-para k-para))
	   (== (list paras body) args)
	   (== (list 'muso-reifier paras body) v-out)
	   (== (answer v-out store) ans)
           (apply-ko cont ans mc out))]
   [(fresh (e r st k spawn-args)
	   (== 'meaning-scm fsubr-name)
	   (== (list e r st k) args)
	   (eval-list-scmo (list e r st k) env store
			   (list 'spawn-scm-k (list env) cont)
			   mc out spawn-args))]
   [(fresh (e s/c-arg r st k spawn-args)
	   (== 'meaning-mk fsubr-name)
	   (== (list e s/c-arg r st k) args)
	   (eval-list-scmo (list e s/c-arg r st k) env store
			   (list 'spawn-mk-k (list env) cont)
			   mc out spawn-args)
	   
	   )]
   [(fresh (pairs body ids bodies bodies-vals)
	   (== 'let fsubr-name)
	   (== (list pairs body) args)
	   (let-ids-bodies pairs ids bodies)
	   (eval-list-scmo bodies env store
			   (list 'let-k (list ids) cont)
			   mc out bodies-vals))]
   [(fresh (pairs body ids bodies bodies-vals)
	   (== 'letrec fsubr-name)
	   (== (list pairs body) args)
	   (let-ids-bodies pairs ids bodies)
	   ;;(ext-envo ids '() env env^)
	   (eval-list-scmo bodies env store
			   (list 'let-k (list ids) cont)
			   mc out bodies-vals))]
   ))
(define (let-ids-bodies pairs ids bodies)
  (conde
   [(== '() pairs)
    (== '() ids)
    (== '() bodies)]
   [(fresh (id1 body1 pairs-rst ids-rst bodies-rst)
	   (== (cons (list id1 body1) pairs-rst) pairs)
	   (== (cons id1 ids-rst) ids)
	   (== (cons body1 bodies-rst) bodies)
	   (let-ids-bodies pairs-rst ids-rst bodies-rst))]))

(define (apply-proco paras body env vals store cont mc out v-out)
  (fresh (addrs env^ store^)
	 (exts-envo paras addrs env env^)
	 (exts-storeo addrs vals store store^)
	 (number*o addrs)
	 (symbol*o paras)
	 (not-in-storeo store addrs)
	 (eval-scm-auxo body env^ store^ cont mc out v-out) 
	 ))
(define (apply-muso-reifier paras body args env store cont mc out $)
  (fresh (e-para r-para st-para k-para
		 upper-s/c upper-env upper-store upper-cont upper-meta-cont
		 forced-mc env-res)
	 (== paras (list e-para r-para st-para k-para))
	 (== (cons (list 'kanren upper-s/c upper-env upper-store upper-cont)
		   upper-meta-cont) forced-mc)
	 (exts-s/co paras (list args env store cont) upper-s/c s/c-res)
	 (meta-cont-forceo mc forced-mc)
	 (eval-gexp-auxo body s/c-res upper-env upper-store upper-cont upper-meta-cont out $)
	 ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;; Interfacing with Scheme ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (walk*o unwalked-v s u)
  (fresh (v)
    (walko unwalked-v s v)
    (conde
      [(== v u)
       (conde
         [(var?o v)]
         [(numbero v)]
         [(symbolo v)]
         [(booleano v)]
         [(== '() v)])]
      [(fresh (a d walk*-a walk*-d)
         (== `(,a . ,d) v)
         (=/= a 'var)
         (conde
           [(== '_. a)
            (== u v)]
           [(=/= '_. a)
            (== `(,walk*-a . ,walk*-d) u)
            (walk*o a s walk*-a)
            (walk*o d s walk*-d)]))])))

(define (pullo $ mc $1)
  (conde
    [(== '() $) (== '() $1)]
    [(fresh (a d)
       (== `(,a . ,d) $)
       (== $ $1)
       (=/= 'delayed a))]
    [(fresh ($a $b $a1 $2)
       (== `(delayed mplus ,$a ,$b) $)
       (pullo $a mc $a1)
       (mpluso $b $a1 $2)
       (pullo $2 mc $1))]
    [(fresh (saved-ge saved-env saved-store saved-$ saved-$1 $2 $-tmp)
       (== `(delayed bind ,saved-$ ,saved-ge ,saved-env ,saved-store) $)
       (pullo saved-$ mc saved-$1)
       (bindo saved-$1 saved-ge saved-env saved-store 'id-cont mc $2 $-tmp)
       (pullo $2 mc $1))]))

(define (take-allo $ mc s/c*)
  (fresh ($1)
    (pullo $ mc $1)
    (conde
      [(== '() $1) (== '() s/c*)]
      [(fresh (a d-s/c* $d)
         (== `(,a . ,$d) $1)
         (== `(,a . ,d-s/c*) s/c*)
         (take-allo $d mc d-s/c*))])))

(define (take-no n $ mc s/c*)
  (conde
    [(== '() n) (== '() s/c*)]
    [(=/= '() n)
     (fresh ($1)
       (pullo $ mc $1)
       (conde
         [(== '() $1) (== '() s/c*)]
         [(fresh (n-1 d-s/c* a d)
            (== `(,a . ,d) $1)
            (== `(,n-1) n)
            (== `(,a . ,d-s/c*) s/c*)
            (take-no n-1 d mc d-s/c*))]))]))

(define (lengtho l len)
  (conde
    [(== '() l) (== '() len)]
    [(fresh (a d len-d)
       (== `(,a . ,d) l)
       (== `(,len-d) len)
       (lengtho d len-d))]))

(define (reify-so v-unwalked s s1)
  (fresh (v)
    (walko v-unwalked s v)
    (conde
      [(var?o v)
       (fresh (len)
         (lengtho s len)
         (== `((,v . (_. . ,len)) . ,s) s1))]
      [(== s s1)
       (conde
         [(numbero v)]
         [(symbolo v)]
         [(booleano v)]
         [(== '() v)])]
      [(fresh (a d sa)
         (=/= 'var a)
         (== `(,a . ,d) v)
         (conde
           [(== '_. a)
            (== s s1)]
           [(=/= '_. a)
            (reify-so a s sa)
            (reify-so d sa s1)]))])))

(define (reify-state/1st-varo s/c out)
  (fresh (s c v u)
    (== `(,s . ,c) s/c)
    (walk*o `(var . ()) s v)
    (reify-so v '() u)
    (walk*o v u out)))

(define (reifyo s/c* out)
    (conde
      [(== '() s/c*) (== '() out)]
      [(fresh (a d va vd)
         (== `(,a . ,d) s/c*)
         (== `(,va . ,vd) out)
         (reify-state/1st-varo a va)
         (reifyo d vd))]))

(define micro-init-env
  '((==mk conj disj call/fresh
	  rel-abs muo muos meaning-scm
	  meaning-mk)
    (1 2 3 4)))
(define micro-init-store
  '((1 2 3 4)
    ((rel-subr ==mk)
     (rel-subr conj)
     (rel-subr disj)
     (rel-subr call/fresh)
     (rel-subr rel-abs)
     (rel-subr muo)
     (rel-subr muos)
     (rel-subr meaning-scm)
     (rel-subr meaning-mk)
     )))
(define mini-init-env micro-init-env)
(define mini-init-store micro-init-store)

(define scm-init-env
  '((set! lambda list muso meaning-scm meaning-mk let letrec)
    (1 2 3 4)))
(define scm-init-store
  '((1 2 3 4)
    ((fsubr set!)
     (fsubr lambda)
     (fsubr list)
     (fsubr muso)
     (fsubr meaning-scm)
     (fsubr meaning-mk)
     (fsubr let)
     (fsubr letrec))))

(define (meta-cont-forceo mc fc)
  (conde
    [(fresh (level)
       (== mc `(next-meta-cont ,level))
       (gen-meta-conto level fc))]
    [(fresh (a d)
       (== (cons a d) mc)
       (=/= a 'next-meta-cont)
       (== mc fc))]))
(define (gen-meta-conto level mc)
  (== `((kanren ,level ,mini-init-env ,mini-init-store id-cont)
	(kanren ,(peano-incr level) ,micro-init-env ,micro-init-store id-cont)
	(scheme ,(peano-incr (peano-incr level)) ,scm-init-env ,scm-init-store id-cont)
	. (next-meta-cont ,(peano-incr (peano-incr (peano-incr level))))) mc))

(define (runo answer-count gexp out)
  (fresh (mc mc-rst init-env init-store empty-sub)
	 (gen-meta-conto peano-zero mc)
	 (== `((kanren
		,peano-zero ,init-env
		,init-store id-cont)
	       . ,mc-rst) mc)
	 (== empty-sub '())
	 (conde
	  [(fresh ($ $/s s/c*)
		  (== answer-count 'all)
		  (eval-gexp-auxo gexp `(,empty-sub . ,peano-zero)
				  init-env init-store 'id-cont mc $/s $)
		  (take-allo $ mc s/c*)
		  (reifyo s/c* out))]
	  [(fresh (n $ $/s s/c*)
		  (=/= answer-count 'all)
		  (eval-gexp-auxo gexp `(,empty-sub . ,peano-zero)
				  init-env init-store 'id-cont mc $/s $)
		  (take-no answer-count $ mc s/c*)
		  (reifyo s/c* out))])))
