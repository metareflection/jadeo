;;any term returning expressions inside
;; can we put meaning inside == if inside it evaluates a scheme expr?

;; debugging showing out is tm, why?
#|
the main issue is meaning scheme and abstractions and reifiers (and perhaps apply cont)

these don't return a stream so might be better to place in the scheme level
|#
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
(define debug-gexp #t)
(define debug-gexpo
  (lambda args
    (lambda (st)
  (if debug-gexp
      (begin
        (apply printf (map (lambda (x) (walk* x (state-S st))) args))
        st)
      st))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Basic Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define answer cons)

(define (var?o x)
  (fresh (val1 val2)
    ;; val1 and val2 are Peano numerals    
    (== `(var ,val1 ,val2) x)))

(define (var=?o x y)  
  (fresh (val1 val2)
    ;; val1 and val2 are Peano numerals    
    (== `(var ,val1, val2) x)
    (== `(var ,val1, val2) y)))

(define (var=/=o x y)
  (fresh (val11 val12 val21 val22)
    ;; `val1` and `val2` are Peano numerals
    (== `(var ,val11 ,val12) x)
    (== `(var ,val21 ,val22) y)
    (=/= (cons val11 val12) (cons val21 val22))))

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
	 (debug-gexpo
	  "\nunifyo:\n u: ~s\n v: ~s\n s: ~s\n s1: ~s\n\n"
	  u v s s1)
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
	  ;; 2 same var, 1 pair case (different vars for a d for unbound and f), 1 nil case, 1 true 1 false cases, 2 different 3615 and 3614 var cases (but seems to be the same since s1 is unbound for one and #f for the other)
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
    (debug-gexpo
     "\nbindo '():\n ge: ~s\n env: ~s\n store: ~s\n cont: ~s\n $-out: ~s\n\n"
     ge env store cont $-out)
    (apply-rel-ko cont (answer $-out store) mc out)]
   [(fresh (d)
	   (== `(delayed . ,d) $)
	   (== `(delayed bind ,$ ,ge ,env ,store) $-out)
	   (apply-rel-ko cont (answer $-out store) mc out))]
   [(fresh (s/c $-rst ge-out)
	   (== (cons s/c $-rst) $)
	   (=/= 'delayed s/c)
	   (debug-gexpo
	    "\nbindo:\n ge: ~s\n s/c: ~s\n env: ~s\n store: ~s\n cont: ~s\n $-out: ~s\n\n"
	    ge s/c env store cont $-out)
	   (eval-gexp-auxo ge s/c env store
			   (list 'bind-rec-k (list $-rst ge env $-out) cont)
			   mc out ge-out)
	   )]))

(define (literalo exp)
  (conde
   [(numbero exp)]
   [(booleano exp)]
   [(== '() exp)]))

(define (lengtho l len)
  (conde
    [(== '() l) (== '() len)]
    [(fresh (a d len-d)
       (== `(,a . ,d) l)
       (== `(,len-d) len)
       (lengtho d len-d))]))

(define (gen-addro env store new-addr)
  (fresh (names addrs vals addr)
	 (== (list names addrs) env)
	 (== (list addrs vals) store)	 
	 (lengtho names addr)
	 (lengtho addrs addr)
	 (lengtho vals addr)
	 (== (peano-incr addr) new-addr)
	 ))
(define (gen-addr*o env store len new-addr*)
  (fresh (start-addr len-d)
	 (gen-addro env store start-addr)
	 (== (peano-incr len-d) len)
	 (gen-addr*-auxo (list start-addr) len-d new-addr*)))
(define (gen-addr*-auxo addr* len new-addr*)
  (conde
   [(== len peano-zero)
    (== addr* new-addr*)]
   [(fresh (len-d addr addr^ addr*-rst addr*^)
	   (== (peano-incr len-d) len)
	   (== (peano-incr addr) addr^)
	   (== (cons addr addr*-rst) addr*)
	   (== (cons addr^ addr*) addr*^)
	   (gen-addr*-auxo addr*^ len-d new-addr*))]))


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
	   ;;(debug-gexpo
	    ;;"\neval-gexp lookup:\n rel: ~s\n s/c: ~s\n env: ~s\n store: ~s\n cont: ~s\n v-out: ~s\n\n"
	    ;;rel s/c env store cont v-out)
           (apply-rel-ko cont ans mc out))]
   [(fresh (rel-e args rel-val-ignore)
	   (== (cons rel-e args) gexp)
	   (debug-gexpo
	    "\neval-gexp:\n rel-e: ~s\n args: ~s\n s/c: ~s\n env: ~s\n store: ~s\n cont: ~s\n v-out: ~s\n\n"
	    rel-e args s/c env store cont v-out)
	   (eval-gexp-auxo rel-e s/c env store
			  (list 'application-rel-k (list args s/c env v-out) cont)
			  mc out rel-val-ignore))]))

(define (apply-rel-ko cont val/store mc out)
  (conde
   [(fresh (val store lv)
           (== 'id-cont cont)
	   (debug-gexpo
	    "\napply-rel-ko id-cont 0:\n val/store: ~s\n mc: ~s\n out: ~s\n\n"
	    val/store mc out)
	   (get-meta-level mc (peano-incr lv))
           (debug-gexpo
	    "\napply-rel-ko id-cont 1:\n val/store: ~s\n out: ~s\n\n"
	    val/store out)
	   ;; debugging showing out is tm, why?
	   (== (cons lv val/store) out)
	   (debug-gexpo
	    "\napply-rel-ko id-cont 2:\n val/store: ~s\n out: ~s\n\n"
	    val/store out)
           (== (answer val store) val/store))]
   [(fresh (args s/c env k rel store v-out)
	   (== (list 'application-rel-k (list args s/c env v-out) k) cont)
	   (== (answer rel store) val/store)
	   (conde
	    [(fresh (rel-subr-name)
		    (== rel (list 'rel-subr rel-subr-name))
		    (debug-gexpo
		     "\napplication-rel-k subro:\n subr-name: ~s\n 
args: ~s\n k: ~s\n v-out: ~s\n\n"
		     rel-subr-name args k v-out)
		    (apply-rel-subro rel-subr-name args s/c env store k mc out v-out))]
	    [(fresh (paras body env^ args^)
		    (== rel (list 'rel-abs paras body env^))
		    (tm-lookupo args env store args^) ; args with unification vars lookup
		    (apply-rel-abso paras body args^ s/c env^ store k mc out v-out))]
	    [(fresh (paras body)
		    (== rel (list 'muo-reifier paras body))
		    (apply-muo-reifiero paras body args s/c env store k mc out v-out))]
	    [(fresh (paras body)
		    (== rel (list 'muos-reifier paras body))
		    (apply-muos-reifiero paras body args s/c env store k mc out v-out))]))]
   [(fresh (g1-$ ge2 env store k v-out)
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
	   (debug-gexpo
	    "\nmplus-with-k:\n full-bind-out: ~s\n store: ~s\n k: ~s\n\n"
	    full-bind-out store k)
	   (apply-rel-ko k (answer full-bind-out store) mc out)
	   )]
   [(fresh ($1 $2 store k v-out)
	   (== (list 'mplus-k (list v-out) k) cont)
	   (== (answer (list $1 $2) store) val/store)
	   (mpluso $1 $2 v-out)
	   (apply-rel-ko k (answer v-out store) mc out))]
   [(fresh (s/c env k v-out store gexp*-rst $*-rst)
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
	   (== (answer v-out store) val/store)
	   (apply-exit-level-conto v-out mc out))]
   [(fresh (v1 v2 s/c k store sub count sub^ v-out ans)
	   (== (list 'unify-with-k (list v1 s/c) k) cont)
	   (== (answer v2 store) val/store)
	   (== (cons sub count) s/c)
	   (conde
            [(== #f sub^) (== '() v-out)]
            [(=/= #f sub^) (== `((,sub^ . ,count)) v-out)])
	   (debug-gexpo
	    "\nunify-with-k:\n v1: ~s\n v2: ~s\n sub: ~s\n store: ~s\n cont: ~s\n\n"
	    v1 v2 sub store k)
	   (unifyo v1 v2 sub sub^)
	   (debug-gexpo
	    "\nunify-with-k:\n v1: ~s\n v2: ~s\n store: ~s\n cont: ~s\n v-out: ~s\n\n"
	    v1 v2 store k v-out)
	   (== (answer v-out store) ans)
	   (apply-rel-ko k ans mc out)
	   )]
  
   ))

(define (apply-rel-subro rel-name args s/c env store cont mc out v-out)
  (conde
   [(fresh (arg1 arg2 v1 v2 sub count sub^ ans)
	   (== '==mk rel-name)
	   (== (list arg1 arg2) args)
	   (tm-lookupo arg1 env store v1)
	   (tm-lookupo arg2 env store v2)
	   (== (cons sub count) s/c)
	   (debug-gexpo
	    "\napply-rel-subr ==mk0:\n v1: ~s\n v2: ~s\n store: ~s\n cont: ~s\n\n"
	    v1 v2 store cont)
	   (conde
            [(== #f sub^) (== '() v-out)]
            [(=/= #f sub^) (== `((,sub^ . ,count)) v-out)])
	   (unifyo v1 v2 sub sub^)
	   (debug-gexpo
	    "\napply-rel-subr ==mk out:\n v1: ~s\n v2: ~s\n store: ~s\n cont: ~s\n v-out: ~s\n\n"
	    v1 v2 store cont v-out)
	   (== (answer v-out store) ans)
           (apply-rel-ko cont ans mc out))]
   [(fresh (ge1 ge2 ge1-$ ge$)
	   (== 'conj rel-name)
	   (== (list ge1 ge2) args)
	   (eval-gexp-auxo ge1 s/c env store
			   (list 'bind-k (list ge2 env v-out) cont)
			   mc out ge1-$))]
   [(fresh (ge1 ge2 ge1-ge2-$-lst)
	   (== 'disj rel-name)
	   (== (list ge1 ge2) args)
	   (eval-list-gexpo (list ge1 ge2) s/c env store
			   (list 'mplus-k (list v-out) cont)
			   mc out ge1-ge2-$-lst))]
   [(fresh (x1 new-addr ge sub count s/c^ env^ store^ lv)
	   (== 'call/fresh rel-name)
	   (== (list (list x1) ge) args)
	   (== (cons sub count) s/c)
	   (gen-addro env store new-addr)
	   (ext-envo x1 new-addr env env^)
	   
	   (get-meta-level mc (peano-incr lv))
	   (debug-gexpo
	    "\napply-rel-subr call/fresh 0:\n x1: ~s\n s/c: ~s\n env: ~s\n store: ~s\n cont: ~s\n v-out: ~s\n\n"
	    x1 s/c env store cont v-out)
	   (ext-storeo new-addr (list 'var lv count) store store^)
	   (symbolo x1)
	   (== (cons sub (peano-incr count)) s/c^)
	   (debug-gexpo
	    "\napply-rel-subr call/fresh:\n x1: ~s\n s/c^: ~s\n env^: ~s\n store^: ~s\n cont: ~s\n v-out: ~s\n\n"
	    x1 s/c^ env^ store^ cont v-out)
	   (eval-gexp-auxo ge s/c^
			   env^ store^
			   cont mc out v-out))]
   [(fresh (paras body ans)
	   (== 'rel-abs rel-name)
	   (== (list paras body) args)
	   (== (list 'rel-abs paras body env) v-out)
	   (== (answer v-out store) ans)
           (apply-rel-ko cont ans mc out))]
     
   [(fresh (paras body ans)
	   (== 'muo rel-name)
	   (== (list paras body) args)
	   (lengtho paras (peano 5))
	   (== (list 'muo-reifier paras body) v-out)
	   (== (answer v-out store) ans)
           (apply-rel-ko cont ans mc out))]
   [(fresh (paras body ans)
	   (== 'muos rel-name)
	   (== (list paras body) args)
	   (lengtho paras (peano 5))
	   (== (list 'muos-reifier paras body) v-out)
	   (== (answer v-out store) ans)
           (apply-rel-ko cont ans mc out))]
   [(fresh (e r st k out lv e^ r^ st^ k^ out^ cont^ meaning-out)
	   (== 'meaning-scmo rel-name)
	   (== (list e r st k out) args)
	   (tm-lookupo (list e r st k out) env store (list e^ r^ st^ k^ out^))
	   (get-meta-level mc (peano-incr lv))
	   (== (list 'unify-with-k (list out^ s/c) cont) cont^)
	   (meaning-scm-o e^ r^ st^ k^ (list 'kanren lv s/c env store cont^) mc out meaning-out)
	   )]
   [(fresh (e r st k lv e^ r^ st^ k^)
	   (== 'meaning-scm rel-name)
	   (== (list e r st k) args)
	   (tm-lookupo (list e r st k) env store (list e^ r^ st^ k^))
	   (get-meta-level mc (peano-incr lv))
	   (meaning-scm-o e^ r^ st^ k^ (list 'kanren lv s/c env store cont) mc out v-out)
	   )]
   [(fresh (e s/c-arg r st k lv e^ s/c^ r^ st^ k^)
	   (== 'meaning-mk rel-name)
	   (== (list e s/c-arg r st k) args)
	   (tm-lookupo (list e s/c-arg r st k) env store (list e^ s/c^ r^ st^ k^))
	   (get-meta-level mc (peano-incr lv))
	   (meaning-mk-o e^ s/c^ r^ st^ k^ (list 'kanren lv s/c env store cont) mc out v-out)
	   )]
   [(fresh (e lv e^)
	   (== 'eval-mk rel-name)
	   (== (list e) args)
	   (tm-lookupo e env store e^)
	   (get-meta-level mc (peano-incr lv))
	   (meaning-mk-o e^ s/c env store 'id-cont
			 (list 'kanren lv s/c env store cont) mc out v-out)
	   )]
   [(fresh (e lv e^ env^ store^)
	   (== 'eval-scm rel-name)
	   (== (list e) args)
	   (tm-lookupo e env store e^)
	   (get-meta-level mc (peano-incr lv))
	   (mk-r/st-to-scm-r/sto env store env^ store^)
	   (meaning-scm-o e^ env^ store^ 'id-cont
			  (list 'kanren lv s/c env store cont) mc out v-out)
	   )]
   [(fresh (e out lv e^ out^ meaning-out env^ store^ cont^)
	   (== 'eval-scmo rel-name)
	   (== (list e out) args)
	   (tm-lookupo (list e out) env store (list e^ out^))
	   (get-meta-level mc (peano-incr lv))
	   (mk-r/st-to-scm-r/sto env store env^ store^)
	   (== (list 'unify-with-k (list out^ s/c) cont) cont^)
	   (meaning-scm-o e^ env^ store^ 'id-cont (list 'kanren lv s/c env store cont^)
			  mc out meaning-out)
	   )]
   [(fresh (e lv e^)
	   (== 'open-scm rel-name)
	   (== (list e) args)
	   (tm-lookupo e env store e^)
	   (get-meta-level mc (peano-incr lv))
	   (meaning-scm-o e^ scm-init-env scm-init-store 'id-cont
			 (list 'kanren lv s/c env store cont) mc out v-out)
	   )]
   [(fresh (e lv e^)
	   (== 'open-mk rel-name)
	   (== (list e) args)
	   (tm-lookupo e env store e^)
	   (get-meta-level mc (peano-incr lv))
	   (meaning-mk-o e^ init-s/c mk-init-env mk-init-store 'id-cont
			 (list 'kanren lv s/c env store cont) mc out v-out)
	   )]
   
   [(fresh (e k e^ k^)
	   (== 'apply-cont-jmp rel-name)
	   (== (list k e) args)
	   (tm-lookupo (list k e) env store (list k^ e^))
	   (apply-rel-ko k^ (answer e^ store) mc out)
	   )]
   [(fresh (e k e^ k^ lv mc^)
	   (== 'apply-cont-psh rel-name)
	   (== (list k e) args)
	   (tm-lookupo (list k e) env store (list k^ e^))
	   (get-meta-level mc (peano-incr lv))
	   (== (cons (list 'kanren lv s/c env store cont) mc) mc^)
	   (apply-rel-ko k^ (answer e^ store) mc^ out)
	   )]))
(define (appendo l1 l2 l-out)
  (conde
   [(== '() l1) (== l2 l-out)]
   [(fresh (v l1-rst l-out-rst)
           (== (cons v l1-rst) l1)
           (== (cons v l-out-rst) l-out)
           (appendo l1-rst l2 l-out-rst))]))

(define (mk-r/st-to-scm-r/sto env store env^ store^)
  (fresh (name* addr* content* name*^ addr*^ content*^
		new-name* new-content* len)
	 (== (list name* addr*) env)
	 (== (list addr* content*) store)
	 (== (list name*^ addr*^) env^)
	 (== (list addr*^ content*^) store^)
	 (appendo new-name* mk-init-env-names name*)
	 (appendo new-content* mk-init-store-contents content*)
	 (appendo new-name* scm-init-env-names name*^)
	 (appendo new-content* scm-init-store-contents content*^)
	 (lengtho name*^ len)
	 (lengtho content*^ len)
	 (peano-iotao len addr*^)))
(define (apply-exit-level-conto v-out mc out)
  (conde
   [(fresh (upper-s/c upper-env upper-store upper-cont
		      upper-level upper-meta-cont forced-mc)
	   (== (cons (list 'kanren upper-level upper-s/c upper-env upper-store upper-cont)
		     upper-meta-cont) forced-mc)
	   (meta-cont-forceo mc forced-mc)
	   (debug-printfo
	    "\nexit-level:\n v-out: ~s\n upper-store: ~s\n upper-cont: ~s\n\n"
	    v-out upper-store upper-cont)
	   (apply-rel-ko upper-cont (cons v-out upper-store) upper-meta-cont out)
           )]
   [(fresh (upper-env upper-store upper-cont upper-level upper-meta-cont forced-mc)
	   (== (cons (list 'scheme upper-level upper-env upper-store upper-cont)
		     upper-meta-cont) forced-mc)
	   (meta-cont-forceo mc forced-mc)
	   (apply-ko upper-cont (cons v-out upper-store) upper-meta-cont out)
           )]))
(define (tm-lookupo tm env store tm^)
  (conde
   [(== (list 'quote tm^) tm)]
   [(literalo tm)
    (== tm tm^)]
   [(symbolo tm)
    (lookupo tm env store tm^)
    (debug-gexpo
     "\ntm-lookupo:\n tm: ~s\n env: ~s\n store: ~s\n tm^: ~s\n\n"
     tm env store tm^)]
   [(fresh (tm1 tm2 tm1^ tm2^)
	   (=/= 'quote tm1)
	   (== (cons tm1 tm2) tm)
	   (== (cons tm1^ tm2^) tm^)
	   (debug-gexpo
	    "\ntm-lookupo compound:\n tm: ~s\n tm^: ~s\n\n"
	    tm tm^)
	   (tm-lookupo tm1 env store tm1^)
	   (tm-lookupo tm2 env store tm2^))]))
    
(define (eval-list-gexpo gexp* s/c env store cont mc out $*)
  (conde
    [(fresh (ans)
         (== '() gexp*)
         (== '() $*)
         (== (answer '() store) ans)
         (apply-rel-ko cont ans mc out))]
    [(fresh (gexp gexp-rst $1 $-rst)
	    (== (cons gexp gexp-rst) gexp*)
	    (== (cons $1 $-rst) $*)
	    (eval-gexp-auxo gexp s/c env store
			    (list 'eval-list-k (list gexp-rst env s/c $-rst) cont)
			    mc out $1))]))

(define (apply-rel-abso para* body arg-val* s/c env store cont mc out $)
  (fresh (arg-num addr* env^ store^)
	 (lengtho para* arg-num)
	 (gen-addr*o env store arg-num addr*)
	 (exts-envo para* addr* env env^)
	 (exts-storeo addr* arg-val* store store^)
	 ;;(peano*o addr*)
	 (symbol*o para*)
	 (not-in-store*o store addr*)
	 (eval-gexp-auxo body s/c env^ store^ cont mc out $)))
(define (peano*o ns)
  (conde
   [(== ns '())]
   [(fresh (n ns-rst)
	   (== (cons n ns-rst) ns)
	   (peano-no n)
	   (peano*o ns-rst))]))
(define (symbol*o ids)
  (conde
   [(== ids '())]
   [(fresh (id ids-rst)
	   (== (cons id ids-rst) ids)
	   (symbolo id)
	   (symbol*o ids-rst))]))
(define (not-in-storeo store addr)
  (fresh (addr*)
	 ;;(peano-no addr)
	 (store->addr*o store addr*)
	 (absento addr addr*)))
	 
	 
(define (not-in-store*o store addrs)
  (fresh (addr*)
	 (store->addr*o store addr*)
	 (no-same-addrs addr* addrs)))

(define (no-same-addrs addrs1 addrs2)
  (conde
   [(== addrs2 '())]
   [(fresh (addr addrs2-rst)
	   (== (cons addr addrs2-rst) addrs2)
	   ;;(peano-no addr)
	   (absento addr addrs1)
	   (no-same-addrs addrs1 addrs2-rst))]))

(define (apply-muo-reifiero para* body args s/c env store cont mc out $)
  (fresh (upper-s/c upper-env upper-store upper-cont
		    upper-level upper-meta-cont forced-mc
		    addr* env-res store-res)
	 (lengtho para* (peano 5))
	 (symbol*o para*)
	 (== (cons (list 'kanren upper-level upper-s/c upper-env upper-store upper-cont)
		   upper-meta-cont) forced-mc)
	 (gen-addr*o upper-env upper-store (peano 5) addr*)
	 (exts-envo para* addr* upper-env env-res)
	 (exts-storeo addr* (list args s/c env store cont) upper-store store-res)
	 (meta-cont-forceo mc forced-mc)
	 (eval-gexp-auxo body upper-s/c env-res store-res upper-cont upper-meta-cont out $)
	 ))
(define (apply-muos-reifiero para* body args s/c env store cont mc out v-out)
  (fresh (upper-level upper-env upper-store upper-cont upper-meta-cont
		      forced-mc addr* env-res store-res)
	 (lengtho paras (peano 5))
	 (symbol*o para*)
	 (== (cons (list 'scheme upper-level upper-env upper-store upper-cont) upper-meta-cont)
	     forced-mc)
	 (gen-addr*o upper-env upper-store (peano 5) addr*)
	 (exts-envo para* addr* upper-env env-res)
	 (exts-storeo addr* (list args s/c env store cont) upper-store store-res)
	 (meta-cont-forceo mc forced-mc)
	 (eval-scm-auxo body env-res store-res upper-cont upper-meta-cont out v-out)
	 ))
#|
(define (reify-s/co s/c s/c^)
  (== `(reified-s/c ,s/c) s/c^))
(define (reify-envo env env^)
  (== `(reified-env ,env) env^))
(define (reify-storeo store store^)
  (== `(reified-store ,store) store^))
(define (reify-conto cont cont^)
  (== `(reified-cont ,cont) cont^))

|#

(define  (meaning-scm-o e r st k cur-level mc out v-out)
  (fresh (e-out new-mc new-k)
	 (== (cons cur-level mc) new-mc)
	 (add-end-conto k (list 'exit-level-k v-out) new-k)
	 ;;(reify-envo r^ r)
	 ;;(reify-storeo st^ st)
	 ;;(reify-storeo k^ k)
	 (eval-scm-auxo e r st new-k new-mc out e-out)
	 ))
(define (meaning-mk-o e s/c r st k cur-level mc out $)
  (fresh (e-out new-mc new-k)
	 (== (cons cur-level mc) new-mc)
	 (add-end-conto k (list 'exit-level-k $) new-k)
	 (eval-gexp-auxo e s/c r st new-k new-mc out e-out)
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
	     (literalo exp)
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
	      "\neval-scm-auxo:\n exp: ~s\n env: ~s\n store: ~s\n cont: ~s\n v-out: ~s\n\n"
	      exp env store cont v-out)
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
             ;;(peano-no addr)
             (exts-storeo addr v store store^)
             (lookup-env-only-auxo x env addr)
             (apply-ko k (answer 'void store^) mc out)
             )]
     [(fresh (env k e-v r-v st-v k-v store v-out level)
	     (== (list 'spawn-scm-k (list env v-out) k) cont)
	     (== (answer (list e-v r-v st-v k-v) store) v/s)
	     (meaning-scm-o e-v r-v st-v k-v
			    (list 'scheme level env store k) mc out v-out))]
     [(fresh (env k e-v s/c-v r-v st-v k-v store v-out level)
	     (== (list 'spawn-mk-k (list env v-out) k) cont)
	     (== (answer (list e-v s/c-v r-v st-v k-v) store) v/s)
	     (meaning-mk-o e-v s/c-v r-v st-v k-v
			   (list 'scheme level env store k) mc out v-out))]
     [(fresh (env k e-v store v-out level)
	     (== (list 'open-mk-k (list env v-out) k) cont)
	     (== (answer e-v store) v/s)
	     (meaning-mk-o e-v init-s/c mk-init-env mk-init-store
			   'id-cont (list 'scheme level env store k) mc out v-out))]
     [(fresh (k e r st store v-out)
	     (== (list 'rei-lookup-k (list v-out) k) cont)
	     (== (answer (list e r st) store) v/s)
	     (lookupo e r st v-out)
	     (debug-printfo
	      "\nrei-lookup-k:\n e: ~s\n r: ~s\n st: ~s\n k: ~s\n v-out: ~s\n\n"
	      e r st k v-out)
	     (apply-rel-ko k (answer v-out store) mc out))]
     [(fresh (ids addrs let-args-vals body env store k env^ store^ v-out)
	     (== (list 'let-k (list ids body) k) cont)
	     (== (answer let-args-vals store) v/s)
	     (exts-envo ids addrs env env^)
	     (exts-storeo addrs let-args-vals store store^)
	     ;;(peano*o addrs)
	     (symbol*o ids)
	     (not-in-store*o store addrs)
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
			   (list 'spawn-scm-k (list env v-out) cont)
			   mc out spawn-args))]
   [(fresh (e s/c-arg r st k spawn-args)
	   (== 'meaning-mk fsubr-name)
	   (== (list e s/c-arg r st k) args)
	   (eval-list-scmo (list e s/c-arg r st k) env store
			   (list 'spawn-mk-k (list env v-out) cont)
			   mc out spawn-args))]
   [(fresh (e e-v)
	   (== 'open-mk fsubr-name)
	   (== (list e) args)
	   (eval-scm-auxo e env store
			  (list 'open-mk-k (list env v-out) cont)
			  mc out e-v)
	   
	   )]
   [(fresh (e r st e^ r^ st^ e-res args-vals)
	   (== 'rei-lookup fsubr-name)
	   (== (list e r st) args)
	   (eval-list-scmo args env store
			   (list 'rei-lookup-k (list v-out) cont)
			   mc out args-vals))]
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
	 ;;(peano*o addrs)
	 (symbol*o paras)
	 (not-in-store*o store addrs)
	 (eval-scm-auxo body env^ store^ cont mc out v-out) 
	 ))
(define (apply-muso-reifier paras body args env store cont mc out $)
  (fresh (e-para r-para st-para k-para
		 upper-level upper-s/c upper-env upper-store upper-cont upper-meta-cont
		 forced-mc env-res)
	 (== paras (list e-para r-para st-para k-para))
	 (== (cons (list 'kanren upper-level upper-s/c upper-env upper-store upper-cont)
		   upper-meta-cont) forced-mc)
	 (exts-s/co paras (list args env store cont) upper-s/c s/c-res)
	 (meta-cont-forceo mc forced-mc)
	 (eval-gexp-auxo body s/c-res upper-env upper-store upper-cont upper-meta-cont out $)
	 ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;; Interfacing with Scheme ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



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



(define (walk*o unwalked-v s u)
  (fresh (v)
    (walko unwalked-v s v)
    (conde
      [(== v u)
       (conde
         [(var?o v)]
         [(symbolo v)]
         [(literalo v)])]
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
        [(symbolo v)]
	[(literalo v)])]
      [(fresh (a d sa)
         (=/= 'var a)
         (== `(,a . ,d) v)
         (conde
           [(== '_. a)
            (== s s1)]
           [(=/= '_. a)
            (reify-so a s sa)
            (reify-so d sa s1)]))])))

(define (reify-state/1st-varo s/c lv out)
  (fresh (s c v u)
	 (== `(,s . ,c) s/c)
	 (debug-gexpo
	  "\nreify-state/1st-varo 0:\n s/c: ~s\n lv: ~s\n\n"
	  s/c lv)
	 (walk*o `(var ,lv ()) s v)
	 (reify-so v '() u)
	 (debug-gexpo
	  "\nreify-state/1st-varo 1:\n v: ~s\n u: ~s\n\n"
	  v u)
	 (walk*o v u out)
	 (debug-gexpo
	  "\nreify-state/1st-varo 2:\n out: ~s\n\n"
	  out)))

(define (reifyo s/c* lv out)
    (conde
     [(== '() s/c*) (== '() out)
      (debug-gexpo
       "\nreifyo:\n s/c*: ~s\n out: ~s\n\n"
       s/c* out)]
      [(fresh (a d va vd)
         (== `(,a . ,d) s/c*)
         (== `(,va . ,vd) out)
         (reify-state/1st-varo a lv va)
	 (debug-gexpo
	  "\nreifyo:\n a: ~s\n va: ~s\n d: ~s\n vd: ~s\n\n"
	  a va d vd)
         (reifyo d lv vd))]))

(define mk-init-env-names
  '(==mk conj disj call/fresh
	  rel-abs muo muos
	  meaning-scm
	  meaning-mk
	  eval-scm
	  eval-scmo
	  open-scm
	  open-mk))
(define mk-init-store-contents
  '((rel-subr ==mk)
    (rel-subr conj)
    (rel-subr disj)
    (rel-subr call/fresh)
    (rel-subr rel-abs)
    (rel-subr muo)
    (rel-subr muos)
    (rel-subr meaning-scm)
    (rel-subr meaning-mk)
    (rel-subr eval-scm)
    (rel-subr eval-scmo)
    (rel-subr open-scm)
    (rel-subr open-mk)
    ))

(define scm-init-env-names
  '(quote set! lambda list muso meaning-scm meaning-mk open-mk rei-lookup let letrec))
(define scm-init-store-contents
  '((fsubr quote)
    (fsubr set!)
    (fsubr lambda)
    (fsubr list)
    (fsubr muso)
    (fsubr meaning-scm)
    (fsubr meaning-mk)
    (fsubr open-mk)
    (fsubr rei-lookup)
    (fsubr let)
    (fsubr letrec)))
(define (iota n)
  (if (= n 0) '()
      (cons n (iota (- n 1)))))
(define mk-init-env
  (list mk-init-env-names (iota (length mk-init-env-names))))
(define scm-init-env
  (list scm-init-env-names (iota (length scm-init-env-names))))
(define mk-init-store
  (list (iota (length mk-init-store-contents)) mk-init-store-contents))
(define scm-init-store
  (list (iota (length scm-init-store-contents)) scm-init-store-contents))

(define init-s/c
  (let ((empty-sub '()))
    `(,empty-sub . ,peano-zero)))

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
  (== `((kanren ,level ,init-s/c ,mk-init-env ,mk-init-store id-cont)
	(kanren ,(peano-incr level) ,init-s/c ,mk-init-env ,mk-init-store id-cont)
	(scheme ,(peano-incr (peano-incr level)) ,scm-init-env ,scm-init-store id-cont)
	. (next-meta-cont ,(peano-incr (peano-incr (peano-incr level))))) mc))
(define (get-meta-level mc lv)
  (fresh (fc lang s/c env store cont fc^)
	 (meta-cont-forceo mc fc)
	 (debug-gexpo
	  "\nget-meta-level 0:\n lv: ~s\n mc: ~s\n fc: ~s\n\n"
	  lv mc fc)
	 (conde
	  [(== `((kanren
		,lv ,s/c ,env
		,store ,cont)
		 . ,fc^) fc)]
	  [(== `((scheme
		,lv ,env
		,store ,cont)
		 . ,fc^) fc)
	   (debug-gexpo
	    "\nget-meta-level 1:\n lv: ~s\n mc: ~s\n fc: ~s\n\n"
	    lv mc fc)])))
(define (runo answer-count gexp out)
  (fresh (mc^ mc init-env init-store)
	 (gen-meta-conto peano-zero mc^)
	 (== `((kanren
		,peano-zero ,init-s/c ,init-env
		,init-store id-cont)
	       . ,mc) mc^)
	 (conde
	  [(fresh (lv lv/$/s st $ s/c* v*)
		  (== answer-count 'all)
		  (eval-gexp-auxo gexp init-s/c
				  init-env init-store 'id-cont mc lv/$/s $)
		  (== (cons lv (cons $ st)) lv/$/s)
		  (take-allo $ mc s/c*)
		  (debug-gexpo
		   "\nruno 0:\n lv: ~s\n $: ~s\n s/c*: ~s\n\n"
		   lv $ s/c*)
		  (reifyo s/c* lv v*)
		  (== (list 'level: lv 'result: v*) out)
		  (debug-gexpo
		   "\nruno 1:\n lv: ~s\n v*: ~s\n out: ~s\n\n"
		   lv v* out)
		  )]
	  [(fresh (n lv lv/$/s st $ s/c* v*)
		  (=/= answer-count 'all)
		  (eval-gexp-auxo gexp init-s/c
				  init-env init-store 'id-cont mc lv/$/s $)
		  (== (cons lv (cons $ st)) lv/$/s)
		  (debug-gexpo
		   "\nruno 0:\n lv: ~s\n $: ~s\n s/c*: ~s\n\n"
		   lv $ s/c*)
		  (take-no answer-count $ mc s/c*)
		  (reifyo s/c* lv v*)
		  (debug-gexpo
		   "\nruno 1:\n lv: ~s\n v*: ~s\n out: ~s\n\n"
		   lv v* out)
		  (== (list 'level: lv 'result: v*) out))])))
