;; difference between this file and relational-cesk:
;; added lookup for s/c
;; addresses represented by peano numbers

(define debug #f)
(define debug-printfo
  (lambda args
    (lambda (st)
  (if debug
      (begin
        (apply printf (map (lambda (x) (walk* x (state-S st))) args))
        st)
      st))))


(define peano-zero '())
(define (peano-incr n) `(,n))
(define (peano n)
  (if (zero? n) '() `(,(peano (- n 1)))))
(define (peano-no n)
  (conde
   [(== peano-zero n)]
   [(fresh (n-d)
	   (== (peano-incr n-d) n)
	   (peano-no n-d))]))
	 

(define empty-s/c '(() ()))
(define empty-env '(() ()))
(define empty-store '(() ()))

(define exts-s/co
  (lambda (xs tms s/c s/c^)
    (conde
     ((== '() xs)
      (== '() tms)
      (== s/c s/c^))
     ((fresh (x tm xs-rst tms-rst s/c-tmp)
	     (== (cons x xs-rst) xs)
	     (== (cons tm tms-rst) tms)
	     (ext-s/co x tm s/c s/c-tmp)
	     (exts-s/co xs-rst tms-rst s/c-tmp s/c^)
	     ))
     )))
(define ext-s/co
  (lambda (x tm s/c s/c^)
    (fresh (x* tm*)
	   (== `(,x* ,tm*) s/c)
	   (== `((,x . ,x*) (,tm . ,tm*)) s/c^)
	   (symbolo x))))
(define exts-envo
  (lambda (xs addrs env env^)
    (conde
     [(== '() xs)
      (== '() addrs)
      (== env env^)]
     [(fresh (x addr xs-rst addrs-rst env-tmp)
	     (== (cons x xs-rst) xs)
	     (== (cons addr addrs-rst) addrs)
	     (ext-envo x addr env env-tmp)
	     (exts-envo xs-rst addrs-rst env-tmp env^)
	     )])))
(define ext-envo
  (lambda (x addr env env^)
    (fresh (x* addr*)
	   (== `(,x* ,addr*) env)
	   (== `((,x . ,x*) (,addr . ,addr*)) env^)
	   ;;(peano-no addr)
	   (symbolo x))))
(define exts-storeo
  (lambda (addrs vs store store^)
    (conde
     [(== '() addrs)
      (== '() vs)
      (== store store^)]
     [(fresh (addr v addrs-rst vs-rst store-tmp)
	     (== (cons addr addrs-rst) addrs)
	     (== (cons v vs-rst) vs)
	     (ext-storeo addr v store store-tmp)
	     (exts-storeo addrs-rst vs-rst store-tmp store^)
	     )])))
(define ext-storeo
  (lambda (addr v store store^)
    (fresh (addr* v*)
	   (== `(,addr* ,v*) store)
	   (== `((,addr . ,addr*) (,v . ,v*)) store^)
	   ;;(peano-no addr)
	   )))

(define x*/addr*-envo
  (lambda (x* a* env)
    (== `(,x* ,a*) env)))

(define addr*/val*-storeo
  (lambda (a* v* store)
    (== `(,a* ,v*) store)))

(define env->x*o
  (lambda (env x*)
    (fresh (a*)
	   (== `(,x* ,a*) env))))

(define env->addr*o
  (lambda (env a*)
    (fresh (x*)
	   (== `(,x* ,a*) env))))

(define store->addr*o
  (lambda (store a*)
    (fresh (v*)
	   (== `(,a* ,v*) store))))

(define store->val*o
  (lambda (store v*)
    (fresh (a*)
	   (== `(,a* ,v*) store))))




(define lookupo
  (lambda (x env store t)
    (fresh (addr)
	   (symbolo x)
	   ;;(peano-no addr)
	   (debug-printfo
	    "\nlookupo:\n x: ~s\n env: ~s\n store: ~s\n t: ~s\n\n"
	    x env store t)
	   (lookup-env-auxo x env store addr)
	   (lookup-store-auxo addr store t))))

(define lookup-env-auxo
;;; it may be possible to avoid having to bound the length of env to
;;; be no greater than the length of store through clever use of
;;; noo/absento.  For now, however, we'll stick with the bound.
  (lambda (x env store t)
    (fresh (y y* addr-e addr-e* addr-s addr-s* v-s v-s*)      
	   (== `((,y . ,y*) (,addr-e . ,addr-e*)) env)
	   (== `((,addr-s . ,addr-s*) (,v-s . ,v-s*)) store)
	   (symbolo x)
	   (symbolo y)
	   ;;(peano-no t)
	   ;;(peano-no addr-e)
	   ;;(peano-no addr-s)
	   (debug-printfo
	    "\nlookup-env-auxo:\n x: ~s\n env: ~s\n store: ~s\n addr: ~s\n\n"
	    x env store t)
	   (conde
            ((== y x) (== addr-e t))
            ((=/= y x)
             (lookup-env-auxo x `(,y* ,addr-e*) `(,addr-s* ,v-s*) t))))))

(define lookup-env-only-auxo
  (lambda (x env t)
    (fresh (y y* addr-e addr-e*)
	   (== `((,y . ,y*) (,addr-e . ,addr-e*)) env)
	   (symbolo x)
	   (symbolo y)
	   ;;(peano-no t)
	   ;;(peano-no addr-e)
	   (conde
            ((== y x) (== addr-e t))
            ((=/= y x)
             (lookup-env-only-auxo x `(,y* ,addr-e*) t))))))

(define lookup-store-auxo
  (lambda (addr store t)
    (fresh (addr-s addr-s* v-s v-s*)
	   (== `((,addr-s . ,addr-s*) (,v-s . ,v-s*)) store)
	   ;;(peano-no addr)
	   ;;(peano-no addr-s)
	   (debug-printfo
	    "\nlookup-store-auxo:\n x: ~s\n env: ~s\n t: ~s\n\n"
	    addr store t)
	   (conde
            ((== addr-s addr) (== v-s t))
            ((=/= addr-s addr)
             (lookup-store-auxo addr `(,addr-s* ,v-s*) t))))))

 ;; )
;;(library (lookupo-lib)
  ;;(export empty-env empty-store ext-envo ext-storeo x*/addr*-envo addr*/val*-storeo env->x*o env->addr*o store->addr*o store->val*o lookupo lookup-env-auxo lookup-env-only-auxo lookup-store-auxo)
  ;;(import (rnrs) (mk-lib))
