(library (mkit)
  (export run run* run+ tabled == occurs-check conde exist)
  (import (rnrs) (rnrs records syntactic))

  (define-record-type data (fields (mutable queue) (mutable answers) (mutable resumers)))
  (define (add-answer! data ansv)
    (data-answers-set! data `(,ansv . ,(data-answers data)))
#;  (printf "\nadded answer\n~a\n" data))
  (define (add-resumer! data k)
    (data-resumers-set! data `(,k . ,(data-resumers data)))
#;  (printf "\nadded resumer\n~a\n" data))

  (define-record-type var (fields s))

  (define reify-name
    (lambda (n) (string->symbol (string-append "_." (number->string n)))))

  (define reify-var
    (lambda (s)
      (lambda (n) (make-var s))))

  (define-syntax trample
    (syntax-rules ()
      ((_ e) (lambda () e))))

  (define fail '())

  (define subunify
    (lambda (arg ans s)
      (let ((arg (stored-shrink-walk arg s)))
        (cond
          ((eq? arg ans) s)
          ((var? arg) (ext-s-no-check arg ans s))
          ((pair? arg) (subunify (cdr arg) (cdr ans)
                         (subunify (car arg) (car ans) s)))
          (else s)))))

  (define reuse
    (lambda (argv ansv s)
      (subunify argv ((reify (reify-var s)) ansv s) s)))

  (define subsumed
    (lambda (arg ans s)
      (let ((arg (stored-shrink-walk arg s))
            (ans (stored-shrink-walk ans s)))
        (cond
          ((eq? arg ans) s)
          ((var? ans) (ext-s ans arg s))
          ((and (pair? arg) (pair? ans))
           (let ((s (subsumed (car arg) (car ans) s)))
             (and s (subsumed (cdr arg) (cdr ans) s))))
          ((equal? arg ans) s)
          (else #f)))))

  (define master
    (lambda (data argv)
      (let ((queue (data-queue data)))
        (cond
          ((null? queue) fail)
          (else
            (data-queue-set! data '())
            `((,(lambda (queue) (data-queue-set! data queue))
                . ,(trample (master data argv)))
              . (,queue . ())))))))

  (define consume
    (lambda (argv s sk data)
      (let ((resumer (lambda (ansv)
                       (trample (sk (reuse argv ansv s))))))
        (add-resumer! data resumer)
        `(#f ,(master data argv)
           . ,(map resumer (data-answers data))))))

  (define installing-sk
    (lambda (argv data)
      (lambda (s)
        (if (exists (lambda (ansv) (subsumed argv ansv s))
              (data-answers data))
          fail
          (let ((ansv ((reify (reify-var s)) argv s)))
            (add-answer! data ansv)
            `(#f . ,(map (lambda (k) (k ansv)) (data-resumers data))))))))

  (define-syntax tabled
    (syntax-rules ()
      ((_ (a ...) g g* ...)
       (let ((table '()))
         (lambda (a ...)
           (let ((argv `(,a ...)))
             (lambda (s sk)
               (let ((key ((reify reify-name) argv s)))
                 (consume argv s sk
                   (cond ((assoc key table) => cdr)
                     (else (let ((data (make-data '() '() '())))
                             (data-queue-set! data
                               `(,(trample
                                    ((exist () g g* ...) s
                                     (installing-sk argv data)))))
                             (set! table `((,key . ,data) . ,table))
                             data))))))))))))

  (define empty-s '())

  (define-syntax conde
    (syntax-rules ()
      ((_ (g))
       (lambda (s sk)
         (trample (g s sk))))
      ((_ (g g* ...))
       (lambda (s sk)
         (trample
           (g s
             (lambda (s)
               (trample
                 ((conde (g* ...)) s sk)))))))
      ((_  (g0 g0* ...) (g1 g1* ...) ...)
       (lambda (s sk)
         `(#f
            ,(trample ((conde (g0 g0* ...)) s sk))
            ,(trample ((conde (g1 g1* ...)) s sk))
            ...)))))

  (define-syntax exist
    (syntax-rules ()
      ((_ (x ...) g g* ...)
       (lambda (s sk)
         (trample
           (let ((x (make-var s)) ...)
             ((conde (g g* ...)) s sk)))))))

  (define ==
    (lambda (u v)
      (lambda (s sk)
        (trample
          (cond
            ((unify u v s) => sk)
            (else fail))))))

  (define taker
    (lambda (queue sk fk)
      (if (null? queue) '()
        (let ((th (car queue)) (queue (cdr queue)))
          (cond
            ((and (pair? th) (pair? (car th)))
             (let ((finish! (caar th)) (old (cadr th))
                   (restart (cdar th)) (new (cddr th)))
               (if (null? old)
                 (let ((wen (reverse new)))
                   (finish! wen)
                   (if (null? wen)
                     (fk queue)
                     (fk `(,@queue ,restart))))
                 (taker `(,(car old))
                   (lambda (a new+)
                     (sk a `((,(car th) . (,(cdr old) . (,@new+ . ,new))) . ,queue)))
                   (lambda (new+)
                     (fk `((,(car th) . (,(cdr old) . (,@new+ . ,new))) . ,queue)))))))
            ((and (pair? th) (car th))
             (sk (cdr th) queue))
            (else
              (fk (cond
                    ((null? th) queue)
                    ((pair? th) `(,@(cdr th) . ,queue))
                    (else `(,@queue ,(th)))))))))))

  (define take
    (lambda (n)
      (lambda (ths)
        (if (zero? n) '()
          (taker ths
            (lambda (a ths) `(,a . ,((take (- n 1)) ths)))
            (take n))))))

  (define take*
    (lambda (ths)
      (taker ths
        (lambda (a ths) `(,a . ,(take* ths)))
        take*)))

  (define take+
    (lambda (ths)
      (taker ths
        (lambda (a ths) `(,a . ,(lambda () (take+ ths))))
        take+)))

  (define-syntax run
    (syntax-rules ()
      ((_ e (q) g g* ...)
       (let ((n e))
         (unless (or (boolean? n) (and (integer? n) (exact? n) (positive? n)))
           (assertion-violation 'run "not an exact positive integer" n))
         ((cond ((number? n) (take n)) (n take+) (else take*))
          (list
            ((exist (q)
               g g* ...
               (lambda (s sk)
                 (sk ((reify reify-name) q s))))
             empty-s
             (lambda (a) `(#t . ,a)))))))))

  (define-syntax run*
    (syntax-rules ()
      ((_ (q) g g* ...)
       (run #f (q) g g* ...))))

  (define-syntax run+
    (syntax-rules ()
      ((_ (q) g g* ...)
       (run #t (q) g g* ...))))

  (define stored-shrink-walk
    (lambda (v start)
      (let loop ((v v) (s start) (end '()))
        (if (or (not (var? v))
              (eq? s (var-s v))
              (eq? s end))
          v
          (if (eq? (caar s) v)
            (loop (cdar s) start (cdr s))
            (loop v (cdr s) end))))))

  (define shrink-walk
    (lambda (v start)
      (let loop ((v v) (s start) (end '()))
        (if (or (not (var? v))
              (eq? s end))
          v
          (if (eq? (caar s) v)
            (loop (cdar s) start (cdr s))
            (loop v (cdr s) end))))))

  (define assq-walk ; not used
    (lambda (v s)
      (cond
        ((and (var? v) (assq v s))
         => (lambda (p) (assq-walk (cdr p) s)))
        (else v))))

  (define walk*
    (lambda (walk)
      (lambda (t s)
        (let walk* ((t t))
          (let ((t (walk t s)))
            (if (pair? t)
              (cons
                (walk* (car t))
                (walk* (cdr t)))
              t))))))

  (define reify
    (lambda (rep)
      (lambda (t s)
        (let ((t ((walk* stored-shrink-walk) t s)))
          (let ((s (reify-vars rep t)))
            ((walk* shrink-walk) t s))))))

  (define reify-vars
    (lambda (rep t)
      (let rec ((t t) (s '()))
        (cond
          ((and (var? t) (not (assq t s)))
           (cons (cons t (rep (length s))) s))
          ((pair? t) (rec (cdr t) (rec (car t) s)))
          (else s)))))

  (define occurs?
    (lambda (x t)
      (or (eq? x t)
        (and (pair? t)
          (or
            (occurs? x (car t))
            (occurs? x (cdr t)))))))

  (define ext-s-no-check
    (lambda (x v s)
      (cons (cons x v) s)))

  (define ext-s-check
    (lambda (x v s)
      (and (not (occurs? x v))
        (ext-s-no-check x v s))))

  (define ext-s ext-s-check)

  (define occurs-check
    (let ((f #t))
      (case-lambda
        (() f)
        ((b) (unless (boolean? b) (assertion-violation 'occurs-check "not a boolean" b))
         (set! f b) (set! ext-s (if f ext-s-check ext-s-no-check))))))

  (define unify
    (lambda (v w s)
      (let ((v (stored-shrink-walk v s))
            (w (stored-shrink-walk w s)))
        (cond
          ((eq? v w) s)
          ((var? v) (ext-s v w s))
          ((var? w) (ext-s w v s))
          ((and (pair? v) (pair? w))
           (let ((s (unify (car v) (car w) s)))
             (and s (unify (cdr v) (cdr w) s))))
          ((equal? v w) s)
          (else #f))))))
