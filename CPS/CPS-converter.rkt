(module CPS-converter
  (lib "eopl.ss" "eopl")
  (require "../cha1.rkt")
  (provide cps-of-program)
;;;;;;;;;;;;;lang;;;;;;;;;;;;;;;;;;;;;;
  (define the-lexical-spec
    '((whitespace (whitespace) skip)
      (comment ("%" (arbno (not #\newline))) skip)
      (identifier
       (letter (arbno (or letter digit "_" "-" "?")))
       symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      ))
  
  (define the-grammar
    '(
      ;;;;;;;;;;;;;;;;CPS-IN;;;;;;;;;;;;;;;;;;;;;
      (program (InpExp) a-program)
      
      (InpExp
       ("emptylist")
       emptylist-exp)
      
      (InpExp
       ("cons" "(" InpExp "," InpExp ")")
       cons-exp)

      (InpExp
       ("list" "(" (arbno InpExp) ")")
       list-exp)
      
      (InpExp
       ("car" "(" InpExp ")")
       car-exp)
      
      (InpExp
       ("cdr" "(" InpExp ")")
       cdr-exp)
      
      (InpExp
       ("zero?" "(" InpExp ")")
       zero?-exp)
      
      (InpExp
       ("null?" "(" InpExp ")")
       null?-exp)

      (InpExp
       ("number?" "(" InpExp ")")
       number?-exp)

      (InpExp
       ("equal?" "(" InpExp "," InpExp ")")
       equal?-exp)
      
      (InpExp (number) const-exp)
      
      (InpExp
       ("-" "(" InpExp "," InpExp ")")
       diff-exp)
      
      (InpExp
       ("*" "(" InpExp "," InpExp ")")
       mult-exp)

      (InpExp
       ("+" "(" (separated-list InpExp ",") ")")
       sum-exp)
      
      (InpExp
       ("if" InpExp "then" InpExp "else" InpExp)
       if-exp)

      (InpExp (identifier) var-exp)

      (InpExp
       ("let" (arbno identifier "=" InpExp) "in" InpExp)
       let-exp)

      (InpExp
       ("proc" "(" (arbno identifier) ")" InpExp)
       proc-exp)

      (InpExp
       ("(" InpExp (arbno InpExp) ")")
       call-exp)

      (InpExp
       ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" InpExp) "in" InpExp)
      letrec-exp)
      ;;;;;;;;;;;;;;;;CPS-OUT;;;;;;;;;;;;;;;;;;;;;
      (cps-program (TfExp) cps-a-program)
      
      (SimpleExp (number) cps-const-exp)

      (SimpleExp (identifier) cps-var-exp)
      
      (SimpleExp
       ("-" "(" SimpleExp "," SimpleExp ")")
       cps-diff-exp)
      
      (SimpleExp
       ("*" "(" SimpleExp "," SimpleExp ")")
       cps-mult-exp)
      
      (SimpleExp
       ("+" "(" (separated-list SimpleExp ",") ")")
       cps-sum-exp)
      
      (SimpleExp
       ("zero?" "(" SimpleExp ")")
       cps-zero?-exp)

      (SimpleExp
       ("null?" "(" SimpleExp ")")
       cps-null?-exp)

      (SimpleExp
       ("number?" "(" SimpleExp ")")
       cps-number?-exp)

      (SimpleExp
       ("equal?" "(" SimpleExp "," SimpleExp ")")
       cps-equal?-exp)
   
      (SimpleExp
       ("proc" "(" (arbno identifier) ")" TfExp)
       cps-proc-exp)

      (SimpleExp
       ("emptylist")
       cps-emptylist-exp)
      
      (SimpleExp
       ("cons" "(" SimpleExp "," SimpleExp ")")
       cps-cons-exp)

      (SimpleExp
       ("list" "(" (arbno SimpleExp) ")")
       cps-list-exp)
      
      (SimpleExp
       ("car" "(" SimpleExp ")")
       cps-car-exp)
      
      (SimpleExp
       ("cdr" "(" SimpleExp ")")
       cps-cdr-exp)      

      (TfExp (SimpleExp) simple-exp->exp)
      
      (TfExp
       ("let" (arbno identifier "=" SimpleExp) "in" TfExp)
       cps-let-exp)

      (TfExp
       ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" TfExp) "in" TfExp)
       cps-letrec-exp)
       
      (TfExp
       ("if" SimpleExp "then" TfExp "else" TfExp)
       cps-if-exp)

      (TfExp
       ("(" SimpleExp (arbno SimpleExp) ")")
       cps-call-exp)
      ))
  
  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  (sllgen:make-define-datatypes the-lexical-spec the-grammar)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;utils;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;fresh-identifier : symbol -> symbol
  (define fresh-identifier
    (let ((sn 0))
      (lambda (identifier)  
        (set! sn (+ sn 1))
        (string->symbol
          (string-append
            (symbol->string identifier)
            "%"             ; this can't appear in an input identifier
            (number->string sn))))))
  ;;list-index : (SchemeVal -> Bool) * SchemeList -> Maybe(Int)
  (define list-index*
    (lambda (pred lst n)
      (cond
        ((null? lst) #f)
        ((pred (car lst)) n)
        (else
         (list-index* pred (cdr lst) (+ n 1))))))
  (define list-index
    (lambda (pred lst)
      (list-index* pred lst 0)))
  ;;list-set : SchemeList * Int * SchemeVal -> SchemeList
  (define list-set*
    (lambda (lst n val cont)
      (cond
        ((null? lst) (eopl:error 'list-set "ran off end"))
        ((zero? n) (cont (cons val (cdr lst))))
        (else (list-set* (cdr lst) (- n 1) val (lambda (v) (cont (cons (car lst) v))))))))
  (define list-set
    (lambda (lst n val)
      (list-set* lst n val (lambda (v) v))))
  ;;every : (SchemeVal -> Bool) * SchemeList -> Bool
  (define every
    (lambda (pred lst)
      (cond
        ((null? lst) #t)
        ((not (pred (car lst))) #f)
        (else (every pred (cdr lst))))))
  ;;cps-of-program : InpExp -> TfExp
  (define cps-of-program
    (lambda (pgm)
      (cases program pgm
        (a-program (exp1)
          (cps-a-program
            (cps-of-exps (list exp1)
              (lambda (new-args)
                (simple-exp->exp (car new-args)))))))))
  ;;cps-of-exps : Listof(InpExp) × (Listof(InpExp) -> TfExp) -> TfExp
  ;;(define cps-of-exps
  ;;  (lambda (exps builder)
  ;;    (let cps-of-rest ((exps exps))
  ;;      ;;cps-of-rest : Listof(InpExp) -> TfExp
  ;;      (let ((pos (list-index
  ;;                   (lambda (exp)
  ;;                     (not (inp-exp-simple? exp)))
  ;;                   exps)))
  ;;        (if (not pos)
  ;;          (builder (map cps-of-simple-exp exps))
  ;;          (let ((var (fresh-identifier 'var)))
  ;;            (cps-of-exp
  ;;               (list-ref exps pos)
  ;;               (cps-proc-exp (list var)
  ;;                 (cps-of-rest
  ;;                   (list-set exps pos (var-exp var)))))))))))
  (define cps-of-exps
    (lambda (exps builder)
      (let cps-of-rest ((exps exps) (acc '()))
        ;;cps-of-rest : Listof(InpExp) × Listof(SimpleExp) → TfExp
        (cond
          ((null? exps) (builder (reverse acc)))
          ((inp-exp-simple? (car exps))
           (cps-of-rest (cdr exps)
           (cons
             (cps-of-simple-exp (car exps))
             acc)))
         (else
          (let ((var (fresh-identifier 'var)))
            (cps-of-exp (car exps)
              (cps-proc-exp (list var)
                (cps-of-rest (cdr exps)
                  (cons
                    (cps-var-exp var)
                    acc))))))))))
  ;;inp-exp-simple? : InpExp -> Bool
  (define inp-exp-simple?
    (lambda (exp)
      (cases InpExp exp
        (const-exp (num) #t)
        (var-exp (var) #t)
        (emptylist-exp () #t)
        (cons-exp (exp1 exp2)
          (and
            (inp-exp-simple? exp1)
            (inp-exp-simple? exp2)))
        (list-exp (loexp)
          (every inp-exp-simple? loexp))
        (car-exp (exp1)
          (inp-exp-simple? exp1))
        (cdr-exp (exp1)
          (inp-exp-simple? exp1))
        (zero?-exp (exp1)
          (inp-exp-simple? exp1))
        (null?-exp (exp1)
          (inp-exp-simple? exp1))
        (number?-exp (exp1)
          (inp-exp-simple? exp1))
        (equal?-exp (exp1 exp2)
          (and
            (inp-exp-simple? exp1)
            (inp-exp-simple? exp2)))
        (diff-exp (exp1 exp2)
          (and
            (inp-exp-simple? exp1)
            (inp-exp-simple? exp2)))
        (mult-exp (exp1 exp2)
          (and
            (inp-exp-simple? exp1)
            (inp-exp-simple? exp2)))
        (sum-exp (loexp)
          (every inp-exp-simple? loexp))
        (proc-exp (lovar body) #t)
        (else #f))))
  ;;cps-of-simple-exp : InpExp -> SimpleExp
  (define cps-of-simple-exp
    (lambda (exp)
      (cases InpExp exp
        (const-exp (num) (cps-const-exp num))
        (var-exp (var) (cps-var-exp var))
        (emptylist-exp () (cps-emptylist-exp))
        (cons-exp (exp1 exp2)
          (cps-cons-exp
             (cps-of-simple-exp exp1)
             (cps-of-simple-exp exp2)))
        (list-exp (loexp)
          (cps-list-exp (map cps-of-simple-exp loexp)))
        (car-exp (exp1)
          (cps-car-exp (cps-of-simple-exp exp1)))
        (cdr-exp (exp1)
          (cps-cdr-exp (cps-of-simple-exp exp1)))
        (zero?-exp (exp1)
          (cps-zero?-exp (cps-of-simple-exp exp1)))
        (null?-exp (exp1)
          (cps-null?-exp (cps-of-simple-exp exp1)))
        (number?-exp (exp1)
          (cps-number?-exp (cps-of-simple-exp exp1)))
        (equal?-exp (exp1 exp2)
          (cps-equal?-exp
            (cps-of-simple-exp exp1)
            (cps-of-simple-exp exp2)))
        (diff-exp (exp1 exp2)
          (cps-diff-exp
            (cps-of-simple-exp exp1)
            (cps-of-simple-exp exp2)))
        (mult-exp (exp1 exp2)
          (cps-mult-exp
            (cps-of-simple-exp exp1)
            (cps-of-simple-exp exp2)))
        (sum-exp (loexp)
          (cps-sum-exp (map cps-of-simple-exp loexp)))
        (proc-exp (lovar body)
          (cps-proc-exp
            (append lovar (list 'k%00))
            (cps-of-exp body (cps-var-exp 'k%00))))
        (else
          (eopl:error 'cps-of-simple-exp "invalid exp to cps-of-simple-exp: ~s~%" exp)))))
  ;;cps-of-exp : InpExp × SimpleExp -> TfExp
  (define cps-of-exp
    (lambda (exp k-exp)
      (cases InpExp exp
        (const-exp (num)
          (make-send-to-cont k-exp (cps-const-exp num)))
        (var-exp (var)
          (make-send-to-cont k-exp (cps-var-exp var)))
        (emptylist-exp ()
          (make-send-to-cont k-exp (cps-emptylist-exp)))
        (proc-exp (lovar body)
          (make-send-to-cont k-exp
            (cps-proc-exp
              (append lovar (list 'k%00))
              (cps-of-exp body (cps-var-exp 'k%00)))))
        (cons-exp (exp1 exp2)
          (cps-of-cons-exp exp1 exp2 k-exp))
        (list-exp (loexp)
          (cps-of-list-exp loexp k-exp))
        (car-exp (exp1)
          (cps-of-car-exp exp1 k-exp))
        (cdr-exp (exp1)
          (cps-of-cdr-exp exp1 k-exp))
        (zero?-exp (exp1)
          (cps-of-zero?-exp exp1 k-exp))
        (null?-exp (exp1)
          (cps-of-null?-exp exp1 k-exp))
        (number?-exp (exp1)
          (cps-of-number?-exp exp1 k-exp))
        (equal?-exp (exp1 exp2)
          (cps-of-equal?-exp exp1 exp2 k-exp))
        (diff-exp (exp1 exp2)
          (cps-of-diff-exp exp1 exp2 k-exp))
        (mult-exp (exp1 exp2)
          (cps-of-mult-exp exp1 exp2 k-exp))
        (sum-exp (loexp)
          (cps-of-sum-exp loexp k-exp))
        (if-exp (exp1 exp2 exp3)
          (cps-of-if-exp exp1 exp2 exp3 k-exp))
        (let-exp (lovar loexp body)
          (cps-of-let-exp lovar loexp body k-exp))
        (letrec-exp (lop-name lob-vars lop-body letrec-body)
          (cps-of-letrec-exp lop-name lob-vars lop-body letrec-body k-exp))
        (call-exp (rator lorand)
          (cps-of-call-exp rator lorand k-exp)))))
  ;;make-send-to-cont : SimpleExp × SimpleExp -> TfExp
  ;;(define make-send-to-cont
  ;;  (lambda (k-exp simple-exp)
  ;;    (eopl:printf "k-exp: ~s~%" k-exp)
  ;;    (cases SimpleExp k-exp
  ;;      (cps-proc-exp (lovar body)
  ;;        (cps-let-exp lovar (list simple-exp) body))  ;;;;;;;;;;;;this new rule applys when the simple position in Tfexp is not SimpleExp but Tfexp instead
  ;;      (else
  ;;        (cps-call-exp k-exp (list simple-exp))))))
  (define make-send-to-cont
    (lambda (k-exp simple-exp)
      (eopl:printf "k-exp: ~s~%simple-exp:~s~%" k-exp simple-exp)
      (cases SimpleExp k-exp
        (cps-proc-exp (lovar body)
          (replaceVarInTfexp (car lovar) simple-exp body))
        (else
          (cps-call-exp k-exp (list simple-exp))))))
  ;;replaceVarInSimples : var × simpleExp × Listof(SimpleExp) -> Listof(SimpleExp)[simple/var]
  (define replaceVarInSimples
    (lambda (var simple-exp losimple)
      (cond
        ((null? losimple) '())
        (else
          (cases SimpleExp (car losimple)
            (cps-var-exp (id)
              (if (eqv? id var)
                (cons simple-exp (replaceVarInSimples var simple-exp (cdr losimple)))
                (cons (car losimple) (replaceVarInSimples var simple-exp (cdr losimple)))))
            (else (cons (car losimple) (replaceVarInSimples var simple-exp (cdr losimple)))))))))
  ;;replaceVar : var × simpleExp × TfExp -> Tfexp[simp/var]
  (define replaceVarInTfexp
    (lambda (var simple-exp tf-exp)
      (cases TfExp tf-exp
        (simple-exp->exp (simple)
          (simple-exp->exp (car (replaceVarInSimples var simple-exp (list simple)))))
        (cps-let-exp (lovar losimple tfbody)
          (cps-let-exp
            lovar
            (replaceVarInSimples var simple-exp losimple)
            (replaceVarInTfexp var simple-exp tfbody)))
        (cps-if-exp (simple tfexp1 tfexp2)
          (cps-if-exp
            (car (replaceVarInSimples var simple-exp (list simple)))
            (replaceVarInTfexp var simple-exp tfexp1)
            (replaceVarInTfexp var simple-exp tfexp2)))
        (cps-call-exp (rator lorand)
          (let ((result (replaceVarInSimples var simple-exp (cons rator lorand))))
            (cps-call-exp
              (car result)
              (cdr result))))
        (else tf-exp))));;;;the cps-letrec-exp situation need to be considered carefully
  ;;cps-of-cons-exp : InpExp × InpExp × SimpleExp -> TfExp
  (define cps-of-cons-exp
    (lambda (exp1 exp2 k-exp)
      (cps-of-exps
        (list exp1 exp2)
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-cons-exp
              (car losimple)
              (cadr losimple)))))))
  ;;cps-of-list-exp : listof(InpExp) × SimpleExp -> TfExp
  (define cps-of-list-exp
    (lambda (loexp k-exp)
      (cps-of-exps loexp
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-list-exp losimple))))))
  ;;cps-of-car-exp : InpExp × SimpleExp -> TfExp
  (define cps-of-car-exp
    (lambda (exp k-exp)
      (cps-of-exps
        (list exp)
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-car-exp (car losimple)))))))
  ;;cps-of-cdr-exp : InpExp × SimpleExp -> TfExp
  (define cps-of-cdr-exp
    (lambda (exp k-exp)
      (cps-of-exps
        (list exp)
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-cdr-exp (car losimple)))))))
  ;;cps-of-zero?-exp : InpExp × SimpleExp -> TfExp
  (define cps-of-zero?-exp
    (lambda (exp k-exp)
      (cps-of-exps
        (list exp)
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-zero?-exp (car losimple)))))))
  ;;cps-of-null?-exp : InpExp × SimpleExp -> TfExp
  (define cps-of-null?-exp
    (lambda (exp k-exp)
      (cps-of-exps
        (list exp)
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-null?-exp (car losimple)))))))
  ;;cps-of-number?-exp : InpExp × SimpleExp -> TfExp
  (define cps-of-number?-exp
    (lambda (exp k-exp)
      (cps-of-exps
        (list exp)
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-number?-exp (car losimple)))))))
  ;;cps-of-equal?-exp : InpExp × InpExp × SimpleExp -> TfExp
  (define cps-of-equal?-exp
    (lambda (exp1 exp2 k-exp)
      (cps-of-exps
        (list exp1 exp2)
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-equal?-exp
              (car losimple)
              (cadr losimple)))))))
  ;;cps-of-diff-exp : InpExp × InpExp × SimpleExp -> TfExp
  (define cps-of-diff-exp
    (lambda (exp1 exp2 k-exp)
      (cps-of-exps
        (list exp1 exp2)
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-diff-exp
              (car losimple)
              (cadr losimple)))))))
  ;;cps-of-mult-exp : InpExp × InpExp × SimpleExp -> TfExp
  (define cps-of-mult-exp
    (lambda (exp1 exp2 k-exp)
      (cps-of-exps
        (list exp1 exp2)
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-mult-exp
              (car losimple)
              (cadr losimple)))))))
  ;;cps-of-sum-exp : listof(InpExp) × SimpleExp -> TfExp
  (define cps-of-sum-exp
    (lambda (loexp k-exp)
      (cps-of-exps loexp
        (lambda (losimple)
          (make-send-to-cont
            k-exp
            (cps-sum-exp losimple))))))
  ;;cps-of-if-exp : InpExp × InpExp × InpExp × SimpleExp -> TfExp
  ;;(define cps-of-if-exp
  ;;  (lambda (exp1 exp2 exp3 k-exp)
  ;;    (cps-of-exps
  ;;      (list exp1)
  ;;      (lambda (losimple)
  ;;        (let ((var (fresh-identifier 'var)))
  ;;          (cps-let-exp (list var) (list k-exp)
  ;;            (cps-if-exp (car losimple)
  ;;              (cps-of-exp exp2 (cps-var-exp var))
  ;;              (cps-of-exp exp3 (cps-var-exp var)))))))))
   (define cps-of-if-exp
    (lambda (exp1 exp2 exp3 k-exp)
      (cps-of-exps
        (list exp1)
        (lambda (losimple)
          (cps-if-exp (car losimple)
                (cps-of-exp exp2 k-exp)
                (cps-of-exp exp3 k-exp))))))    
  ;;cps-of-let-exp : listof(Var) × listof(InpExp) × InpExp × SimpleExp -> TfExp
  ;;(define cps-of-let-exp
  ;;  (lambda (lovar loexp body k-exp)
  ;;    (cps-of-exps loexp
  ;;      (lambda (losimple)
  ;;        (cps-let-exp lovar losimple
  ;;          (cps-of-exp body k-exp))))))
  (define cps-of-let-exp
    (lambda (lovar loexp body k-exp)
      (cond
        ((eq? (length loexp) 1) (cps-of-exp (car loexp) (cps-proc-exp lovar (cps-of-exp body k-exp))))
        (else (cps-of-exp (car loexp) (cps-proc-exp (list (car lovar)) (cps-of-let-exp (cdr lovar) (cdr loexp) body k-exp)))))))
  ;;cps-of-letrec-exp : Listof(Var) × Listof(Listof(Var)) × Listof(InpExp) × SimpleExp -> TfExp
  (define cps-of-letrec-exp
    (lambda (lop-name lob-vars lop-body letrec-body k-exp)
      (cps-letrec-exp
        lop-name
        (map
          (lambda (b-vars) (append b-vars (list 'k%00)))
          lob-vars)
        (map
          (lambda (p-body) (cps-of-exp p-body (cps-var-exp 'k%00)))
          lop-body)
        (cps-of-exp letrec-body k-exp))))
  ;;cps-of-call-exp : InpExp × Listof(InpExp) × SimpleExp -> TfExp
  (define cps-of-call-exp
    (lambda (rator lorand k-exp)
      (cps-of-exps (cons rator lorand)
        (lambda (losimple)
          (cps-call-exp
            (car losimple)
            (append (cdr losimple) (list k-exp)))))))
)

