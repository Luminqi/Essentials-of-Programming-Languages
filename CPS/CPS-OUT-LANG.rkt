(module CPS-OUT-LANG
(lib "eopl.ss" "eopl")
(provide (all-defined-out))
;;;;;;;;;;;;;lang;;;;;;;;;;;;;;;;;;;;;;
  (define cps-the-lexical-spec
    '((whitespace (whitespace) skip)
      (comment ("%" (arbno (not #\newline))) skip)
      (identifier
       (letter (arbno (or letter digit "_" "-" "?")))
       symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      ))
  
  (define cps-the-grammar
    '((program (TfExp) cps-a-program)
      
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
  (sllgen:make-define-datatypes cps-the-lexical-spec cps-the-grammar)
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes cps-the-lexical-spec cps-the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser cps-the-lexical-spec cps-the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner cps-the-lexical-spec cps-the-grammar))
)