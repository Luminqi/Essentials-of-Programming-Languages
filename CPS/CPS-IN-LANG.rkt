(module CPS-IN-LANG
(lib "eopl.ss" "eopl")
(provide (all-defined-out))
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
    '((program (InpExp) a-program)
      
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
      ))
  
  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  (sllgen:make-define-datatypes the-lexical-spec the-grammar)
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser the-lexical-spec the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner the-lexical-spec the-grammar))
  
)
