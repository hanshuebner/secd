(in-package :cl-user)

(defun vars (d)
  (if (eq d nil)
      nil
      (cons (car (car d)) (vars (cdr d)))))

(defun exprs (d)
  (if (eq d nil)
      nil
      (cons (cdr (car d)) (exprs (cdr d)))))

(defun evlis (l n v)
  (if (eq l nil) nil
      (cons (lk-eval (car l) n v) (evlis (cdr l) n v))))

(defun lk-locate (x l m)
  (if (eq x (car l))
      (car m)
      (when (cdr l)
        (lk-locate x (cdr l) (cdr m)))))

(defun lk-member (x l)
  (if (eq l nil)
      'f
      (if (eq x (car l))
          't
          (lk-member x (cdr l)))))

(defun lk-assoc (x n v)
  (if (lk-member x (car n))
      (lk-locate x (car n) (car v))
      (lk-assoc x (cdr n) (cdr v))))

(defun lk-eval (e n v)
    (if (atom e)
        (lk-assoc e n v)
        (let ((key (car e)))
          (case key
            ('quote (let ((const (cadr e))
                          (case const
                            ('nil nil)
                            ('true t)
                            ('false nil)
                            (otherwise const)))))
            ('add
             (+ (lk-eval (cadr e) n v) (lk-eval (caddr e) n v)))
            ('sub
             (- (lk-eval (cadr e) n v) (lk-eval (caddr e) n v)))
            ('mul
             (* (lk-eval (cadr e) n v) (lk-eval (caddr e) n v)))
            ('div
             (/ (lk-eval (cadr e) n v) (lk-eval (caddr e) n v)))
            ('rem
             (rem (lk-eval (cadr e) n v) (lk-eval (caddr e) n v)))
            ('eq
             (eq (lk-eval (cadr e) n v) (lk-eval (caddr e) n v)))
            ('leq
             (<= (lk-eval (cadr e) n v) (lk-eval (caddr e) n v)))
            ('car
             (car (lk-eval (cadr e) n v)))
            ('cdr
             (cdr (lk-eval (cadr e) n v)))
            ('cons
             (cons (lk-eval (cadr e) n v) (lk-eval (caddr e) n v)))
            ('atom
             (atom (lk-eval (cadr e) n v)))
            ('if
             (let ((e1 (cadr e))
                   (e2 (caddr e))
                   (e3 (cadddr e)))
               (lk-eval (if (lk-eval e1 n v) e2 e3) n v)))
            ('lambda
             (cons (cons (cadr e) (caddr e)) (cons n v)))
            ('let
             (let ((y (vars (cddr e)))
                   (z (evlis (exprs (cddr e)) n v)))
               (lk-eval (cadr e) (cons y n) (cons z v))))
            ('letrec
             (let* ((y (vars (cddr e)))
                    (v1 (cons 'pending v))
                    (z (evlis (exprs (cddr e)) (cons y n) v1)))
               (lk-eval (card e) (cons y n) (rplaca v1 z)))
             (let ((c (lk-eval key n v))
                   (z (evlis (cdr e) n v)))
               (lk-eval (cdar c) (cons (caar c) (cadr c)) (cons z (cddr c)))))))))
                
(defun lk-apply (f x)
  (let ((c (lk-eval f nil nil)))
    (lk-eval (cdar c) (cons (caar c) (cadr c)) (cons x (cddr c)))))