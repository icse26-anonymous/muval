(set-logic HORN)

(declare-fun inv-f (Int Int Int Int Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int))
  (=> (and (inv-f B A G F E D C)
              (< (+ (- 1) D) 0)
              (= (- B G) 0)
              (>= G 0)
              (= (- A D) 0)
              (not (= D 0)))
         false)
    ))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int))
  (=> (and (= (- B G) 0) (= (- A E) 0) (= (- E G) 0)) (inv-f B A G F E D C))
    ))
(assert (forall ((A Int)
         (B Int)
         (C Int)
         (D Int)
         (E Int)
         (F Int)
         (G Int)
         (H Int)
         (I Int)
         (J Int)
         (K Int)
         (L Int)
         (M Int)
         (N Int))
  (let ((a!1 (and (= (- J A) 0)
                     (>= (+ (- 1) J) 0)
                     (= (+ (- 1 J) I) 0)
                     (= (- I H) 0)
                     (= (- B M) 0)
                     (= (- N M) 0))))
     (let ((a!2 (or (and (= (- J A) 0) (= (- J H) 0) (= (- B N) 0)) a!1)))
       (=> (and (inv-f B A M L K J I) a!2) (inv-f N H G F E D C))))
    ))


(check-sat)
(exit)
