(set-logic HORN)

(declare-fun InvF (Int Int Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
  (=> (and (InvF D C B A E) (< C 0)) false)))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
  (=> (and (= D 0) (= C 0)) (InvF D C B A E))))
(assert (forall ((A Int)
         (B Int)
         (C Int)
         (D Int)
         (E Int)
         (F Int)
         (G Int)
         (H Int)
         (I Int)
         (J Int))
  (let ((a!1 (and (InvF D C B A I)
                     (>= C 0)
                     (= (- J D) 0)
                     (= (- (- H D) C) 0))))
       (=> a!1 (InvF J H G F E)))
    ))


(check-sat)
(exit)
