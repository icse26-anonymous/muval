(set-logic HORN)

(declare-fun InvF (Int Int Int Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int))
  (let ((a!1 (and (InvF C B A F E D)
                     (not (= (- A B) 0))
                     (< (- B C) 0)
                     (not (= A 0)))))
       (=> a!1 false))
    ))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int))
  (=> (and (= A 0) (= (+ (- 1) C) 0)) (InvF C B A F E D))))
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
         (L Int))
  (let ((a!1 (and (InvF C B A K J I)
                     (>= (- B C) 0)
                     (= (- (+ (- 1) L) C) 0)
                     (= (- H B) 0)
                     (= (- (+ (- 1) G) A) 0))))
       (=> a!1 (InvF L H G F E D)))
    ))


(check-sat)
(exit)
