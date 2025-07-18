(set-logic HORN)

(declare-fun str_invariant
             (Bool Bool Bool Bool Bool Bool Bool Int Int Bool Bool Int Bool)
             Bool)
(assert (forall ((A Bool)
         (B Int)
         (C Bool)
         (D Bool)
         (E Int)
         (F Int)
         (G Bool)
         (H Bool)
         (I Bool)
         (J Bool)
         (K Bool)
         (L Bool)
         (M Bool))
  (=> (and (str_invariant M L K J I H G F E D C B A) (not (= K true)))
         false)
    ))
(assert (forall ((A Bool)
         (B Int)
         (C Bool)
         (D Bool)
         (E Int)
         (F Int)
         (G Bool)
         (H Bool)
         (I Bool)
         (J Bool)
         (K Bool)
         (L Bool)
         (M Bool))
  (let ((a!1 (ite (and (= D true) (>= (+ 999 E) 0) (>= (- 999 E) 0))
                     (+ E F)
                     E))
           (a!3 (or (and (not (= M true)) (not (= L true))) (= D true)))
           (a!4 (ite (and (= L true) (not (= M true))) (- 1) 0)))
     (let ((a!2 (= (- B (ite (= C true) E a!1)) 0))
           (a!5 (ite (and (= M true) (not (= L true))) 1 a!4)))
     (let ((a!6 (and (not (= I true))
                     a!2
                     (not (= H true))
                     (or (= M true) (= L true) (not (= D true)))
                     (not (= C true))
                     (>= E 0)
                     (= A true)
                     a!3
                     (>= (+ 1 F) 0)
                     (>= (- E) 0)
                     (= E 0)
                     (or (= K true) (and (= I true) (= H true)))
                     (>= (- 1 F) 0)
                     (= (- F a!5) 0)
                     (or (not (= K true)) (not (= I true)) (not (= H true)))
                     (= G true)
                     (= J true))))
       (=> a!6 (str_invariant M L K J I H G F E D C B A)))))
    ))
(assert (forall ((A Int)
         (B Int)
         (C Bool)
         (D Bool)
         (E Bool)
         (F Bool)
         (G Bool)
         (H Bool)
         (I Int)
         (J Bool)
         (K Bool)
         (L Int)
         (M Int)
         (N Bool)
         (O Bool)
         (P Bool)
         (Q Bool)
         (R Bool)
         (S Bool)
         (T Bool)
         (U Bool)
         (V Bool)
         (W Int)
         (X Bool)
         (Y Bool)
         (Z Bool))
  (let ((a!1 (or (and (= Q true) (< W 0))
                    (and (not (= Q true)) (<= W (- 10)))
                    (not (= E true))))
           (a!2 (or (and (= P true) (> W 0))
                    (and (not (= P true)) (>= W 10))
                    (not (= D true))))
           (a!3 (and (or (not (= Q true)) (>= W 0))
                     (or (= Q true) (> W (- 10)))))
           (a!4 (ite (and (= Y true) (>= (+ 999 I) 0) (>= (- 999 I) 0))
                     (+ I B)
                     I))
           (a!6 (and (or (not (= P true)) (<= W 0)) (or (= P true) (< W 10))))
           (a!7 (or (and (not (= Z true)) (not (= O true))) (= Y true)))
           (a!8 (ite (and (= O true) (not (= Z true))) (- 1) 0)))
     (let ((a!5 (= (- W (ite (= X true) A a!4)) 0))
           (a!9 (ite (and (= Z true) (not (= O true))) 1 a!8)))
     (let ((a!10 (and (str_invariant U T S R Q P N M L K J I H)
                      a!1
                      a!2
                      (or a!3 (= E true))
                      a!5
                      (or a!6 (= D true))
                      (or (= Z true) (= O true) (not (= Y true)))
                      (not (= X true))
                      (>= A 0)
                      (not (= V true))
                      a!7
                      (>= (+ 1 B) 0)
                      (>= (- A) 0)
                      (= A 0)
                      (or (= G true) (and (= E true) (= D true)))
                      (>= (- 1 B) 0)
                      (= (- B a!9) 0)
                      (or (not (= G true)) (not (= E true)) (not (= D true)))
                      (not (= C true))
                      (not (= F true)))))
       (=> a!10 (str_invariant Z O G F E D C B A Y X W V)))))
    ))


(check-sat)
(exit)
