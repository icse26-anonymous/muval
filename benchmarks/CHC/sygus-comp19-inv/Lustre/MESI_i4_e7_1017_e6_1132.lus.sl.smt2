(set-logic HORN)

(declare-fun str_invariant
             (Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Int
              Bool
              Bool
              Bool
              Bool
              Bool)
             Bool)
(assert (forall ((A Bool)
         (B Bool)
         (C Bool)
         (D Bool)
         (E Bool)
         (F Int)
         (G Int)
         (H Int)
         (I Int)
         (J Bool)
         (K Bool)
         (L Bool)
         (M Bool)
         (N Bool)
         (O Bool))
  (=> (and (str_invariant O N M L K J I H G F E D C B A) (not (= K true)))
         false)
    ))
(assert (forall ((A Bool)
         (B Bool)
         (C Bool)
         (D Bool)
         (E Bool)
         (F Int)
         (G Int)
         (H Int)
         (I Int)
         (J Bool)
         (K Bool)
         (L Bool)
         (M Bool)
         (N Bool)
         (O Bool))
  (let ((a!1 (and (or (not (= O true)) (not (= N true)))
                     (or (not (= O true)) (not (= M true)))
                     (or (not (= O true)) (not (= L true)))
                     (or (not (= N true)) (not (= M true)))
                     (or (not (= N true)) (not (= L true)))
                     (or (not (= M true)) (not (= L true))))))
     (let ((a!2 (and (= (+ (- 3) F) 0)
                     (or (not (= D true)) (>= F 0) (not (= K true)))
                     (or (= E true) (not (= D true)))
                     (= G 0)
                     (= H 0)
                     (= I 0)
                     (or (and (= D true) (< F 0)) (= K true))
                     (or (= E true)
                         (and (= O true) (= N true))
                         (and (= O true) (= M true))
                         (and (= O true) (= L true))
                         (and (= N true) (= M true))
                         (and (= N true) (= L true))
                         (and (= M true) (= L true)))
                     (or (not (= E true)) (= D true))
                     (= C true)
                     (or (not (= E true)) a!1)
                     (= B true)
                     (= A true)
                     (= J true))))
       (=> a!2 (str_invariant O N M L K J I H G F E D C B A))))
    ))
(assert (forall ((A Int)
         (B Int)
         (C Int)
         (D Bool)
         (E Bool)
         (F Bool)
         (G Bool)
         (H Bool)
         (I Bool)
         (J Bool)
         (K Bool)
         (L Bool)
         (M Int)
         (N Int)
         (O Int)
         (P Int)
         (Q Bool)
         (R Bool)
         (S Bool)
         (T Bool)
         (U Bool)
         (V Bool)
         (W Bool)
         (X Bool)
         (Y Bool)
         (Z Bool)
         (A1 Bool)
         (B1 Bool)
         (C1 Int)
         (D1 Bool)
         (E1 Bool)
         (F1 Bool)
         (G1 Bool))
  (let ((a!1 (ite (= H true)
                     (ite (= F1 true) 0 P)
                     (ite (= F true) (ite (= E1 true) 0 P) P)))
           (a!4 (ite (= F true) (ite (= E1 true) (+ (+ (- 1) P) O N M) M) M))
           (a!7 (ite (= H true)
                     (ite (= F1 true) 1 O)
                     (ite (= F true) (ite (= E1 true) 1 O) O)))
           (a!10 (ite (= H true)
                      (ite (= F1 true) 0 N)
                      (ite (= F true) (ite (= E1 true) 0 N) N)))
           (a!12 (or (and (not (= B1 true)) (not (= K true))) (= A1 true)))
           (a!13 (and (or (not (= D1 true)) (not (= S true)))
                      (or (not (= D1 true)) (not (= H true)))
                      (or (not (= D1 true)) (not (= F true)))
                      (or (not (= S true)) (not (= H true)))
                      (or (not (= S true)) (not (= F true)))
                      (or (not (= H true)) (not (= F true))))))
     (let ((a!2 (ite (= S true) (ite (>= (+ (- 1) O) 0) (+ (- 1) P) P) a!1))
           (a!5 (ite (= H true) (ite (= F1 true) (+ (+ (- 1) P) O N M) M) a!4))
           (a!8 (ite (= S true) (ite (>= (+ (- 1) O) 0) (+ (- 1) O) O) a!7))
           (a!11 (- A
                    (ite (= D1 true)
                         (ite (= G1 true) (+ 1 P O N) N)
                         (ite (= S true) N a!10)))))
     (let ((a!3 (- C (ite (= D1 true) (ite (= G1 true) 0 P) a!2)))
           (a!6 (- C1
                   (ite (= D1 true)
                        (ite (= G1 true) (+ (- 1) M) M)
                        (ite (= S true) M a!5))))
           (a!9 (- B (ite (= D1 true) (ite (= G1 true) 0 O) a!8))))
     (let ((a!14 (and (str_invariant W V U T R Q P O N M L K J I G)
                      (= a!3 0)
                      (= a!6 0)
                      (= a!9 0)
                      (or (not (= A1 true)) (>= C1 0) (not (= E true)))
                      (or (= B1 true) (= K true) (not (= A1 true)))
                      (= a!11 0)
                      (or (and (= A1 true) (< C1 0)) (= E true))
                      (or (= B1 true)
                          (and (= D1 true) (= S true))
                          (and (= D1 true) (= H true))
                          (and (= D1 true) (= F true))
                          (and (= S true) (= H true))
                          (and (= S true) (= F true))
                          (and (= H true) (= F true)))
                      a!12
                      (not (= Z true))
                      (or (not (= B1 true)) a!13)
                      (not (= Y true))
                      (not (= X true))
                      (= G1 (>= (+ (- 1) M) 0))
                      (= F1 (>= (+ (- 1) N) 0))
                      (= E1 (>= (+ (- 1) M) 0))
                      (not (= D true)))))
       (=> a!14 (str_invariant D1 S H F E D C B A C1 B1 A1 Z Y X))))))
    ))


(check-sat)
(exit)
