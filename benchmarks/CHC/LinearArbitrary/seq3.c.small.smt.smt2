(set-logic HORN)

(declare-fun |main@.lr.ph10| ( Int Int Bool Int Bool Int Int ) Bool)
(declare-fun |main@.lr.ph| ( Int Int Int Int ) Bool)
(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |main@.preheader| ( Int Int Bool Int ) Bool)
(declare-fun |main@.lr.ph14| ( Int Int Bool Int Int Int ) Bool)
(declare-fun |main@.lr.ph7| ( Int Int Bool Int Int Int ) Bool)
(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@.preheader2| ( Int Int Bool Int Int ) Bool)
(declare-fun |main@.preheader1| ( Int Int Bool Int Bool Int ) Bool)
(declare-fun |main@verifier.error| ( ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (main@entry A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (main@entry D)
        (and (= G (not (<= E 0)))
     (= B D)
     (= C D)
     (= I 0)
     (= J 0)
     (= A true)
     (= G true)
     (= A (= F 1)))
      )
      (main@.lr.ph14 E F G H I J)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Int) (I Int) ) 
    (=>
      (and
        (main@entry D)
        (and (= G (not (<= E 0)))
     (= B D)
     (= C D)
     (= I 0)
     (= A true)
     (not G)
     (= A (= F 1)))
      )
      (main@.preheader2 E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Bool) (G Int) (H Int) ) 
    (=>
      (and
        (main@.preheader2 B C D E A)
        (and (= G 0) (= H A) (= F true) (= F (not (<= E 0))))
      )
      (main@.lr.ph10 B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Bool) (G Int) ) 
    (=>
      (and
        (main@.preheader2 D E F A C)
        (and (= G C) (not B) (= B (not (<= A 0))))
      )
      (main@.preheader D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (main@.lr.ph14 F G H I A B)
        (and (= D (+ 1 A))
     (= E (+ 1 B))
     (= J D)
     (= K E)
     (= C true)
     (= C (not (<= F D))))
      )
      (main@.lr.ph14 F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Int) (G Int) (H Bool) (I Int) (J Int) ) 
    (=>
      (and
        (main@.lr.ph14 F G H I A B)
        (and (= C (+ 1 A)) (= E (+ 1 B)) (= J E) (not D) (= D (not (<= F C))))
      )
      (main@.preheader2 F G H I J)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (main@.preheader1 C D E H A B)
        (and (= G B) (= A true) (= F 0))
      )
      (main@.lr.ph7 C D E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Bool) (G Int) ) 
    (=>
      (and
        (main@.preheader1 D E F A B C)
        (and (not B) (= G C))
      )
      (main@.preheader D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Int) (J Bool) (K Int) (L Int) ) 
    (=>
      (and
        (main@.lr.ph10 F G H I J A B)
        (and (= D (+ 1 A))
     (= E (+ 1 B))
     (= K D)
     (= L E)
     (= C true)
     (= C (not (<= I D))))
      )
      (main@.lr.ph10 F G H I J K L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Int) (G Bool) (H Int) (I Bool) (J Int) ) 
    (=>
      (and
        (main@.lr.ph10 E F G H I A B)
        (and (= C (+ 1 A)) (= J (+ 1 B)) (not D) (= D (not (<= H C))))
      )
      (main@.preheader1 E F G H I J)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (main@.preheader F G A C)
        (and (= D 0) (= E C) (= A true) (= B true) (= B (not (<= C 0))))
      )
      (main@.lr.ph D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Bool) ) 
    (=>
      (and
        (main@.preheader A B C D)
        (and (not E) (= C true) (= E (not (<= D 0))))
      )
      main@verifier.error
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (main@.lr.ph7 F G H A B K)
        (and (= D (+ 1 A))
     (= E (+ (- 1) B))
     (= I D)
     (= J E)
     (= C true)
     (= C (not (<= K D))))
      )
      (main@.lr.ph7 F G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Bool) (J Int) ) 
    (=>
      (and
        (main@.lr.ph7 G H I A B D)
        (and (= C (+ 1 A)) (= F (+ (- 1) B)) (= J F) (not E) (= E (not (<= D C))))
      )
      (main@.preheader G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (main@.lr.ph A C I J)
        (and (= B (not (<= I E)))
     (= G E)
     (= E (+ 1 A))
     (= F (+ (- 1) C))
     (= H F)
     (= D true)
     (= B true)
     (= D (not (<= C J))))
      )
      (main@.lr.ph G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Bool) ) 
    (=>
      (and
        (main@.lr.ph A F D G)
        (and (= E (not (<= D C)))
     (= B (+ (- 1) F))
     (= C (+ 1 A))
     (not H)
     (= E true)
     (= H (not (<= F G))))
      )
      main@verifier.error
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@verifier.error
        true
      )
      main@verifier.error.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@verifier.error.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
