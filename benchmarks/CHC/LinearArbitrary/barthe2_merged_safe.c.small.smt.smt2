(set-logic HORN)

(declare-fun |main@precall.split| ( ) Bool)
(declare-fun |main@postcall| ( Bool Int Int Int Int Int ) Bool)
(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@precall| ( Bool ) Bool)
(declare-fun |main@postcall.preheader| ( Int Bool Bool Int Int ) Bool)

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
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Int) (J Bool) (K Bool) (L Int) (M Int) ) 
    (=>
      (and
        (main@entry B)
        (and (= D (not (<= M I)))
     (= E (not (<= L I)))
     (= F (and E D))
     (= G (not (<= I (- 1))))
     (= J (not C))
     (= K (= (not G) J))
     (= A B)
     (= L (ite C 1 2))
     (= M (ite G 1 0))
     (not F)
     (= H true)
     (= C (not (<= 1 I))))
      )
      (main@postcall.preheader I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) ) 
    (=>
      (and
        (main@entry B)
        (and (= J (not (<= F (- 1))))
     (= M (= (not J) K))
     (= N M)
     (= G (not (<= D F)))
     (= H (not (<= E F)))
     (= I (and H G))
     (= K (not C))
     (= A B)
     (= D (ite J 1 0))
     (= E (ite C 1 2))
     (not I)
     (not L)
     (= C (not (<= 1 F))))
      )
      (main@precall N)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Bool) (G Int) (H Int) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (main@postcall.preheader H A B C E)
        (and (= G E) (= J C) (= D (ite A 1 0)) (= I 0) (= K D) (= F B))
      )
      (main@postcall F G H I J K)
    )
  )
)
(assert
  (forall ( (A Bool) ) 
    (=>
      (and
        (main@precall A)
        (= A true)
      )
      main@precall.split
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Int) (M Int) (N Bool) (O Bool) (P Bool) (Q Int) (R Bool) (S Bool) (T Int) (U Int) (V Int) (W Int) (X Bool) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) ) 
    (=>
      (and
        (main@postcall A E Z F L I)
        (and (= D (not (<= E Z)))
     (= J (not (<= L Z)))
     (= K (not J))
     (= N (not (<= W Z)))
     (= O (not (<= T Z)))
     (= P (and O N))
     (= S (not (= U Q)))
     (= X S)
     (= C (ite B 1 0))
     (= G (ite D 0 E))
     (= H (ite J 0 L))
     (= M (ite K 1 0))
     (= T (+ L M))
     (= U (+ H I))
     (= Q (+ V W))
     (= Y W)
     (= B1 T)
     (= V (+ F G))
     (= W (+ E C))
     (= A1 V)
     (= C1 U)
     (not A)
     (not P)
     (= R true)
     (= B (not D)))
      )
      (main@postcall X Y Z A1 B1 C1)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Int) (M Int) (N Int) (O Int) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Bool) (X Bool) (Y Bool) ) 
    (=>
      (and
        (main@postcall A E O F L I)
        (and (= D (not (<= E O)))
     (= J (not (<= L O)))
     (= K (not J))
     (= X (not (= U V)))
     (= Y X)
     (= P (not (<= T O)))
     (= Q (not (<= N O)))
     (= R (and Q P))
     (= G (ite D 0 E))
     (= T (+ E C))
     (= C (ite B 1 0))
     (= H (ite J 0 L))
     (= M (ite K 1 0))
     (= N (+ L M))
     (= U (+ H I))
     (= S (+ F G))
     (= V (+ S T))
     (not A)
     (not R)
     (not W)
     (= B (not D)))
      )
      (main@precall Y)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@precall.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
