; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new9 (Int Bool Int Int) Bool)
(declare-fun new5 (Bool Int Int) Bool)
(declare-fun new4 (Int Int Bool Int Int) Bool)
(declare-fun new31 (Int) Bool)
(declare-fun new3 (Int Int Bool Int Int) Bool)
(declare-fun new25 (Int) Bool)
(declare-fun new2 (Int Int Int Bool) Bool)
(declare-fun new19 (Int Bool Int Int) Bool)
(declare-fun new15 (Bool Int Int) Bool)
(declare-fun new1 (Int Int Int Bool) Bool)
(declare-fun diff_new21 (Int Int) Bool)
(declare-fun diff_new11 (Int Int) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (new31 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= A (+ 1 B))
        (new31 B)
      )
      (new31 A)
    )
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (new25 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= A (+ 1 B))
        (new25 B)
      )
      (new25 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) )
    (=>
      (and
        (= B true)
        (= D 0)
        (= C 0)
        (= A 0)
      )
      (new19 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) )
    (=>
      (and
        (= B true)
        (= B true)
        (>= E 0)
        (>= F 0)
        (<= G H)
        (= A (+ 1 G))
        (= I (+ F E))
        (= D (+ 1 I))
        (= C (+ 1 G))
        (new15 B H F)
        (new15 B G E)
      )
      (new19 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= B 0)
        (= A 0)
      )
      (diff_new21 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (= B (+ 1 C))
        (= A 0)
        (new25 C)
      )
      (diff_new21 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (= B 0)
      (diff_new21 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (= B (+ 1 C))
        (new25 C)
      )
      (diff_new21 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) )
    (=>
      (and
        (= A true)
        (= C 0)
        (= B 0)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) )
    (=>
      (and
        (= A true)
        (= A true)
        (>= D 0)
        (>= E 0)
        (<= F G)
        (= H (+ 1 F))
        (= I (+ E D))
        (= C (+ 1 I))
        (= B (+ 1 F))
        (new15 A G E)
        (new15 A F D)
      )
      (new15 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) )
    (=>
      (and
        (= B true)
        (= D 0)
        (= C 0)
        (= A 0)
      )
      (new9 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) )
    (=>
      (and
        (= B true)
        (= B true)
        (>= E 0)
        (>= F 0)
        (<= G H)
        (= A (+ 1 G))
        (= I (+ F E))
        (= D (+ 1 I))
        (= C (+ 1 G))
        (new5 B H F)
        (new5 B G E)
      )
      (new9 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= B 0)
        (= A 0)
      )
      (diff_new11 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (= B (+ 1 C))
        (= A 0)
        (new31 C)
      )
      (diff_new11 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (= B 0)
      (diff_new11 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (= B (+ 1 C))
        (new31 C)
      )
      (diff_new11 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) )
    (=>
      (and
        (= A true)
        (= C 0)
        (= B 0)
      )
      (new5 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) )
    (=>
      (and
        (= A true)
        (= A true)
        (>= D 0)
        (>= E 0)
        (<= F G)
        (= H (+ 1 F))
        (= I (+ E D))
        (= C (+ 1 I))
        (= B (+ 1 F))
        (new5 A G E)
        (new5 A F D)
      )
      (new5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= C true)
        (>= F 0)
        (>= G 0)
        (= F 0)
        (= G 0)
        (= H (+ G F))
        (= E (+ 1 H))
        (= D 0)
        (= A 1)
      )
      (new4 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) )
    (=>
      (and
        (= F 1)
        (= G 1)
        (= C true)
        (= C true)
        (>= H 0)
        (>= I 0)
        (>= J 0)
        (>= K 0)
        (>= H 0)
        (>= I 0)
        (<= L M)
        (<= N (- B 1))
        (<= O P)
        (= Q (+ I H))
        (= P 0)
        (= R (+ 1 O))
        (= O (+ 1 L))
        (= J (+ 1 Q))
        (= K 0)
        (= S (+ K J))
        (= T (+ I H))
        (= E (+ 1 S))
        (= D (+ 1 T))
        (= A 1)
        (new5 C M I)
        (new5 C L H)
      )
      (new4 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) )
    (=>
      (and
        (= F 0)
        (= G 1)
        (= C true)
        (= C true)
        (>= H 0)
        (>= I 0)
        (>= J (+ K 1))
        (>= L 0)
        (>= M 0)
        (>= H 0)
        (>= I 0)
        (<= N O)
        (<= P (- B 1))
        (= Q (+ I H))
        (= K 0)
        (= R 0)
        (= S (+ 1 R))
        (= J (+ 1 N))
        (= L 0)
        (= M (+ 1 Q))
        (= T (+ M L))
        (= U (+ I H))
        (= E (+ 1 T))
        (= D (+ 1 U))
        (= A 1)
        (new5 C O I)
        (new5 C N H)
      )
      (new4 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) )
    (=>
      (and
        (= F 1)
        (= G 0)
        (= C true)
        (>= H B)
        (>= I 0)
        (>= J 0)
        (>= K 0)
        (<= L M)
        (<= N O)
        (= P (+ 1 L))
        (= Q (+ 1 N))
        (= R (+ K I))
        (= S (+ K J))
        (= E (+ 1 R))
        (= D (+ 1 S))
        (= A 1)
        (diff_new11 N L)
        (new9 O C M K)
        (new4 A B C J I)
      )
      (new4 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) )
    (=>
      (and
        (= F 0)
        (= G 0)
        (= C true)
        (>= H (+ I 1))
        (>= J B)
        (>= K 0)
        (>= L 0)
        (>= M 0)
        (<= N O)
        (= P (+ 1 N))
        (= Q (+ 1 I))
        (= R (+ K M))
        (= S (+ M L))
        (= E (+ 1 R))
        (= D (+ 1 S))
        (= A 1)
        (diff_new11 H N)
        (new4 A B C L K)
        (new9 I C O M)
      )
      (new4 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= C true)
        (>= F 0)
        (>= G 0)
        (= F 0)
        (= G 0)
        (= H (+ G F))
        (= E (+ 1 H))
        (= D 0)
        (= A 1)
      )
      (new3 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) )
    (=>
      (and
        (= F 1)
        (= G 1)
        (= C true)
        (= C true)
        (>= H 0)
        (>= I 0)
        (>= J 0)
        (>= K 0)
        (>= H 0)
        (>= I 0)
        (<= L M)
        (<= N (- B 1))
        (<= O P)
        (= Q (+ I H))
        (= P 0)
        (= R (+ 1 O))
        (= O (+ 1 L))
        (= J (+ 1 Q))
        (= K 0)
        (= S (+ K J))
        (= T (+ I H))
        (= E (+ 1 S))
        (= D (+ 1 T))
        (= A 1)
        (new15 C M I)
        (new15 C L H)
      )
      (new3 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) )
    (=>
      (and
        (= F 0)
        (= G 1)
        (= C true)
        (= C true)
        (>= H 0)
        (>= I 0)
        (>= J (+ K 1))
        (>= L 0)
        (>= M 0)
        (>= H 0)
        (>= I 0)
        (<= N O)
        (<= P (- B 1))
        (= Q (+ I H))
        (= K 0)
        (= R 0)
        (= S (+ 1 R))
        (= J (+ 1 N))
        (= L 0)
        (= M (+ 1 Q))
        (= T (+ M L))
        (= U (+ I H))
        (= E (+ 1 T))
        (= D (+ 1 U))
        (= A 1)
        (new15 C O I)
        (new15 C N H)
      )
      (new3 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) )
    (=>
      (and
        (= F 1)
        (= G 0)
        (= C true)
        (>= H B)
        (>= I 0)
        (>= J 0)
        (>= K 0)
        (<= L M)
        (<= N O)
        (= P (+ 1 L))
        (= Q (+ 1 N))
        (= R (+ K I))
        (= S (+ K J))
        (= E (+ 1 R))
        (= D (+ 1 S))
        (= A 1)
        (diff_new21 N L)
        (new19 O C M K)
        (new3 A B C J I)
      )
      (new3 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) )
    (=>
      (and
        (= F 0)
        (= G 0)
        (= C true)
        (>= H (+ I 1))
        (>= J B)
        (>= K 0)
        (>= L 0)
        (>= M 0)
        (<= N O)
        (= P (+ 1 N))
        (= Q (+ 1 I))
        (= R (+ K M))
        (= S (+ M L))
        (= E (+ 1 R))
        (= D (+ 1 S))
        (= A 1)
        (diff_new21 H N)
        (new3 A B C L K)
        (new19 I C O M)
      )
      (new3 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= E 1)
        (new3 E A D C B)
      )
      (new2 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) )
    (=>
      (and
        (= E 1)
        (new4 E A D C B)
      )
      (new1 A B C D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= A true)
        (<= (- B C) 0)
        (new1 D B C A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= A true)
        (>= (- B C) 2)
        (new2 D B C A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
