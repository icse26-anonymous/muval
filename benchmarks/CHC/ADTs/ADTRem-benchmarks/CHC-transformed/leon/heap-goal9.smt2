; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new9 (Int) Bool)
(declare-fun new6 (Bool Int) Bool)
(declare-fun new3 (Bool Int) Bool)
(declare-fun new27 (Int Int) Bool)
(declare-fun new23 (Int) Bool)
(declare-fun new2 (Int Int Int Bool) Bool)
(declare-fun new13 (Int Int) Bool)
(declare-fun new1 (Int Int Int Bool) Bool)
(declare-fun diff_new8 (Int Int Int Int) Bool)
(declare-fun diff_new5 (Int Int Int Int) Bool)
(declare-fun diff_new34 (Int) Bool)
(declare-fun diff_new29 (Int) Bool)
(declare-fun diff_new20 (Int) Bool)
(declare-fun diff_new15 (Int) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (diff_new34 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= A (+ 1 B))
        (diff_new34 B)
      )
      (diff_new34 A)
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
      (new27 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (>= C 0)
        (>= D 0)
        (= E (+ D C))
        (= B (+ 1 E))
        (new23 D)
        (new23 C)
      )
      (new27 A B)
    )
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (diff_new29 A)
    )
  )
)
(assert
  (forall ( (A Int) )
    (diff_new29 A)
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (new23 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (>= B 0)
        (>= C 0)
        (= D (+ B C))
        (= A (+ 1 D))
        (new23 B)
        (new23 C)
      )
      (new23 A)
    )
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (diff_new20 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= A (+ 1 B))
        (diff_new20 B)
      )
      (diff_new20 A)
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
      (new13 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (>= C 0)
        (>= D 0)
        (= E (+ D C))
        (= B (+ 1 E))
        (new9 D)
        (new9 C)
      )
      (new13 A B)
    )
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (diff_new15 A)
    )
  )
)
(assert
  (forall ( (A Int) )
    (diff_new15 A)
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (new9 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (>= B 0)
        (>= C 0)
        (= D (+ B C))
        (= A (+ 1 D))
        (new9 B)
        (new9 C)
      )
      (new9 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (>= E 0)
        (>= F 0)
        (= E 0)
        (= F 0)
        (= G (+ F E))
        (= D (+ 1 G))
        (= B 1)
        (= A 0)
      )
      (diff_new8 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) )
    (=>
      (and
        (= E 1)
        (= F 1)
        (>= G 0)
        (>= H 0)
        (>= I 0)
        (>= J 0)
        (>= G 0)
        (>= H 0)
        (<= K (- C 1))
        (<= L M)
        (= N (+ H G))
        (= M 0)
        (= O (+ 1 L))
        (= I (+ 1 N))
        (= J 0)
        (= P (+ J I))
        (= Q (+ H G))
        (= D (+ 1 P))
        (= B 1)
        (= A (+ 1 Q))
        (new9 H)
        (new9 G)
      )
      (diff_new8 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) )
    (=>
      (and
        (= E 0)
        (= F 1)
        (>= G 0)
        (>= H 0)
        (>= I (+ J 1))
        (>= K 0)
        (>= L 0)
        (>= G 0)
        (>= H 0)
        (<= M (- C 1))
        (= N (+ H G))
        (= J 0)
        (= O 0)
        (= P (+ 1 O))
        (= K 0)
        (= L (+ 1 N))
        (= Q (+ L K))
        (= R (+ H G))
        (= D (+ 1 Q))
        (= B 1)
        (= A (+ 1 R))
        (new9 H)
        (new9 G)
      )
      (diff_new8 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) )
    (=>
      (and
        (= E 0)
        (= F 1)
        (>= G 0)
        (>= H C)
        (>= I 0)
        (>= J 0)
        (<= K L)
        (= M (+ I G))
        (= N (+ I J))
        (= O (+ 1 K))
        (= D (+ 1 N))
        (= B 1)
        (= A (+ 1 M))
        (diff_new15 K)
        (new13 L I)
        (diff_new8 G B C J)
      )
      (diff_new8 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) )
    (=>
      (and
        (= E 0)
        (= F 0)
        (>= G 0)
        (>= H C)
        (>= I (+ J 1))
        (>= K 0)
        (>= L 0)
        (= M (+ L G))
        (= N (+ K L))
        (= O (+ 1 J))
        (= D (+ 1 N))
        (= B 1)
        (= A (+ 1 M))
        (diff_new15 I)
        (diff_new8 G B C K)
        (new13 J L)
      )
      (diff_new8 A B C D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) )
    (=>
      (and
        (= A true)
        (= B 0)
      )
      (new6 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= A true)
        (>= C 0)
        (>= D 0)
        (<= E F)
        (= G (+ 1 E))
        (= H (+ D C))
        (= B (+ 1 H))
        (diff_new20 E)
        (diff_new20 F)
        (new6 A D)
        (new6 A C)
      )
      (new6 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (>= E 0)
        (>= F 0)
        (= E 0)
        (= F 0)
        (= G (+ F E))
        (= D (+ 1 G))
        (= B 1)
        (= A 0)
      )
      (diff_new5 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) )
    (=>
      (and
        (= E 1)
        (= F 1)
        (>= G 0)
        (>= H 0)
        (>= I 0)
        (>= J 0)
        (>= G 0)
        (>= H 0)
        (<= K (- C 1))
        (<= L M)
        (= N (+ H G))
        (= M 0)
        (= O (+ 1 L))
        (= I (+ 1 N))
        (= J 0)
        (= P (+ J I))
        (= Q (+ H G))
        (= D (+ 1 P))
        (= B 1)
        (= A (+ 1 Q))
        (new23 H)
        (new23 G)
      )
      (diff_new5 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) )
    (=>
      (and
        (= E 0)
        (= F 1)
        (>= G 0)
        (>= H 0)
        (>= I (+ J 1))
        (>= K 0)
        (>= L 0)
        (>= G 0)
        (>= H 0)
        (<= M (- C 1))
        (= N (+ H G))
        (= J 0)
        (= O 0)
        (= P (+ 1 O))
        (= K 0)
        (= L (+ 1 N))
        (= Q (+ L K))
        (= R (+ H G))
        (= D (+ 1 Q))
        (= B 1)
        (= A (+ 1 R))
        (new23 H)
        (new23 G)
      )
      (diff_new5 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) )
    (=>
      (and
        (= E 0)
        (= F 1)
        (>= G 0)
        (>= H C)
        (>= I 0)
        (>= J 0)
        (<= K L)
        (= M (+ I G))
        (= N (+ I J))
        (= O (+ 1 K))
        (= D (+ 1 N))
        (= B 1)
        (= A (+ 1 M))
        (diff_new29 K)
        (new27 L I)
        (diff_new5 G B C J)
      )
      (diff_new5 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) )
    (=>
      (and
        (= E 0)
        (= F 0)
        (>= G 0)
        (>= H C)
        (>= I (+ J 1))
        (>= K 0)
        (>= L 0)
        (= M (+ L G))
        (= N (+ K L))
        (= O (+ 1 J))
        (= D (+ 1 N))
        (= B 1)
        (= A (+ 1 M))
        (diff_new29 I)
        (diff_new5 G B C K)
        (new27 J L)
      )
      (diff_new5 A B C D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) )
    (=>
      (and
        (= A true)
        (= B 0)
      )
      (new3 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= A true)
        (>= C 0)
        (>= D 0)
        (<= E F)
        (= G (+ 1 E))
        (= H (+ D C))
        (= B (+ 1 H))
        (diff_new34 E)
        (diff_new34 F)
        (new3 A D)
        (new3 A C)
      )
      (new3 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= B 0)
        (new3 C A)
      )
      (new2 A A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= E 1)
        (= C (+ 1 F))
        (diff_new5 G E H A)
        (new2 G B F D)
      )
      (new2 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= B 0)
        (new6 C A)
      )
      (new1 A A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= E 1)
        (= C (+ 1 F))
        (diff_new8 G E H A)
        (new1 G B F D)
      )
      (new1 A B C D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= A true)
        (<= (+ B 1) C)
        (= (+ D E) B)
        (new1 C D E A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= A true)
        (>= B (+ C 1))
        (= (+ D E) B)
        (new2 C D E A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
