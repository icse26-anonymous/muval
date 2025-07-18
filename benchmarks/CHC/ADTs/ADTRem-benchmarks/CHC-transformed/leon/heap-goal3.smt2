; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new8 (Bool Int) Bool)
(declare-fun new6 (Bool Int) Bool)
(declare-fun new3 (Int Int Bool) Bool)
(declare-fun new2 (Int Int Bool) Bool)
(declare-fun new1 (Int Bool Bool Bool) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Bool) (B Int) )
    (=>
      (and
        (= A true)
        (= B 0)
      )
      (new8 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= A true)
        (= A true)
        (<= C D)
        (= E (+ 1 C))
        (= B (+ 1 C))
        (new8 A D)
        (new8 A C)
      )
      (new8 A B)
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
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= A true)
        (= A true)
        (<= C D)
        (= E (+ 1 C))
        (= B (+ 1 C))
        (new6 A D)
        (new6 A C)
      )
      (new6 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (= B 0)
        (= A 0)
      )
      (new3 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) )
    (=>
      (and
        (= C true)
        (= C true)
        (<= D E)
        (= B (+ 1 D))
        (= A (+ 1 D))
        (new6 C E)
        (new6 C D)
      )
      (new3 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (= B 0)
        (= A 0)
      )
      (new2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) )
    (=>
      (and
        (= C true)
        (= C true)
        (<= D E)
        (= B (+ 1 D))
        (= A (+ 1 D))
        (new8 C E)
        (new8 C D)
      )
      (new2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= C 1)
        (= B true)
        (= B true)
        (<= D E)
        (<= F G)
        (= H (+ 1 D))
        (= H (+ 1 F))
        (new2 E G B)
        (new3 D F B)
      )
      (new1 A B B B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (= C 0)
        (= B true)
        (= B true)
        (>= D (+ E 1))
        (<= F G)
        (= H (+ 1 F))
        (= H (+ 1 E))
        (new3 G D B)
        (new2 F E B)
      )
      (new1 A B B B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) )
    (=>
      (and
        (= A true)
        (= B false)
        (new1 C B A A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
