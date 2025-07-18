; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new9 (Int) Bool)
(declare-fun new6 (Int Int) Bool)
(declare-fun new3 (Int Int) Bool)
(declare-fun new2 (Int Int) Bool)
(declare-fun new12 (Int) Bool)
(declare-fun new1 (Int Int) Bool)
(declare-fun diff_new8 (Int Int Int) Bool)
(declare-fun diff_new5 (Int Int Int) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (new12 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= A (+ 1 B))
        (new12 B)
      )
      (new12 A)
    )
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
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= A (+ 1 B))
        (new9 B)
      )
      (new9 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (= C (+ 1 A))
        (new9 A)
      )
      (diff_new8 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= C (+ 1 D))
        (= A (+ 1 E))
        (diff_new8 E B D)
      )
      (diff_new8 A B C)
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
      (new6 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= B (+ 1 C))
        (= A (+ 1 D))
        (new6 D C)
      )
      (new6 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (= C (+ 1 A))
        (new12 A)
      )
      (diff_new5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= C (+ 1 D))
        (= A (+ 1 E))
        (diff_new5 E B D)
      )
      (diff_new5 A B C)
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
      (new3 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= B (+ 1 C))
        (= A (+ 1 D))
        (new3 D C)
      )
      (new3 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (new3 A B)
      (new2 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= A (+ 1 C))
        (diff_new5 D E B)
        (new2 C D)
      )
      (new2 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (new6 A B)
      (new1 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= A (+ 1 C))
        (diff_new8 D E B)
        (new1 C D)
      )
      (new1 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= A (+ (* 2 B) 1))
        (= C (* 2 D))
        (new1 C A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= A (* 2 B))
        (= C (+ (* 2 D) 1))
        (new2 C A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
