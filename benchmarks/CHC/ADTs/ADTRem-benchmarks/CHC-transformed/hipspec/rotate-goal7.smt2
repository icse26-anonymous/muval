; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new6 (Int) Bool)
(declare-fun new3 (Int) Bool)
(declare-fun new2 (Int Int Int) Bool)
(declare-fun new1 (Int Int Int) Bool)
(declare-fun diff_new8 (Int Int Int) Bool)
(declare-fun diff_new5 (Int Int Int) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= D 0)
        (= B 0)
        (= A (+ 1 D))
      )
      (diff_new8 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= B (+ 1 D))
        (= A (+ 1 E))
        (diff_new8 E D C)
      )
      (diff_new8 A B C)
    )
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (new6 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= A (+ 1 B))
        (new6 B)
      )
      (new6 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= D 0)
        (= B 0)
        (= A (+ 1 D))
      )
      (diff_new5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (= B (+ 1 D))
        (= A (+ 1 E))
        (diff_new5 E D C)
      )
      (diff_new5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (new3 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (= A (+ 1 B))
        (new3 B)
      )
      (new3 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (>= A 0)
        (= A 0)
        (new3 B)
      )
      (new2 A B B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (>= D 0)
        (>= A 0)
        (= C 0)
        (= B 0)
        (= A (+ 1 D))
      )
      (new2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (>= D 0)
        (>= A 0)
        (= C (+ 1 E))
        (= A (+ 1 D))
        (diff_new5 F E G)
        (new2 D B F)
      )
      (new2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (>= A 0)
        (= A 0)
        (new6 B)
      )
      (new1 A B B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (>= D 0)
        (>= A 0)
        (= C 0)
        (= B 0)
        (= A (+ 1 D))
      )
      (new1 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (>= D 0)
        (>= A 0)
        (= C (+ 1 E))
        (= A (+ 1 D))
        (diff_new8 F E G)
        (new1 D B F)
      )
      (new1 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (>= (- A B) 1)
        (>= C 0)
        (new1 C B A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (>= A 0)
        (<= (- B C) (- 1))
        (new2 A C B)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
