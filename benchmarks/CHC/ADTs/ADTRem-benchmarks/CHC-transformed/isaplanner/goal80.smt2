; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new9 (Int Int Bool Int Bool) Bool)
(declare-fun new7 (Int Int Bool Int Bool) Bool)
(declare-fun new6 (Int Int Bool) Bool)
(declare-fun new4 (Int Bool) Bool)
(declare-fun new13 (Int Bool) Bool)
(declare-fun new1 (Bool) Bool)
(declare-fun diff_new3 (Bool Int Bool) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B true)
      (new13 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) )
    (=>
      (and
        (= B false)
        (>= A (+ C 1))
      )
      (new13 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) )
    (=>
      (and
        (<= A C)
        (new13 C B)
      )
      (new13 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) )
    (=>
      (and
        (= D true)
        (>= (- A B) 0)
        (<= B A)
        (new4 A C)
      )
      (new9 A B C B D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (>= (- A B) 0)
        (<= B E)
        (<= B A)
        (<= A (- E 1))
        (new7 A E C E D)
      )
      (new9 A B C B D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (= D false)
        (= C false)
        (>= (- A B) 0)
        (>= B (+ E 1))
        (>= B (+ E 1))
        (>= A E)
      )
      (new9 A B C B D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) )
    (=>
      (and
        (>= (- A B) 0)
        (>= A E)
        (<= B E)
        (<= B E)
        (new9 A E C E D)
      )
      (new9 A B C B D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (>= (- B A) 0)
        (<= A B)
        (new13 B C)
      )
      (new7 A B C B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C false)
        (>= A (+ B 1))
        (<= (- B A) (- 1))
      )
      (new6 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (= B true)
      (new4 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (= A true)
      )
      (diff_new3 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= A true)
        (<= B D)
        (<= B (- D 1))
        (new4 D C)
      )
      (diff_new3 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (= A true)
        (>= B D)
        (<= D B)
        (new4 B C)
      )
      (diff_new3 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Int) (E Int) )
    (=>
      (and
        (= A false)
        (>= D (+ E 1))
        (<= B D)
        (<= B (- D 1))
        (new6 D E C)
      )
      (diff_new3 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Int) (E Int) )
    (=>
      (and
        (= C false)
        (= A false)
        (>= D (+ E 1))
        (>= D (+ E 1))
        (>= B E)
        (>= B D)
      )
      (diff_new3 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Int) (E Int) )
    (=>
      (and
        (<= D E)
        (<= B D)
        (<= B (- D 1))
        (new7 D E C E A)
      )
      (diff_new3 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Int) (E Int) )
    (=>
      (and
        (>= B D)
        (<= D B)
        (<= D E)
        (<= B (- E 1))
        (new7 B E C E A)
      )
      (diff_new3 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Bool) (D Int) (E Int) )
    (=>
      (and
        (>= B D)
        (>= B E)
        (<= E D)
        (<= E D)
        (new9 B D C D A)
      )
      (diff_new3 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) )
    (=>
      (= A true)
      (new1 A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) )
    (=>
      (and
        (diff_new3 B C A)
        (new1 B)
      )
      (new1 A)
    )
  )
)
(assert
  (forall ( (A Bool) )
    (=>
      (and
        (= A false)
        (new1 A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
