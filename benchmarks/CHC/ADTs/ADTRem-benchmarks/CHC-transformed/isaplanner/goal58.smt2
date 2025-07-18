; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new7 (Bool Int) Bool)
(declare-fun new5 (Int Int Bool) Bool)
(declare-fun new3 (Int Int Bool) Bool)
(declare-fun new2 (Int Int Int Int Bool) Bool)
(declare-fun new12 (Int Bool) Bool)
(declare-fun new11 (Int Int Bool) Bool)
(declare-fun new10 (Int Bool) Bool)
(declare-fun new1 (Int Int Int Int Bool) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (= A 0)
      )
      (new12 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (= A 0)
      )
      (new12 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (= B 0)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (= B 0)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= B 0)
        (= A 0)
        (new12 B C)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (>= D 0)
        (= B 0)
        (= A (+ 1 D))
        (new11 D B C)
      )
      (new11 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (= A 0)
      )
      (new10 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) )
    (=>
      (and
        (= B true)
        (= A 0)
      )
      (new10 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) )
    (=>
      (and
        (= A true)
        (>= B 0)
      )
      (new7 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) )
    (=>
      (and
        (= A true)
        (>= B 0)
        (= B 0)
      )
      (new7 A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) )
    (=>
      (and
        (>= C 0)
        (>= B 0)
        (= B (+ 1 C))
        (new7 A C)
      )
      (new7 A B)
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
      (new5 A B C)
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
      (new5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= B 0)
        (= A 0)
        (new10 B C)
      )
      (new5 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) )
    (=>
      (and
        (= C true)
        (>= A 1)
        (= B 0)
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
        (>= A 1)
        (= B 0)
      )
      (new3 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) )
    (=>
      (and
        (>= D 0)
        (>= A 1)
        (= B 0)
        (= A (+ 1 D))
        (new11 D B C)
      )
      (new3 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (>= A 0)
        (<= (- A B) (- 1))
        (= C 0)
      )
      (new2 A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) )
    (=>
      (and
        (= D true)
        (>= A 0)
        (<= (- A B) (- 1))
        (= C 0)
      )
      (new2 A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) )
    (=>
      (and
        (>= A 0)
        (<= (- A B) (- 1))
        (= C 0)
        (= A 0)
        (new3 B C D)
      )
      (new2 A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Int) (G Int) )
    (=>
      (and
        (>= E 0)
        (>= F 0)
        (>= G 0)
        (>= A 0)
        (<= (- A B) (- 1))
        (= C 0)
        (= B (+ 1 E))
        (= B (+ 1 F))
        (= A (+ 1 G))
        (new2 G F E C D)
      )
      (new2 A B B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (>= (- A D) 0)
        (>= D 0)
        (= C (- A D))
        (= B (- A D))
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (>= (- A D) 0)
        (>= D 0)
        (= D 0)
        (= C (- A D))
        (= B (- A D))
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (>= (- A D) 0)
        (>= D 0)
        (= C (- A D))
        (= B (- A D))
        (= B 0)
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (>= (- A D) 0)
        (>= D 0)
        (= D 0)
        (= C (- A D))
        (= B (- A D))
        (= B 0)
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (>= (- A D) 0)
        (>= D 0)
        (= C (- A D))
        (= C 0)
        (= B (- A D))
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (>= (- A D) 0)
        (>= D 0)
        (= D 0)
        (= C (- A D))
        (= C 0)
        (= B (- A D))
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (>= (- A D) 0)
        (>= D 0)
        (= C (- A D))
        (= C 0)
        (= B (- A D))
        (= B 0)
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (= E true)
        (>= (- A D) 0)
        (>= D 0)
        (= D 0)
        (= C (- A D))
        (= C 0)
        (= B (- A D))
        (= B 0)
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (>= (- A D) 0)
        (>= D 0)
        (= C (- A D))
        (= B (- A D))
        (= A 0)
        (new5 C D E)
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) )
    (=>
      (and
        (>= (- A D) 0)
        (>= D 0)
        (= C (- A D))
        (= B (- A D))
        (= B 0)
        (= A 0)
        (new5 C D E)
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) )
    (=>
      (and
        (>= (- A D) 0)
        (>= F 0)
        (>= G 0)
        (>= D 0)
        (= D (+ 1 F))
        (= C (- A D))
        (= C 0)
        (= B (- A D))
        (= B 0)
        (= A (+ 1 G))
        (new7 E G)
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) )
    (=>
      (and
        (>= (- A D) 0)
        (>= F 0)
        (>= G 0)
        (>= H 0)
        (>= D 0)
        (= C (- A D))
        (= C (+ 1 F))
        (= B (- A D))
        (= B (+ 1 G))
        (= A (+ 1 H))
        (new1 H G F D E)
      )
      (new1 A B C D E)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= A false)
        (>= B 0)
        (>= C 0)
        (>= D 0)
        (= D (- C B))
        (new1 C B B D A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) )
    (=>
      (and
        (= A false)
        (>= B 0)
        (>= C 0)
        (<= C (- B 1))
        (= D 0)
        (new2 C B B D A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
